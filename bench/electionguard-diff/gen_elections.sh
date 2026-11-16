#!/bin/sh
# Generates the fixture elections of the campaign with the ElectionGuard
# reference implementation (electionguard-kotlin-multiplatform, egk): manifest,
# configuration, trusted key ceremony, input ballots, batch encryption, the
# chosen ballots marked CHALLENGED, tally accumulation, trusted tally and
# challenged-ballot decryption. egk draws its randomness from SecureRandom, so
# an election cannot be regenerated bit for bit: the campaign runs on the
# saved fixtures (fixtures/, with the trustees' and voters' private data that
# the forgeries need), and this script only documents and repeats how they
# were made.
#
# usage: gen_elections.sh EGK_ALL_JAR JAVA OUT_DIR
set -eu
jar=$1; java=$2; out=$3
mkdir -p "$out"; out=$(cd "$out" && pwd)
run() { (cd "$out" && "$java" -classpath "$jar" "$@" > /dev/null); }   # egk writes egkServer.log into its cwd
mark_challenged() {   # RECORD K...: set the state of the K-th ballots (1-based, files sorted by name) to SPOILED (egk: CAST, SPOILED, UNKNOWN)
  rec=$1; shift
  python3 -I -c 'import json,sys,glob
fs=sorted(glob.glob(sys.argv[1]+"/encrypted_ballots/*/eballot-*.json"))
for k in sys.argv[2:]:
    f=fs[int(k)-1]; b=json.load(open(f)); b["state"]="SPOILED"; json.dump(b,open(f,"w"),indent=2)' "$rec" "$@"
}
# election NAME NCONTESTS NSELECTIONS NGUARDIANS QUORUM NBALLOTS CHAIN(true|false) VOTES_ALLOWED_OF_CONTEST_2 MISSING CHALLENGED...
election() {
  name=$1 nc=$2 ns=$3 ng=$4 qu=$5 nb=$6 chain=$7 l2=$8 missing=$9; shift 9
  w="$out/$name.work"; rec="$out/$name"
  rm -rf "$w" "$rec"; mkdir -p "$w"
  run electionguard.cli.RunCreateTestManifest -ncontests "$nc" -nselections "$ns" -out "$w/manifest"
  if [ "$l2" != 1 ]; then   # a contest with more than one vote allowed
    python3 -I -c 'import json,sys
f=sys.argv[1]; m=json.load(open(f)); c=m["contests"][1]
c["votes_allowed"]=int(sys.argv[2]); c["number_elected"]=int(sys.argv[2]); c["vote_variation"]="n_of_m"
json.dump(m,open(f,"w"),indent=2)' "$w/manifest/manifest.json" "$l2"
  fi
  if [ "$chain" = true ]; then chainopt=--chainCodes; else chainopt=; fi
  run electionguard.cli.RunCreateElectionConfig -manifest "$w/manifest" -nguardians "$ng" -quorum "$qu" -out "$w/config" -device device42 $chainopt
  run electionguard.cli.RunTrustedKeyCeremony -in "$w/config" -trustees "$w/trustees" -out "$w/keyceremony"
  run electionguard.cli.RunCreateInputBallots -manifest "$w/manifest" -out "$w/input" -n "$nb" -json
  run electionguard.cli.RunBatchEncryption -in "$w/keyceremony" -ballots "$w/input" -out "$rec" -device device42 -nthreads 4 --cleanOutput
  [ $# -gt 0 ] && mark_challenged "$rec" "$@"
  run electionguard.cli.RunAccumulateTally -in "$rec" -out "$rec"
  if [ -n "$missing" ]; then
    run electionguard.cli.RunTrustedTallyDecryption -in "$rec" -trustees "$w/trustees" -out "$rec" -missing "$missing"
  else
    run electionguard.cli.RunTrustedTallyDecryption -in "$rec" -trustees "$w/trustees" -out "$rec"
  fi
  [ $# -gt 0 ] && run electionguard.cli.RunTrustedBallotDecryption -in "$rec" -trustees "$w/trustees" -out "$rec" -nthreads 4
  mkdir -p "$rec/private_data"
  cp -r "$w/trustees" "$rec/private_data/trustees"; cp -r "$w/input" "$rec/private_data/input"
  rm -rf "$w"
  echo "generated $name"
}
mkdir -p "$out"
#        name     contests sel guardians quorum ballots chain L2 missing challenged (positions)
election small    2  3  3  3   6 false 1 ""    2
election chained-batch 2 3 3 3 6 true 1 "" 3   # egk batch encryption does not chain the codes (a protocol case)
election quorum   2  3  5  3   6 false 1 "2,4" 4
election multi    3  4  3  3   6 false 2 ""    1
election medium   4  4  3  3  15 false 1 ""    2 7
