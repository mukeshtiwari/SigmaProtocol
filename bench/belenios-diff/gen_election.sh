#!/bin/bash
# Generates one Belenios election with belenios-tool, following the
# Belenios test script tests/tool/demo.sh of the pinned release: Ed25519,
# "Single" trustees, credentials, ballots (and revotes), encrypted tally,
# partial decryptions, result, and belenios-tool's own final verification.
#
# usage: gen_election.sh BELENIOS_TOOL OUTDIR NAME TEMPLATE.json VOTERS.txt VOTES.txt NTRUSTEES [REVOTES.txt]
#   VOTERS.txt  lines id,login[,weight] (as belenios-tool setup generate-credentials --file)
#   VOTES.txt   one choice vector per voter, in the order of VOTERS.txt
#   REVOTES.txt optional choice vectors re-cast by the first voters, after all votes
# Writes OUTDIR/NAME/{NAME.bel, private_creds.txt, trustee*.privkey, verify.log}.
# belenios-tool draws its randomness from /dev/urandom (BELENIOS_USE_URANDOM=1),
# so the archives are not reproducible bit for bit: they are kept as fixtures.
set -euo pipefail
TOOL=$(cd "$(dirname "$1")" && pwd)/$(basename "$1"); OUT=$2; NAME=$3
TEMPLATE=$(cd "$(dirname "$4")" && pwd)/$(basename "$4")
VOTERS=$(cd "$(dirname "$5")" && pwd)/$(basename "$5")
VOTES=$(cd "$(dirname "$6")" && pwd)/$(basename "$6"); NT=$7
REVOTES=${8:+$(cd "$(dirname "$8")" && pwd)/$(basename "$8")}
export BELENIOS_USE_URANDOM=1
bt () { "$TOOL" "$@"; }
DIR=$OUT/$NAME; rm -rf "$DIR"; mkdir -p "$DIR"; cd "$DIR"
UUID=$(bt setup generate-token)
group="--group Ed25519"
bt setup generate-credentials --uuid "$UUID" $group --file "$VOTERS" > generate-credentials.out
mv ./*.pubcreds public_creds.json; mv ./*.privcreds private_creds.json
paste <(jq --raw-output 'keys_unsorted[]' < private_creds.json) <(jq --raw-output '.[]' < private_creds.json) > private_creds.txt
for i in $(seq 1 "$NT"); do bt setup generate-trustee-key $group; done
cat ./*.pubkey > public_keys.jsons
bt setup make-trustees; rm public_keys.jsons
bt setup make-election --uuid "$UUID" $group --template "$TEMPLATE"
bt archive init
rm -f election.json trustees.json public_creds.json generate-credentials.out
cast () {   # privcred choice
    local B; B="$(bt election generate-ballot --privcred <(echo "$1") --choice <(echo "$2"))"
    bt election verify-ballot --ballot <(echo "$B") > /dev/null
    echo "$B" | bt archive add-event --type=Ballot
}
# the first |VOTES| voters vote (an empty VOTES.txt gives an election without ballots)
paste <(head -n "$(wc -l < "$VOTES")" private_creds.txt) "$VOTES" | while IFS=$'\t' read -r id cred vote; do cast "$cred" "$vote"; done
if [ -n "$REVOTES" ]; then
    paste <(head -n "$(wc -l < "$REVOTES")" private_creds.txt) "$REVOTES" | while IFS=$'\t' read -r id cred vote; do cast "$cred" "$vote"; done
fi
bt archive add-event --type=EndBallots < /dev/null
bt election compute-encrypted-tally | bt archive add-event --type=EncryptedTally
t=1
for u in $(ls ./*.privkey | sort); do
    bt election decrypt --privkey "$u" --trustee-id $t | bt archive add-event --type=PartialDecryption
    mv "$u" "trustee$t.privkey"; t=$((t + 1))
done
rm -f ./*.pubkey
bt election compute-result | bt archive add-event --type=Result
bt election verify > verify.log 2>&1
mv "$UUID.bel" "$NAME.bel"
echo "$NAME: uuid $UUID, $(tar -tf "$NAME.bel" | wc -l | tr -d ' ') archive entries"
