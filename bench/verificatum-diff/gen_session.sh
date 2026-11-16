#!/bin/sh
# Generates one Verificatum mixing session with vmn's own demo scripts
# (demo/mixnet of verificatum-vmn-3.1.0), deterministically: every random
# source is VCR's PRGHeuristic (SHA-256 in counter mode) with a seed derived
# from SEED, the global one (ciphertext generation) and one per mix-server
# (or one shared by all of them with SEEDMODE=shared). The group is the
# certified Helios group of Examples/HeliosTallyIns.v (group.txt).
#
# usage: gen_session.sh VMN_INSTALL VMN_SRC OUT N K THRESHOLD SEED [SEEDMODE] [MAXCIPH]
#   OUT receives protInfo.xml and default/ (the proof directory of mix-server 1)
set -e
INSTALL=$1; SRC=$2; OUT=$3; N=$4; K=$5; THR=$6; SEED=$7; SEEDMODE=${8:-distinct}; MAXCIPH=${9:-}
here=$(cd "$(dirname "$0")" && pwd)
PATH=$INSTALL/bin:$PATH; export PATH
W=$OUT.work; rm -rf "$W" "$OUT"; mkdir -p "$W" "$OUT"; W=$(cd "$W" && pwd)
cp -R "$SRC/demo/mixnet" "$W/"
cd "$W/mixnet"
h() { printf '%s' "$1" | shasum -a 256 | cut -c1-64; }
VERIFICATUM_RANDOM_SOURCE=$W/random_source; VERIFICATUM_RANDOM_SEED=$W/random_seed
export VERIFICATUM_RANDOM_SOURCE VERIFICATUM_RANDOM_SEED
h "$SEED/global" > "$W/seed_global"
vog -rndinit -seed "$W/seed_global" PRGHeuristic > /dev/null
for i in $(seq 1 "$K"); do
  if [ "$SEEDMODE" = shared ]; then h "$SEED/party" > "seedfile_$i"; else h "$SEED/party/$i" > "seedfile_$i"; fi
done
# each mix-server gets its own seed file
sed -i.bak 's|^    copyto seedfile \$i *$|    copyto seedfile_$i $i seedfile|' info_files
grep -q 'copyto seedfile_\$i \$i seedfile' info_files
python3 - "$N" "$K" "$THR" "$(cat "$here/group.txt")" "$MAXCIPH" <<'EOF'
import re, sys
n, k, thr, pg, maxc = sys.argv[1:6]
s = open("conf").read()
def setv(name, val):
    global s
    # the live definition, or else the commented-out example
    s, c = re.subn(r"^%s=.*$" % name, "%s=%s" % (name, val), s, count=1, flags=re.M)
    if c == 0: s, c = re.subn(r"^#%s=.*$" % name, "%s=%s" % (name, val), s, count=1, flags=re.M)
    assert c == 1, name
setv("NO_CIPHERTEXTS", n); setv("NO_MIXSERVERS", k); setv("THRESHOLD", thr)
setv("PGROUP", "'%s'" % pg); setv("RAND", "$(vog -gen PRGHeuristic)")
setv("INTER", "raw"); setv("TERM", "./vterm")
if maxc: setv("MAX_NO_CIPHERTEXTS", maxc)
open("conf", "w").write(s)
EOF
steps="clean info_files keygen"
[ -n "$MAXCIPH" ] && steps="$steps precomp"
steps="$steps gen_ciphs mix"
for s in $steps; do
  ./$s > "$W/$s.log" 2>&1 || { echo "gen_session: step $s failed (see $W/$s.log)"; exit 1; }
  if grep -q 'Demo command failed' "$W/$s.log"; then echo "gen_session: step $s failed (see $W/$s.log)"; exit 1; fi
done
cp mydemodir/Party01/protInfo.xml "$OUT/"
cp -R mydemodir/Party01/dir/nizkp/default "$OUT/default"
echo "gen_session: $OUT (N=$N K=$K threshold=$THR seed=$SEED $SEEDMODE${MAXCIPH:+ maxciph=$MAXCIPH})"
