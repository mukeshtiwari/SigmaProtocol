#!/bin/sh
# Reproducible differential-testing campaign: Verificatum's own verifier vmnv
# against our certified verifier (src/Executable/Vmnverifier/main.exe), on
# mixing sessions produced by vmn.
#
#   bench/verificatum-diff/run.sh WORKDIR
#
# WORKDIR holds the download, the VMN build, the generated sessions and the
# results. Needs: a JDK >= 21 (JAVA_HOME, or openjdk@25 at the Homebrew path
# below), GCC/make/autotools, curl, python3, and the certified verifier built
# in the default opam switch (dune build src/Executable/Vmnverifier/main.exe).
#
# Pinned versions (verified by sha256):
#   verificatum-vmn-3.1.0-full.tar.gz  e848b8704df8ea04a5715808419f09318369ecfcd22dba86760dce520e473aad
#   contains vcr-3.1.0, vmn-3.1.0 (built pure-Java; the rest are unused).
# The group is the certified 2048-bit Helios group of HeliosTallyIns.v
# (group.txt), the one src/Executable/Vmnverifier targets.
set -e
W=$1; [ -n "$W" ] || { echo "usage: run.sh WORKDIR"; exit 2; }
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
mkdir -p "$W"; W=$(cd "$W" && pwd)
JAVA_HOME=${JAVA_HOME:-/opt/homebrew/opt/openjdk@25/libexec/openjdk.jdk/Contents/Home}
export JAVA_HOME; export PATH="$JAVA_HOME/bin:$PATH"
TARBALL_SHA=e848b8704df8ea04a5715808419f09318369ecfcd22dba86760dce520e473aad
OURS=$root/_build/default/src/Executable/Vmnverifier/main.exe
[ -x "$OURS" ] || { echo "build the certified verifier first: dune build src/Executable/Vmnverifier/main.exe"; exit 2; }

# ---- 1. fetch and build VMN 3.1.0 (vcr + vmn, pure Java) into $W/install ----
dl=$W/download; mkdir -p "$dl"
if [ ! -f "$dl/vmn.tar.gz" ]; then
  curl -sfL -o "$dl/vmn.tar.gz" https://www.verificatum.org/files/verificatum-vmn-3.1.0-full.tar.gz
fi
echo "$TARBALL_SHA  $dl/vmn.tar.gz" | shasum -a 256 -c -
INSTALL=$W/install; SRC=$W/src
if [ ! -x "$INSTALL/bin/vmnv" ]; then
  rm -rf "$SRC"; mkdir -p "$SRC"; (cd "$SRC" && tar xzf "$dl/vmn.tar.gz")
  bundle="$SRC/verificatum-vmn-3.1.0-full"
  (cd "$bundle" && tar xzf verificatum-vcr-3.1.0.tar.gz && tar xzf verificatum-vmn-3.1.0.tar.gz)
  # VMN's URL check rejects hostnames with upper-case letters; lower-case the default.
  perl -0pi -e 's/return ia\.getHostName\(\);/return ia.getHostName().toLowerCase(java.util.Locale.ROOT);/' \
    "$bundle/verificatum-vcr-3.1.0/src/java/com/verificatum/protocol/ProtocolDefaults.java"
  (cd "$bundle/verificatum-vcr-3.1.0" && ./configure --prefix="$INSTALL" >/dev/null && make >/dev/null && make install >/dev/null)
  (cd "$bundle/verificatum-vmn-3.1.0" && ./configure --prefix="$INSTALL" >/dev/null && make >/dev/null && make install >/dev/null)
  cp "$bundle/verificatum-vmn-3.1.0/src/sh/mixnet"/* "$INSTALL/demo-not-used" 2>/dev/null || true
fi
VMN_SRC="$W/src/verificatum-vmn-3.1.0-full/verificatum-vmn-3.1.0"
"$INSTALL/bin/vmnv" -version

# vmnv needs a configured random source for its temporary randomness.
export VERIFICATUM_RANDOM_SOURCE=$W/vmnv_rs VERIFICATUM_RANDOM_SEED=$W/vmnv_rseed
printf '%064d' 0 > "$W/vmnv_seed0"
"$INSTALL/bin/vog" -rndinit -seed "$W/vmnv_seed0" PRGHeuristic >/dev/null 2>&1 || true

# ---- 2. generate sessions (seed fixed; shared and distinct per-server seeds) ----
# "shared" is what VMN's own demo does (one seedfile for all parties), which
# makes the mix-servers' proof announcements A' collide.
gen() { "$here/gen_session.sh" "$INSTALL" "$VMN_SRC" "$@"; }
[ -d "$W/s_shared" ]   || gen "$W/s_shared"   10 3 2 vdiff-seed shared
[ -d "$W/s_distinct" ] || gen "$W/s_distinct" 10 3 2 vdiff-seed distinct
[ -d "$W/s_prime" ]    || gen "$W/s_prime"    11 3 2 vdiff-seed shared    # N prime

# ---- 3. run the campaign (twice on the shared session, confirm determinism) ----
VMNV=$INSTALL/bin/vmnv
run_camp() { python3 -I "$here/campaign.py" "$1" "$VMNV" "$OURS" "$2"; }
mkdir -p "$W/results"
for s in s_shared s_distinct s_prime; do
  run_camp "$W/$s" "$W/camp_$s" > "$W/results/$s.out" 2>&1 || true
  cp "$W/camp_$s/summary.tsv" "$W/results/$s.tsv"
done
# determinism: a second run of the shared campaign must give the same verdict table
run_camp "$W/s_shared" "$W/camp_s_shared_2" > "$W/results/s_shared_2.out" 2>&1 || true
if cut -f1-5 "$W/camp_s_shared/summary.tsv" | sort > "$W/.r1" && cut -f1-5 "$W/camp_s_shared_2/summary.tsv" | sort > "$W/.r2" && diff -q "$W/.r1" "$W/.r2" >/dev/null; then
  echo "determinism: the two seeded shared-session runs give identical verdict tables"
else
  echo "determinism: WARNING the two runs differ"; diff "$W/.r1" "$W/.r2" || true
fi

# ---- 4. the pre-fix driver, if present, to show the completeness bug ----
echo
echo "Summary (vmnv vs certified):"
for s in s_shared s_distinct s_prime; do
  echo "  $s: $(tail -1 "$W/results/$s.out")"
done
echo "Verdict tables in $W/results/*.tsv"
