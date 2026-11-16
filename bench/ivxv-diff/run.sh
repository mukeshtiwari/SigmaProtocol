#!/bin/sh
# Reproducible IVXV differential campaign (verdict comparison only).
#
#   bench/ivxv-diff/run.sh [WORK]          default WORK = bench/ivxv-diff/_work
#   SEED=1 JOBS=4 REGEN=1 (regenerate the IVXV-randomness fixtures)
#
# Fetches and verifies the pinned inputs, builds everything, runs campaign.py,
# and writes results/ (summary.tsv, shuffle.tsv, dec.tsv, go.tsv). IVXV is
# CC BY-NC-ND 3.0: it is fetched at run time and never modified; our drivers
# (java/, go/) are compiled alongside it.
#
# Pinned:
#   IVXV            https://github.com/valimised/ivxv  branch published, commit 2785872f84dffb56bbecc41b096a7ee0f2876e64
#   Verificatum     verificatum-vmn-3.1.0-full.tar.gz  sha256 e848b8704df8ea04a5715808419f09318369ecfcd22dba86760dce520e473aad
#   Gradle          gradle-8.11-bin.zip                sha256 57dafb5c2622c6cc08b993c85b7c06956a2f53536432a30ead46166dbca0f1e9
# Toolchains (Homebrew): openjdk@21 (IVXV, Gradle 8.11), openjdk@25 (Verificatum),
# go (recorded in results/versions.txt; GOTOOLCHAIN=local), the default opam switch.
set -e
here=$(cd "$(dirname "$0")" && pwd); root=$(cd "$here/../.." && pwd)
W=${1:-$here/_work}; mkdir -p "$W"; W=$(cd "$W" && pwd)
IVXV_COMMIT=2785872f84dffb56bbecc41b096a7ee0f2876e64
VMN_SHA=e848b8704df8ea04a5715808419f09318369ecfcd22dba86760dce520e473aad
GRADLE_SHA=57dafb5c2622c6cc08b993c85b7c06956a2f53536432a30ead46166dbca0f1e9
JDK21=${JDK21:-/opt/homebrew/opt/openjdk@21/libexec/openjdk.jdk/Contents/Home}
JDK25=${JDK25:-/opt/homebrew/opt/openjdk@25/libexec/openjdk.jdk/Contents/Home}
GO=${GO:-$(command -v go || echo /opt/homebrew/bin/go)}
export JDK21 JDK25 GOTOOLCHAIN=local

# ---- IVXV ----
[ -d "$W/ivxv/.git" ] || git clone -q --branch published https://github.com/valimised/ivxv.git "$W/ivxv"
git -C "$W/ivxv" checkout -q "$IVXV_COMMIT"
[ "$(git -C "$W/ivxv" rev-parse HEAD)" = "$IVXV_COMMIT" ] || { echo "wrong IVXV commit"; exit 1; }
[ -z "$(git -C "$W/ivxv" status --porcelain --untracked-files=no)" ] || { echo "the IVXV checkout is modified"; exit 1; }

# ---- Gradle 8.11 and the IVXV auditor (JDK 21) ----
if [ ! -x "$W/gradle-8.11/bin/gradle" ]; then
  curl -sfL -o "$W/gradle-8.11-bin.zip" https://services.gradle.org/distributions/gradle-8.11-bin.zip
  echo "$GRADLE_SHA  $W/gradle-8.11-bin.zip" | shasum -a 256 -c - >/dev/null
  (cd "$W" && unzip -q -o gradle-8.11-bin.zip)
fi
if [ ! -d "$W/ivxv/auditor/build/install/auditor/lib" ]; then
  (cd "$W/ivxv/auditor" && JAVA_HOME=$JDK21 "$W/gradle-8.11/bin/gradle" -q -g "$W/gradle-home" --max-workers=4 installDist -x test)
fi
mkdir -p "$W/drivers-classes"
"$JDK21/bin/javac" -nowarn -d "$W/drivers-classes" -cp "$W/ivxv/auditor/build/install/auditor/lib/*" \
  "$here/java/ee/ivxv/audit/shuffle/IvxvShuffleDiff.java" "$here/java/ee/ivxv/common/crypto/elgamal/IvxvDecDiff.java"

# ---- Verificatum 3.1.0 (pure Java, JDK 25), as bench/verificatum-diff ----
if [ ! -x "$W/vmn-install/bin/vmnv" ]; then
  [ -f "$W/vmn.tar.gz" ] || curl -sfL -o "$W/vmn.tar.gz" https://www.verificatum.org/files/verificatum-vmn-3.1.0-full.tar.gz
  echo "$VMN_SHA  $W/vmn.tar.gz" | shasum -a 256 -c - >/dev/null
  rm -rf "$W/vmn-src"; mkdir -p "$W/vmn-src"; (cd "$W/vmn-src" && tar xzf "$W/vmn.tar.gz")
  b="$W/vmn-src/verificatum-vmn-3.1.0-full"
  (cd "$b" && tar xzf verificatum-vcr-3.1.0.tar.gz && tar xzf verificatum-vmn-3.1.0.tar.gz)
  # VMN's URL check rejects hostnames with upper-case letters; lower-case the default (as bench/verificatum-diff)
  perl -0pi -e 's/return ia\.getHostName\(\);/return ia.getHostName().toLowerCase(java.util.Locale.ROOT);/' \
    "$b/verificatum-vcr-3.1.0/src/java/com/verificatum/protocol/ProtocolDefaults.java"
  export JAVA_HOME=$JDK25 PATH=$W/vmn-install/bin:$JDK25/bin:$PATH   # vmn's configure runs vcr-3.1.0-info
  (cd "$b/verificatum-vcr-3.1.0" && ./configure --prefix="$W/vmn-install" >/dev/null && make >/dev/null && make install >/dev/null)
  (cd "$b/verificatum-vmn-3.1.0" && ./configure --prefix="$W/vmn-install" >/dev/null && make >/dev/null && make install >/dev/null)
  ln -sfn "$b/verificatum-vmn-3.1.0" "$W/vmn-src/verificatum-vmn-3.1.0"
fi
# vmnv's own temporary randomness, seeded
printf '%064d' 0 > "$W/vmnv_seed0"
VERIFICATUM_RANDOM_SOURCE=$W/vmnv_rs VERIFICATUM_RANDOM_SEED=$W/vmnv_rseed JAVA_HOME=$JDK25 PATH=$JDK25/bin:$PATH \
  "$W/vmn-install/bin/vog" -rndinit -seed "$W/vmnv_seed0" PRGHeuristic >/dev/null 2>&1 || true
# the group of the campaign is vog's fixed 2048-bit safe-prime group
JAVA_HOME=$JDK25 PATH=$JDK25/bin:$PATH "$W/vmn-install/bin/vog" -gen ModPGroup -fixed 2048 | tr -d '\n' > "$W/group.txt"
[ "$(cat "$W/group.txt")" = "$(tr -d '\n' < "$here/group.txt")" ] || { echo "group.txt differs from vog -fixed 2048"; exit 1; }

# ---- the Go driver against the unmodified IVXV core ----
mkdir -p "$W/go"; cp "$here/go/main.go" "$W/go/"
(cd "$W/go" && rm -f go.mod go.sum && "$GO" mod init ivxvdiff >/dev/null 2>&1 &&
  "$GO" mod edit -require=tivi.io/core@v0.0.0 -replace=tivi.io/core="$W/ivxv/core" &&
  GOFLAGS=-mod=mod "$GO" mod tidy >/dev/null 2>&1 && "$GO" build -o ivxvgo .)
q_go=$("$W/go/ivxvgo" group | cut -f1 -d' ')
python3 -c "import sys; sys.path.insert(0, '$here'); import ivxvlib as L; assert str(L.Q14) == '$q_go', 'RFC 3526 group 14 differs from the Go core table'"

# ---- the certified side ----
(cd "$root" && eval "$(opam env --switch=default --set-switch)" && python3 "$here/mkins.py" >/dev/null &&
  dune build src/Executable/Ivxvdiff/main.exe 2>&1 | grep -E '^Error' && exit 1 || true)

# ---- versions ----
mkdir -p "$here/results"
{ echo "IVXV $IVXV_COMMIT"; echo "Verificatum 3.1.0 $VMN_SHA"; echo "Gradle 8.11 $GRADLE_SHA"
  "$JDK21/bin/java" -version 2>&1 | head -1; "$JDK25/bin/java" -version 2>&1 | head -1; "$GO" version
  (cd "$root" && eval "$(opam env --switch=default)" && echo "OCaml $(ocamlc -version), Rocq $(rocq -v 2>/dev/null | head -1 | grep -o '[0-9][0-9.]*' | head -1)")
  python3 --version; uname -sr; } > "$here/results/versions.txt"

# ---- the campaign ----
rm -rf "$W/cases"
SEED=${SEED:-1} JOBS=${JOBS:-4} python3 "$here/campaign.py" "$W"
