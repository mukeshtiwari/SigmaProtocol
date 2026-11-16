#!/bin/bash
# Differential testing of Belenios: belenios-tool (`election verify`) against
# the certified verifier of this repository. Reproducible from the committed
# fixtures; see README.md.
#
# usage: bench/belenios-diff/run.sh [WORK_DIR] [--regen]
#   WORK_DIR   build and case directory (default bench/belenios-diff/_work)
#   SEED=n     seed of every generated case (default 1)
#   JOBS=n     parallel verifications (default 4)
#   --regen    regenerate the fixtures with belenios-tool first (not
#              reproducible bit for bit: belenios-tool reads /dev/urandom)
# Requires: opam, git, python3, jq, libsodium and pkg-config (macOS: brew install libsodium pkgconf).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
WORK=${1:-$HERE/_work}; [ "${1:-}" = "--regen" ] && WORK=$HERE/_work
REGEN=0; for a in "$@"; do [ "$a" = "--regen" ] && REGEN=1; done
SEED=${SEED:-1}; JOBS=${JOBS:-4}
SWITCH=belenios-diff
BELENIOS_URL=https://gitlab.inria.fr/belenios/belenios.git
BELENIOS_COMMIT=50a79aed0d34d77a406958dd5a8cb77fe2f32b30   # tag 3.2.0
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)
[ "$(uname)" = Darwin ] && export PKG_CONFIG_PATH=/opt/homebrew/lib/pkgconfig C_INCLUDE_PATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib

echo "== opam switch $SWITCH (the default switch is not touched)"
if ! opam switch list -s | grep -qx "$SWITCH"; then
    opam switch create "$SWITCH" ocaml-base-compiler.5.4.1 --no-switch -y
    opam switch import "$HERE/belenios-diff.opam-switch" --switch="$SWITCH" -y
fi

echo "== Belenios $BELENIOS_COMMIT"
if [ ! -d "$WORK/belenios/.git" ]; then git clone -q "$BELENIOS_URL" "$WORK/belenios"; fi
git -C "$WORK/belenios" fetch -q origin "$BELENIOS_COMMIT" 2>/dev/null || true
git -C "$WORK/belenios" checkout -q "$BELENIOS_COMMIT"
[ "$(git -C "$WORK/belenios" rev-parse HEAD)" = "$BELENIOS_COMMIT" ] || { echo "wrong Belenios commit"; exit 1; }
TOOL=$WORK/belenios-install/bin/belenios-tool
if [ ! -x "$TOOL" ]; then
    (cd "$WORK/belenios" && eval "$(opam env --switch=$SWITCH --set-switch)" &&
        dune build -p belenios-platform,belenios-platform-native,belenios-lib,belenios-tool @install &&
        dune install -p belenios-platform,belenios-platform-native,belenios-lib,belenios-tool --destdir="$WORK/belenios-install" --prefix=/)
fi
BELENIOS_USE_URANDOM=1 "$TOOL" --version | tee "$WORK/versions.txt"

echo "== certified verifier"
(cd "$ROOT" && eval "$(opam env --switch=default --set-switch)" && dune build src/Executable/Beleniosverifier/main.exe)
OURS=$ROOT/_build/default/src/Executable/Beleniosverifier/main.exe

FIX=$HERE/fixtures
if [ "$REGEN" = 1 ]; then
    echo "== regenerating the fixtures with belenios-tool"
    E=$HERE/elections
    for n in demo multi single empty complex; do
        NT=1; [ $n = demo ] && NT=3; [ $n = multi ] && NT=2
        R=; [ -f "$E/$n.revotes.txt" ] && R=$E/$n.revotes.txt
        "$HERE/gen_election.sh" "$TOOL" "$FIX" $n "$E/$n.template.json" "$E/$n.voters.txt" "$E/$n.votes.txt" $NT $R
    done
fi

echo "== cases (SEED=$SEED)"
rm -rf "$WORK/cases"
python3 -I "$HERE/cases.py" "$FIX" "$WORK" "$SEED"
(cd "$WORK/cases" && find . -name '*.bel' -print0 | sort -z | xargs -0 shasum -a 256) > "$WORK/cases.sha256"

echo "== verdicts"
python3 -I "$HERE/run_cases.py" "$TOOL" "$OURS" "$WORK" "$HERE/results" "$JOBS"
