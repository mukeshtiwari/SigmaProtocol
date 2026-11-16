#!/bin/bash
# Differential testing of the Belenios mix-net (src/lib/v1/mixnet.ml) against
# the prime-order model of this repository's certified mix-net verifier. See
# README.md. Reuses the belenios-tool built by bench/belenios-diff/run.sh.
#
# usage: bench/belenios-mixnet-diff/run.sh [--regen]
#   SEEDS=n   torsion seeds per order (default 100)
#   JOBS=n    parallel verifications (default 4)
#   --regen   regenerate the fixture election with belenios-tool (not
#             reproducible bit for bit: belenios-tool reads /dev/urandom)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
SEEDS=${SEEDS:-100}; EXT_SEEDS=${EXT_SEEDS:-50}; JOBS=${JOBS:-4}
TOOL=$ROOT/bench/belenios-diff/_work/belenios-install/bin/belenios-tool
[ "$(uname)" = Darwin ] && export PKG_CONFIG_PATH=/opt/homebrew/lib/pkgconfig C_INCLUDE_PATH=/opt/homebrew/include LIBRARY_PATH=/opt/homebrew/lib

if [ ! -x "$TOOL" ]; then
    echo "belenios-tool not found; run bench/belenios-diff/run.sh first (it builds it)" >&2
    exit 1
fi
export BELENIOS_USE_URANDOM=1
"$TOOL" --version

REGEN=0; for a in "$@"; do [ "$a" = "--regen" ] && REGEN=1; done
if [ "$REGEN" = 1 ]; then
    echo "== regenerating the fixture (a non-homomorphic election with two shuffles)"
    TMP=$(mktemp -d); "$HERE/gen_mix.sh" "$TOOL" "$TMP"
    cp "$TMP/e.bel" "$HERE/fixtures/nh.bel"   # the public archive only; the campaign never decrypts
    rm -rf "$TMP"
fi

echo "== campaign (SEEDS=$SEEDS)"
python3 -I "$HERE/campaign.py" "$TOOL" "$HERE/fixtures/nh.bel" "$HERE/results" "$SEEDS" "$JOBS"

echo "== extended campaign (EXT_SEEDS=$EXT_SEEDS)"
python3 -I "$HERE/campaign_ext.py" "$TOOL" "$HERE/fixtures/nh.bel" "$HERE/results" "$EXT_SEEDS" "$JOBS"

echo "== extracted certified verifier on Belenios shuffles (EXT_SEEDS=$EXT_SEEDS)"
# the TW verifier driver runs ShuffleTW.v's tw_verify at Ed25519; build it in the
# project's default switch (OCaml 5.x, where the extraction theories live)
( cd "$ROOT" && eval "$(opam env --switch=default --set-switch)" &&
  dune build src/Executable/Belenioshuffleverifier/main.exe )
DRIVER=$ROOT/_build/default/src/Executable/Belenioshuffleverifier/main.exe
python3 -I "$HERE/campaign_rocq.py" "$TOOL" "$DRIVER" "$HERE/fixtures/nh.bel" "$HERE/results" "$EXT_SEEDS"
