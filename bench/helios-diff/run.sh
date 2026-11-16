#!/bin/sh
# Differential testing of Helios (the pinned helios-server's own Python
# verification code and booth JavaScript) against the certified Helios
# verifier and prover. See README.md.
#
# usage: bench/helios-diff/run.sh [--twice] [--no-iacr] [--regen-booth] [WORK_DIR]
#   SEED (default 1) seeds everything except the booth's ballots, which are
#   the fixtures in fixtures/booth.json (regenerated, for the keys SEED
#   gives, only with --regen-booth; needs Node).
#   --twice runs the whole campaign a second time from scratch and checks
#   that the two verdict tables are identical.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
SEED=${SEED:-1}
twice=; noiacr=; regen=; WORK=$here/work
for a in "$@"; do
  case $a in
    --twice) twice=1 ;; --no-iacr) noiacr=--no-iacr ;; --regen-booth) regen=--regen-booth ;;
    *) WORK=$a ;;
  esac
done
mkdir -p "$WORK"; WORK=$(cd "$WORK" && pwd)

# the deployed code: helios-server, pinned
git -C "$root" submodule update --init bench/helios-server
rev=$(git -C "$root/bench/helios-server" rev-parse HEAD)
[ "$rev" = 88621e3196961ec03fe54bbd3a1c2196e715e9a2 ] || { echo "bench/helios-server is at $rev, not 88621e3"; exit 1; }

# Python 3.13.16 and pycryptodome 4.1.0 (Helios's crypto dependency)
VENV=$WORK/venv
[ -x "$VENV/bin/python" ] || uv venv -q "$VENV" --python 3.13.16
uv pip install -q -p "$VENV/bin/python" pycryptodome==4.1.0

# the certified side
# (waits while another dune instance holds the build lock)
build() { (cd "$root" && opam exec --switch=default -- dune build \
  src/Executable/HeliosVerifiercode/diff.exe src/Executable/HeliosVerifiercode/prove.exe) 2>&1; }
until out=$(build); do
  case $out in *"Another Dune instance"*) sleep 30 ;; *) echo "$out"; exit 1 ;; esac
done

campaign() {   # $1: run directory, $2: results directory
  rm -rf "$1"
  "$VENV/bin/python" "$here/gen.py" "$SEED" "$1" $regen
  "$VENV/bin/python" "$here/campaign.py" "$SEED" "$1" "$2" $noiacr
}
start=$(date +%s)
campaign "$WORK/run" "$here/results"
echo "campaign: $(( $(date +%s) - start )) s"
if [ -n "$twice" ]; then
  regen=
  campaign "$WORK/run2" "$WORK/results2" > /dev/null
  if cmp -s "$here/results/verdicts.tsv" "$WORK/results2/verdicts.tsv"; then
    echo "second run: identical verdicts ($(shasum -a 256 "$here/results/verdicts.tsv" | cut -c1-16)…)"
  else
    echo "second run: verdicts differ"; diff "$here/results/verdicts.tsv" "$WORK/results2/verdicts.tsv" | head; exit 1
  fi
fi
