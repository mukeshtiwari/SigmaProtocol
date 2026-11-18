#!/usr/bin/env bash
# Parallel prover for the Schulze certificate, at the sizes of Table 14 of
# Yang's thesis (the Cortier-Gaudry-Yang tally-hiding Schulze benchmark).
# Run from anywhere; logs go to log/par-<m>-<N>-w<workers>.log.
#
#   bench/schulze_par.sh                 12 workers, the five default sizes
#   bench/schulze_par.sh 18              18 workers
#   bench/schulze_par.sh 12 20:1024      one size (candidates:voters)
#
# Environment:
#   MODE=onepass|twopass   onepass (default) patches the challenge instead of
#                          recomputing every proof; twopass is the extracted
#                          prover's two passes, cell by cell.
#   VERIFY=auto|all|none   run the extracted (single-process) verifier on the
#                          result: auto (default) only below 500,000 branches,
#                          where it takes under about 35 minutes.
#
# A size above about 5 million branches (20:1024 has 18 million) needs the
# chunked hash and tens of GB of memory and temporary disk space; the script
# adds `chunkhash` there.
set -uo pipefail
cd "$(dirname "$0")/.."
W=${1:-12}
if [ $# -gt 0 ]; then shift; fi
SIZES=${*:-"5:64 10:64 20:64 5:1024 10:1024"}
MODE=${MODE:-onepass}
VERIFY=${VERIFY:-auto}
dune build src/Executable/SchulzeBenchcode/par.exe || exit 1
EXE=_build/default/src/Executable/SchulzeBenchcode/par.exe
mkdir -p log
# the extracted transcript functions recurse over the whole transcript
export OCAMLRUNPARAM=${OCAMLRUNPARAM:-l=2000M}

echo "== self-test: 3 candidates, 5 voters, against the extracted prover and verifier"
if ! $EXE 3 5 "$W" onepass check | tee log/par-selftest.log | tail -3; then
  echo "self-test failed"; exit 1
fi
grep -q "equal certificate = true" log/par-selftest.log || { echo "self-test failed"; exit 1; }

for s in $SIZES; do
  m=${s%%:*}; N=${s##*:}
  branches=$(( m*m*m*(2*N+2) + m*m*(4*N+3) + (m*m+m)*(N+1) ))
  flags=""
  [ "$MODE" = onepass ] && flags="$flags onepass"
  [ "$branches" -gt 5000000 ] && flags="$flags chunkhash"
  case "$VERIFY" in
    none) flags="$flags noverify" ;;
    auto) [ "$branches" -gt 500000 ] && flags="$flags noverify" ;;
  esac
  out=log/par-$m-$N-w$W.log
  echo "== m=$m N=$N workers=$W (about $branches branches)$flags -> $out"
  $EXE "$m" "$N" "$W" $flags 2>&1 | tee "$out"
done
echo "== done; logs in log/par-*.log"
