#!/usr/bin/env bash
# Re-run of the Schulze experiments of the paper after the performance
# changes (commit 450a976). One phase per argument:
#   run.sh micro par simple first
# Logs go next to this script; the logs of 2026-11 in log/ are untouched.
set -uo pipefail
cd "$(dirname "$0")/../.."
OUT=log/perf-2026-11-24
B=log/perf-2026-11-24/bin
export OCAMLRUNPARAM=l=2000M
JOBS=${JOBS:-4}
for phase in "$@"; do
  echo "### $phase $(date '+%F %T')"
  case $phase in
    micro)   # tab:ballotcost and tab:tallycost, sequential
      for m in 3 5 7 10 13 17; do
        it=5; [ $m -ge 10 ] && it=3
        $B/SchulzeBenchcode/main.exe $m 1 $it ballot > $OUT/first-$m.log 2>&1
        $B/SchulzeBenchcode/simple.exe $m 11 > $OUT/simple-$m.log 2>&1
      done
      for s in 3:5 3:20 5:50 7:100; do
        $B/SchulzeBenchcode/main.exe ${s%%:*} ${s##*:} 1 > $OUT/tally-${s%%:*}-${s##*:}.log 2>&1
      done ;;
    par)     # tab:par, 12 workers; both verifiers
      $B/SchulzeBenchcode/par.exe 3 5 12 onepass check > $OUT/par-selftest.log 2>&1
      for s in 5:64 10:64 20:64 5:1024 10:1024; do
        m=${s%%:*}; N=${s##*:}
        $B/SchulzeBenchcode/par.exe $m $N 12 onepass > $OUT/par-$m-$N-w12.log 2>&1
      done ;;
    simple)  # tab:gentoo, batched ballot, sequential
      for p in bench/gentoo-votes/positions-council-20[12]*06.txt; do
        e=$(basename $p .txt); e=${e#positions-}
        $B/SchulzeGentoocode/gentoo3.exe $p bench/gentoo-board3/perf-2026-11-24/$e.txt --no-cert \
          > $OUT/gentoo3-$e-ballots.log 2>&1
      done ;;
    first)   # tab:gentoo, first ballot and certificate, JOBS elections at a time
      ls bench/gentoo-votes/positions-council-20[12]*06.txt | xargs -P $JOBS -n 1 sh -c '
        e=$(basename $0 .txt); e=${e#positions-}; b=bench/gentoo-board/perf-2026-11-24/$e.txt
        '$B'/SchulzeGentoocode/encrypt.exe $0 $b > '$OUT'/encrypt-$e.log 2>&1 &&
        '$B'/SchulzeGentoocode/main.exe $b > '$OUT'/main-$e.log 2>&1' ;;
    parverify) # tab:gentoo certificates again, verifier on 12 workers, sequential
      for p in bench/gentoo-votes/positions-council-20[12]*06.txt; do
        e=$(basename $p .txt); e=${e#positions-}
        $B/SchulzeGentoocode/gentoo3.exe $p bench/gentoo-board3/perf-2026-11-24/cert-$e.txt --workers=12 \
          > $OUT/gentoo3-$e-w12.log 2>&1
      done ;;
  esac
done
echo "### done $(date '+%F %T')"
