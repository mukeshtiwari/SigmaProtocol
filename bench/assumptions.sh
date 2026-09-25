#!/usr/bin/env bash
# Print the assumptions of every theorem listed in THEOREMS.md.
# Run from the repository root after `dune build`.
set -uo pipefail
cd "$(dirname "$0")/.."
B=_build/default/src
rocq compile -w -all \
  -Q "$B/Algebra" Algebra -Q "$B/Utility" Utility -Q "$B/Probability" Probability \
  -Q "$B/Crypto" Crypto -Q "$B/Frontend" Frontend -Q "$B/Backend" Backend \
  -Q "$B/Examples" Examples \
  bench/assumptions.v 2>&1 | grep -v '^$'
status=${PIPESTATUS[0]}
rm -f bench/assumptions.vo bench/assumptions.vos bench/assumptions.vok \
  bench/assumptions.glob bench/.assumptions.aux 2>/dev/null || true
exit "$status"
