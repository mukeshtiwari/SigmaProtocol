#!/usr/bin/env bash
# Fetch the pinned external inputs of build.sh into DIR (default
# bench/peregrine/deps) and print the environment that build.sh reads.
#
#   eval "$(bench/peregrine/deps.sh [DIR])"
#
# - RT: the C runtime of CertiRocq, commit ab66e01 of
#   https://github.com/CertiRocq/certirocq (build.sh uses gc_stack.c and the
#   headers of runtime/).
# - MINIGMP: mini-gmp of GMP 6.3.0 (https://ftp.gnu.org/gnu/gmp/, checked
#   against its SHA-256), for the WebAssembly build.
# - PEREGRINE_TOOL: peregrine-tool at commit 13c701b of branch
#   numeral-literals (https://github.com/peregrine-project/peregrine-tool),
#   which has the numeral-hoisting pass.  It is fetched, not built: build it
#   with dune in an opam switch with the dependencies of its
#   rocq-peregrine.opam (Rocq 9.1), so that _build/default/bin/main.exe
#   exists.
#
# The GMP remapping (GMPZ) is in bench/peregrine/gmpz and needs no fetch.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
D=$(mkdir -p "${1:-$HERE/deps}" && cd "${1:-$HERE/deps}" && pwd)

CERTIROCQ_COMMIT=ab66e0164e7ecb63e5af95c90c8e479068bf95c2
PEREGRINE_TOOL_COMMIT=13c701be7fa272c3e57f7d7211b4ff897095860c
GMP_VERSION=6.3.0
GMP_SHA256=a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898

if [ ! -f "$D/certirocq/runtime/gc_stack.c" ]; then
  git init -q "$D/certirocq"
  git -C "$D/certirocq" fetch -q --depth 1 https://github.com/CertiRocq/certirocq "$CERTIROCQ_COMMIT"
  git -C "$D/certirocq" checkout -q FETCH_HEAD -- runtime
fi

if [ ! -f "$D/mini-gmp/mini-gmp.c" ]; then
  t="$D/gmp-$GMP_VERSION.tar.xz"
  curl -sSfLo "$t" "https://ftp.gnu.org/gnu/gmp/gmp-$GMP_VERSION.tar.xz"
  echo "$GMP_SHA256  $t" | sha256sum -c --quiet -
  mkdir -p "$D/mini-gmp"
  tar -xJf "$t" -C "$D/mini-gmp" --strip-components=2 \
    "gmp-$GMP_VERSION/mini-gmp/mini-gmp.c" "gmp-$GMP_VERSION/mini-gmp/mini-gmp.h"
  rm -f "$t"
fi

if [ ! -d "$D/peregrine-tool/.git" ]; then
  git clone -q https://github.com/peregrine-project/peregrine-tool "$D/peregrine-tool"
fi
git -C "$D/peregrine-tool" checkout -q "$PEREGRINE_TOOL_COMMIT"

echo "export RT=$D/certirocq/runtime"
echo "export MINIGMP=$D/mini-gmp"
echo "export PEREGRINE_TOOL=$D/peregrine-tool"
