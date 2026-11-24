#!/usr/bin/env bash
# Extract the approval ballot of Ballot_LamBox.v with Peregrine, remap Z,
# positive and N to GMP integers, compile the C with gcc and run it.
#
# Usage, after `dune build _build/default/src/Examples/WasmBenchSmallDefs.vo`
# in the repository root:
#   F=<peregrine-frontend> M=<peregrine-tool main.exe, built from branch
#   numeral-literals of https://github.com/peregrine-project/peregrine-tool,
#   which has the numeral-hoisting pass> RT=<CertiRocq C runtime> \
#   GMPZ=<dir with GmpZ.v, z_gmp.c, z_gmp.h, splice_gmp_z.py, splice_locked.py,
#         stub_axioms.py, run_deep.py, main_bool.c> \
#   [PEREGRINE_FINDLIB=<findlib dir holding rocq-peregrine/META>] \
#   [PROGRAMS="small64_verify ..."] [RUN_TIMEOUT=3600] [MEM_MAX=5G] \
#   bench/peregrine/build.sh
#
# With MINIGMP=<dir with mini-gmp.c and mini-gmp.h> set, every program is also
# compiled to 64-bit WebAssembly with emscripten (EMCC, default emcc; the
# generated C assumes 64-bit words, hence -sMEMORY64=1), with mini-gmp as the
# big-integer library, and run with NODE (default node, which must support
# memory64, e.g. Node 24).  The JavaScript glue of emscripten 3.1.6 (Ubuntu
# 24.04) passes 64-bit pointers as BigInt to two library functions that expect
# numbers; the script patches those two functions.  Ubuntu's emscripten has no
# prebuilt wasm64 system libraries: point EM_CONFIG at a copy of its config
# with FROZEN_CACHE = False and a writable CACHE.
#
# Every step runs in a systemd scope with MemoryMax=$MEM_MAX (or, without
# systemd, under ulimit -v), so that a step that runs out of memory is killed
# alone. Peregrine needs about 2.5 GB for a program with 256-bit numerals.
#
# The attribute file passed to Peregrine sets PeregrineNumerals.threshold to
# NUM_BITS (default 64): Peregrine's numeral-hoisting pass moves every numeral
# of at least that many bits into a constant, which the C backend compiles to
# a call of peregrine_numeral_of_string (numeral_hook.c) on its decimal
# digits.  Without it the 2048-bit ballot does not compile in 4 GB.
#
# GMPZ is the GMP remapping of the executable KZG demo (demo/c-exec and
# demo/extraction/GmpZ.v of the Commitments repository). Outputs, logs and
# timings (<program>.<step>.time, with /usr/bin/time) stay in
# bench/peregrine/work/.
#
# Trusted: Peregrine, the GMP remapping (GmpZ.v against z_gmp.c, and
# splice_gmp_z.py), numeral_hook.c, stub_axioms.py, the CertiRocq C runtime,
# gcc and GMP.
set -euo pipefail
: "${F:?set F to the Peregrine frontend directory}"
: "${M:?set M to the Peregrine tool main.exe}"
: "${RT:?set RT to the CertiRocq C runtime directory}"
: "${GMPZ:?set GMPZ to the directory of the GMP remapping}"
RUN_TIMEOUT=${RUN_TIMEOUT:-3600}
MEM_MAX=${MEM_MAX:-5G}
NUM_BITS=${NUM_BITS:-64}
PROGRAMS=${PROGRAMS:-"small64_verify small64_forged small128_verify small256_verify helios2048_verify helios2048_forged"}
if [ -n "${PEREGRINE_FINDLIB:-}" ]; then
  export OCAMLPATH=$PEREGRINE_FINDLIB${OCAMLPATH:+:$OCAMLPATH}
fi
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
B=$ROOT/_build/default/src
W=$HERE/work
mkdir -p "$W"
cd "$W"
lim() {  # lim cmd...: run under the memory cap MEM_MAX
  if systemd-run --user --scope -q -p MemoryMax=1G true 2>/dev/null; then
    systemd-run --user --scope -q -p MemoryMax="$MEM_MAX" -p MemorySwapMax=0 "$@"
  else
    local kb=$(numfmt --from=iec "$MEM_MAX"); kb=$((kb / 1024))
    (ulimit -v "$kb"; "$@")
  fi
}
tm() {  # tm <log-prefix> cmd...: run capped, recording time and peak memory if possible
  local p=$1; shift
  if [ -x /usr/bin/time ]; then lim /usr/bin/time -v -o "$p.time" "$@"; else lim "$@"; fi
}
ROCQ_FLAGS=(
  -Q "$B/Algebra" Algebra -Q "$B/Utility" Utility -Q "$B/Probability" Probability
  -Q "$B/Crypto" Sigma -Q "$B/Frontend" Frontend -Q "$B/Examples" Examples
  -Q "$W" Bench
  -Q "$F/theories" Peregrine -Q "$F/plugin/theories" Peregrine.Plugin
  -w -all -native-compiler no
)
cp "$GMPZ/GmpZ.v" "$HERE/Helios2048Defs.v" "$HERE/Ballot_LamBox.v" "$W/"
if [ ! -f gmp_z.ast ]; then
  echo "== GmpZ.v"
  tm GmpZ.extract rocq compile "${ROCQ_FLAGS[@]}" GmpZ.v > GmpZ.extract.log 2>&1
fi
echo "== Helios2048Defs.v"
tm Helios2048Defs.compile rocq compile "${ROCQ_FLAGS[@]}" Helios2048Defs.v > Helios2048Defs.log 2>&1
echo "== Ballot_LamBox.v"
tm Ballot_LamBox.extract rocq compile "${ROCQ_FLAGS[@]}" Ballot_LamBox.v > Ballot_LamBox.extract.log 2>&1
for p in $PROGRAMS; do
  echo "== $p"
  python3 "$GMPZ/run_deep.py" "$GMPZ/splice_gmp_z.py" "$p.ast" gmp_z.ast "${p}_z.ast" "${p}_z.attrs" \
    > "$p.splice.log"
  python3 "$GMPZ/run_deep.py" "$GMPZ/stub_axioms.py" "${p}_z.ast" "${p}_z.attrs" \
    "${p}_zs.ast" "${p}_zs.attrs" "${p}_stubs" >> "$p.splice.log"
  # custom attributes (the last field): enable the numeral hoisting
  python3 -c 'import sys; a = open(sys.argv[1]).read().rstrip(); assert a.endswith("())"); open(sys.argv[1], "w").write(a[:-3] + "((((MPfile (\"PeregrineNumerals\")) \"threshold\") \"" + sys.argv[2] + "\")))\n")' \
    "${p}_zs.attrs" "$NUM_BITS"
  tm "$p.peregrine" "$M" c "${p}_zs.ast" --attributes="${p}_zs.attrs" -o "${p}_z.c" > "$p.peregrine.log" 2>&1 \
    || { echo "$p: peregrine failed (see $p.peregrine.log, $p.peregrine.time)"; continue; }
  tm "$p.gcc" gcc -O2 -w -I"$RT" -I"$GMPZ" -I. "${p}_z.c" "$RT/gc_stack.c" \
    "$GMPZ/z_gmp.c" "$HERE/numeral_hook.c" "${p}_stubs.c" "$GMPZ/main_bool.c" -lgmp -o "${p}_z" > "$p.gcc.log" 2>&1 \
    || { echo "$p: gcc failed (see $p.gcc.log)"; continue; }
  tm "$p.run" timeout "$RUN_TIMEOUT" "./${p}_z" > "$p.out" 2> "$p.run.log" || true
  t=$(grep -m1 "Elapsed (wall" "$p.run.time" 2>/dev/null | awk '{print $NF}')
  mem=$(grep -m1 "Maximum resident" "$p.run.time" 2>/dev/null | awk '{print $NF}')
  echo "$p: $(cat "$p.out") (wall ${t:-?}, max RSS ${mem:-?} KB)"
  if [ -n "${MINIGMP:-}" ]; then
    mkdir -p inc && printf '#include "mini-gmp.h"\n' > inc/gmp.h
    tm "$p.emcc" "${EMCC:-emcc}" -O2 -w -Wno-error=int-conversion \
      -Wno-error=incompatible-function-pointer-types -sMEMORY64=1 -sALLOW_MEMORY_GROWTH=1 \
      -sINITIAL_MEMORY=64MB -sENVIRONMENT=node -sSINGLE_FILE=1 \
      -I. -Iinc -I"$MINIGMP" -I"$RT" -I"$GMPZ" "${p}_z.c" "$RT/gc_stack.c" "$GMPZ/z_gmp.c" \
      "$MINIGMP/mini-gmp.c" "$HERE/numeral_hook.c" "${p}_stubs.c" "$GMPZ/main_bool.c" \
      -o "${p}_wasm.js" > "$p.emcc.log" 2>&1 || { echo "$p: emcc failed (see $p.emcc.log)"; continue; }
    sed -i -e 's/function _emscripten_memcpy_big(dest,src,num){/&dest=Number(dest);src=Number(src);num=Number(num);/' \
      -e 's/HEAPU8.copyWithin(dest,src,src+num)}/HEAPU8.copyWithin(dest,src,src+num);return BigInt(dest)}/' \
      -e 's/function _emscripten_resize_heap(requestedSize){/&requestedSize=Number(requestedSize);/' \
      "${p}_wasm.js"
    tm "$p.wasmrun" timeout "$RUN_TIMEOUT" "${NODE:-node}" "${p}_wasm.js" > "$p.wasm.out" 2> "$p.wasmrun.log" || true
    t=$(grep -m1 "Elapsed (wall" "$p.wasmrun.time" 2>/dev/null | awk '{print $NF}')
    mem=$(grep -m1 "Maximum resident" "$p.wasmrun.time" 2>/dev/null | awk '{print $NF}')
    echo "$p (wasm64): $(grep -m1 -E '^(true|false)$' "$p.wasm.out" || echo failed) (wall ${t:-?}, max RSS ${mem:-?} KB)"
  fi
done
