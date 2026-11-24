#!/usr/bin/env bash
# Extract the approval ballots of Ballot_LamBox.v (Schnorr groups) and
# Ed25519Ballot_LamBox.v (Ed25519) with Peregrine, remap Z, positive and N to
# GMP integers, compile the C with gcc and run it.
#
# Usage, after `dune build _build/default/src/Examples/WasmBenchSmallDefs.vo
# _build/default/src/Examples/Ed25519Ins.vo` in the repository root:
#   F=<peregrine-frontend> RT=<CertiRocq C runtime> \
#   PEREGRINE_TOOL=<checkout of https://github.com/peregrine-project/peregrine-tool
#   at branch numeral-literals (commit 13c701b or a descendant), built with
#   dune; it has the numeral-hoisting pass> or M=<its main.exe> \
#   GMPZ=<dir with GmpZ.v, z_gmp.c, z_gmp.h, splice_gmp_z.py, splice_locked.py,
#         stub_axioms.py, run_deep.py, main_bool.c> \
#   [PEREGRINE_FINDLIB=<findlib dir holding rocq-peregrine/META>] \
#   [PROGRAMS="small64_verify ..."] [VFILES="Ballot_LamBox.v ..."] \
#   [SIGMA_BUILD=<dune build of src, default _build/default/src>] \
#   [RUN_TIMEOUT=3600] [MEM_MAX=5G] bench/peregrine/build.sh
#
# VFILES lists the extraction files to compile (default: all three; empty
# reuses earlier extractions), PROGRAMS the extracted programs to compile and
# run.  A program prints its result, a bool; the programs *_digest return an
# integer instead, printed in decimal by main_z.c.  A program p_bedrock is the
# program p with Ed.fast_smul remapped (remap_const.py) to the verified
# bedrock2 scalar multiplication of ed25519_bedrock.c, through the glue
# ed25519_glue.c; a program p_bedrockl moreover has Zl.add, Zl.sub, Zl.mul
# and Zl.opp remapped to the verified bedrock2 arithmetic modulo l of
# fieldl_bedrock.c, through the glue zl_glue.c.
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
# gcc and GMP; for the *_bedrock programs also remap_const.py, the glue
# ed25519_glue.c and bedrock2's C printer, which produced ed25519_bedrock.c;
# for the *_bedrockl programs moreover the glue zl_glue.c and the printed
# fieldl_bedrock.c.
set -euo pipefail
: "${F:?set F to the Peregrine frontend directory}"
# Peregrine with the numeral-hoisting pass (ENumeralHoist), first in commit
# 13c701b of branch numeral-literals of peregrine-tool.
PEREGRINE_NUMERALS_COMMIT=13c701be7fa272c3e57f7d7211b4ff897095860c
if [ -n "${PEREGRINE_TOOL:-}" ]; then
  if ! git -C "$PEREGRINE_TOOL" merge-base --is-ancestor "$PEREGRINE_NUMERALS_COMMIT" HEAD 2>/dev/null; then
    echo "PEREGRINE_TOOL must be at commit $PEREGRINE_NUMERALS_COMMIT (branch numeral-literals) or a descendant" >&2
    exit 2
  fi
  M=${M:-$PEREGRINE_TOOL/_build/default/bin/main.exe}
fi
: "${M:?set PEREGRINE_TOOL to a peregrine-tool checkout (branch numeral-literals), or M to its main.exe}"
: "${RT:?set RT to the CertiRocq C runtime directory}"
: "${GMPZ:?set GMPZ to the directory of the GMP remapping}"
RUN_TIMEOUT=${RUN_TIMEOUT:-3600}
MEM_MAX=${MEM_MAX:-5G}
NUM_BITS=${NUM_BITS:-64}
PROGRAMS=${PROGRAMS:-"small64_verify small64_forged small128_verify small256_verify helios2048_verify helios2048_forged ed25519_verify ed25519_forged ed25519_digest"}
VFILES=${VFILES-"Helios2048Defs.v Ballot_LamBox.v Ed25519Ballot_LamBox.v"}
if [ -n "${PEREGRINE_FINDLIB:-}" ]; then
  export OCAMLPATH=$PEREGRINE_FINDLIB${OCAMLPATH:+:$OCAMLPATH}
fi
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/../.." && pwd)
B=${SIGMA_BUILD:-$ROOT/_build/default/src}
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
  -Q "$B/Fiat" Fiat -Q "$B/Curve" Curve
  -Q "$W" Bench
  -Q "$F/theories" Peregrine -Q "$F/plugin/theories" Peregrine.Plugin
  -w -all -native-compiler no
)
cp "$GMPZ/GmpZ.v" "$W/"
if [ ! -f gmp_z.ast ]; then
  echo "== GmpZ.v"
  tm GmpZ.extract rocq compile "${ROCQ_FLAGS[@]}" GmpZ.v > GmpZ.extract.log 2>&1
fi
for v in $VFILES; do
  echo "== $v"
  cp "$HERE/$v" "$W/"
  tm "${v%.v}.compile" rocq compile "${ROCQ_FLAGS[@]}" "$v" > "${v%.v}.log" 2>&1
done
for p in $PROGRAMS; do
  echo "== $p"
  q=${p%_bedrockl}; q=${q%_bedrock}
  case $q in *_digest) MAIN=$HERE/main_z.c ;; *) MAIN=$GMPZ/main_bool.c ;; esac
  python3 "$GMPZ/run_deep.py" "$GMPZ/splice_gmp_z.py" "$q.ast" gmp_z.ast "${p}_z.ast" "${p}_z.attrs" \
    > "$p.splice.log"
  python3 "$GMPZ/run_deep.py" "$GMPZ/stub_axioms.py" "${p}_z.ast" "${p}_z.attrs" \
    "${p}_zs.ast" "${p}_zs.attrs" "${p}_stubs" >> "$p.splice.log"
  EXTRA=()
  if [ "$q" != "$p" ]; then
    # *_bedrock: Ed.fast_smul by the bedrock2 scalar multiplication
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/remap_const.py" "${p}_zs.ast" "${p}_zs.attrs" \
      "${p}_zs.ast" "${p}_zs.attrs" ed25519_glue.h \
      Curve.Ed25519.Ed25519.Ed.fast_smul=ed25519_fast_smul/2 >> "$p.splice.log"
    EXTRA=("$HERE/ed25519_glue.c")
  fi
  case $p in *_bedrockl)
    # *_bedrockl: also Zl.add, Zl.sub, Zl.mul, Zl.opp by the bedrock2
    # arithmetic modulo l of fieldl_bedrock.c
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/remap_const.py" "${p}_zs.ast" "${p}_zs.attrs" \
      "${p}_zs.ast" "${p}_zs.attrs" zl_glue.h \
      Curve.Ed25519.Ed25519.Zl.add=zl_add/2 Curve.Ed25519.Ed25519.Zl.sub=zl_sub/2 \
      Curve.Ed25519.Ed25519.Zl.mul=zl_mul/2 Curve.Ed25519.Ed25519.Zl.opp=zl_opp/1 >> "$p.splice.log"
    EXTRA+=("$HERE/zl_glue.c") ;;
  esac
  # custom attributes (the last field): enable the numeral hoisting
  python3 -c 'import sys; a = open(sys.argv[1]).read().rstrip(); assert a.endswith("())"); open(sys.argv[1], "w").write(a[:-3] + "((((MPfile (\"PeregrineNumerals\")) \"threshold\") \"" + sys.argv[2] + "\")))\n")' \
    "${p}_zs.attrs" "$NUM_BITS"
  tm "$p.peregrine" "$M" c "${p}_zs.ast" --attributes="${p}_zs.attrs" -o "${p}_z.c" > "$p.peregrine.log" 2>&1 \
    || { echo "$p: peregrine failed (see $p.peregrine.log, $p.peregrine.time)"; continue; }
  tm "$p.gcc" gcc -O2 -w -I"$RT" -I"$GMPZ" -I"$HERE" -I. "${p}_z.c" "$RT/gc_stack.c" \
    "$GMPZ/z_gmp.c" "$HERE/numeral_hook.c" "${p}_stubs.c" "${EXTRA[@]}" "$MAIN" -lgmp -o "${p}_z" > "$p.gcc.log" 2>&1 \
    || { echo "$p: gcc failed (see $p.gcc.log)"; continue; }
  tm "$p.run" timeout "$RUN_TIMEOUT" "./${p}_z" > "$p.out" 2> "$p.run.log" || true
  t=$(grep -m1 "Elapsed (wall" "$p.run.time" 2>/dev/null | awk '{print $NF}')
  mem=$(grep -m1 "Maximum resident" "$p.run.time" 2>/dev/null | awk '{print $NF}')
  r=$(cat "$p.out"); [ ${#r} -gt 40 ] && r="${#r} digits, sha256 $(sha256sum < "$p.out" | cut -c1-16)"
  echo "$p: $r (wall ${t:-?}, max RSS ${mem:-?} KB)"
  if [ -n "${MINIGMP:-}" ]; then
    mkdir -p inc && printf '#include "mini-gmp.h"\n' > inc/gmp.h
    tm "$p.emcc" "${EMCC:-emcc}" -O2 -w -Wno-error=int-conversion \
      -Wno-error=incompatible-function-pointer-types -sMEMORY64=1 -sALLOW_MEMORY_GROWTH=1 \
      -sINITIAL_MEMORY=64MB -sENVIRONMENT=node -sSINGLE_FILE=1 \
      -I. -Iinc -I"$MINIGMP" -I"$RT" -I"$GMPZ" -I"$HERE" "${p}_z.c" "$RT/gc_stack.c" "$GMPZ/z_gmp.c" \
      "$MINIGMP/mini-gmp.c" "$HERE/numeral_hook.c" "${p}_stubs.c" "${EXTRA[@]}" "$MAIN" \
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
