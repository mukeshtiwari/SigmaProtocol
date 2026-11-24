#!/usr/bin/env bash
# Extract the approval ballots of Ballot_LamBox.v (Schnorr groups) and
# Ed25519Ballot_LamBox.v (Ed25519) with Peregrine, remap Z, positive and N to
# GMP integers, compile the C with gcc and run it.
#
# deps.sh fetches the pinned CertiRocq runtime, mini-gmp and peregrine-tool
# and prints RT, MINIGMP and PEREGRINE_TOOL: eval "$(bench/peregrine/deps.sh)".
#
# Usage, after `dune build _build/default/src/Examples/WasmBenchSmallDefs.vo
# _build/default/src/Examples/Ed25519Ins.vo` in the repository root:
#   F=<peregrine-frontend> RT=<CertiRocq C runtime> \
#   PEREGRINE_TOOL=<checkout of https://github.com/peregrine-project/peregrine-tool
#   at branch numeral-literals (commit 13c701b or a descendant), built with
#   dune; it has the numeral-hoisting pass> or M=<its main.exe> \
#   [GMPZ=<the GMP remapping, default bench/peregrine/gmpz>] \
#   [PEREGRINE_FINDLIB=<findlib dir holding rocq-peregrine/META>] \
#   [PROGRAMS="small64_verify ..."] [VFILES="Ballot_LamBox.v ..."] \
#   [SIGMA_BUILD=<dune build of src, default _build/default/src>] \
#   [RUN_TIMEOUT=3600] [MEM_MAX=5G] [VALGRIND=valgrind] bench/peregrine/build.sh
#
# VFILES lists the extraction files to compile (default: all three; empty
# reuses earlier extractions), PROGRAMS the extracted programs to compile and
# run.  A program prints its result, a bool; the programs *_digest return an
# integer instead, printed in decimal by main_z.c.  A program p_bedrock is the
# program p with Ed.fast_smul remapped (remap_const.py) to the verified
# bedrock2 scalar multiplication of ed25519_bedrock.c, through the glue
# ed25519_glue.c; a program p_bedrockl moreover has Zl.add, Zl.sub, Zl.mul
# and Zl.opp remapped to the verified bedrock2 arithmetic modulo l of
# fieldl_bedrock.c, through the glue zl_glue.c.  The programs p_jasmin and
# p_jasminl are p_bedrock and p_bedrockl with the same bedrock2 functions
# printed as Jasmin (ed25519_bedrock.jazz, fieldl_bedrock.jazz;
# bedrock/jasmin/EmitJasmin.v) and compiled by jasminc -auto-spill (JASMINC,
# default jasminc) instead of printed as C and compiled by gcc; the glue is
# compiled from copies in work/jasmin, next to files ed25519_bedrock.c and
# fieldl_bedrock.c that include bedrock_jasmin.h, the declarations of the
# Jasmin export functions.
#
# A program p_ct (constant-time build; for the Ed25519 programs) represents
# scalars of Zl.F and points of Ed.G as 32- and 64-byte values: every
# operation of Zl and Ed that the program uses, the conversions of
# Examples/Ed25519Ins.v, the secret input [secret] and the publication
# functions of Ed25519Ballot_LamBox.v are remapped (remap_const.py) to
# zl_ct_glue.c and ed25519_ct_glue.c, which compute with the verified bedrock2
# code of fieldl_bedrock.c and ed25519_bedrock.c; check_abstract.py then
# checks that the program computes with no operation of Zmod, of the curve or
# of Zl and Ed beyond the remapped ones.  The secrets (gen_secrets.py writes
# them from Ed25519Ballot_LamBox.v) enter from a buffer that main_ct.c marks
# undefined for valgrind's memcheck; with VALGRIND=<valgrind> set, each *_ct
# program also runs under memcheck, which reports every branch and memory
# address that depends on a secret.  ed25519_digest_ct, ed25519_verify_ct and
# ed25519_forged_ct report none; ed25519_branching_digest_ct, the ballot of
# the prover that branches on the votes, reports one branch per vote (the
# control of the test).
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
# fieldl_bedrock.c; for the *_ct programs remap_const.py, check_abstract.py,
# gen_secrets.py, the glue zl_ct_glue.c and ed25519_ct_glue.c (with
# ct_values.h), and the printed fieldl_bedrock.c and ed25519_bedrock.c.
# For the *_jasmin and *_jasminl programs, in place of bedrock2's C printer
# and gcc on the printed C: the Jasmin printer (bedrock/jasmin, unverified),
# jasminc and the assembler; bedrock_jasmin.h.  The MINIGMP build does not
# cover them (jasminc emits x86-64 assembly).
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
GMPZ=${GMPZ:-$(cd "$(dirname "$0")" && pwd)/gmpz}
RUN_TIMEOUT=${RUN_TIMEOUT:-3600}
MEM_MAX=${MEM_MAX:-5G}
NUM_BITS=${NUM_BITS:-64}
PROGRAMS=${PROGRAMS:-"small64_verify small64_forged small128_verify small256_verify helios2048_verify helios2048_forged ed25519_verify ed25519_forged ed25519_digest ed25519_verify_ct ed25519_forged_ct ed25519_digest_ct ed25519_branching_digest_ct"}
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
case " $PROGRAMS " in *_jasmin\ *|*_jasminl\ *|*_ctj\ *)
  # the Jasmin modules, compiled once; the glue copies next to the files
  # ed25519_bedrock.c and fieldl_bedrock.c that include bedrock_jasmin.h
  JW=$W/jasmin
  mkdir -p "$JW"
  cp "$HERE/ed25519_glue.c" "$HERE/zl_glue.c" "$HERE/ed25519_ct_glue.c" "$HERE/zl_ct_glue.c" "$JW/"
  for m in ed25519_bedrock fieldl_bedrock; do
    printf '#include "bedrock_jasmin.h"\n' > "$JW/$m.c"
    echo "== $m.jazz"
    tm "$m.jasminc" "${JASMINC:-jasminc}" -auto-spill "$HERE/$m.jazz" -o "$JW/$m.s" > "$m.jasminc.log" 2>&1 \
      || { echo "$m.jazz: jasminc failed (see $W/$m.jasminc.log)"; exit 1; }
  done ;;
esac
for p in $PROGRAMS; do
  echo "== $p"
  q=${p%_bedrockl}; q=${q%_bedrock}; q=${q%_jasminl}; q=${q%_jasmin}; q=${q%_ctj}; q=${q%_ct}
  MAINFLAGS=()
  case $q in *_digest) MAIN=$HERE/main_z.c ;; *) MAIN=$GMPZ/main_bool.c ;; esac
  case $p in *_ct|*_ctj)
    MAIN=$HERE/main_ct.c
    case $q in *_digest) MAINFLAGS=(-DCT_RESULT_Z) ;; esac ;;
  esac
  python3 "$GMPZ/run_deep.py" "$GMPZ/splice_gmp_z.py" "$q.ast" gmp_z.ast "${p}_z.ast" "${p}_z.attrs" \
    > "$p.splice.log"
  python3 "$GMPZ/run_deep.py" "$GMPZ/stub_axioms.py" "${p}_z.ast" "${p}_z.attrs" \
    "${p}_zs.ast" "${p}_zs.attrs" "${p}_stubs" >> "$p.splice.log"
  EXTRA=()
  case $p in *_bedrock|*_bedrockl|*_jasmin|*_jasminl)
    # *_bedrock: Ed.fast_smul by the bedrock2 scalar multiplication
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/remap_const.py" "${p}_zs.ast" "${p}_zs.attrs" \
      "${p}_zs.ast" "${p}_zs.attrs" ed25519_glue.h \
      Curve.Ed25519.Ed25519.Ed.fast_smul=ed25519_fast_smul/2 >> "$p.splice.log"
    case $p in
      *_jasmin|*_jasminl) EXTRA=("$JW/ed25519_glue.c" "$JW/ed25519_bedrock.s") ;;
      *) EXTRA=("$HERE/ed25519_glue.c") ;;
    esac ;;
  esac
  case $p in *_bedrockl|*_jasminl)
    # *_bedrockl: also Zl.add, Zl.sub, Zl.mul, Zl.opp by the bedrock2
    # arithmetic modulo l of fieldl_bedrock.c
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/remap_const.py" "${p}_zs.ast" "${p}_zs.attrs" \
      "${p}_zs.ast" "${p}_zs.attrs" zl_glue.h \
      Curve.Ed25519.Ed25519.Zl.add=zl_add/2 Curve.Ed25519.Ed25519.Zl.sub=zl_sub/2 \
      Curve.Ed25519.Ed25519.Zl.mul=zl_mul/2 Curve.Ed25519.Ed25519.Zl.opp=zl_opp/1 >> "$p.splice.log"
    case $p in
      *_jasminl) EXTRA+=("$JW/zl_glue.c" "$JW/fieldl_bedrock.s") ;;
      *) EXTRA+=("$HERE/zl_glue.c") ;;
    esac ;;
  esac
  case $p in *_ct|*_ctj)
    # *_ct: scalars and points as fixed-size byte values (zl_ct_glue.c,
    # ed25519_ct_glue.c), the secrets read from a buffer, the published
    # values declared public; then check that no operation on Zmod or on the
    # curve is left in the program
    python3 "$HERE/gen_secrets.py" "$HERE/Ed25519Ballot_LamBox.v" ct_secrets.h >> "$p.splice.log"
    Z=Curve.Ed25519.Ed25519.Zl E=Curve.Ed25519.Ed25519.Ed B=Bench.Ed25519Ballot_LamBox.Ed25519Ballot
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/remap_const.py" "${p}_zs.ast" "${p}_zs.attrs" \
      "${p}_zs.ast" "${p}_zs.attrs" zl_ct_glue.h \
      "?$Z.zero=zlc_zero/0/pure" "?$Z.one=zlc_one/0/pure" "?$Z.add=zlc_add/2" "?$Z.sub=zlc_sub/2" \
      "?$Z.mul=zlc_mul/2" "?$Z.opp=zlc_opp/1" "?$Z.Fdec=zlc_eq/2/pure" "?$Z.of_Z=zlc_of_Z/1" \
      "?$Z.to_Z=zlc_to_Z/1" $B.secret=zlc_secret/1 $B.publish_F=zlc_publish/1/pure \
      "?Examples.Ed25519Ins.x=zlc_secret_key/0" >> "$p.splice.log"
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/remap_const.py" "${p}_zs.ast" "${p}_zs.attrs" \
      "${p}_zs.ast" "${p}_zs.attrs" ed25519_ct_glue.h \
      "?$E.B=edc_base/0/pure" "?$E.gid=edc_gid/0/pure" "?$E.gop=edc_gop/2" "?$E.ginv=edc_ginv/1" \
      "?$E.gpow_fast=edc_gpow/2" "?$E.Gdec=edc_eq/2/pure" "?Examples.Ed25519Ins.point_to_Z=edc_to_Z/1" \
      Examples.Ed25519Ins.h=edc_public_key/0 \
      $B.publish_G=edc_publish/1/pure >> "$p.splice.log"
    GMPZ=$GMPZ python3 "$GMPZ/run_deep.py" "$HERE/check_abstract.py" "${p}_zs.ast" \
      Stdlib.Zmod Fiat Curve.Ed25519 >> "$p.splice.log" \
      || { echo "$p: check_abstract failed (see $p.splice.log)"; continue; }
    case $p in
      # *_ctj: the same glue over the Jasmin build of the bedrock2 functions
      *_ctj) EXTRA=("$JW/zl_ct_glue.c" "$JW/ed25519_ct_glue.c" "$JW/fieldl_bedrock.s" "$JW/ed25519_bedrock.s") ;;
      *) EXTRA=("$HERE/zl_ct_glue.c" "$HERE/ed25519_ct_glue.c") ;;
    esac ;;
  esac
  # custom attributes (the last field): enable the numeral hoisting
  python3 -c 'import sys; a = open(sys.argv[1]).read().rstrip(); assert a.endswith("())"); open(sys.argv[1], "w").write(a[:-3] + "((((MPfile (\"PeregrineNumerals\")) \"threshold\") \"" + sys.argv[2] + "\")))\n")' \
    "${p}_zs.attrs" "$NUM_BITS"
  tm "$p.peregrine" "$M" c "${p}_zs.ast" --attributes="${p}_zs.attrs" -o "${p}_z.c" > "$p.peregrine.log" 2>&1 \
    || { echo "$p: peregrine failed (see $p.peregrine.log, $p.peregrine.time)"; continue; }
  tm "$p.gcc" gcc -O2 -w -I"$RT" -I"$GMPZ" -I"$HERE" -I. "${p}_z.c" "$RT/gc_stack.c" \
    "$GMPZ/z_gmp.c" "$HERE/numeral_hook.c" "${p}_stubs.c" "${EXTRA[@]}" "${MAINFLAGS[@]}" "$MAIN" -lgmp -o "${p}_z" > "$p.gcc.log" 2>&1 \
    || { echo "$p: gcc failed (see $p.gcc.log)"; continue; }
  tm "$p.run" timeout "$RUN_TIMEOUT" "./${p}_z" > "$p.out" 2> "$p.run.log" || true
  t=$(grep -m1 "Elapsed (wall" "$p.run.time" 2>/dev/null | awk '{print $NF}')
  mem=$(grep -m1 "Maximum resident" "$p.run.time" 2>/dev/null | awk '{print $NF}')
  r=$(cat "$p.out"); [ ${#r} -gt 40 ] && r="${#r} digits, sha256 $(sha256sum < "$p.out" | cut -c1-16)"
  echo "$p: $r (wall ${t:-?}, max RSS ${mem:-?} KB)"
  case $p in *_ct|*_ctj) if [ -n "${VALGRIND:-}" ]; then
    lim "$VALGRIND" --tool=memcheck --track-origins=yes --error-limit=no "./${p}_z" \
      > "$p.memcheck.out" 2> "$p.memcheck.log" || true
    n=$(sed -n 's/.*ERROR SUMMARY: \([0-9]*\) errors.*/\1/p' "$p.memcheck.log")
    echo "$p (memcheck): ${n:-?} errors, output $(cmp -s "$p.out" "$p.memcheck.out" && echo unchanged || echo differs)"
  fi ;; esac
  if [ -n "${MINIGMP:-}" ] && case $p in *_jasmin|*_jasminl|*_ctj) false ;; *) true ;; esac; then
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
