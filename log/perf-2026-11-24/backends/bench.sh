#!/bin/bash
S=${WORK:?set WORK to the build directory}; OUT=${OUTDIR:?set OUTDIR to the log directory}
R="python3 -I $S/exp/rep.py"
. $S/exp/deps.env
PK=$S/exp/sig92/bench/peregrine; PR="small64_verify small64_forged small128_verify small256_verify helios2048_verify helios2048_forged ed25519_verify ed25519_forged ed25519_digest"
cd $PK/work
echo "## wasm64 build $(date +%T)"
for p in $PR; do
  case $p in *_digest) MAIN=../main_z.c;; *) MAIN=../gmpz/main_bool.c;; esac
  emcc -O2 -w -Wno-error=int-conversion -Wno-error=incompatible-function-pointer-types -sMEMORY64=1 -sALLOW_MEMORY_GROWTH=1 -sINITIAL_MEMORY=64MB -sENVIRONMENT=node -sSINGLE_FILE=1 -I. -Iinc -I$MINIGMP -I$RT -I../gmpz -I.. ${p}_z.c $RT/gc_stack.c ../gmpz/z_gmp.c $MINIGMP/mini-gmp.c ../numeral_hook.c ${p}_stubs.c $MAIN -o ${p}_wasm.js > $OUT/emcc-$p.log 2>&1 || echo "$p emcc failed"
done
/bin/sleep 20
{ echo "## ocaml $(date +%T)"; for i in 1 2 3 4 5; do $S/build/default/src/Executable/HeliosBenchcode/main.exe 7 30; done
echo "## C GMP $(date +%T)"; for p in $PR; do $R 5 1800 ./${p}_z; done
echo "## wasm64 $(date +%T)"; for p in $PR; do $R 5 1800 node ${p}_wasm.js; done
echo "## certirocq wasm $(date +%T)"; cd $S/exp/sig91/bench/wasm
for f in Examples.*.wasm; do echo "- $f"; timeout 3600 node bench_wasm2.js $f 5 2>&1 | head -5 | cut -c1-300; done
echo "## cakeml probe $(date +%T)"; cd ../cakeml; export CML_STACK_SIZE=2000 CML_HEAP_SIZE=6000
$R 5 1800 ./modexp16_prog
echo "## cakeml ballot $(date +%T)"; $R 1 21600 ./ballot_prog
echo "## done $(date +%T)"; } > $OUT/results.txt 2>&1
