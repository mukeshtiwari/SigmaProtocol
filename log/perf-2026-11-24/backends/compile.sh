#!/bin/bash
ulimit -s 65520
S=${WORK:?set WORK to the build directory}
step() { n=$1; shift; echo "### $n start $(date +%T)"; "$@" > $S/exp/log-$n.txt 2>&1; echo "### $n exit $? $(date +%T)"; }
B=$S/exp/sig91/_build/default/src
Q="-Q $B/Utility Utility -Q $B/Algebra Algebra -Q $B/Probability Probability -Q $B/Crypto Sigma -Q $B/Frontend Frontend -Q $B/Backend Backend -Q $B/Examples Examples"
wasm() { cd $S/exp/sig91/bench/wasm && opam exec --switch=peregrine -- rocq c $Q $1; }
cml() { cd $S/exp/sig91/bench/cakeml && opam exec --switch=peregrine -- rocq c $Q Driver.v; }
cfront() { eval "$(cat $S/exp/deps.env)"; cd $S/exp/sig92 && M=$S/peregrine/pt-nollvm/_build/default/bin/main.exe GNUTIME=$S/exp/shim/gnutime PATH=$S/exp/shim:$PATH RUN_TIMEOUT=1800 PROGRAMS="small64_verify small64_forged small128_verify small256_verify helios2048_verify helios2048_forged ed25519_verify ed25519_forged ed25519_digest" env -u PEREGRINE_TOOL -u MINIGMP opam exec --switch=sigma92 -- bash bench/peregrine/build-macos.sh; }
step wasmsmall wasm WasmBenchSmall.v
step wasm2048 wasm WasmBench.v
step cakeml-extract cml
step c cfront
