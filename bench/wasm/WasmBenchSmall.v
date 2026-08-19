(* Compile the reduced-parameter WebAssembly benchmarks with CertiRocq.
   See ../README.md for toolchain setup. Unlike WasmBench.v, the
   definitions in WasmBenchSmallDefs.v do not depend on Coqprime (the
   small primality proofs are Admitted and erased), so no
   quick-compilation trick is needed. *)
From Stdlib Require Import ZArith Vector.
From Examples Require Import WasmBenchSmallDefs.
From MetaRocq.Utils Require Import bytestring.
From CertiRocq.Plugin Require Import CertiRocq.

CertiRocq Compile Wasm Small64.ballot_bench.
CertiRocq Compile Wasm Small64.ballot_verify_bench.
CertiRocq Compile Wasm Small128.ballot_bench.
CertiRocq Compile Wasm Small128.ballot_verify_bench.
CertiRocq Compile Wasm Small256.vote_bench.
CertiRocq Compile Wasm Small256.ballot_bench.
CertiRocq Compile Wasm Small256.ballot_verify_bench.
