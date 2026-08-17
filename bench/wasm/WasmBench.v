(* Compile the WebAssembly benchmarks with CertiRocq. See ../README.md
   for toolchain setup. The modexp16 probe runs in Node; the vote and
   ballot benchmarks compile but exhaust the backend's linear memory at
   the 2048-bit Helios parameters (see README). *)
From Stdlib Require Import ZArith Vector.
From Examples Require Import WasmBenchDefs.
From MetaRocq.Utils Require Import bytestring.
From CertiRocq.Plugin Require Import CertiRocq.

CertiRocq Compile Wasm helios_wasm_modexp16_bench.
CertiRocq Compile Wasm helios_wasm_vote_bench.
CertiRocq Compile Wasm helios_wasm_ballot_bench.
