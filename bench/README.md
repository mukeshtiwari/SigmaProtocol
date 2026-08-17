# Benchmarks

Benchmarks for the paper. We measure our certified OCaml code against the hand-written JavaScript that the [Helios voting booth](https://github.com/benadida/helios-server) serves to voters, at the real Helios parameters (2048 bit p, 256 bit q, same as [HeliosTallyIns.v](/src/Examples/HeliosTallyIns.v)). All the numbers below are from an Apple M3 Pro laptop.

1. Run `dune exec _build/default/src/Executable/HeliosBenchcode/main.exe -- 7 30` (7 candidates, 30 iterations) to benchmark the certified OCaml code. It encrypts an approval ballot and generates the NIZK proofs (SHAKE-256 as random oracle), and then verifies them, using the functions from [HeliosFrontendIns.v](/src/Examples/HeliosFrontendIns.v). You will see an output like this:
   ```OCaml
   candidates n = 7, iterations = 30, all ballots verified = true
   ballot encryption + NIZK proofs: median 61.82 ms, mean 62.29 ms
   ballot verification:             median 48.64 ms, mean 49.52 ms
   p bits = 2048, q bits = 256
   ```
2. Run `git submodule update --init bench/helios-server` (from the repository root) to fetch the Helios booth code. It is pinned to commit `88621e3196961ec03fe54bbd3a1c2196e715e9a2`, the version we used for the paper. Then run `node bench_helios_js.js 7 30` in this directory (we tested with Node v26.5.0). It loads the booth scripts (jsbn big integers, elgamal.js, SHA-1 Fiat-Shamir) in the same order as `heliosbooth/vote.html` and does exactly what the booth does per candidate: encrypt g^0 or g^1 and produce a disjunctive 0/1 proof. You will see an output like this:
   ```
   Helios booth JS (jsbn), n=7, iters=30, all verified=true
   ballot encryption + proofs: median 333.70 ms, mean 334.11 ms
   ballot verification:        median 384.85 ms, mean 387.06 ms
   ```
   So our certified OCaml code is about 5 times faster than the JavaScript that Helios actually ships. Two caveats: this runs under Node's V8 rather than a browser (same engine as Chrome, so the timings transfer), and the JS verification recomputes the SHA-1 challenge while our verifier checks the equations against the challenge in the transcript (the hash is microseconds, it does not change the picture).

## WebAssembly (CertiRocq)

We also tried to benchmark the WebAssembly path at the same 2048 bit parameters, using [CertiRocq](https://github.com/certirocq/certirocq) to compile the terms in [WasmBenchDefs.v](/src/Examples/WasmBenchDefs.v) (a fixed 7-candidate ballot, a single vote, and small modular exponentiation probes). The short version: everything compiles, but the generated code cannot execute at real-world parameters. CertiRocq computes on Rocq's binary-represented integers with no garbage collector, so a single 2048 bit modular multiplication allocates about 50 MB and takes about 0.5 seconds. A full exponentiation (256 bit exponent, roughly 384 multiplications) would need about 19 GB, well past the 2 GB WebAssembly address space, so the vote and ballot modules run out of memory before finishing. Running certified clients in the browser at real parameters has to wait for primitive big-integer arithmetic in the verified backend. The `g^65537` probe (17 modular operations) does run:
   ```
   Examples.WasmBenchDefs.helios_wasm_modexp16_bench.wasm: iters=3 median 8377.27 ms, min 8258.96 ms, max 8500.51 ms
     mem used: 839.6 MB
   ```

To reproduce it, first set up the toolchain. CertiRocq needs Rocq 9.1 and a MetaRocq commit that matches its main branch (the released MetaRocq 1.5.1 does not have `EImplementLazyForce` and the current MetaRocq 9.1 head has moved past CertiRocq, so pin the exact commits below -- this pairing is known to build, CertiRocq `45a1950` with MetaRocq `4b201296`):
   ```
   opam switch create certirocq ocaml-base-compiler.4.14.2
   opam repo add --switch=certirocq rocq-released https://rocq-prover.org/opam/released
   git clone https://github.com/certirocq/certirocq
   git clone -b 9.1 https://github.com/MetaRocq/metarocq
   (cd metarocq && git checkout 4b201296)
   opam pin -n -y --switch=certirocq ./metarocq
   opam pin -n -y --switch=certirocq ./certirocq
   brew install gsed        # macOS only, CertiRocq's Makefile needs GNU sed
   opam install -y --switch=certirocq rocq-certirocq dune coq-ext-lib
   ```

Then compile this repository in the certirocq switch. Use the quick compilation trick from the [top-level README](/README.md) (admit `prime_p` and `prime_q` in [HeliosTallyIns.v](/src/Examples/HeliosTallyIns.v), comment out the primeP primeQ import, and also remove `Coqprime Bignums` from the theory list in [src/Examples/dune](/src/Examples/dune)) -- the primality proofs are erased during compilation anyway, so the generated code is identical. Then:
   ```
   opam exec --switch=certirocq -- dune build _build/default/src/Examples/WasmBenchDefs.vo
   cd bench/wasm
   ulimit -s 65520          # CertiRocq compilation needs a large stack
   B=../../_build/default
   opam exec --switch=certirocq -- rocq c \
     -Q $B/src/Utility Utility -Q $B/src/Algebra Algebra \
     -Q $B/src/Probability Probability -Q $B/src/Crypto Crypto \
     -Q $B/src/Frontend Frontend -Q $B/src/Backend Backend \
     -Q $B/src/Examples Examples WasmBench.v
   node bench_wasm.js Examples.WasmBenchDefs.helios_wasm_modexp16_bench.wasm 3
   ```

Two gotchas we ran into, so you do not have to: `dec_zpstar` in [Zpstar.v](/src/Utility/Zpstar.v) used to be `Qed`, which CertiRocq rejects as an axiom (extraction unfolds opaque constants, CertiRocq does not) -- it is `Defined` now, so both the encryption and the verification terms compile. And the backend caps its linear memory at 30000 pages (about 1.9 GB), see `max_mem_pages` in CertiRocq's `theories/CodegenWasm/LambdaANF_to_Wasm.v`; patching the binary past 2 GB does not help because the generated code does not address memory beyond that.
