# Benchmarks

This directory contains the JavaScript baseline benchmark used in the paper's
performance evaluation. It measures ballot encryption and 0/1 disjunctive
proof generation (and verification) using the **unmodified cryptographic
JavaScript served by the Helios voting booth** (`heliosbooth/js/jscrypto/`:
`jsbn` big-integer arithmetic, `elgamal.js` for encryption and disjunctive
Chaum-Pedersen proofs, SHA-1 Fiat-Shamir challenges), at the IACR 2024 Helios
election parameters (2048-bit `p`, 256-bit `q` — the same constants as in
`src/Examples/HeliosTallyIns.v`).

The certified counterpart of this benchmark is the extracted OCaml program in
`src/Executable/HeliosBenchcode/` (built by `dune build`), which encrypts a
ballot and generates the NIZK proofs via `src/Examples/HeliosFrontendIns.v`
with a SHAKE-256 random oracle:

```
dune exec _build/default/src/Executable/HeliosBenchcode/main.exe -- 7 30
```

## Running the JavaScript benchmark

Requirements: Node.js (tested with v26.5.0). The Helios scripts are included
as a git submodule (`bench/helios-server`), pinned to commit
`88621e3196961ec03fe54bbd3a1c2196e715e9a2` — the version used for the numbers
reported in the paper. Fetch it and run:

```
git submodule update --init bench/helios-server
cd bench
node bench_helios_js.js 7 30       # 7 candidates, 30 iterations
```

## What it does

`bench_helios_js.js` loads the booth scripts in the same order as
`heliosbooth/vote.html` into a Node `vm` context, seeds sjcl's PRNG from
Node's CSPRNG, and then, per candidate, performs exactly what the booth's
`helios.js` does when constructing an `EncryptedAnswer`: encrypt `g^0` or
`g^1` with fresh randomness and produce a disjunctive 0/1 encryption proof
with `ElGamal.disjunctive_challenge_generator`. A ballot is `n` such
candidates (default `n = 7`, matching the IACR 2024 election). It reports the
median and mean wall-clock time per ballot for proof generation and for
verification, over the requested number of iterations (default 30, after one
unmeasured warm-up round).

Caveats: the scripts run under Node's V8 rather than a browser (the same
engine as Chrome, so timings transfer), and verification in the JS baseline
recomputes the SHA-1 Fiat-Shamir challenge, whereas the certified verifier
checks the Σ-protocol equations against the challenge in the transcript; the
hash accounts for microseconds and does not affect the comparison.

## WebAssembly benchmark (CertiRocq)

`wasm/WasmBench.v` compiles the terms defined in
`src/Examples/WasmBenchDefs.v` (a fixed 7-candidate ballot, a single vote,
and modular-exponentiation probes, all at the 2048-bit Helios parameters)
to WebAssembly with [CertiRocq](https://github.com/certirocq/certirocq),
and `wasm/bench_wasm.js` times the resulting modules in Node.

**Result summary (Apple M3 Pro, Node 26):** the current CertiRocq/
CertiCoq-Wasm backend computes on constructor-represented binary integers
with bump allocation and no garbage collector. A single 2048-bit modular
multiplication allocates ~50 MB and takes ~0.5 s (measured with the
`helios_wasm_modexp16_bench` probe, `g^65537`: 8.4 s, 840 MB for 17
modular operations). A full 256-bit-exponent exponentiation therefore
needs ~19 GB — beyond the 2 GB wasm32 address space — so the vote and
ballot benchmarks compile but run out of linear memory at real-world
parameters. Certified browser clients at these parameters await primitive
big-integer arithmetic in the verified backend.

### Toolchain setup (exact versions used)

CertiRocq requires Rocq 9.1 and a MetaRocq commit that matches its `main`
branch; the released MetaRocq 1.5.1 does not. The pairing below is known
to build (CertiRocq commit `45a1950`, MetaRocq branch `9.1` commit
`4b201296`):

```
opam switch create certirocq ocaml-base-compiler.4.14.2
opam repo add --switch=certirocq rocq-released https://rocq-prover.org/opam/released
git clone https://github.com/certirocq/certirocq   # tested at 45a1950
git clone -b 9.1 https://github.com/MetaRocq/metarocq
(cd metarocq && git checkout 4b201296)
opam pin -n -y --switch=certirocq ./metarocq
opam pin -n -y --switch=certirocq ./certirocq
brew install gsed        # macOS only; CertiRocq's Makefile needs GNU sed
opam install -y --switch=certirocq rocq-certirocq dune coq-ext-lib
```

### Building the benchmark modules

Compile this repository's theories in the `certirocq` switch. To skip the
~3 h Coqprime primality certificates (their proofs are erased during
compilation, so the generated code is identical), use the fast path
described in the top-level README: in `src/Examples/HeliosTallyIns.v`
replace the proofs of `prime_p`/`prime_q` with `Admitted`, comment out the
`From Examples Require Import primeP primeQ` line, and remove `Coqprime
Bignums` from the theory list in `src/Examples/dune`. Then:

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

Known limitations encountered: a term using `dec_zpstar` (e.g. ballot
verification) cannot be compiled because that constant is `Qed`-opaque and
CertiRocq, unlike extraction, does not unfold opaque proofs — changing it
to `Defined` in `src/Utility/Zpstar.v` would enable it. The backend's
linear memory is capped at 30000 pages (~1.9 GB) by `max_mem_pages` in
CertiRocq's `theories/CodegenWasm/LambdaANF_to_Wasm.v`, and generated code
does not address memory beyond 2 GB.
