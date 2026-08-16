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

Requirements: Node.js (tested with v26.5.0). The Helios scripts are not
vendored here; fetch them first:

```
cd bench
git clone --depth 1 https://github.com/benadida/helios-server.git
node bench_helios_js.js 7 30       # 7 candidates, 30 iterations
```

The numbers reported in the paper were obtained at helios-server commit
`88621e3196961ec03fe54bbd3a1c2196e715e9a2`.

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
