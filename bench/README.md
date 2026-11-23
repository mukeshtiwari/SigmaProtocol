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
3. Run `node bench_helios_bigint.js 7 30` in this directory for a modern-JavaScript baseline: the same booth computation (same ElGamal encryption, same DH-tuple proofs, same SHA-1 challenges), reimplemented with JavaScript's native `BigInt` instead of jsbn. This isolates how much of the booth's cost is jsbn's 2005-era pure-JS big-integer arithmetic versus the protocol itself. On the same machine, same session:
   ```
   Helios protocol, native BigInt, n=7, iters=30, all verified=true
   ballot encryption + proofs: median 67.34 ms, mean 69.89 ms
   ballot verification:        median 80.27 ms, mean 82.89 ms
   ```
   (Same-session jsbn numbers: 341.13 ms / 391.64 ms; certified OCaml: 62.09 ms / 48.94 ms.) So most of the jsbn gap is the big-integer library, and the fair headline is: our certified OCaml is on par with a native-`BigInt` reimplementation of the booth (62 vs 67 ms on proving) and still ~5x faster than the JavaScript Helios actually ships.

4. The certified client also runs in a browser. [src/Executable/HeliosJscode](/src/Executable/HeliosJscode) compiles the same extracted `helios_nizk_encrypt_ballot_and_generate_enc_proof` and `helios_verify_encryption_ballot_proof` to JavaScript with js_of_ocaml (big integers through `zarith_stubs_js`, hashing through digestif's pure-OCaml SHA3-256, randomness from Web Crypto, timing from `performance.now`), so no native code is involved. `dune build` produces `_build/default/src/Executable/HeliosJscode/main.bc.js`; run it with `node _build/default/src/Executable/HeliosJscode/main.bc.js 7 30` (with Deno, copy it to a `.cjs` file first: `deno run --allow-all client.cjs 7 30`), or load it from any web page and read the console. Same machine, Node v26.10.0:
   ```
   candidates n = 7, iterations = 30, all ballots verified = true
   ballot encryption + NIZK proofs: median 270.76 ms, mean 261.70 ms
   ballot verification:             median 171.02 ms, mean 171.45 ms
   p bits = 2048, q bits = 256
   ```
   This session ran with a browser consuming about one core, so everything measured in it is roughly 35-40% slower than the numbers above; for a fair ratio, the same session gave certified OCaml 87 ms / 60 ms, native-`BigInt` JS 84 ms / 99 ms and Helios booth jsbn 444 ms / 523 ms (proving / verifying). So the certified code compiled to JavaScript proves a 7-candidate ballot at the real 2048-bit parameters about 3x slower than native OCaml (GMP) or the native-`BigInt` reimplementation, and still about 1.6x faster than the jsbn-based JavaScript the Helios booth ships; unlike the CertiRocq WebAssembly path, it runs at the real parameters. Rerun all four on a quiet machine before quoting absolute numbers together.

## Ed25519

`_build/default/src/Executable/Ed25519code/main.exe 7 30` runs the same certified ballot code (individual 0/1 proofs plus the overall proof, so slightly more work than the Helios rows, which have no overall proof) on Ed25519, i.e. 255-bit curve arithmetic in extended coordinates instead of 2048-bit modular exponentiation. Same machine, same loaded session as the js_of_ocaml row above:
```
benchmark n = 7, iterations = 30, all verified = true
ballot encryption + proofs (individual + overall): median 129.70 ms
ballot verification (individual + overall):        median 58.04 ms
```
The curve arithmetic is the extracted fiat-crypto specification (field elements as zarith integers reduced modulo p after every operation), not an optimised implementation; it is within a factor of two of the 2048-bit Schnorr-group client on the same day.

## P-256

`_build/default/src/Executable/P256code/main.exe 7 10` runs the same ballot code on P-256 (short Weierstrass curve, Jacobian coordinates from fiat-crypto, one field inversion per scalar multiplication at the final conversion):
```
benchmark n = 7, iterations = 10, all verified = true
ballot encryption + proofs (individual + overall): median 255.07 ms
ballot verification (individual + overall):        median 112.37 ms
```
About twice the Ed25519 figures: the Jacobian addition formulas of fiat-crypto's specification are the generic ones (no mixed addition, no precomputation) and each addition also decides two field equalities.

## Belenios verifier

`_build/default/src/Executable/Beleniosverifier/main.exe ELECTION.bel` verifies a Belenios 3.x election archive on Ed25519 with the certified verifier of [BeleniosTally.v](/src/Backend/BeleniosTally.v). Elections generated with Belenios 3.2.0's own tool (`tests/tool/demo.sh`, `demo-n-voters.sh` with `num_voters=300`, `demo-complex.sh`; the three archives are in [src/Executable/Beleniosverifier/data](/src/Executable/Beleniosverifier/data), as `ve3KB6dyuh66fD.bel`, `eyo1Ps3KrSKYJy.bel` and `JDMgPNJoVM6ZuT.bel`), same machine, same session:

| election | ballots | questions | certified verifier (core) | total | `belenios-tool election verify` |
|---|---|---|---|---|---|
| demo (weighted, 3 revotes) | 8 | 2 answers min 0 max 1; 2 answers + blank, min 1 max 1 | 0.43 s | 0.6 s | 0.1 s |
| n-voters | 300 | same | 14.2 s | 22.0 s | 2.2 s |
| complex | 10 | 8 answers min 1 max 1; 131 answers min 1 max 10; 19 answers min 1 max 10 | 9.9 s | 12.1 s | not timed |

Belenios's own verifier uses libsodium's optimised Ed25519 arithmetic; the certified verifier uses the extracted fiat-crypto specification with zarith integers, and each of its points also goes through the order-l check. Every tampered archive from `belenios_tamper.py` (wrong individual, overall or blank proof under a valid signature; wrong decryption factor, result or weight) is rejected.

### Differential testing against belenios-tool

[belenios-diff/](belenios-diff) compares `belenios-tool election verify` (Belenios 3.2.0, commit `50a79aed`, built in its own opam switch) with the certified verifier on 961 elections, reproducibly (`bench/belenios-diff/run.sh`, seed 1, fixtures committed; two runs give byte-identical cases and identical verdicts): 9 honest elections (belenios-tool's, and the same re-cast by an independent Python prover), 749 typed field mutants, 99 structural and encoding mutants, and 104 single-check forgeries with controls (valid proofs built with the voters' credentials and the trustees' keys). Field mutants: all rejected by both. Disagreements: 49, all triaged. `belenios-tool election verify` accepts ballots with invalid proofs or signatures (it discards the promise of its ballot check; ballot stuffing and vote override are accepted, the certified verifier rejects them), and accepts a board whose ballots before a second `EndBallots` are not tallied; the certified driver accepts duplicated events and Ballot events after `EndBallots`, which belenios-tool rejects. Details in its [README](belenios-diff/README.md).

## ElectionGuard verifier

`_build/default/src/Executable/Egverifier/main.exe RECORD_DIRECTORY` verifies an ElectionGuard 2.0 JSON election record with the certified verifier of [ElectionGuardTally.v](/src/Backend/ElectionGuardTally.v) at the 4096-bit parameters of the specification. Test records of the reference implementation (electionguard-kotlin-multiplatform, `egklib/src/commonTest/data/workflow`), same machine, same session:

| record | guardians | ballots | contests × options | certified verifier (core) | total |
|---|---|---|---|---|---|
| allAvailableJson | 3 | 11 cast | 20 × 5 | 61.3 s | 63.6 s |
| chainedJson | 3 | 8 cast + 3 challenged | 20 × 5 | 59.5 s | 65.6 s |

Each option carries a range proof with two branches and each contest a selection-limit proof of the same shape, so a ballot costs about 1,200 exponentiations of 4096-bit numbers to 256-bit exponents; they are computed by the extracted binary exponentiation of [Zpstar.v](/src/Utility/Zpstar.v) over zarith integers, not by GMP's `powm`. The driver's own membership checks (one `powm` per element) are a small part of the total. Every tampered record from `electionguard_tamper.py` (wrong range, selection-limit, coefficient or decryption proof; wrong encrypted tally or decrypted value; swapped options; a cast ballot marked as challenged; a duplicated ballot) is rejected.

### Differential testing against the ElectionGuard reference

[electionguard-diff/](electionguard-diff) runs the certified verifier and the verifier of the reference implementation (electionguard-kotlin-multiplatform, commit `194b9c78`, the final one; JDK 17) on the same records: `bench/electionguard-diff/run.sh WORK_DIR [SEED]` fetches, checks and builds the reference, and runs the campaign twice with the same seed (identical verdict tables required). 779 cases: 7 honest records (5 fixture elections made with the reference's tools, saved, and the reference's 3 test records), 675 field mutants, 42 structural and encoding mutants, and 55 forgeries and protocol scenarios with their controls: ballots of a Python prover (checked against the reference's proofs) with Fiat–Shamir-consistent cheating range and selection-limit proofs counted in a validly decrypted tally, tallies validly decrypted by the trustees that are not the product of the cast ballots, base hashes replaced and used consistently by the reference's own pipeline, and confirmation-chain manipulations. Every honest record and control is accepted by both, every cheating ballot and every tally forgery rejected by both. In all 29 disagreements the reference accepts (or aborts on an unchecked field) and the certified verifier rejects; among them, the reference's verifier accepts a challenged ballot whose published decryption is that of another ciphertext (it checks the decryption proofs against the ciphertexts in the decryption file, not against the challenged ballot: a device that encrypts a wrong choice would pass the voter's challenge), a cast ballot's decryption published as a challenged one, a published ballot left out of the confirmation chain and the tally, a decrypted tally missing a contest, and an encrypted tally naming another election. The campaign found four gaps in the certified side's driver, now fixed: the confirmation chain (verification 7, now with the requirement that the chain list exactly the published ballots) was not checked, nor the challenged ballots' contest-data decryptions (verification 14) and election id, and pre-encrypted ballots were not refused. See [electionguard-diff/README.md](electionguard-diff/README.md).

## Verificatum verifier

`_build/default/src/Executable/Vmnverifier/main.exe protInfo.xml PROOF_DIRECTORY` verifies a mixing session of the Verificatum mix-net (VMN 3.1.0) with the certified verifier of [VerificatumVerifier.v](/src/Backend/VerificatumVerifier.v). The proofs were produced by Verificatum's own demo (three mix-servers, threshold two, pure-Java build) over the certified Helios group (2048-bit p, 256-bit q); same machine, same session:

| ciphertexts | mix-servers | certified verifier (core) | total | `vmnv -mix` (Verificatum, 6 threads) |
|---|---|---|---|---|
| 10 | 3 (2 active) | 0.38 s | 0.45 s | 1.6 s (2.9 s CPU) |
| 1000 | 3 (2 active) | 135.3 s | 137.7 s | 5.9 s (33.4 s CPU) |

Per ciphertext and mix-server the shuffle proof costs about 12 exponentiations of 2048-bit numbers to 256-bit exponents, plus the decryption; the certified verifier computes them with the extracted binary exponentiation of [Zpstar.v](/src/Utility/Zpstar.v) over zarith integers, single-threaded and without simultaneous multi-exponentiation, which is where Verificatum's Java implementation gets its factor of about four in CPU time. Every tampered proof from `verificatum_tamper.py` (a shuffle response or announcement, an output ciphertext, two swapped outputs, the permutation commitment, a decryption factor or reply, a plaintext, the public key) is rejected.

### Differential testing against vmnv

[verificatum-diff/](verificatum-diff) runs Verificatum's own verifier `vmnv` (VMN 3.1.0) next to the certified verifier on the same `vmn`-produced sessions and compares verdicts; `run.sh WORKDIR` builds VMN from the pinned 3.1.0 bundle (sha256 `e848b870…`), generates sessions deterministically (fixed seeds, `vmn`'s demo scripts), runs `campaign.py` and confirms the verdict table is reproducible. Each case is a tampered copy of a proof directory: honest, field mutants by type (group element × g / 1 / random, scalar +1 / 0 / random), structural and encoding mutants (short or long arrays, a malformed byte tree, a non-member element, an out-of-range scalar), protocol tampering (swapped outputs, a replaced output list, a shared permutation commitment, a flipped `CorrectIndices`), and a crafted `A'`-collision forgery. On 79 cases per session both verifiers agree on 75; the four differences are all `vmnv`-accepts / certified-rejects, each sound (identical plaintexts), described in [verificatum-diff/FINDINGS.md](verificatum-diff/FINDINGS.md): a stricter decryption-quorum check and a stricter proof-array parser on our side. The campaign also surfaced a completeness bug in our own driver, now fixed: when the mix-servers share a seed (as `vmn`'s demo does) their proof announcements `A'` collide, and the driver's table of commitments keyed by `A'` returned the wrong one, so the certified verifier rejected an honest session that `vmnv` accepts; the driver now re-derives each proof's commitment from the proof itself.

## U-Prove verifier

`_build/default/src/Executable/Uproveverifier/main.exe [--tamper] [FILE...]` verifies U-Prove tokens and presentation proofs (Cryptographic Specification V1.1 Revision 3, unchanged in Revision 5, P-256, SHA-256) with the certified verifier of [UProveVerifier.v](/src/Backend/UProveVerifier.v) instantiated in [UProveIns.v](/src/Examples/UProveIns.v). The inputs are the twelve official test vectors of the U-Prove C# SDK ([data/](/src/Executable/Uproveverifier/data)); each is one token with five attributes and one presentation proof:

| test vectors | tokens | disclosed | extensions | certified verifier |
|---|---|---|---|---|
| `testvectors_EC_*_doc.txt` (12 files) | 12 | 0, 2 or 5 of 5 | pseudonym and two commitments in 4 files, Device protection in 6 | 349 ms in total, about 30 ms per token |

A token costs one Chaum–Pedersen check (4 exponentiations) for the Issuer's signature and one multi-base reconstruction for the presentation (`2 + |U| + [device]` exponentiations, plus 2 per pseudonym and 3 per commitment), all with the extracted Jacobian scalar multiplication of [P256.v](/src/Curve/P256.v) over zarith integers. With `--tamper` the driver re-verifies the two-attribute file with a changed response, a changed disclosed attribute, a changed signature response and a replaced commitment, and every copy is rejected.

## BBS# verifier

`_build/default/src/Executable/Bbssharpverifier/main.exe N D ITERS` runs the BBS# protocol (ePrint 2025/619) at P-256 with N attributes of which D are disclosed, with the extracted code on both sides, and verifies the presentation with the certified verifier of [BBSSharpVerifier.v](/src/Backend/BBSSharpVerifier.v):

| attributes | disclosed | presentation (holder) | certified verification | paper, Table 3 (verification, N = 10, C library, i7-8565U) |
|---|---|---|---|---|
| 10 | 1 | 54 ms | 31 ms | 1.4 ms ((N + 12) exponentiations at 63 µs) |

The verifier computes N + 12 scalar multiplications (Schnorr: 2, validity proof: N + 6, DLEQ: 4) with the extracted Jacobian arithmetic of [P256.v](/src/Curve/P256.v) over zarith integers, about 2 ms each, against 63 µs for the paper's native implementation; the count of operations is the paper's. Ten tampered presentations (a response of each of the three proofs, a disclosed attribute, B̄ replaced by Ā, pk_Blind replaced by g, Ā = 1, a different nonce, another Issuer key) are rejected.

## Bayer–Groth verifier (Swiss Post)

`_build/default/src/Executable/Bgverifier/main.exe DATA_DIR` verifies the mix-net test vectors of the Swiss Post crypto-primitives library ([data/](/src/Executable/Bgverifier/data), specification 1.6.0, Section 9) with the certified Fiat–Shamir verifier of [BayerGrothVerifier.v](/src/Backend/BayerGrothVerifier.v) instantiated at the 3072-bit group in [BayerGrothIns.v](/src/Examples/BayerGrothIns.v), and runs the extracted honest prover on fresh shuffles. Times of the certified verifier (Apple M-series laptop, extracted OCaml over zarith, modular exponentiation with 3071-bit exponents by the extracted `Zpow_mod`):

| fixture | (m, n, l) | certified verification |
|---|---|---|
| shuffle argument (Algorithm 9.12) | (1, 2, 1) | 254 ms |
| | (2, 3, 2) | 799 ms |
| | (8, 8, 2) | 8.0 s |
| | (8, 8, 4) | 12.4 s |
| product argument (9.19) | (1, 2, 1) / (2, 3, 2) / (8, 8, 2) / (8, 8, 4) | 60 / 288 / 902 / 902 ms |
| Hadamard argument (9.21) | (2, 3, 2) / (8, 8, 2) / (8, 8, 4) | 204 / 703 / 704 ms |
| zero argument (9.23) | (1, 2, 1) / (2, 3, 2) / (8, 8, 2) / (8, 8, 4) | 96 / 129 / 416 / 419 ms |
| single value product argument (9.26) | (1, 2, 1) / (2, 3, 2) / (8, 8, 2) / (8, 8, 4) | 61 / 84 / 206 / 201 ms |
| multi-exponentiation argument (9.16) | (1, 2, 1) / (2, 3, 2) / (8, 8, 2) / (8, 8, 4) | 134 / 342 / 2869 / 4612 ms |

| fresh shuffle, extracted prover and verifier | (m, n, l) | prover | certified verification |
|---|---|---|---|
| | (1, 2, 1) | 1.4 s | 248 ms |
| | (2, 3, 2) | 5.2 s | 791 ms |
| | (4, 4, 1) | 12.8 s | 1.5 s |

The recomputed RecursiveHash challenges (x, y, z of the shuffle argument and the challenge of each sub-argument) agree with the values recorded in the fixtures in every case; all 6 + 15 fixture cases are accepted and 32 tampered arguments rejected (84 checks in all, about 2 minutes). The shuffle verifier's cost is dominated by the N·(l+1) exponentiations of ∏ C_i^{x^i} and of the multi-exponentiation check, each with a full 3071-bit exponent; the Java library uses the same operation count with native multi-exponentiation.

### Differential testing against the Swiss Post Java verifier

[swisspost-diff/](swisspost-diff) runs the Swiss Post prover and verifier (the submodule [crypto-primitives/](crypto-primitives), pinned at commit 94a8438, the commit of the fixtures) next to the certified verifier on fresh cases:

```sh
git submodule update --init bench/crypto-primitives
bench/swisspost-diff/build.sh bench/crypto-primitives BUILD_DIR        # JDK >= 25, Maven
bench/swisspost-diff/swisspost_diff.py BUILD_DIR WORK_DIR [--stages 123] [--java M,N,L[,K] ...] [--ocaml M,N,L ...]
```

`build.sh` compiles the library (and the fixture parsers of its test suite) with [BgDiff.java](swisspost-diff/BgDiff.java) as one module, since the shuffle argument's prover and verifier are package-private; the upstream pom needs an in-house Maven plugin, so Maven only fetches the dependency jars. Every case gets the Swiss Post verdict (an exception of its argument checks counts as a rejection) and the certified verdict of `main.exe --diff` (a shape or parse error of the trusted driver counts as a rejection), each certified run on its own file, in parallel; the verdicts are written to `WORK_DIR/stage*.tsv`.

1. *Swiss Post prover, field mutations.* An honest argument at the 3072-bit group for each (m, n, l), and k = |pk| ≥ l; one random occurrence of every field of the context (pk, h, g_i), the statement and the argument is mutated (group elements: times g, 1, inverse, random, swapped with a sibling; exponents: +1, 0, negated, random; the statement: two ciphertexts swapped, C' := C). On the honest cases the challenges x, y, z are compared too.
2. *Extracted prover (`main.exe --gen`).* Honest arguments with degenerate prover randomness (all 0, all 1) or statements (identity permutation, no re-encryption, identity ciphertexts, all ciphertexts equal), which both must accept; and arguments of the prover run on a witness that does not explain the statement (not a permutation, a wrong re-encryption exponent, a changed plaintext, another shuffle), whose Fiat–Shamir challenges are all derived from the transcript, so verification reaches the algebraic checks; both must reject.
3. *Structure and encoding.* Every vector one element short or long, the Hadamard argument removed, N not a multiple of m, non-minimal and negative encodings, exponents ≥ q or < 0, integers that are not group elements (0, p, p − 1, x + p, −x), another generator or q in the context.

With the defaults (stage 1: (m, n, l[, k]) = (1,2,1), (1,3,3), (2,2,1), (2,3,2), (3,4,2), (4,4,1), (8,8,2), (1,2,1,3), (2,3,2,4); stage 2: (1,2,1), (2,2,1), (2,3,2), (3,3,2); stage 3 on the shapes with m ≤ 3): 1,233 + 48 + 348 cases, 0 disagreements. All honest arguments of either prover are accepted by both verifiers, with the same challenges; every mutated, malformed or cheating one is rejected by both. The Swiss Post verifier also accepts the arguments of the extracted prover with all-zero randomness.

Found in the certified side's trusted driver, and fixed:

- *A public key longer than the ciphertexts* (k > l, which the Swiss Post library allows: all of pk is hashed, its first l elements encrypt) made the driver segfault: it took l = |pk|, and the extracted verifier read missing components of length-indexed vectors. `--diff` now takes l from the ciphertexts, checks every shape the extracted verifier relies on before calling it (1 ≤ l ≤ k, all ciphertexts of size l + 1, |C'| = |C|, m | N, 2 ≤ n ≤ |ck|), and passes the first l elements of pk; honest arguments with k > l are now accepted.
- *Negative encodings* (a first byte with the top bit set, a negative two's-complement number to Java) were read as unsigned by the parser, which accepted a group element that the Swiss Post parser rejects; [ast.ml](/src/Executable/Bgverifier/parsing/ast.ml) now rejects them.

Differences that are not disagreements: the Swiss Post library refuses a commitment key containing 1 (h = 1 or g_i = 1) with an exception, where the certified verifier, taking the key as given, rejects because the argument no longer verifies; and its verifier derives the commitment key itself in production (`getVerifiableCommitmentKey`), which this test does not compare. The Java verifier takes about 1 s of CPU per case (parallel), the certified verifier 0.3–8 s (single-threaded).

*Single-check forgeries* ([forge.py](swisspost-diff/forge.py), `forge.py BUILD_DIR WORK_DIR [M,N,L ...]`). Most checks of the sub-argument verifiers compare a response with the commitments; responses are not hashed, so the field mutations above break one equation at a time and cover them. Seven checks instead compare a hashed value with a constant or with the statement: c_d[m+1] = 1 (zero argument, 9.23), b̃₀ = ã₀ and b̃ₙ₋₁ = x·b (single value product, 9.26), c_B0 = c_A0 and c_B{m−1} = c_b (Hadamard, 9.21), c_B[m] = 1 and E_m = C (multi-exponentiation, 9.16). Changing such a value changes the challenge and breaks every equation, so mutation never isolates them. `forge.py` implements the provers of the specification in Python (its RecursiveHash reproduces the challenges of the Swiss Post test vectors) and runs them on false statements arranged so that every equation holds and only the targeted check fails (the zero statement sums to e ≠ 0, the product chain starts at a₀ + e, c_b commits to b + e, C is multiplied by Enc(g^e; σ), absorbed by E_m or by b_m = e); a verifier without that check would accept a false statement. Each forgery comes with its control (e = 0, a true statement). The Swiss Post sub-verifiers (`SubDiff.java`) and the certified ones (`main.exe --diff-sub KIND FILE`) are run on both. On (m, n, l) = (1,2,1), (2,2,1), (2,3,2), (3,4,2), (4,3,1): 66 cases, every control accepted and every forgery rejected by both, the Swiss Post verifier reporting exactly the targeted check ("c_B_0 must equal c_A_0.", "E_m must equal C.", "cB_m must equal one.", …) and no other. So both implementations contain each of the seven checks, and each is necessary.

*Stage 4, the production path* (`--stages 4 [--prod N,L[,K] ...] [--prod-mutants K]`, not in the default `123`). Shuffles of the production `MixnetService.genVerifiableShuffle` for N ∈ {2, 3, 7, 16, 100, 257, 1000}, l ∈ {1, 3}, and (N, l, k) = (100, 1, 3), under both optimization modes. `COMPUTATION_OPTIMIZED`, the default, always takes m = 1, n = N. `MEMORY_OPTIMIZED` takes m the largest divisor of N up to √N: 4×4, 10×10, and 25×40 for N = 16, 100, 1000; for prime N it also takes m = 1, and those shapes are generated once. The context holds the verifiable commitment key (`getVerifiableCommitmentKey(n)`). Each honest shuffle is followed by 6 stage-1 mutants of randomly chosen fields. The Java verdicts of `ShuffleArgumentService` (key from the file) and of the production `MixnetService.verifyShuffle` (which derives the key itself, so the 8 commitment-key mutants are not compared on that side) are compared with each other and with `main.exe --diff`.

Results: 154 cases (22 honest), 0 disagreements. All 22 honest arguments are accepted by both, with the same challenges, and all 132 mutants are rejected by both; one of them, h = 1, by an exception on the Java side. The two Java paths agree on every case. Generating and Java-verifying the largest case (N = 1000, l = 3, m = 1) takes about 53 s. The certified verifier takes 157 s for it, single-threaded, in 46 MB. The whole stage took 31 minutes of wall-clock time, mostly the certified side and the sequential production verifier on the N = 1000 cases.

## Swiss Post zero-knowledge proofs (differential testing)

[swisspost-zkp-diff/](swisspost-zkp-diff) compares the Schnorr, exponentiation, plaintext equality and decryption proof verifiers of the Swiss Post crypto-primitives library (submodule [crypto-primitives/](crypto-primitives), specification 1.6.0, Section 10) with a certified verifier: all four are Maurer proofs in compact form (e, z), verified by reconstructing c' = y^{−e}·φ(z) and comparing e with the RecursiveHash of (f, y, c', h_aux), which is `verify_rows` of [BBSSharpVerifier.v](/src/Backend/BBSSharpVerifier.v) for the rows of φ. [SwissPostZkpIns.v](/src/Examples/SwissPostZkpIns.v) instantiates it at the 3072-bit group of [BayerGrothIns.v](/src/Examples/BayerGrothIns.v) (instantiation and extraction only; `verify_zkp_ins_accepting` covers K = 1 by a padding column of base 1, with no axioms beyond the group's primality certificate), and [Executable/Swisspostzkp](/src/Executable/Swisspostzkp/main.ml) decodes the test-vector format, builds the rows and computes the hash.

```sh
dune build src/Executable/Swisspostzkp/main.exe
bench/swisspost-zkp-diff/build.sh bench/crypto-primitives BUILD_DIR        # JDK >= 25, Maven
bench/swisspost-zkp-diff/swisspost_zkp_diff.py BUILD_DIR WORK_DIR [COUNT]
```

The certified verifier accepts the 9 Swiss Post test vectors, recomputing every challenge. With COUNT = 25 (per kind: the test vectors, 25 + 3 honest proofs of the Swiss Post prover, the last 3 under the generator g = 4, and 8–10 proofs of a third prover written from the specification for edge statements: y = 1, x = 0, bases 1 or repeated, n = 20, h = h′, h = 1, r = 0, γ = 1, sk = 0, ℓ = 10, k > ℓ; then every field mutated, the auxiliary information changed, the proof replayed on another statement, and structural and encoding cases): 1,158 + 1,727 + 2,209 + 2,129 = 7,223 cases, 0 disagreements, about 31 minutes (mostly the Java verifier, 7,900 s of CPU). Every honest proof is accepted by both, every mutated or malformed one rejected by both, with these exceptions, all of which both verifiers share and which follow from the specification: the key elements pk_ℓ, …, pk_{k−1} of a decryption proof are neither hashed nor in φ, so changing them leaves a proof valid (Swiss Post's own test vector `k-greater-than-l` is `decryption-5` with one more key element and the same proof); an exponentiation proof does not use the generator of the context; and with every base 1 an exponentiation proof's response is not bound.

Found on the certified side and fixed: the driver at first required the generator g = 2, while the specification allows any g ∈ G_q ∖ {1}; it now takes g from the context, and honest proofs under g = 4 are accepted. Not covered: `VerifyDecryptions` (the batch with the γ = γ′ check) and `GenVerifiableDecryptions`, and the provers' zero knowledge.

### Swiss Post Verifier on the E2E election

[swisspost-e2e/verifier/](swisspost-e2e/verifier) runs the Swiss Post Verifier 1.7.1.0 (the auditors' software) headlessly on the synthetic election `Post_E2E_DEV` of the testdata repository 1.6.1.0: all 43 verifications (24 setup, 19 tally) pass on the untampered election. [tamper.py](swisspost-e2e/verifier/tamper.py) builds 29 protocol-level tampered copies and re-signs every changed payload with the dev key of the component that signs it ([Tamper.java](swisspost-e2e/verifier/Tamper.java), using the e-voting-libraries domain classes; validated by re-signing unchanged payloads, accepted, and by a changed payload with its old signature, rejected): ballot boxes exchanged or relabelled, control component payloads exchanged between nodes, ballot boxes or elections, confirmed votes dropped, duplicated, added or reordered, the tally component's votes payload, decrypted votes and write-ins changed, the eCH-0222 result file changed, single proof fields changed, a payload deleted. Every tampered election is rejected; the one accepted change, reordering the confirmed votes, is a no-op by the specification (Algorithm 6.1 sorts them). Observations: a failed tally decryption proof can surface as an UNEXPECTED_ERROR of plaintext processing instead of a proof failure. Attacks that need valid proofs for a tampered statement need key shares or electoral board passwords the dataset does not publish. Details: [swisspost-e2e/verifier/README.md](swisspost-e2e/verifier/README.md).

### Certified checking of the E2E election's tally

[swisspost-e2e/certified/](swisspost-e2e/certified) checks every proof of the tally of the synthetic election `Post_E2E_DEV` (Swiss Post testdata 1.6.1.0) with the certified verifiers, instantiated at the election's 3072-bit group in [BayerGrothE2EIns.v](/src/Examples/BayerGrothE2EIns.v) and [SwissPostZkpE2EIns.v](/src/Examples/SwissPostZkpE2EIns.v) (generated; the primality of q is assumed, an axiom). `e2e_extract.py` is the protocol wiring of Verifier Specification 1.7.1 (4.1, 4.2) and System Specification 1.6.1 (6.1, 6.10): the shuffle inputs (the confirmed votes ordered and padded, then each control component's partially decrypted output), the combined keys, the decryption keys and i_aux, the commitment key of Algorithm 9.6, and the checks without proofs (key combination, the control components' agreement on the confirmed votes, payload identifiers, γ′ = γ, the decrypted votes in order). [Swissposte2e](/src/Executable/Swissposte2e/main.ml) verifies the statements. On the untampered election: 20 shuffles, 60 decryption proofs and 57 checks verified, in 12 s. On the 29 re-signed tampered copies above it agrees with the Swiss Post Verifier on all 21 scenarios within its scope; the 8 others (signatures, decoded votes and write-ins, the eCH-0222 file) are outside it. See its [README](swisspost-e2e/certified/README.md).

## IVXV (Estonia)

[ivxv-diff/](ivxv-diff) compares Estonia's IVXV (`valimised/ivxv`, branch `published`, commit `2785872f`, KOV2025; CC BY-NC-ND 3.0, fetched at run time and never modified), Verificatum's `vmnv` 3.1.0 and certified verifiers instantiated at the campaign's safe-prime group and at RFC 3526 group 14 (generated by [mkins.py](ivxv-diff/mkins.py), primality assumed): Verificatum shuffling sessions (key width 5) verified by `vmnv`, by IVXV's auditor in both of its modes and by the certified Terelius–Wikström verifier (per key-width component); IVXV's Java decryption proofs as the auditor verifies them; and the decryption proofs of IVXV's Go core library. `bench/ivxv-diff/run.sh` pins and builds everything; two runs with the same seed give byte-identical result tables. 408 + 424 + 184 cases: every honest proof and control accepted, every Fiat–Shamir-consistent proof of a false statement rejected, by every verifier. Disagreements: IVXV's default auditor shuffle verifier does not check the B equation at index 0 (its threaded mode does), so a changed reply k_B,0 is accepted by the default mode only; `vmnv -shuffle` exits 0 on failed proofs and does not check `ShuffledCiphertexts.bt` against the last party's output; and the IVXV readers accept non-canonical and non-reduced encodings that the certified boundary rejects. See [ivxv-diff/README.md](ivxv-diff/README.md).

## Primality certificates

Every prime of the case studies is proved in Rocq by a certificate checked by Coqprime, so no instantiation carries a primality hypothesis. Two generators live in this directory:

- [pocklington.py](pocklington.py) (sympy) emits Pocklington certificates when `N − 1` factors: Helios's `q` and `p`, ElectionGuard's `q = 2^256 − 189`, P-256's `p` and `n`, Ed25519's `l` (fiat-crypto's own certificate).
- [ecpp2coq.py](ecpp2coq.py) converts an elliptic-curve (ECPP) certificate produced by [PARI/GP](https://pari.math.u-bordeaux.fr/) (`write(file, primecert(N))`, PARI 2.17.4) into a chain of Coqprime `Ell_certif` steps, each certifying `N_i` from a curve over `Z/N_i` whose order is `s_i` times the next prime, down to a prime below 2^64 that gets a Pocklington certificate. It is used where `N − 1` has no known factorisation: the 3071-bit Swiss Post `q` ([primeQSP.v](/src/Examples/primeQSP.v)) and the 4096-bit ElectionGuard `p` ([primePEG.v](/src/Examples/primePEG.v)). The Swiss Post `p = 2q + 1` is then proved by Pocklington's criterion inside [BayerGrothIns.v](/src/Examples/BayerGrothIns.v).

| prime | bits | certificate | generation (PARI) | kernel check (Rocq, `dune build`) |
|---|---|---|---|---|
| Swiss Post `q` | 3071 | 107 elliptic steps + Pocklington tail | 54 s | 2.5 h (9,300 s CPU) |
| ElectionGuard `p` | 4096 | 147 elliptic steps + Pocklington tail | 172 s | 7.8 h (27,900 s CPU) |

The elliptic-curve checker computes over Bignums' BigN, so these lemmas, like the Helios certificates, depend on the primitive-integer axioms `Uint63Axioms.*` reported by [assumptions.sh](assumptions.sh). Regenerate with

```
echo 'default(parisize, "1G"); write("cert.txt", primecert(N))' | gp -q
python3 bench/ecpp2coq.py cert.txt prime_name > src/Examples/primeName.v
```

## Helios's own Python verifier

To put the certified verifier's 39 s / 51 s IACR runs in context, [verify_iacr_python.py](verify_iacr_python.py) runs the same end-to-end verification using Helios's own Python crypto code (`helios/crypto/algs.py` from the pinned submodule, imported verbatim; the script builds a stub package in a temp dir because `helios/__init__.py` needs Django settings). It performs the same checks as the certified verifier: every ballot's disjunctive 0/1 proofs, homomorphic aggregation, the trustees' Chaum-Pedersen decryption proofs and Schnorr proofs of knowledge, the public-key product, and the plaintext tally. Setup and run (needs the submodule from step 2 above; `hval2023`/`hval2024` are the election public keys from [HeliosTallyIns.v](/src/Examples/HeliosTallyIns.v)):

```
uv venv .venv-helios --python 3.13
uv pip install -p .venv-helios/bin/python pycryptodome
.venv-helios/bin/python verify_iacr_python.py \
  ../src/Executable/HeliosDatacode/IACR2024.txt <hval2024>
```

Same machine, same session (certified OCaml verifier via `_build/default/src/Executable/HeliosVerifiercode/main.exe <year> < IACR<year>.txt`):

| election | ballots | certified OCaml (total) | Helios Python crypto (total) |
|---|---|---|---|
| IACR 2023 | 848, 6 candidates | 38.3 s | 222.8 s |
| IACR 2024 | 932, 7 candidates | 52.7 s | 288.8 s |

Both agree on every verdict (all ballots valid, all trustee proofs valid, tally consistent, public keys consistent). The certified verifier is about 5.5-5.8x faster than the same checks written in Helios's own Python (CPython arbitrary-precision ints vs GMP through zarith); the point is not the speedup but that the certified code is not the slow option even against the reference implementation's language of choice.

### Differential testing against Helios

[helios-diff/](helios-diff) compares Helios's own verification code (`algs.py` and `electionalgs.py` of the pinned submodule, unmodified: `EncryptedVote.verify`, `Tally.add_vote`, `Tally.verify_decryption_proofs`, `verify_sk_proof`, `Tally.decrypt_from_factors`) with the certified verifier (`HeliosVerifiercode/diff.exe`), component by component, on 734 elections: 7 honest (five generated with ballots from the Helios booth JS and from the certified prover, IACR 2023 and 2024), 509 field mutants, 165 structural and encoding mutants, 53 tally-level tamperings. `bench/helios-diff/run.sh --twice` reproduces it (SEED = 1, booth ballots as fixtures) and checks that two runs give identical verdicts. Both accept every honest election; there is no case the certified verifier accepts and Helios rejects; the 70 cases Helios accepts and the certified verifier rejects are 15 where Helios ignores extra proofs or decryption factors or accepts an unreduced response r + q, and 55 where the certified parser, by design, refuses non-canonical JSON or integer encodings. Three defects of the certified side's parser (recorded challenges of decryption proofs and proofs of knowledge discarded, ballots not bound to the election hash and UUID, non-decimal integers accepted) were found and fixed; see the [README](helios-diff/README.md).

## CakeML (fully verified pipeline)

We also compiled the same fixed-challenge ballot term (`helios_wasm_ballot_bench` from [WasmBenchDefs.v](/src/Examples/WasmBenchDefs.v)) with the [Peregrine CakeML backend](https://github.com/peregrine-project/cakeml-backend) and the [verified CakeML compiler](https://cakeml.org/) (v3400, arm8). This is the strongest assurance point of our three pipelines: Rocq proofs, verified MetaRocq erasure, a CakeML backend that comes with correctness proofs, and a fully verified compiler down to ARM64 machine code -- no unverified extraction and no unverified compiler anywhere. The price is that integers stay in constructor representation (there is no GMP mapping like OCaml extraction has), so on the same machine:

| pipeline | `g^65537` probe (17 modular ops) | full ballot (n = 7) |
|---|---|---|
| OCaml + GMP (unverified extraction) | ~66 microseconds | 62 ms |
| CakeML, fully verified to ARM64 | 1.8 s | 49.3 min |
| CertiCoq-Wasm (next section) | 8.4 s | out of memory |

CakeML is about 4.6 times faster than the wasm backend on identical constructor arithmetic (native code plus a real garbage collector, so the full ballot actually *completes*, in 2959 s), and 4-5 orders of magnitude slower than GMP-backed OCaml. A planned limb-arithmetic backend (a separate project, not linked for anonymous review) would close most of that gap for both verified backends.

To reproduce: `opam install rocq-cakeml-extraction` (works with the released MetaRocq on Rocq 9.0/9.1, no commit pinning needed), download `cake-arm8-64.tar.gz` from the [CakeML releases](https://github.com/CakeML/cakeml/releases) and run `make cake` in it, then in [cakeml/](cakeml/):

```
rocq c -Q ../../_build/default/src/Utility Utility \
  -Q ../../_build/default/src/Algebra Algebra \
  -Q ../../_build/default/src/Probability Probability \
  -Q ../../_build/default/src/Crypto Sigma \
  -Q ../../_build/default/src/Frontend Frontend \
  -Q ../../_build/default/src/Backend Backend \
  -Q ../../_build/default/src/Examples Examples Driver.v > ballot.exp
python3 wrap_prog.py ballot.exp ballot_prog.sexp
CML_STACK_SIZE=2000 CML_HEAP_SIZE=6000 \
  cake --sexp=true --skip_type_inference=true --target=arm8 \
  < ballot_prog.sexp > ballot_prog.S
cc -O2 ballot_prog.S basis_ffi.c -o ballot_prog
CML_STACK_SIZE=2000 CML_HEAP_SIZE=6000 time ./ballot_prog
```

Use the quick compilation trick (admitted primality, see the next section) before extracting, otherwise `tmQuoteRec` drags the multi-megabyte Coqprime certificates through the pipeline.

Gotchas we ran into with v0.1.0 of the backend (reported upstream, handled by [cakeml/Driver.v](cakeml/Driver.v) and [cakeml/wrap_prog.py](cakeml/wrap_prog.py)): the backend emits global bindings in reverse dependency order, so the driver reverses them (`List.rev`), otherwise programs crash at runtime on unbound forward references; the backend emits no `Dtype` declarations, so `wrap_prog.py` scrapes constructor names and arities from the term and declares them all in one datatype (fine, because type inference is skipped anyway); cake's sexp lexer is ASCII-only, so unicode identifiers (our sources use subscript names like `m₁`) must be transliterated; and `--skip_type_inference=true` is required because erased code is not ML-typable.

## WebAssembly (CertiRocq)

We also tried to benchmark the WebAssembly path at the same 2048 bit parameters, using [CertiRocq](https://github.com/certirocq/certirocq) to compile the terms in [WasmBenchDefs.v](/src/Examples/WasmBenchDefs.v) (a fixed 7-candidate ballot, a single vote, and small modular exponentiation probes). The short version: everything compiles, but the generated code cannot execute at real-world parameters. CertiRocq computes on Rocq's binary-represented integers with no garbage collector, so a single 2048 bit modular multiplication allocates about 50 MB and takes about 0.5 seconds. A full exponentiation (256 bit exponent, roughly 384 multiplications) would need about 19 GB, well past the 2 GB WebAssembly address space, so the vote and ballot modules run out of memory before finishing. Running certified clients in the browser at real parameters has to wait for primitive big-integer arithmetic in the verified backend. The `g^65537` probe (17 modular operations) does run:
   ```
   Examples.WasmBenchDefs.helios_wasm_modexp16_bench.wasm: iters=3 median 8377.27 ms, min 8258.96 ms, max 8500.51 ms
     mem used: 839.6 MB
   ```

### Reduced parameters: where the 2 GB limit binds

To show that the WebAssembly client is functional and to locate the exact point at which the linear-memory cap binds, [WasmBenchSmallDefs.v](/src/Examples/WasmBenchSmallDefs.v) defines the same fixed 7-candidate ballot over small Schnorr groups (64-, 128-, and 256-bit p, generated by [wasm/gen_small_params.py](wasm/gen_small_params.py); the small primality proofs are Admitted, which is fine because they are erased during compilation, same reasoning as the quick-compilation trick). Compiled with [wasm/WasmBenchSmall.v](wasm/WasmBenchSmall.v) and run with `node bench_wasm.js <file>.wasm 5`:

| parameters | full ballot (n = 7) | ballot + verification |
|---|---|---|
| 64-bit p, 32-bit q | 0.53 s, 147 MB | 1.41 s, 316 MB |
| 128-bit p, 64-bit q | 13.1 s, 1226 MB | out of memory |
| 256-bit p, 128-bit q | out of memory (single vote: 16.7 s, 1274 MB) | out of memory |
| 2048-bit p, 256-bit q (Helios) | out of memory | out of memory |

So the certified WebAssembly client completes an entire ballot, end to end, at up to 128-bit parameters, and the wasm-compiled verifier accepts the wasm-compiled ballot (the `result` global of the verification module is the encoding of `true`; note the unboxed constructor encoding is `true = 3`, `false = 1`). Memory grows about 8x per parameter doubling (4x per multiplication times 2x exponent length), which extrapolates cleanly to the ~19 GB a 2048-bit exponentiation would need. The limit is purely the constructor representation of integers, not the protocol code: primitive big-integer arithmetic in the verified backend (the same planned limb-arithmetic backend) is the fix.

Because WasmBenchSmallDefs.v does not depend on Coqprime, compiling it needs no quick-compilation trick -- only the dune edit (remove `Coqprime Bignums` from [src/Examples/dune](/src/Examples/dune), since the certirocq switch does not have them). Then, with the toolchain below:
   ```
   opam exec --switch=certirocq -- dune build _build/default/src/Examples/WasmBenchSmallDefs.vo
   cd bench/wasm
   ulimit -s 65520
   B=../../_build/default
   opam exec --switch=certirocq -- rocq c \
     -Q $B/src/Utility Utility -Q $B/src/Algebra Algebra \
     -Q $B/src/Probability Probability -Q $B/src/Crypto Sigma \
     -Q $B/src/Frontend Frontend -Q $B/src/Backend Backend \
     -Q $B/src/Examples Examples WasmBenchSmall.v
   node bench_wasm.js Examples.WasmBenchSmallDefs.Small64.ballot_bench.wasm 5
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
     -Q $B/src/Probability Probability -Q $B/src/Crypto Sigma \
     -Q $B/src/Frontend Frontend -Q $B/src/Backend Backend \
     -Q $B/src/Examples Examples WasmBench.v
   node bench_wasm.js Examples.WasmBenchDefs.helios_wasm_modexp16_bench.wasm 3
   ```

Two gotchas we ran into, so you do not have to: `dec_zpstar` in [Zpstar.v](/src/Utility/Zpstar.v) used to be `Qed`, which CertiRocq rejects as an axiom (extraction unfolds opaque constants, CertiRocq does not) -- it is `Defined` now, so both the encryption and the verification terms compile. And the backend caps its linear memory at 30000 pages (about 1.9 GB), see `max_mem_pages` in CertiRocq's `theories/CodegenWasm/LambdaANF_to_Wasm.v`; patching the binary past 2 GB does not help because the generated code does not address memory beyond that.

## Gentoo elections (the real-world corpus of the Schulze paper)

`python3 bench/gentoo_leak.py` reads the master ballots that Gentoo
publishes for its Council and Trustees elections (`bench/gentoo-votes/`,
copied from https://anongit.gentoo.org/git/proj/elections.git at commit
`4ca0b003`, 2026-07-19) and prints, per election, the number of ballots and
candidates, the number of ballots whose ranking no other voter cast, the
number of candidate pairs with a margin of at most two, the Schulze
(beatpath) winner and Gentoo's own first-pass winner (Schwartz sequential
dropping, `countify`). On all 41 elections the two winners agree. The
`--tex` flag prints the rows of the paper's leak table, and `--positions`
writes `bench/gentoo-votes/positions-<election>.txt`, the position vector
of every ballot (first line: `m` and the candidate names).

The council elections are run through the extracted Schulze protocol at
the 2048-bit Helios parameters (`src/Examples/SchulzeBenchIns.v`) in two
steps, so that an interrupted run loses nothing:

```
dune exec src/Executable/SchulzeGentoocode/encrypt.exe -- \
  bench/gentoo-votes/positions-council-202306.txt bench/gentoo-board/council-202306.txt
dune exec src/Executable/SchulzeGentoocode/main.exe -- bench/gentoo-board/council-202306.txt
```

`encrypt.exe` is the voters: it encrypts every ballot with its NIZK proofs
under a voter-bound oracle (voter `k` has credential `voter-k`) and appends
it to the bulletin board file, one decimal line per ballot (`Board.write_ballot`
documents the format); run again on an existing board, it encrypts only the
missing voters. `main.exe` is the verifier and the trustees: it verifies every
ballot under its voter's oracle, checks that a ballot replayed under another
credential is rejected, aggregates, decrypts the margins with the (fixed,
single-trustee) key of the instance, certifies the Schulze winner and verifies
the certificate, printing every time. Boards are 100-600 MB per election and
are not committed (`bench/gentoo-board/` is ignored).

`dune exec src/Executable/SchulzeGentoocode/gentoo3.exe -- positions-file board-file [--no-cert]`
runs the same election through the simplified batched ballot
(`src/Frontend/SchulzeSimple.v`): voters, verifier and trustees in one
process, since a ballot takes about a second rather than minutes. It
encrypts every ballot under the voter-bound oracle, writes the board (for
its size; `bench/gentoo-board3/`, ignored), verifies, checks the replay,
aggregates, decrypts, and, unless `--no-cert`, certifies the winner and
verifies the certificate, which does not depend on the ballot protocol. The
log format is that of `encrypt.exe` and `main.exe`, so `bench/gentoo_table.py`
summarises these runs too.

`dune exec src/Executable/SchulzeBenchcode/batched.exe -- m iterations`
measures the batched ballot (`src/Frontend/SchulzeBatched.v`) at the same
parameters: one prover pass with the final Fiat–Shamir challenges,
verification, the size, and two tamper checks (a changed ciphertext and a
changed commitment must be rejected). The commitment keys are hashed to the
order-q subgroup from fixed labels.

`dune exec src/Executable/SchulzeBenchcode/simple.exe -- m iterations`
measures the simplified batched ballot (`src/Frontend/SchulzeSimple.v`: one
commitment key, the derived position key, one zero argument) the same way,
with a third tamper check (a changed bit commitment, which breaks the
opening of C₀). At m = 17 on the same machine: 180 KB, 0.67 s to prove,
1.5 s to verify, against 352 KB, 4.2 s, 5.7 s for `batched.exe`.

`python3 bench/gentoo_table.py <logs of the Gentoo runs>` turns the output of
`encrypt.exe` and `main.exe` on each council election into the rows of the
paper's table (year, m, N, median encryption and verification time, accepted
ballots, certificate times and size, winner).
