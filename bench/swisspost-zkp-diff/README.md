# Swiss Post zero-knowledge proofs: differential testing

Compares the zero-knowledge proof verifiers of the Swiss Post
crypto-primitives library (submodule [../crypto-primitives](../crypto-primitives),
commit 94a8438; specification 1.6.0, Section 10) with the certified verifier
of [SwissPostZkpIns.v](/src/Examples/SwissPostZkpIns.v), driven by
[Executable/Swisspostzkp](/src/Executable/Swisspostzkp/main.ml).

| proof | algorithm | rows of φ (K witnesses, m equations) |
|---|---|---|
| Schnorr | 10.3 | K = 1, m = 1: `[g]` |
| exponentiation | 10.9 | K = 1, m = n: `[g_i]` |
| plaintext equality | 10.12 | K = 2, m = 3: `[g, 1], [1, g], [h, h'^-1]` |
| decryption | 10.6 | K = ℓ, m = 2ℓ: `g·e_i`, `γ·e_i` |

All four are Maurer proofs in compact form (e, z): the verifier reconstructs
c'_i = y_i^{-e} · ∏_j B_{i,j}^{z_j} and checks e = RecursiveHash(f, y, c', h_aux).
The certified part is `verify_rows` of
[BBSSharpVerifier.v](/src/Backend/BBSSharpVerifier.v) at the 3072-bit group of
[BayerGrothIns.v](/src/Examples/BayerGrothIns.v), padded with a column of base 1
so that its accepting-transcript theorem (stated for K ≥ 2) covers every proof
(`verify_zkp_ins_accepting`, no axioms beyond those of the group's primality
certificate). Trusted: the driver's decoding, the rows and targets above, and
the RecursiveHash closures.

```sh
git submodule update --init bench/crypto-primitives
dune build src/Executable/Swisspostzkp/main.exe          # opam switch with cryptokit, yojson
bench/swisspost-zkp-diff/build.sh bench/crypto-primitives BUILD_DIR      # JDK >= 25, Maven
bench/swisspost-zkp-diff/swisspost_zkp_diff.py BUILD_DIR WORK_DIR [COUNT]
_build/default/src/Executable/Swisspostzkp/main.exe KIND FILE           # one file, KIND as below
```

`ZkpDiff.java` (compiled into the library's module, package
`internal.zeroknowledgeproofs`) generates honest proofs with the library's
provers (`gen KIND FIXTURE OUT COUNT`) and verifies files through the
production entry points of `ZeroKnowledgeProofService` (`verify KIND FILE`).
KIND is `schnorr`, `exponentiation`, `plaintext-equality` or `decryption`;
the files are in the format of the library's test vectors
(`src/test/resources/zeroknowledgeproofs/verify-KIND.json`).

The orchestrator runs, per kind: the Swiss Post test vectors; COUNT honest
proofs of the Swiss Post prover (random sizes, k ≥ ℓ, random auxiliary
information with empty, Unicode, NUL and long strings) and COUNT/8 under the
generator g = 4; proofs of a third prover written in the script from the
specification for statements at the edges (y = 1, x = 0, a base 1, repeated
bases, n = 20, h = h', h = 1, r = 0, γ = 1, sk = 0, ℓ = 10); then for every
honest case, every field mutated by type, the auxiliary information changed
(a string appended, removed, changed, reordered, `[]` ↔ `[""]`, composed and
decomposed accents, a lone surrogate), the proof replayed on another case's
statement, and structural and encoding cases (vectors one element short or
long, e ≥ q, negative and non-minimal encodings, non-members, another or
the identity generator). The verdicts are in `WORK_DIR/KIND.tsv`
(expected, Swiss Post, certified, note).
