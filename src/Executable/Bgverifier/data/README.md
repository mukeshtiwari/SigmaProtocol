# Swiss Post mix-net test vectors

The six `verify-*.json` files are the verifier test vectors of the Swiss
Post crypto-primitives library (`src/test/resources/mixnet/` of
https://gitlab.com/swisspost-evoting/crypto-primitives/crypto-primitives,
commit 94a8438, Apache License 2.0), which implements the specification
"Crypto-Primitives Specification" version 1.6.0 whose Section 9 is the
Bayer–Groth shuffle argument. All cases use the 3072-bit group of the
specification (p = 2q + 1, g = 2, Section 3.1); the values are Base64
encodings of Java `BigInteger.toByteArray()` (big-endian two's complement).

Each file is a list of cases with a `context` (p, q, g, the ElGamal public
key `pk` with l components, the commitment key `ck` = (h, g_1, …, g_ν)), an
`input` (`statement` and `argument`) and the expected `output`
(`result`, and the challenges `x`, `y`, `z` that the Swiss Post verifier
derives with RecursiveHash, which the driver recomputes and compares):

| file | argument | cases (m, n, l) |
|---|---|---|
| `verify-shuffle-argument.json` | Algorithm 9.12, whole shuffle argument | (1,2,1), (2,3,2), (8,8,2), (8,8,4) |
| `verify-product-argument.json` | Algorithm 9.19 | (1,2,1), (2,3,2), (8,8,2), (8,8,4) |
| `verify-hadamard-argument.json` | Algorithm 9.21 | (2,3,2), (8,8,2), (8,8,4) |
| `verify-zero-argument.json` | Algorithm 9.23 | (1,2,1), (2,3,2), (8,8,2), (8,8,4) |
| `verify-single-value-product-argument.json` | Algorithm 9.26 | (1,2,1), (2,3,2), (8,8,2), (8,8,4) |
| `verify-multiexp-argument.json` | Algorithm 9.16 | (1,2,1), (2,3,2), (8,8,2), (8,8,4) |

The ciphertexts of a shuffle are N = m·n multi-recipient ElGamal
ciphertexts (γ, φ_1, …, φ_l); the multi-exponentiation statement holds
them as an m × n matrix (row i = ciphertexts n·i, …, n·i + n − 1).
