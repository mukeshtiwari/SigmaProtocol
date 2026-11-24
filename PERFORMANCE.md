# Performance: faster tally, Peregrine C, and verified Ed25519 code

We made three additions to the executable code of the library. We sped up
the extracted OCaml tally and proved the changed functions equal to the
originals. We compiled ballots to C and WebAssembly with Peregrine instead of
OCaml extraction. In the Peregrine build, we replaced the Ed25519 scalar
multiplication with verified bedrock2 code from AUCurves.

## Faster Schulze tally

We made three changes to the tally, each with a proof that the result is
unchanged.

- The inverse in the Schnorr group is `a^(q-1) mod p` instead of
  `a^(p-2) mod p` (`Utility/Zpstar.v`). Every element has order dividing `q`,
  so `schnorr_left_inv` derives `a · a^(q-1) = 1` from the subgroup
  condition. The exponent has 256 bits instead of 2048.
- Fixed-base tables (`Utility/FixedBasePow.v`) store the powers `c^(j·16^i)`
  of the generators `g` and `h`. The table-based `pow_fb` equals the
  square-and-multiply `pow` (`pow_fb_pow`), so it gives the same vector space
  (`pow_fb_vspace`).
- The certificate verifier is a list of independent tasks
  (`tally_tasks`, `nizk_verify_tally_tasks` in `Backend/SchulzeTally.v`).
  `verify_tally_tasks` and `nizk_verify_tally_tasks_spec` prove that the
  conjunction of the tasks is the original verifier, so the drivers can run
  the tasks on forked workers.

| Election (candidates m, ballots N, workers) | Prover before → after | Verifier before → after (one process / workers) |
|---|---|---|
| m = 5, N = 64, 4 workers | 120 s → 34.8 s | 193 s → 54.1 s / 21.4 s |
| m = 10, N = 64, 2 workers | 1598 s → 557 s | 1356 s → 457 s / 265 s |
| Gentoo council 2023, m = 10, N = 50 | 2154 s → 490 s | 1030 s → 132 s (2 workers) |

The whole Gentoo 2023 run takes 714 s instead of 3308 s and certifies the
same winner. `bench/README.md` gives the full table and the commands.

Trusted: OCaml extraction, the OCaml runtime, zarith and GMP, the SHAKE-256
implementation of the Fiat–Shamir oracle (the oracle is a parameter of the
proved prover and verifier), and the scheduling of tasks on workers.

## Ballots in C and WebAssembly with Peregrine

Peregrine compiles the erased program (λ□) to C through the CertiRocq
backend. We remap the integer types `Z`, `positive` and `N` and their
operations to GMP, as in the KZG demonstrator of the Commitments
development. The C backend cannot compile a 2048-bit numeral, because it
builds one constructor per bit. A verified Peregrine pass, `ENumeralHoist`
(branch `numeral-literals` of peregrine-tool), moves every numeral above a
size threshold into a named constant. The C backend then emits each such
constant as a GMP integer parsed from its decimal string. The pass has
proofs of well-formedness, eta-expansion and inductive lookup, and a proof
that evaluation is unchanged once the constants are replaced by their
numerals; its axioms are those of the standard
library's primitive types and functional extensionality.

The approval ballot at the 2048-bit Helios parameters (encrypt, prove,
verify) runs in 0.15 s natively. The same C compiled with emscripten and
mini-gmp to 64-bit WebAssembly runs in 0.6 s under Node 24.
`bench/peregrine/build.sh` builds both.

Trusted: Peregrine and the CertiRocq C runtime, the GMP remapping
(`GmpZ.v` against `z_gmp.c`, and the splicing scripts), the numeral hook,
gcc, and GMP; for WebAssembly also emscripten, mini-gmp and Node.

## Verified Ed25519 code from AUCurves

AUCurves proves bedrock2 implementations of Ed25519 field and point
operations against fiat-crypto's curve specification. SigmaProtocol defines
its Ed25519 group with an earlier fiat-crypto, vendored under the root
`Fiat`, whose field type is `Zmod p`; the AUCurves version uses `F p`. This
library's theory and AUCurves' fiat-crypto both had the logical root
`Crypto`, so we renamed the library's theory to `Sigma`.

The bridge (`bedrock/`) transports the field (`FieldTransport.v`) and proves
that the bedrock2 functions compute the group operations of this library.

| Function | Theorem | Result |
|---|---|---|
| `double` | `ed25519_exec_double` | doubling |
| `to_cached2`, `readd`, `add` | `ed25519_exec_add_fn` | group addition |
| `from_affine`, `to_affine` | `ed25519_exec_from_affine`, `ed25519_exec_to_affine` | coordinate conversion |
| `scalarmult` | `ed25519_exec_scalarmult` | `Ed.gpow_fast` |
| `scalarmult_ct` | `ed25519_exec_scalarmult_ct` | `Ed.gpow_fast` |

The function `scalarmult_ct` computes the double and the sum at every bit
and selects one with a masked copy. No branch condition and no memory address
depends on the scalar; we state this property without a formal proof. All theorems are
closed under the global context. `EmitC.v` prints the functions as C with
bedrock2's printer and proves that the emitted field functions meet the
specifications the theorems assume.

In the Peregrine build of the Ed25519 approval ballot (seven candidates), we
remap `Ed.fast_smul` to `scalarmult_ct` through a C glue function. The
program gives the same output as the GMP build.

| Ed25519 ballot, encrypt + prove + verify | Time |
|---|---|
| Peregrine C, field arithmetic in GMP | 90 ms |
| Peregrine C, `scalarmult_ct` | 23.8 ms |

Trusted, in addition to the Peregrine list: the script that remaps the
constant, the glue (conversion between GMP integers and bytes, the heap
layout of points, the constant 2d, the bound `0 ≤ n < 2^256` on the scalar),
the renaming of the C keyword `double`, and bedrock2's C printer. The
theorems connect the emitted functions to `Ed.gpow_fast` in separate steps;
no single theorem states the end-to-end result. Only the scalar multiplication is constant
time: the arithmetic modulo the group order still uses GMP.
