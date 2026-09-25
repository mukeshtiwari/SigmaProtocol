# Theorem index

This file maps every claim made in the paper to the Rocq definition or
theorem that establishes it. Names are given as `File.v: name`; all files
live under [src/](src/). Every theorem listed here is closed under the
global context (no axioms, no admits) unless stated otherwise; the
`Print Assumptions` audit that checks this is described at the end.

Two kinds of results appear for every protocol. The results marked
*(map form)* are the original statements, which compare the real and
simulated distributions after mapping the verifier's acceptance predicate
over them. The results marked *(permutation form)* are the strengthened
statements: the two distributions, as lists of (transcript, probability)
pairs, are permutations of each other, which is literally the textbook
definition of special honest-verifier zero-knowledge. The permutation form
implies the map form, and a constant simulator cannot satisfy it.

## Section 4: the Schnorr protocol and its properties

| Claim | Rocq |
|---|---|
| Prover, simulator, and verification equation | `Crypto/Sigma.v: schnorr_protocol`, `schnorr_simulator`, `accepting_conversation` |
| Completeness | `Crypto/Sigma.v: schnorr_completeness` (and `schnorr_completeness_berry`) |
| Completeness of the simulator | `Crypto/Sigma.v: simulator_completeness` (and `simulator_completeness_berry`) |
| Special soundness with the explicit extractor `(r₁ - r₂) / (c₁ - c₂)` | `Crypto/Sigma.v: special_soundness_berry` (generic version `special_soundness_berry_gen`) |
| Special honest-verifier zero-knowledge *(map form)* | `Crypto/Sigma.v: special_honest_verifier_zkp` |
| Special honest-verifier zero-knowledge *(permutation form)*, for any challenge set closed under `u ↦ u + c·x` | `Crypto/Sigma.v: special_honest_verifier_zkp_perm` |
| Same, for the whole field (challenge set enumerates `F`) | `Crypto/Sigma.v: special_honest_verifier_zkp_enum` |
| Randomness bijection behind the proof: `schnorr_protocol x g u c = schnorr_simulator g h (u + c·x) c` | `Crypto/Sigma.v: schnorr_protocol_simulator_shift` (via `schnorr_commitment_shift`) |
| Soundness error: for a fixed announcement, either two distinct accepting challenges yield the witness, or the acceptance probability over a uniform challenge is at most `1/|C|` | `Crypto/Sigma.v: soundness_error_bound` |

## Section 4.1: uniform distributions

| Claim | Rocq |
|---|---|
| Distributions as lists of (value, probability) pairs | `Probability/Distr.v: dist` (probabilities in `Probability/Prob.v: prob`) |
| Equality of distributions is permutation | `Probability/Distr.v: dist_equiv` |
| `dist` is a monad (`Ret`, `Bind`, the three laws) | `Probability/Distr.v: Ret`, `Bind`, `bind_ret_left`, `bind_ret_right`, `bind_assoc` |
| Uniform distribution over a non-empty list, summing to one | `Probability/Distr.v: uniform_with_replacement`, `uniform_with_replacement_adds_to_one`, `uniform_probability` |
| `n` independent draws as a distribution over vectors | `Probability/Distr.v: repeat_dist_ntimes_vector` |
| Each vector of `n` draws has probability `1/|lf|^n` | `Probability/Distr.v: uniform_probability_multidraw_prob` |
| Probability of an event under a distribution | `Probability/Distr.v: prob_of_an_event`, `event_uniform_prob`, `list_of_events_uniform` |
| A permutation of the support of a uniform distribution permutes the distribution | `Probability/Distr.v: uniform_perm`, `bind_ret_perm` |
| A coordinatewise family of permutations permutes `n` uniform draws | `Probability/Distr.v: repeat_uniform_perm` (with `vec_apply`) |
| Any bijection with an explicit inverse permutes `n` uniform draws over a complete, duplicate-free list | `Probability/Distr.v: repeat_uniform_bijection_perm` |

## Section 4.2 to 4.5: compositions

Each composition has a prover, a simulator, a verifier, and the three
properties. `*_perm` is the permutation-form zero-knowledge theorem.

| Composition | File | Prover / simulator / verifier | Completeness (prover, simulator) | Special soundness | SHVZK (map form) | SHVZK (permutation form) |
|---|---|---|---|---|---|---|
| Parallel (`n` Schnorr runs on one statement) | `Crypto/ParallelSigma.v` | `construct_parallel_conversations_schnorr`, `construct_parallel_conversations_simulator`, `generalised_parallel_accepting_conversations` | `construct_parallel_conversations_schnorr_completeness`, `construct_parallel_conversations_simulator_completeness` | `generalise_parallel_sigma_soundness` | `generalised_parallel_special_honest_verifier_zkp` | `generalised_parallel_special_honest_verifier_zkp_perm` |
| And, one generator | `Crypto/AndSigma.v` | `construct_and_conversations_schnorr`, `construct_and_conversations_simulator`, `generalised_and_accepting_conversations` | `construct_and_conversations_schnorr_completeness`, `construct_and_conversations_simulator_completeness` | `generalise_and_sigma_soundness` | `generalised_and_special_honest_verifier_zkp` | `generalised_and_special_honest_verifier_zkp_perm` |
| And, one generator per statement | `Crypto/AndSigmaGen.v` | same names as above | same names as above | `generalise_and_sigma_soundness`, `generalise_and_sigma_soundness_neq` | `generalised_and_special_honest_verifier_zkp` | `generalised_and_special_honest_verifier_zkp_perm` |
| Or, `2 + n` statements, one generator | `Crypto/OrSigma.v` | `generalised_construct_or_conversations_schnorr`, `generalised_construct_or_conversations_simulator`, `generalised_or_accepting_conversations` | `generalised_construct_or_conversations_schnorr_completeness`, `generalised_construct_or_conversations_simulator_completeness` | `generalised_or_sigma_soundness_main` | `generalised_or_special_honest_verifier_zkp` | `generalised_or_special_honest_verifier_zkp_perm` |
| Or, one generator per statement | `Crypto/OrSigmaGen.v` | same names as above | same names as above | `generalised_or_sigma_soundness_main` | `generalised_or_special_honest_verifier_zkp` | `generalised_or_special_honest_verifier_zkp_perm` |
| Eq (same exponent under `n` generators) | `Crypto/EqSigma.v` | `construct_eq_conversations_schnorr`, `construct_eq_conversations_simulator`, `generalised_eq_accepting_conversations` | `construct_eq_conversations_schnorr_completeness`, `construct_eq_conversations_simulator_completeness` | `generalise_eq_sigma_soundness` | `generalised_eq_special_honest_verifier_zkp` | `generalised_eq_special_honest_verifier_zkp_perm` |
| Chaum-Pedersen (Eq with two generators) | `Crypto/ChaumPedersen.v` | `construct_cp_conversations_schnorr`, `construct_cp_conversations_simulator`, `generalised_cp_accepting_conversations` | `construct_cp_conversations_schnorr_completeness`, `construct_cp_conversations_simulator_completeness` | `generalise_cp_sigma_soundness` | `generalised_cp_special_honest_verifier_zkp` | `generalised_cp_special_honest_verifier_zkp_perm` |
| ElGamal encryption proof (ciphertext encrypts one of `2 + n` messages) | `Crypto/EncProof.v` | `generalised_construct_encryption_proof_elgamal_real`, `generalised_construct_encryption_proof_elgamal_simulator`, `generalised_accepting_encryption_proof_elgamal` | `generalised_construct_encryption_proof_elgamal_real_completeness`, `generalised_construct_encryption_proof_elgamal_simulator_completeness` | `generalised_accepting_elgamal_soundness_main` | `generalised_encryption_proof_elgamal_special_honest_verifier_zkp` | `generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm` |
| ElGamal decryption proof | `Crypto/DecProof.v` | `construct_decryption_proof_elgamal_real`, `construct_decryption_proof_elgamal_simulator`, `decryption_proof_accepting_conversations` | `construct_decryption_proof_elgamal_real_completeness`, `construct_decryption_proof_elgamal_simulator_completeness` (vector form `decryption_proof_accepting_conversations_vector_completeness`) | `special_soundness_construct_decryption_proof_elgamal` | `construct_decryption_proof_elgamal_special_honest_verifier_zkp` | `construct_decryption_proof_elgamal_special_honest_verifier_zkp_perm` |
| Okamoto, `2 + n` generators | `Crypto/Okamoto.v` | `generalised_okamoto_real_protocol` (`generalised_okamoto_commitment`, `generalised_okamoto_response`), `generalised_okamoto_simulator_protocol`, `generalised_okamoto_accepting_conversation` | `generalised_okamoto_real_accepting_conversation`, `generalised_okamoto_simulator_accepting_conversation` | `generalised_okamoto_real_special_soundenss` | `generalised_okamoto_special_honest_verifier_zkp` | `generalised_okamoto_special_honest_verifier_zkp_perm` |
| Neq (pairwise distinct witnesses) | `Crypto/NeqSigma.v` | `generalised_construct_neq_conversations_real_transcript`, `generalised_construct_neq_conversations_simulator_transcript`, `generalised_neq_accepting_conversations` | `generalised_neq_real_transcript_accepting_conversations`, `generalised_neq_simulator_transcript_accepting_conversations` | `generalised_neq_accepting_conversations_soundenss` (sic; the unconditional dichotomy of Listing "Neq Σ Protocol") | `generalised_neq_special_honest_verifier_zkp` | `generalised_neq_special_honest_verifier_zkp_perm` |
| Linear relations over Pedersen commitments | `Crypto/PedLinearRel.v` | `pedersen_commitment_vector`, `generalised_pedersen_linear_relation_distribution`, `generalised_pedersen_linear_relation_simulator_distribution` | `pedersen_linear_relation_completeness`, `pedersen_linear_relation_simulator_completeness` | `pedersen_linear_relation_special_soundness` (dichotomy: the linear constraint holds or `g` is the identity) | `generalised_pedersen_special_honest_verifier_zkp` | `generalised_pedersen_special_honest_verifier_zkp_perm` |

Further results referenced in the text:

| Claim | Rocq |
|---|---|
| Okamoto witness indistinguishability (Listing "Witness Indistinguishability") | `Crypto/Okamoto.v: generalised_okamoto_witness_indistinguishable` (bijections `transform_us`, `inverse_transform`; homomorphism `generalised_okamoto_commitment_homomorphic`) |
| ElGamal encryption, decryption, re-encryption, homomorphic product | `Crypto/Elgamal.v: enc`, `dec`, `re_enc`, `mul_cipher`, `dec_is_left_inv_of_enc`, `dec_re_enc_left_inv`, `additive_homomorphic_property` |
| Confidential-transaction instance of the linear relation | `Examples/PedLinearRelIns.v` |

The permutation-form theorems for the Or-style protocols (Or, Or with
generators, encryption proof) and for Neq are stated for a challenge list
that is duplicate-free and enumerates the field, because their randomness
bijections are not coordinatewise. The other permutation-form theorems
only need the challenge list to be closed under the relevant shift
`u ↦ u + c·x`; each of them also has an `_enum` corollary with the same
hypotheses as the Or-style theorems (`List.NoDup lf` and
`forall y, List.In y lf`), obtained through
`Probability/Distr.v: enumerates_perm_map`, so that every protocol has a
zero-knowledge theorem of the same shape as
`Crypto/Sigma.v: special_honest_verifier_zkp_enum`:
`generalised_parallel_special_honest_verifier_zkp_enum`,
`generalised_and_special_honest_verifier_zkp_enum` (in `AndSigma.v` and
`AndSigmaGen.v`), `generalised_eq_special_honest_verifier_zkp_enum`,
`generalised_cp_special_honest_verifier_zkp_enum`,
`construct_decryption_proof_elgamal_special_honest_verifier_zkp_enum`,
`generalised_okamoto_special_honest_verifier_zkp_enum` and
`generalised_pedersen_special_honest_verifier_zkp_enum`.

## Section 4.6: modular arithmetic

| Claim | Rocq |
|---|---|
| `Z_p^*` is a commutative group | `Utility/Zpstar.v: zpstar_comm` |
| The Schnorr group (order-`q` subgroup of `Z_p^*`) is a commutative group | `Utility/Zpstar.v: schnorr_comm` (elements `Schnorr_group`, operations `one`, `mul_schnorr_group`, `inv_schnorr_group`) |
| `Z_q` is a field | `Utility/Zpstar.v: zp_field` |
| Schnorr group and `Z_q` form a vector space (`pow` is the scalar action) | `Utility/Zpstar.v: pow_vspace`, `pow` |
| Decidable equality of group elements | `Utility/Zpstar.v: dec_zpstar` |

## Section 4.7: efficient extractor

| Claim | Rocq |
|---|---|
| Square-and-multiply exponentiation and its logarithmic step count (a `Prop`, erased by extraction) | `Utility/Functions.v: repeat_op_ntimes_rec`, `complexity_repeat_op_ntimes_rec`, `correct_complexity_repeat_op_ntimes_rec` |

## Section 5.1: approval voting

| Claim | Rocq |
|---|---|
| Vote encryption and 0/1 proof (Listing "Frontend Functions") | `Frontend/Approval.v: encrypt_vote`, `generate_enc_proof`, `encrypt_vote_and_generate_enc_proof`, `verify_encryption_vote_proof` |
| A well-formed vote is accepted | `Frontend/Approval.v: vote_proof_valid` |
| A vote that is neither 0 nor 1 is rejected (and the one corner case that is accepted) | `Frontend/Approval.v: vote_proof_invalid_reject`, `vote_proof_invalid_accept` |
| Whole ballot: ciphertexts and proofs, and their verification | `Frontend/Approval.v: encrypt_ballot_and_generate_enc_proof`, `verify_encryption_ballot_proof`, `ballot_proof_valid` |
| Overall proof that the ballot has between 0 and `n` approvals (a disjunctive encryption proof on the homomorphic product of the ballot) | `Frontend/Approval.v: generate_overall_proof`, `verify_overall_proof`, `verify_ballot` |
| The overall proof of a well-formed ballot is accepted, and so is the full ballot | `Frontend/Approval.v: overall_proof_valid`, `ballot_with_overall_proof_valid` |
| The announcements hashed by the non-interactive client are exactly the announcements of the proofs it sends | `Frontend/Approval.v: generate_enc_proof_commitment`, `generate_ballot_commitment`, `generate_enc_proof_commitment_announcement`, `ballot_commitment_announcement` |
| Tallying as an inductive state machine (`ax`, `cvalid`, `cinvalid`, `cfinish`) | `Backend/Tally.v: state`, `count` |
| Executable tally and the invariant `Permutation bs (vbs ++ inbs)` | `Backend/Tally.v: compute_final_tally`, `compute_final_count` |
| Instantiation at concrete parameters and the non-interactive client | `Examples/TallyIns.v: compute_final_count_ins`; `Examples/ApprovalIns.v: nizk_encrypt_ballot_with_overall_proof_ins` |

The client and tally programs are `Executable/Approvalcode/main.ml` and
`Executable/Tallycode/main.ml`. The tally program recomputes every
challenge (SHAKE-256 over the public parameters and the announcements)
before calling the certified verifier, so a ballot whose stored challenges
do not match its announcements is rejected.

## Section 5.2: Helios verifier

| Claim | Rocq |
|---|---|
| Ballots, talliers, and the verification state machine | `Backend/HeliosTally.v: ballot`, `tallier`, `state`, `count` |
| Certified verifier returning a `count (finished …)` certificate | `Backend/HeliosTally.v: compute_final_tally`, `compute_final_count` |
| Instantiation at the Helios parameters (2048-bit `p`, 256-bit `q`, election keys `h2023`, `h2024`) | `Examples/HeliosTallyIns.v: compute_final_count_ins` |
| Primality of `q` and `p` (Coqprime certificates) | `Examples/primeQ.v: prime_q`; `Examples/primeP.v: prime_p` (used by `Examples/HeliosTallyIns.v: prime_q`, `prime_p`) |
| Certified Helios client at the same parameters | `Examples/HeliosFrontendIns.v: helios_nizk_encrypt_ballot_and_generate_enc_proof`, `helios_verify_encryption_ballot_proof` |

The driver `Executable/HeliosVerifiercode/main.ml` and its parser
(`parsing/parser.mly`, `parsing/ast.ml`) recompute Helios's SHA-1
Fiat-Shamir challenges from the announcements (`helios_challenge`) and check
that every group element lies in the order-`q` subgroup and every field
element is below `q` (`group_elt`, `field_elt`) before handing the data to
the certified verifier. `bench/forge_ballot.py` produces a ballot that
passes the verification equations with forged challenges; the verifier
rejects it.

## Section 5.3: performance and the compiled pipelines

| Claim | Where |
|---|---|
| OCaml extraction of every library and case study | `Extraction/*/Extraction.v`, `Extraction/dune` |
| Benchmark programs and reproduction instructions | `bench/README.md`, `Executable/HeliosBenchcode/main.ml` |
| WebAssembly client (CertiRocq) and the reduced-parameter measurements | `Wasm/approval.wasm`, `Examples/WasmBenchDefs.v`, `Examples/WasmBenchSmallDefs.v`, `bench/wasm/` |
| CakeML pipeline | `bench/cakeml/` |

## Axiom audit

`bash bench/assumptions.sh` (after `dune build`) runs `Print Assumptions`
on every theorem named above (`bench/assumptions.v`). All security
theorems of the library, the distribution toolkit, the modular arithmetic
instances, the extractor complexity result and the approval-voting
theorems in `Frontend/Approval.v` report `Closed under the global
context`. The remaining entries report the following, expected,
assumptions:

| Theorem | Assumptions | Why |
|---|---|---|
| `Backend/Tally.v: compute_final_count`, `Examples/TallyIns.v: compute_final_count_ins` | `hdiscrete` | An `Axiom` in `Backend/Tally.v` stating that the discrete-logarithm search passed to the tally is correct (`discrete_logarithm_search hx hy = y → hx ^ y = hy`). The Helios verifier does not need it: `Backend/HeliosTally.v` checks `g ^ pt = ds` for the published tally instead. |
| `Examples/TallyIns.v: compute_final_count_ins` | `proof_irrelevance` | Identifies two proofs of primality when instantiating the tally (`Stdlib.Logic.ProofIrrelevance`). |
| `Examples/HeliosTallyIns.v: prime_q`, `prime_p`, `compute_final_count_ins`; `Examples/HeliosFrontendIns.v: helios_nizk_encrypt_ballot_and_generate_enc_proof`, `helios_verify_encryption_ballot_proof` | `Uint63Axioms.*`, `PrimInt63.*` | The Coqprime primality certificates for the 256-bit `q` and 2048-bit `p` compute with Rocq's primitive 63-bit integers, whose specification is axiomatised in the standard library (`Stdlib.Numbers.Cyclic.Int63.Uint63Axioms`). Everything instantiated at the Helios parameters inherits them. |
