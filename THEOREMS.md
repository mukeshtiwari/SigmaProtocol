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
| Completeness | `Crypto/Sigma.v: schnorr_completeness` (and `schnorr_completeness_transcript`) |
| Completeness of the simulator | `Crypto/Sigma.v: simulator_completeness` (and `simulator_completeness_transcript`) |
| Special soundness with the explicit extractor `(r₁ - r₂) / (c₁ - c₂)` | `Crypto/Sigma.v: special_soundness` (generic version `special_soundness_extractor`) |
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
| Okamoto, `2 + n` generators | `Crypto/Okamoto.v` | `generalised_okamoto_real_protocol` (`generalised_okamoto_commitment`, `generalised_okamoto_response`), `generalised_okamoto_simulator_protocol`, `generalised_okamoto_accepting_conversation` | `generalised_okamoto_real_accepting_conversation`, `generalised_okamoto_simulator_accepting_conversation` | `generalised_okamoto_real_special_soundness` | `generalised_okamoto_special_honest_verifier_zkp` | `generalised_okamoto_special_honest_verifier_zkp_perm` |
| Neq (pairwise distinct witnesses) | `Crypto/NeqSigma.v` | `generalised_construct_neq_conversations_real_transcript`, `generalised_construct_neq_conversations_simulator_transcript`, `generalised_neq_accepting_conversations` | `generalised_neq_real_transcript_accepting_conversations`, `generalised_neq_simulator_transcript_accepting_conversations` | `generalised_neq_accepting_conversations_soundness` (the unconditional dichotomy of Listing "Neq Σ Protocol") | `generalised_neq_special_honest_verifier_zkp` | `generalised_neq_special_honest_verifier_zkp_perm` |
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
| Special soundness at the ballot level: two accepting vote proofs (resp. overall proofs) with the same announcement and different challenges show that the ciphertext encrypts 0 or 1 (resp. that the ballot product encrypts `g^m` with `m ≤ n`) | `Frontend/Approval.v: vote_proof_sound`, `overall_proof_sound` (instances of `Crypto/EncProof.v: generalised_accepting_elgamal_soundness_main`) |
| A prover without a case analysis on the vote (both branches computed as simulated ones, combined by multiplication with `m` and `1 - m`) computes the same proofs and ballots on votes 0 and 1 | `Frontend/Approval.v: generate_enc_proof_ct`, `encrypt_ballot_and_generate_enc_proof_ct`, `generate_enc_proof_ct_eq`, `encrypt_ballot_and_generate_enc_proof_ct_eq` |
| The announcements hashed by the non-interactive client are exactly the announcements of the proofs it sends | `Frontend/Approval.v: generate_enc_proof_commitment`, `generate_ballot_commitment`, `generate_enc_proof_commitment_announcement`, `ballot_commitment_announcement` |
| Tallying as an inductive state machine (`ax`, `cvalid`, `cinvalid`, `cfinish`); the final state records whether `g^pt_i = ds_i` was checked for every candidate | `Backend/Tally.v: state`, `count` |
| A certificate whose flag is true gives, for every candidate, `g^pt_i = ds_i` and accepted decryption proofs | `Backend/Tally.v: finished_true_correct` |
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

## Ed25519 instantiation

A second instantiation of the vector-space class, next to the Schnorr
group: the field is `Z/lZ` (`l` the prime order of the Ed25519 base point)
and the group is the order-`l` subgroup of Curve25519 in twisted Edwards
form. The curve specification is the vendored specification layer of
fiat-crypto (`src/Fiat`, logical root `Fiat`, see `src/Fiat/dune`).

| Claim | Rocq |
|---|---|
| `Z/lZ` is a field, with decidable equality; its type is a record around `Zmod l`, reached through its operations and the conversions `of_Z`, `to_Z` | `Curve/Ed25519.v: Zl.F`, `Zl.zl_field`, `Zl.Fdec`, `Zl.to_Z_inj` (from `Fiat.Arithmetic.PrimeFieldTheorems` and `Fiat.Spec.Curve25519.prime_l`) |
| Affine points with coordinate equality are Leibniz-equal, and point equality is decidable | `Curve/Ed25519.v: Ed.peq_leibniz`, `Ed.point_dec` |
| The order-`l` subgroup is a commutative group with decidable equality | `Curve/Ed25519.v: Ed.G`, `Ed.ed25519_comm_group`, `Ed.Gdec` (from `Fiat.Curves.Edwards.AffineProofs.E.edwards_curve_commutative_group`) |
| Scalar multiplication by `Z/lZ` makes it a vector space | `Curve/Ed25519.v: Ed.gpow`, `Ed.ed25519_vspace` (laws from `Fiat.Algebra.ScalarMult`, exponent reduction by `scalarmult_mod_order`) |
| A double-and-add in extended coordinates equals the reference scalar multiplication | `Curve/Ed25519.v: Ed.fast_smul`, `Ed.fast_smul_eq` (from `Fiat.Curves.Edwards.XYZT.Basic`) |
| The vector-space instance used for extraction, built on the fast multiplication | `Curve/Ed25519.v: Ed.gpow_fast`, `Ed.ed25519_vspace_fast` |
| The base point has order `l`, by computation | `Curve/Ed25519.v: Ed.B_in_subgroup`, `Ed.B` |
| Schnorr, Chaum-Pedersen and approval ballots (individual and overall proofs) at Ed25519 | `Examples/Ed25519Ins.v` |
| The ballot without a case analysis on the votes equals the ballot | `Examples/Ed25519Ins.v: encrypt_ballot_and_generate_enc_proof_ct_ins_eq` |

All of these are closed under the global context. The driver
`Executable/Ed25519code/main.ml` produces and verifies the proofs, rejects
tampered proofs and a ballot encrypting `5`, and benchmarks a ballot.

## Belenios verifier

A certified verifier for Belenios elections (specification version 1, as
implemented by Belenios 3.x): group Ed25519, homomorphic questions with or
without blank votes, weighted credentials, "Single" trustees. Belenios
stores every proof as (challenge, response); the verifier reconstructs the
announcements and checks the challenge against the hash, which the driver
computes (SHA-256 over Belenios's serialisation) and passes in.

| Claim | Rocq |
|---|---|
| The product of two vector spaces over the same field is a vector space (used for statements `(α, β/m) = (g, y)^r` in `G × G`) | `Algebra/Product_space.v: prod_vspace`, `prod_dec` |
| Belenios-style verification of a single proof yields an accepting transcript of the library's Schnorr protocol (reconstructed announcement, negated challenge) | `Backend/BeleniosTally.v: reconstruct_accepting`, `fs_verify_schnorr_accepting` |
| Belenios-style verification of a disjunction yields an accepting transcript of the library's Or composition (`Crypto/OrSigmaGen.v`); this covers the individual 0/1 proofs, the interval proofs and the two proofs of possibly-blank votes | `Backend/BeleniosTally.v: fs_verify_or_accepting` |
| Ballot verification: credential in the roll, signature, individual proofs, overall proof, blank proofs | `Backend/BeleniosTally.v: verify_ballot`, `verify_answer` |
| Tally of the last ballot of each credential, raised to the credential's weight | `Backend/BeleniosTally.v: last_per_credential`, `encrypted_tally` |
| Trustees' proofs of knowledge, decryption proofs, combined factors, and the published result | `Backend/BeleniosTally.v: verify_trustee`, `combined_factors`, `verify_result` |
| The certificate and the certified verifier | `Backend/BeleniosTally.v: count`, `compute_final_count`; `Examples/BeleniosIns.v: compute_final_count_ins` |

All closed under the global context. The driver is
`Executable/Beleniosverifier/main.ml`; it also checks the archive's own
content hashes and event chain, decodes and validates every point (on the
curve, canonical, of order l), and rejects malformed ballots.

## P-256 instantiation and shared infrastructure for the applications plan

`plans/ZK_APPLICATIONS_PLAN.md` (shuffles, U-Prove, BBS#) rests on three
pieces added in its Step 0, next to the Ed25519 instantiation above.

| Claim | Rocq |
|---|---|
| The n-fold product `Vector.t V n` of a vector space is a vector space, with decidable equality and coordinate lemmas | `Algebra/Vector_product_space.v: vec_vspace`, `vec_dec`, `nth_vec_add`, `nth_vec_smul` |
| Fiat–Shamir verification of a multi-base proof (challenge, responses) for `h = g_1^{x_1} ⋯ g_k^{x_k}`: the reconstructed announcement `g_1^{s_1} ⋯ g_k^{s_k} · h^d` with challenge `−d` is an accepting transcript of the generalised Okamoto protocol, for either sign convention of the response | `Backend/FiatShamirLinRel.v: reconstruct_linrel_accepting`, `fs_verify_linrel_accepting` |
| P-256 (secp256r1): the field `Z/nZ`, the curve group with Leibniz equality, the vector-space instance, a Jacobian-coordinate double-and-add proved equal to fiat-crypto's reference scalar multiplication, and the base point of order n by computation | `Curve/P256.v: Zn.zn_field`, `Wp.p256_comm_group`, `Wp.Gdec`, `Wp.p256_vspace`, `Wp.fast_smul_eq`, `Wp.p256_vspace_fast`, `Wp.B_in_subgroup` |
| p and n of P-256 are prime (Pocklington certificates generated by `bench/pocklington.py`) | `Curve/P256Primes.v: prime_p256_p`, `prime_p256_n` |
| The library at P-256: Schnorr, Chaum-Pedersen, approval ballots with individual and overall proofs | `Examples/P256Ins.v` (mirrors `Examples/Ed25519Ins.v`) |

The curve comes from six more vendored fiat-crypto files
(`Fiat/Spec/WeierstrassCurve.v`, `Fiat/Curves/Weierstrass/{Affine,AffineProofs}.v`,
`Fiat/Curves/Weierstrass/Jacobian/Jacobian.v`, `Fiat/Util/FsatzAutoLemmas.v`,
`Fiat/Util/Tactics/Beta1.v`). Everything in this section is closed under
the global context: the Pocklington certificates use Coqprime's Z-based
checker (`PrimalityTest.PocklingtonCertificat`, as fiat-crypto's
`Spec/Curve25519.v` does), not the Bignums-based one, so unlike the Helios
and ElectionGuard primes they carry no primitive-integer axioms. The
driver is `Executable/P256code/main.ml`.

## ElectionGuard verifier

A certified verifier for ElectionGuard 2.0 election records (specification
version 2.0.0; the JSON records of the reference implementation
electionguard-kotlin-multiplatform): the guardians' coefficient proofs and
the joint public key (verifications 2 and 3), the range proofs of the
encrypted options and the selection-limit proofs of the contests (5 and
6), the aggregation of the cast ballots (8), the decryption proofs and the
decrypted values of the tally (9 and 10) and of the challenged ballots (12
and 13). ElectionGuard writes each proof as (challenge, response) and the
verifier reconstructs the announcements. In the product group `G × G` with
base `(g, K)`, the reconstruction of a range-proof branch,
`(g^v · α^c, K^(v − j·c) · β^c) = (g, K)^v · (α, β / K^j)^c`, is exactly the
Belenios one, so the Fiat-Shamir layer of `Backend/BeleniosTally.v` is
reused unchanged. The hash functions (HMAC-SHA-256 over the encodings of
section 5 of the specification) are computed by the driver and passed in.

| Claim | Rocq |
|---|---|
| Range proofs and selection-limit proofs are disjunctions of the Schnorr statements `(α, β / K^j) = (g, K)^ξ`, `j = 0..R`, in `G × G`; a verified proof is an accepting transcript of the library's Or composition (`Crypto/OrSigmaGen.v`) | `Backend/ElectionGuardTally.v: range_statements`, `verify_range`, `verify_range_or_accepting` |
| Every coefficient proof of a verified guardian is an accepting transcript of the Schnorr protocol for `K_ij = g^a_ij` | `Backend/ElectionGuardTally.v: coefficient_proof_schnorr_accepting`, `verify_guardian_schnorr_accepting` |
| A verified decryption proof is an accepting Schnorr transcript in `G × G` for `(K, M) = (g, A)^s` with `M = B / T`, and `T = K^t` | `Backend/ElectionGuardTally.v: verify_decryption`, `verify_decryption_schnorr_accepting` |
| Ballot verification: distinct contests of the manifest, in order; the range proof of every option (limit R) and the selection-limit proof of the contest over the aggregate of its options (limit L) | `Backend/ElectionGuardTally.v: verify_contest`, `verify_ballot` |
| Encrypted tally: the product, option by option, of the cast ballots | `Backend/ElectionGuardTally.v: encrypted_tally` |
| Guardians `1..n` with `k` coefficients each, `K = ∏ K_i0` | `Backend/ElectionGuardTally.v: verify_guardians`, `joint_key` |
| The certificate and the certified verifier | `Backend/ElectionGuardTally.v: count`, `compute_final_count`; `Examples/ElectionGuardIns.v: compute_final_count_ins` |
| The parameters of the specification: `q = 2^256 − 189` is prime (Pocklington certificate generated by `bench/pocklington.py`), the 4096-bit `p` is prime (elliptic-curve certificate of 147 steps generated by PARI/GP's `primecert` and converted by `bench/ecpp2coq.py`), `p − 1 = q·r`, and `g^q = 1 mod p`, checked in the kernel with the exponentiation computed over Bignums' BigN | `Examples/primeQEG.v: prime_q_eg`; `Examples/primePEG.v: prime_p_eg`; `Examples/ElectionGuardIns.v: prime_q`, `prime_p`, `cofactor`, `g_order`; `Examples/BigNPow.v: bpow_mod_spec` |

The theorems of `Backend/ElectionGuardTally.v` are closed under the global
context. The instantiation `Examples/ElectionGuardIns.v` proves both
primes: `q` by a Pocklington certificate and the 4096-bit `p` by an
elliptic-curve (ECPP) certificate, `Examples/primePEG.v`, since `p − 1 =
q·r` with `r` a 3840-bit cofactor whose factorisation is not known, so
Pocklington's criterion does not apply. The certificate is a chain of 147
`Ell_certif` steps (each a curve over `Z/N_i` whose order `N_i + 1 − t_i`
is `s_i` times the next prime `N_{i+1}`, ending at a 49-bit prime with a
Pocklington certificate), generated by PARI/GP 2.17's `primecert` and
converted to Coqprime's syntax by `bench/ecpp2coq.py`; Coqprime's
`PocklingtonRefl` checker verifies it in the kernel over Bignums' BigN in
about 7.8 hours (about 27,900 s of CPU on an Apple M-series laptop). The instantiated theorems therefore carry only the
primitive-integer axioms of BigN (assumptions table below). The driver is
`Executable/Egverifier/main.ml`; it checks the parameters, the base hashes
`H_P`, `H_M`, `H_B`, `H_E`, the contest hashes and the confirmation codes,
and that every element is in the order-`q` subgroup and every scalar in
`Z_q`. Not covered: the chaining of confirmation codes across ballots
(7.C–7.G), the hashed-ElGamal contest data (11) and pre-encrypted ballots.

## Terelius–Wikström shuffles and the Verificatum verifier

Step 1 of `plans/ZK_APPLICATIONS_PLAN.md`. The proof of a shuffle of
Terelius and Wikström (AFRICACRYPT 2010), as implemented by the Verificatum
mix-net, is built from the library's generalised Okamoto protocol: after
the verifier's batching vector e is fixed, the five equations of the
round-2 statement (A = g^a ∏ h_i^{e'_i}, C = g^c, D = g^d,
B_i = g^{β_i} B_{i−1}^{e'_i}, F = Enc(1; −f) ∏ w'_i^{e'_i}) are linear in
the witness (a, c, d, f, β, e') with the e'_i shared between them, so they
are one multi-base statement in the vector space
V = G × G × G × G^{N+1} × (G × G). Haines, Goré and Sharma verified this
shuffle in Coq before (S&P 2021); the point here is that its round-2
protocol is an instance of an existing library protocol, and that the
certified verifier runs on Verificatum's own proofs.

| Claim | Rocq |
|---|---|
| Multi-exponentiation over any vector space and its algebra (append, identity bases, diagonal bases, components in the product) | `Crypto/MultiExp.v: mexp`, `mexp_app`, `mexp_const_vid`; `Crypto/ShuffleTW.v: mexp_diag`, `mexp_V_components` |
| The statement space V is a vector space | `Crypto/ShuffleTW.v: V_vspace` |
| The multi-base relation over the bases and target of the shuffle is exactly the conjunction of the five equations | `Crypto/ShuffleTW.v: tw_relation_iff` |
| Completeness, special soundness and honest-verifier zero knowledge of the round-2 protocol (the Okamoto theorems at V) | `Crypto/ShuffleTW.v: tw_completeness`, `tw_special_soundness`, `tw_special_honest_verifier_zkp_enum` |
| Verificatum's Algorithm 19 (proof of a shuffle) is the Okamoto acceptance test at V for the transcript (τ; v; σ); a verified proof is an accepting transcript | `Backend/VerificatumVerifier.v: verify_pos`, `verify_pos_accepting` |
| Algorithm 25 (all mix-servers): every server either produced a verified proof from its input list to its output list or left the list unchanged, and at least one did the former | `Backend/VerificatumVerifier.v: verify_shuffling`, `verify_shuffling_spec` |
| Algorithm 22 (joint decryption): the proofs of the parties in Δ, combined with the exponents α·c_l, form an accepting Chaum–Pedersen transcript for (y, B^{−1}) = (g, U)^x; the plaintexts are v_i · f_i | `Backend/VerificatumVerifier.v: verify_decryption`, `verify_decryption_accepting` |
| Algorithm 28 for a mixing session | `Backend/VerificatumVerifier.v: verify_mixing`; `Examples/VerificatumIns.v: verify_mixing_ins` |
| Completeness of the whole five-move protocol: the honest prover's derived witness (a = ⟨r, e⟩, c = Σ r, d = Σ_i β_i ∏_{k>i} e'_k, f = ⟨s, e⟩, e' = e∘π) satisfies the five equations, so round 2 accepts for every e and v | `Crypto/ShuffleTWProps.v: tw_derived_witness_correct`, `tw_full_completeness` |
| Honest-verifier zero knowledge of the whole protocol: with uniform β and ω, the bridging chain and the round-2 transcript have the same distribution as a simulator's that knows neither π nor s (hypothesis h_0 ∈ ⟨g⟩); the change of variables on β is `reshift` | `Crypto/ShuffleTWProps.v: tw_full_shvzk`, `chain_reshift`, `reshift_inverse` |
| Extraction algebra: witnesses for the unit vectors open the commitment; a witness for any e gives either a discrete-log relation among g, h_0..h_N or e' = Mᵀe, column sums one, ∏(Mᵀe) = ∏e, and w_j = Enc(1; −f_j) ∏ w'_i^{m_ji} | `Crypto/ShuffleTWSound.v: opening_from_unit`, `relation_A`, `relation_C`, `relation_D`, `relation_F`, `chain_unique` |
| A non-zero univariate polynomial has fewer roots than coefficients; k such polynomials of length ≤ d have a common non-root among more than k·d field elements | `Crypto/PolyRoots.v: roots_bound`, `common_nonroot` |
| Permutation-matrix lemma: columns summing to one and ∏_i (Mᵀe)_i = ∏_j e_j for all e, over a field with more than (N+1)² elements, make M a permutation matrix | `Crypto/ShuffleTWSound2.v: exists_unit_column`, `matrix_is_permutation` |
| Soundness: from witnesses for every unit vector and for every e, either a non-trivial discrete-log relation among g, h_0..h_N (a binding break) or a permutation π with w'_{π(j)} = w_j · Enc(1; f_j) for explicit f_j | `Crypto/ShuffleTWSound2.v: tw_soundness` |

All closed under the global context (the instantiation is at the Helios
group, whose primes are certified). The soundness theorem quantifies over
all batching vectors e, decided by enumerating F^{N+1} (F is finite, given
by a duplicate-free complete list): it is the statement that a prover who
can answer every e either knows the shuffle or breaks the commitment. The
statistical version for one uniformly random e, which needs the
Schwartz–Zippel bound for the polynomial ∏_i (Mᵀe)_i − ∏_j e_j, is not
proved and is recorded as future work in `plans/ZK_APPLICATIONS_PLAN.md`.
Not covered either: pre-computation (proofs of shuffles of commitments and
commitment-consistent proofs), key width and ciphertext width greater
than one, and elliptic-curve groups. The driver is
`Executable/Vmnverifier/main.ml`: byte trees, the SHA-256 random oracles
and PRG, the derivation of the independent generators, and the checks of
the protocol parameters against the certified group.

## U-Prove credentials and the U-Prove verifier

Step 2 of `plans/ZK_APPLICATIONS_PLAN.md`. Microsoft's U-Prove
(Cryptographic Specification V1.1 Revision 3, December 2013, unchanged in
Revisions 4 and 5 of March 2023 except for the note on the ROS attack
against parallel issuance and the deprecation of the subgroup construction;
Brands' credentials) is built from the library's protocols: a token has public key
h = γ^α with γ = g_0 g_1^{x_1} ⋯ g_n^{x_n} g_t^{x_t} [g_d^{x_d}], a
presentation with disclosed set D proves knowledge of α⁻¹ and of the
undisclosed x_i with g_0 g_t^{x_t} ∏_{i∈D} g_i^{x_i} = h^{α⁻¹} ∏_{i∉D}
g_i^{−x_i} [g_d^{−x_d}], which is the generalised Okamoto protocol with
bases (h, g_i for i ∉ D, [g_d]) and the spec's response convention
r = w + c·x; the Issuer's signature (σ_z', σ_c', σ_r') is a Chaum–Pedersen
proof of g_0 = g^{y_0} ∧ σ_z' = h^{y_0}; the scope-exclusive pseudonym
P_s = g_s^{x_p} and the attribute commitments c̃_i = g^{x_i} g_1^{õ_i} are
further linear equations over the same witness, so a presentation with
extensions is one Okamoto statement in the product space G^m, one
component per equation, verified with one challenge and shared responses.

| Claim | Rocq |
|---|---|
| Multi-exponentiation over any vector space (shared with the shuffles) | `Crypto/MultiExp.v: mexp`, `mexp_okamoto`, `mexp_cons`, `mexp_app`, `mexp_const_vid`, `mexp_single` |
| The token relation: h = γ^α and α·α⁻¹ = 1 give the multi-base statement over (h, hidden bases) with witness (α⁻¹, −x_i) | `Crypto/UProve.v: pres_relation` |
| Presentation with at least one hidden coordinate: completeness, special soundness (extraction of α⁻¹ and the hidden attributes), special honest-verifier zero knowledge, as the Okamoto theorems | `Crypto/UProve.v: pres_completeness`, `pres_simulator_completeness`, `pres_special_soundness`, `pres_shvzk` |
| Presentation with every attribute disclosed and no Device: the same as the Schnorr theorems | `Crypto/UProve.v: pres0_completeness`, `pres0_special_soundness`, `pres0_shvzk` |
| Figure 4: the reconstruction g^{σ_r'} g_0^{−σ_c'}, h^{σ_r'} σ_z'^{−σ_c'} with challenge σ_c' is an accepting Chaum–Pedersen transcript for (g_0, σ_z') = (g, h)^{y_0} (the generic Chaum–Pedersen reconstruction is `cp_reconstruct_accepting`) | `Crypto/UProve.v: sig_reconstruct_accepting`; `Crypto/OkamotoRows.v: cp_reconstruct_accepting` |
| Figure 8 (issuance): the issued token's reconstruction is the Prover's announcement (σ_a', σ_b'), and its signature statement holds for the Issuer's key | `Crypto/UProve.v: issue`, `issuance_reconstruct`, `issuance_statement` |
| Signature: special soundness (extraction of y_0) and honest-verifier zero knowledge, as the Chaum–Pedersen theorems | `Crypto/UProve.v: sig_special_soundness`, `sig_shvzk` |
| The product-space multi-exponentiation over the columns of the base rows is the vector of the rows' multi-exponentiations; the componentwise reconstructions T_j^{−c} ∏ B_j[i]^{r_i} with challenge c form an accepting Okamoto transcript in G^m | `Crypto/OkamotoRows.v: transpose`, `vexp_transpose`, `ext_reconstruct`, `ext_reconstruct_accepting` |
| Presentation with pseudonym and commitments: completeness, special soundness (one witness satisfying every component, so the pseudonym and the commitments are bound to the token's attributes), honest-verifier zero knowledge | `Crypto/OkamotoRows.v: ext_completeness`, `ext_special_soundness`, `ext_shvzk` |
| The U-Prove rows: the core row padded with identity bases for the openings, the pseudonym row (single base g_s at coordinate p, target P_s^{−1}), the commitment row (g at the attribute's coordinate, g_1 at the opening's, target c̃^{−1}) satisfy their equations for the honest witness | `Crypto/UProve.v: core_relation`, `nym_relation`, `commit_relation`; `Crypto/OkamotoRows.v: mexp_unit_row` |
| Fiat–Shamir verifier, Figure 4: a verified signature has h ≠ 1, σ_c' = Hs(σ_a', σ_b') for the reconstructed pair, and yields the accepting Chaum–Pedersen transcript | `Backend/UProveVerifier.v: verify_signature`, `verify_signature_accepting` |
| Fiat–Shamir verifier, Figure 10 without extensions: a verified proof has a = Ha(A) for the reconstructed announcement A and yields an accepting Okamoto transcript (Schnorr transcript when nothing is hidden) with challenge C(a) | `Backend/UProveVerifier.v: verify_presentation`, `verify_presentation_okamoto`, `verify_presentation_schnorr` |
| Fiat–Shamir verifier with extensions: every published digest (a, a_p, ã_i) is the hash of its reconstructed component and the transcript is accepting in G^m; the rows are built in Rocq from the parsed indices | `Backend/UProveVerifier.v: verify_ext`, `verify_ext_accepting`, `uprove_components`, `verify_uprove`, `verify_uprove_accepting` |
| Instantiation at P-256 with SHA-256 digests as integers; curve points from coordinates with the curve equation decided in Z/pZ and n·P = 0 by computation | `Examples/UProveIns.v: mk_G`, `verify_signature_ins`, `verify_presentation_ins`, `verify_uprove_ins` |

All closed under the global context. The driver
`Executable/Uproveverifier/main.ml` implements the hash formatting of spec
section 2.2 (length-prefixed octet strings, minimal big-endian field
elements, SEC1 points, the group description), recomputes the
Issuer-parameter digest P, x_t, the x_i, the token identifier and the
challenge c = H(⟨c_p, m_d⟩), and runs the twelve test vectors of the U-Prove
C# SDK (zero, two or five disclosed attributes; Device-protected or not;
with a pseudonym and two commitments): all accepted, and the tampered
variants (a response, a disclosed attribute, the signature response, a
commitment) rejected. Not covered: the 2048-bit subgroup profile (the
theorems are group-generic; there are no public test vectors), the
range-proof, set-membership, identity-escrow and revocation extensions,
and the theorem-level treatment of the scope element g_s (the driver
derives it from the scope string as the C# SDK does, hashing the scope
followed by the decimal strings of index, counter and iteration, and
checks it against the vectors; this differs from the byte encoding of spec
Figure 7). As for the other verifiers, the
random-oracle step from a hash-consistent accepting transcript to
soundness of the non-interactive proof is not formalised.

## BBS# credentials and the BBS# verifier

Step 3 of `plans/ZK_APPLICATIONS_PLAN.md`. BBS# (Desmoulins, Dumanois, Kane
and Traoré, "Making BBS Anonymous Credentials eIDAS 2.0 Compliant", ePrint
2025/619) is the pairing-free variant of BBS proposed for the EU Digital
Identity Wallet. The credential is the algebraic MAC MAC_BBS: Cm = g_0 · pk
· ∏ g_i^{m_i}, A = Cm^{1/(x+e)}, σ = (A, e), with B = Cm · A^{−e} = A^x for the
Issuer's key x (pk_I = g̃^x). A presentation blinds the holder's key,
pk_Blind = g^{sk+r}, randomises the MAC (Ā = A^{r_1 r_2}, D = Cm^{r_2},
B̄ = Ā^{−e} D^{r_1} = Ā^x), and proves B̄ = Ā^{−e} D^{r_1} ∧ g_0 pk_Blind
∏_{i∈D} g_i^{m_i} = D^{r_3} g^{r} ∏_{i∉D} g_i^{−m_i} with one challenge (the
validity proof, Figure 8), the discrete logarithm of pk_Blind (holder
binding, Figure 7, an ECSDSA signature) and, replacing the BBS pairing
check, a Chaum–Pedersen proof that B̄ = Ā^x ∧ pk_I = g̃^x (Figure 6), issued
by the Issuer online or obliviously in advance; the verifier's check is the
same in all three options. The generic pieces are in
`Crypto/OkamotoRows.v` (shared with U-Prove).

| Claim | Rocq |
|---|---|
| Several linear equations over one witness vector with one challenge are one Okamoto statement in the product space G^m: the transpose of the rows, the componentwise reconstruction, completeness, special soundness (one witness for all rows), honest-verifier zero knowledge | `Crypto/OkamotoRows.v: transpose`, `vexp_transpose`, `ext_reconstruct_accepting`, `ext_completeness`, `ext_special_soundness`, `ext_shvzk` |
| Chaum–Pedersen reconstruction (g^ρ c₁^{−c}, h^ρ c₂^{−c}) with challenge c is an accepting transcript; special soundness and zero knowledge of the discrete-logarithm-equality proof | `Crypto/OkamotoRows.v: cp_reconstruct_accepting`, `cp_special_soundness`, `cp_shvzk` |
| MAC_BBS: B = Cm · A^{−e} = A^x; the randomised credential satisfies B̄ = Ā^{−e} D^{r_1} = Ā^x and D^{r_3} = Cm | `Crypto/BBSSharp.v: mac_relation`, `rand_relation`, `rand_D_inv` |
| The honest holder's witness (−e, r_1, r_3, r, −m_U) satisfies both rows of the validity proof (additive key blinding, ECSchnorr variant); the multiplicative-blinding rows (ECDSA variant, Section 5.3) as well | `Crypto/BBSSharp.v: row1_relation`, `row2_relation`, `validity_relation`, `row2_mul_relation` |
| Validity proof: completeness, special soundness (a witness for both equations), honest-verifier zero knowledge, as the product-space Okamoto theorems | `Crypto/BBSSharp.v: validity_completeness`, `validity_special_soundness`, `validity_shvzk` |
| Holder binding: Schnorr theorems for pk_Blind = g^{sk+r} | `Crypto/BBSSharp.v: hb_completeness`, `hb_special_soundness`, `hb_shvzk` |
| π_DLEQ: Chaum–Pedersen theorems for (pk_I, B̄) = (g̃, Ā)^x | `Crypto/BBSSharp.v: dleq_reconstruct_accepting`, `dleq_special_soundness`, `dleq_shvzk` |
| Appendix C: a witness of the validity proof, the discrete logarithm x of π_DLEQ and the discrete logarithm of pk_Blind give, when w_1, w_2 ≠ 0, a MAC_BBS tag (Ā^{w_2/w_1}, −w_0) on (sk_B − w_3, the disclosed attributes, −w_U); w_1 = 0 gives the Issuer's key | `Crypto/BBSSharp.v: credential_extraction`, `issuer_key_extraction` |
| Soundness of the whole presentation: two accepting transcripts of each of the three proofs give x behind pk_I, sk_B behind pk_Blind and a MAC_BBS tag, or the Issuer's key, or a representation of g_0 pk_Blind ∏_D g_i^{m_i} in the bases g, g_i | `Crypto/BBSSharp.v: presentation_soundness` |
| Statistical anonymity of the randomised credential (Game 5 of the paper): for any two credentials the distribution of (Ā, D) over uniform (r_1, r_2) is the same, by the bijection (r_1, r_2) ↦ (r_1 a c'/(a' c), r_2 c/c') | `Crypto/BBSSharp.v: randomisation_uniform` |
| Fiat–Shamir verifier: verified π_HB, π_validity, π_DLEQ yield accepting Schnorr, product-space Okamoto and Chaum–Pedersen transcripts with the oracle challenges on the reconstructed announcements, and Ā ≠ 1 | `Backend/BBSSharpVerifier.v: verify_hb_accepting`, `verify_rows_accepting`, `verify_validity_accepting`, `verify_dleq_accepting`, `verify_presentation`, `verify_presentation_accepting` |
| Instantiation at P-256 (Issuer, holder and verifier sides) | `Examples/BBSSharpIns.v: cm_ins`, `mac_ins`, `rand_*_ins`, `validity_prove_ins`, `hb_prove_ins`, `dleq_prove_ins`, `verify_presentation_ins` |

All closed under the global context. There is no published BBS# test-vector
suite or wire format, so the driver `Executable/Bbssharpverifier/main.ml`
runs the whole protocol with the extracted code on both sides (the Issuer's
MAC and DLEQ proofs, the holder's presentation with the library's real
protocols, the certified verifier), computing the challenges as
hash_to_scalar of RFC 9380's expand_message_xmd (SHA-256) over an
IETF-BBS-style serialisation with one domain-separation tag per proof, and
deriving the generators by try-and-increment; this encoding is the driver's,
not a standard's. Ten tampered presentations (responses of each proof, a
disclosed attribute, B̄, pk_Blind, Ā = 1, the nonce, another Issuer key) are
rejected. Not covered: the oblivious issuance of π_DLEQ (Orrù et al.,
Appendix E; the verifier's check is the same as for the online proof), the
ECDSA holder-binding signature of the multiplicative variant (only its
validity rows are proved), revocation and pseudonyms. As for the other
verifiers, the random-oracle step from a hash-consistent accepting transcript
to soundness of the non-interactive proof is not formalised.

## Bayer–Groth shuffles and the Swiss Post verifier

Step 4 of `plans/ZK_APPLICATIONS_PLAN.md`. The shuffle argument of Bayer
and Groth (EUROCRYPT 2012) as specified for the Swiss Post e-voting system
(crypto-primitives specification 1.6.0, Section 9, Algorithms 9.7–9.26):
the prover commits to the permutation π (c_A = com(π; r), as m columns of
n entries), receives x, commits to b_i = x^{π(i)} (c_B), receives y, z, and
proves with the product argument that the committed d = y·π + b − z has
∏ d_i = ∏_i (y·i + x^i − z), and with the multi-exponentiation argument
that ∏ C_i^{x^i} = Enc(1; ρ) ∏ C'_i^{b_i}. The product argument is the
Hadamard argument (which reduces to the zero argument with the bilinear
map ⋆_y) followed by the single value product argument. Haines, Goré and
Sharma verified this shuffle in Coq before (S&P 2021); as for
Terelius–Wikström the point here is the reuse of the library's algebra
(the vector-space class, the product space of ciphertexts, the generic
multi-exponentiation of `Crypto/MultiExp.v`) and the certified verifier
run on the system's own test data. The sub-arguments are multi-round
protocols with several challenges; their completeness theorems are
obtained by rewriting each verification equation of
the specification as an identity of polynomial evaluations
(`veval`: Σ x^i v_i in any vector space, `pmul`: the Cauchy product with a
bilinear map, `star`: the specification's bilinear ⋆_y).

| Claim | Rocq |
|---|---|
| Polynomial evaluation Σ_i x^i v_i in a vector space: shifts, sums, scalar multiples, zero padding, the Cauchy product identity eval(p ⋆ q) = eval(p) ⋆ eval(q) for a bilinear map | `Crypto/BayerGroth.v: veval_cons`, `veval_shift`, `veval_map2`, `veval_pmul`, `feval_pmul_star` |
| Pedersen commitments com(a; r) = h^r ∏ g_i^{a_i} are homomorphic; ∏_i com(A_i; r_i)^{x^i} = com(Σ x^i A_i; Σ x^i r_i) | `Crypto/BayerGroth.v: com_add`, `com_scale`, `geval_com_list` |
| Single value product argument (Algorithms 9.25, 9.26): the honest argument on com(a; r) and ∏ a_i is accepted, for any challenge | `Crypto/BayerGroth.v: svp_completeness` |
| Zero argument (Algorithms 9.22, 9.23): Σ_i A_i ⋆_y B_i = 0 gives an accepted argument, for any challenge; the diagonal coefficient of the Cauchy product | `Crypto/BayerGroth.v: zero_completeness`, `conv_middle` |
| Hadamard argument (Algorithms 9.20, 9.21): the chain b_i = a_0 ∘ ⋯ ∘ a_i and its reduction to the zero argument on ((c_{A1}, …, c_{−1}), (c_{D0}, …, c_D)) | `Crypto/BayerGroth.v: hadamard_completeness`, `hadamard_zero_stmt`, `star_ones_hprefix` |
| Multi-exponentiation argument (Algorithms 9.15, 9.16): the cross-term identity ∏_k E_k^{x^k} = Enc(g^{b(x)}; τ(x)) ∏_i C_i^{x^{m−i−1} a(x)} for the diagonals of the exponent matrix, ciphertexts as the product space G^{l+1} | `Crypto/BayerGroth.v: multiexp_completeness`, `ceval_diag_row`, `diagonals` |
| Product argument (Algorithms 9.18, 9.19): the composition of the Hadamard and single value product arguments (m > 1) or the single value product argument alone (m = 1) | `Crypto/BayerGroth.v: product_completeness` |
| Shuffle argument (Algorithms 9.11, 9.12): for a permutation π of 0..N−1 and C'_i = Enc(1; ρ_i) C_{π(i)}, the derived witness d = y·π + b − z has ∏ d_i = ∏ (y·i + x^i − z), the re-encryption witness is ρ = −⟨ρs, b⟩, and the honest argument is accepted for all challenges x, y, z and all sub-argument challenges | `Crypto/BayerGroth.v: shuffle_completeness`, `shuffle_product_stmt`, `shuffle_mexp_C`, `fold_mul_perm`, `cmexp_chunks` |
| Fiat–Shamir verifiers: the Swiss Post verifier of each argument is by definition the interactive verifier at the RecursiveHash challenges (an oracle record whose fields receive the announcements in the specification's order: x from c_A; y, z from c_A, c_B; the Hadamard challenges from (c_A, c_b, c_B); the zero challenge from (c_{A0}, c_{Bm}, c_d, c_B, c_A); the single value product challenge from (c_Δ, c_δ, c_d, b, c_a); the multi-exponentiation challenge from (C matrix, C, c_A, c_{A0}, c_B, E)) | `Backend/BayerGrothVerifier.v: shuffle_challenges`, `shuffle_verify_fs`, `shuffle_verify_fs_spec`, `product_verify_fs_spec`, `hadamard_verify_fs_spec`, `zero_verify_fs_spec`, `svp_verify_fs_spec`, `multiexp_verify_fs_spec` |
| Fiat–Shamir completeness: the honest non-interactive provers (which query the oracle stage by stage on their own announcements) produce arguments that the Fiat–Shamir verifiers accept, for every oracle (for the Hadamard, product and shuffle arguments: every oracle whose Hadamard challenges are non-zero) | `Backend/BayerGrothVerifier.v: shuffle_prove_fs`, `shuffle_fs_completeness`, `product_fs_completeness`, `hadamard_fs_completeness`, `zero_fs_completeness`, `svp_fs_completeness`, `multiexp_fs_completeness` |
| Instantiation at the 3072-bit group of the Swiss Post test vectors (p = 2q + 1, g = 2), with q prime by an elliptic-curve certificate, p prime by Pocklington's criterion from q, and p = 2q + 1 and the order of g checked by computation, both sides | `Examples/primeQSP.v: prime_q_sp`; `Examples/BayerGrothIns.v: prime_q`, `prime_p`, `cofactor`, `g_order`, `shuffle_verify_fs_ins`, `shuffle_prove_fs_ins`, `shuffle_fs_completeness_ins` |
| k-special soundness algebra (Step 4.1): a polynomial of length ≤ k is determined by its values at k distinct points; the Lagrange basis of k distinct challenges and its coefficient matrix λ, the inverse of the Vandermonde matrix (Σ_j λ_{ij} x_j^m = δ_{im}); in any vector space, the coefficients of a polynomial with vector coefficients are the λ-combinations of its values at k distinct points | `Crypto/SigmaK.v: agree_nth`, `eval_lag_basis`, `vandermonde_inv`, `coeff_from_evals` |
| Soundness error of k-special soundness: a prover strategy accepted on fewer than k challenges of the challenge set lf is accepted with probability at most (k − 1)/|lf| under the uniform challenge | `Crypto/SigmaK.v: k_special_soundness_error` |
| Root multiset lemma (Step 4.3): ∏_i (r_i − z) = ∏_i (s_i − z) on more points z than factors gives a permutation of the roots | `Crypto/PolyPerm.v: prod_roots_perm` |
| The shuffle's product identity ∏_i (y a_i + b_i − z) = ∏_i (y·i + x^i − z), for all y in a set of more than 2N² values and all z in a set of more than N values, gives a permutation σ of 0..N−1 with a_i = σ(i) and b_i = x^{σ(i)} (a counting argument in place of Schwartz–Zippel, for a field in which 0, …, N−1 are distinct) | `Crypto/PolyPerm.v: perm_of_products` |
| Pedersen openings from k evaluations: if ∏_i c_i^{x_j^i} = com(a_j; r_j) for k distinct x_j then c_i = com(Σ_j λ_{ij} a_j; Σ_j λ_{ij} r_j); a binding break is two different openings of full length of one commitment | `Crypto/BayerGrothSound.v: geval_openings`, `binding_break`, `open_eq_or_break` |
| Zero argument, (2m+1)-special soundness: 2m + 1 accepting transcripts with distinct challenges and the same announcements give openings of c_A and c_B with Σ_i a_i ⋆_y b_i = 0, or a binding break (the ⋆-product's coefficient of x^{m+1} against the opening of c_{d,m+1} = com(0; 0)) | `Crypto/BayerGrothSound.v: zero_soundness` |
| Single value product argument, (n+1)-special soundness: n + 1 accepting transcripts give an opening a of c_a with ∏ a_i = b, or a binding break (Bayer–Groth's recursion x^{i+1} b̃_{i+1} = x^i b̃_i ã_{i+1} + x^i e_i makes x^n b a polynomial T_{n−1}(x) whose leading coefficient is ∏ a_i) | `Crypto/BayerGrothSound.v: svp_soundness`, `svpT_eval`, `svpT_lead` |
| Hadamard argument, soundness: for m non-zero Hadamard challenges x, n non-zero challenges y and a (2m+1)-transcript zero argument at each pair, the openings of c_A and c_b satisfy b = a_0 ∘ ⋯ ∘ a_{m−1}, or a binding break (zero_soundness at every pair, then the identities Σ_i x^{i+1}(a_{i+1} ⋆_y b_i − 1 ⋆_y b_{i+1}) = 0 in x and in y) | `Crypto/BayerGrothSound.v: hadamard_soundness` |
| Product argument, soundness: the composition of the Hadamard and single value product extractors for m > 1, the single value product extractor for m = 1: an opening of c_A with ∏ a_{ij} = b, or a binding break | `Crypto/BayerGrothSound.v: product_soundness` |
| Shuffle argument, soundness: a prover accepted on N values of x, more than 2N² values of y, more than N values of z and the sub-arguments' challenge sets at each tuple either breaks the binding of the commitment key or knows σ and ρ with C'_i = Enc(1; ρ_i) C_{σ(i)} for all i (c_A opened from two values of y, the product identity to σ by `perm_of_products` at every x, the re-encryption exponents by `coeff_from_evals` in the ciphertext space over the N values of x, with a reindexing lemma for ∏ C'_k^{x^{σ(k)}}) | `Crypto/BayerGrothSound.v: shuffle_soundness`, `cmexp_perm`, `perm_inv_spec` |
| Multi-exponentiation argument, 2m-special soundness: 2m accepting transcripts give openings A of c_A and ρ with C = Enc(1; ρ) ∏_i C_i^{A_i}, or a binding break (the inverse Vandermonde matrix in the ciphertext space applied to E · D^{−1} · Enc(g^{b(x)}; 0)^{−1} = Enc(1; τ)) | `Crypto/BayerGrothSound.v: multiexp_soundness` |
| Random-oracle step, rewinding form: a prover whose arguments are accepted by the Fiat–Shamir verifier under every reprogramming of the oracle tree (the oracle at index (jx, jy, jz, p, q, j, j', jm) returns the challenges of that index on the announcements of that argument) either breaks the binding of the commitment key or knows the shuffle witness; this is the deterministic content of the forking argument, whose probabilistic analysis (the loss in the number of oracle queries) is not formalised | `Backend/BayerGrothVerifier.v: shuffle_fs_soundness` |
| One-query non-interactive soundness of the single-challenge arguments: a prover who fixes the announcements and answers the oracle's value c with resp(c) either has the extractor's witness, or breaks the binding of the key, or is accepted with probability at most (k − 1)/|lf| over a uniform oracle value (k = 2m + 1, n + 1, 2m) | `Backend/BayerGrothVerifier.v: zero_fs_soundness_error`, `svp_fs_soundness_error`, `multiexp_fs_soundness_error` |
| Honest-verifier zero knowledge by a bijection of the randomness: if the honest prover's transcript on the uniformly random list l equals the simulator's output on Φ(l) for a bijection Φ of the lists of length k, the two transcript distributions are equal (as permutations of the distribution lists, in the form of `special_honest_verifier_zkp_perm`) | `Crypto/BayerGrothZK.v: zk_of_bijection`, `rand_bijection_perm` |
| Zero argument, perfect SHVZK: the simulator draws the responses ã, b̃, r̃, s̃, t̃ and the commitments c_{d,k} (k ≠ 0, m+1) at random and solves the three verification equations for c_{A0}, c_{Bm}, c_{d0}; the map from the prover's randomness (a_0, b_m, r_0, s_m, t) to the simulator's is a bijection given the discrete logarithms of the commitment key | `Crypto/BayerGrothZK.v: zero_shvzk`, `zreal_eq_zsim` |
| Single value product argument, perfect SHVZK (random ã, r̃, s̃, b̃_1..b̃_{n−2}, c_Δ; b̃_0 = ã_0 and b̃_{n−1} = x b are forced, c_d and c_δ solved) | `Crypto/BayerGrothZK.v: svp_shvzk`, `svp_prove_eq_ssim` |
| Hadamard argument, perfect SHVZK: c_{B1..m−2} random group elements, c_{B0} = c_{A0} and c_{B(m−1)} = c_b as the verifier demands, the zero argument simulated on the statement the verifier derives | `Crypto/BayerGrothZK.v: hadamard_shvzk`, `hreal_eq_hsim` |
| Product argument, perfect SHVZK: a random c_b with the simulated Hadamard and single value product arguments (m > 1), the simulated single value product argument alone (m = 1) | `Crypto/BayerGrothZK.v: product_shvzk`, `preal_eq_psim` |
| Multi-exponentiation argument, perfect SHVZK for single-message ElGamal (l = 1): random responses, c_{Bk} = h^{u_k} and E_k = (g^{u'_k}, g^{v_k}) random for k ∉ {0, m}, c_{Bm} = 1 and E_m = C, and c_{A0}, c_{B0}, E_0 solved from the three equations; the bijection uses the discrete logarithms of the key, the secret key and a discrete-logarithm function for g (g generates the group) | `Crypto/BayerGrothZK.v: multiexp_shvzk`, `mreal_eq_msim` |
| Shuffle argument, perfect SHVZK (l = 1): random commitments c_A, c_B and the simulated product and multi-exponentiation arguments on the statements the verifier derives | `Crypto/BayerGrothZK.v: shuffle_shvzk`, `shreal_eq_shsim` |

The 3071-bit q of the Swiss Post group is proved prime in
`Examples/primeQSP.v` by an elliptic-curve (ECPP) certificate of 107
steps, generated by PARI/GP's `primecert` and converted by
`bench/ecpp2coq.py` as for ElectionGuard (kernel check about 2.5 hours (about 9,300 s of CPU on an Apple M-series laptop, one 3071-bit step alone taking 406 s));
the 3072-bit p = 2q + 1 is then prime by Pocklington's criterion
(`PocklingtonCorollary1` of Coqprime with the factored part q of p − 1 and
the witness 2, whose order is checked by `g_order`), in
`Examples/BayerGrothIns.v: prime_q`, `prime_p`. The driver
`Executable/Bgverifier/main.ml` verifies all cases of the six verifier
test-vector files of Swiss Post's crypto-primitives library
(`verify-shuffle-argument.json` and the five sub-arguments; m ∈ {1, 2, 8},
n ∈ {2, 3, 8}, l ∈ {1, 2, 4}), recomputing RecursiveHash (SHA3-256) as
the library does and checking the recomputed challenges x, y, z against
the values recorded in the fixtures; tampered arguments (swapped
ciphertexts, a commitment multiplied by g, a response of each sub-argument
incremented, a wrong re-encryption, a changed statement) are rejected, and
the extracted honest Fiat–Shamir prover's arguments on fresh shuffles are
accepted. Soundness (Steps 4.1 to 4.3, `Crypto/SigmaK.v`, `Crypto/PolyPerm.v`,
`Crypto/BayerGrothSound.v`): the k-special soundness algebra and the
polynomial lemmas are proved once, generically, and every argument has its
extractor, composed into `shuffle_soundness`: a prover who answers every
challenge tuple of the stated sets acceptingly either breaks the binding
of the commitment key or knows the permutation and the re-encryption
exponents. The statement is in the perfect-adversary form of the
Terelius–Wikström theorem (transcripts for all challenges of the sets),
not a probabilistic knowledge-soundness bound; `k_special_soundness_error`
gives the per-round (k−1)/|lf| bound that a probabilistic statement would
compose. The verifiers of `Crypto/BayerGroth.v` check that the response
vectors have the commitment key's length (`length (za_a arg) =? length gs`
and its analogues in the zero, single value product and
multi-exponentiation verifiers) and that the Hadamard challenges x, y are
non-zero (Bayer and Groth draw them in Z_q^*; Swiss Post's verifier does
not check it, so ours rejects, with probability 2/q, an argument Swiss
Post would accept), so the soundness theorems have no hypothesis on the
transcripts beyond their acceptance (`zero_verify_lengths`,
`svp_verify_length`, `multiexp_verify_length`, `hadamard_verify_nonzero`).
In exchange the completeness theorems require the honest prover's vectors
to have the key's length, and the Fiat–Shamir completeness theorems of the
Hadamard, product and shuffle arguments hold for every oracle whose
Hadamard challenges are never zero (`o_xh O cA cb cB <> zero`), the
statement that matches the random oracle up to probability 2/q per
argument. Random-oracle step (`Backend/BayerGrothVerifier.v`):
`shuffle_fs_soundness` is `shuffle_soundness` for the Fiat–Shamir verifier
under every reprogramming of the oracle tree, and
`zero_fs_soundness_error`, `svp_fs_soundness_error`,
`multiexp_fs_soundness_error` are the one-query bounds of the
single-challenge arguments; the probabilistic forking lemma (the loss in
the number of oracle queries) is not formalised, as for the other
verifiers. Zero knowledge (Step 4.2, `Crypto/BayerGrothZK.v`): every
sub-argument and the shuffle have a simulator whose output distribution
on uniformly random coins equals the honest prover's (perfect SHVZK, as an
equality of the two distribution lists up to permutation), proved by
`zk_of_bijection` from an explicit bijection between the prover's coins and
the simulator's. The simulators need the discrete logarithms of the
commitment key (as `special_honest_verifier_zkp_perm` needs the challenge
set closed under shifts), and the multi-exponentiation and shuffle
simulators are for single-message ElGamal (l = 1) with a generator g whose
discrete-logarithm function is a hypothesis: a random ciphertext is then a
pair of random group elements, which is what makes the E_k of the
simulated argument identically distributed. For l > 1 the argument is
only computationally zero-knowledge (the E_k are encryptions under DDH),
which the finite-distribution framework does not express; the Swiss Post
fixtures with l = 2, 4 are covered by the verifier and the soundness
theorems, not by the zero-knowledge theorems.

## Receipt-free Schulze tally

The position-encoded Schulze protocol: a ballot is
`Enc(s_i)` for every candidate with a membership proof `s_i ∈ {0..m}`
(ties allowed, `m` = unranked), and for every pair `(i, j)` a bit
`Enc(b_ij)` with a 0/1 proof and one membership proof of
`K·b_ij + (s_j − s_i) ∈ {−m..0} ∪ {K+1..K+m}`, `K = 2m+1`, where the
verifier computes `Enc(s_j)/Enc(s_i)` itself. The margins `Enc(D_ij)` are
the homomorphic products of the bits. The trustees publish encrypted
defeats `d`, encrypted strongest paths `p` and a certificate (range
proofs, the defeat and closure disjunctions as ORs of Chaum–Pedersen
statements over `G × G`, witness paths with per-edge proofs, winner
inequalities) that the verifier checks against the margins.

| Claim | Rocq |
|---|---|
| Ballot format, voter and verifier | `Frontend/Schulze.v: pos_cell`, `pair_cell`, `ballot`, `encrypt_ballot`, `verify_ballot` |
| A ballot with positions `≤ m` is accepted; also for the non-interactive ballot (one SHAKE challenge over the ciphertexts and announcements) | `Frontend/Schulze.v: ballot_valid`, `nizk_ballot_valid` |
| Special soundness of a ballot: two accepting transcripts with the same announcements and different challenges give positions `s`, `s_i ≤ m`, with every plaintext bit `b_ij = [s_i < s_j]`. Hypotheses: `exp_injective g` (`g` has order `q`) and `natF_injective (4m+2)` (the field has characteristic above `4m+2`) | `Frontend/Schulze.v: ballot_sound` (helpers `membership_sound`, `bit_sound`, `pair_decode`) |
| SHVZK of a ballot *(permutation form)* | `Frontend/Schulze.v: ballot_zk` |
| Aggregation `Enc(D_ij) = ∏ Enc(b_ij)` and its plaintext | `Frontend/Schulze.v: aggregate_margins`, `aggregate_margins_enc`, `cdec_aggregate`, `margin_count` |
| Schulze over `Z`: defeats, strongest paths; a certificate `cert_ok d p paths` (`p ≥ d`, `p` closed, a witness path of strength `p_ij` for every pair) characterises the min-max closure of `d`, the closure is unique, and the certified winner is the winner of every closure | `Backend/SchulzeTally.v: defeat`, `cert_ok`, `schulze_winner`, `is_closure`, `cert_ok_is_closure`, `closure_unique`, `cert_winner`; boolean form `cert_ok_b_sound`, `schulze_winner_b_sound` |
| The certificate and its verifier; the honest trustees (decryption by a bounded discrete-log search, closure by Kleene iteration on tabulated matrices, breadth-first path search; neither is in the trusted base, `cert_ok_b` checks the result) | `Backend/SchulzeTally.v: tally_proof`, `verify_tally`, `tally_checks`, `generate_tally`, `decrypt_margins`, `minmax_closure`, `witness_path` |
| Completeness: a certificate for a correct plaintext certificate is accepted; with the trustees' own (unverified, but checked by `cert_ok_b`) closure algorithm; with the true margins, since the discrete-log search is correct under injectivity; and non-interactively | `Backend/SchulzeTally.v: verify_tally_complete`, `verify_tally_complete_auto`, `verify_tally_complete_inj`, `decrypt_margins_correct`, `nizk_tally_complete` |
| Special soundness of the certificate: two accepting transcripts on margins `D ∈ [0, N]` give `d = defeat D`, `cert_ok d p paths` and `schulze_winner p w`. Hypotheses: `exp_injective g`, `natF_injective (2N² + 3N)` | `Backend/SchulzeTally.v: verify_tally_sound` (extractors `range_sound`, `or_sound`, `reenc_sound`, `defeat_sound`, `upper_sound`, `verify_path_sound`) |
| SHVZK of the certificate *(permutation form)* | `Backend/SchulzeTally.v: tally_zk` |
| End to end: `k ≤ N` accepting ballot pairs and an accepting certificate pair on their aggregate give positions whose margins have `w` as the Schulze winner of every closure | `Backend/SchulzeTally.v: schulze_end_to_end` |
| Tallying as an inductive state machine (`ax`, `cvalid`, `cinvalid`, `finish`) with the invariant `Permutation us (vbs ++ inbs)`; the running margins are the aggregate of the valid ballots; the executable count; a true verdict with rewinding transcripts certifies the winner | `Backend/SchulzeTally.v: state`, `count`, `count_partial_aggregate`, `count_finished_true`, `compute_final_tally`, `compute_final_count`, `count_sound` |
| Fiat–Shamir: one challenge per ballot and per certificate | `Frontend/Schulze.v: nizk_encrypt_ballot`, `nizk_verify_ballot`; `Backend/SchulzeTally.v: nizk_generate_tally`, `nizk_verify_tally` |
| Every element other than 1 of the Schnorr group has order `q`; exponentiation with such a base is injective; `Z_q` has characteristic `q` | `Utility/SchnorrOrder.v: prime_order`, `pow_injective`, `natF_injective_below_q` |
| Instantiation (`q = 2963`, three candidates, five ballots): the two hypotheses are discharged, `h = g^x` is checked by computation, and the soundness theorems hold with no hypothesis beyond the transcripts | `Examples/SchulzeIns.v: exp_injective_g`, `natF_injective_ins`, `h_eq`, `ballot_sound_ins`, `schulze_end_to_end_ins`, `count_sound_ins`, `tally_complete_ins`, `compute_final_count_ins` |
| Instantiation at the 2048-bit Helios parameters, generic in `m` and `N`, for the benchmark | `Examples/SchulzeBenchIns.v: nizk_encrypt_ballot_bench`, `nizk_verify_ballot_bench`, `nizk_generate_tally_bench`, `nizk_verify_tally_bench` |
| Σ-protocol for the preimage of a linear map `φ : F^W → V` (V any vector space): completeness, special soundness (witness `(z − z')/(c − c')`), perfect SHVZK *(permutation form)* | `Crypto/LinearSigma.v: lin_completeness`, `lin_soundness`, `lin_shvzk` |
| The batched ballot: `m²` ciphertexts `Enc(b_ij)`, Pedersen vector commitments to `s, δ, b, p = b∘δ` and to the bits `X` of `v = −δ + 2p − b`, a linear-relation proof (commitment openings, the random-linear-combination link `∏ Enc(b_ij)^{β_ij} = Enc(⟨β,b⟩)`, `δ = Ms`, `v = Σ 2^k X^(k)`), and three zero arguments (`p = b∘δ`, `X ∈ {0,1}`, `b ∈ {0,1}`); the honest ballot is accepted, also non-interactively (ten oracle queries, three prover passes) | `Frontend/SchulzeBatched.v: ballot2`, `verify_ballot2`, `encrypt_ballot2`, `ballot2_valid`, `challenges_of`, `nizk_verify_ballot2`, `nizk_encrypt_ballot2`, `nizk_ballot2_valid` |
| Special soundness of the batched ballot, perfect-adversary form: accepted on a base coefficient tuple and on a tuple differing in each single coordinate of `β`, `γ₁`, `γ₂` (two challenges each), and on the zero arguments at `m²` (resp. `Lm²`) distinct non-zero `y` with `2r+1` challenges each ⇒ a binding break of a commitment key, or positions `pos ≤ 2·2^L` with `Dec(Enc(b_ij)) = g^{[pos_i < pos_j]}`. Hypotheses: `h = g^x`, `L ≥ 1`, `natF_injective (3·2^L + 2)`; no hypothesis on the order of `g` (roots are taken in the vector space, `root_unique`) | `Frontend/SchulzeBatched.v: ballot2_sound` (extractors `lin_open`, `open_agree`, `zero_bits_open`, `zero_prod_open`, `beta_bits`, `gamma_rows`, `decode_positions`) |
| SHVZK of the batched ballot *(permutation form)*: over the voter's randomness (K encryption randomnesses, 5 commitment randomnesses, the announcement of the linear proof, the randomness of the three zero arguments), the honest ballot is a permutation of the output of a simulator given the ciphertexts and the challenges: five uniform commitments `h₁^u`, then the linear proof and the zero arguments from the library's simulators. Hypotheses: positions ≤ m, `m < 2^L`, known discrete logarithms of the commitment keys in base `h₁` (as in the library's zero-argument simulator) | `Frontend/SchulzeBatched.v: ballot2_real_dist`, `ballot2_sim_dist`, `ballot2_zk` (via `real_proofs_perm`, `com_vals_perm`) |
| End to end with batched ballots: `k ≤ N` batched ballots each with the rewinding transcripts of `ballot2_sound` (`ballot2_rewound`) and an accepted certificate (two transcripts) on the aggregate of their ciphertext matrices ⇒ a binding break of a commitment key, or positions `ss` (each ≤ 2·2^L) whose Schulze winner (of the pairwise margins, unique closure) is the certified candidate. Hypotheses: `h = g^x`, `exp_injective g` (for the certificate), `L ≥ 1`, key lengths, `natF_injective (3·2^L + 2 + 2N² + 3N)` | `Backend/SchulzeBatchedTally.v: aggregate_bits`, `cdec_aggregate_bits`, `fin_choice_or`, `schulze_end_to_end2`; `Frontend/SchulzeBatched.v: ballot2_rewound`, `ballot2_sound_bits` |
| Instantiation of the batched ballot at the Helios parameters for the benchmark | `Examples/SchulzeBenchIns.v: encrypt_ballot2_bench`, `nizk_verify_ballot2_bench` |
| The simplified batched ballot (tutorial §7.9–7.10): one commitment key `gs₁`; `C_δ = com_{g'}(s; ρ_δ)` under the derived key `g'_i = ∏_k g_k^{M_ki}`, which is a commitment to `Ms` under `gs₁` (`com_gd`); `L` commitments to the bit vectors `X^(t)`; the verifier forms `C₀ = C_δ C_b C_p^{-2} ∏ C_{X(t)}^{2^t}` and the voter opens it as `h₁^{ρ*}`; a five-row linear argument into `G^5` (witness `(s, b, ρ_δ, ρ_b, R, ρ*)`) and one zero argument with `L+3` rows weighted by powers of a challenge `z`; the honest ballot is accepted, also non-interactively (five challenges `β, y, z, c, x`, three prover passes) | `Frontend/SchulzeSimple.v: ballot3`, `verify_ballot3`, `encrypt_ballot3`, `com_gd`, `ballot3_valid`, `challenges_of3`, `nizk_verify_ballot3`, `nizk_encrypt_ballot3`, `nizk_ballot3_valid` |
| Special soundness of the simplified batched ballot, perfect-adversary form: accepted by the linear argument on a base `β` and on a `β` differing in each single coordinate (two challenges each), and by the zero argument on `m²` distinct non-zero `y` and `L+2` distinct non-zero `z` with `2(L+3)+1` challenges each ⇒ a binding break of `(h₁, gs₁)`, or positions `pos ≤ 2·2^L` with `Dec(Enc(b_ij)) = g^{[pos_i < pos_j]}`. Hypotheses: `h = g^x`, `L ≥ 1`, `natF_injective (3·2^L + 2)`. The row weights `z^i` are separated by the Vandermonde argument in `z` (`weighted_sum_eval`, `coeffs_vanish`), the coordinates by the one in `y` (`prod_of_star`, `bits_of_star`); the openings of `C_p` and the `C_{X(t)}` come from one accepted zero argument (`zero_open_ref`) and agree across all others by binding (`zero_open_at`) | `Frontend/SchulzeSimple.v: ballot3_sound`, `ballot3_rewound`, `ballot3_sound_bits` (extractors `lin_open3`, `phi3_target_open`, `zero_open_ref`, `zero_open_at`, `C0_open`; reuses `beta_bits`, `decode_positions`) |
| SHVZK of the simplified batched ballot *(permutation form)*: over the voter's randomness (K encryption randomnesses, L+3 commitment randomnesses, the announcement of the linear proof, the randomness of the zero argument), the honest ballot is a permutation of the output of a simulator given the ciphertexts and the challenges: L+3 uniform commitments `h₁^u`, then the linear proof and the zero argument from the library's simulators. Hypotheses: positions ≤ m, `m < 2^L`, known discrete logarithms of `gs₁` in base `h₁` (the derived key needs none of its own, by `com_gd`) | `Frontend/SchulzeSimple.v: ballot3_real_dist`, `ballot3_sim_dist`, `ballot3_zk` (via `real_proofs_perm3`, `com_vals_perm3`) |
| End to end with simplified batched ballots: `k ≤ N` ballots each with the rewinding transcripts of `ballot3_sound` (`ballot3_rewound`) and an accepted certificate (two transcripts) on the aggregate of their ciphertext matrices ⇒ a binding break of `(h₁, gs₁)`, or positions `ss` (each ≤ 2·2^L) whose Schulze winner (of the pairwise margins, unique closure) is the certified candidate. Hypotheses as for `schulze_end_to_end2` with one key | `Backend/SchulzeSimpleTally.v: schulze_end_to_end3` (reuses `aggregate_bits`, `cdec_aggregate_bits`, `fin_choice_or`) |
| Instantiation of the simplified batched ballot at the Helios parameters for the benchmark (m = 17: 180 KB, 0.67 s to prove, 1.5 s to verify, against 352 KB, 4.2 s, 5.7 s for the batched ballot in the same run) | `Examples/SchulzeBenchIns.v: encrypt_ballot3_bench`, `nizk_verify_ballot3_bench`, `gd_bench`; `Executable/SchulzeBenchcode/simple.ml` |

The example program is `Executable/Schulzecode/main.ml` (it walks the
`count` derivation ballot by ballot), the benchmarks are
`Executable/SchulzeBenchcode/main.ml` (first ballot) and `batched.ml`
(batched ballot) (`bench/README.md`). Soundness is
stated in the rewinding form (two transcripts); the random-oracle step
for the non-interactive versions is not formalised. The closure algorithm
of the honest trustees is not verified: the certificate it produces is
checked by `cert_ok_b` before publication and by `verify_tally_sound`
after it.

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
instances, the extractor complexity result, the approval-voting
theorems in `Frontend/Approval.v` and `Backend/Tally.v` and the
receipt-free Schulze theorems in `Frontend/Schulze.v`,
`Backend/SchulzeTally.v`, `Utility/SchnorrOrder.v` and
`Examples/SchulzeIns.v` report `Closed under the global context`. (The discrete-logarithm search that the tally
driver supplies is not trusted: `cfinish` checks `g ^ pt_i = ds_i` for
every candidate and records the outcome in the final state, exactly as
`Backend/HeliosTally.v` does, so no axiom about the search is needed.)
Of the 337 entries, 311 are closed; the remaining 26 report the following,
expected, assumptions. No theorem takes a primality hypothesis: every
prime of the case studies is certified (Pocklington or elliptic-curve
certificates checked by Coqprime).

| Theorem | Assumptions | Why |
|---|---|---|
| `Backend/SchulzeTally.v: decrypt_margins_correct`, `verify_tally_complete_inj`; `Examples/SchulzeIns.v: tally_complete_ins` | `functional_extensionality_dep` | The margins decrypted by the trustees' discrete-log search are shown equal, as a function on candidate pairs, to the true margins, so that completeness can be restated over the true margins (`Stdlib.Logic.FunctionalExtensionality`). The soundness and end-to-end theorems do not use it. |
| `Examples/TallyIns.v: compute_final_count_ins` | `proof_irrelevance` | Identifies two proofs of primality when instantiating the tally (`Stdlib.Logic.ProofIrrelevance`). |
| `Examples/HeliosTallyIns.v: prime_q`, `prime_p`, `compute_final_count_ins`; `Examples/HeliosFrontendIns.v: helios_nizk_encrypt_ballot_and_generate_enc_proof`, `helios_verify_encryption_ballot_proof`; `Examples/SchulzeBenchIns.v: nizk_encrypt_ballot_bench`, `nizk_verify_tally_bench` | `Uint63Axioms.*`, `PrimInt63.*` | The Coqprime primality certificates for the 256-bit `q` and 2048-bit `p` compute with Rocq's primitive 63-bit integers, whose specification is axiomatised in the standard library (`Stdlib.Numbers.Cyclic.Int63.Uint63Axioms`). Everything instantiated at the Helios parameters inherits them. |
| `Examples/ElectionGuardIns.v: prime_q`, `prime_p`, `g_order`, `compute_final_count_ins`, `verify_range_or_accepting_ins`, `verify_decryption_schnorr_accepting_ins`; `Examples/primeQEG.v: prime_q_eg`; `Examples/primePEG.v: prime_p_eg`; `Examples/BigNPow.v: bpow_mod_spec` | `Uint63Axioms.*`, `PrimInt63.*` | The same primitive-integer axioms: the Pocklington certificate of `q = 2^256 − 189`, the elliptic-curve certificate of the 4096-bit `p` and the in-kernel check `g^q = 1 mod p`, computed over Bignums' BigN, use them. |
| `Examples/primeQSP.v: prime_q_sp`; `Examples/BayerGrothIns.v: prime_q`, `prime_p`, `g_order`, `shuffle_verify_fs_ins`, `shuffle_prove_fs_ins`, `shuffle_fs_completeness_ins` | `Uint63Axioms.*`, `PrimInt63.*` | The elliptic-curve certificate of the 3071-bit q and the in-kernel check `2^q = 1 mod p` for the 3072-bit Swiss Post group, computed over BigN as for ElectionGuard; `prime_p` is derived from both, and everything instantiated at the Swiss Post group inherits them. |
