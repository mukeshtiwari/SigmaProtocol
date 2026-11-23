(* Axiom audit for every theorem listed in THEOREMS.md.
   Run with bench/assumptions.sh after `dune build`. Every line should
   print "Closed under the global context"; the only expected exceptions
   are compute_final_count_ins in Examples/TallyIns.v, which uses
   proof_irrelevance, and the Helios, ElectionGuard and Swiss Post
   instantiations, which inherit the primitive-integer axioms
   (Uint63Axioms and PrimInt63) of the Bignums-based Coqprime
   certificates and in-kernel exponentiations (BigNPow). No theorem of
   the repository takes a primality hypothesis. *)

From Stdlib Require Import Utf8.
From Probability Require Import Prob Distr.
From Algebra Require Import Product_space Vector_product_space.
From Utility Require Import Zpstar Functions SchnorrOrder.
From Sigma Require Import LinearSigma.
From Sigma Require Import Sigma ParallelSigma AndSigma AndSigmaGen EqSigma
  OrSigma OrSigmaGen ChaumPedersen EncProof DecProof Okamoto NeqSigma
  PedLinearRel Elgamal MultiExp ShuffleTW ShuffleTWProps ShuffleTWSound ShuffleTWSound2 PolyRoots
  OkamotoRows UProve BBSSharp SigmaK PolyPerm BayerGroth BayerGrothSound BayerGrothZK.
From Frontend Require Import Approval Schulze SchulzeBatched SchulzeSimple.
From Backend Require Import SchulzeBatchedTally SchulzeSimpleTally.
From Backend Require Import Tally HeliosTally BeleniosTally ElectionGuardTally FiatShamirLinRel
  VerificatumVerifier UProveVerifier BBSSharpVerifier BayerGrothVerifier SchulzeTally.
From Examples Require Import ApprovalIns TallyIns HeliosTallyIns
  HeliosFrontendIns PedLinearRelIns Ed25519Ins BeleniosIns
  ElectionGuardIns BigNPow primeQEG primePEG primeQSP P256Ins UProveIns BBSSharpIns BayerGrothIns
  SchulzeIns SchulzeBenchIns.
From Curve Require Import Ed25519 P256 P256Primes.

(* Schnorr *)
Print Assumptions Sigma.Sigma.schnorr_completeness.
Print Assumptions Sigma.Sigma.simulator_completeness.
Print Assumptions Sigma.Sigma.special_soundness_berry.
Print Assumptions Sigma.Sigma.special_honest_verifier_zkp.
Print Assumptions Sigma.Sigma.special_honest_verifier_zkp_perm.
Print Assumptions Sigma.Sigma.special_honest_verifier_zkp_enum.
Print Assumptions Sigma.Sigma.schnorr_protocol_simulator_shift.
Print Assumptions Sigma.Sigma.soundness_error_bound.

(* Distributions *)
Print Assumptions Probability.Distr.bind_ret_left.
Print Assumptions Probability.Distr.bind_ret_right.
Print Assumptions Probability.Distr.bind_assoc.
Print Assumptions Probability.Distr.uniform_with_replacement_adds_to_one.
Print Assumptions Probability.Distr.uniform_probability.
Print Assumptions Probability.Distr.uniform_probability_multidraw_prob.
Print Assumptions Probability.Distr.event_uniform_prob.
Print Assumptions Probability.Distr.list_of_events_uniform.
Print Assumptions Probability.Distr.uniform_perm.
Print Assumptions Probability.Distr.bind_ret_perm.
Print Assumptions Probability.Distr.repeat_uniform_perm.
Print Assumptions Probability.Distr.repeat_uniform_bijection_perm.

(* Parallel *)
Print Assumptions Sigma.ParallelSigma.construct_parallel_conversations_schnorr_completeness.
Print Assumptions Sigma.ParallelSigma.construct_parallel_conversations_simulator_completeness.
Print Assumptions Sigma.ParallelSigma.generalise_parallel_sigma_soundness.
Print Assumptions Sigma.ParallelSigma.generalised_parallel_special_honest_verifier_zkp.
Print Assumptions Sigma.ParallelSigma.generalised_parallel_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.ParallelSigma.generalised_parallel_special_honest_verifier_zkp_enum.

(* And *)
Print Assumptions Sigma.AndSigma.construct_and_conversations_schnorr_completeness.
Print Assumptions Sigma.AndSigma.construct_and_conversations_simulator_completeness.
Print Assumptions Sigma.AndSigma.generalise_and_sigma_soundness.
Print Assumptions Sigma.AndSigma.generalised_and_special_honest_verifier_zkp.
Print Assumptions Sigma.AndSigma.generalised_and_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.AndSigma.generalised_and_special_honest_verifier_zkp_enum.
Print Assumptions Sigma.AndSigmaGen.construct_and_conversations_schnorr_completeness.
Print Assumptions Sigma.AndSigmaGen.construct_and_conversations_simulator_completeness.
Print Assumptions Sigma.AndSigmaGen.generalise_and_sigma_soundness.
Print Assumptions Sigma.AndSigmaGen.generalise_and_sigma_soundness_neq.
Print Assumptions Sigma.AndSigmaGen.generalised_and_special_honest_verifier_zkp.
Print Assumptions Sigma.AndSigmaGen.generalised_and_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.AndSigmaGen.generalised_and_special_honest_verifier_zkp_enum.

(* Or *)
Print Assumptions Sigma.OrSigma.generalised_construct_or_conversations_schnorr_completeness.
Print Assumptions Sigma.OrSigma.generalised_construct_or_conversations_simulator_completeness.
Print Assumptions Sigma.OrSigma.generalised_or_sigma_soundness_main.
Print Assumptions Sigma.OrSigma.generalised_or_special_honest_verifier_zkp.
Print Assumptions Sigma.OrSigma.generalised_or_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.OrSigmaGen.generalised_construct_or_conversations_schnorr_completeness.
Print Assumptions Sigma.OrSigmaGen.generalised_construct_or_conversations_simulator_completeness.
Print Assumptions Sigma.OrSigmaGen.generalised_or_sigma_soundness_main.
Print Assumptions Sigma.OrSigmaGen.generalised_or_special_honest_verifier_zkp.
Print Assumptions Sigma.OrSigmaGen.generalised_or_special_honest_verifier_zkp_perm.

(* Eq, Chaum-Pedersen *)
Print Assumptions Sigma.EqSigma.construct_eq_conversations_schnorr_completeness.
Print Assumptions Sigma.EqSigma.construct_eq_conversations_simulator_completeness.
Print Assumptions Sigma.EqSigma.generalise_eq_sigma_soundness.
Print Assumptions Sigma.EqSigma.generalised_eq_special_honest_verifier_zkp.
Print Assumptions Sigma.EqSigma.generalised_eq_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.EqSigma.generalised_eq_special_honest_verifier_zkp_enum.
Print Assumptions Sigma.ChaumPedersen.construct_cp_conversations_schnorr_completeness.
Print Assumptions Sigma.ChaumPedersen.construct_cp_conversations_simulator_completeness.
Print Assumptions Sigma.ChaumPedersen.generalise_cp_sigma_soundness.
Print Assumptions Sigma.ChaumPedersen.generalised_cp_special_honest_verifier_zkp.
Print Assumptions Sigma.ChaumPedersen.generalised_cp_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.ChaumPedersen.generalised_cp_special_honest_verifier_zkp_enum.

(* ElGamal, encryption and decryption proofs *)
Print Assumptions Sigma.Elgamal.dec_is_left_inv_of_enc.
Print Assumptions Sigma.Elgamal.dec_re_enc_left_inv.
Print Assumptions Sigma.Elgamal.additive_homomorphic_property.
Print Assumptions Sigma.EncProof.generalised_construct_encryption_proof_elgamal_real_completeness.
Print Assumptions Sigma.EncProof.generalised_construct_encryption_proof_elgamal_simulator_completeness.
Print Assumptions Sigma.EncProof.generalised_accepting_elgamal_soundness_main.
Print Assumptions Sigma.EncProof.generalised_encryption_proof_elgamal_special_honest_verifier_zkp.
Print Assumptions Sigma.EncProof.generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.DecProof.construct_decryption_proof_elgamal_real_completeness.
Print Assumptions Sigma.DecProof.construct_decryption_proof_elgamal_simulator_completeness.
Print Assumptions Sigma.DecProof.decryption_proof_accepting_conversations_vector_completeness.
Print Assumptions Sigma.DecProof.special_soundness_construct_decryption_proof_elgamal.
Print Assumptions Sigma.DecProof.construct_decryption_proof_elgamal_special_honest_verifier_zkp.
Print Assumptions Sigma.DecProof.construct_decryption_proof_elgamal_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.DecProof.construct_decryption_proof_elgamal_special_honest_verifier_zkp_enum.

(* Okamoto, Neq, Pedersen linear relations *)
Print Assumptions Sigma.Okamoto.generalised_okamoto_real_accepting_conversation.
Print Assumptions Sigma.Okamoto.generalised_okamoto_simulator_accepting_conversation.
Print Assumptions Sigma.Okamoto.generalised_okamoto_real_special_soundness.
Print Assumptions Sigma.Okamoto.generalised_okamoto_special_honest_verifier_zkp.
Print Assumptions Sigma.Okamoto.generalised_okamoto_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.Okamoto.generalised_okamoto_special_honest_verifier_zkp_enum.
Print Assumptions Sigma.Okamoto.generalised_okamoto_witness_indistinguishable.
Print Assumptions Sigma.NeqSigma.generalised_neq_real_transcript_accepting_conversations.
Print Assumptions Sigma.NeqSigma.generalised_neq_simulator_transcript_accepting_conversations.
Print Assumptions Sigma.NeqSigma.generalised_neq_accepting_conversations_soundness.
Print Assumptions Sigma.NeqSigma.generalised_neq_special_honest_verifier_zkp.
Print Assumptions Sigma.NeqSigma.generalised_neq_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.PedLinearRel.pedersen_linear_relation_completeness.
Print Assumptions Sigma.PedLinearRel.pedersen_linear_relation_simulator_completeness.
Print Assumptions Sigma.PedLinearRel.pedersen_linear_relation_special_soundness.
Print Assumptions Sigma.PedLinearRel.generalised_pedersen_special_honest_verifier_zkp.
Print Assumptions Sigma.PedLinearRel.generalised_pedersen_special_honest_verifier_zkp_perm.
Print Assumptions Sigma.PedLinearRel.generalised_pedersen_special_honest_verifier_zkp_enum.

(* Modular arithmetic and the extractor *)
Print Assumptions Utility.Zpstar.Zpgroup.zpstar_comm.
Print Assumptions Utility.Zpstar.Zpfield.zp_field.
Print Assumptions Utility.Zpstar.Schnorr.schnorr_comm.
Print Assumptions Utility.Zpstar.Vspace.pow_vspace.
Print Assumptions Utility.Functions.correct_complexity_repeat_op_ntimes_rec.

(* Approval voting *)
Print Assumptions Frontend.Approval.vote_proof_valid.
Print Assumptions Frontend.Approval.vote_proof_invalid_reject.
Print Assumptions Frontend.Approval.vote_proof_invalid_accept.
Print Assumptions Frontend.Approval.ballot_proof_valid.
Print Assumptions Frontend.Approval.overall_proof_valid.
Print Assumptions Frontend.Approval.ballot_with_overall_proof_valid.
Print Assumptions Frontend.Approval.generate_enc_proof_commitment_announcement.
Print Assumptions Frontend.Approval.ballot_commitment_announcement.
Print Assumptions Frontend.Approval.vote_proof_sound.
Print Assumptions Frontend.Approval.overall_proof_sound.
Print Assumptions Backend.Tally.compute_final_count.
Print Assumptions Backend.Tally.finished_true_correct.
Print Assumptions Examples.ApprovalIns.nizk_encrypt_ballot_with_overall_proof_ins.
Print Assumptions Examples.TallyIns.compute_final_count_ins.

(* Helios *)
Print Assumptions Backend.HeliosTally.compute_final_count.
Print Assumptions Examples.HeliosTallyIns.prime_q.
Print Assumptions Examples.HeliosTallyIns.prime_p.
Print Assumptions Examples.HeliosTallyIns.compute_final_count_ins.
Print Assumptions Examples.HeliosFrontendIns.helios_nizk_encrypt_ballot_and_generate_enc_proof.
Print Assumptions Examples.HeliosFrontendIns.helios_verify_encryption_ballot_proof.
Print Assumptions Examples.PedLinearRelIns.construct_pedersen_linear_relation_commitment_ins.

(* Ed25519 instantiation *)
Print Assumptions Curve.Ed25519.Ed25519.Zl.zl_field.
Print Assumptions Curve.Ed25519.Ed25519.Zl.Fdec.
Print Assumptions Curve.Ed25519.Ed25519.Ed.ed25519_comm_group.
Print Assumptions Curve.Ed25519.Ed25519.Ed.Gdec.
Print Assumptions Curve.Ed25519.Ed25519.Ed.ed25519_vspace.
Print Assumptions Curve.Ed25519.Ed25519.Ed.fast_smul_eq.
Print Assumptions Curve.Ed25519.Ed25519.Ed.ed25519_vspace_fast.
Print Assumptions Curve.Ed25519.Ed25519.Ed.B_in_subgroup.
Print Assumptions Examples.Ed25519Ins.schnorr_protocol_verification_ins.
Print Assumptions Examples.Ed25519Ins.generalised_cp_accepting_conversations_ins.
Print Assumptions Examples.Ed25519Ins.verify_ballot_ins.
Print Assumptions Examples.Ed25519Ins.nizk_encrypt_ballot_with_overall_proof_ins.

(* Belenios verifier *)
Print Assumptions Algebra.Product_space.prod_vspace.
Print Assumptions Backend.BeleniosTally.fs_verify_schnorr_accepting.
Print Assumptions Backend.BeleniosTally.fs_verify_or_accepting.
Print Assumptions Backend.BeleniosTally.compute_final_count.
Print Assumptions Examples.BeleniosIns.compute_final_count_ins.

(* ElectionGuard verifier *)
Print Assumptions Backend.ElectionGuardTally.coefficient_proof_schnorr_accepting.
Print Assumptions Backend.ElectionGuardTally.verify_guardian_schnorr_accepting.
Print Assumptions Backend.ElectionGuardTally.verify_range_or_accepting.
Print Assumptions Backend.ElectionGuardTally.verify_decryption_schnorr_accepting.
Print Assumptions Backend.ElectionGuardTally.compute_final_count.
Print Assumptions Examples.BigNPow.BigNPow.bpow_mod_spec.
Print Assumptions Examples.primeQEG.prime_q_eg.
Print Assumptions Examples.primePEG.prime_p_eg.
Print Assumptions Examples.ElectionGuardIns.prime_q.
Print Assumptions Examples.ElectionGuardIns.prime_p.
Print Assumptions Examples.ElectionGuardIns.g_order.
Print Assumptions Examples.ElectionGuardIns.cofactor.
Print Assumptions Examples.ElectionGuardIns.compute_final_count_ins.
Print Assumptions Examples.ElectionGuardIns.verify_range_or_accepting_ins.
Print Assumptions Examples.ElectionGuardIns.verify_decryption_schnorr_accepting_ins.

(* Step 0 of plans/ZK_APPLICATIONS_PLAN.md: shared infrastructure *)
Print Assumptions Algebra.Vector_product_space.vec_vspace.
Print Assumptions Algebra.Vector_product_space.vec_dec.
Print Assumptions Backend.FiatShamirLinRel.reconstruct_linrel_accepting.
Print Assumptions Backend.FiatShamirLinRel.fs_verify_linrel_accepting.

(* P-256 instantiation *)
Print Assumptions Curve.P256Primes.prime_p256_p.
Print Assumptions Curve.P256Primes.prime_p256_n.
Print Assumptions Curve.P256.P256.Zn.zn_field.
Print Assumptions Curve.P256.P256.Wp.p256_comm_group.
Print Assumptions Curve.P256.P256.Wp.Gdec.
Print Assumptions Curve.P256.P256.Wp.p256_vspace.
Print Assumptions Curve.P256.P256.Wp.fast_smul_eq.
Print Assumptions Curve.P256.P256.Wp.p256_vspace_fast.
Print Assumptions Curve.P256.P256.Wp.B_in_subgroup.
Print Assumptions Examples.P256Ins.schnorr_protocol_verification_ins.
Print Assumptions Examples.P256Ins.verify_ballot_ins.

(* Terelius–Wikström shuffle, round 2 (Step 1.1 of plans/ZK_APPLICATIONS_PLAN.md) *)
Print Assumptions Sigma.ShuffleTW.tw_relation_iff.
Print Assumptions Sigma.ShuffleTW.tw_completeness.
Print Assumptions Sigma.ShuffleTW.tw_special_soundness.
Print Assumptions Sigma.ShuffleTW.tw_special_honest_verifier_zkp_enum.

(* Verificatum verifier (Step 1.2) *)
Print Assumptions Backend.VerificatumVerifier.verify_pos_accepting.
Print Assumptions Backend.VerificatumVerifier.verify_shuffling_spec.
Print Assumptions Backend.VerificatumVerifier.verify_decryption_accepting.

(* Terelius–Wikström, the whole protocol (Step 1.3) *)
Print Assumptions Sigma.ShuffleTWProps.tw_derived_witness_correct.
Print Assumptions Sigma.ShuffleTWProps.tw_full_completeness.
Print Assumptions Sigma.ShuffleTWProps.tw_full_shvzk.
Print Assumptions Sigma.PolyRoots.roots_bound.
Print Assumptions Sigma.PolyRoots.common_nonroot.
Print Assumptions Sigma.ShuffleTWSound.opening_from_unit.
Print Assumptions Sigma.ShuffleTWSound.relation_A.
Print Assumptions Sigma.ShuffleTWSound.relation_C.
Print Assumptions Sigma.ShuffleTWSound.relation_D.
Print Assumptions Sigma.ShuffleTWSound.relation_F.
Print Assumptions Sigma.ShuffleTWSound2.matrix_is_permutation.
Print Assumptions Sigma.ShuffleTWSound2.tw_soundness.

(* U-Prove (Step 2 of plans/ZK_APPLICATIONS_PLAN.md) *)
Print Assumptions Sigma.UProve.pres_relation.
Print Assumptions Sigma.UProve.pres_completeness.
Print Assumptions Sigma.UProve.pres_special_soundness.
Print Assumptions Sigma.UProve.pres_shvzk.
Print Assumptions Sigma.UProve.pres0_completeness.
Print Assumptions Sigma.UProve.pres0_special_soundness.
Print Assumptions Sigma.UProve.pres0_shvzk.
Print Assumptions Sigma.UProve.sig_reconstruct_accepting.
Print Assumptions Sigma.UProve.issuance_reconstruct.
Print Assumptions Sigma.UProve.issuance_statement.
Print Assumptions Sigma.UProve.sig_special_soundness.
Print Assumptions Sigma.UProve.sig_shvzk.
Print Assumptions Sigma.OkamotoRows.ext_reconstruct_accepting.
Print Assumptions Sigma.OkamotoRows.ext_completeness.
Print Assumptions Sigma.OkamotoRows.ext_special_soundness.
Print Assumptions Sigma.OkamotoRows.ext_shvzk.
Print Assumptions Sigma.UProve.core_relation.
Print Assumptions Sigma.UProve.nym_relation.
Print Assumptions Sigma.UProve.commit_relation.
Print Assumptions Backend.UProveVerifier.verify_signature_accepting.
Print Assumptions Backend.UProveVerifier.verify_presentation_okamoto.
Print Assumptions Backend.UProveVerifier.verify_presentation_schnorr.
Print Assumptions Backend.UProveVerifier.verify_ext_accepting.
Print Assumptions Backend.UProveVerifier.verify_uprove_accepting.
Print Assumptions Examples.UProveIns.verify_signature_ins.
Print Assumptions Examples.UProveIns.verify_presentation_ins.
Print Assumptions Examples.UProveIns.verify_uprove_ins.

(* BBS# (Step 3 of plans/ZK_APPLICATIONS_PLAN.md) *)
Print Assumptions Sigma.OkamotoRows.cp_reconstruct_accepting.
Print Assumptions Sigma.OkamotoRows.cp_special_soundness.
Print Assumptions Sigma.OkamotoRows.cp_shvzk.
Print Assumptions Sigma.BBSSharp.mac_relation.
Print Assumptions Sigma.BBSSharp.rand_relation.
Print Assumptions Sigma.BBSSharp.validity_relation.
Print Assumptions Sigma.BBSSharp.validity_completeness.
Print Assumptions Sigma.BBSSharp.validity_special_soundness.
Print Assumptions Sigma.BBSSharp.validity_shvzk.
Print Assumptions Sigma.BBSSharp.row2_mul_relation.
Print Assumptions Sigma.BBSSharp.hb_completeness.
Print Assumptions Sigma.BBSSharp.hb_special_soundness.
Print Assumptions Sigma.BBSSharp.hb_shvzk.
Print Assumptions Sigma.BBSSharp.dleq_reconstruct_accepting.
Print Assumptions Sigma.BBSSharp.dleq_special_soundness.
Print Assumptions Sigma.BBSSharp.dleq_shvzk.
Print Assumptions Sigma.BBSSharp.credential_extraction.
Print Assumptions Sigma.BBSSharp.issuer_key_extraction.
Print Assumptions Sigma.BBSSharp.presentation_soundness.
Print Assumptions Sigma.BBSSharp.randomisation_uniform.
Print Assumptions Backend.BBSSharpVerifier.verify_hb_accepting.
Print Assumptions Backend.BBSSharpVerifier.verify_dleq_accepting.
Print Assumptions Backend.BBSSharpVerifier.verify_rows_accepting.
Print Assumptions Backend.BBSSharpVerifier.verify_validity_accepting.
Print Assumptions Backend.BBSSharpVerifier.verify_presentation_accepting.
Print Assumptions Examples.BBSSharpIns.verify_presentation_ins.

(* Bayer–Groth shuffles and the Swiss Post verifier *)
Print Assumptions Sigma.BayerGroth.veval_pmul.
Print Assumptions Sigma.BayerGroth.feval_pmul_star.
Print Assumptions Sigma.BayerGroth.geval_com_list.
Print Assumptions Sigma.BayerGroth.svp_completeness.
Print Assumptions Sigma.BayerGroth.zero_completeness.
Print Assumptions Sigma.BayerGroth.hadamard_completeness.
Print Assumptions Sigma.BayerGroth.multiexp_completeness.
Print Assumptions Sigma.BayerGroth.product_completeness.
Print Assumptions Sigma.BayerGroth.shuffle_completeness.
Print Assumptions Backend.BayerGrothVerifier.svp_verify_fs_spec.
Print Assumptions Backend.BayerGrothVerifier.zero_verify_fs_spec.
Print Assumptions Backend.BayerGrothVerifier.hadamard_verify_fs_spec.
Print Assumptions Backend.BayerGrothVerifier.multiexp_verify_fs_spec.
Print Assumptions Backend.BayerGrothVerifier.product_verify_fs_spec.
Print Assumptions Backend.BayerGrothVerifier.shuffle_verify_fs_spec.
Print Assumptions Backend.BayerGrothVerifier.svp_fs_completeness.
Print Assumptions Backend.BayerGrothVerifier.zero_fs_completeness.
Print Assumptions Backend.BayerGrothVerifier.hadamard_fs_completeness.
Print Assumptions Backend.BayerGrothVerifier.multiexp_fs_completeness.
Print Assumptions Backend.BayerGrothVerifier.product_fs_completeness.
Print Assumptions Backend.BayerGrothVerifier.shuffle_fs_completeness.
Print Assumptions Examples.primeQSP.prime_q_sp.
Print Assumptions Examples.BayerGrothIns.prime_q.
Print Assumptions Examples.BayerGrothIns.prime_p.
Print Assumptions Examples.BayerGrothIns.cofactor.
Print Assumptions Examples.BayerGrothIns.g_order.
Print Assumptions Examples.BayerGrothIns.shuffle_fs_completeness_ins.
Print Assumptions Examples.BayerGrothIns.shuffle_verify_fs_ins.

(* k-special soundness algebra, polynomials and permutations, extractors *)
Print Assumptions Sigma.SigmaK.agree_nth.
Print Assumptions Sigma.SigmaK.vandermonde_inv.
Print Assumptions Sigma.SigmaK.coeff_from_evals.
Print Assumptions Sigma.SigmaK.k_special_soundness_error.
Print Assumptions Sigma.PolyPerm.prod_roots_perm.
Print Assumptions Sigma.PolyPerm.perm_of_products.
Print Assumptions Sigma.BayerGrothSound.geval_openings.
Print Assumptions Sigma.BayerGrothSound.zero_soundness.
Print Assumptions Sigma.BayerGrothSound.svp_soundness.
Print Assumptions Sigma.BayerGrothSound.zero_soundness_ext.
Print Assumptions Sigma.BayerGrothSound.hadamard_soundness.
Print Assumptions Sigma.BayerGrothSound.product_soundness.
Print Assumptions Sigma.BayerGrothSound.cmexp_perm.
Print Assumptions Sigma.BayerGrothSound.shuffle_soundness.
Print Assumptions Sigma.BayerGrothSound.multiexp_soundness.

(* random-oracle step: rewinding form and one-query bounds for the Fiat–Shamir verifiers *)
Print Assumptions Backend.BayerGrothVerifier.shuffle_fs_soundness.
Print Assumptions Backend.BayerGrothVerifier.zero_fs_soundness_error.
Print Assumptions Backend.BayerGrothVerifier.svp_fs_soundness_error.
Print Assumptions Backend.BayerGrothVerifier.multiexp_fs_soundness_error.

(* honest-verifier zero-knowledge simulators *)
Print Assumptions Sigma.BayerGrothZK.zk_of_bijection.
Print Assumptions Sigma.BayerGrothZK.zero_shvzk.
Print Assumptions Sigma.BayerGrothZK.svp_shvzk.
Print Assumptions Sigma.BayerGrothZK.hadamard_shvzk.
Print Assumptions Sigma.BayerGrothZK.product_shvzk.
Print Assumptions Sigma.BayerGrothZK.multiexp_shvzk.
Print Assumptions Sigma.BayerGrothZK.shuffle_shvzk.

(* receipt-free Schulze tally *)
Print Assumptions Frontend.Schulze.ballot_valid.
Print Assumptions Frontend.Schulze.nizk_ballot_valid.
Print Assumptions Frontend.Schulze.ballot_sound.
Print Assumptions Frontend.Schulze.ballot_zk.
Print Assumptions Frontend.Schulze.aggregate_margins_enc.
Print Assumptions Frontend.Schulze.cdec_aggregate.
Print Assumptions Backend.SchulzeTally.cert_ok_is_closure.
Print Assumptions Backend.SchulzeTally.closure_unique.
Print Assumptions Backend.SchulzeTally.cert_winner.
Print Assumptions Backend.SchulzeTally.cert_ok_b_sound.
Print Assumptions Backend.SchulzeTally.schulze_winner_b_sound.
Print Assumptions Backend.SchulzeTally.verify_tally_complete.
Print Assumptions Backend.SchulzeTally.verify_tally_complete_auto.
Print Assumptions Backend.SchulzeTally.decrypt_margins_correct.
Print Assumptions Backend.SchulzeTally.verify_tally_complete_inj.
Print Assumptions Backend.SchulzeTally.verify_tally_sound.
Print Assumptions Backend.SchulzeTally.schulze_end_to_end.
Print Assumptions Backend.SchulzeTally.nizk_tally_complete.
Print Assumptions Backend.SchulzeTally.tally_zk.
Print Assumptions Backend.SchulzeTally.count_partial_aggregate.
Print Assumptions Backend.SchulzeTally.count_finished_true.
Print Assumptions Backend.SchulzeTally.compute_final_count.
Print Assumptions Backend.SchulzeTally.count_sound.
Print Assumptions Utility.SchnorrOrder.prime_order.
Print Assumptions Utility.SchnorrOrder.pow_injective.
Print Assumptions Utility.SchnorrOrder.natF_injective_below_q.
Print Assumptions Examples.SchulzeIns.exp_injective_g.
Print Assumptions Examples.SchulzeIns.natF_injective_ins.
Print Assumptions Examples.SchulzeIns.h_eq.
Print Assumptions Examples.SchulzeIns.ballot_sound_ins.
Print Assumptions Examples.SchulzeIns.schulze_end_to_end_ins.
Print Assumptions Examples.SchulzeIns.count_sound_ins.
Print Assumptions Examples.SchulzeIns.tally_complete_ins.
Print Assumptions Examples.SchulzeIns.compute_final_count_ins.
Print Assumptions Examples.SchulzeBenchIns.nizk_encrypt_ballot_bench.
Print Assumptions Examples.SchulzeBenchIns.nizk_verify_tally_bench.

(* the batched Schulze ballot *)
Print Assumptions Sigma.LinearSigma.lin_completeness.
Print Assumptions Sigma.LinearSigma.lin_soundness.
Print Assumptions Sigma.LinearSigma.lin_shvzk.
Print Assumptions Frontend.SchulzeBatched.ballot2_valid.
Print Assumptions Frontend.SchulzeBatched.nizk_ballot2_valid.
Print Assumptions Frontend.SchulzeBatched.ballot2_sound.
Print Assumptions Frontend.SchulzeBatched.ballot2_zk.
Print Assumptions Backend.SchulzeBatchedTally.schulze_end_to_end2.

(* the simplified batched Schulze ballot (one key, one zero argument) *)
Print Assumptions Frontend.SchulzeSimple.com_gd.
Print Assumptions Frontend.SchulzeSimple.ballot3_valid.
Print Assumptions Frontend.SchulzeSimple.nizk_ballot3_valid.
Print Assumptions Frontend.SchulzeSimple.ballot3_sound.
Print Assumptions Frontend.SchulzeSimple.ballot3_sound_bits.
Print Assumptions Frontend.SchulzeSimple.ballot3_zk.
Print Assumptions Backend.SchulzeSimpleTally.schulze_end_to_end3.
Print Assumptions Examples.SchulzeBenchIns.nizk_verify_ballot3_bench.
