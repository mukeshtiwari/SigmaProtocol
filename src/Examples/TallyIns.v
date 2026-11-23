From Stdlib Require Import Utf8 ZArith Vector.
From Sigma Require Import Sigma EncProof.
From Backend Require Import Tally.
From Utility Require Import Zpstar Util.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup
  VectorNotations.

(** * Approval-voting tally: the trustee side over a toy Schnorr group

    This file instantiates the end-to-end tally of [Backend/Tally.v] over
    the toy group of [Examples/ApprovalIns.v]: the order-[q] subgroup of
    [Z_p^*] with [q = 2963] and the safe prime [p = 2q + 1 = 5927],
    generator [g = 4], secret key [x = 1234] and public key
    [h = 3210 = g^x]. It is the server-side counterpart of
    [Examples/ApprovalIns.v]. The trustee holds [x], aggregates the valid
    ballots homomorphically, decrypts the totals, and proves correct
    decryption with Chaum–Pedersen proofs.

    The single computational definition, [compute_final_count_ins], is
    extracted by [src/Extraction/Tallylib/Extraction.v] and driven by
    [src/Executable/Tallycode]. The parameters are for testing only. *)
Section Ins.

  (** The prime order [q] of the subgroup. *)
  Definition q : Z := 2963.

  (** The safe prime [p = 2q + 1]. *)
  Definition p : Z := 2 * q + 1.

  (** Primality of [q] and [p] by trial division up to the square root, and
      the safe-prime equation. *)
  Theorem prime_q : Znumtheory.prime q : Prop : Type.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  Theorem prime_p : Znumtheory.prime p : Prop : Type.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.

  (** The generator [g = 4], whose membership in the subgroup is checked by
      [vm_compute]. *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  (** The trustee's secret key [x = 1234]. *)
  Definition x : @Zp q.
  Proof.
    refine {| Zpfield.v := 1234;
    Zpfield.Hv := eq_refl : (1234 mod q)%Z = 1234%Z |}.
  Defined.

  (** The public key [h = 3210 = g^1234]. *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 3210;
    Ha := conj eq_refl eq_refl : (0 < 3210 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 3210 q p)).
  Defined.

  (** The trustee's tally ([Tally.compute_final_count]) for ballots with [n]
      entries. It returns the valid and invalid ballots, the plaintext totals
      [pt], the verdict, and a [count] derivation that justifies them. Its
      arguments are:

      - [discrete_logarithm_search], which recovers totals from [g^t] and is
        supplied by the caller (a small search in the extracted program);
      - [us] and [cs], the commitment randomness and challenges of the
        decryption proofs;
      - [bs], the ballots.

      The side condition [g^x = h] is discharged by computation, and the
      remaining equalities between proof components of the Schnorr-group
      records are closed with the proof-irrelevance axiom
      ([ProofIrrelevance.PI.proof_irrelevance]). The axiom is used in a
      [Prop] argument only, so it is erased by extraction. *)
  Definition compute_final_count_ins {n : nat}
    (discrete_logarithm_search : @Schnorr_group p q -> @Schnorr_group p q ->
    (@Zp q))
    (us cs : Vector.t (@Zp q) n)
    (bs :  list (@ballot (@Zp q) (@Schnorr_group p q) n)) :
    existsT (vbs inbs :
      list (@ballot (@Zp q) (@Schnorr_group p q) n))
      (pt : Vector.t (@Zp q) n) (bfinal : bool),
      @count (@Zp q) (@Zpfield.zero q prime_q)
      (@Zpfield.one q prime_q) zp_add zp_dec
      (@Schnorr_group p q)
      (@Schnorr.one p q prime_p prime_q)
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow 2 p q safe_prime prime_p prime_q)
      Schnorr.dec_zpstar n g h
     (finished bs vbs inbs pt bfinal).
  Proof.
    refine(@compute_final_count (@Zp q) (@Zpfield.zero q prime_q)
      (@Zpfield.one q prime_q) zp_add zp_mul
      zp_sub zp_div zp_opp zp_inv zp_dec
      (@Schnorr_group p q) Schnorr.one
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow 2 p q safe_prime prime_p prime_q)
       Schnorr.dec_zpstar n g h pow_vspace
       discrete_logarithm_search x us cs _ bs).
    compute; f_equal.
    eapply ProofIrrelevance.PI.proof_irrelevance.
    eapply ProofIrrelevance.PI.proof_irrelevance.
  Defined.

End Ins.
