From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma EncProof.
From Backend Require Import Tally.
From Utility Require Import Zpstar Util.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup
  VectorNotations.

Section Ins.

  (* Prime q*)
  Definition q : Z := 2963.

  (* Prime p *)
  Definition p : Z := 2 * q + 1.
  
  (* Prime Proof *)
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
  
  
  (* safe prime *)
  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.

  (* group generator *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  Definition x : @Zp q.
  Proof.
    refine {| Zpfield.v := 1234; 
    Zpfield.Hv := eq_refl : (1234 mod q)%Z = 1234%Z |}.
  Defined.


   
  Definition h : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 3210;
    Ha := conj eq_refl eq_refl : (0 < 3210 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 3210 q p)).
  Defined.
 (*end of group generator *)

  (* rs is the randomness used to encrypt 0 
      us and cs is the randomess used to construct 
      decryption proof. 
  *)
  Definition compute_final_count_ins {n : nat} 
    (discrete_logarithm_search : @Schnorr_group p q -> @Schnorr_group p q ->
    (@Zp q))
    (rs : Vector.t (@Zp q) n) (us cs : Vector.t (@Zp q) (n + n))
    (bs :  list (Vector.t (@Schnorr_group p q * @Schnorr_group p q * 
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n)) : 
    existsT (vbs inbs : 
      list (Vector.t (@Schnorr_group p q * @Schnorr_group p q * 
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n))
      (pt : Vector.t (@Zp q) n), 
      @count (@Zp q) (@Zpfield.zero q prime_q) 
      (@Zpfield.one q prime_q) zp_add zp_dec
      (@Schnorr_group p q) 
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) 
      (@pow 2 p q safe_prime prime_p prime_q) 
      Schnorr.dec_zpstar n g h 
     (finished bs vbs inbs pt).
  Proof.
    refine(@compute_final_count (@Zp q) (@Zpfield.zero q prime_q) 
      (@Zpfield.one q prime_q) zp_add zp_mul 
      zp_sub zp_div zp_opp zp_inv zp_dec 
      (@Schnorr_group p q) Schnorr.one 
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) 
      (@pow 2 p q safe_prime prime_p prime_q)
       Schnorr.dec_zpstar n g h pow_vspace 
       discrete_logarithm_search x rs us cs _ bs).
    compute; f_equal.
    (* We have decidable equality so we can use 
    Eqdep_dec.eq_proofs_unicity_on  *)
    eapply ProofIrrelevance.PI.proof_irrelevance.
    eapply ProofIrrelevance.PI.proof_irrelevance.
  Defined.
  
End Ins.


