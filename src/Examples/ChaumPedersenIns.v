From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma 
  ChaumPedersen.
From Utility Require Import Zpstar.
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
  

  (* group generator *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 7;
    Ha := conj eq_refl eq_refl : (0 < 7 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 7 q p)).
  Defined.


  (* randomness *)
  Definition x : @Zp q :=
    {| Zpfield.v := 30; Zpfield.Hv := eq_refl : (30 mod q)%Z = 30%Z |}.

  (* c₁ = g^x ∧ c₂ = h^x *)
  Definition c₁ : @Schnorr_group p q.
  Proof.
    refine(pow g x).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Qed.

  Definition c₂ : @Schnorr_group p q.
  Proof.
    refine(pow h x).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Qed.



  Definition construct_cp_conversations_schnorr_ins 
    (u c : @Zp q ) : @sigma_proto (@Zp q) (@Schnorr_group p q) 2 1 1.
  Proof.
    refine(@construct_cp_conversations_schnorr (@Zp q)
    zp_add zp_mul (@Schnorr_group p q) pow x g h u c).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Defined.

  Definition generalised_cp_accepting_conversations_ins : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 1 1 -> bool.
  Proof.
    intros s.
    refine(@generalised_cp_accepting_conversations (@Zp q) 
    (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q) pow
    Schnorr.dec_zpstar g h c₁ c₂ s).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Defined.

End Ins.




 
