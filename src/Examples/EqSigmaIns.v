From Stdlib Require Import Utf8 ZArith 
Vector Fin.
From Crypto Require Import Sigma EqSigma.
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

  Definition x : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  
  Definition g₁ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 12;
    Ha := conj eq_refl eq_refl : (0 < 12 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 12 q p)).
  Defined.

  
  Definition h₁ : @Schnorr_group p q := 
    Eval vm_compute in @pow _ _ _ safe_prime prime_p prime_q g₁ x.

  
  Definition g₂ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 16;
    Ha := conj eq_refl eq_refl : (0 < 16 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 16 q p)).
  Defined.


  Definition h₂ : @Schnorr_group p q := 
    Eval vm_compute in @pow _ _ _ safe_prime prime_p prime_q g₂ x.


Definition g₃ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 18;
    Ha := conj eq_refl eq_refl : (0 < 18 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 18 q p)).
  Defined.


  Definition h₃ : @Schnorr_group p q := 
    Eval vm_compute in @pow _ _ _ safe_prime prime_p prime_q g₃ x.

  Definition hfake : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  Definition construct_eq_conversations_schnorr_commitment_ins 
    (u : @Zp q) : Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@construct_eq_conversations_schnorr_commitment 
      (@Zp q) (@Schnorr_group p q) pow 1 [g₁; g₂; g₃] u).
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.


  Definition construct_eq_conversations_schnorr_ins (u c : @Zp q) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 1.
  Proof.
    refine(@construct_eq_conversations_schnorr (@Zp q)
      zp_add zp_mul (@Schnorr_group p q) pow 1 x [g₁; g₂; g₃] u c). 
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  Definition nizk_construct_eq_conversations_schnorr_ins 
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q)) 
    (u : @Zp q) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 1.
  Proof.
    set (comm := construct_eq_conversations_schnorr_commitment_ins u).
    set (c := fn _ ([inl p; inl q; inr g₁; inr h₁; inr g₂; inr h₂; inr g₃;
      inr h₃] ++ Vector.map inr comm)).
    refine(construct_eq_conversations_schnorr_ins u c).
  Defined.


  Definition generalised_eq_accepting_conversations_ins 
    (proof :  @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 1) : bool.
  Proof.
    refine(@generalised_eq_accepting_conversations (@Zp q) (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q) pow
      Schnorr.dec_zpstar 1 [g₁; g₂; g₃] [h₁; h₂; h₃] proof).
    (* try replacing one of the hs with hfake *)
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.
  
End Ins.






