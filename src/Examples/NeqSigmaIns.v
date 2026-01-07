From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma 
  NeqSigma.
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

  Definition g₁ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.
  
  (* first secret key *)
  Definition x₁ : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  (* group generator *)
  Definition h₁ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g₁) (Zpfield.v x₁) p;
    Ha := conj eq_refl eq_refl : 
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g₁) (Zpfield.v x₁) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g₁) q p)).
  Defined.


  Definition g₂ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 7;
    Ha := conj eq_refl eq_refl : (0 < 7 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 7 q p)).
  Defined.


  (* second secret key *)
  Definition x₂ : @Zp q :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  
  (* group generator *)
  Definition h₂ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g₂) (Zpfield.v x₂) p; (* replace this x₂ with x₁ 
    or x₃ and it will fail. *)
    Ha := conj eq_refl eq_refl : 
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g₂) (Zpfield.v x₂) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g₂) q p)).
  Defined.

  Definition g₃ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 13;
    Ha := conj eq_refl eq_refl : (0 < 13 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 13 q p)).
  Defined.

  (* third secret key *)
  Definition x₃ : @Zp q :=
    {| Zpfield.v := 8; Zpfield.Hv := eq_refl : (8 mod q)%Z = 8%Z |}.


  (* group generator *)
  Definition h₃ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g₃) (Zpfield.v x₃) p;
    Ha := conj eq_refl eq_refl : 
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g₃) (Zpfield.v x₃) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g₃) q p)).
  Defined.

  Definition generalised_construct_neq_commitment_ins 
    (us : Vector.t (@Zp q) 9) : Vector.t (@Schnorr_group p q) 6.
  Proof.
    refine(@generalised_construct_neq_commitment (@Zp q)
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) 
    (@pow 2 p q safe_prime prime_p prime_q) _ 
    [g₁; g₂; g₃] [h₁; h₂; h₃] us).
  Defined.

  
  Definition generalised_construct_neq_conversations_real_transcript_ins 
    (us : Vector.t (@Zp q) 9) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 6 1 9.
  Proof.
    refine (@generalised_construct_neq_conversations_real_transcript 
    (@Zp q) zp_add zp_mul zp_sub zp_inv  
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ 
    [x₁; x₂; x₃] [g₁; g₂; g₃] [h₁; h₂; h₃] us c).
  Defined.

  Definition nizk_generalised_construct_neq_conversations_real_transcript_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (us : Vector.t (@Zp q) 9) : @sigma_proto (@Zp q) (@Schnorr_group p q) 6 1 9.
  Proof.
    set (comm := generalised_construct_neq_commitment_ins us).
    set (c := fn _ ([inl p; inl q; inr g₁; inr h₁; inr g₂; inr h₂; 
      inr g₃; inr h₃] ++ Vector.map inr comm)).
    exact (generalised_construct_neq_conversations_real_transcript_ins us c).
  Defined.

  Definition generalised_neq_accepting_conversations_ins : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 6 1 9 -> bool.
  Proof.
    intro pf.
    refine(@generalised_neq_accepting_conversations (@Zp q)
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q)
    Schnorr.dec_zpstar _ [g₁; g₂; g₃] [h₁; h₂; h₃]
    pf).
  Defined.

End Ins.



    
  





