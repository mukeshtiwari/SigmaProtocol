From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma 
  AndSigma.
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
  
  (* first secret key *)
  Definition x₁ : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.


  (* second secret key *)
  Definition x₂ : @Zp q :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  (* third secret key *)
  Definition x₃ : @Zp q :=
    {| Zpfield.v := 8; Zpfield.Hv := eq_refl : (8 mod q)%Z = 8%Z |}.

 
  (* group generator *)
  Definition h₁ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₁) p;
    Ha := conj eq_refl eq_refl : 
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₁) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g) q p)).
  Defined.

  (* group generator *)
  Definition h₂ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₂) p;
    Ha := conj eq_refl eq_refl : 
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₂) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g) q p)).
  Defined.

  (* group generator *)
  Definition h₃ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₃) p;
    Ha := conj eq_refl eq_refl : 
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₃) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g) q p)).
  Defined.

  Definition construct_and_conversations_schnorr_commitment_ins
    (us : Vector.t (@Zp q) 3) : Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@construct_and_conversations_schnorr_commitment 
      (@Zp q) (@Schnorr_group p q) pow _ g us).
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  
  Definition construct_and_conversations_schnorr_ins (us : Vector.t (@Zp q) 3) (c : (@Zp q)) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 3.
  Proof.
    refine(@construct_and_conversations_schnorr (@Zp q) 
    zp_add zp_mul (@Schnorr_group p q) pow 3 [x₁; x₂; x₃] g us c).
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  Definition nizk_construct_and_conversations_schnorr_ins 
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (us : Vector.t (@Zp q) 3)  : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 3.
  Proof.
    set (comm := construct_and_conversations_schnorr_commitment_ins us).
    set (c := fn _ ([inl p; inl q; inr g; inr h₁; inr h₂; inr h₃] ++ 
      Vector.map inr comm)).
    refine(construct_and_conversations_schnorr_ins us c).
  Defined.


  Definition generalised_and_accepting_conversations_ins : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 3 ->  bool.
  Proof.
    intro proof.
    refine (@generalised_and_accepting_conversations (@Zp q) (@Schnorr_group p q)  
    mul_schnorr_group pow Schnorr.dec_zpstar _ g [h₁; h₂; h₃] proof).
    eapply prime_p.
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.


