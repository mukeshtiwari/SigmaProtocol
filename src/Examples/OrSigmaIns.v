From Stdlib Require Import Utf8 ZArith 
Vector Fin.
From Crypto Require Import Sigma OrSigma.
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
  

  
  Definition h₁ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 12;
    Ha := conj eq_refl eq_refl : (0 < 12 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 12 q p)).
  Defined.

  (* secret key *)
  Definition x : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.
  
  (* group generator *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  (* we know the secret corresponding to this public key *)
  Definition h₂ : @Schnorr_group p q := 
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x.
  
  Definition h₃ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  Definition construct_or_conversations_schnorr_commitment_ins 
     (uscs : Vector.t (@Zp q) 5)  : 
     Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@construct_or_conversations_schnorr_commitment (@Zp q)
      zp_opp (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q)
      pow 1 1 g [h₁; h₂; h₃] (uscs)).
      eapply prime_q.
      exact safe_prime.
      eapply prime_p.
      eapply prime_q.
  Defined.

  Definition generalised_construct_or_conversations_schnorr_ins 
    (uscs : Vector.t (@Zp q) 5) (c : (@Zp q)) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 4 3.
  Proof.
    (* Try to fake a proof here and see how it get rejected by 
      the verifier. To fake a proof, put some random data 
      for (Fin.FS Fin.F1) x g [h₁; h₂; h₃]  *)
    refine(@generalised_construct_or_conversations_schnorr 
      (@Zp q) zero zp_add zp_mul zp_sub zp_opp 
      (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q)
      pow _ (Fin.FS Fin.F1) x g [h₁; h₂; h₃] (uscs) c).
      eapply prime_q.
      eapply prime_q.
      exact safe_prime.
      eapply prime_p.
      eapply prime_q.
  Defined.

  
  Definition generalised_or_accepting_conversations_ins 
    (pf :  @sigma_proto (@Zp q) (@Schnorr_group p q) 3 4 3) : bool.
  Proof.
    refine(@generalised_or_accepting_conversations 
    (@Zp q) zero zp_add zp_dec (@Schnorr_group p q) 
    (@mul_schnorr_group p q prime_p prime_q) pow
    Schnorr.dec_zpstar 3 g [h₁; h₂; h₃] pf).
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.