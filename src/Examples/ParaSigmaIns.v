From Stdlib Require Import Utf8 ZArith.
From Crypto Require Import Sigma 
  ParallelSigma.
From Utility Require Import Zpstar.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup.

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
  
  (* public key *)
  Definition h : @Schnorr_group p q := 
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x.

  (* us is the randomness for commitment and cs is the challenge. 
  For the moment, it is random but I need to *)
  Definition construct_parallel_conversations_schnorr_ins
    (us cs : Vector.t (@Zp q) 2) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 2 2.
  Proof.
    refine 
    (@construct_parallel_conversations_schnorr (@Zp q) 
    zp_add zp_mul (@Schnorr_group p q) pow 2 x g us cs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  
  Definition generalised_parallel_accepting_conversations_ins : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 2 2 -> bool.
  Proof.
    intro transcript.
    refine
    (@generalised_parallel_accepting_conversations (@Zp q) (@Schnorr_group p q)  
    mul_schnorr_group pow Schnorr.dec_zpstar _ g h transcript).
    eapply prime_p.
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.

