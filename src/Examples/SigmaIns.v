From Stdlib Require Import Utf8 ZArith.
From Crypto Require Import Sigma.
From Utility Require Import Zpstar.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup.


Section Ins.
  
  (* Prime q*)
  Definition q : Z := 593.

  (* Prime p *)
  Definition p : Z := 1187.

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
  
  Definition g : @Schnorr_group p q :=
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := eq_refl : (4 ^ q mod p)%Z = 1%Z|}.
  
    (* public key *)
  Definition h : @Schnorr_group p q := 
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x.
  
  (* u is the randomness for commitment and c is the challenge. 
  For the moment, it is random but I need to *)
  Definition schnorr_protocol_construction_ins (u c : @Zp q) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1.
  Proof.
    refine (@schnorr_protocol Zp zp_add zp_mul 
      Schnorr_group pow x g u c).
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply prime_p.
    eapply prime_q. 
  Defined.

  (* Non-interactive: u is randomness and c is computed using 
  hashing*)
  (* 
  Definition nizk_schnorr_protocol_construction_ins 
    (fn : @Schnorr_group p q -> String.string) (gn : N -> @Zp q) (u : @Zp q) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1.
  Proof.
    refine (@nizk_schnorr_protocol (@Schnorr_group p q) (@Zp q) fn gn 
      zp_add zp_mul pow x g h u).
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply prime_p.
    eapply prime_q. 
  Defined.
  *)


  Definition schnorr_protocol_verification_ins : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1 -> bool.
  Proof. 
    intro transcript.
    refine (@accepting_conversation (@Zp q) (@Schnorr_group p q)  
      mul_schnorr_group pow Schnorr.dec_zpstar g h transcript).
    eapply prime_p.
    eapply prime_q.
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
