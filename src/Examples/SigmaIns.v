From Stdlib Require Import Utf8 ZArith.
From Crypto Require Import Sigma.
From Utility Require Import Zpstar.
Import Vspace Schnorr Zpfield Zpgroup.


Section Ins.
  
  (* Prime q*)
  Definition q : Z := 11.
  (* Prime p *)
  Definition p : Z := 23.
  (* Prime Proof *)
  Theorem prime_q : Znumtheory.prime q : Prop : Type.
  Proof. compute. Admitted. 
  Theorem prime_p : Znumtheory.prime p : Prop : Type. 
  Proof. compute. Admitted.
  (* safe prime *)
  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.
  (* secret key *)
  Definition x : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.
  (* group generator *)
  Definition g : @Schnorr_group p q := 
    {| Schnorr.v := 2;
    Ha := conj eq_refl eq_refl : (0 < 2 < p)%Z;
    Hb := eq_refl : (2 ^ q mod p)%Z = 1%Z|}.
  (* public key *)
  Definition h : @Schnorr_group p q := 
    Eval compute in @pow 2 23 11 safe_prime prime_p prime_q g x.
  (* u is the randomness for commitment and c is the challenge. 
  For the moment, it is random but I need to *)
  Definition schnorr_protocol_construction (u c : @Zp q) : 
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1.
  Proof.
    refine (@schnorr_protocol Zp zp_add zp_mul 
      Schnorr_group pow x g u c).
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply prime_p.
    eapply prime_q. 
  Defined.

  Definition schnorr_protocol_verification : 
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
