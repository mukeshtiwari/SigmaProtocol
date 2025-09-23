From Stdlib Require Import Utf8 ZArith.
From Crypto Require Import Elgamal.
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

 
  Definition encrypt (m r : @Zp q) : 
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@Elgamal.enc (@Zp q) (@Schnorr_group p q)
     (@mul_schnorr_group p q prime_p prime_q) pow g h m r).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.


  Definition decrypt (c :  @Schnorr_group p q * @Schnorr_group p q) : @Schnorr_group p q.
  Proof.
    refine(@Elgamal.dec (@Zp q) (@Schnorr_group p q) 
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    pow x c).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  
  Definition re_encryption (c :  @Schnorr_group p q * @Schnorr_group p q) (r : @Zp q) : 
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@Elgamal.re_enc (@Zp q) (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q) pow 
    g h c r).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

 
  Definition multiply_cipher (c₁ c₂ : @Schnorr_group p q * @Schnorr_group p q) : 
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@Elgamal.mul_cipher (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q)
      c₁ c₂).
  Defined.

 
  Definition encrypt_ballot {n : nat} (ms rs : Vector.t (@Zp q) n) : 
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.encrypted_ballot (@Zp q) (@Schnorr_group p q) 
      (@mul_schnorr_group p q prime_p prime_q) pow g h n ms rs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  Definition decrypt_ballot {n : nat}  (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.decrypted_ballot (@Zp q) (@Schnorr_group p q)
     (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
     (@mul_schnorr_group p q prime_p prime_q) pow x n cs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.


  Definition reencrypt_ballots {n : nat} (cs :  Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) 
    (rs : Vector.t (@Zp q) n) :  Vector.t (@Schnorr_group p q * @Schnorr_group p q) n. 
  Proof.
    refine(@Elgamal.re_encryption_ballot (@Zp q) (@Schnorr_group p q) 
      (@mul_schnorr_group p q prime_p prime_q) pow g h n cs rs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.
    

  Definition multiply_encrypted_ballots {n : nat} (cs₁ cs₂ : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :  
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.mul_encrypted_ballots (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q) n cs₁ cs₂).
  Defined.

End Ins.




    
    
    
 










