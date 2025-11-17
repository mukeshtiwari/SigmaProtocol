From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import DistElgamal.
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


  (* secret key of first Trustee*)
  Definition x₁ : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  (* public key of first Trustee *)
  Definition h₁ : @Schnorr_group p q := 
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x₁.

  (* secret key of second Trustee*)
  Definition x₂ : @Zp q :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  (* public key of second Trustee *)
  Definition h₂ : @Schnorr_group p q := 
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x₂.

  (* secret key of third Trustee *)
  Definition x₃ : @Zp q :=
    {| Zpfield.v := 7; Zpfield.Hv := eq_refl : (7 mod q)%Z = 7%Z |}.

  (* public key of third Trustee *)
  Definition h₃ : @Schnorr_group p q := 
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x₃.

  (* combined public key *)

  Definition h : @Schnorr_group p q.
  Proof.
    refine(@mul_schnorr_group p q prime_p prime_q h₁ 
      (@mul_schnorr_group p q prime_p prime_q h₂ h₃)).
  Defined.


  Definition encrypt_dist_value_ins (m r : @Zp q) : 
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.encrypt_value_dist (@Zp q) 
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) 
    (@pow 2 p q safe_prime prime_p prime_q) 
    _ g [h₁; h₂; h₃] m r).
  Defined.

  (* decryption factor of first tallier *)
  Definition decryption_factor_value_first_ins (c :  @Schnorr_group p q * @Schnorr_group p q) : 
    @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value_partial (@Zp q) 
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) c x₁).
  Defined.

  (* decryption factor of second tallier *)
  Definition decryption_factor_value_second_ins (c :  @Schnorr_group p q * @Schnorr_group p q) : 
    @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value_partial (@Zp q) 
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) c x₂).
  Defined.

  (* decryption factor of third tallier *)
  Definition decryption_factor_value_third_ins (c :  @Schnorr_group p q * @Schnorr_group p q) : 
    @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value_partial (@Zp q) 
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) c x₃).
  Defined.

  Definition decrypt_dist_value_ins (c :  @Schnorr_group p q * @Schnorr_group p q)
    (df₁ df₂ df₃ : @Schnorr_group p q) : @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value (@Schnorr_group p q)
    (@Schnorr.one p q prime_p prime_q)
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) _ c [df₁; df₂; df₃]).
  Defined.


  Definition encrypt_dist_ballot_ins {n : nat} (ms : Vector.t (@Zp q) n)
    (rs : Vector.t (@Zp q) n) :  Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.encrypt_ballot_dist (@Zp q) 
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) 
    (@pow 2 p q safe_prime prime_p prime_q) _ n g [h₁; h₂; h₃] ms rs).
  Defined.


  (* decryption factors of first tallier *)
  Definition decrypt_ballot_partial_first_ins {n : nat} 
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) : 
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_partial (@Zp q) 
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) n cs x₁).
  Defined.

  (* decryption factors of second tallier *)
  Definition decrypt_ballot_partial_second_ins {n : nat} 
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) : 
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_partial (@Zp q) 
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) n cs x₂).
  Defined.


  (* decryption factors of third tallier *)
  Definition decrypt_ballot_partial_third_ins {n : nat} 
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) : 
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_partial (@Zp q) 
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) n cs x₃).
  Defined.

  Definition decrypt_ballot_value_ins {n : nat} 
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n)
    (dfs₁ dfs₂ dfs₃ : Vector.t (@Schnorr_group p q) n) : 
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_value (@Schnorr_group p q)
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) _ n cs [dfs₁; dfs₂; dfs₃]).
  Defined.


End Ins.



