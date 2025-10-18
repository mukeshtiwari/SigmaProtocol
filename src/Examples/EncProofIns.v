From Stdlib Require Import Utf8 ZArith 
Vector Fin.
From Crypto Require Import Sigma EncProof.
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

  Definition g : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 12;
    Ha := conj eq_refl eq_refl : (0 < 12 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 12 q p)).
  Defined.

   
  Definition h : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  Definition m₀ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 28;
    Ha := conj eq_refl eq_refl : (0 < 28 < p)%Z;
    Hb := _ |}. 
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 28 q p)).
  Defined.

  Definition m₁ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 134;
    Ha := conj eq_refl eq_refl : (0 < 134 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 134 q p)).
  Defined.

  Definition m₂ : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 38;
    Ha := conj eq_refl eq_refl : (0 < 38 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 38 q p)).
  Defined.

  Definition mfake : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  (* randomness used in encryption  *)
  Definition r : @Zp q.
  Proof.
    refine {| Zpfield.v := 1876; Zpfield.Hv := _ |}.
    vm_cast_no_check (eq_refl ((1876 mod q)%Z)).
  Defined.

  (* we encrypt m₂ using the randomness r. *)
  Definition cp : (@Schnorr_group p q * @Schnorr_group p q).
  Proof.
    exact (@pow _ _ _ safe_prime prime_p prime_q g r, 
     (@mul_schnorr_group p q prime_p prime_q m₂ 
     (@pow _ _ _ safe_prime prime_p prime_q h r))).
  Defined.

  Definition construct_encryption_proof_elgamal_commitment_ins 
    (uscs : Vector.t (@Zp q) 5) : 
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) 3.
  Proof.
    refine(@construct_encryption_proof_elgamal_commitment
    (@Zp q) zp_opp (@Schnorr_group p q) 
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    pow 1 1 (uscs) [m₀; m₁; m₂] g h cp).
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.


  Definition generalised_construct_encryption_proof_elgamal_real_ins 
    (uscs : Vector.t (@Zp q) 5) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 3 4 3.
  Proof.
    refine(@generalised_construct_encryption_proof_elgamal_real (@Zp q)
      Zpfield.zero zp_add zp_mul zp_sub zp_opp (@Schnorr_group p q)
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      pow 1 (Fin.FS (Fin.FS Fin.F1)) r (uscs) 
      [m₀; m₁; m₂] g h cp c).
    eapply prime_q.
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.


  Definition nizk_generalised_construct_encryption_proof_elgamal_real_ins 
    (fn  : ∀ {m : nat}, Vector.t (Z + ((@Schnorr_group p q) + 
      (@Schnorr_group p q * @Schnorr_group p q))) m -> (@Zp q)) 
    (uscs : Vector.t (@Zp q) 5) :
    @sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 3 4 3.
  Proof.
    set (comm := construct_encryption_proof_elgamal_commitment_ins uscs).
    (* all the public values goes here into hashing. *)
    set (c := fn _ ([inl p; inl q; inr (inl g); inr (inl h); 
      inr (inl m₀); inr (inl m₁); inr (inl m₂)] ++ 
      Vector.map (fun x => inr (inr x)) (cp :: comm))).
    refine(generalised_construct_encryption_proof_elgamal_real_ins uscs c).
  Defined.


  
  Definition generalised_accepting_encryption_proof_elgamal_ins 
    (proof : @sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 3 4 3) : bool.
  Proof.
    refine(@generalised_accepting_encryption_proof_elgamal 
      (@Zp q) Zpfield.zero zp_add zp_dec 
      (@Schnorr_group p q)
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) pow 
      Schnorr.dec_zpstar _  [m₀; m₁; m₂] g h cp proof).
      (* Try to replace [m₀; m₁; m₂] with 
      [m₀; m₁; mfake]*)
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.






  

