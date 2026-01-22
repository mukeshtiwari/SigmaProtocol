From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma 
  PedLinearRel.
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

  (* g and h should be generated 
   in verifiable manner *)
  (* group generator *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  (* group generator *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 7;
    Ha := conj eq_refl eq_refl : (0 < 7 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 7 q p)).
  Defined.


  (* 
    
   APPLICATION: Confidential Transactions in Cryptocurrencies

   Problem: In blockchain systems like Bitcoin, all transaction amounts are 
   publicly visible. You want privacy while still preventing fraud (creating 
   money out of thin air).

   Example: Private Payment
   
   Alice sends Bob some cryptocurrency. She needs to prove the transaction 
   balances WITHOUT revealing the amounts.

   Setup:
   - Alice's balance: v₁ (secret)
   - Transaction amount: v₂ (secret)  
   - Alice's new balance: v₃ (secret)
   - Each value is committed: Cᵢ = g^{vᵢ} · h^{rᵢ}

   Linear constraint to prove: v₁ - v₂ - v₃ = 0

   Using this protocol with coefficients αs = (1, -1, -1) and z = 0:

   1 · v₁ + (-1) · v₂ + (-1) · v₃ = 0

   This proves: old balance = sent amount + new balance (conservation of money)

   Why It's Powerful:
   - Privacy: Transaction amounts stay hidden
   - Auditability: Anyone can verify no money was created/destroyed
   - No trusted party: Pure cryptographic proof

   Real-World Use:
   This exact technique is used in:
   - Mimblewimble (Grin, Beam cryptocurrencies)
   - Monero (combined with ring signatures)
   - Zcash (as part of their ZK-SNARK system)
   - Confidential Assets on Liquid Network

   The linear constraint can also enforce more complex policies like 
   transaction fees, multi-input/output transactions, or even smart 
   contract conditions - all while keeping values private!
*)

  Definition αs : Vector.t (@Zp q) 3.
  Proof.
    refine ([Zpfield.one; @zp_opp q prime_q Zpfield.one; @zp_opp q prime_q Zpfield.one]); 
    try (exact prime_q).
  Defined. 

  Definition z : @Zp q := @zero q prime_q.

  Definition construct_pedersen_linear_relation_commitment_ins  
    (usws : Vector.t (@Zp q) 6) : Vector.t (@Schnorr_group p q) 4.
  Proof.
    refine(@construct_pedersen_linear_relation_commitment (@Zp q) 
    (@zero q prime_q) zp_add zp_mul (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ g h αs usws). 
  Defined.

  Definition pedersen_commitment_vector_ins 
    (vs rs : Vector.t (@Zp q) 3) : Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@pedersen_commitment_vector (@Zp q) (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ g h vs rs).
  Defined.
    

  Definition construct_pedersen_linear_relation_generalised_real_proof_ins  
    (vs rs : Vector.t (@Zp q) 3) (usws : Vector.t (@Zp q) 6) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 4 1 6.
  Proof.
    refine(@construct_pedersen_linear_relation_generalised_real_proof (@Zp q) 
    (@zero q prime_q) zp_add zp_mul (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ g h αs 
    usws vs rs c).
  Defined.

   Definition nizk_construct_pedersen_linear_relation_generalised_real_proof_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))  
    (vs rs : Vector.t (@Zp q) 3) (usws : Vector.t (@Zp q) 6) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 4 1 6.
  Proof.
    set (comm₁ := construct_pedersen_linear_relation_commitment_ins usws).
    set (comm₂ := pedersen_commitment_vector_ins vs rs).
    set (c := fn _ ([inl p; inl q; inr g; inr h] ++ 
    Vector.map inr (comm₁ ++ comm₂))).
    refine(construct_pedersen_linear_relation_generalised_real_proof_ins 
    vs rs usws c).
  Defined.

  Definition verify_pedersen_linear_relation_generalised_proof_ins 
    (cs : Vector.t (@Schnorr_group p q) 3) 
    (pf : @sigma_proto (@Zp q) (@Schnorr_group p q) 4 1 6) : bool.
  Proof.
    refine(@verify_pedersen_linear_relation_generalised_proof (@Zp q) 
    (@zero q prime_q) zp_add zp_mul (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q)
    Schnorr.dec_zpstar _ g h z αs cs pf).
  Defined. 
    

End Ins.
  

  




    





