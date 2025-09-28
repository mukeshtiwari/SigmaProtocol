From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma EncProof.
From Frontend Require Import Approval.
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
  (* private is not provided because all the functions 
  defined in this file runs on frontend, i.e., 
  on voters' computer. Private key for this 
  one is provided in the TallyIns.v file that 
  runs on the backend (server). 
  
  It's not very hard to compute the x such that 
  h = g ^ x for this example but in real world 
  we use much larger primes where computing 
  discrete log is hard, e.g., see the 
  HeliosSigmaIns.v file. 
  *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

   
  Definition h : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 3210;
    Ha := conj eq_refl eq_refl : (0 < 3210 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 3210 q p)).
  Defined.
 (*end of group generator *)

 (* I need to expose the And commitment function here so 
 that I can hash the values to compute the challenge. *)
  Definition encrypt_vote_and_generate_enc_proof_ins 
    (r m : (@Zp q)) (uscs : Vector.t (@Zp q) 3) (c : (@Zp q)) : 
    @Schnorr_group p q * @Schnorr_group p q * 
    @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 
    2 3 2.
  Proof.
    refine(@encrypt_vote_and_generate_enc_proof (@Zp q)
     Zpfield.zero Zpfield.one zp_add zp_mul zp_sub zp_opp zp_dec 
     (@Schnorr_group p q) 
     (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
     (@mul_schnorr_group p q prime_p prime_q) pow 
     r g h m uscs c).
    all: (try eapply prime_q).
    exact safe_prime.
    eapply prime_p.
  Defined.


  Definition verify_encryption_vote_proof_ins 
    (proof : @Schnorr_group p q * @Schnorr_group p q * 
    @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 
    2 3 2) : bool.
  Proof.
    refine(@verify_encryption_vote_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_dec 
      (@Schnorr_group p q) 
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) pow
      Schnorr.dec_zpstar g h proof).
    all: (try eapply prime_q).
    exact safe_prime.
    eapply prime_p.
  Defined.
    



  Definition encrypt_ballot_and_generate_enc_proof_ins {n : nat} 
    (rs : Vector.t (@Zp q) n) (ms : Vector.t (@Zp q) n) 
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) (c : Vector.t (@Zp q) n) : 
    Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) * 
    @Sigma.sigma_proto (@Zp q) 
    (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n.
  Proof.
    refine(@encrypt_ballot_and_generate_enc_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_mul zp_sub
      zp_opp zp_dec (@Schnorr_group p q) 
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) pow _ rs 
      g h ms uscs c).
    all: (try eapply prime_q).
    exact safe_prime.
    eapply prime_p.
  Defined.

  Definition verify_encryption_ballot_proof_ins {n : nat} 
    (proof : Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) * 
    @Sigma.sigma_proto (@Zp q) 
    (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n) : bool.
  Proof.
    refine(@verify_encryption_ballot_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_dec 
      (@Schnorr_group p q) 
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) pow
      Schnorr.dec_zpstar _ g h proof).
    all: (try eapply prime_q).
    exact safe_prime.
    eapply prime_p.
  Defined.

End Ins.
  



