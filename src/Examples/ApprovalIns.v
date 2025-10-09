From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma EncProof.
From Frontend Require Import Approval.
From Utility Require Import Zpstar Util.
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
  (* private key (the relation between g and h) 
  is not provided in this file because all the functions 
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
 (* In this commitnement, the messages are 
  [pow g Zpfield.zero; pow g Zpfield.one] 
  because that's what we pass in 
   Definition encrypt_vote_and_generate_enc_proof (r : F) (g h : G) (m : F) 
   ... 

  *)
  
  Definition generate_vote_commitment  
    (g h : @Schnorr_group p q) (r m : (@Zp q)) (uscs : Vector.t (@Zp q) 3) : 
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2.
  Proof.
    set (cp := @encrypt_vote (@Zp q) (@Schnorr_group p q)  
      (@mul_schnorr_group p q prime_p prime_q) 
      (@pow 2 p q safe_prime prime_p prime_q)
      r g h m).
    refine(@construct_encryption_proof_elgamal_commitment
    (@Zp q) zp_opp (@Schnorr_group p q) 
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    pow 1 0 uscs [pow g Zpfield.zero; pow g Zpfield.one] g h cp).
    all:(try (eapply prime_q)).
    all:(try (eapply prime_p)).
    all:(try (eapply safe_prime)).
  Defined.
  

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
    


  Definition generate_ballot_commitment 
    {n : nat} (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) :
    Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n.
  Proof.
    set (cp := @encrypt_ballot (@Zp q) (@Schnorr_group p q)  
      (@mul_schnorr_group p q prime_p prime_q) 
      (@pow 2 p q safe_prime prime_p prime_q)
      _ rs g h ms).
    refine(Vector.map (fun '(uscs', cp') => 
      @construct_encryption_proof_elgamal_commitment
      (@Zp q) zp_opp (@Schnorr_group p q) 
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      pow 1 0 uscs' [pow g Zpfield.zero; pow g Zpfield.one] g h cp')
      (zip_with (fun u v => (u, v)) uscs cp)).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Qed.
      
      

  Definition encrypt_ballot_and_generate_enc_proof_ins {n : nat} 
    (rs : Vector.t (@Zp q) n) (ms : Vector.t (@Zp q) n) 
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) (c : Vector.t (@Zp q) n) : 
    Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) * 
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n.
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
  

