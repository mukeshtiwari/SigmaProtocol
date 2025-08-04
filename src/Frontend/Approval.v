From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin. 
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import 
  Util.
From Crypto Require Import 
  Elgamal EncProof.
Import VectorNotations.
Section Approval.

  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec: @vector_space F (@eq F) zero one add mul sub 
      div opp inv G (@eq G) gid ginv gop gpow}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.


  Section Definitions.

    (* 
      In this case, a vote encrypts either 0 or 1.  
      r : randomness for encryption 
      g group generator, h : public key -- ∃ x : g ^ x = h 
      m : vote value -- 0 or 1 in this case 
      uscs : randomness for encryption proof 
      c : challenge -- I need to think about making it non-interactive (fiat-shamir)
    *)

    Definition encrypt_vote_and_generate_enc_proof (r : F) (g h : G) (m : F) 
      (uscs : Vector.t F 3) (c : F) : G * G * @Sigma.sigma_proto F (G * G) 2 3 2 := 
      let cp := @enc F G gop gpow g h m r in 
      let ms := [g^zero; g^one] in 
      let sig_proof := 
        match Fdec m zero with 
        | left _ => @generalised_construct_encryption_proof_elgamal_real F zero add mul sub 
            opp G ginv gop gpow 0 Fin.F1 r uscs ms g h cp c (* real one goes to the first place Fin.F1 *)
        | right _ =>  @generalised_construct_encryption_proof_elgamal_real F zero add mul sub 
            opp G ginv gop gpow 0 (Fin.FS Fin.F1) r uscs ms g h cp c (* real one goes to the second place (Fin.FS Fin.F1) *)
        end 
      in (cp, sig_proof).



    

  End Definitions.
  Section Proofs.

    
    Theorem encryption_correct : ∀ (r : F) (g h : G) (m : F) 
      (uscs : Vector.t F 3) (c : F),
      let (cp, _) := encrypt_vote_and_generate_enc_proof r g h m uscs c in
      cp = @enc F G gop gpow g h m r.
    Proof.
      intros *. 
      unfold encrypt_vote_and_generate_enc_proof, enc.
      destruct (Fdec m zero).
      - (* Case m = zero *) 
        reflexivity.  (* Directly reduces to (gʳ, hʳ) *)
      - (* Case m = one *)
        reflexivity.  (* Directly reduces to (gʳ, g¹·hʳ) *)
    Qed.


    Theorem decryption_correct : ∀ (x : F) (r : F) (g h : G) (m : F) 
      (uscs : Vector.t F 3) (c : F), h = g^x ->
      let (cp, _) := encrypt_vote_and_generate_enc_proof r g h m uscs c in 
      g^m = @dec F G ginv gop gpow x cp.
    Proof.
      intros * ha.
      unfold encrypt_vote_and_generate_enc_proof, enc, dec.
      eapply dec_is_left_inv_of_enc with (x := x) (r := r).
      exact ha.
      unfold enc. reflexivity.
    Qed.

   
    Theorem proof_valid:
      ∀ (r : F) (g h : G) (m : F) (uscs : Vector.t F 3) (c : F),
        (m = zero ∨ m = one) →
        let (cp, pf) := encrypt_vote_and_generate_enc_proof r g h m uscs c in
        @generalised_accepting_encryption_proof_elgamal F zero add 
        Fdec G ginv gop gpow Gdec 2 [g^zero; g^one] g h cp pf = true.
    Proof.
      intros * ha.
      unfold encrypt_vote_and_generate_enc_proof.
      destruct (Fdec m zero) as [fa | fa].
      + admit.
      + admit.
    Admitted.

  End Proofs.

End Approval.