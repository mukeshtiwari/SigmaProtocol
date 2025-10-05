From Stdlib Require Import Setoid
  setoid_ring.Field  Lia Vector Utf8 Fin. 
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import 
  Util.
From Crypto Require Import 
  Elgamal EncProof Sigma.
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
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.

  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section Definitions.

  (* 
      In this case, a vote encrypts either 0 or 1.  
      r : randomness for encryption 
      g group generator, h : public key -- ∃ x : g ^ x = h 
      m : vote value  
      uscs : randomness for encryption proof 
      c : challenge -- I need to think about making it non-interactive (fiat-shamir)
   *)

   (* In this function, when you pass a value of m that not 0 and 1, the 
    function still creates a proof but it won't pass the check 
    of verify_encryption_vote_proof, which checks if cp is encryption of 
    zero or one. See the proofs vote_proof_valid and vote_proof_invalid *)
    Definition encrypt_vote_and_generate_enc_proof 
      (r : F) (g h : G) (m : F) 
      (uscs : Vector.t F 3) (c : F) : G * G * @Sigma.sigma_proto F (G * G) 2 3 2 := 
      let cp := @enc F G gop gpow g h m r in
      let sig_proof := 
        match Fdec m zero with 
        | left _ => 
          @generalised_construct_encryption_proof_elgamal_real F zero add mul sub 
            opp G ginv gop gpow 0 Fin.F1 r uscs [g^m; g^one] g h cp c (* real one goes to 
            the first place Fin.F1 *)
        | right _ =>  
          @generalised_construct_encryption_proof_elgamal_real F zero add mul sub 
            opp G ginv gop gpow 0 (Fin.FS Fin.F1) r uscs [g^zero; g^m] g h cp c (* real one 
            goes to the second place (Fin.FS Fin.F1) *)
        end 
      in (cp, sig_proof).

    (* verification of encryption proof *)
    Definition verify_encryption_vote_proof (g h : G)
       (cppf : G * G * @Sigma.sigma_proto F (G * G) 2 3 2) : bool :=
       match cppf with 
       | (cp, pf) => @generalised_accepting_encryption_proof_elgamal F zero add 
        Fdec G ginv gop gpow Gdec _ [g^zero; g^one] g h cp pf
      end.


    (* encrypts the whole ballot. *)
    Fixpoint encrypt_ballot_and_generate_enc_proof {n : nat}
      (r : Vector.t F n) (g h : G) (m : Vector.t F n) 
      (uscs : Vector.t (Vector.t F 3) n) (c : Vector.t F n) : 
      Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n.
    Proof.
      destruct n as [| n].
      +
        exact [].
      +
        destruct (vector_inv_S r) as (rh & rt & _).
        destruct (vector_inv_S m) as (mh & mt & _).
        destruct (vector_inv_S uscs) as (uscsh & uscst & _).
        destruct (vector_inv_S c) as (ch & ct & _).
        exact ((encrypt_vote_and_generate_enc_proof rh g h mh uscsh ch) ::
          (encrypt_ballot_and_generate_enc_proof n 
          rt g h mt uscst ct)).
    Defined.


    
    Fixpoint verify_encryption_ballot_proof {n : nat} (g h : G)
    (cppf : Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) : bool.
    Proof.
      destruct n as [| n].
      +
        exact true.
      +
        destruct (vector_inv_S cppf) as (cppfh & cppft & _).
        exact ((verify_encryption_vote_proof g h cppfh) && 
          (verify_encryption_ballot_proof _ g h cppft))%bool.
    Defined.


  End Definitions.

  Section Proofs.

    (* Vector Space *)
      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub 
        div opp inv G (@eq G) gid ginv gop gpow}.

      
      (* add field *)
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

    
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

    Theorem vote_proof_valid :
      ∀ (r : F) (g h : G) (m : F) (uscs : Vector.t F 3) (c : F),
        (m = zero ∨ m = one) →
        verify_encryption_vote_proof g h 
          (encrypt_vote_and_generate_enc_proof r g h m uscs c) = true.
    Proof.
      intros * ha.
      unfold encrypt_vote_and_generate_enc_proof, 
      verify_encryption_vote_proof.
      destruct (Fdec m zero) as [fa | fa].
      +
        subst.
        eapply generalised_construct_encryption_proof_elgamal_real_completeness.
        (* I had a mini-heart attack by looking at the goal :) *)
        subst; cbn. split. reflexivity.
        assert (Hwt : gop (g ^ zero) (h ^ r) = gop (h ^ r) (g ^ zero)).
        rewrite commutative; reflexivity.
        rewrite Hwt; clear Hwt.
        setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid).
        assert (Hwt : (gop (g ^ zero) (gop (ginv (g ^ zero)) (h ^ r))) = 
        (h ^ r)).
        rewrite associative.
        rewrite group_is_right_inverse,
        monoid_is_left_idenity;
        reflexivity. rewrite associative, commutative in Hwt.
        rewrite Hwt. reflexivity. 
        typeclasses eauto.
      +
        destruct ha as [ha | ha]; try congruence. subst.
        eapply generalised_construct_encryption_proof_elgamal_real_completeness.
         (* m = 1 *)
        split. reflexivity.
        cbn. subst.
        assert (Hwt : gop (g ^ one) (h ^ r) = gop (h ^ r) (g ^ one)).
        rewrite commutative; reflexivity.
        rewrite Hwt; clear Hwt.
        setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid).
        assert (Hwt : (gop (g ^ one) (gop (ginv (g ^ one)) (h ^ r))) = 
        (h ^ r)).
        rewrite associative.
        rewrite group_is_right_inverse,
        monoid_is_left_idenity;
        reflexivity. rewrite associative, commutative in Hwt.
        rewrite Hwt. reflexivity. 
        typeclasses eauto.
    Qed.

    
    Theorem vote_proof_invalid_reject :
      ∀ (r : F) (g h : G) (m : F) (uscs : Vector.t F (2 + 0 + (1 + 0))) (c : F),
        (m <> zero ∧ m <> one) →
        verify_encryption_vote_proof g h 
          (encrypt_vote_and_generate_enc_proof r g h m uscs c) = false.
    Proof.
      intros * hu.
      unfold encrypt_vote_and_generate_enc_proof, 
      verify_encryption_vote_proof.
      destruct (Fdec m zero) as [fa | fa].
      +
        
        destruct hu as (hal & har).
        subst. specialize (hal eq_refl).
        inversion hal.
      +
        destruct (Fdec m one) as [faa | faa].
        ++
          subst; destruct hu as (hal & har).
          specialize (har eq_refl). 
          inversion har.
        ++
          (* challenging case *)
          eapply generalised_accepting_elgamal_conversations_reject_correctness_gen.
          refine 
            (match generalised_construct_encryption_proof_elgamal_real (FS F1) r uscs [g ^ zero; g ^ m] g h (enc g h m r) c as s' return 
            generalised_construct_encryption_proof_elgamal_real (FS F1) r uscs
            [g ^ zero; g ^ m] g h (enc g h m r) c = s' -> _
            with 
            |(a₁; c₁; r₁) => fun hb => _ 
            end eq_refl).
          rewrite hb.
          unfold generalised_construct_encryption_proof_elgamal_real in hb.

          
          






          
    Admitted.
    
    (* ballot proof is valid *)
    Theorem ballot_proof_valid :
      ∀ (n : nat) (rs : Vector.t F n) (g h : G) 
        (ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n) (chs : Vector.t F n),
        (∀ (i : Fin.t n), Vector.nth ms i = zero ∨ Vector.nth ms i = one) ->
        verify_encryption_ballot_proof g h 
          (encrypt_ballot_and_generate_enc_proof rs g h ms uscs chs) = true.
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        pose proof (vector_inv_0 rs) as hb.
        pose proof (vector_inv_0 ms) as hc.
        pose proof (vector_inv_0 uscs) as hd.
        pose proof (vector_inv_0 chs) as he.
        subst; cbn. reflexivity.
      +
        intros * ha.
        destruct (vector_inv_S rs) as (rsh & rst & hb).
        destruct (vector_inv_S ms) as (msh & mst & hc).
        destruct (vector_inv_S uscs) as (uscsh & uscst & hd).
        destruct (vector_inv_S chs) as (chsh & chst & he).
        subst. simpl. eapply Bool.andb_true_iff.
        split.
        ++
          eapply vote_proof_valid.
          exact (ha Fin.F1).
        ++
          eapply ihn.
          intro f.
          exact (ha (Fin.FS f)).
    Qed.  
  End Proofs.
End Approval.