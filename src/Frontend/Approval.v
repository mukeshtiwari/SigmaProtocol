From Stdlib Require Import Setoid
  setoid_ring.Field  Psatz Vector Utf8 Fin Lia. 
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

    

      (* encrypt vote *)
      Definition encrypt_vote (g h : G) (r : F) (m : F) : G * G :=
        @enc F G gop gpow g h m r.

      (* create a proof *)
      Definition generate_enc_proof 
        (g h : G) (r : F)  (m : F) 
        (uscs : Vector.t F 3) (cp : G * G) (c : F) : @Sigma.sigma_proto F (G * G) 2 3 2 :=
          match Fdec m zero with 
          | left _ => 
            @generalised_construct_encryption_proof_elgamal_real F zero add mul sub 
              opp G ginv gop gpow 0 Fin.F1 r uscs [g^m; g^one] g h cp c (* real one goes to 
              the first place Fin.F1 *)
          | right _ =>  
            @generalised_construct_encryption_proof_elgamal_real F zero add mul sub 
              opp G ginv gop gpow 0 (Fin.FS Fin.F1) r uscs [g^zero; g^m] g h cp c (* real one 
              goes to the second place (Fin.FS Fin.F1) *)
          end.

      (* The announcement of generate_enc_proof, computed before the 
        challenge is known. A non-interactive ballot derives its challenges 
        from these announcements (nizk_encrypt_ballot_and_generate_enc_proof_ins 
        in Examples/ApprovalIns.v); generate_enc_proof_commitment_announcement 
        shows that they are exactly the announcements of the proofs. *)
      Definition generate_enc_proof_commitment 
        (g h : G) (m : F) (uscs : Vector.t F 3) (cp : G * G) : 
        Vector.t (G * G) 2 :=
          match Fdec m zero with 
          | left _ => 
            @construct_encryption_proof_elgamal_commitment F opp G ginv gop gpow 
              0 1 uscs [g^m; g^one] g h cp
          | right _ =>  
            @construct_encryption_proof_elgamal_commitment F opp G ginv gop gpow 
              1 0 uscs [g^zero; g^m] g h cp
          end.

      
      (* wrap both of them *)
      (* In this function, when you pass a value of m that not 0 and 1, the 
      function still creates a proof but it won't pass the check 
      of verify_encryption_vote_proof, which checks if cp is encryption of 
      zero or one. See the proofs vote_proof_valid and vote_proof_invalid *)
      Definition encrypt_vote_and_generate_enc_proof 
        (g h : G) (r : F)  (m : F) 
        (uscs : Vector.t F 3) (c : F) : G * G * @Sigma.sigma_proto F (G * G) 2 3 2 := 
        let cp := @enc F G gop gpow g h m r in
        let sig_proof := generate_enc_proof g h r m uscs cp c
        in (cp, sig_proof).

      (* verification of encryption proof *)
      Definition verify_encryption_vote_proof (g h : G)
        (cppf : G * G * @Sigma.sigma_proto F (G * G) 2 3 2) : bool :=
        match cppf with 
        | (cp, pf) => @generalised_accepting_encryption_proof_elgamal F zero add 
          Fdec G ginv gop gpow Gdec _ [g^zero; g^one] g h cp pf
        end.


      (* encrypt the whole ballot *)
      Fixpoint encrypt_ballot {n : nat}
        (g h : G) (r : Vector.t F n) (m : Vector.t F n) : Vector.t (G * G) n.
      Proof.
        destruct n as [| n].
        +
          exact [].
        +
          destruct (vector_inv_S r) as (rh & rt & _).
          destruct (vector_inv_S m) as (mh & mt & _).
          exact (encrypt_vote g h rh mh :: encrypt_ballot _ g h rt mt).
      Defined.

      (* generate enc proof for a ballot *)
      Fixpoint generate_enc_proof_ballot {n : nat}
        (g h : G) (r : Vector.t F n) (m : Vector.t F n) 
        (uscs : Vector.t (Vector.t F 3) n) 
        (cp : Vector.t (G * G) n) (c : Vector.t F n) : 
        Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n.
      Proof.
        destruct n as [| n].
        +
          exact [].
        +
          destruct (vector_inv_S r) as (rh & rt & _).
          destruct (vector_inv_S m) as (mh & mt & _).
          destruct (vector_inv_S uscs) as (uscsh & uscst & _).
          destruct (vector_inv_S cp) as (cph & cpt & _).
          destruct (vector_inv_S c) as (ch & ct & _).
          exact(generate_enc_proof g h rh mh uscsh cph ch :: 
            generate_enc_proof_ballot _ g h rt mt uscst cpt ct).
      Defined.




      (* the announcements of the whole ballot, before the challenges *)
      Fixpoint generate_ballot_commitment {n : nat}
        (g h : G) (r : Vector.t F n) (m : Vector.t F n) 
        (uscs : Vector.t (Vector.t F 3) n) : 
        Vector.t (Vector.t (G * G) 2) n.
      Proof.
        destruct n as [| n].
        +
          exact [].
        +
          destruct (vector_inv_S r) as (rh & rt & _).
          destruct (vector_inv_S m) as (mh & mt & _).
          destruct (vector_inv_S uscs) as (uscsh & uscst & _).
          exact (generate_enc_proof_commitment g h mh uscsh (encrypt_vote g h rh mh) :: 
            generate_ballot_commitment _ g h rt mt uscst).
      Defined.

      (* encrypts the whole ballot and generate proof *)
      Fixpoint encrypt_ballot_and_generate_enc_proof {n : nat}
        (g h : G) (r : Vector.t F n) (m : Vector.t F n) 
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
          exact ((encrypt_vote_and_generate_enc_proof g h rh mh uscsh ch) ::
            (encrypt_ballot_and_generate_enc_proof n 
            g h rt mt uscst ct)).
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

      (* ---------------------------------------------------------------- *)
      (* Overall proof.

        The individual proofs show that every vote encrypts 0 or 1. The 
        overall proof shows, on the homomorphic product of the ballot's 
        ciphertexts, that the number of approvals is between 0 and the 
        number of candidates: it is the disjunctive encryption proof over 
        the messages g^0, g^1, ..., g^n, proved at the index equal to the 
        actual number of approvals. This is the proof Helios attaches to a 
        ballot when the question has a maximum; here the maximum is the 
        number of candidates. *)

      (* the field element k = 1 + ... + 1 *)
      Fixpoint of_nat (k : nat) : F :=
        match k with
        | 0 => zero
        | S k' => one + of_nat k'
        end.

      (* [g^0; g^1; ...; g^k] *)
      Fixpoint powers (g : G) (k : nat) : Vector.t G (S k) :=
        match k with
        | 0 => [g ^ zero]
        | S k' => g ^ zero :: Vector.map (fun m => gop g m) (powers g k')
        end.

      (* the homomorphic product of a ballot's ciphertexts *)
      Definition ballot_product {k : nat} (cps : Vector.t (G * G) k) : G * G :=
        Vector.fold_right (fun '(a, b) '(c, d) => (gop a c, gop b d)) cps (gid, gid).

      (* the number of approvals on a ballot *)
      Definition count_ones {k : nat} (ms : Vector.t F k) : nat :=
        Vector.fold_right (fun m acc => if Fdec m one then S acc else acc) ms 0.

      Lemma count_ones_le : forall (k : nat) (ms : Vector.t F k), count_ones ms <= k.
      Proof.
        induction k as [| k ih]; intros ms.
        + rewrite (vector_inv_0 ms); cbn; lia.
        + destruct (vector_inv_S ms) as (m & ms' & hm); subst.
          unfold count_ones in *; cbn.
          destruct (Fdec m one); specialize (ih ms'); lia.
      Qed.

      (* the index of the message g^(number of approvals) *)
      Definition overall_index {n : nat} (ms : Vector.t F (S n)) : Fin.t (2 + n) :=
        Fin.of_nat_lt (le_n_S _ _ (count_ones_le _ ms)).

      Definition generate_overall_proof {n : nat} (g h : G) 
        (rs ms : Vector.t F (S n)) (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) : 
        @Sigma.sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n) :=
        @generalised_construct_encryption_proof_elgamal_real F zero add mul sub opp 
          G ginv gop gpow n (overall_index ms) (Vector.fold_right add rs zero) 
          uscs (powers g (S n)) g h (ballot_product (encrypt_ballot g h rs ms)) c.

      (* A ballot with no candidate has nothing to prove. *)
      Definition verify_overall_proof {k : nat} (g h : G) (cps : Vector.t (G * G) k)
        (pf : @Sigma.sigma_proto F (G * G) (S k) (S (S k)) (S k)) : bool :=
        match k as k' return Vector.t (G * G) k' -> 
          @Sigma.sigma_proto F (G * G) (S k') (S (S k')) (S k') -> bool 
        with
        | 0 => fun _ _ => true
        | S k' => fun cps pf => 
          @generalised_accepting_encryption_proof_elgamal F zero add Fdec 
            G ginv gop gpow Gdec (S (S k')) (powers g (S k')) g h (ballot_product cps) pf
        end cps pf.

      (* the full ballot: one ciphertext and proof per candidate, and the 
        overall proof *)
      Definition encrypt_ballot_with_overall_proof {n : nat} (g h : G) 
        (rs ms : Vector.t F (S n)) (uscs : Vector.t (Vector.t F 3) (S n)) 
        (cs : Vector.t F (S n)) (uscs' : Vector.t F ((2 + n) + (1 + n))) (c : F) :
        Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) (S n) * 
        @Sigma.sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n) :=
        (encrypt_ballot_and_generate_enc_proof g h rs ms uscs cs, 
         generate_overall_proof g h rs ms uscs' c).

      Definition verify_ballot {k : nat} (g h : G)
        (b : Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) k * 
             @Sigma.sigma_proto F (G * G) (S k) (S (S k)) (S k)) : bool :=
        (verify_encryption_ballot_proof g h (fst b) && 
         verify_overall_proof g h (Vector.map fst (fst b)) (snd b))%bool.

    End Definitions.

    Section Proofs.
    
      (* Vector Space *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
          div opp inv G (@eq G) gid ginv gop gpow}.

        
        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

      Theorem first_projection_vote_encryption : 
        ∀ (r : F) (g h : G) (m : F) 
        (uscs : Vector.t F 3) (c : F), 
        fst (encrypt_vote_and_generate_enc_proof g h r m uscs c) = 
        encrypt_vote g h r m.
      Proof.
        intros *; 
        unfold encrypt_vote_and_generate_enc_proof, 
        enc, encrypt_vote, enc; cbn.
        reflexivity.
      Qed.

      Theorem second_projection_vote_sigma_proof : 
        ∀ (r : F) (g h : G) (m : F) 
        (uscs : Vector.t F 3) (cp : G * G) (c : F), 
        cp =  @enc F G gop gpow g h m r  -> 
        snd (encrypt_vote_and_generate_enc_proof g h r m uscs c) = 
        generate_enc_proof g h r m uscs cp c.
      Proof.
        intros * ha.
        unfold encrypt_vote_and_generate_enc_proof, 
        generate_enc_proof; subst.  simpl.
        reflexivity.
      Qed.


      Theorem first_project_ballot_encryption : 
        ∀ (n : nat) (r : Vector.t F n) (g h : G) (m : Vector.t F n) 
          (uscs : Vector.t (Vector.t F 3) n) (c : Vector.t F n),
        Vector.map fst (encrypt_ballot_and_generate_enc_proof g h r m uscs c) = 
        encrypt_ballot g h r m.
      Proof.
        induction n as [|n ihn].
        +
          intros *. 
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S r) as (rh & rt & ha).
          destruct (vector_inv_S m) as (mh & mt & hb).
          destruct (vector_inv_S uscs) as (uscsh & uscst & hc).
          destruct (vector_inv_S c) as (ch & ct & hd).
          subst. cbn. 
          rewrite ihn.
          unfold encrypt_vote.
          reflexivity.
      Qed.



      Theorem second_project_ballot_sigma_proof : 
        ∀ (n : nat) (r : Vector.t F n) (g h : G) (m : Vector.t F n) 
        (uscs : Vector.t (Vector.t F 3) n) (cp : Vector.t (G * G) n) (c : Vector.t F n),
        (∀ (i : Fin.t n), Vector.nth cp i = @enc F G gop gpow g h (Vector.nth m i) (Vector.nth r i)) ->
        Vector.map snd (encrypt_ballot_and_generate_enc_proof g h r m uscs c) = 
        generate_enc_proof_ballot g h r m uscs cp c.
      Proof.  
        induction n as [|n ihn].
        +
          intros * ha.
          reflexivity.
        +
          intros * hf.
          destruct (vector_inv_S r) as (rh & rt & ha).
          destruct (vector_inv_S m) as (mh & mt & hb).
          destruct (vector_inv_S uscs) as (uscsh & uscst & hc).
          destruct (vector_inv_S cp) as (cph & cpt & hd).
          destruct (vector_inv_S c) as (ch & ct & he).
          subst. cbn. f_equal.
          specialize (hf Fin.F1); cbn in hf.
          subst. reflexivity.
          eapply ihn. intro f.
          specialize (hf (Fin.FS f)).
          cbn in hf. exact hf.
      Qed.
          



      
      Theorem encryption_correct : ∀ (r : F) (g h : G) (m : F) 
        (uscs : Vector.t F 3) (c : F),
        match encrypt_vote_and_generate_enc_proof g h r m uscs c with 
        | (cp, _) => cp = (gpow g r, gop (gpow g m) (gpow h r))
        end.
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
            (encrypt_vote_and_generate_enc_proof g h r m uscs c) = true.
      Proof.
        intros * ha.
        unfold encrypt_vote_and_generate_enc_proof, 
        verify_encryption_vote_proof, generate_enc_proof.
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


      Lemma mul_eq_zero (a b : F) : a * b = zero → a = zero ∨ b = zero.
      Proof.
        intro ha.  (* Assume a * b = 0 *)
        (* Case analysis on whether a = 0 *)
        destruct (Fdec a zero) as [hb | hb].
        - (* Case 1: a = 0 *)
          left; assumption.
        - (* Case 2: a ≠ 0 *)
          right.
          eapply f_equal with (f := fun x => inv a * x) in ha.
          rewrite associative in ha.
          assert (hc : inv a * a = one). field.
          assumption.
          rewrite hc in ha; clear hc.
          assert (hc : inv a * zero = zero). field.
          assumption. rewrite hc in ha; clear hc.
          assert (hc : one * b = b). field.
          rewrite hc in ha. exact ha.
      Qed.

      Lemma sub_eq : forall (u v : F), sub u v = zero -> u = v.
      Proof.
        intros * ha.
        assert (hb : sub u v = u + opp v). field.
        rewrite hb in ha.
        eapply f_equal with (f := fun x => x + v) in ha.
        assert (hc : opp v + v = zero). field.
        rewrite <-associative in ha.
        rewrite hc in ha; clear hc.
        assert (hc : u + zero = u) by field.
        rewrite hc in ha; clear hc.
        assert (hc : zero + v = v) by field.
        rewrite hc in ha. exact ha.
      Qed.
        


      Theorem vote_proof_invalid_reject_ :
        ∀ (r : F) (g h : G) (m : F)  (u₁ u₂ c₁ : F) (c : F),
         (m <> zero ∧ m <> one) → 
          verify_encryption_vote_proof g h 
            (encrypt_vote_and_generate_enc_proof g h r m [u₁; u₂; c₁] c) = false ∨
            g = gid ∨ c₁ = c.
      Proof.
        intros * hu.
         unfold encrypt_vote_and_generate_enc_proof, 
        verify_encryption_vote_proof, generate_enc_proof.
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
            unfold generalised_accepting_encryption_proof_elgamal, 
            enc, generalised_construct_encryption_proof_elgamal_real, 
            generate_enc_proof.
            simpl.
            destruct (Gdec g gid) as [gaa | gaa].
            +++
              right; left.
              exact gaa.
            +++
              destruct (Fdec c₁ c) as [fcc | fcc].
              ++++
                right; right; exact fcc.
              ++++
                destruct (vector_fin_app_pred 1 (FS F1) [u₁; u₂] [c₁]) as
                (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
                destruct pfaa as [pfa].
                destruct pfbb as [pfb].
                destruct haa as [ha].
                destruct ha as (ha & hb & hc & hd).
                subst; cbn in * |- *.
                assert (m₂ = 0). 
                {
                  destruct m₂ as [|m₂].
                  reflexivity. nia.
                }
                subst. cbn. 
                assert (pfa = eq_refl). 
                eapply Eqdep_dec.UIP_refl_nat.
                assert (pfb = eq_refl). 
                eapply Eqdep_dec.UIP_refl_nat.
                subst. cbn in * |- *.
                pose proof (vector_inv_0 v₂) as hd.
                pose proof (vector_inv_0 v₄) as he.
                rewrite hd, he in * |- *. cbn.
                subst; cbn.
                destruct (vector_inv_S v₁) as (ma & msr & hmm).
                rewrite hmm in * |- *.
                subst; cbn.
                pose proof (vector_inv_0 msr) as hd.
                subst; cbn.
                destruct (vector_inv_S v₃) as (mb & msr & hmm).
                subst; cbn.
                pose proof (vector_inv_0 msr) as hd.
                subst; cbn.
                assert (hd : c = (c₁ + (sub c (c₁ + zero) + zero))). field.
                rewrite <-hd; clear hd.
                destruct (Fdec c c)
                as [hdec | hdec]; try auto.
                rewrite Bool.andb_false_intro2. left; reflexivity.
                rewrite Bool.andb_false_intro1. reflexivity.
                rewrite Bool.andb_false_intro2. reflexivity.
                eapply dec_false; intro haa.
                assert (hb : c₁ + zero = c₁). field.
                rewrite !hb in haa; clear hb.
                assert(hb : g ^ one = g).
                rewrite field_one; reflexivity.
                rewrite !hb in haa; clear hb.
                assert (hb : gop (g ^ m) (h ^ r) = gop (h ^ r) (g ^ m)).
                rewrite commutative. reflexivity.
                rewrite !hb in haa; clear hb.
                assert (hb : (gop (gop (h ^ r) (g ^ m)) (ginv g)) = 
                gop (h ^ r) (gop (g ^ m) (ginv g))).
                rewrite associative; reflexivity.
                rewrite !hb in haa; clear hb.
                remember ((gop (g ^ m) (ginv g))) as gp.
                rewrite smul_distributive_vadd, smul_pow_mul,
                associative in haa.
                assert (hb : (gop (h ^ u₂) (h ^ (sub c c₁ * r))) = 
                  h ^ (u₂ + sub c c₁ * r)).
                destruct Hvec. (* why do I need this destruct this? *)
                setoid_rewrite <-vector_space_smul_distributive_fadd;
                reflexivity.
                rewrite hb in haa; clear hb.
                eapply f_equal with (f := fun x => 
                  gop (h ^ (opp (u₂ + sub c c₁ * r))) x) in haa.
                assert (hb : gop (h ^ opp (u₂ + sub c c₁ * r)) (h ^ (u₂ + sub c c₁ * r)) = gid).
                destruct Hvec.
                setoid_rewrite <-vector_space_smul_distributive_fadd.
                assert (hb : (opp (u₂ + sub c c₁ * r) + (u₂ + sub c c₁ * r)) = zero). field.
                rewrite hb; clear hb.
                rewrite field_zero; reflexivity.
                rewrite !hb in haa; clear hb.
                rewrite associative in haa.
                assert (hb : gop (h ^ opp (u₂ + sub c c₁ * r)) (h ^ (u₂ + sub c c₁ * r)) = 
                gid). destruct Hvec.
                rewrite <-vector_space_smul_distributive_fadd.
                assert (hb : (opp (u₂ + sub c c₁ * r) + (u₂ + sub c c₁ * r)) = zero).
                field. rewrite hb; clear hb.
                rewrite field_zero; reflexivity.
                rewrite hb in haa; clear hb.
                rewrite left_identity in haa.
                rewrite Heqgp in haa; clear Heqgp.
                rewrite <- (vector_space_field_zero g) in haa.
                assert (hb : gop (g ^ m) (ginv g) ^ sub c c₁ = 
                  gop ((g ^ m) ^ sub c c₁) (ginv g ^ sub c c₁)).
                destruct Hvec.
                rewrite vector_space_smul_distributive_vadd; reflexivity.
                rewrite hb in haa; clear hb.
                eapply f_equal with (f := fun x => gop x (g ^ sub c c₁)) in haa.
                rewrite <-associative in haa.
                assert (hb : (gop (ginv g ^ sub c c₁) (g ^ sub c c₁)) = gid).
                destruct Hvec.
                rewrite <-vector_space_smul_distributive_vadd, left_inverse, 
                <-field_zero, smul_pow_up.
                assert (hb : zero * sub c c₁ = zero). field.
                rewrite hb; clear hb.
                reflexivity.
                rewrite hb in haa; clear hb.
                destruct Hvec.
                rewrite <- vector_space_smul_distributive_fadd, right_identity,
                smul_pow_up in haa.
                assert (hb : zero + sub c c₁ = sub c c₁). field.
                rewrite hb in haa; clear hb.
                eapply f_equal with (f := fun x => gop x (g ^ opp (sub c c₁))) in haa.
                assert(hb : gop (g ^ sub c c₁) (g ^ opp (sub c c₁)) = gid).
                destruct Hvec.
                rewrite <-vector_space_smul_distributive_fadd.
                assert(hb : (sub c c₁ + opp (sub c c₁)) = zero). field.
                rewrite hb; clear hb.
                rewrite field_zero; reflexivity.
                rewrite !hb in haa; clear hb.
                rewrite  <-smul_distributive_fadd in haa.
                assert (hb : (m * sub c c₁ + opp (sub c c₁)) = 
                  (sub m one) * sub c c₁). field.
                rewrite hb in haa; clear hb.
                eapply eq_sym in haa.
                eapply gid_power_zero in haa.
                destruct haa as [haa | haa]; try congruence.
                eapply mul_eq_zero in haa.
                destruct haa as [haa | haa].
                -
                  eapply faa.
                  eapply sub_eq;
                  assumption.
                -
                  eapply fcc.
                  eapply eq_sym.
                  eapply sub_eq.
                  assumption.
            Unshelve.
            exact g. exact Fdec.
      Qed.
     

      Theorem vote_proof_invalid_reject :
        ∀ (r : F) (g h : G) (m : F)  (u₁ u₂ c₁ : F) (c : F),
          g <> gid -> (m <> zero ∧ m <> one) → c₁ <> c ->
          verify_encryption_vote_proof g h 
            (encrypt_vote_and_generate_enc_proof g h r m [u₁; u₂; c₁] c) = false.
      Proof.
        intros * ht hu hv.
        unfold encrypt_vote_and_generate_enc_proof, 
        verify_encryption_vote_proof, generate_enc_proof.
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
            unfold generalised_accepting_encryption_proof_elgamal, 
            enc, generalised_construct_encryption_proof_elgamal_real, 
            generate_enc_proof.
            simpl. 
            destruct (vector_fin_app_pred 1 (FS F1) [u₁; u₂] [c₁]) as
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
            destruct pfaa as [pfa].
            destruct pfbb as [pfb].
            destruct haa as [ha].
            destruct ha as (ha & hb & hc & hd).
            subst; cbn in * |- *.
            assert (m₂ = 0). 
            {
              destruct m₂ as [|m₂].
              reflexivity. nia.
            }
            subst. cbn. 
            assert (pfa = eq_refl). 
            eapply Eqdep_dec.UIP_refl_nat.
            assert (pfb = eq_refl). 
            eapply Eqdep_dec.UIP_refl_nat.
            subst. cbn in * |- *.
            pose proof (vector_inv_0 v₂) as hd.
            pose proof (vector_inv_0 v₄) as he.
            rewrite hd, he in * |- *. cbn.
            subst; cbn.
            destruct (vector_inv_S v₁) as (ma & msr & hmm).
            rewrite hmm in * |- *.
            subst; cbn.
            pose proof (vector_inv_0 msr) as hd.
            subst; cbn.
            destruct (vector_inv_S v₃) as (mb & msr & hmm).
            subst; cbn.
            pose proof (vector_inv_0 msr) as hd.
            subst; cbn.
            assert (hd : c = (c₁ + (sub c (c₁ + zero) + zero))). field.
            rewrite <-hd; clear hd.
            destruct (Fdec c c)
            as [hdec | hdec]; try auto. 
            eapply Bool.andb_false_intro2.
            eapply Bool.andb_false_intro1.
            eapply Bool.andb_false_intro2.
            eapply dec_false; intro haa.
            assert (hb : c₁ + zero = c₁). field.
            rewrite !hb in haa; clear hb.
            assert(hb : g ^ one = g).
            rewrite field_one; reflexivity.
            rewrite !hb in haa; clear hb.
            assert (hb : gop (g ^ m) (h ^ r) = gop (h ^ r) (g ^ m)).
            rewrite commutative. reflexivity.
            rewrite !hb in haa; clear hb.
            assert (hb : (gop (gop (h ^ r) (g ^ m)) (ginv g)) = 
            gop (h ^ r) (gop (g ^ m) (ginv g))).
            rewrite associative; reflexivity.
            rewrite !hb in haa; clear hb.
            remember ((gop (g ^ m) (ginv g))) as gp.
            rewrite smul_distributive_vadd, smul_pow_mul,
            associative in haa.
            assert (hb : (gop (h ^ u₂) (h ^ (sub c c₁ * r))) = 
              h ^ (u₂ + sub c c₁ * r)).
            destruct Hvec. (* why do I need this destruct this? *)
            setoid_rewrite <-vector_space_smul_distributive_fadd;
            reflexivity.
            rewrite hb in haa; clear hb.
            eapply f_equal with (f := fun x => 
              gop (h ^ (opp (u₂ + sub c c₁ * r))) x) in haa.
            assert (hb : gop (h ^ opp (u₂ + sub c c₁ * r)) (h ^ (u₂ + sub c c₁ * r)) = gid).
            destruct Hvec.
            setoid_rewrite <-vector_space_smul_distributive_fadd.
            assert (hb : (opp (u₂ + sub c c₁ * r) + (u₂ + sub c c₁ * r)) = zero). field.
            rewrite hb; clear hb.
            rewrite field_zero; reflexivity.
            rewrite !hb in haa; clear hb.
            rewrite associative in haa.
            assert (hb : gop (h ^ opp (u₂ + sub c c₁ * r)) (h ^ (u₂ + sub c c₁ * r)) = 
            gid). destruct Hvec.
            rewrite <-vector_space_smul_distributive_fadd.
            assert (hb : (opp (u₂ + sub c c₁ * r) + (u₂ + sub c c₁ * r)) = zero).
            field. rewrite hb; clear hb.
            rewrite field_zero; reflexivity.
            rewrite hb in haa; clear hb.
            rewrite left_identity in haa.
            rewrite Heqgp in haa; clear Heqgp.
            rewrite <- (vector_space_field_zero g) in haa.
            assert (hb : gop (g ^ m) (ginv g) ^ sub c c₁ = 
              gop ((g ^ m) ^ sub c c₁) (ginv g ^ sub c c₁)).
            destruct Hvec.
            rewrite vector_space_smul_distributive_vadd; reflexivity.
            rewrite hb in haa; clear hb.
            eapply f_equal with (f := fun x => gop x (g ^ sub c c₁)) in haa.
            rewrite <-associative in haa.
            assert (hb : (gop (ginv g ^ sub c c₁) (g ^ sub c c₁)) = gid).
            destruct Hvec.
            rewrite <-vector_space_smul_distributive_vadd, left_inverse, 
            <-field_zero, smul_pow_up.
            assert (hb : zero * sub c c₁ = zero). field.
            rewrite hb; clear hb.
            reflexivity.
            rewrite hb in haa; clear hb.
            destruct Hvec.
            rewrite <- vector_space_smul_distributive_fadd, right_identity,
            smul_pow_up in haa.
            assert (hb : zero + sub c c₁ = sub c c₁). field.
            rewrite hb in haa; clear hb.
            eapply f_equal with (f := fun x => gop x (g ^ opp (sub c c₁))) in haa.
            assert(hb : gop (g ^ sub c c₁) (g ^ opp (sub c c₁)) = gid).
            destruct Hvec.
            rewrite <-vector_space_smul_distributive_fadd.
            assert(hb : (sub c c₁ + opp (sub c c₁)) = zero). field.
            rewrite hb; clear hb.
            rewrite field_zero; reflexivity.
            rewrite !hb in haa; clear hb.
            rewrite  <-smul_distributive_fadd in haa.
            assert (hb : (m * sub c c₁ + opp (sub c c₁)) = 
              (sub m one) * sub c c₁). field.
            rewrite hb in haa; clear hb.
            eapply eq_sym in haa.
            eapply gid_power_zero in haa.
            destruct haa as [haa | haa]; try congruence.
            eapply mul_eq_zero in haa.
            destruct haa as [haa | haa].
            +++
              eapply faa.
              eapply sub_eq;
              assumption.
            +++
              eapply hv.
              eapply eq_sym.
              eapply sub_eq.
              assumption.
          Unshelve.
          exact g. exact Fdec.
      Qed.



      (* 
        A theorem that states that if the prover can predict the challenge of 
        the verifier, then it can fake the proof. 


        if it is the case c = c₁ then 
        an invalid proof will also be accepted but 
        c = c₁ will happen with 1/|C| probability.
      *)
      Theorem vote_proof_invalid_accept :
        ∀ (r : F) (g h : G) (m : F)  (u₁ u₂ c₁ : F) (c : F),
          (m <> zero ∧ m <> one) → c₁ = c ->
          verify_encryption_vote_proof g h 
            (encrypt_vote_and_generate_enc_proof g h r m [u₁; u₂; c₁] c) = true.
      Proof.
        intros * [hal har] hb.
        unfold encrypt_vote_and_generate_enc_proof, 
        verify_encryption_vote_proof, 
        generate_enc_proof.
        eapply generalised_accepting_elgamal_conversations_correctness_gen.
        destruct (Fdec m zero) as [fa | fa]; try congruence.
        subst.
        unfold generalised_accepting_encryption_proof_elgamal, 
        enc, generalised_construct_encryption_proof_elgamal_real.
        simpl. 
        destruct (vector_fin_app_pred 1 (FS F1) [u₁; u₂] [c]) as
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
        destruct pfaa as [pfa].
        destruct pfbb as [pfb].
        destruct haa as [ha].
        destruct ha as (ha & hb & hc & hd).
        subst; cbn in * |- *.
        assert (m₂ = 0). 
        {
          destruct m₂ as [|m₂].
          reflexivity. nia.
        }
        subst. cbn. 
        assert (pfa = eq_refl). 
        eapply Eqdep_dec.UIP_refl_nat.
        assert (pfb = eq_refl). 
        eapply Eqdep_dec.UIP_refl_nat.
        subst. cbn in * |- *.
        pose proof (vector_inv_0 v₂) as hd.
        pose proof (vector_inv_0 v₄) as he.
        rewrite hd, he in * |- *. cbn.
        subst; cbn.
        destruct (vector_inv_S v₁) as (ma & msr & hmm).
        rewrite hmm in * |- *.
        subst; cbn.
        pose proof (vector_inv_0 msr) as hd.
        subst; cbn.
        destruct (vector_inv_S v₃) as (mb & msr & hmm).
        subst; cbn.
        pose proof (vector_inv_0 msr) as hd.
        subst; cbn.
        assert (hd : c = (c + (sub c (c + zero) + zero))). field.
        rewrite <-hd; clear hd.
        split. reflexivity.
        intros f. rewrite !dec_true.
        destruct (fin_inv_S _ f) as [f' | (f' & hf)].
        +
          subst; cbn.
          split.
          ++
            pose proof @simulator_completeness F zero one add mul sub div opp inv 
              G gid ginv gop gpow Gdec Hvec g (g ^ r) u₁ c as hb.
            unfold accepting_conversation, schnorr_simulator in hb.
            rewrite dec_true in hb; cbn in hb.
            exact hb.
          ++
            assert(hb :  (ginv (g ^ zero)) = gid). 
            rewrite field_zero, group_inv_id;
            reflexivity.
            rewrite !hb; clear hb.
            remember (gop (g ^ m) (h ^ r)) as gm.
            rewrite <-associative.
            assert (hb : gop (gop gm gid ^ opp c) (gop gm gid ^ c) = gid). 
            destruct Hvec.
            rewrite <-vector_space_smul_distributive_fadd.
            assert (hb : (opp c + c) = zero).
            field. rewrite hb; clear hb.
            rewrite field_zero; reflexivity.
            rewrite hb; clear hb.
            rewrite right_identity. 
            reflexivity.
        +
          subst; cbn.
          destruct (fin_inv_S _ f') as [f'' | (f'' & hf)];
          subst; cbn; (try refine match f'' with end).
          split.
          ++
            assert (hb : sub c (c + zero) * r = zero). field.
            rewrite !hb; clear hb.
            assert(hb : sub c (c + zero) = zero). field.
            rewrite hb; clear hb.
            rewrite field_zero, right_identity.
            rewrite right_identity; reflexivity.
          ++
            assert (hb : sub c (c + zero) * r = zero). field.
            rewrite !hb; clear hb.
            assert(hb : sub c (c + zero) = zero). field.
            rewrite hb; clear hb.
            rewrite field_one, field_zero, 
            right_identity, right_identity.
            reflexivity.
      Qed.


      (* ballot proof is valid *)
      Theorem ballot_proof_valid :
        ∀ (n : nat) (rs : Vector.t F n) (g h : G) 
          (ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n) (chs : Vector.t F n),
          (∀ (i : Fin.t n), Vector.nth ms i = zero ∨ Vector.nth ms i = one) ->
          verify_encryption_ballot_proof g h 
            (encrypt_ballot_and_generate_enc_proof g h rs ms uscs chs) = true.
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

      (* ---------------------------------------------------------------- *)
      (* Completeness of the overall proof. *)

      Lemma powers_nth : forall (g : G) (k : nat) (i : Fin.t (S k)), 
        (powers g k)[@i] = g ^ of_nat (proj1_sig (Fin.to_nat i)).
      Proof.
        intros g; induction k as [| k ih]; intros i.
        + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; 
          [reflexivity | inversion j].
        + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn; [reflexivity |].
          rewrite map_fin, ih.
          destruct (Fin.to_nat j) as (a & ha); cbn.
          rewrite (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_one; reflexivity.
          typeclasses eauto.
      Qed.

      Lemma gop_rearrange : forall (a b c d : G), 
        gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
      Proof.
        intros a b c d.
        rewrite <- associative, (associative b c d), (commutative b c), 
          <- (associative c b d), associative.
        reflexivity.
      Qed.

      (* the product of a ballot's ciphertexts encrypts the sum of the votes 
        under the sum of the randomness *)
      Lemma ballot_product_enc : forall (k : nat) (g h : G) (rs ms : Vector.t F k),
        ballot_product (encrypt_ballot g h rs ms) = 
        (g ^ Vector.fold_right add rs zero, 
         gop (g ^ Vector.fold_right add ms zero) (h ^ Vector.fold_right add rs zero)).
      Proof.
        induction k as [| k ih]; intros g h rs ms.
        + rewrite (vector_inv_0 rs), (vector_inv_0 ms); cbn.
          rewrite !vector_space_field_zero, left_identity; reflexivity.
        + destruct (vector_inv_S rs) as (r & rs' & hr).
          destruct (vector_inv_S ms) as (m & ms' & hm).
          subst; cbn.
          change (fold_right (λ '(a, b) '(c, d), (gop a c, gop b d)) 
            (encrypt_ballot g h rs' ms') (gid, gid)) 
            with (ballot_product (encrypt_ballot g h rs' ms')).
          rewrite ih; cbn.
          rewrite gop_rearrange.
          rewrite <- !(@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow).
          reflexivity.
          all: typeclasses eauto.
      Qed.

      (* on a 0/1 ballot the sum of the votes is the number of approvals *)
      Lemma sum_ballot_count : forall (k : nat) (ms : Vector.t F k),
        (forall i : Fin.t k, ms[@i] = zero ∨ ms[@i] = one) ->
        Vector.fold_right add ms zero = of_nat (count_ones ms).
      Proof.
        induction k as [| k ih]; intros ms hm.
        + rewrite (vector_inv_0 ms); reflexivity.
        + destruct (vector_inv_S ms) as (m & ms' & hms); subst.
          unfold count_ones in *; cbn.
          rewrite (ih ms' (fun i => hm (Fin.FS i))).
          destruct (Fdec m one) as [hone | hnone].
          * subst; cbn; reflexivity.
          * destruct (hm Fin.F1) as [hz | ho]; 
            [cbn in hz; subst; field | cbn in ho; contradiction].
      Qed.

      Theorem overall_proof_valid : forall (n : nat) (g h : G) 
        (rs ms : Vector.t F (S n)) (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F),
        (forall i : Fin.t (S n), ms[@i] = zero ∨ ms[@i] = one) ->
        verify_overall_proof g h (encrypt_ballot g h rs ms) 
          (generate_overall_proof g h rs ms uscs c) = true.
      Proof.
        intros * hm.
        unfold verify_overall_proof, generate_overall_proof.
        rewrite ballot_product_enc.
        apply generalised_construct_encryption_proof_elgamal_real_completeness.
        split; [reflexivity |].
        rewrite (powers_nth g (S n)).
        unfold overall_index; rewrite Fin.to_nat_of_nat; cbn.
        rewrite <- (sum_ballot_count _ ms hm).
        rewrite (commutative (g ^ Vector.fold_right add ms zero)), <- associative, 
          group_is_right_inverse, right_identity.
        reflexivity.
      Qed.

      (* an honest 0/1 ballot with its overall proof is accepted *)
      Theorem ballot_with_overall_proof_valid : forall (n : nat) (g h : G) 
        (rs ms : Vector.t F (S n)) (uscs : Vector.t (Vector.t F 3) (S n)) 
        (cs : Vector.t F (S n)) (uscs' : Vector.t F ((2 + n) + (1 + n))) (c : F),
        (forall i : Fin.t (S n), ms[@i] = zero ∨ ms[@i] = one) ->
        verify_ballot g h (encrypt_ballot_with_overall_proof g h rs ms uscs cs uscs' c) = true.
      Proof.
        intros * hm.
        unfold verify_ballot, encrypt_ballot_with_overall_proof; cbn [fst snd].
        rewrite ballot_proof_valid, first_project_ballot_encryption, overall_proof_valid;
        [reflexivity | exact hm | exact hm].
      Qed.


      (* ---------------------------------------------------------------- *)
      (* The commitments hashed by a non-interactive ballot are exactly 
        the announcements of the proofs. *)

      Lemma generate_enc_proof_commitment_announcement : 
        forall (g h : G) (r m : F) (uscs : Vector.t F 3) (cp : G * G) (c : F),
        Sigma.announcement (generate_enc_proof g h r m uscs cp c) = 
        generate_enc_proof_commitment g h m uscs cp.
      Proof.
        intros *.
        destruct (vector_inv_S uscs) as (u₁ & ust & ha).
        destruct (vector_inv_S ust) as (u₂ & ust' & hb).
        destruct (vector_inv_S ust') as (c₁ & ust'' & hc).
        pose proof (vector_inv_0 ust'') as hd.
        subst.
        unfold generate_enc_proof, generate_enc_proof_commitment.
        destruct (Fdec m zero) as [fa | fa].
        - unfold generalised_construct_encryption_proof_elgamal_real; simpl.
          destruct (vector_fin_app_pred 1 F1 [u₁; u₂] [c₁]) as 
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa]; destruct pfbb as [pfb]; 
          destruct haa as [ha]; destruct ha as (ha & hb & hc & hd).
          subst. cbn in * |- *.
          assert (m₂ = 1) by (destruct m₂ as [|[|m₂]]; try nia; reflexivity). 
          subst.
          assert (hp : pfa = eq_refl) by apply Stdlib.Logic.Eqdep_dec.UIP_refl_nat. 
          subst pfa. cbn in ha, hc. subst. 
          rewrite !eq_rew_r_dep_refl_nat. 
          destruct cp; cbn; reflexivity.
        - unfold generalised_construct_encryption_proof_elgamal_real; simpl.
          destruct (vector_fin_app_pred 1 (FS F1) [u₁; u₂] [c₁]) as 
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa]; destruct pfbb as [pfb]; 
          destruct haa as [ha]; destruct ha as (ha & hb & hc & hd).
          subst. cbn in * |- *.
          assert (m₂ = 0) by (destruct m₂ as [|m₂]; try nia; reflexivity). 
          subst.
          assert (hp : pfa = eq_refl) by apply Stdlib.Logic.Eqdep_dec.UIP_refl_nat. 
          subst pfa. cbn in ha, hc. subst. 
          rewrite !eq_rew_r_dep_refl_nat. 
          destruct cp; cbn.
          assert (hq : pfb = eq_refl) by apply Stdlib.Logic.Eqdep_dec.UIP_refl_nat. 
          subst pfb. cbn in hc. subst. 
          rewrite !eq_rew_r_dep_refl_nat. 
          cbn. reflexivity.
      Qed.

      Theorem ballot_commitment_announcement : 
        ∀ (n : nat) (r : Vector.t F n) (g h : G) (m : Vector.t F n) 
          (uscs : Vector.t (Vector.t F 3) n) (c : Vector.t F n),
        Vector.map (fun '(_, pf) => Sigma.announcement pf) 
          (encrypt_ballot_and_generate_enc_proof g h r m uscs c) = 
        generate_ballot_commitment g h r m uscs.
      Proof.
        induction n as [|n ihn].
        + intros *. reflexivity.
        + intros *.
          destruct (vector_inv_S r) as (rh & rt & ha).
          destruct (vector_inv_S m) as (mh & mt & hb).
          destruct (vector_inv_S uscs) as (uscsh & uscst & hc).
          destruct (vector_inv_S c) as (ch & ct & hd).
          subst. cbn. 
          rewrite ihn, generate_enc_proof_commitment_announcement.
          reflexivity.
      Qed.

    End Proofs.
End Approval.