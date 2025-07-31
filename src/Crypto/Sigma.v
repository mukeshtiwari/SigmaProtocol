From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef 
  BinPos. 
From Algebra Require Import 
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import 
  Prob Distr. 
From Utility Require Import 
  Util. 
From ExtLib Require Import 
  Monad. 
  

Import MonadNotation 
  VectorNotations.

#[local] Open Scope monad_scope.

(* Discrete Logarithm Zero Knowlege Proof *) 
Section DL. 
  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}. 
    (* decidable equality on Field *)

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}. 
    (* decidable equality on G *)
    

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.


  Section SigmaDefinition.
    (* sigma protocol for proof of knowledge of discrete logarithm *)
    (* A prover is convincing a verifier that she know the discrete log, 
      log_{g} h = x. We will turn this into NIZK by Fiat-Shamir transform 
      (careful )*)
  
    Record sigma_proto {n m r : nat} : Type := 
      mk_sigma 
      {
        announcement : Vector.t G n; (* prover announcement*)
        challenge : Vector.t F m; (* verifier randomness *)
        response : Vector.t F r (* prover response *)
      }.

      
  

  End SigmaDefinition.


  #[local] Notation "( a ; c ; r )" := 
    (@mk_sigma _ _ _ a c r).

  

  Section Basic_sigma.

    (* 
      x is a secret that a prover tries to convince a verifier, 
      g and h are public value, in a group, and the relation 
      is discrete log ∃ x : F, g ^ x = h. 
    *)
    Section Def.
    
      (* x is a secret *)
      (* g and h are public values *)
      (* Relation: R := h = g^x *)
      (* A prover convinces a verified that they know 
        x such that h := g^x *)
      
      
      (* Real transcript, using randomness u and (secret) witness x *)
      Definition schnorr_protocol (x : F) (g : G) (u c : F) : @sigma_proto 1 1 1 :=  
        ([g^u]; [c]; [u + c * x]).

      (* Fake transcript (without the witness x) *)
      Definition schnorr_simulator (g h : G) (u c : F) : @sigma_proto 1 1 1 := 
        ([gop (g^u) (h^(opp c))]; [c]; [u]).

      (* 
        This function checks if a conversation (a; c; r) 
        is accepting or not. It checks if g^r = a * h^c
      *)
      Definition accepting_conversation 
        (g h : G) (v : @sigma_proto 1 1 1) : bool :=
        match v with
        | (a; c; r) =>  
          match Gdec (g^(hd r)) (gop (hd a) (h^(hd c))) with 
          | left _ => true
          | right _ => false 
          end
        end.


      (* Distribution that involves the secret x *)
      Definition schnorr_distribution  (lf : list F) 
        (Hlfn : lf <> List.nil) (x : F) (g : G) (c : F) : dist sigma_proto :=
        (* draw u from a random distribution *)
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (schnorr_protocol x g u c).
      
      
      (* without secret x *)
      Definition simulator_distribution (lf : list F) 
        (Hlfn : lf <> List.nil) (g h : G) (c : F) : dist sigma_proto :=
        (* draw u from a random distribution *)
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (schnorr_simulator g h u c).

    End Def.

    Section Proofs.

      (* properties about  accepting_conversation  *)
      (* (a; c; r) *)
      (* g^r := a ∙ h^c *)
      Lemma accepting_conversation_correct : 
          forall (g h a : G) (c r : F), 
          accepting_conversation g h ([a]; [c]; [r]) = true <->
          (g^r) = (gop a (h^c)). (* g^r := a ∙ h^c *)
      Proof.
        intros *; 
        split; intros Ha.
        all:
          (apply (@dec_true _ Gdec) in Ha; 
          exact Ha).
      Qed.
      
      (* end of properties *)

      (* Vector Space *)
      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub 
          div opp inv G (@eq G) gid ginv gop gpow}.

      
      (* add field *)
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).
        
      (* Sigma protocol is correct.
        For some randomness r (a = g^r) and challenge c, 
        (schnorr_protocol x g r c) returns 
        an accepting conversation.
      *)
      Lemma schnorr_completeness (g h : G) (x : F) (R : h = g^x) :
        forall (r c : F),
          accepting_conversation g h 
          (schnorr_protocol x g r c) = true.
      Proof.
        unfold schnorr_protocol, 
        accepting_conversation; cbn.
        intros *; rewrite R.
        assert (Hg : (g ^ x) ^ c = (g ^ (x * c))).
        rewrite smul_pow_up. 
        reflexivity.
        rewrite Hg; clear Hg.
        assert (Hxc : x * c = c * x) by field.
        rewrite Hxc; clear Hxc.
        rewrite <- (@vector_space_smul_distributive_fadd F (@eq F) 
          zero one add mul sub div
          opp inv G (@eq G) gid ginv gop gpow);
        subst; [rewrite dec_true; exact eq_refl 
        | assumption].
      Qed.


      (* it's same as above but more clear. 
          It explicitly binds the accepting 
          conversation to variables (a₁; c₁; r₁).
      *)
      Lemma schnorr_completeness_berry (g h : G) (x : F) (R : h = g^x) : 
        forall (r c : F) (a₁ : t G 1) (c₁ r₁ : t F 1),
        (a₁; c₁; r₁) = (schnorr_protocol x g r c) ->
        accepting_conversation g h (a₁; c₁; r₁) = true.
      Proof.
        intros * Ha; rewrite Ha;
        now eapply schnorr_completeness.
      Qed.


      (* simulator produces an accepting conversation,
          without using the secret x *)
      Lemma simulator_completeness (g h : G) : 
        forall (r c : F), 
        accepting_conversation g h (schnorr_simulator g h r c) = true.
      Proof.
        unfold accepting_conversation, 
          schnorr_simulator; 
        intros *; simpl.
        rewrite (@dec_true _ Gdec).
        rewrite <-associative.
        rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
          zero one add mul sub div 
          opp inv G (@eq G) gid ginv gop gpow).
        rewrite field_zero_iff_left,
        vector_space_field_zero,
        monoid_is_right_identity.
        reflexivity.
        typeclasses eauto.
      Qed.
      
      (* it's same as above but more clear. 
          It explicitly binds the accepting 
          conversation of simulator 
          to variables (a₁; c₁; r₁).
      *)
      Lemma simulator_completeness_berry (g h : G) : 
        forall (r c : F) (a₁ : t G 1) (c₁ r₁ : t F 1),
        (a₁; c₁; r₁) = (schnorr_simulator g h r c) ->
        accepting_conversation g h (a₁; c₁; r₁) = true.
      Proof.
        intros * Ha;
        rewrite Ha;
        apply simulator_completeness.
      Qed.



      (* special soundness: if the prover replies two challenge with 
        same randomness r, i.e., same announcement, 
        then exatractor can extract a witness 
      *)
    
      Lemma special_soundness_berry_gen (g h : G) : 
        forall (a : G) (c₁ r₁ c₂ r₂ : F),
        c₁ <> c₂ -> 
        accepting_conversation g h ([a]; [c₁]; [r₁]) = true -> (* and it's accepting *) 
        accepting_conversation g h ([a]; [c₂]; [r₂]) = true -> (* and it's accepting *)
        ∃ y : F, g^y = h ∧ y =  ((r₁ - r₂) * inv (c₁ - c₂)).
        (* The explicit value of y is require in EQ proof *)
        (* then we can find a witness y such that g^y = h *)
      Proof.
        intros * Ha Hb Hc.
        apply (@dec_true _ Gdec) in Hb, Hc. 
        cbn in Hb, Hc.
        (* produce a witness *)
        exists ((r₁ - r₂) * inv (c₁ - c₂)).
        eapply f_equal with (f := ginv) in Hc.
        rewrite connection_between_vopp_and_fopp in Hc.
        rewrite group_inv_flip  in Hc.
        rewrite commutative in Hc.
        pose proof (@rewrite_gop G gop _ _ _ _ Hb Hc) as Hcom.
        rewrite <-(@vector_space_smul_distributive_fadd 
          F (@eq F) zero one add mul sub div 
          opp inv G (@eq G) gid ginv gop gpow) in Hcom.
        rewrite <-ring_sub_definition in Hcom.
        assert (Hwt : gop a (h ^ c₁) = gop (h ^ c₁) a).
        rewrite commutative; reflexivity.
        rewrite Hwt in Hcom; clear Hwt.
        setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
        in Hcom.
        assert (Hwt : (gop a (gop (ginv a) (ginv (h ^ c₂)))) = 
        (ginv (h ^ c₂))).
        rewrite associative.
        rewrite group_is_right_inverse,
        monoid_is_left_idenity;
        reflexivity.
        rewrite Hwt in Hcom; clear Hwt.
        rewrite connection_between_vopp_and_fopp in Hcom.
        rewrite <-(@vector_space_smul_distributive_fadd 
          F (@eq F) zero one add mul sub div 
          opp inv G (@eq G) gid ginv gop gpow) in Hcom.
        apply f_equal with (f := fun x => x^(inv (c₁ + opp c₂)))
        in Hcom.
        rewrite !smul_pow_up in Hcom.
        assert (Hw : (c₁ + opp c₂) * inv (c₁ + opp c₂) = 
        (inv (c₁ + opp c₂) * (c₁ + opp c₂))).
        rewrite commutative; reflexivity.
        rewrite Hw in Hcom; clear Hw.
        rewrite field_is_left_multiplicative_inverse in Hcom.
        pose proof vector_space_field_one as Hone.
        unfold is_field_one in Hone.
        specialize (Hone h).
        rewrite Hone in Hcom.
        rewrite <-ring_sub_definition in Hcom.
        exact (conj Hcom eq_refl).
        intros Hf.
        pose proof ring_neq_sub_neq_zero c₁ c₂ Ha as Hw.
        apply Hw.
        rewrite ring_sub_definition.
        exact Hf.
        all:typeclasses eauto.
      Qed.


      Lemma special_soundness_berry (g h : G) : 
        forall (a : G) (c₁ r₁ c₂ r₂ : F),
        c₁ <> c₂ -> 
        accepting_conversation g h ([a]; [c₁]; [r₁]) = true -> (* and it's accepting *) 
        accepting_conversation g h ([a]; [c₂]; [r₂]) = true -> (* and it's accepting *)
        ∃ y : F, g^y = h.
        (* then we can find a witness y such that g^y = h *)
      Proof.
        intros * Ha Hb Hc.
        pose proof special_soundness_berry_gen g h
        a c₁ r₁ c₂ r₂ Ha Hb Hc as Hd.
        destruct Hd as (y & Hd & He).
        exists y; exact Hd.
      Qed.




      (* https://www.win.tue.nl/~berry/2WC13/LectureNotes.pdf 
        We fix the challenge and show that both,  protocol 
        using witness x as input and simulated --not using x--, 
        have the same distributions.
      
        To prove the indistinguishability between a real transcript 
        and a simulated transcript, we construct two distributions,
        one using the witness (real transcript) and other without
        using the witness (fake/simulator transcript). 
        We demonstrate that  
        the probability of the real transcript is same as 
        the fake transcript. One thing that is implicit 
        in these two distributions is both, real transcript 
        and fake transcript, pass the verification test, 
        i.e. returns true to a verifier. 
        We use this implicit knowledge and
        construct two distributions as a pair in 
        which the first pair is a sigma triple and second pair
        is the probability of the triple, ((a, c, r), prob), 
        in the given distribution. 
      
      *)

      (* involves secret x*)    
      (* Under the hood, it is modelled as a list and looks like:
          [((a; c; r), prob); ((a; c; r), prob) ......]
      *)
    
      
      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      (* every triple in schnorr distribution has 
        probability 1/n *)
      Lemma schnorr_distribution_probability_generic (x : F) (g h : G) : 
        forall (l : dist F) (trans : sigma_proto) 
        (prob : Prob.prob) (c : F) (n : nat),
        (forall trx prx, List.In (trx, prx) l -> prx = 1 / n) ->  
        List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_protocol x g u c))) ->
        prob = 1 / n.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          cbn in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst; 
          clear Hwa.
          unfold mul_prob, 
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.


      (* every triple in schnorr distribution is 
        an accepting conversation *)
      Lemma schnorr_distribution_transcript_generic (x : F) (g h : G) (R : h = g^x) : 
        forall(l : dist F) (trans : sigma_proto) 
        (prob : Prob.prob) (c : F),
        List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_protocol x g u c))) ->
        accepting_conversation g h trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha.
          simpl in Ha;
          inversion Ha.
        + intros * Ha.
          (* destruct l *)
          destruct l as [|(la, lp) l].
          ++
            simpl in Ha;
            destruct Ha as [Ha | Ha];
            inversion Ha.
            now eapply schnorr_completeness.
          ++
            
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              now eapply  schnorr_completeness.
            +++
              (* inductive case *)
              eapply IHl; exact Ha.
      Qed.
        
        
      

      (* special honest verifier zero-knowledge-proof *)
      (* Every elements in @schnorr_distribution 
        has probability 1/ (List.length lf) where 
        lf the list of scalor (Field) elements from which the 
        random r is drawn and every corresponding 
        conversation is accepting
      *)

      Lemma schnorr_distribution_probability (x : F) (g h : G) (R : h = g^x) : 
        forall (lf : list F) (Hlfn : lf <> List.nil) 
        (c : F) (a₁ : t G 1) (c₁ r₁ : t F 1) 
        (prob : Prob.prob) (n : nat),
        n = List.length lf -> 
        List.In ((a₁; c₁; r₁), prob) 
          (@schnorr_distribution lf Hlfn x g c) ->
        prob = 1 / n ∧
        accepting_conversation g h (a₁; c₁; r₁) = true.
      Proof.
        intros * Hn Hl.
        split.
        +
          assert (Hlt : List.length (uniform_with_replacement lf Hlfn) =
            List.length lf).
          unfold uniform_with_replacement.
          rewrite List.length_map;
          reflexivity.
          pose proof schnorr_distribution_probability_generic x g h  
          (uniform_with_replacement lf Hlfn)
          (a₁; c₁; r₁) prob c n as Ht.
          rewrite Hn in Ht |- *.
          exact (Ht (uniform_probability lf Hlfn) Hl).
        +
          unfold schnorr_distribution in Hl;
          cbn in Hl.
          eapply schnorr_distribution_transcript_generic;
          [exact R | exact Hl].
      Qed.
          
    

        
      Lemma simulator_distribution_probability_generic (g h : G) : 
        forall (l : dist F) (trans : sigma_proto) 
        (prob : Prob.prob) (c : F) (n : nat),
        (forall trx prx, List.In (trx, prx) l -> prx = 1 / n) ->  
        List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_simulator g h u c))) ->
        prob = 1 / n.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst; 
          clear Hwa.
          unfold mul_prob, 
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.


      Lemma simulator_distribution_transcript_generic (g h : G) : 
        forall (l : dist F) (trans : sigma_proto) 
        (prob : Prob.prob) (c : F),
        List.In (trans, prob) (Bind l (λ u : F, Ret (schnorr_simulator g h u c))) ->
        accepting_conversation g h trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha.
          simpl in Ha;
          inversion Ha.
        + intros * Ha.
          (* destruct l *)
          destruct l as [|(la, lp) l].
          ++
            simpl in Ha;
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply simulator_completeness.
          ++
            
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply simulator_completeness.
            +++
              (* inductive case *)
              eapply IHl; exact Ha.
      Qed.
      

      (* special honest verifier zero-knowledge-proof *)
      (* Every elements in @simulator_distribution 
        has probability 1/ (List.length lf) where 
        lf the list of Field element from which the 
        random r is drawn and it's an accepting 
        conversation *)
      Lemma probability_simulator_distribution (g h : G) : 
        forall (lf : list F) (Hlfn : lf <> List.nil) 
        (c : F) (a₁ : t G 1) (c₁ r₁ : t F 1) 
        (prob : Prob.prob) (n : nat),
        n = List.length lf -> 
        List.In ((a₁; c₁; r₁), prob) 
          (@simulator_distribution lf Hlfn g h c) ->
        prob = 1 / n ∧  (* probability is 1/n *)
        accepting_conversation g h (a₁; c₁; r₁) = true.
      Proof.
        intros * Hn Hl.
        split.
        +
          assert (Hlt : List.length (uniform_with_replacement lf Hlfn) =
            List.length lf).
          unfold uniform_with_replacement.
          rewrite List.length_map;
          reflexivity.
          pose proof simulator_distribution_probability_generic g h 
          (uniform_with_replacement lf Hlfn)
          (a₁; c₁; r₁) prob c n as Ht.
          rewrite Hn.
          rewrite Hn in Ht.
          specialize (Ht 
            (uniform_probability lf Hlfn) Hl).
          exact Ht.
        +
          unfold simulator_distribution in Hl.
          eapply simulator_distribution_transcript_generic;
          exact Hl.
      Qed.
        
          

      (* it's identical (information theoretic zero-knowledge proof) *)
      (* Under the hood, it is modelled as a list and looks like:
          [((a; c; r), prob); ((a; c; r), prob) ......].
        We map accepting_conversation to crunch the first pair, 
        (a, c, r), and produce boolean a value (true), 
        and then we show that these two distribution are 
        identical 
      *)
      Lemma special_honest_verifier_zkp (x : F) (g h : G) (R : h = g^x): 
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F), 
          List.map (fun '(a, p) => 
            (accepting_conversation g h a, p))
            (@schnorr_distribution lf Hlfn x g c) = 
          List.map (fun '(a, p) => 
            (accepting_conversation g h a, p))
            (@simulator_distribution lf Hlfn g h c).
      Proof.
        intros ? ? ?.
        eapply map_ext_eq.
        + unfold schnorr_distribution, simulator_distribution.
          cbn. repeat rewrite distribution_length. 
          reflexivity. 
        +
          intros (aa, cc, rr) y Ha. 
          eapply and_comm.
          eapply schnorr_distribution_probability.
          exact R. 
          auto. exact Ha.
        + 
          intros (aa, cc, rr) y Ha. 
          eapply and_comm.
          eapply probability_simulator_distribution.
          reflexivity. 
          exact Ha. 
      Qed.
      
    

    End Proofs.

    (* call the sha 256 hash function 
      here to turn the interactive version into non-interactive,
      strong Fiat Shamir transformation
      https://eprint.iacr.org/2016/771.pdf.
      Definition nizp_schnorr (r : F) :=
        let c := sha256_string statement-with-other-values in  
        schnorr_protocol r c.
    *)

  End Basic_sigma.
End DL.

Module Test.

  From Utility Require Import Zpstar.
  From Stdlib Require Import ZArith.
  Import Vspace Schnorr Zpfield Zpgroup.


  Definition q : Z := 11.
  Definition p : Z := 23.
  Theorem primeQ : Znumtheory.prime q : Prop : Type.
  Proof. compute. Admitted. 
  Theorem primeP : Znumtheory.prime p : Prop.
  Proof. compute. Admitted.
  Theorem pqrel : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Defined.
  (* secret value *)
  Definition x : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.
  (* group generator *)
  Definition g : @Schnorr_group p q := 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := eq_refl : (4 ^ q mod p)%Z = 1%Z|}.
  (* randomness for commitment*)
  Definition u : @Zp q :=
    {| Zpfield.v := 6; Zpfield.Hv := eq_refl : (6 mod q)%Z = 6%Z |}.
  (* challenge and it should be computed by hashing all the public values *)
  Definition c : @Zp q :=
    {| Zpfield.v := 4; Zpfield.Hv := eq_refl : (4 mod q)%Z = 4%Z |}.
  (* h = g^x *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine 
    (mk_schnorr 18 _ _ ).
    compute. split; reflexivity.
    compute. reflexivity.
  Defined.
  (* transcripte *)
  Definition transcript : @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1.
  Proof.
    refine (@schnorr_protocol Zp zp_add zp_mul Schnorr_group pow x g u c).
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply primeP.
    eapply primeQ.
  Defined.
  (* verification of transcript *)
  Definition verify : bool. 
  Proof.
    refine (@accepting_conversation (@Zp q) (@Schnorr_group p q)  mul_schnorr_group pow Schnorr.dec_zpstar g h transcript).
    eapply primeP.
    eapply primeQ.
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply primeP.
    eapply primeQ.
  Defined.
  (* ton of crap because of Qed *)
  (* Eval compute in verify. *)

End Test.

(* 
Require Import Extraction.
Extraction Language Haskell.
Recursive Extraction Test.verify.
https://gist.github.com/mukeshtiwari/6fd2c9cd8627271fd8d4c33625bad158
*)