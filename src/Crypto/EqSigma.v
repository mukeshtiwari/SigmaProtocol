From Coq Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef 
  BinPos. 
From Algebra Require Import 
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import 
  Prob Distr. 
From Utility Require Import Util. 
From ExtLib Require Import Monad. 
From Crypto Require Import Sigma.
  

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

  
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section EQ.

    Section Def. 

       Definition compose_two_eq_sigma_protocols {n : nat} 
          (s₁ : @sigma_proto F G 1 1 1) (s₂ : @sigma_proto F G n 1 1) :
          @sigma_proto F G (1 + n) 1 1 :=
        match s₁, s₂ with 
        |(a₁; c₁; r₁), (a₂; _; _) =>
          (a₁ ++ a₂; c₁; r₁)
        end.


      
        (* 
          
          x : common witness for all relations
          gs and hs : public inputs 
          c : single challenge

          h₁ = g₁^x ∧ h₂ = g₂^x ∧ h₃ = g₃^x ∧ ....
        *)
        Definition construct_eq_conversations_schnorr :
          forall {n : nat}, 
          F -> Vector.t G (1 + n) -> F  -> 
          F -> @sigma_proto F G (1 + n) 1 1. (* @sigma_proto n 1 1 *)
        Proof.
          refine(
            fix Fn n :=
            match n with 
            | 0 => fun x gs u c => _ 
            | S n' => fun x gs u c => _
            end).
          +
            (* base case *)
            destruct (vector_inv_S gs) as (g & _ & _).
            exact (@schnorr_protocol F add mul G gpow  x g u c).
          +
            (* inductive case *)
            destruct (vector_inv_S gs) as (g & gtl & _).
            exact (compose_two_eq_sigma_protocols 
            (@schnorr_protocol F add mul G gpow x g u c)
            (Fn _ x gtl u c)).
        Defined.


        (* Does not involve the secret x *)
        (* input gs hs u c *)
        Definition construct_eq_conversations_simulator :
          forall {n : nat}, 
          Vector.t G (1 + n) ->  Vector.t G (1 + n) -> 
          F -> F -> @sigma_proto F G (1 + n) 1 1.
        Proof.
          refine(
            fix Fn n :=
            match n with 
            | 0 => fun gs hs u c => _ 
            | S n' => fun gs hs u c => _
            end).
          +
            (* base case *)
            destruct (vector_inv_S gs) as (g & _ & _).
            destruct (vector_inv_S hs) as (h & _ & _).
            exact (@schnorr_simulator F opp G gop gpow g h u c).
          +
            (* inductive case *)
            destruct (vector_inv_S gs) as (g & gtl & _).
            destruct (vector_inv_S hs) as (h & htl & _).
            exact (compose_two_eq_sigma_protocols 
            (@schnorr_simulator F opp G gop gpow g h u c)
            (Fn _ gtl htl u c)).
        Defined.


        Definition generalised_eq_accepting_conversations : 
          forall {n : nat},
          Vector.t G (1 + n) -> Vector.t G (1 + n) ->
          @sigma_proto F G (1 + n) 1 1 -> bool.
        Proof.
          refine(
            fix Fn n :=
            match n with 
            | 0 => fun gs hs Ha => _ 
            | S n' => fun gs hs Ha => _
            end).
          +
            (* base case *)
            destruct (vector_inv_S gs) as (g & _ & _).
            destruct (vector_inv_S hs) as (h & _ & _).
            exact (@accepting_conversation F G gop gpow Gdec g h Ha).
          +
            destruct (vector_inv_S gs) as (g & gtl & _).
            destruct (vector_inv_S hs) as (h & htl & _).
            refine 
              match Ha with 
              |(a; c; r) => _ 
              end.
            destruct (vector_inv_S a) as (ah & atl & _).
            exact ((@accepting_conversation F G gop gpow Gdec g h ([ah]; c; r)) && 
              (Fn _ gtl htl (atl; c; r))).
        Defined.


        Definition generalised_eq_schnorr_distribution  
          {n : nat} (lf : list F)  (Hlfn : lf <> List.nil) (x : F) 
          (gs : Vector.t G (1 + n)) (c : F) : dist (@sigma_proto F G (1 + n) 1 1) :=
          (* draw u randomly *)
          u <- (uniform_with_replacement lf Hlfn) ;;
          Ret (construct_eq_conversations_schnorr x gs u c).
        
      
      
        (* without secret *)
        Definition generalised_eq_simulator_distribution 
          {n : nat} (lf : list F) 
          (Hlfn : lf <> List.nil) (gs hs : Vector.t G (1 + n)) 
          (c : F) : dist (@sigma_proto F G (1 + n) 1 1) :=
          (* draw u random  *)
          u <- uniform_with_replacement lf Hlfn ;;
          Ret (construct_eq_conversations_simulator gs hs u c).


    End Def.

    Section Proofs.


      (* properties about generalised_eq_accepting_conversations *)

        Lemma generalised_eq_accepting_conversations_correctness_forward : 
          forall (n : nat) (gs hs : Vector.t G (1 + n)) 
          (s : @sigma_proto F G (1 + n) 1 1),
          generalised_eq_accepting_conversations gs hs s = true ->
          (∀ f : Fin.t (1 + n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
              ([(nth a f)]; c; r) = true
          end).
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha ?.
            cbn in f.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)];
            [|inversion hf].
            subst; cbn.
            cbn in Ha |- *.
            rewrite dec_true in Ha |- *.
            exact Ha.
          +
            intros * Ha ?.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            subst; cbn in Ha |- *.
            eapply andb_true_iff in Ha.
            destruct Ha as [Hal Har].
            exact Hal.
            subst. cbn in Ha |- *.
            eapply andb_true_iff in Ha;
            destruct Ha as [Hal Har].
            specialize (IHn gstl hstl _ Har hf); 
            cbn in IHn.
            exact IHn.
        Qed.


         Lemma generalised_eq_accepting_conversations_correctness_backward : 
          forall (n : nat) (gs hs : Vector.t G (1 + n)) 
          (s : @sigma_proto F G (1 + n) 1 1),
          (∀ f : Fin.t (1 + n), 
            match s with 
            | (a; c; r) => 
              @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
                ([(nth a f)]; c; r) = true
            end) -> generalised_eq_accepting_conversations gs hs s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            specialize (Ha Fin.F1).
            rewrite Hb in Ha.
            subst; cbn in Ha |- *;
            exact Ha.
          +

            intros * Ha.
            refine
              (match s as s' return s = s' -> _ 
              with 
              |(a; c; r) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & Hc).
            destruct (vector_inv_S hs) as (hh & hstl & Hd).
            destruct (vector_inv_S a) as (ah & atl & He).
            rewrite Hc, Hd, He; cbn.
            eapply andb_true_iff.
            split.
            specialize (Ha Fin.F1);
            rewrite Hb, Hc, Hd, He in Ha; 
            cbn in Ha; exact Ha.
            eapply IHn;
            intros f.
            pose proof (Ha (Fin.FS f)) as Hf.
            rewrite Hb, Hc, Hd, He in Hf; 
            cbn in Hf.
            exact Hf.
        Qed.


        Lemma generalised_eq_accepting_conversations_correctness : 
          forall (n : nat) (gs hs : Vector.t G (1 + n)) 
          (s : @sigma_proto F G (1 + n) 1 1),
          (∀ f : Fin.t (1 + n), 
            match s with 
            | (a; c; r) => 
              @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
                ([(nth a f)]; c; r) = true
            end) <-> generalised_eq_accepting_conversations gs hs s = true.
        Proof.
          intros *; 
          split.
          +
            eapply generalised_eq_accepting_conversations_correctness_backward;
            try assumption.
          +
            eapply generalised_eq_accepting_conversations_correctness_forward;
            try assumption.
        Qed.


        Lemma construct_eq_conversations_schnorr_challenge_and_response :
          forall (n : nat) (aw gs : Vector.t G (1 + n)) 
          (cw rw : Vector.t F 1) (c x u : F), 
          (aw; cw; rw) = construct_eq_conversations_schnorr x gs u c ->
          cw = [c] ∧ rw = [u + c * x].
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            destruct (vector_inv_S gs) as (gsh & gstl & Hb).
            subst; cbn in Ha.
            unfold schnorr_protocol in Ha; 
            inversion Ha; subst. 
            refine (conj _ _); reflexivity.
          +
            intros * Ha.
            destruct (vector_inv_S aw) as (awh & awtl & Hb).
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
            specialize (IHn awtl gstl cw rw c x u).
            rewrite Hc in Ha; cbn in Ha.
            remember (construct_eq_conversations_schnorr x gstl u c) 
            as s.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd, Hb in Ha.
            inversion Ha; subst.
            refine(conj _ _);
            reflexivity.
        Qed.


         Lemma construct_eq_conversations_simulator_challenge_and_response :
          forall (n : nat) (aw gs hs : Vector.t G (1 + n)) 
          (cw rw : Vector.t F 1) (u c : F), 
          (aw; cw; rw) = construct_eq_conversations_simulator gs hs u c ->
          cw = [c] ∧ rw = [u].
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            destruct (vector_inv_S gs) as (gsh & gstl & Hb).
            destruct (vector_inv_S hs) as (hsh & hstl & Hc).
            subst; cbn in Ha.
            unfold schnorr_protocol in Ha; 
            inversion Ha; subst. 
            refine (conj _ _); reflexivity.
          +
            intros * Ha.
            destruct (vector_inv_S aw) as (awh & awtl & Hb).
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            specialize (IHn awtl gstl hstl cw rw u c).
            rewrite Hc in Ha; cbn in Ha.
            rewrite Hd in Ha; cbn in Ha.
            remember (construct_eq_conversations_simulator gstl hstl u c) 
            as s.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd, Hb in Ha.
            inversion Ha; subst.
            refine(conj _ _);
            reflexivity.
        Qed.


        (* end of properties *)

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}
          {n : nat}
          (x : F) (* common witness for all relations *)
          (gs hs : Vector.t G (1 + n))
          (R : forall (f : Fin.t (1 + n)), 
            (Vector.nth gs f)^x = Vector.nth hs f).

        
         (* completeness *)
        Lemma construct_eq_conversations_schnorr_completeness : 
          forall (u c : F),
          generalised_eq_accepting_conversations gs hs
            (construct_eq_conversations_schnorr x gs u c) = true.
        Proof.
          induction n as [|n' IHn].
          +
            intros *.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            specialize (R Fin.F1); subst; cbn in R |- *.
            eapply schnorr_completeness.
            rewrite <-R; reflexivity.
          +
            intros *; cbn.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            remember (construct_eq_conversations_schnorr x gstl u c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            eapply andb_true_iff.
            split.
            ++
              eapply schnorr_completeness.
              (* I need hsa = gsa^x *)
              subst.
              specialize (R Fin.F1); 
              cbn in R; subst; reflexivity.
            ++
              specialize (IHn gstl hstl).
              assert (Hg : (∀ f : Fin.t (1 + n'), gstl[@f] ^ x = hstl[@f])).
              intros f; subst.
              exact (R (Fin.FS f)).
              specialize (IHn Hg u c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_eq_conversations_schnorr_challenge_and_response 
              in Heqs.
              destruct Heqs as [Heqsl Heqsr].
              subst; exact IHn.
        Qed.


         Lemma construct_eq_conversations_simulator_completeness : 
          forall (u c : F),
          generalised_eq_accepting_conversations gs hs
            (construct_eq_conversations_simulator gs hs u c) = true.
        Proof using -(x R).
          clear x R.
          induction n as [|n' IHn].
          +
            intros *.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            subst.
            eapply simulator_completeness.
          +
            intros *; cbn.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            remember (construct_eq_conversations_simulator gstl hstl u c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            eapply andb_true_iff.
            split.
            ++
              eapply simulator_completeness.
            ++
              specialize (IHn gstl hstl u c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_eq_conversations_simulator_challenge_and_response
              in Heqs.
              destruct Heqs; subst.
              exact IHn.
              Unshelve.
              eapply Fdec.
              eapply Fdec.
        Qed.


        (* special soundness (proof of knowledge) *)
        (* This is a bit challenging *)
        Lemma generalise_eq_sigma_soundness :
         forall (a : Vector.t G (1 + n)) 
         (c₁ c₂ : F) (r₁ r₂ : F),
         generalised_eq_accepting_conversations gs hs (a; [c₁]; [r₁]) = true ->
         generalised_eq_accepting_conversations gs hs (a; [c₂]; [r₂]) = true ->
         c₁ <> c₂ ->
         ∃ y : F, (forall (f : Fin.t (1 + n)),
          (nth gs f)^y = (nth hs f)).
        Proof using -(x R).
          clear x R. (* otherwise trival *)
          intros * Ha Hb Hc.
          pose proof 
            (generalised_eq_accepting_conversations_correctness_forward _ 
            gs hs _ Ha) as Hd.
          pose proof 
            (generalised_eq_accepting_conversations_correctness_forward _ 
            gs hs _ Hb) as He.
          clear Ha; clear Hb.
          rename Hd into Ha.
          rename He into Hb.
          induction n as [|n' IHn].
          +
            specialize (Ha Fin.F1). 
            specialize (Hb Fin.F1).
            cbn in Ha, Hb.
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S gs) as (gsh & gstl & He).
            destruct (vector_inv_S hs) as (hsh & hstl & Hf).
            subst; cbn in Ha, Hb.
            rewrite dec_true in Ha, Hb.
            exists ((r₁ - r₂) * inv (c₁ - c₂));
            intros f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)];
            [|inversion hf].
            subst; cbn.
            eapply f_equal with (f := ginv) in Hb.
            rewrite connection_between_vopp_and_fopp in Hb.
            rewrite group_inv_flip in Hb.
            rewrite commutative in Hb.
            pose proof (@rewrite_gop G gop _ _ _ _ Ha Hb) as Hcom.
            rewrite <-(@vector_space_smul_distributive_fadd 
              F (@eq F) zero one add mul sub div 
              opp inv G (@eq G) gid ginv gop gpow) in Hcom.
            rewrite <-ring_sub_definition in Hcom.
            assert (Hwt : gop ah (hsh ^ c₁) = gop (hsh ^ c₁) ah).
            rewrite commutative; reflexivity.
            rewrite Hwt in Hcom; clear Hwt.
            setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
            in Hcom.
            assert (Hwt : (gop ah (gop (ginv ah) (ginv (hsh ^ c₂)))) = 
            (ginv (hsh ^ c₂))).
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
            specialize (Hone hsh).
            rewrite Hone in Hcom.
            rewrite <-ring_sub_definition in Hcom.
            exact Hcom.
            intros Hf.
            pose proof ring_neq_sub_neq_zero c₁ c₂ Hc as Hw.
            apply Hw.
            rewrite ring_sub_definition.
            exact Hf.
            all:typeclasses eauto. 
          +
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S gs) as (gsh & gstl & He).
            destruct (vector_inv_S hs) as (hsh & hstl & Hf).
            exists ((r₁ - r₂) * inv (c₁ - c₂)).
            intros f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)].
            ++
              specialize (Ha f).
              specialize (Hb f).
              rewrite He, Hf, hf.
              cbn.
              subst. cbn in Ha, Hb.
              rewrite dec_true in Ha, Hb.
              eapply f_equal with (f := ginv) in Hb.
              rewrite connection_between_vopp_and_fopp in Hb.
              rewrite group_inv_flip in Hb.
              rewrite commutative in Hb.
              pose proof (@rewrite_gop G gop _ _ _ _ Ha Hb) as Hcom.
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow) in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              assert (Hwt : gop ah (hsh ^ c₁) = gop (hsh ^ c₁) ah).
              rewrite commutative; reflexivity.
              rewrite Hwt in Hcom; clear Hwt.
              setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
              in Hcom.
              assert (Hwt : (gop ah (gop (ginv ah) (ginv (hsh ^ c₂)))) = 
              (ginv (hsh ^ c₂))).
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
              specialize (Hone hsh).
              rewrite Hone in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              exact Hcom.
              intros Hf.
              pose proof ring_neq_sub_neq_zero c₁ c₂ Hc as Hw.
              apply Hw.
              rewrite ring_sub_definition.
              exact Hf.
              all:typeclasses eauto.
            ++
              specialize (Ha f).
              specialize (Hb f).
              rewrite He, Hf, Hl in Ha, Hb |- *.
              cbn in Ha, Hb |- *.
              rewrite Hd in Ha, Hb.
              cbn in Ha, Hb.
              pose proof @special_soundness_berry_gen 
              F zero one add mul sub div opp inv 
              Fdec G gid ginv gop gpow Gdec Hvec
              _ _ _ _ _ _ _ Hc Ha Hb as Hi.
              destruct Hi as (y & Hi & Hj).
              rewrite <-Hj.
              exact Hi.
        Qed.



        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (* zero-knowledge *)
        Lemma generalised_eq_schnorr_distribution_transcript_generic : 
          forall (l : dist F) (trans : sigma_proto) (pr : prob) (c : F ),
          List.In (trans, pr)
            (Bind l (λ u,
              Ret (construct_eq_conversations_schnorr x gs u c))) → 
          generalised_eq_accepting_conversations gs hs trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_eq_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_eq_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.


         Lemma generalised_eq_schnorr_distribution_probability_generic : 
          forall (l :  dist F) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : F) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr)
            (Bind l (λ u : F,
              Ret (construct_eq_conversations_schnorr x gs u c))) → 
          pr = 1 / m.
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


         (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf| 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        Lemma generalised_eq_special_honest_verifier_schnorr_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_eq_schnorr_distribution lf Hlfn x gs c) ->
            (* it's an accepting conversation and probability is *)
          generalised_eq_accepting_conversations gs hs a = true ∧ 
          b = 1 / (List.length lf).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_eq_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_eq_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability; exact Hc|
            exact Ha].
        Qed.



          (* fact about simultor *)
        Lemma generalised_eq_simulator_distribution_transcript_generic : 
          forall (l :  dist F) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ u : F,
              Ret (construct_eq_conversations_simulator gs hs u c))) → 
          generalised_eq_accepting_conversations gs hs trans = true.
        Proof.
          induction l as [|(a, p) l IHl].
          +
            intros * Ha.
            cbn in Ha; 
            inversion Ha.
          +
            (* destruct l *)
            destruct l as [|(la, lp) l].
            ++
              intros * Ha.
              cbn in Ha.
              destruct Ha as [Ha | Ha];
              inversion Ha.
              eapply construct_eq_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_eq_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.


        Lemma generalised_eq_simulator_distribution_probability_generic : 
          forall (l :  dist F) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : F) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr)
            (Bind l (λ u : F,
              Ret (construct_eq_conversations_simulator gs hs u c))) → 
          pr = 1 / m.
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


        (* special honest verifier zero-knowledge *)
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|
        *)
        Lemma generalised_eq_special_honest_verifier_simulator_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_eq_simulator_distribution lf Hlfn gs hs c) ->
            (* first component is true and probability is *)
          generalised_eq_accepting_conversations gs hs a = true ∧ 
          b = 1 / (List.length lf).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_eq_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_eq_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability; exact Hc|
            exact Ha].
        Qed.


         Lemma generalised_eq_special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) => 
            (generalised_eq_accepting_conversations gs hs a, p))
            (@generalised_eq_schnorr_distribution n lf Hlfn x gs c) = 
          List.map (fun '(a, p) => 
            (generalised_eq_accepting_conversations gs hs a, p))
            (@generalised_eq_simulator_distribution n lf Hlfn gs hs c).
        Proof.
          intros ? ? ?.
          eapply map_ext_eq.
          +
            unfold generalised_eq_schnorr_distribution, 
            generalised_eq_simulator_distribution;
            cbn. repeat rewrite distribution_length. 
            reflexivity. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_eq_special_honest_verifier_schnorr_dist.
            exact Ha. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_eq_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed.

    End Proofs.
  End EQ.
End DL.


