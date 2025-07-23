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
      
      (* 
        
        x : common witness for all relations
        gs and hs : public inputs 
        c : single challenge

        h₁ = g₁^x ∧ h₂ = g₂^x ∧ h₃ = g₃^x ∧ ....
      *)
      Definition construct_eq_conversations_schnorr :
        forall {n : nat}, 
        F -> Vector.t G (2 + n) -> F  -> 
        F -> @sigma_proto F G (2 + n) 1 1. (* @sigma_proto n 1 1 *)
      Proof.
        intros n x gs u c.
        (* prover commits *)
        remember (Vector.map (fun g => gpow g u) gs) as commitment.
        exact (commitment; [c]; [u + c * x]).
      Defined.

      (* Does not involve the secret x *)
      (* input gs hs u c *)
      Definition construct_eq_conversations_simulator :
        forall {n : nat}, 
        Vector.t G (2 + n) ->  Vector.t G (2 + n) -> 
        F -> F -> @sigma_proto F G (2 + n) 1 1.
      Proof.
        intros n gs hs u c.
        remember (zip_with (fun x y => (x, y)) gs hs) as commitment.
        exact (map (fun '(g, h) => gop (gpow g u) (gpow h (opp c))) commitment;
        [c]; [u]).
      Defined.

       Definition generalised_eq_accepting_conversations : 
        forall {n : nat},
        Vector.t G (2 + n) -> Vector.t G (2 + n) ->
        @sigma_proto F G (2 + n) 1 1 -> bool.
      Proof.
        refine(
          fix Fn n :=
          match n with 
          | 0 => fun gs hs Ha => _ 
          | S n' => fun gs hs Ha => _
          end).
        +
          refine 
            match Ha with 
            |(a; c; r) => _ 
            end.
          destruct (vector_inv_S gs) as (g₁ & gs₁ & _).
          destruct (vector_inv_S gs₁) as (g₂ & _ & _).
          destruct (vector_inv_S hs) as (h₁ & hs₁ & _).
          destruct (vector_inv_S hs₁) as (h₂ & _ & _).
          destruct (vector_inv_S a) as (a₁ & a₂ & _).
          exact (@accepting_conversation F G gop gpow Gdec g₁ h₁ ([a₁]; c; r) && 
          @accepting_conversation F G gop gpow Gdec g₂ h₂ (a₂; c; r)).
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
        (gs : Vector.t G (2 + n)) (c : F) : dist (@sigma_proto F G (2 + n) 1 1) :=
        (* draw u randomly *)
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (construct_eq_conversations_schnorr x gs u c).
      
    
    
      (* without secret *)
      Definition generalised_eq_simulator_distribution 
        {n : nat} (lf : list F) 
        (Hlfn : lf <> List.nil) (gs hs : Vector.t G (2 + n)) 
        (c : F) : dist (@sigma_proto F G (2 + n) 1 1) :=
        (* draw u random  *)
        u <- uniform_with_replacement lf Hlfn ;;
        Ret (construct_eq_conversations_simulator gs hs u c).


    End Def.
    
    Section Proofs. 

      (* properties about generalised_eq_accepting_conversations *)

        Lemma generalised_eq_accepting_conversations_correctness_forward : 
          forall (n : nat) (gs hs : Vector.t G (2 + n)) 
          (s : @sigma_proto F G (2 + n) 1 1),
          generalised_eq_accepting_conversations gs hs s = true ->
          (∀ f : Fin.t (2 + n), 
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
            destruct (vector_inv_S gstl) as (ggh & gstll & Hd).
            destruct (vector_inv_S hs) as (hh & hstl & He).
            destruct (vector_inv_S hstl) as (hhh & hstll & Hf).
            destruct (vector_inv_S a) as (ah & atl & Hg).
            destruct (vector_inv_S atl) as (ahh & atll & Hi).
            destruct (fin_inv_S _ f) as [hf | (hf & Hj)].
            ++
              subst; cbn.
              cbn in Ha |- *.
              eapply andb_true_iff in Ha. 
              destruct Ha as [Hal Har].
              rewrite dec_true in Hal, Har |- *.
              exact Hal.
            ++
              destruct (fin_inv_S _ hf) as [hff | (hff & Hjj)];
              [|inversion hff].
              cbn.
              eapply dec_true. subst.
              cbn in Ha |- *.
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              rewrite dec_true in Hal, Har.
              exact Har.

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
          forall (n : nat) (gs hs : Vector.t G (2 + n)) 
          (s : @sigma_proto F G (2 + n) 1 1),
          (∀ f : Fin.t (2 + n), 
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
            destruct (vector_inv_S gstl) as (ggh & gstll & Hd).
            destruct (vector_inv_S hs) as (hh & hstl & He).
            destruct (vector_inv_S hstl) as (hhh & hstll & Hf).
            destruct (vector_inv_S a) as (ah & atl & Hg).
            destruct (vector_inv_S atl) as (ahh & atll & Hi).
            pose proof (Ha Fin.F1) as Hj.
            pose proof (Ha (Fin.FS Fin.F1)) as Hk.
            subst. cbn in Hk, Hj |- *.
            rewrite Hk, Hj. reflexivity.
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
          forall (n : nat) (gs hs : Vector.t G (2 + n)) 
          (s : @sigma_proto F G (2 + n) 1 1),
          (∀ f : Fin.t (2 + n), 
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
          forall (n : nat) (aw gs : Vector.t G (2 + n)) 
          (cw rw : Vector.t F 1) (c x u : F), 
          (aw; cw; rw) = construct_eq_conversations_schnorr x gs u c ->
          cw = [c] ∧ rw = [u + c * x].
        Proof.
          intros * ha. 
          unfold construct_eq_conversations_schnorr in ha.
          inversion ha; subst; 
          split; exact eq_refl.
        Qed.
        

         Lemma construct_eq_conversations_simulator_challenge_and_response :
          forall (n : nat) (aw gs hs : Vector.t G (2 + n)) 
          (cw rw : Vector.t F 1) (u c : F), 
          (aw; cw; rw) = construct_eq_conversations_simulator gs hs u c ->
          cw = [c] ∧ rw = [u].
        Proof.
          intros * ha.
          inversion ha; subst.
          split; exact eq_refl.
        Qed.

         (* end of properties *)

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.
        (* 
          {n : nat}
          (x : F) (* common witness for all relations *)
          (gs hs : Vector.t G (2 + n))
          (R : forall (f : Fin.t (2 + n)), 
            (Vector.nth gs f)^x = Vector.nth hs f).
        *)
        
         (* completeness *)
        Lemma construct_eq_conversations_schnorr_completeness 
          {n : nat}
          (x : F) (* common witness for all relations *)
          (gs hs : Vector.t G (2 + n))
          (R : forall (f : Fin.t (2 + n)), 
            (Vector.nth gs f)^x = Vector.nth hs f) : 
          forall (u c : F),
          generalised_eq_accepting_conversations gs hs
            (construct_eq_conversations_schnorr x gs u c) = true.
        Proof.
          unfold construct_eq_conversations_schnorr.
          induction n as [|n' IHn].
          +
            intros *.
            destruct (vector_inv_S gs) as (gh & gstl & Ha).
            destruct (vector_inv_S gstl) as (ggh & gstll & Hb).
            destruct (vector_inv_S hs) as (hh & hstl & Hc).
            destruct (vector_inv_S hstl) as (hhh & hstll & Hd).
            pose proof (R Fin.F1) as He.
            pose proof (R (Fin.FS Fin.F1)) as Hf.
            subst. cbn in He, Hf |- *.
            subst. cbn. eapply andb_true_iff.
            split; eapply schnorr_completeness; exact eq_refl.
          +
            intros *. cbn in * |-.
            destruct (vector_inv_S gs) as (gh & gstl & Ha).
            destruct (vector_inv_S hs) as (hh & hstl & Hb).
            rewrite Ha, Hb. cbn. 
            eapply andb_true_iff. split.
            ++
              eapply schnorr_completeness.
              subst; cbn.
              specialize (R Fin.F1); 
              cbn in R; subst; reflexivity.
            ++
              eapply IHn.
              rewrite Ha, Hb in R.
              intro f.
              exact (R (Fin.FS f)).
        Qed.

        

        Lemma construct_eq_conversations_simulator_completeness 
          {n : nat}
          (gs hs : Vector.t G (2 + n)) : 
          forall (u c : F),
          generalised_eq_accepting_conversations gs hs
            (construct_eq_conversations_simulator gs hs u c) = true.
        Proof.
          induction n as [|n' IHn].
          +
            intros *.
            destruct (vector_inv_S gs) as (gh & gstl & Ha).
            destruct (vector_inv_S gstl) as (ggh & gstll & Hb).
            destruct (vector_inv_S hs) as (hh & hstl & Hc).
            destruct (vector_inv_S hstl) as (hhh & hstll & Hd).
            subst; cbn.
            eapply andb_true_iff; split;
            eapply simulator_completeness.
            Unshelve. 
            all:eapply Fdec.
          +
            (* inductive case *)
            intros *.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            subst; cbn.
            eapply andb_true_iff; split.
            ++
              eapply simulator_completeness.
            ++
              eapply IHn.
      Qed.

      (* special soundness (proof of knowledge) *)
      (* This is a bit challenging *)
      Lemma generalise_eq_sigma_soundness 
        {n : nat}
        (gs hs : Vector.t G (2 + n)) :
        forall (a : Vector.t G (2 + n)) 
        (c₁ c₂ : F) (r₁ r₂ : F),
        generalised_eq_accepting_conversations gs hs (a; [c₁]; [r₁]) = true ->
        generalised_eq_accepting_conversations gs hs (a; [c₂]; [r₂]) = true ->
        c₁ <> c₂ ->
        ∃ y : F, (forall (f : Fin.t (2 + n)),
        (nth gs f)^y = (nth hs f)).
      Proof.
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
          
          destruct (vector_inv_S a) as (ah & atl & Hd).
          destruct (vector_inv_S gs) as (gsh & gstl & He).
          destruct (vector_inv_S hs) as (hsh & hstl & Hf).
          exists ((r₁ - r₂) * inv (c₁ - c₂));
          intros f.
          destruct (fin_inv_S _ f) as [hf | (hf & Hl)].
          ++
            pose proof (Ha Fin.F1) as Ha.
            pose proof (Hb Fin.F1) as Hb.
            subst; cbn. cbn in Ha, Hb.
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
            destruct (fin_inv_S _ hf) as [hff | (hff & _)];
            [|inversion hff].
            destruct (vector_inv_S gstl) as (ggh & gstll & Hg).
            destruct (vector_inv_S hstl) as (hhh & hstll & Hi).
            pose proof (Ha (Fin.FS Fin.F1)) as Ha.
            pose proof (Hb (Fin.FS Fin.F1)) as Hb.
             destruct (vector_inv_S atl) as (ahh & atll & Hj).
            subst; cbn in * |- *.
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
            assert (Hwt : gop ahh (hhh ^ c₁) = gop (hhh ^ c₁) ahh).
            rewrite commutative; reflexivity.
            rewrite Hwt in Hcom; clear Hwt.
            setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
            in Hcom.
            assert (Hwt : (gop ahh (gop (ginv ahh) (ginv (hhh ^ c₂)))) = 
            (ginv (hhh ^ c₂))).
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
            specialize (Hone hhh).
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
             G gid ginv gop gpow Gdec Hvec
            _ _ _ _ _ _ _ Hc Ha Hb as Hi.
            destruct Hi as (y & Hi & Hj).
            rewrite <-Hj.
            exact Hi.
      Qed.

      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      (* zero-knowledge *)
      Lemma generalised_eq_schnorr_distribution_transcript_generic 
        {n : nat}
        (x : F) (* common witness for all relations *)
        (gs hs : Vector.t G (2 + n))
        (R : forall (f : Fin.t (2 + n)), 
          (Vector.nth gs f)^x = Vector.nth hs f) : 
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
            exact R.
          ++
            intros * Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply construct_eq_conversations_schnorr_completeness.
              exact R.
            +++
              eapply IHl; try assumption.
              exact Ha.
      Qed.

      Lemma generalised_eq_schnorr_distribution_probability_generic 
        {n : nat}
        (x : F) (* common witness for all relations *)
        (gs : Vector.t G (2 + n)) : 
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
      Lemma generalised_eq_special_honest_verifier_schnorr_dist 
        {n : nat}
        (x : F) (* common witness for all relations *)
        (gs hs : Vector.t G (2 + n))
        (R : forall (f : Fin.t (2 + n)), 
          (Vector.nth gs f)^x = Vector.nth hs f) : 
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
          eapply generalised_eq_schnorr_distribution_transcript_generic.
          exact R.
          exact Ha.
        +
          eapply generalised_eq_schnorr_distribution_probability_generic;
          [intros * Hc;
          eapply uniform_probability; exact Hc|
          exact Ha].
      Qed.


      (* fact about simultor *)
      Lemma generalised_eq_simulator_distribution_transcript_generic 
        {n : nat}
        (gs hs : Vector.t G (2 + n)) : 
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


      Lemma generalised_eq_simulator_distribution_probability_generic 
        {n : nat}
        (gs hs : Vector.t G (2 + n)) : 
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
      Lemma generalised_eq_special_honest_verifier_simulator_dist 
        {n : nat}
        (gs hs : Vector.t G (2 + n)) : 
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


      Lemma generalised_eq_special_honest_verifier_zkp 
        {n : nat}
        (x : F) (* common witness for all relations *)
        (gs hs : Vector.t G (2 + n))
        (R : forall (f : Fin.t (2 + n)), 
          (Vector.nth gs f)^x = Vector.nth hs f) : 
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
          exact R.
          exact Ha. 
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_eq_special_honest_verifier_simulator_dist.
          exact Ha.
      Qed.
      
    End Proofs. 
  End EQ.
End DL. 