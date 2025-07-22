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

  Section And.
    Section Def. 

        (*
            ∃ x₁ x₂ x₃ : g^x₁ = h₁ ∧ g^x₂ = h₂ ∧ g^x₃ = h₃ ...
            
            xs : List F (* list of secres*)
            g and hs : List G (* list of public values *)
            c : single challenge
        *)
        (* input: xs g us c *)

        Definition construct_and_conversations_schnorr {n : nat}
          (xs : Vector.t F n) (g : G)  
          (us : Vector.t F n) (c : F) :  @sigma_proto F G n 1 n.
        Proof.
          (* commitment *)
          set (comm := Vector.map (fun y => g^y) us).
          (* challenge is already there *)
          set (usxs := zip_with (fun u x => (u, x)) us xs).
          set (res := Vector.map (fun '(u, x) => u + c * x) usxs).
          exact (comm; [c]; res).
        Defined.

        (* Does not involve the secret x *)
        (*input: gs hs us c *)
        Definition construct_and_conversations_simulator {n : nat}
          (g : G) (hs : Vector.t G n) (us : Vector.t F n) 
          (c : F) : @sigma_proto F G n 1 n.
        Proof.
          (* commitment *)
          set (ushs := zip_with (fun u h => (u, h)) us hs).
          set (comm := Vector.map (fun '(u, h) => gop (g^u) (h^(opp c))) ushs).
          refine(comm; [c]; us).
        Defined.


        Definition generalised_and_accepting_conversations : 
          forall {n : nat}, G -> Vector.t G n ->
          @sigma_proto F G n 1 n -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun _ _ p => true
            | S n' => fun g hs p => 
              match p with 
              | (a; c ; r) => _ 
              end 
            end).
          destruct (vector_inv_S a) as (ah & atl & _).
          destruct (vector_inv_S c) as (ch & ctl & _).
          destruct (vector_inv_S r) as (rh & rtl & _).
          destruct (vector_inv_S hs) as (h & htl & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([ah]; [ch]; [rh])) &&
            (Fn _ g htl (atl; c; rtl))).
        Defined.


         (* Generalised And distribution *)
        Definition generalised_and_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (xs : Vector.t F n) (g : G) 
          (c : F) : dist (@sigma_proto F G n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_schnorr xs g us c).
        
        
        
        (* Generalised simulator distribution (without secret) *)
        Definition generalised_and_simulator_distribution 
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (g : G) (hs : Vector.t G n) 
          (c : F) : dist (@sigma_proto F G n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_simulator g hs us c).



    End Def. 

    Section Proofs.
      
      (* properties about the generalised_and_accepting_conversations function *)

        Lemma generalised_and_accepting_conversations_correctness_forward : 
          forall (n : nat) (g : G) (hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          generalised_and_accepting_conversations g hs s = true ->
          (∀ (f : Fin.t n), 
            match s with 
            | (a; c; r) => 
              @accepting_conversation F G gop gpow Gdec g (nth hs f)
                ([(nth a f)]; c; [(nth r f)]) = true
            end).
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +  
            intros * Ha f.
            refine (match f with end).
          +
            intros * Ha f.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hc => _  
            end eq_refl).
            rewrite Hc in Ha.
            destruct (vector_inv_S a) as (ha & ta & Hd).
            destruct (vector_inv_S c) as (hc & tc & He).
            destruct (vector_inv_S r) as (hr & tr & Hf).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            eapply andb_true_iff in Ha.
            destruct Ha as [Hal Har].
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            ++
              subst; cbn;
              exact Hal.
            ++
              rewrite  Hf, Hd, Hj, He, 
              Hg; cbn.
              specialize (IHn _ _ _ Har hf);
              cbn in IHn.
              rewrite He in IHn;
              cbn in IHn; exact IHn.
        Qed.




        Lemma generalised_and_accepting_conversations_correctness_backward : 
          forall (n : nat) (g : G) (hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation F G gop gpow Gdec  g (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end) ->
          generalised_and_accepting_conversations g hs s = true.         
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +
            intros * Ha.
            reflexivity.
          +
            intros * Ha.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hb => _  
            end eq_refl).
            destruct (vector_inv_S a) as (ha & ta & Hc).
            destruct (vector_inv_S c) as (hc & tc & Hd).
            destruct (vector_inv_S r) as (hr & tr & He).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            eapply andb_true_iff; split.
            ++
              subst.
              exact (Ha Fin.F1).
            ++
              eapply IHn;
              intro fz.
              pose proof (Ha (Fin.FS fz)) as Hk.
              subst; cbn in Hk |- *.
              exact Hk.
        Qed.


        Lemma generalised_and_accepting_conversations_correctness : 
          forall (n : nat) (g : G) (hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end) <->
          generalised_and_accepting_conversations g hs s = true.         
        Proof.
          intros *; 
          split.
          +
            eapply generalised_and_accepting_conversations_correctness_backward;
            try assumption.
          +
            eapply generalised_and_accepting_conversations_correctness_forward;
            try assumption.
        Qed.


        (* Proof that we are using the same challenge for all 
          relations *)
        Lemma construct_and_conversations_schnorr_challenge : 
          ∀ (n : nat) (xs : t F n) (g : G) (us : t F n) 
          (c : F) (aw : t G n) (cw : t F 1) (rw : t F n),
          (aw; cw; rw) = construct_and_conversations_schnorr xs g us c ->
          cw = [c].
        Proof.
          intros * Ha.
          unfold construct_and_conversations_schnorr in Ha.
          inversion Ha; subst; reflexivity.
        Qed.


        Lemma construct_and_conversations_simulator_challenge : 
          ∀ (n : nat) (g : G) (hs : t G n) (us : t F n) 
          (c : F) (aw : t G n) (cw : t F 1) (rw : t F n),
          (aw; cw; rw) = construct_and_conversations_simulator g hs us c ->
          cw = [c].
        Proof.
         intros * Ha.
         inversion Ha; subst; 
         reflexivity.
        Qed.
        (* end of same challenge *)


        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

       
        Theorem construct_and_conversations_schnorr_completeness_generic : 
          forall (n : nat) (f : Fin.t n) (g : G) (hs : Vector.t G n)
          (us : Vector.t F n) (xs : Vector.t F n) (c : F),
          (forall (f : Fin.t n), g^(Vector.nth xs f) = Vector.nth hs f) ->
          @accepting_conversation F G gop gpow Gdec g hs[@f]
          ([(map (λ y : F, g ^ y) us)[@f]]; [c];
          [(map (λ '(u, x), u + c * x)
          (zip_with (λ u x : F, (u, x)) us xs))[@f]]) = true.
        Proof.
          induction n as [|n ihn].
          + 
            intros * R. refine match f with end.
          +
            intros * R. 
            destruct (vector_inv_S hs) as (hh & hst & ha).
            destruct (vector_inv_S us) as (uh & ust & hb).
            destruct (vector_inv_S xs) as (xh & xst & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              specialize (R Fin.F1); cbn in R.
              subst; cbn.
              eapply dec_true. 
              assert (Hg : (g ^ xh) ^ c = (g ^ (xh * c))).
              rewrite smul_pow_up. 
              reflexivity.
              rewrite Hg; clear Hg.
              assert (Hxc : xh * c = c * xh) by field.
              rewrite Hxc; clear Hxc.
              rewrite <- (@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow);
              subst; [exact eq_refl 
              | assumption].
            ++
              subst; cbn.
              eapply dec_true.
              specialize (ihn f' g hst ust xst c).
              cbn in ihn. rewrite dec_true in ihn.
              eapply ihn.
              intro f.
              specialize (R (Fin.FS f)); cbn in R.
              exact R.
        Qed.

        Theorem construct_and_conversations_simulator_completeness_generic : 
          forall (n : nat) (f : Fin.t n) (g : G) (hs : Vector.t G n)
          (us : Vector.t F n) (c : F),
          @accepting_conversation F G gop gpow Gdec g hs[@f]
          ([(map (λ '(u, h), gop (g ^ u) (h ^ opp c))
          (zip_with (λ (u : F) (h : G), (u, h)) us hs))[@f]];
          [c]; [us[@f]]) = true.
        Proof.
           induction n as [|n ihn].
          + 
            intros *. refine match f with end.
          +
            intros *. 
            destruct (vector_inv_S hs) as (hh & hst & ha).
            destruct (vector_inv_S us) as (uh & ust & hb).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              eapply dec_true.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn in ihn |- *.
              eapply ihn.
        Qed. 


         (*
          ∃ x₁ x₂ x₃ : F : h₁ = g^x₁ ∧ h₂ = g^x₂ ∧ h₃ = g^x₃ ..... 
        *)
        Context
          {n : nat}
          (xs : Vector.t F n)
          (g : G) 
          (hs : Vector.t G n)
          (R : forall (f : Fin.t n), 
            g^(Vector.nth xs f) = Vector.nth hs f).
        
        (* AND composition completeness *)
        Lemma construct_and_conversations_schnorr_completeness : 
          forall (us : Vector.t F n) (c : F),
          generalised_and_accepting_conversations g hs
            (construct_and_conversations_schnorr xs g us c) = true.
        Proof.
          intros *.
          eapply  generalised_and_accepting_conversations_correctness.
          unfold construct_and_conversations_schnorr.
          intro f. 
          eapply construct_and_conversations_schnorr_completeness_generic.
          exact R.
        Qed.

        Lemma construct_and_conversations_simulator_completeness : 
          forall (us : Vector.t F n) (c : F),
          generalised_and_accepting_conversations g hs
            (construct_and_conversations_simulator g hs us c) = true.
        Proof using -(xs R).
          clear xs R.
          intros *.
          eapply generalised_and_accepting_conversations_correctness.
          intro f.
          unfold construct_and_conversations_simulator.
          eapply construct_and_conversations_simulator_completeness_generic.
        Qed.


        (* special soundeness (proof of knowledge) *)
        Lemma generalise_and_sigma_soundness :
          forall (a : Vector.t G n) (c₁ : Vector.t F 1) 
          (r₁ : Vector.t F n) (c₂ : Vector.t F 1) (r₂ : Vector.t F n),
          generalised_and_accepting_conversations g hs (a; c₁; r₁) = true ->
          generalised_and_accepting_conversations g hs (a; c₂; r₂) = true ->
          c₁ <> c₂ ->
          (* we can extract a vector of witnesses such that 
            all the individual relations hold gi^xi = hi *)
          (∃ ys : Vector.t F n, ∀ (f : Fin.t n), 
            g^(nth ys f) = (nth hs f)).
        Proof using -(xs R).
          clear xs R. (* otherwise trival *)
          induction n as [|n' IHn].
          +
            intros * Ha Hb Hc.
            exists [];
            intros f; inversion f.
          +
            intros * Ha Hb Hc.
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & He).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hf).
            destruct (vector_inv_S c₂) as (ch₂ & ctl₂ & Hg).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S hs) as (hsh & hstl & Hk).
            specialize (IHn hstl atl c₁ rtl₁ c₂ rtl₂).
            rewrite Hd, Hf, He, Hk in Ha; 
            cbn in Ha.
            rewrite Hd, Hg, Hi, Hk in Hb; 
            cbn in Hb.
            eapply andb_true_iff in Ha, Hb.
            destruct Ha as [Hal Har];
            destruct Hb as [Hbl Hbr].
            rewrite <-He in Har;
            rewrite <-Hg in Hbr.
            specialize (IHn Har Hbr Hc).
            destruct IHn as (ys & IHn).
            exists (((rh₁ - rh₂) * inv (ch₁ - ch₂)) :: ys).
            intro f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)].
            ++
              subst; cbn.
              rewrite dec_true in Hal, Hbl.
              eapply f_equal with (f := ginv) in Hbl.
              rewrite connection_between_vopp_and_fopp in Hbl.
              rewrite group_inv_flip in Hbl.
              rewrite commutative in Hbl.
              pose proof (@rewrite_gop G gop _ _ _ _ Hal Hbl) as Hcom.
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow) in Hcom.
              rewrite <-ring_sub_definition in Hcom.
              assert (Hwt : gop ah (hsh ^ ch₁) = gop (hsh ^ ch₁) ah).
              rewrite commutative; reflexivity.
              rewrite Hwt in Hcom; clear Hwt.
              setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
              in Hcom.
              assert (Hwt : (gop ah (gop (ginv ah) (ginv (hsh ^ ch₂)))) = 
              (ginv (hsh ^ ch₂))).
              rewrite associative.
              rewrite group_is_right_inverse,
              monoid_is_left_idenity;
              reflexivity.
              rewrite Hwt in Hcom; clear Hwt.
              rewrite connection_between_vopp_and_fopp in Hcom.
              rewrite <-(@vector_space_smul_distributive_fadd 
                F (@eq F) zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow) in Hcom.
              apply f_equal with (f := fun x => x^(inv (ch₁ + opp ch₂)))
              in Hcom.
              rewrite !smul_pow_up in Hcom.
              assert (Hw : (ch₁ + opp ch₂) * inv (ch₁ + opp ch₂) = 
              (inv (ch₁ + opp ch₂) * (ch₁ + opp ch₂))).
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
              assert (Ht : ch₁ <> ch₂).
              intro Hg; eapply Hc;
              subst. f_equal.
              rewrite (vector_inv_0 ctl₁);
              rewrite (vector_inv_0 ctl₂);
              reflexivity.
              pose proof ring_neq_sub_neq_zero ch₁ ch₂ Ht as Hw.
              apply Hw.
              rewrite ring_sub_definition.
              exact Hf.
              all:typeclasses eauto.
            ++
              specialize (IHn hf).
              rewrite Hk, Hl; cbn.
              exact IHn.
        Qed.
        (* what an awesome proof *)


         #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).
        (* zero-knowledge-proof *)
        
        
        Lemma generalised_and_schnorr_distribution_transcript_generic : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (c : F ),
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_schnorr xs g us c))) → 
          generalised_and_accepting_conversations g hs trans = true.
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
              eapply construct_and_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_and_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.


         Lemma generalised_and_schnorr_distribution_probability_generic : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_schnorr xs g us c))) → 
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
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        Lemma generalised_and_special_honest_verifier_schnorr_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F) (a : sigma_proto) (b : prob), 
          List.In (a, b)  (generalised_and_schnorr_distribution lf Hlfn xs g c) ->
          (* it's an accepting conversation and probability is *)
          generalised_and_accepting_conversations g hs a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) n).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_and_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_and_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.



        (* fact about simultor *)
        Lemma generalised_and_simulator_distribution_transcript_generic : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_simulator g hs us c))) → 
          generalised_and_accepting_conversations g hs trans = true.
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
              eapply construct_and_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_and_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.


         Lemma generalised_and_simulator_distribution_probability_generic : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (c : F) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_and_conversations_simulator g hs us c))) → 
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
          is an accepting conversation and it's probability 1 / |lf|^n 
        *)
        Lemma generalised_and_special_honest_verifier_simulator_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F)  (a : sigma_proto) (b : prob),
          List.In (a, b) (generalised_and_simulator_distribution lf Hlfn g hs c) ->
          (* first component is true and probability is 1 / |lf|^n *)
          generalised_and_accepting_conversations g hs a = true ∧ 
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_and_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_and_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.
        


        (* Two distributions are identical (information theoretic security)*)
        Lemma generalised_and_special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) => 
            (generalised_and_accepting_conversations g hs a, p))
            (@generalised_and_schnorr_distribution n lf Hlfn xs g c) = 
          List.map (fun '(a, p) => 
            (generalised_and_accepting_conversations g hs a, p))
            (@generalised_and_simulator_distribution n lf Hlfn g hs c).
        Proof.
          intros ? ? ?.
          eapply map_ext_eq.
          + 
            unfold generalised_and_schnorr_distribution,
            generalised_and_simulator_distribution; cbn.
            repeat rewrite distribution_length.
            reflexivity.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_and_special_honest_verifier_schnorr_dist.
            exact Ha. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_and_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed. 

    End Proofs. 
  Section And. 
Section DL.