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

  Section And.
    Section Def. 

        Definition compose_two_and_sigma_protocols {n : nat} 
          (s₁ : @sigma_proto F G 1 1 1) (s₂ : @sigma_proto F G n 1 n) :
          @sigma_proto F G (1 + n) 1 (1 + n) :=
          match s₁, s₂ with 
          |(a₁; c₁; r₁), (a₂; _; r₂) =>
            (a₁ ++ a₂; c₁; r₁ ++ r₂)
          end.


        (*
            ∃ x₁ x₂ x₃ : g₁ = h₁^x₁ ∧ g₂ = h₂^x₂ ∧ g₃ = h₃^x₃ ...
            
            xs : List F (* list of secres*)
            gh and hs : List G (* list of public values *)
            c : single challenge 
        *)

        (* input: xs gs us c *)
        Definition construct_and_conversations_schnorr :
          forall {n : nat}, Vector.t F n -> Vector.t G n -> 
          Vector.t F n -> F -> @sigma_proto F G n 1 n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun xs gs us c => _
          | S n' => fun xs gs us c  => _
          end).
          + 
            (* Base case *)
            refine (mk_sigma _ _ _ [] [c] []).
          +
            destruct (vector_inv_S xs) as (xsh & xstl & _).
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            exact (@compose_two_and_sigma_protocols _
              (@schnorr_protocol F add mul G gpow xsh gsh ush c)
              (Fn _ xstl gstl ustl c)).
        Defined.


        (* Does not involve the secret x *)
        (*input: gs hs us c *)
        Definition construct_and_conversations_simulator :
          forall {n : nat}, 
          Vector.t G n ->  Vector.t G n -> Vector.t F n -> 
          F -> @sigma_proto F G n 1 n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun gs hs us c => _
          | S n' => fun gs hs us c  => _
          end).
          + 
            refine (mk_sigma _ _ _ [] [c] []).
          + 
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S hs) as (hsh & hstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            exact (@compose_two_and_sigma_protocols _ 
              (@schnorr_simulator F opp G gop gpow gsh hsh ush c)
              (Fn _ gstl hstl ustl c)).
        Defined.


        Definition generalised_and_accepting_conversations : 
          forall {n : nat}, 
          Vector.t G n -> Vector.t G n ->
          @sigma_proto F G n 1 n -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun _ _ p => true
            | S n' => fun gs hs p => 
              match p with 
              | (a; c ; r) => _ 
              end 
            end).
          destruct (vector_inv_S a) as (ah & atl & _).
          destruct (vector_inv_S c) as (ch & ctl & _).
          destruct (vector_inv_S r) as (rh & rtl & _).
          destruct (vector_inv_S gs) as (g & gtl & _).
          destruct (vector_inv_S hs) as (h & htl & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([ah]; [ch]; [rh])) &&
            (Fn _ gtl htl (atl; c; rtl))).
        Defined.


        (* Generalised And distribution *)
        Definition generalised_and_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (xs : Vector.t F n) (gs : Vector.t G n) 
          (c : F) : dist (@sigma_proto F G n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_schnorr xs gs us c).
        
        
        
        (* Generalised simulator distribution (without secret) *)
        Definition generalised_and_simulator_distribution 
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G n) 
          (c : F) : dist (@sigma_proto F G n 1 n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_simulator gs hs us c).

    End Def. 

    Section Proofs.

        (* properties about the generalised_and_accepting_conversations function *)

        Lemma generalised_and_accepting_conversations_correctness_forward : 
          forall (n : nat) (gs hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          generalised_and_accepting_conversations gs hs s = true ->
          (∀ (f : Fin.t n), 
            match s with 
            | (a; c; r) => 
              @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
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
            destruct (vector_inv_S gs) as (gsa & gstl & Hi).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            eapply andb_true_iff in Ha.
            destruct Ha as [Hal Har].
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            ++
              subst; cbn;
              exact Hal.
            ++
              rewrite Hi, Hf, Hd, Hj, He, 
              Hg; cbn.
              specialize (IHn _ _ _ Har hf);
              cbn in IHn.
              rewrite He in IHn;
              cbn in IHn; exact IHn.
        Qed.




        Lemma generalised_and_accepting_conversations_correctness_backward : 
          forall (n : nat) (gs hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation F G gop gpow Gdec  (nth gs f) (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end) ->
          generalised_and_accepting_conversations gs hs s = true.         
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
            destruct (vector_inv_S gs) as (gsa & gstl & Hi).
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
          forall (n : nat) (gs hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          (∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = true
          end) <->
          generalised_and_accepting_conversations gs hs s = true.         
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
          ∀ (n : nat) (xs : t F n) (gs : t G n) (us : t F n) 
          (c : F) (aw : t G n) (cw : t F 1) (rw : t F n),
          (aw; cw; rw) = construct_and_conversations_schnorr xs gs us c ->
          cw = [c].
        Proof.
          destruct n as [|n].
          +
            cbn;
            intros * ? ? ? ? ? ? ? Ha.
            inversion Ha; subst;
            reflexivity.
          +
            cbn;
            intros ? ? ? ? ? ? ? H.
            destruct (vector_inv_S xs) as (xsa & xstl & Ha).
            destruct (vector_inv_S gs) as (gsa & gstl & Hb).
            destruct (vector_inv_S us) as (usa & ustl & Hc).
            remember (construct_and_conversations_schnorr xstl gstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd in H;
            inversion H; 
            reflexivity.
        Qed.


        Lemma construct_and_conversations_simulator_challenge : 
          ∀ (n : nat) (gs hs : t G n) (us : t F n) 
          (c : F) (aw : t G n) (cw : t F 1) (rw : t F n),
          (aw; cw; rw) = construct_and_conversations_simulator gs hs us c ->
          cw = [c].
        Proof.
          destruct n as [|n].
          +
            cbn;
            intros * ? ? ? ? ? ? ? Ha.
            inversion Ha; subst;
            reflexivity.
          +
            cbn;
            intros ? ? ? ? ? ? ? H.
            destruct (vector_inv_S gs) as (gsa & gstl & Hb).
            destruct (vector_inv_S hs) as (hsa & hstl & Hc).
            destruct (vector_inv_S us) as (usa & ustl & Hd).
            remember (construct_and_conversations_simulator gstl hstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            rewrite Hd in H;
            inversion H; 
            reflexivity.
        Qed.
        (* end of same challenge *)


        (*
          ∃ x₁ x₂ x₃ : F : h₁ = g₁^x₁ ∧ h₂ = g₂^x₂ ∧ h₃ = g₃^x₃ ..... 
        *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}
          {n : nat}
          (xs : Vector.t F n)
          (gs hs : Vector.t G n)
          (R : forall (f : Fin.t n), 
            (Vector.nth gs f)^(Vector.nth xs f) = Vector.nth hs f).

        
        (* completeness *)
        Lemma construct_and_conversations_schnorr_completeness : 
          forall (us : Vector.t F n) (c : F),
          generalised_and_accepting_conversations gs hs
            (construct_and_conversations_schnorr xs gs us c) = true.
        Proof.
          induction n as [|n' IHn].
          +
            intros *.
            cbn; reflexivity.
          +
            intros *.
            cbn.
            destruct (vector_inv_S xs) as (xsa & xstl & Ha).
            destruct (vector_inv_S gs) as (gsa & gstl & Hb).
            destruct (vector_inv_S us) as (usa & ustl & Hc).
            remember (construct_and_conversations_schnorr xstl gstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            destruct (vector_inv_S hs) as (hsa & hstl & He).
            eapply andb_true_iff.
            split.
            ++
              eapply schnorr_completeness.
              (* I need hsa = gsa^x *)
              subst.
              specialize (R Fin.F1); 
              cbn in R; subst; reflexivity.
            ++
              specialize (IHn xstl gstl hstl).
              assert (Hg : (∀ f : Fin.t n', gstl[@f] ^ xstl[@f] = hstl[@f])).
              intros f; subst.
              exact (R (Fin.FS f)).
              specialize (IHn Hg ustl c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_and_conversations_schnorr_challenge in Heqs.
              rewrite <-Heqs.
              exact IHn. 
        Qed.




         Lemma construct_and_conversations_simulator_completeness : 
          forall (us : Vector.t F n) (c : F),
          generalised_and_accepting_conversations gs hs
            (construct_and_conversations_simulator gs hs us c) = true.
        Proof using -(xs R).
          clear xs R. 
          induction n as [|n' IHn].
          +
            intros *;
            cbn; reflexivity.
          +
            intros *;
            cbn.
            destruct (vector_inv_S gs) as (gsa & gstl & Ha).
            destruct (vector_inv_S hs) as (hsa & hstl & Hb).
            destruct (vector_inv_S us) as (usa & ustl & Hc).
            remember (construct_and_conversations_simulator gstl hstl ustl c) 
            as s. 
            refine
            (match s as s'
            return s = s' -> _ with 
            |(aw; cw; rw) => fun Hd => _  
            end eq_refl); cbn.
            eapply andb_true_iff.
            split.
            ++
              subst.
              now eapply simulator_completeness.
            ++
              specialize (IHn gstl hstl ustl c).
              rewrite <-Heqs, Hd in IHn.
              rewrite Hd in Heqs.
              eapply construct_and_conversations_simulator_challenge in Heqs.
              rewrite <-Heqs.
              exact IHn.
              Unshelve.
              eapply Fdec.
        Qed. 



        (* special soundeness (proof of knowledge) *)
        Lemma generalise_and_sigma_soundness :
          forall (a : Vector.t G n) (c₁ : Vector.t F 1) 
          (r₁ : Vector.t F n) (c₂ : Vector.t F 1) (r₂ : Vector.t F n),
          generalised_and_accepting_conversations gs hs (a; c₁; r₁) = true ->
          generalised_and_accepting_conversations gs hs (a; c₂; r₂) = true ->
          c₁ <> c₂ ->
          (* we can extract a vector of witnesses such that 
            all the individual relations hold gi^xi = hi *)
          (∃ ys : Vector.t F n, ∀ (f : Fin.t n), 
            (nth gs f)^(nth ys f) = (nth hs f)).
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
            destruct (vector_inv_S gs) as (gsh & gstl & Hj).
            destruct (vector_inv_S hs) as (hsh & hstl & Hk).
            specialize (IHn gstl hstl atl c₁ rtl₁ c₂ rtl₂).
            rewrite Hd, Hf, He, Hj, Hk in Ha; 
            cbn in Ha.
            rewrite Hd, Hg, Hi, Hj, Hk in Hb; 
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
              rewrite Hj, Hk, Hl; cbn.
              exact IHn.
        Qed.
        (* what an awesome proof *)


         #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).
        (* zero-knowledge-proof *)
        
        
        Lemma generalised_and_schnorr_distribution_transcript_generic : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (c : F ),
          List.In (trans, pr) (Bind l (λ us : t F n, 
            Ret (construct_and_conversations_schnorr xs gs us c))) → 
          generalised_and_accepting_conversations gs hs trans = true.
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
            Ret (construct_and_conversations_schnorr xs gs us c))) → 
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
          List.In (a, b)  (generalised_and_schnorr_distribution lf Hlfn xs gs c) ->
          (* it's an accepting conversation and probability is *)
          generalised_and_accepting_conversations gs hs a = true ∧ 
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
            Ret (construct_and_conversations_simulator gs hs us c))) → 
          generalised_and_accepting_conversations gs hs trans = true.
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
            Ret (construct_and_conversations_simulator gs hs us c))) → 
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
          List.In (a, b) (generalised_and_simulator_distribution lf Hlfn gs hs c) ->
          (* first component is true and probability is 1 / |lf|^n *)
          generalised_and_accepting_conversations gs hs a = true ∧ 
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
            (generalised_and_accepting_conversations gs hs a, p))
            (@generalised_and_schnorr_distribution n lf Hlfn xs gs c) = 
          List.map (fun '(a, p) => 
            (generalised_and_accepting_conversations gs hs a, p))
            (@generalised_and_simulator_distribution n lf Hlfn gs hs c).
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
  End And.
End DL.
