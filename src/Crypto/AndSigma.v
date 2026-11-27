(** * AND composition of Schnorr proofs with a common base *)

(** This file proves knowledge of [n] discrete logarithms simultaneously,
    all with respect to the same generator [g]: the relation is

    [[
      R(g, (h₁, …, hₙ); (x₁, …, xₙ))  :⇔  ∀ i, g ^ xᵢ = hᵢ.
    ]]

    The composition runs [n] Schnorr protocols in parallel but, unlike
    [ParallelSigma], under a _single shared_ challenge [c]: the prover
    sends [(g ^ u₁, …, g ^ uₙ)], receives [c] and answers
    [(u₁ + c · x₁, …, uₙ + c · xₙ)]. The verifier
    [generalised_and_accepting_conversations] checks
    [g ^ rᵢ = aᵢ · hᵢ ^ c] for every [i]. Transcripts have type
    [@sigma_proto F G n 1 n].

    _Results._

    - Characterisation of the verifier: it accepts iff every component is an
      accepting Schnorr transcript (and rejects iff some component
      rejects).
    - Completeness of the prover (under [∀ i, g ^ xᵢ = hᵢ]) and of the
      simulator (unconditionally).
    - Special soundness [generalise_and_sigma_soundness]: two accepting
      transcripts with the same announcement vector and different shared
      challenges yield a full witness vector [ys] with [g ^ yᵢ = hᵢ] for
      all [i], computed componentwise by Schnorr's extractor
      [(r₁ᵢ - r₂ᵢ) · (c₁ - c₂)⁻¹].
    - Special HVZK, weak form
      ([generalised_and_special_honest_verifier_zkp]: equal lists of
      acceptance bits and probabilities) and as equality of distributions
      up to permutation ([generalised_and_special_honest_verifier_zkp_perm],
      [generalised_and_special_honest_verifier_zkp_enum]).

    A generalisation with an independent base per component lives in
    [AndSigmaGen]. This file is used by [Okamoto] and instantiated (and
    extracted) in [Examples/AndSigmaIns.v]. Reference: Cramer, Damgård and
    Schoenmakers, ‘Proofs of partial knowledge’, CRYPTO 1994, for AND/OR
    composition of Sigma protocols. *)
From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
   BinPos Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import Util.
From ExtLib Require Import Monad.
From Sigma Require Import Sigma.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(** ** AND composition with a common generator *)

(** Field of exponents with decidable equality. *)
Section DL.
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** Group of elements with exponentiation [gpow] and decidable equality. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Local infix notations for exponentiation and field operations. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** Transcript constructor [(a; c; r)] for [sigma_proto]. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section And.
    (** *** Definitions *)
    Section Def.

        (** Announcement vector [(g ^ u₁, …, g ^ uₙ)] for randomness [us]. *)
        Definition construct_and_conversations_schnorr_commitment
          {n : nat} (g : G) (us : Vector.t F n) : Vector.t G n :=
          Vector.map (fun y => g^y) us.

        (** Honest prover with witnesses [xs], generator [g], randomness [us]
            and the single challenge [c]: announcement [(g ^ uᵢ)ᵢ],
            one-element challenge vector [c :: nil], responses
            [(uᵢ + c · xᵢ)ᵢ]. *)
        Definition construct_and_conversations_schnorr {n : nat}
          (xs : Vector.t F n) (g : G)
          (us : Vector.t F n) (c : F) :  @sigma_proto F G n 1 n.
        Proof.
          set (comm := construct_and_conversations_schnorr_commitment
            g us).
          set (usxs := zip_with (fun u x => (u, x)) us xs).
          set (res := Vector.map (fun '(u, x) => u + c * x) usxs).
          exact (comm; [c]; res).
        Defined.

        (** Simulator for statements [hs], randomness [us] and challenge [c]:
            announcement [(g ^ uᵢ · hᵢ ^ (-c))ᵢ], one-element challenge
            vector [c :: nil], responses [us]. No witness is used. *)
        Definition construct_and_conversations_simulator {n : nat}
          (g : G) (hs : Vector.t G n) (us : Vector.t F n)
          (c : F) : @sigma_proto F G n 1 n.
        Proof.
          set (ushs := zip_with (fun u h => (u, h)) us hs).
          set (comm := Vector.map (fun '(u, h) => gop (g^u) (h^(opp c))) ushs).
          refine(comm; [c]; us).
        Defined.

        (** Verifier for the AND composition: by recursion on [n], checks the
            Schnorr equation [g ^ rᵢ = aᵢ · hᵢ ^ c] for the head component and
            recurses on the tails, passing the _same_ one-element challenge
            vector [c] down. Accepts trivially when [n = 0]. *)
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

        (** Real transcript distribution for a fixed challenge [c]: draw [n]
            independent uniform values from [lf] and run the honest
            prover. *)
        Definition generalised_and_schnorr_distribution
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
          (xs : Vector.t F n) (g : G)
          (c : F) : dist (@sigma_proto F G n 1 n) :=
          us <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_schnorr xs g us c).

        (** Simulated transcript distribution for a fixed challenge [c]: draw
            [n] independent uniform values from [lf] and run the
            simulator. *)
        Definition generalised_and_simulator_distribution
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
          (g : G) (hs : Vector.t G n)
          (c : F) : dist (@sigma_proto F G n 1 n) :=
          us <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_and_conversations_simulator g hs us c).

    End Def.

    (** *** Proofs *)
    Section Proofs.

        (** If the AND verifier accepts [(a; c; r)], then for every [f] the
            Schnorr transcript [(a_f; c; r_f)] is accepting for statement
            [h_f]. *)
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

        (** If the AND verifier rejects, some component Schnorr transcript
            is rejecting. *)
        Lemma generalised_and_accepting_conversations_correctness_forward_reject :
          forall (n : nat) (g : G) (hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          generalised_and_accepting_conversations g hs s = false ->
          (∃ (f : Fin.t n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec g (nth hs f)
                ([(nth a f)]; c; [(nth r f)]) = false
            end).
        Proof.
          induction n as [|n ihn].
          +
            intros * ha.
            cbn in ha.
            congruence.
          +
            intros * Ha.
            refine
            (match s as s'
            return s = s' -> _ with
            |(a; c; r) => fun Hb => _
            end eq_refl).
            rewrite Hb in Ha.
            destruct (vector_inv_S a) as (ha & ta & Hd).
            destruct (vector_inv_S c) as (hc & tc & He).
            destruct (vector_inv_S r) as (hr & tr & Hf).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            subst.
            cbn in Ha.
            eapply andb_false_iff in Ha.
            destruct Ha as [Ha | Ha].
            ++
              exists Fin.F1.
              exact Ha.
            ++
              destruct (ihn g hstl (ta; hc :: tc; tr) Ha) as (f & ihnn).
              exists (Fin.FS f).
              cbn.
              exact ihnn.
        Qed.

        (** If every component Schnorr transcript is accepting, the AND
            verifier accepts. *)
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

        (** If some component Schnorr transcript rejects, the AND verifier
            rejects. The [n = 0] case is discharged by an empty dependent
            match on [Fin.t 0]. *)
        Lemma generalised_and_accepting_conversations_correctness_backward_reject :
          forall (n : nat) (g : G) (hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          (∃ (f : Fin.t n),
          match s with
          | (a; c; r) =>
            @accepting_conversation F G gop gpow Gdec  g (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = false
          end) ->
          generalised_and_accepting_conversations g hs s = false.
        Proof.
          induction n as [|n ihn].
          +
            intros * (f & ha).
            refine
            match f as f' in Fin.t n return
              match n as n' return sigma_proto -> Type
              with
              | 0 => fun s' => generalised_and_accepting_conversations g hs s' = false
              | _ => fun _ => IDProp
              end s
            with end.
          +
            intros * (f & Ha).
            refine
            (match s as s'
            return s = s' -> _ with
            |(a; c; r) => fun Hb => _
            end eq_refl).
            rewrite Hb in Ha.
            destruct (vector_inv_S a) as (ha & ta & Hc).
            destruct (vector_inv_S c) as (hc & tc & Hd).
            destruct (vector_inv_S r) as (hr & tr & He).
            destruct (vector_inv_S hs) as (hsa & hstl & Hj).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            subst.
            ++
              cbn in Ha |- *.
              rewrite Ha; reflexivity.
            ++
              subst; cbn in Ha |- *.
              specialize (ihn g hstl (ta; hc :: tc; tr) (ex_intro _ hf Ha)).
              now rewrite ihn, andb_false_r.
        Qed.

        (** The AND verifier accepts iff every component is an accepting
            Schnorr transcript. *)
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

        (** The AND verifier rejects iff some component rejects. *)
        Lemma generalised_and_accepting_conversations_correctness_reject :
          forall (n : nat) (g : G) (hs : Vector.t G n) (s : @sigma_proto F G n 1 n),
          (∃ (f : Fin.t n),
          match s with
          | (a; c; r) =>
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; c; [(nth r f)]) = false
          end) <->
          generalised_and_accepting_conversations g hs s = false.
        Proof.
          intros *;
          split.
          +
            eapply generalised_and_accepting_conversations_correctness_backward_reject;
            try assumption.
          +
            eapply generalised_and_accepting_conversations_correctness_forward_reject;
            try assumption.
        Qed.

        (** From here on [G] is a vector space over [F]. *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub
            div opp inv G (@eq G) gid ginv gop gpow}.

        (** Registers [F] with the [field] tactic. *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        (** Componentwise completeness: if [g ^ xᵢ = hᵢ] for all [i], then
            for every index [f] the [f]-th component of the honest AND
            transcript is an accepting Schnorr transcript for [h_f]. Stated
            over generic [n] so that it can be proved by induction. *)
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

        (** Componentwise simulator completeness: the [f]-th component of a
            simulated AND transcript is always an accepting Schnorr
            transcript. *)
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

        (** Section context for the remaining results: [n] statements
            [hs] with witnesses [xs] and the relation [R : ∀ f, g ^ xs_f = hs_f].
            Results that do not need the witness are proved with
            [Proof using -(xs R)], so they do not depend on it. *)
        Context
          {n : nat}
          (xs : Vector.t F n)
          (g : G)
          (hs : Vector.t G n)
          (R : forall (f : Fin.t n),
            g^(Vector.nth xs f) = Vector.nth hs f).

        (** _Completeness._ For all randomness [us] and challenges [c], the
            honest AND transcript is accepted. *)
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

        (** _Simulator completeness._ Every simulated AND transcript is
            accepted; no witness or relation is needed. *)
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

        (** _Special soundness._ Two accepting AND transcripts
            [(a; c₁; r₁)] and [(a; c₂; r₂)] with the same announcement
            vector and different challenges [c₁ ≠ c₂] yield witnesses
            [ys] with [g ^ ys_f = hs_f] for every [f]. Does not use the
            section witness [xs].

            Proof by induction on [n]: the induction hypothesis gives the
            tail witnesses, and the head witness is
            [(r₁₀ - r₂₀) · (c₁ - c₂)⁻¹], verified with the same algebra as
            [special_soundness_extractor]. *)
        Lemma generalise_and_sigma_soundness :
          forall (a : Vector.t G n) (c₁ : Vector.t F 1)
          (r₁ : Vector.t F n) (c₂ : Vector.t F 1) (r₂ : Vector.t F n),
          generalised_and_accepting_conversations g hs (a; c₁; r₁) = true ->
          generalised_and_accepting_conversations g hs (a; c₂; r₂) = true ->
          c₁ <> c₂ ->
          (∃ ys : Vector.t F n, ∀ (f : Fin.t n),
            g^(nth ys f) = (nth hs f)).
        Proof using -(xs R).
          clear xs R.
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
            (* Head witness: Schnorr's extractor on the head component. *)
            exists (((rh₁ - rh₂) * inv (ch₁ - ch₂)) :: ys).
            intro f.
            destruct (fin_inv_S _ f) as [hf | (hf & Hl)].
            ++
              (* From the two verification equations derive
                 [g ^ (r₁ - r₂) = h ^ (c₁ - c₂)] and divide the exponent by
                 [c₁ - c₂]. *)
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
              (* Side condition [c₁ - c₂ ≠ 0], from [c₁ ≠ c₂] as
                 one-element vectors. *)
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
            (* Tail witnesses: from the induction hypothesis. *)
            ++
              specialize (IHn hf).
              rewrite Hk, Hl; cbn.
              exact IHn.
        Qed.

         (** [p / q] is local notation for the probability [p/q]. *)
         #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (** Every transcript in the support of the honest prover mapped over
            any randomness distribution is accepted. *)
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

        (** Uniform probabilities [1/m] are preserved by mapping the honest
            prover. *)
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

        (** Every element of the real AND distribution is accepting and has
            probability [1/|lf|ⁿ]. *)
        Lemma generalised_and_special_honest_verifier_schnorr_dist :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F) (a : sigma_proto) (b : prob),
          List.In (a, b)  (generalised_and_schnorr_distribution lf Hlfn xs g c) ->
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

        (** Every transcript in the support of the simulator mapped over any
            randomness distribution is accepted. *)
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

        (** Uniform probabilities [1/m] are preserved by mapping the
            simulator. *)
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

        (** Every element of the simulated AND distribution is accepting and
            has probability [1/|lf|ⁿ]. *)
        Lemma generalised_and_special_honest_verifier_simulator_dist :
          forall (lf : list F) (Hlfn : lf <> List.nil)
          (c : F)  (a : sigma_proto) (b : prob),
          List.In (a, b) (generalised_and_simulator_distribution lf Hlfn g hs c) ->
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

        (** _Weak special HVZK._ Projecting the real and simulated AND
            distributions to (acceptance bit, probability) yields the same
            list (every entry is [(true, 1/|lf|ⁿ)]). This compares
            verdicts only; the transcript-level statement is
            [generalised_and_special_honest_verifier_zkp_perm]. *)
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

        (** Shift lemma: if [g ^ xᵢ = hᵢ] for all [i], the honest transcript
            with randomness [us] equals the simulated transcript with
            randomness shifted componentwise, [uᵢ ↦ uᵢ + c · xᵢ]. Stated for
            arbitrary length [m] and vectors (not the section ones) so that
            it can be proved by induction. *)
        Lemma construct_and_shift (c : F) :
          forall (m : nat) (xs us : Vector.t F m) (hs : Vector.t G m),
          (forall f : Fin.t m, g ^ (Vector.nth xs f) = Vector.nth hs f) ->
          construct_and_conversations_schnorr xs g us c =
          construct_and_conversations_simulator g hs
            (vec_apply (Vector.map (fun x u => u + c * x) xs) us) c.
        Proof.
          induction m as [| m ih]; intros ys vs ks Rm.
          + rewrite (vector_inv_0 ys), (vector_inv_0 vs), (vector_inv_0 ks);
            reflexivity.
          + destruct (vector_inv_S ys) as (y & ys' & hy).
            destruct (vector_inv_S vs) as (v & vs' & hv).
            destruct (vector_inv_S ks) as (k & ks' & hk).
            subst.
            specialize (ih ys' vs' ks' (fun f => Rm (Fin.FS f))).
            unfold construct_and_conversations_schnorr,
              construct_and_conversations_simulator,
              construct_and_conversations_schnorr_commitment in *.
            cbn in *.
            inversion ih as [[ha hr]].
            f_equal.
            * f_equal;
              [apply schnorr_commitment_shift; symmetry; exact (Rm Fin.F1) | exact ha].
            * f_equal; exact hr.
        Qed.

        (** _Special HVZK, distribution equality._ If for every [x] the
            translation [u ↦ u + c · x] permutes [lf] as a multiset, then
            for the section statement and witnesses the real and simulated
            AND distributions are permutations of each other. Proof: the
            shift lemma, [repeat_uniform_perm] and [bind_ret_perm]. *)
        Theorem generalised_and_special_honest_verifier_zkp_perm :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          (forall x : F, Permutation (List.map (fun u => u + c * x) lf) lf) ->
          Permutation
            (@generalised_and_schnorr_distribution n lf Hlfn xs g c)
            (@generalised_and_simulator_distribution n lf Hlfn g hs c).
        Proof.
          intros * hp.
          change (Permutation
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n)
              (fun us => Ret (construct_and_conversations_schnorr xs g us c)))
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n)
              (fun us => Ret (construct_and_conversations_simulator g hs us c)))).
          eapply bind_ret_perm with
            (phi := vec_apply (Vector.map (fun x u => u + c * x) xs)).
          + apply repeat_uniform_perm; intros i.
            rewrite (nth_map _ _ i i eq_refl).
            apply hp.
          + intros us p _.
            apply construct_and_shift; exact R.
        Qed.

        (** _Special HVZK for an enumerated field._ If [lf] lists every
            element of [F] exactly once, the real and simulated AND
            transcript distributions are equal up to permutation. *)
        Theorem generalised_and_special_honest_verifier_zkp_enum :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.NoDup lf -> (forall y : F, List.In y lf) ->
          Permutation
            (@generalised_and_schnorr_distribution n lf Hlfn xs g c)
            (@generalised_and_simulator_distribution n lf Hlfn g hs c).
        Proof.
          intros * hnd hall.
          eapply generalised_and_special_honest_verifier_zkp_perm.
          intro x.
          eapply enumerates_perm_map with (psi := fun u => u - c * x);
          [exact hnd | exact hall | intros u; field | intros u; field].
        Qed.

    End Proofs.
  End And.
End DL.
