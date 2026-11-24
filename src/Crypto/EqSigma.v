(** * Equality of Discrete Logarithms: the EQ Sigma Protocol *)

(** This file formalises the generalised Sigma protocol for equality of
    discrete logarithms. Given public bases [gs = [g₁; …; gₖ]] and public
    values [hs = [h₁; …; hₖ]] with [k = 2 + n ≥ 2], the prover shows
    knowledge of a single witness [x] such that

    [[
      R(gs, hs; x)  :⇔  ∀ i, gᵢ ^ x = hᵢ
    ]]

    i.e. all the [hᵢ] share the same discrete logarithm with respect to their
    bases. For [k = 2] this is the Chaum–Pedersen protocol (Chaum and
    Pedersen, Crypto 1992), instantiated in [ChaumPedersen]; it is the core of
    proofs of correct decryption (see [DecProof]) and of correct key shares
    in [DistElgamal].

    The protocol runs [k] Schnorr protocols in lock-step with a single
    shared randomness [u] and a single challenge [c]:

    [[
      Prover → Verifier :  aᵢ = gᵢ ^ u          (for every i)
      Verifier → Prover :  c
      Prover → Verifier :  r  = u + c · x
      Verifier checks   :  gᵢ ^ r = aᵢ · hᵢ ^ c (for every i)
    ]]

    Transcripts are values of type [@sigma_proto F G (2 + n) 1 1] from
    [Sigma]: [2 + n] announcements, one challenge and one response. The
    verifier [generalised_eq_accepting_conversations] is the conjunction of
    the Schnorr verification equations [accepting_conversation] from [Sigma]
    at every index.

    Main results (all for an abstract field [F] and an [F]-vector space [G]
    with decidable equality):

    - completeness: [construct_eq_conversations_schnorr_completeness];
    - special soundness: [generalise_eq_sigma_soundness] extracts a common
      witness [y = (r₁ - r₂) / (c₁ - c₂)] from two accepting transcripts with
      the same announcement and distinct challenges;
    - special honest-verifier zero-knowledge, in two forms: the weak form
      [generalised_eq_special_honest_verifier_zkp] (both distributions put
      the same probability [1 / |lf|] on accepting transcripts), and the
      strong form [generalised_eq_special_honest_verifier_zkp_perm] /
      [generalised_eq_special_honest_verifier_zkp_enum], which shows that
      the real and simulated transcript distributions are equal as
      multisets (a permutation of each other) whenever the randomness
      list [lf] enumerates the field.

    Distributions are finite lists of (value, probability) pairs built with
    the [dist] monad of [Probability.Distr]; the randomness is drawn by
    [uniform_with_replacement lf Hlfn] from a non-empty list [lf]. *)
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

(** ** Parameters *)
Section DL.
  (** The scalar field [F] with its operations and decidable equality
      [Fdec]. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] with identity [gid], inverse [ginv], operation [gop],
      scalar action [gpow] and decidable equality [Gdec]. The vector-space
      laws are only assumed later, in the proofs section. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** [(a; c; r)] builds the transcript with announcements [a], challenges
      [c] and responses [r]. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** The EQ protocol *)
  Section EQ.

    (** *** Prover, simulator, verifier and distributions *)
    Section Def.

      (** The prover’s announcement [map (fun g => g ^ u) gs]: one Schnorr
          commitment per base, all with the same randomness [u]. Exposed
          separately so that Fiat–Shamir variants can hash it. *)
      Definition construct_eq_conversations_schnorr_commitment
        {n : nat} (gs : Vector.t G (2 + n)) (u : F) : Vector.t G (2 + n) :=
        Vector.map (fun g => gpow g u) gs.

      (** Honest prover: [construct_eq_conversations_schnorr x gs u c] is the
          transcript [(gᵢ ^ u)ᵢ; [c]; [u + c · x]] for witness [x],
          randomness [u] and challenge [c]. *)
      Definition construct_eq_conversations_schnorr :
        forall {n : nat},
        F -> Vector.t G (2 + n) -> F  ->
        F -> @sigma_proto F G (2 + n) 1 1.
      Proof.
        intros n x gs u c.
        remember (construct_eq_conversations_schnorr_commitment gs u)
        as commitment.
        exact (commitment; [c]; [u + c * x]).
      Defined.

      (** Honest-verifier simulator: given the statement [gs], [hs], a
          random response [u] and challenge [c], it produces announcements
          [aᵢ = gᵢ ^ u · hᵢ ^ (-c)] so that every verification equation holds
          by construction. It does not use any witness. *)
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

      (** Verifier: [generalised_eq_accepting_conversations gs hs (a; c; r)]
          returns [true] iff for every index [i] the Schnorr equation
          [gᵢ ^ r = aᵢ · hᵢ ^ c] holds (checked by [accepting_conversation]).
          Defined by recursion on [n], peeling off one base at a time; the
          base case [n = 0] handles two bases. *)
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
        (* Base case: exactly two bases, two Schnorr checks. *)
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
        (* Recursive case: check the head, recurse on the tails. *)
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

      (** The distribution of honest transcripts for challenge [c]: draw [u]
          uniformly from [lf] and run the honest prover. *)
      Definition generalised_eq_schnorr_distribution
        {n : nat} (lf : list F)  (Hlfn : lf <> List.nil) (x : F)
        (gs : Vector.t G (2 + n)) (c : F) : dist (@sigma_proto F G (2 + n) 1 1) :=
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (construct_eq_conversations_schnorr x gs u c).

      (** The distribution of simulated transcripts for challenge [c]: draw
          the response uniformly from [lf] and run the simulator. *)
      Definition generalised_eq_simulator_distribution
        {n : nat} (lf : list F)
        (Hlfn : lf <> List.nil) (gs hs : Vector.t G (2 + n))
        (c : F) : dist (@sigma_proto F G (2 + n) 1 1) :=
        r <- uniform_with_replacement lf Hlfn ;;
        Ret (construct_eq_conversations_simulator gs hs r c).

    End Def.

    (** *** Proofs *)

    (** The first group of lemmas characterises the boolean verifier as the
        index-wise conjunction of Schnorr checks, in both the accepting and
        the rejecting direction. They need no algebraic assumptions. *)
    Section Proofs.

        (** If the EQ verifier accepts, then every component Schnorr
            transcript [([aᵢ]; c; r)] for [(gᵢ, hᵢ)] accepts. By induction on
            [n]. *)
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

        (** If the EQ verifier rejects, then some index [f] has a rejecting
            component Schnorr transcript. *)
        Lemma generalised_eq_accepting_conversations_correctness_forward_reject :
          forall (n : nat) (gs hs : Vector.t G (2 + n))
          (s : @sigma_proto F G (2 + n) 1 1),
          generalised_eq_accepting_conversations gs hs s = false ->
          (∃ f : Fin.t (2 + n),
          match s with
          | (a; c; r) =>
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
              ([(nth a f)]; c; r) = false
          end).
        Proof.
          induction n as [|n ihn].
          +
            intros * ha.
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
            subst. cbn in ha.
            rewrite andb_false_iff in ha.
            destruct ha as [ha | ha].
            exists Fin.F1. cbn. exact ha.
            exists (Fin.FS Fin.F1). cbn.
            exact ha.
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              |(a; c; r) => fun hb => _
              end eq_refl).
            destruct (vector_inv_S gs) as (gh & gstl & hc).
            destruct (vector_inv_S hs) as (hh & hstl & hd).
            destruct (vector_inv_S a) as (ah & atl & he).
            subst.
            cbn in ha.
            rewrite andb_false_iff in ha.
            destruct ha as [ha | ha].
            exists Fin.F1. cbn. exact ha.
            destruct (ihn gstl hstl (atl; c; r) ha) as (f & ihnn).
            exists (Fin.FS f).
            exact ihnn.
        Qed.

        (** Converse of [generalised_eq_accepting_conversations_correctness_forward]:
            if every component accepts, the EQ verifier accepts. *)
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

        (** Converse of
            [generalised_eq_accepting_conversations_correctness_forward_reject]:
            a single rejecting component makes the EQ verifier reject. *)
         Lemma generalised_eq_accepting_conversations_correctness_backward_reject :
          forall (n : nat) (gs hs : Vector.t G (2 + n))
          (s : @sigma_proto F G (2 + n) 1 1),
          (∃ f : Fin.t (2 + n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
                ([(nth a f)]; c; r) = false
            end) -> generalised_eq_accepting_conversations gs hs s = false.
        Proof.
          induction n as [|n ihn].
          +
            intros * (f & ha).
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
            rewrite Hb in ha. cbn in ha.
            subst; cbn in ha |- *.
            ++
              rewrite ha. reflexivity.
            ++
              destruct (fin_inv_S _ hf) as [hff | (hff & Hjj)];
              [|inversion hff]. subst.
              cbn in ha |- *.
              rewrite ha.
              eapply andb_false_r.
          +
            intros * (f & ha).
            refine
              (match s as s' return s = s' -> _
              with
              |(a; c; r) => fun hb => _
              end eq_refl).
            rewrite hb in ha.
            destruct (vector_inv_S gs) as (gh & gstl & hc).
            destruct (vector_inv_S hs) as (hh & hstl & hd).
            destruct (vector_inv_S a) as (ah & atl & he).
            destruct (fin_inv_S _ f) as [hf | (hf & hj)].
            subst; cbn in ha |- *.
            ++
              rewrite ha; reflexivity.
            ++
              subst.
              specialize (ihn gstl hstl (atl; c; r) (ex_intro _ hf ha)).
              cbn in |- *.
              rewrite ihn.
              eapply andb_false_r.
        Qed.

        (** The EQ verifier accepts iff every component Schnorr transcript
            accepts. *)
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

        (** The EQ verifier rejects iff some component Schnorr transcript
            rejects. *)
        Lemma generalised_eq_accepting_conversations_correctness_reject :
          forall (n : nat) (gs hs : Vector.t G (2 + n))
          (s : @sigma_proto F G (2 + n) 1 1),
          (∃ f : Fin.t (2 + n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f)
                ([(nth a f)]; c; r) = false
            end) <-> generalised_eq_accepting_conversations gs hs s = false.
        Proof.
          intros *;
          split.
          +
            eapply generalised_eq_accepting_conversations_correctness_backward_reject;
            try assumption.
          +
            eapply generalised_eq_accepting_conversations_correctness_forward_reject;
            try assumption.
        Qed.

        (** From here on [G] is assumed to be an [F]-vector space (a
            prime-order group with scalars in [F]), and the [field] tactic is
            registered for [F]. *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub
            div opp inv G (@eq G) gid ginv gop gpow}.

        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        (** Completeness: if [x] is a common discrete logarithm,
            [gᵢ ^ x = hᵢ] for all [i], then the honest transcript
            [construct_eq_conversations_schnorr x gs u c] is accepted for
            every [u] and [c]. By induction on [n], reducing each index to
            [schnorr_completeness] from [Sigma]. *)
        Lemma construct_eq_conversations_schnorr_completeness
          {n : nat}
          (x : F)
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

        (** Simulator completeness: every simulated transcript is accepted,
            for every statement [gs], [hs] (no relation between them is
            needed). Reduces to [simulator_completeness] from [Sigma]. *)
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

      (** Special soundness: given two accepting transcripts
          [(a; [c₁]; [r₁])] and [(a; [c₂]; [r₂])] with the same announcement
          and distinct challenges [c₁ ≠ c₂], there is a single [y] with
          [gᵢ ^ y = hᵢ] for every [i]. The extracted witness is
          [y = (r₁ - r₂) · (c₁ - c₂)⁻¹].

          Proof idea: from [gᵢ ^ r₁ = aᵢ · hᵢ ^ c₁] and
          [gᵢ ^ r₂ = aᵢ · hᵢ ^ c₂], dividing gives
          [gᵢ ^ (r₁ - r₂) = hᵢ ^ (c₁ - c₂)]; raising both sides to
          [(c₁ - c₂)⁻¹] yields the claim. Because the extracted [y] is a
          fixed expression in the challenges and responses, it is the same
          for every index. *)
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
        (* Turn both boolean verifier results into per-index Schnorr
           equations. *)
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
        (* Case split on [n]. In both cases the witness is
           [(r₁ - r₂) · (c₁ - c₂)⁻¹]. The case [n = 0] treats the two indices
           by explicit algebra; the case [n = S n'] does the head index by
           hand and delegates other indices to [special_soundness_berry_gen]. *)
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
            (* Combine the two verification equations by multiplying the
               first by the inverse of the second, cancelling the
               announcement [ah]. *)
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
            (* Raise both sides to [(c₁ - c₂)⁻¹]; the remaining side
               condition [c₁ - c₂ ≠ 0] follows from [c₁ ≠ c₂]. *)
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
          (* Second index: the same algebra. *)
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
            (* Remaining indices: use the Schnorr extractor from [Sigma],
               which also returns that its witness equals
               [(r₁ - r₂) · (c₁ - c₂)⁻¹]. *)
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

      (** [p / q] denotes the rational probability [p / q] with a natural
          denominator (local to this file). *)
      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      (** Every transcript in the support of [Bind l (fun u => Ret (honest
          transcript))] is accepted when the witness relation holds, for any
          finite distribution [l] of randomness. By induction on [l]. *)
      Lemma generalised_eq_schnorr_distribution_transcript_generic
        {n : nat}
        (x : F)
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

      (** If every entry of the randomness distribution [l] has probability
          [1 / m], then so does every entry of the induced honest
          transcript distribution. *)
      Lemma generalised_eq_schnorr_distribution_probability_generic
        {n : nat}
        (x : F)
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

      (** Every entry of the honest transcript distribution
          [generalised_eq_schnorr_distribution lf Hlfn x gs c] is accepting
          and has probability [1 / |lf|]. *)
      Lemma generalised_eq_special_honest_verifier_schnorr_dist
        {n : nat}
        (x : F)
        (gs hs : Vector.t G (2 + n))
        (R : forall (f : Fin.t (2 + n)),
          (Vector.nth gs f)^x = Vector.nth hs f) :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (c : F) a b,
        List.In (a, b)
          (generalised_eq_schnorr_distribution lf Hlfn x gs c) ->
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

      (** Simulator analogue of
          [generalised_eq_schnorr_distribution_transcript_generic]: every
          transcript in the support of the simulated distribution is
          accepting (no witness needed). *)
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

      (** Simulator analogue of
          [generalised_eq_schnorr_distribution_probability_generic]. *)
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

      (** Every entry of the simulated distribution
          [generalised_eq_simulator_distribution lf Hlfn gs hs c] is accepting
          and has probability [1 / |lf|]. *)
      Lemma generalised_eq_special_honest_verifier_simulator_dist
        {n : nat}
        (gs hs : Vector.t G (2 + n)) :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (c : F) a b,
        List.In (a, b)
          (generalised_eq_simulator_distribution lf Hlfn gs hs c) ->
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

      (** Special honest-verifier zero-knowledge, weak form: after mapping
          each transcript to the verifier’s verdict, the honest and simulated
          distributions are equal as lists. Both lists have length [|lf|]
          and every entry is [(true, 1 / |lf|)]. This only compares
          verdicts and probabilities, not transcripts; the strong form is
          [generalised_eq_special_honest_verifier_zkp_perm]. *)
      Lemma generalised_eq_special_honest_verifier_zkp
        {n : nat}
        (x : F)
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

      (** Simulator transcripts are accepting for any statement, including
          statements outside the language (where no common discrete
          logarithm exists). This is why the simulator can be used in the
          OR-composition. *)
      Lemma generalised_eq_special_honest_verifier_zkp_not_in_lang
        {n : nat} (gs hs : Vector.t G (2 + n)) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F) (a : sigma_proto) b,
        List.In (a, b) (generalised_eq_simulator_distribution lf Hlfn gs hs c) ->
        generalised_eq_accepting_conversations gs hs a = true.
      Proof.
        intros * ha.
        eapply generalised_eq_special_honest_verifier_simulator_dist.
        exact ha.
      Qed.

      (** Commitment shift: if [gᵢ ^ x = hᵢ] for all [i], then the honest
          announcement with randomness [u] equals the simulated
          announcement with response [u + c · x], index by index:
          [gᵢ ^ u = gᵢ ^ (u + c · x) · hᵢ ^ (-c)]. Proved for vectors of any
          length [m] from [schnorr_commitment_shift]. *)
      Lemma eq_commitment_shift (x : F) :
        forall (m : nat) (gs hs : Vector.t G m) (u c : F),
        (forall f : Fin.t m, (Vector.nth gs f) ^ x = Vector.nth hs f) ->
        Vector.map (fun g => gpow g u) gs =
        Vector.map (fun '(g, h) => gop (gpow g (u + c * x)) (gpow h (opp c)))
          (zip_with (fun g h => (g, h)) gs hs).
      Proof.
        induction m as [| m ih]; intros gs hs u c R.
        + rewrite (vector_inv_0 gs), (vector_inv_0 hs); reflexivity.
        + destruct (vector_inv_S gs) as (g & gs' & hg).
          destruct (vector_inv_S hs) as (h & hs' & hh).
          subst; cbn; f_equal.
          * apply schnorr_commitment_shift.
            symmetry; exact (R Fin.F1).
          * apply ih. intros f; exact (R (Fin.FS f)).
      Qed.

      (** Transcript shift: the honest transcript for randomness [u] is
          exactly the simulated transcript for response [u + c · x]. *)
      Lemma construct_eq_shift {n : nat} (x : F) (gs hs : Vector.t G (2 + n))
        (R : forall f : Fin.t (2 + n), (Vector.nth gs f) ^ x = Vector.nth hs f) :
        forall (u c : F),
        construct_eq_conversations_schnorr x gs u c =
        construct_eq_conversations_simulator gs hs (u + c * x) c.
      Proof.
        intros *.
        unfold construct_eq_conversations_schnorr,
          construct_eq_conversations_simulator,
          construct_eq_conversations_schnorr_commitment; cbn.
        f_equal.
        apply eq_commitment_shift; exact R.
      Qed.

      (** Special honest-verifier zero-knowledge, strong form: if the map
          [u ↦ u + c · x] permutes the randomness list [lf], then the honest
          and simulated transcript distributions are permutations of each
          other, i.e. identical as distributions. Proof: rewrite both as
          [Bind] over the uniform distribution and apply [bind_ret_perm]
          with the shift [u ↦ u + c · x], using [construct_eq_shift]. *)
      Theorem generalised_eq_special_honest_verifier_zkp_perm {n : nat} (x : F)
        (gs hs : Vector.t G (2 + n))
        (R : forall f : Fin.t (2 + n), (Vector.nth gs f) ^ x = Vector.nth hs f) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        Permutation (List.map (fun u => u + c * x) lf) lf ->
        Permutation
          (@generalised_eq_schnorr_distribution n lf Hlfn x gs c)
          (@generalised_eq_simulator_distribution n lf Hlfn gs hs c).
      Proof.
        intros * hp.
        change (Permutation
          (Bind (uniform_with_replacement lf Hlfn)
            (fun u => Ret (construct_eq_conversations_schnorr x gs u c)))
          (Bind (uniform_with_replacement lf Hlfn)
            (fun u => Ret (construct_eq_conversations_simulator gs hs u c)))).
        eapply bind_ret_perm with (phi := fun u => u + c * x).
        + apply uniform_perm; exact hp.
        + intros u p _. apply construct_eq_shift; exact R.
      Qed.

      (** Special honest-verifier zero-knowledge when [lf] enumerates the
          field without duplicates: then [u ↦ u + c · x] is a bijection of
          [lf] (with inverse [u ↦ u - c · x]), so
          [generalised_eq_special_honest_verifier_zkp_perm] applies. *)
      Theorem generalised_eq_special_honest_verifier_zkp_enum {n : nat} (x : F)
        (gs hs : Vector.t G (2 + n))
        (R : forall f : Fin.t (2 + n), (Vector.nth gs f) ^ x = Vector.nth hs f) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.NoDup lf -> (forall y : F, List.In y lf) ->
        Permutation
          (@generalised_eq_schnorr_distribution n lf Hlfn x gs c)
          (@generalised_eq_simulator_distribution n lf Hlfn gs hs c).
      Proof.
        intros * hnd hall.
        eapply generalised_eq_special_honest_verifier_zkp_perm; [exact R |].
        eapply enumerates_perm_map with (psi := fun u => u - c * x);
        [exact hnd | exact hall | intros u; field | intros u; field].
      Qed.

    End Proofs.
  End EQ.
End DL.
