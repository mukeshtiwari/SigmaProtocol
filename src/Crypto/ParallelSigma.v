(** * Parallel composition of Schnorr's protocol *)

(** This file runs [n] independent copies of Schnorr's protocol for the
    _same_ statement [h = g ^ x] side by side, with an independent
    challenge per copy. Parallel repetition is the standard way to shrink
    the knowledge error of a Sigma protocol whose challenge space is small:
    a cheating prover must now answer a whole challenge vector.

    _Protocol._ With randomness [us = (u₁, …, uₙ)] and challenge vector
    [cs = (c₁, …, cₙ)], the prover sends [(g ^ u₁, …, g ^ uₙ)] and responds
    with [(u₁ + c₁ · x, …, uₙ + cₙ · x)]. The verifier
    [generalised_parallel_accepting_conversations] checks the Schnorr
    equation [g ^ rᵢ = aᵢ · h ^ cᵢ] for every coordinate. Transcripts use
    the generic record [sigma_proto] from [Sigma] with all three
    dimensions equal to [n].

    _Results._

    - The vector verifier accepts iff every coordinate is an accepting
      Schnorr transcript, and rejects iff some coordinate rejects
      ([generalised_parallel_accepting_conversations_correctness] and its
      [_reject] counterpart).
    - Completeness of the prover and of the simulator.
    - Special soundness [generalise_parallel_sigma_soundness]: two accepting
      transcripts with the same announcement vector and different challenge
      vectors yield a witness. Only the existence of a witness is
      concluded; the extractor is Schnorr's, applied at a coordinate where
      the challenges differ.
    - Special HVZK, in the weak (acceptance-bit) form
      [generalised_parallel_special_honest_verifier_zkp] and as equality of
      distributions up to permutation
      ([generalised_parallel_special_honest_verifier_zkp_perm] and
      [generalised_parallel_special_honest_verifier_zkp_enum]).

    Used by [Examples/ParaSigmaIns.v], which instantiates the protocol and
    is extracted to OCaml. *)
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

(** ** Parallel Schnorr

    Same abstract field [F] and group [G] as in [Sigma]; the vector-space
    axioms are assumed only in the [Proofs] section. *)

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

  Section Parallel.

    (** *** Definitions *)
    Section Def.

      (** Announcement vector [(g ^ u₁, …, g ^ uₙ)] for randomness [us]. *)
      Definition construct_parallel_conversations_schnorr_commitment {n : nat}
        (g : G) (us : Vector.t F n) : Vector.t G n := Vector.map (fun u => g^u) us.

      (** Honest prover for the parallel protocol: announcement
          [(g ^ uᵢ)ᵢ], challenge vector [cs], responses [(uᵢ + cᵢ · x)ᵢ].
          Defined in proof mode but transparent ([Defined]), so it computes
          and extracts. *)
      Definition construct_parallel_conversations_schnorr
         {n : nat} (x : F) (g : G) (us : Vector.t F n) (cs : Vector.t F n) :
        @sigma_proto F G n n n.
      Proof.
        set (com := construct_parallel_conversations_schnorr_commitment g us).
        set (uscs := zip_with (fun ui ci => (ui, ci)) us cs).
        set (res := Vector.map (fun '(ui, ci) => ui + ci * x) uscs).
        exact (com; cs; res).
      Defined.

      (** Simulator: for randomness [us] and challenges [cs] it outputs the
          announcement [(g ^ uᵢ · h ^ (-cᵢ))ᵢ], the challenges [cs] and the
          responses [us]. Uses no witness. *)
      Definition construct_parallel_conversations_simulator {n : nat}
        (g h : G) (us : Vector.t F n) (cs : Vector.t F n) :  @sigma_proto F G n n n.
      Proof.
        set (uscs := zip_with (fun ui ci => (ui, ci)) us cs).
        set(com := Vector.map (fun '(ui, ci) =>
          gop (g^ui) (h^(opp ci))) uscs).
        exact (com; cs; us).
      Defined.

      (** Verifier for the parallel protocol: by recursion on [n], it checks
          the Schnorr equation [g ^ rᵢ = aᵢ · h ^ cᵢ] on the head
          coordinate with [accepting_conversation] and conjoins the result
          on the tail. Accepts the empty transcript when [n = 0]. *)
      Definition generalised_parallel_accepting_conversations :
        forall {n : nat},
        G -> G -> @sigma_proto F G n n n -> bool.
      Proof.
        refine(fix Fn n {struct n} :=
          match n with
          | 0 => fun _ _ p => true
          | S n' => fun g h p =>
            match p with
            | (a; c ; r) => _
            end
          end).
        destruct (vector_inv_S a) as (ah & atl & _).
        destruct (vector_inv_S c) as (ch & ctl & _).
        destruct (vector_inv_S r) as (rh & rtl & _).
        exact ((@accepting_conversation F G gop gpow Gdec g h ([ah]; [ch]; [rh])) &&
          (Fn _ g h (atl; ctl; rtl))).
      Defined.

      (** Real transcript distribution for a fixed challenge vector [cs]:
          draw [n] independent uniform values from [lf] (via
          [repeat_dist_ntimes_vector]) and run the honest prover. *)
      Definition generalised_parallel_schnorr_distribution
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
        (x : F) (g : G) (cs : Vector.t F n) : dist (@sigma_proto F G n n n) :=
        us <- repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) n ;;
        Ret (construct_parallel_conversations_schnorr x g us cs).

      (** Simulated transcript distribution for a fixed challenge vector
          [cs]: draw [n] independent uniform values from [lf] and run the
          simulator. *)
      Definition generalised_parallel_simulator_distribution
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
        (g h : G) (cs : Vector.t F n) : dist (@sigma_proto F G n n n) :=
        us <- repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) n ;;
        Ret (construct_parallel_conversations_simulator g h us cs).

    End Def.

    (** *** Proofs *)
    Section Proofs.

        (** If the parallel verifier accepts [(a; c; r)], then for every
            index [f] the [f]-th coordinate [(a_f; c_f; r_f)] is an accepting
            Schnorr transcript. By induction on [n] with [Fin.t] case
            analysis. *)
        Lemma generalised_parallel_accepting_conversations_correctness_forward :
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          @generalised_parallel_accepting_conversations n g h s = true ->
          ∀ (f : Fin.t n),
          match s with
          | (a; c; r) =>
            @accepting_conversation F G gop gpow Gdec g h
              ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true
          end.
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
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            subst; simpl.
            eapply andb_true_iff in Ha.
            destruct Ha as (Ha & _).
            rewrite Ha; reflexivity.
            subst ; simpl.
            eapply andb_true_iff in Ha.
            destruct Ha as (_ & Ha).
            exact (IHn _ _ _ Ha hf).
        Qed.

        (** Converse: if every coordinate is an accepting Schnorr
            transcript, the parallel verifier accepts. *)
        Lemma generalised_parallel_accepting_conversations_correctness_backward :
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          (forall (f : Fin.t n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec g h
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true
            end) ->
          @generalised_parallel_accepting_conversations n g h s = true.
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
            destruct (vector_inv_S r) as (hr & tr & He);
            subst.
            eapply andb_true_iff; split;
            [exact (Ha Fin.F1) |
            eapply IHn;
            intros fz;
            exact (Ha (Fin.FS fz))].
        Qed.

        (** The parallel verifier accepts iff every coordinate is an
            accepting Schnorr transcript. *)
        Lemma generalised_parallel_accepting_conversations_correctness :
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          (forall (f : Fin.t n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec g h
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true
            end) <->
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof.
          split;
          [apply generalised_parallel_accepting_conversations_correctness_backward |
          apply generalised_parallel_accepting_conversations_correctness_forward].
        Qed.

        (** If the parallel verifier rejects, some coordinate is a
            rejecting Schnorr transcript. *)
        Lemma generalised_parallel_accepting_conversations_correctness_forward_reject :
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          @generalised_parallel_accepting_conversations n g h s = false ->
          ∃ (f : Fin.t n),
          match s with
          | (a; c; r) =>
            @accepting_conversation F G gop gpow Gdec g h
              ([(nth a f)]; [(nth c f)]; [(nth r f)]) = false
          end.
        Proof.
          induction n as [|n ihn].
          +
            intros * ha *.
            unfold generalised_parallel_accepting_conversations in ha;
            congruence.
          +
            intros * ha *.
            refine
            (match s as s'
            return s = s' -> _ with
            |(a; c; r) => fun hc => _
            end eq_refl).
            rewrite hc in ha.
            destruct (vector_inv_S a) as (hda & tla & hb).
            destruct (vector_inv_S c) as (hdc & tlc & hd).
            destruct (vector_inv_S r) as (hdr & tlr & he).
            subst. cbn in ha.
            destruct (Gdec (g ^ hdr) (gop hda (h ^ hdc))) as [hg | hg].
            ++

              destruct (ihn g h (tla; tlc; tlr) ha) as (f' & hi).
              exists (Fin.FS f'); cbn. exact hi.
            ++
              exists Fin.F1; cbn.
              eapply dec_false.
              exact hg.
        Qed.

        (** If some coordinate rejects, the parallel verifier rejects. *)
        Lemma generalised_parallel_accepting_conversations_correctness_backward_reject :
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          (∃ (f : Fin.t n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec g h
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = false
            end) ->
          @generalised_parallel_accepting_conversations n g h s = false.
        Proof.
          induction n as [|n ihn].
          +
            intros * (f & ha).
            refine match f with end.
          +
            intros * (f & ha).
            refine
            (match s as s'
            return s = s' -> _ with
            |(a; c; r) => fun hc => _
            end eq_refl).
            rewrite hc in ha.
            destruct (vector_inv_S a) as (hda & tla & hb).
            destruct (vector_inv_S c) as (hdc & tlc & hd).
            destruct (vector_inv_S r) as (hdr & tlr & he).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & hf)].
            ++
              subst; cbn in ha |- *.
              rewrite dec_false in ha.
              eapply andb_false_iff; left.
              rewrite dec_false; exact ha.
            ++
              subst; cbn in ha |- *.
              rewrite dec_false in ha.
              eapply andb_false_iff; right.
              eapply ihn.
              exists f'. cbn. rewrite dec_false.
              exact ha.
        Qed.

        (** The parallel verifier rejects iff some coordinate rejects. *)
        Lemma generalised_parallel_accepting_conversations_correctness_reject :
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          (∃ (f : Fin.t n),
            match s with
            | (a; c; r) =>
              @accepting_conversation F G gop gpow Gdec g h
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = false
            end) <->
          @generalised_parallel_accepting_conversations n g h s = false.
        Proof.
          intros *; split; intro ha;
          [eapply  generalised_parallel_accepting_conversations_correctness_backward_reject |
          eapply  generalised_parallel_accepting_conversations_correctness_forward_reject];
          assumption.
        Qed.

        (** From here on [G] is a vector space over [F]. *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub
            div opp inv G (@eq G) gid ginv gop gpow}.

        (** Registers [F] with the [field] tactic. *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        (** _Completeness._ If [h = g ^ x], the honest parallel transcript
            is accepting for every randomness vector [us] and challenge
            vector [cs]. Reduces, coordinatewise, to
            [schnorr_completeness]. *)
        Lemma construct_parallel_conversations_schnorr_completeness (x : F) (g h : G) (R : h = g^x) :
          forall (n : nat) (us cs : Vector.t F n),
          generalised_parallel_accepting_conversations g h
            (construct_parallel_conversations_schnorr x g us cs) = true.
        Proof.
          intros *.
          eapply generalised_parallel_accepting_conversations_correctness.
          unfold construct_parallel_conversations_schnorr.
          generalize dependent n.
          induction n as [|n IHn].
          +
            intros *.
            refine match f with end.
          +
            intros *.
            destruct (vector_inv_S us) as (hus & tus & Ha).
            destruct (vector_inv_S cs) as (hcs & tcs & Hb).
            destruct (fin_inv_S _ f) as [hd | (hd & Hf)].
            ++
              subst; cbn.
              now eapply schnorr_completeness.
            ++
              subst; cbn.
              eapply IHn.
        Qed.

        (** _Simulator completeness._ For all [g], [h], [us], [cs], the
            simulated parallel transcript is accepting (no relation
            assumed). Coordinatewise [simulator_completeness]. *)
        Lemma construct_parallel_conversations_simulator_completeness (g h : G) :
          forall (n : nat) (us cs : Vector.t F n),
          generalised_parallel_accepting_conversations g h
            (construct_parallel_conversations_simulator g h us cs) = true.
        Proof.
          intros *.
          eapply generalised_parallel_accepting_conversations_correctness.
          unfold construct_parallel_conversations_schnorr.
          generalize dependent n.
          induction n as [|n IHn].
          +
            intros *.
            refine match f with end.
          +
            intros *.
            destruct (vector_inv_S us) as (hus & tus & Ha).
            destruct (vector_inv_S cs) as (hcs & tcs & Hb).
            destruct (fin_inv_S _ f) as [hd | (hd & Hf)].
            ++
              subst; cbn.
              now eapply simulator_completeness.
            ++
              subst; cbn.
              eapply IHn.
        Qed.

        (** Soundness workhorse, for [n + 1] copies: if two accepting
            parallel transcripts [s₁], [s₂] have equal announcement vectors
            (pointwise) and challenge vectors differing in some coordinate,
            then [∃ y, g ^ y = h]. By induction on [n]: if the challenges
            differ at the head, apply Schnorr's [special_soundness_berry]
            there; otherwise recurse on the tails. *)
        Lemma generalise_parallel_sigma_soundness_supplement (g h : G) :
          ∀ (n : nat) (s₁ s₂ : @sigma_proto F G (S n) (S n) (S n)),
          (match s₁, s₂ with
          | (a₁; c₁; _), (a₂; c₂; _) =>
            two_challenge_vectors_same_everyelem a₁ a₂ ->
            two_challenge_vectors_disjoint_someelem c₁ c₂ ->
            generalised_parallel_accepting_conversations g h s₁ = true ->
            generalised_parallel_accepting_conversations g h s₂ = true ->
            ∃ y : F, g^y = h
          end).
        Proof.
          (* Base case: a single coordinate, which must be the one where the
             challenges differ. *)
          induction n as [|n IHn].
          +
            intros ? ?.
            refine
            (match s₁ as s'
            return s₁ = s' -> _ with
            |(a₁; c₁; r₁) => fun Ha => _
            end eq_refl).
            refine
            (match s₂ as s'
            return s₂ = s' -> _ with
            |(a₂; c₂; r₂) => fun Hb => _
            end eq_refl).
            intros Hc Hd He Hf.
            unfold two_challenge_vectors_same_everyelem in Hc.
            destruct Hd as [f Hd].
            destruct (vector_inv_S a₁) as (ha₁ & ta₁ & Hg).
            destruct (vector_inv_S c₁) as (hc₁ & tc₁ & Hh).
            destruct (vector_inv_S r₁) as (hr₁ & tr₁ & Hi).
            rewrite Hg, Hh, Hi in He;
            cbn in He.
            destruct (vector_inv_S a₂) as (ha₂ & ta₂ & Hj).
            destruct (vector_inv_S c₂) as (hc₂ & tc₂ & Hk).
            destruct (vector_inv_S r₂) as (hr₂ & tr₂ & Hl).
            rewrite Hj, Hk, Hl in Hf;
            cbn in Hf.
            eapply special_soundness_berry with
            (a := ha₁) (c₁ := hc₁) (r₁ := hr₁)
            (c₂ := hc₂) (r₂ := hr₂).

            rewrite Hh, Hk in Hd.
            destruct (fin_inv_S _ f) as [hf | (hf & Hm)];
            [rewrite hf in Hd;
            cbn in Hd; exact Hd |
            inversion hf].
            apply andb_true_iff in He;
            cbn; exact (proj1 He).
            apply andb_true_iff in Hf;
            cbn.
            rewrite Hg, Hj in Hc.
            specialize (Hc f).
            destruct (fin_inv_S _ f) as [hf | (hf & Hm)].
            rewrite hf in Hc;
            cbn in Hc; rewrite Hc.
            exact (proj1 Hf).
            inversion hf.
          (* Inductive case: split on whether the differing coordinate is
             the head. *)
          +
            intros ? ?.
            refine
            (match s₁ as s'
            return s₁ = s' -> _ with
            |(a₁; c₁; r₁) => fun Ha => _
            end eq_refl).
            refine
            (match s₂ as s'
            return s₂ = s' -> _ with
            |(a₂; c₂; r₂) => fun Hb => _
            end eq_refl).
            intros Hc Hd He Hf.
            remember (S n) as sn.
            destruct (vector_inv_S a₁) as (ha₁ & ta₁ & Hg).
            destruct (vector_inv_S c₁) as (hc₁ & tc₁ & Hh).
            destruct (vector_inv_S r₁) as (hr₁ & tr₁ & Hi).
            destruct (vector_inv_S a₂) as (ha₂ & ta₂ & Hj).
            destruct (vector_inv_S c₂) as (hc₂ & tc₂ & Hk).
            destruct (vector_inv_S r₂) as (hr₂ & tr₂ & Hl).
            rewrite Hg, Hj in Hc.
            rewrite Hh, Hk in Hd.
            rewrite Hg, Hh, Hi in He.
            rewrite Hj, Hk, Hl in Hf.
            cbn in He, Hf.
            apply andb_true_iff in He, Hf.
            destruct He as [Hel Her].
            destruct Hf as [Hfl Hfr].
            destruct Hd as [f Hm].
            (* Differing coordinate is the head: Schnorr extraction. *)
            destruct (fin_inv_S _ f) as [hf | (hf & Hn)].
            rewrite hf in Hm;
            cbn in Hm.
            eapply special_soundness_berry with
            (a := ha₁) (c₁ := hc₁) (r₁ := hr₁)
            (c₂ := hc₂) (r₂ := hr₂).
            exact Hm.
            exact Hel.
            cbn.
            pose proof (Hc f) as Hn;
            rewrite hf in Hn;
            cbn in Hn;
            rewrite Hn;
            exact Hfl.
            (* Differing coordinate is in the tail: apply the induction
               hypothesis to the tails. *)
            specialize (IHn (ta₁; tc₁; tr₁)
            (ta₂; tc₂; tr₂));
            cbn in IHn.
            assert (Ho : two_challenge_vectors_same_everyelem ta₁ ta₂).
            intro Ho;
            pose proof (Hc (Fin.FS Ho)) as Hp;
            cbn in Hp;
            exact Hp.
            assert (Hp : two_challenge_vectors_disjoint_someelem tc₁ tc₂).
            exists hf;
            rewrite Hn in Hm;
            cbn in Hm; exact Hm.
            eapply IHn;
            try assumption.
        Qed.

        (** _Special soundness._ For [1 + n] parallel copies, two accepting
            transcripts [(a; c₁; r₁)] and [(a; c₂; r₂)] with a common
            announcement vector and [c₁ ≠ c₂] (as vectors) imply
            [∃ y, g ^ y = h]. Note the challenge vectors need only differ
            in one coordinate. *)
        Lemma generalise_parallel_sigma_soundness (g h : G) :
          ∀ (n : nat) (a : Vector.t G (1 + n))
          (c₁ r₁ c₂ r₂ : Vector.t F (1 + n)),
          c₁ <> c₂ ->
          generalised_parallel_accepting_conversations g h (a; c₁; r₁) = true ->
          generalised_parallel_accepting_conversations g h (a; c₂; r₂) = true ->
          ∃ y : F, g^y = h.
        Proof.
          intros * Ha Hb Hc.
          exact (generalise_parallel_sigma_soundness_supplement g h n
            (a; c₁; r₁) (a; c₂; r₂)
            (vector_same_implies_same_everyelem _ a a eq_refl)
            (@vector_not_equal_implies_disjoint_someelem _ Fdec _ c₁ c₂ Ha)
            Hb Hc).
        Qed.

        (** [p / q] is local notation for the probability [p/q]. *)
        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (** Every transcript in the support of the honest prover mapped over
            any distribution [l] of randomness vectors is accepting, if
            [h = g ^ x]. *)
        Lemma generalised_parallel_schnorr_distribution_transcript_generic
          {n : nat} (x : F) (g h : G) (R : h = g^x) :
          forall (l : dist (Vector.t F n))
          (trans : sigma_proto) (pr : prob) (cs : Vector.t F n),
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_schnorr x g us cs))) →
          generalised_parallel_accepting_conversations g h trans = true.
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
              now eapply construct_parallel_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply construct_parallel_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (** Uniform probabilities [1/m] in the randomness distribution are
            preserved by mapping the honest prover. *)
        Lemma generalised_parallel_schnorr_distribution_probability_generic {n : nat}
          (x : F) (g : G) : forall (l : dist (Vector.t F n)) (trans : sigma_proto)
          (pr : prob) (cs : Vector.t F n) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob),
            List.In (trx, prx) l → prx = 1 / m) ->
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_schnorr x g us cs))) →
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

        (** Every element of the real parallel distribution is accepting
            and has probability [1/|lf|ⁿ]. *)
        Lemma generalised_parallel_special_honest_verifier_schnorr_dist {n : nat}
          (x : F) (g h : G) (R : h = g^x) :
          forall (lf : list F) (Hlfn : lf <> List.nil)
          (cs : Vector.t F n) a b,
          List.In (a, b)
            (generalised_parallel_schnorr_distribution lf Hlfn x g cs) ->
          generalised_parallel_accepting_conversations g h a = true ∧
          b = 1 / (Nat.pow (List.length lf) n).
        Proof.
          intros * Ha.
          refine(conj _ _).
          +
            eapply generalised_parallel_schnorr_distribution_transcript_generic.
            exact R.
            exact Ha.
          +
            eapply generalised_parallel_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.

        (** Every transcript in the support of the simulator mapped over any
            randomness distribution is accepting. *)
        Lemma generalised_parallel_simulator_distribution_transcript_generic {n : nat}
          (g h : G) : forall (l : dist (Vector.t F n))
          (trans : sigma_proto) (pr : prob) (cs : Vector.t F n),
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_simulator g h us cs))) →
          generalised_parallel_accepting_conversations g h trans = true.
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
              eapply construct_parallel_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_parallel_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (** Uniform probabilities [1/m] are preserved by mapping the
            simulator. *)
        Lemma generalised_parallel_simulator_distribution_probability_generic {n : nat}
          (g h : G) : forall (l : dist (Vector.t F n)) (trans : sigma_proto)
          (pr : prob) (cs : Vector.t F n) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), List.In (trx, prx) l → prx = 1 / m) ->
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_simulator g h us cs))) →
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

        (** Every element of the simulated parallel distribution is
            accepting and has probability [1/|lf|ⁿ]. *)
        Lemma generalised_parallel_special_honest_verifier_simulator_dist {n : nat}
          (g h : G) : forall (lf : list F) (Hlfn : lf <> List.nil)
          (cs : Vector.t F n) (a : sigma_proto) (b : prob),
          List.In (a, b)
            (generalised_parallel_simulator_distribution lf Hlfn g h cs) ->
          generalised_parallel_accepting_conversations g h a = true ∧
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
          intros * Ha.
          refine(conj _ _).
          +
            eapply generalised_parallel_simulator_distribution_transcript_generic;
            exact Ha.
          +
            eapply generalised_parallel_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.

        (** _Weak special HVZK._ For [h = g ^ x], projecting the real and the
            simulated parallel distributions to (acceptance bit,
            probability) gives the same list: every entry is
            [(true, 1/|lf|ⁿ)]. This compares verdicts only; see
            [generalised_parallel_special_honest_verifier_zkp_perm] for
            equality of the transcript distributions. *)
        Lemma generalised_parallel_special_honest_verifier_zkp
          (x : F) (g h : G) (R : h = g^x) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
          (cs : Vector.t F n),
          List.map (fun '(a, p) =>
            (generalised_parallel_accepting_conversations g h a, p))
            (@generalised_parallel_schnorr_distribution n lf Hlfn x g cs) =
          List.map (fun '(a, p) =>
            (generalised_parallel_accepting_conversations g h a, p))
            (@generalised_parallel_simulator_distribution n lf Hlfn g h cs).
        Proof.
          intros ? ? ? ?.
          eapply map_ext_eq.
          + unfold generalised_parallel_schnorr_distribution,
            generalised_parallel_simulator_distribution;
            cbn. repeat rewrite distribution_length.
            reflexivity.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_parallel_special_honest_verifier_schnorr_dist.
            exact R.
            exact Ha.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_parallel_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed.

        (** Shift lemma: for [h = g ^ x], the real transcript with
            randomness [us] equals the simulated transcript with randomness
            shifted coordinatewise, [uᵢ ↦ uᵢ + cᵢ · x] (expressed with
            [vec_apply]). Coordinatewise [schnorr_commitment_shift]. *)
        Lemma construct_parallel_shift (x : F) (g h : G) (R : h = g^x) :
          forall (n : nat) (us cs : Vector.t F n),
          construct_parallel_conversations_schnorr x g us cs =
          construct_parallel_conversations_simulator g h
            (vec_apply (Vector.map (fun c u => u + c * x) cs) us) cs.
        Proof.
          induction n as [| n ih]; intros us cs.
          + rewrite (vector_inv_0 us), (vector_inv_0 cs); reflexivity.
          + destruct (vector_inv_S us) as (u & us' & hu).
            destruct (vector_inv_S cs) as (c & cs' & hc).
            subst.
            specialize (ih us' cs').
            unfold construct_parallel_conversations_schnorr,
              construct_parallel_conversations_simulator,
              construct_parallel_conversations_schnorr_commitment in *.
            cbn in *.
            inversion ih as [[ha hr]].
            f_equal.
            * f_equal;
              [apply (schnorr_commitment_shift x g (g ^ x) eq_refl) | exact ha].
            * f_equal; exact hr.
        Qed.

        (** _Special HVZK, distribution equality._ Assume [h = g ^ x] and that
            for every [c] the translation [u ↦ u + c · x] permutes [lf] as a
            multiset. Then for every challenge vector [cs] the real and
            simulated parallel distributions are permutations of each other.
            Proof: by [construct_parallel_shift] the real distribution is the
            simulator applied to the shifted randomness; [repeat_uniform_perm]
            shows the coordinatewise shift permutes the product of uniform
            distributions, and [bind_ret_perm] concludes. *)
        Theorem generalised_parallel_special_honest_verifier_zkp_perm
          (x : F) (g h : G) (R : h = g^x) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
          (cs : Vector.t F n),
          (forall c : F, Permutation (List.map (fun u => u + c * x) lf) lf) ->
          Permutation
            (@generalised_parallel_schnorr_distribution n lf Hlfn x g cs)
            (@generalised_parallel_simulator_distribution n lf Hlfn g h cs).
        Proof.
          intros * hp.
          change (Permutation
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n)
              (fun us => Ret (construct_parallel_conversations_schnorr x g us cs)))
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) n)
              (fun us => Ret (construct_parallel_conversations_simulator g h us cs)))).
          eapply bind_ret_perm with
            (phi := vec_apply (Vector.map (fun c u => u + c * x) cs)).
          + apply repeat_uniform_perm; intros i.
            rewrite (nth_map _ _ i i eq_refl).
            apply hp.
          + intros us p _.
            apply construct_parallel_shift; exact R.
        Qed.

        (** _Special HVZK for an enumerated field._ When [lf] lists every
            element of [F] exactly once, the translation hypothesis holds
            (inverse [u ↦ u - c · x]), so the real and simulated parallel
            transcript distributions are equal up to permutation. *)
        Theorem generalised_parallel_special_honest_verifier_zkp_enum
          (x : F) (g h : G) (R : h = g^x) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (n : nat)
          (cs : Vector.t F n),
          List.NoDup lf -> (forall y : F, List.In y lf) ->
          Permutation
            (@generalised_parallel_schnorr_distribution n lf Hlfn x g cs)
            (@generalised_parallel_simulator_distribution n lf Hlfn g h cs).
        Proof.
          intros * hnd hall.
          eapply generalised_parallel_special_honest_verifier_zkp_perm; [exact R |].
          intro c.
          eapply enumerates_perm_map with (psi := fun u => u - c * x);
          [exact hnd | exact hall | intros u; field | intros u; field].
        Qed.

    End Proofs.
  End Parallel.
End DL.
