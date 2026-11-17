(** * Sigma protocols: the generic transcript record and Schnorr's protocol *)

(** This file is the foundation of the Crypto library. It fixes the shape
    of a three-move public-coin Sigma-protocol transcript and develops, in
    full, Schnorr's proof of knowledge of a discrete logarithm.

    _Setting._ We work over an abstract prime-order group [G] (written
    multiplicatively, operation [gop], identity [gid], inverse [ginv]) that
    is a vector space over a field [F] of exponents, with scalar
    multiplication written [g ^ u] ([gpow]). Equality on both [F] and [G] is
    decidable ([Fdec], [Gdec]), which is what lets the verifier be a
    boolean function. Concrete instances (Schnorr groups mod p, P-256,
    Ed25519) are provided in the Examples and Curve directories.

    _Schnorr's protocol._ For public [g, h : G] the relation is
    [R(g, h; x) :⇔ h = g ^ x]. The prover knowing [x]:

    - picks a random [u : F] and sends the announcement [a = g ^ u];
    - receives a challenge [c : F] from the verifier;
    - replies with [r = u + c · x].

    The verifier accepts iff [g ^ r = a · h ^ c]. The simulator, given
    [c] and a random [u], outputs the transcript [(g ^ u · h ^ (-c); c; u)],
    which is accepting without any knowledge of [x].

    _What is proved._

    - Completeness: [schnorr_completeness], [simulator_completeness].
    - Special soundness (2-special soundness with an explicit extractor
      [(r₁ - r₂) / (c₁ - c₂)]): [special_soundness_berry_gen] and its
      existential corollary [special_soundness_berry].
    - Special honest-verifier zero knowledge, in two strengths. The weak
      form [special_honest_verifier_zkp] only says that the multiset of
      pairs (acceptance bit, probability) agrees for real and simulated
      transcripts. The strong form [special_honest_verifier_zkp_perm] /
      [special_honest_verifier_zkp_enum] states that the real and the
      simulated distributions are equal up to permutation of their
      support lists, that is, identical as distributions, provided the
      randomness is drawn uniformly from a list that enumerates the whole
      field without duplicates.
    - A soundness-error bound [soundness_error_bound]: for a fixed
      announcement and any (possibly cheating) response function, either
      the witness can be extracted, or the prover is accepted with
      probability at most [1/|challenge space|].
    - The corner case [schnorr_completeness_corner_case_invalid_proof_accept]
      records that with challenge [c = 0] the transcript [(g ^ u; 0; u)]
      is accepted whatever [h] is, so a prover without a witness succeeds
      exactly when the challenge happens to be [0] (probability
      [1/|challenge space|]). It was found while proving vote-proof
      rejection in the approval-voting development.

    Distributions are the finite list-based distributions of
    [Probability.Distr]: a [dist A] is a list of (value, probability)
    pairs and [uniform_with_replacement lf _] gives each element of [lf]
    probability [1/|lf|].

    _Use elsewhere._ The record [sigma_proto] and the Schnorr definitions
    are reused by every other Sigma protocol in this directory
    ([ParallelSigma], [AndSigma], [AndSigmaGen], [OrSigma], [EqSigma],
    [NeqSigma], [ChaumPedersen], [Okamoto], [EncProof], [DecProof],
    [ShuffleTW], ...).

    References: C. P. Schnorr, ‘Efficient signature generation by smart
    cards’, J. Cryptology 1991; R. Cramer, ‘Modular design of secure yet
    practical cryptographic protocols’, PhD thesis 1996 (Sigma-protocol
    terminology); B. Schoenmakers, lecture notes ‘Cryptographic
    Protocols’ (TU Eindhoven, course 2WC13), whose formulations the lemmas
    with suffix [_berry] follow. *)
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
From Utility Require Import
  Util.
From ExtLib.Structures Require Import
  Monad.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(** ** Discrete-logarithm Sigma protocols

    The section is parameterised by a field [F] of exponents and a group
    [G] of elements; the vector-space laws relating them are only assumed
    later, in the [Proofs] section, so that the definitions extract to
    code without carrying proofs. *)

(** Field of exponents: carrier [F], constants [zero], [one], ring and field
    operations, and decidable equality [Fdec]. *)
Section DL.
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** Group of elements: carrier [G], identity [gid], inverse [ginv],
      group operation [gop], exponentiation [gpow : G → F → G], and decidable
      equality [Gdec]. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Local notations: [^] is exponentiation in [G]; [*], [/], [+], [-] are
      the field operations on [F]. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** ** Generic transcript record *)
  Section SigmaDefinition.

    (** [sigma_proto] is a Sigma-protocol transcript (conversation) with
        [n] group elements in the announcement, [m] field elements in the
        challenge and [r] field elements in the response. All Sigma
        protocols in the library use this record; for example Schnorr is
        [@sigma_proto 1 1 1] and an [n]-fold parallel or AND composition
        uses vectors of length [n]. *)
    Record sigma_proto {n m r : nat} : Type :=
      mk_sigma
      {
        announcement : Vector.t G n;
        challenge : Vector.t F m;
        response : Vector.t F r
      }.

  End SigmaDefinition.

  (** [(a; c; r)] builds the transcript with announcement [a], challenge
      [c] and response [r]. *)
  #[local] Notation "( a ; c ; r )" :=
    (@mk_sigma _ _ _ a c r).

  (** ** Schnorr's protocol for knowledge of a discrete logarithm *)
  Section Basic_sigma.

    (** *** Definitions

        The prover, simulator, verifier and the induced distributions.
        Throughout, [x] is the secret witness, [g] and [h] are public, and
        the relation is [h = g ^ x]. *)
    Section Def.

      (** The announcement [g ^ u] for the prover's randomness [u], kept as
          a separate definition so that a non-interactive (Fiat–Shamir)
          prover can compute it before deriving the challenge. *)
      Definition schnorr_protocol_commitment (g : G) (u : F) : G := g^u.

      (** The honest prover's transcript for witness [x], generator [g],
          randomness [u] and challenge [c]:
          [(g ^ u; c; u + c · x)]. *)
      Definition schnorr_protocol (x : F) (g : G) (u c : F) : @sigma_proto 1 1 1 :=
        ([schnorr_protocol_commitment g u]; [c]; [u + c * x]).

      (** The HVZK simulator: given only public [g], [h], a uniformly drawn
          [u] and the challenge [c], it outputs [(g ^ u · h ^ (-c); c; u)].
          No witness is used. *)
      Definition schnorr_simulator (g h : G) (u c : F) : @sigma_proto 1 1 1 :=
        ([gop (g^u) (h^(opp c))]; [c]; [u]).

      (** The verifier's check for a Schnorr transcript [(a; c; r)]:
          returns [true] iff [g ^ r = a · h ^ c], decided with [Gdec]. *)
      Definition accepting_conversation
        (g h : G) (v : @sigma_proto 1 1 1) : bool :=
        match v with
        | (a; c; r) =>
          match Gdec (g^(hd r)) (gop (hd a) (h^(hd c))) with
          | left _ => true
          | right _ => false
          end
        end.

      (** The distribution of real transcripts for a fixed challenge [c]:
          draw [u] uniformly from the (non-empty) list [lf] and run
          [schnorr_protocol x g u c]. *)
      Definition schnorr_distribution  (lf : list F)
        (Hlfn : lf <> List.nil) (x : F) (g : G) (c : F) : dist sigma_proto :=
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (schnorr_protocol x g u c).

      (** The distribution of simulated transcripts for a fixed challenge
          [c]: draw [u] uniformly from [lf] and run [schnorr_simulator]. *)
      Definition simulator_distribution (lf : list F)
        (Hlfn : lf <> List.nil) (g h : G) (c : F) : dist sigma_proto :=
        u <- (uniform_with_replacement lf Hlfn) ;;
        Ret (schnorr_simulator g h u c).

    End Def.

    (** *** Proofs

        Verifier characterisation, completeness, special soundness,
        special HVZK and the soundness-error bound. *)
    Section Proofs.

      (** [accepting_conversation] is exactly the predicate
          [g ^ r = a · h ^ c] on singleton transcripts. *)
      Lemma accepting_conversation_correct :
          forall (g h a : G) (c r : F),
          accepting_conversation g h ([a]; [c]; [r]) = true <->
          (g^r) = (gop a (h^c)).
      Proof.
        intros *;
        split; intros Ha.
        unfold accepting_conversation in Ha.
        all:
          (apply (@dec_true _ Gdec) in Ha;
          exact Ha).
      Qed.

      (** Rejection counterpart: [accepting_conversation] returns [false]
          iff [g ^ r ≠ a · h ^ c]. *)
      Lemma accepting_conversation_reject :
          forall (g h a : G) (c r : F),
          accepting_conversation g h ([a]; [c]; [r]) = false <->
          (g^r) ≠ (gop a (h^c)).
      Proof.
        intros *.
        split; intro ha.
        +
          unfold accepting_conversation in ha.
          destruct (Gdec (g ^ hd [r]) (gop (hd [a]) (h ^ hd [c]))) as [hb | hb];
          try congruence.
          cbn in hb; exact hb.
        +
          unfold accepting_conversation.
          destruct (Gdec (g ^ hd [r]) (gop (hd [a]) (h ^ hd [c]))) as [hb | hb];
          cbn in hb; try congruence.
      Qed.

      (** From here on, [G] is assumed to be a vector space over [F]
          ([Hvec]); this gives the exponent laws
          [g ^ (u + v) = g ^ u · g ^ v] and [(g ^ x) ^ c = g ^ (x · c)]
          used in every proof below. *)
      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.

      (** Registers [F] with the [field] tactic. *)
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** _Completeness._ If [h = g ^ x], then for every randomness [u] and
          challenge [c] the honest transcript is accepting:
          [g ^ (u + c · x) = g ^ u · (g ^ x) ^ c]. The proof rewrites
          [(g ^ x) ^ c] to [g ^ (x · c)] and uses distributivity of [^]
          over field addition. *)
      Lemma schnorr_completeness (g h : G) (x : F) (R : h = g^x) :
        forall (u c : F),
          accepting_conversation g h
          (schnorr_protocol x g u c) = true.
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

      (** Completeness restated for an explicitly named transcript
          [(a₁; c₁; r₁)] equal to the honest one. *)
      Lemma schnorr_completeness_berry (g h : G) (x : F) (R : h = g^x) :
        forall (u c : F) (a₁ : t G 1) (c₁ r₁ : t F 1),
        (a₁; c₁; r₁) = (schnorr_protocol x g u c) ->
        accepting_conversation g h (a₁; c₁; r₁) = true.
      Proof.
        intros * Ha; rewrite Ha;
        now eapply schnorr_completeness.
      Qed.

      (** Corner case: when the challenge is [zero], the honest transcript
          [(g ^ u; 0; u)] is accepting for _any_ [g], [h] and [x], even if
          [h ≠ g ^ x]. Note that this lemma does not assume the relation.
          It shows why a zero challenge carries no evidence; in the
          non-interactive setting a hash output of [0] would let a forger
          succeed trivially. *)
      Lemma schnorr_completeness_corner_case_invalid_proof_accept
        (g h : G) (x : F) : forall (u c : F), c = zero ->
        accepting_conversation g h
          (schnorr_protocol x g u c) = true.
      Proof.
        intros * ha.
        unfold schnorr_protocol,
        accepting_conversation,
        schnorr_protocol_commitment; cbn.
        eapply dec_true. subst.
        assert (ha : u + zero * x = u) by field.
        rewrite ha; clear ha.
        rewrite field_zero, right_identity;
        reflexivity.
      Qed.

      (** The simulator always produces an accepting transcript, with no
          relation assumed: [g ^ u = (g ^ u · h ^ (-c)) · h ^ c], by
          associativity, [h ^ (-c) · h ^ c = h ^ 0 = gid] and right
          identity. *)
      Lemma simulator_completeness (g h : G) :
        forall (u c : F),
        accepting_conversation g h (schnorr_simulator g h u c) = true.
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

      (** Simulator completeness restated for an explicitly named transcript
          [(a₁; c₁; r₁)]. *)
      Lemma simulator_completeness_berry (g h : G) :
        forall (u c : F) (a₁ : t G 1) (c₁ r₁ : t F 1),
        (a₁; c₁; r₁) = (schnorr_simulator g h u c) ->
        accepting_conversation g h (a₁; c₁; r₁) = true.
      Proof.
        intros * Ha;
        rewrite Ha;
        apply simulator_completeness.
      Qed.

      (** _Special soundness with explicit extractor._ Given two accepting
          transcripts [(a; c₁; r₁)] and [(a; c₂; r₂)] with the same
          announcement and different challenges [c₁ ≠ c₂], the value
          [y = (r₁ - r₂) · (c₁ - c₂)⁻¹] satisfies [g ^ y = h]. The explicit
          form of [y] is needed by protocols such as [EqSigma] that must
          show the same witness is extracted for several bases.

          Proof idea: from [g ^ r₁ = a · h ^ c₁] and
          [g ^ r₂ = a · h ^ c₂], dividing gives
          [g ^ (r₁ - r₂) = h ^ (c₁ - c₂)]; raising both sides to
          [(c₁ - c₂)⁻¹], which exists because [c₁ - c₂ ≠ 0], yields the
          claim. *)
      Lemma special_soundness_berry_gen (g h : G) :
        forall (a : G) (c₁ r₁ c₂ r₂ : F),
        c₁ <> c₂ ->
        accepting_conversation g h ([a]; [c₁]; [r₁]) = true ->
        accepting_conversation g h ([a]; [c₂]; [r₂]) = true ->
        ∃ y : F, g^y = h ∧ y =  ((r₁ - r₂) * inv (c₁ - c₂)).
      Proof.
        (* Invert the second verification equation and multiply it with
           the first, cancelling the common announcement [a]. *)
        intros * Ha Hb Hc.
        apply (@dec_true _ Gdec) in Hb, Hc.
        cbn in Hb, Hc.
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
        (* Now [g ^ (r₁ - r₂) = h ^ (c₁ - c₂)]; raise both sides to the
           inverse of [c₁ - c₂]. *)
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
        (* Side condition: [c₁ - c₂ ≠ 0] since [c₁ ≠ c₂]. *)
        intros Hf.
        pose proof ring_neq_sub_neq_zero c₁ c₂ Ha as Hw.
        apply Hw.
        rewrite ring_sub_definition.
        exact Hf.
        all:typeclasses eauto.
      Qed.

      (** _Special soundness._ Two accepting transcripts with a common
          announcement and distinct challenges imply the existence of a
          discrete logarithm [y] with [g ^ y = h]. Corollary of
          [special_soundness_berry_gen]. *)
      Lemma special_soundness_berry (g h : G) :
        forall (a : G) (c₁ r₁ c₂ r₂ : F),
        c₁ <> c₂ ->
        accepting_conversation g h ([a]; [c₁]; [r₁]) = true ->
        accepting_conversation g h ([a]; [c₂]; [r₂]) = true ->
        ∃ y : F, g^y = h.
      Proof.
        intros * Ha Hb Hc.
        pose proof special_soundness_berry_gen g h
        a c₁ r₁ c₂ r₂ Ha Hb Hc as Hd.
        destruct Hd as (y & Hd & He).
        exists y; exact Hd.
      Qed.

      (** [p / q] is local notation for the probability [p/q]. *)
      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      (** Helper for the probability part of HVZK: if every entry of a
          distribution [l] over [F] has probability [1/n], then so does every
          entry of the transcript distribution obtained by mapping
          [schnorr_protocol x g · c] over it. By induction on [l]. *)
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

      (** Helper: if [h = g ^ x], every transcript in the support of
          [Bind l (λ u, Ret (schnorr_protocol x g u c))] is accepting. By
          induction on [l] and [schnorr_completeness]. *)
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
              eapply IHl; exact Ha.
      Qed.

      (** Every element [((a₁; c₁; r₁), prob)] of the real distribution
          [schnorr_distribution lf _ x g c] has probability [1/|lf|] and
          is an accepting transcript (assuming [h = g ^ x]). *)
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

      (** Simulator analogue of
          [schnorr_distribution_probability_generic]: uniform input
          probabilities [1/n] are preserved by mapping the simulator. *)
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

      (** Every transcript in the support of the mapped simulator is
          accepting (no relation assumed). *)
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
              eapply IHl; exact Ha.
      Qed.

      (** Every element of [simulator_distribution lf _ g h c] has
          probability [1/|lf|] and is accepting. *)
      Lemma probability_simulator_distribution (g h : G) :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (c : F) (a₁ : t G 1) (c₁ r₁ : t F 1)
        (prob : Prob.prob) (n : nat),
        n = List.length lf ->
        List.In ((a₁; c₁; r₁), prob)
          (@simulator_distribution lf Hlfn g h c) ->
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

      (** _Weak special HVZK._ For [h = g ^ x], any non-empty randomness
          list [lf] and any challenge [c], projecting each transcript of the
          real and simulated distributions to its acceptance bit gives the
          same list of (bit, probability) pairs: both lists have length
          [|lf|] and every entry is [(true, 1/|lf|)].

          This is a statement about the verifier's verdicts only; it does
          not compare the transcripts themselves. The stronger statement
          that the transcript distributions coincide is
          [special_honest_verifier_zkp_perm]. *)
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

      (** Algebraic identity behind the simulator: for [h = g ^ x],
          [g ^ u = g ^ (u + c · x) · h ^ (-c)]. *)
      Lemma schnorr_commitment_shift (x : F) (g h : G) (R : h = g^x) :
        forall (u c : F),
        g ^ u = gop (g ^ (u + c * x)) (h ^ (opp c)).
      Proof.
        intros *; rewrite R.
        assert (ha : (g ^ x) ^ opp c = g ^ (x * opp c)) by
          (rewrite smul_pow_up; reflexivity).
        rewrite ha; clear ha.
        rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
          zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow).
        + assert (hb : u + c * x + x * opp c = u) by field.
          rewrite hb; reflexivity.
        + typeclasses eauto.
      Qed.

      (** Shift lemma: the real transcript with randomness [u] equals the
          simulated transcript with randomness [u + c · x]. Hence the
          simulator is the real prover with its randomness translated by
          [c · x]. *)
      Lemma schnorr_protocol_simulator_shift (x : F) (g h : G) (R : h = g^x) :
        forall (u c : F),
        schnorr_protocol x g u c = schnorr_simulator g h (u + c * x) c.
      Proof.
        intros *.
        unfold schnorr_protocol, schnorr_simulator,
          schnorr_protocol_commitment.
        f_equal; f_equal.
        apply schnorr_commitment_shift; exact R.
      Qed.

      (** _Special HVZK, distribution equality._ Assume [h = g ^ x] and
          that translation by [c · x] permutes the randomness list [lf]
          (as a multiset). Then the real distribution
          [schnorr_distribution lf _ x g c] and the simulated distribution
          [simulator_distribution lf _ g h c] are permutations of each
          other, so they assign the same probability to every transcript.

          Proof idea: by [schnorr_protocol_simulator_shift] the real
          distribution is the simulator applied to the shifted
          randomness, and [bind_ret_perm] with [uniform_perm] turns the
          multiset hypothesis on [lf] into a permutation of
          distributions. *)
      Theorem special_honest_verifier_zkp_perm (x : F) (g h : G) (R : h = g^x) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        Permutation (List.map (fun u => u + c * x) lf) lf ->
        Permutation (@schnorr_distribution lf Hlfn x g c)
          (@simulator_distribution lf Hlfn g h c).
      Proof.
        intros * hp.
        change (Permutation
          (Bind (uniform_with_replacement lf Hlfn)
            (fun u => Ret (schnorr_protocol x g u c)))
          (Bind (uniform_with_replacement lf Hlfn)
            (fun u => Ret (schnorr_simulator g h u c)))).
        eapply bind_ret_perm with (phi := fun u => u + c * x).
        + eapply uniform_perm; exact hp.
        + intros u p _.
          eapply schnorr_protocol_simulator_shift; exact R.
      Qed.

      (** _Special HVZK for a fully enumerated field._ If [lf] lists every
          element of [F] exactly once ([NoDup] and total), the
          translation hypothesis of [special_honest_verifier_zkp_perm]
          holds automatically (its inverse is [u ↦ u - c · x]), so the
          real and simulated transcript distributions are equal up to
          permutation. This is the textbook perfect special HVZK
          statement for uniform randomness over [F]. *)
      Theorem special_honest_verifier_zkp_enum (x : F) (g h : G) (R : h = g^x) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.NoDup lf -> (forall y : F, List.In y lf) ->
        Permutation (@schnorr_distribution lf Hlfn x g c)
          (@simulator_distribution lf Hlfn g h c).
      Proof.
        intros * hnd hall.
        eapply special_honest_verifier_zkp_perm; [exact R |].
        eapply enumerates_perm_map with (psi := fun u => u - c * x);
        [exact hnd | exact hall | intros u; field | intros u; field].
      Qed.

      (** _Soundness error._ Fix an announcement [a] and an arbitrary
          prover strategy given as a response function [resp : F → F].
          Let challenges be uniform over a duplicate-free list [lf]. Then
          either

          - there are two distinct challenges [c₁ ≠ c₂] in [lf] on which
            the prover is accepted, and the extracted value
            [(resp c₁ - resp c₂) · (c₁ - c₂)⁻¹] is a discrete logarithm of
            [h]; or
          - the probability that the verifier accepts is at most
            [1/|lf|].

          So a prover who does not know a witness is accepted with
          probability at most [1/|lf|] (the usual knowledge error of
          Schnorr). Proof: case split on whether the filtered list of
          accepting challenges has length 0, 1, or at least 2; in the last
          case apply [special_soundness_berry_gen]. *)
      Theorem soundness_error_bound (g h a : G) (resp : F -> F) :
        forall (lf : list F) (Hlfn : lf <> List.nil), List.NoDup lf ->
        (∃ c₁ c₂ : F, c₁ <> c₂ ∧ List.In c₁ lf ∧ List.In c₂ lf ∧
          accepting_conversation g h ([a]; [c₁]; [resp c₁]) = true ∧
          accepting_conversation g h ([a]; [c₂]; [resp c₂]) = true ∧
          g ^ ((resp c₁ - resp c₂) * inv (c₁ - c₂)) = h) ∨
        leq (@prob_of_an_event F
              (fun c => accepting_conversation g h ([a]; [c]; [resp c]))
              (uniform_with_replacement lf Hlfn))
            (mk_prob 1 (Pos.of_nat (List.length lf))) = true.
      Proof.
        intros * hnd.
        (* Rewrite the event probability as a sum of [1/|lf|] over the
           accepting challenges. *)
        set (e := fun c => accepting_conversation g h ([a]; [c]; [resp c])).
        assert (hpe : @prob_of_an_event F e (uniform_with_replacement lf Hlfn) =
          List.fold_right (fun '(_, bx) ax => add_prob ax bx) Prob.zero
            (List.map (fun x => (x, mk_prob 1 (Pos.of_nat (List.length lf))))
              (List.filter e lf))).
        {
          unfold prob_of_an_event, list_of_events.
          rewrite uniform_with_replacement_unfold, list_of_events_uniform.
          reflexivity.
        }
        (* Case split on the number of accepting challenges. *)
        destruct (List.filter e lf) as [| c₁ [| c₂ cs]] eqn:hf.
        + right.
          rewrite hpe; cbn;
          first [reflexivity | apply PeanoNat.Nat.leb_le; lia].
        + right.
          rewrite hpe; cbn;
          first [reflexivity | apply PeanoNat.Nat.leb_le; lia].
        (* Two distinct accepting challenges: extract the witness. *)
        + left.
          assert (hnf : List.NoDup (List.filter e lf)) by
            (apply List.NoDup_filter; exact hnd).
          rewrite hf in hnf.
          inversion hnf as [| ? ? hnin hnd']; subst.
          assert (hc₁ : List.In c₁ (List.filter e lf)) by
            (rewrite hf; left; reflexivity).
          assert (hc₂ : List.In c₂ (List.filter e lf)) by
            (rewrite hf; right; left; reflexivity).
          apply List.filter_In in hc₁, hc₂.
          destruct hc₁ as [hc₁ he₁], hc₂ as [hc₂ he₂].
          assert (hne : c₁ <> c₂) by
            (intro heq; subst; apply hnin; left; reflexivity).
          destruct (special_soundness_berry_gen g h a c₁ (resp c₁) c₂ (resp c₂)
            hne he₁ he₂) as (y & hy & heq).
          exists c₁, c₂.
          repeat split; try assumption.
          rewrite <-heq; exact hy.
      Qed.

    End Proofs.
  End Basic_sigma.
End DL.
