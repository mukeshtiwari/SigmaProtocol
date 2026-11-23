(** * The Chaum–Pedersen Protocol *)

(** This file instantiates the generic equality-of-discrete-logarithms
    protocol of [EqSigma] at two bases, giving the Chaum–Pedersen protocol
    (Chaum and Pedersen, ‘Wallet databases with observers’, Crypto 1992).
    For public group elements [g], [h], [c₁], [c₂] the prover shows knowledge
    of [x] with

    [[
      g ^ x = c₁  ∧  h ^ x = c₂
    ]]

    i.e. that [(g, h, c₁, c₂)] is a Diffie–Hellman tuple. Typical uses: [x]
    is ElGamal encryption randomness (so [c₁ = g ^ x] is the first ciphertext
    component and [c₂ = h ^ x] the mask under public key [h]), or [x] is a
    secret key and the protocol proves correct partial decryption.

    Protocol, with randomness [u] and challenge [c]:

    [[
      announcement  (g ^ u, h ^ u)
      response      r = u + c · x
      check         g ^ r = a₁ · c₁ ^ c   and   h ^ r = a₂ · c₂ ^ c
    ]]

    Every definition here is a thin wrapper that fixes [gs = [g; h]] and
    [hs = [c₁; c₂]] in the corresponding [EqSigma] definition, and every
    property is inherited from the [EqSigma] results: completeness, special
    soundness (two accepting transcripts with distinct challenges yield the
    witness), and special honest-verifier zero-knowledge (both the weak
    verdict-level form and the strong ‘equal distributions’ form). The file
    also gives the verifier in explicit two-equation form
    ([generalised_cp_accepting_conversations_accept] and
    [generalised_cp_accepting_conversations_reject]), which is convenient for
    the extracted verifiers in [Backend]. *)
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
From Sigma Require Import
  Sigma EqSigma.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(** ** Parameters *)
Section DL.
  (** The scalar field [F] with decidable equality. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] with decidable equality. *)
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

  (** [(a; c; r)] builds a transcript from announcement, challenge and
      response vectors. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** Chaum–Pedersen *)
  Section CP.
    (** *** Definitions *)
    Section Def.
      (** The announcement vector, with entries [g ^ u] and [h ^ u], for
          randomness [u]. *)
      Definition construct_cp_conversations_schnorr_commitment
         (g h : G) (u : F) : Vector.t G 2 :=
        @construct_eq_conversations_schnorr_commitment
          F G gpow _ [g; h] u.

      (** Honest prover transcript [([g ^ u; h ^ u]; [c]; [u + c · x])] for
          witness [x], randomness [u] and challenge [c]. *)
      Definition construct_cp_conversations_schnorr
        (x : F) (g h : G) (u c : F) : @sigma_proto F G 2 1 1 :=
        @construct_eq_conversations_schnorr F add mul G gpow _ x
          [g; h] u c.

      (** Simulator: for a response [u] and challenge [c] it outputs
          announcements [g ^ u · c₁ ^ (-c)] and [h ^ u · c₂ ^ (-c)], so the
          transcript is accepting without knowledge of [x]. *)
      Definition construct_cp_conversations_simulator
        (g h : G) (c₁ c₂ : G) (u c : F) : @sigma_proto F G 2 1 1 :=
        @construct_eq_conversations_simulator F opp G gop gpow _
        [g; h] [c₁; c₂] u c.

      (** Verifier: accepts [([a₁; a₂]; [c]; [r])] iff
          [g ^ r = a₁ · c₁ ^ c] and [h ^ r = a₂ · c₂ ^ c]. *)
      Definition generalised_cp_accepting_conversations (g h : G) (c₁ c₂ : G)
        (s : @sigma_proto F G 2 1 1) : bool :=
        @generalised_eq_accepting_conversations F G gop gpow Gdec _ [g; h]
        [c₁; c₂] s.

      (** Distribution of honest transcripts for challenge [c], with [u]
          drawn uniformly from the non-empty list [lf]. *)
      Definition generalised_cp_schnorr_distribution
        (lf : list F) (Hlfn : lf <> List.nil) (x : F)
        (g h : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_eq_schnorr_distribution F add mul G gpow _
          lf Hlfn x [g; h] c.

      (** Distribution of simulated transcripts for challenge [c], with the
          response drawn uniformly from [lf]. *)
      Definition generalised_cp_simulator_distribution
        (lf : list F) (Hlfn : lf <> List.nil) (g h : G)
        (c₁ c₂ : G) c : dist (@sigma_proto F G 2 1 1) :=
        @generalised_eq_simulator_distribution  F opp G gop
        gpow _ lf Hlfn [g; h] [c₁; c₂] c.

    End Def.

    (** *** Proofs *)

    (** The first five theorems characterise the boolean verifier by its
        two group equations; they need no algebraic hypotheses. *)
    Section Proofs.

      (** Acceptance implies both verification equations. *)
      Theorem generalised_cp_accepting_conversations_accept_forward :
        ∀ (g h c₁ c₂ : G) (a₁ a₂ : G) (c r : F),
        generalised_cp_accepting_conversations g h c₁ c₂
        ([a₁; a₂]; [c]; [r]) = true -> g ^ r = gop a₁ (c₁ ^ c) ∧
        h ^ r = gop a₂ (c₂ ^ c).
      Proof.
        intros * ha. unfold generalised_cp_accepting_conversations,
        generalised_eq_accepting_conversations. cbn in ha.
        eapply andb_true_iff in ha.
        destruct ha as (hal & har).
        rewrite dec_true in hal, har.
        rewrite hal, har; split; reflexivity.
      Qed.

      (** Both verification equations imply acceptance. *)
      Theorem generalised_cp_accepting_conversations_accept_backward :
        ∀ (g h c₁ c₂ : G) (a₁ a₂ : G) (c r : F),
        g ^ r = gop a₁ (c₁ ^ c) -> h ^ r = gop a₂ (c₂ ^ c) ->
        generalised_cp_accepting_conversations g h c₁ c₂
        ([a₁; a₂]; [c]; [r]) = true.
      Proof.
        intros * ha hb.
        cbn. eapply andb_true_iff; split;
        eapply dec_true; [exact ha | exact hb].
      Qed.

      (** Acceptance is equivalent to [g ^ r = a₁ · c₁ ^ c ∧
          h ^ r = a₂ · c₂ ^ c]. *)
      Theorem generalised_cp_accepting_conversations_accept :
        ∀ (g h c₁ c₂ : G) (a₁ a₂ : G) (c r : F),
        generalised_cp_accepting_conversations g h c₁ c₂
        ([a₁; a₂]; [c]; [r]) = true <-> g ^ r = gop a₁ (c₁ ^ c) ∧
        h ^ r = gop a₂ (c₂ ^ c).
      Proof.
        intros *; split; intros ha.
        eapply generalised_cp_accepting_conversations_accept_forward;
        assumption.
        eapply generalised_cp_accepting_conversations_accept_backward;
        destruct ha as (hal & har); assumption.
      Qed.

      (** Rejection implies that at least one verification equation
          fails. *)
      Theorem generalised_cp_accepting_conversations_reject_forward :
        ∀ (g h c₁ c₂ : G) (a₁ a₂ : G) (c r : F),
        generalised_cp_accepting_conversations g h c₁ c₂
        ([a₁; a₂]; [c]; [r]) = false -> g ^ r ≠ gop a₁ (c₁ ^ c) ∨
        h ^ r ≠ gop a₂ (c₂ ^ c).
      Proof.
        intros * ha; cbn in ha.
        eapply andb_false_iff in ha.
        destruct ha as [ha | ha].
        +
          eapply dec_false in ha;
          left; exact ha.
        +
          eapply dec_false in ha;
          right; exact ha.
      Qed.

      (** If at least one verification equation fails, the verifier
          rejects. *)
      Theorem generalised_cp_accepting_conversations_reject_backward :
        ∀ (g h c₁ c₂ : G) (a₁ a₂ : G) (c r : F),
        (g ^ r ≠ gop a₁ (c₁ ^ c) ∨ h ^ r ≠ gop a₂ (c₂ ^ c)) ->
        generalised_cp_accepting_conversations g h c₁ c₂
        ([a₁; a₂]; [c]; [r]) = false.
      Proof.
        intros * [ha | ha].
        +
          cbn. eapply andb_false_iff.
          left. eapply dec_false.
          exact ha.
        +
          cbn. eapply andb_false_iff.
          right. eapply dec_false.
          exact ha.
      Qed.

      (** Rejection is equivalent to the failure of at least one
          verification equation. *)
      Theorem generalised_cp_accepting_conversations_reject :
        ∀ (g h c₁ c₂ : G) (a₁ a₂ : G) (c r : F),
        (g ^ r ≠ gop a₁ (c₁ ^ c) ∨ h ^ r ≠ gop a₂ (c₂ ^ c)) <->
        generalised_cp_accepting_conversations g h c₁ c₂
        ([a₁; a₂]; [c]; [r]) = false.
      Proof.
        intros *; split; intros ha.
        eapply generalised_cp_accepting_conversations_reject_backward;
        assumption.
        eapply generalised_cp_accepting_conversations_reject_forward;
        assumption.
      Qed.

      (** From here on [G] is an [F]-vector space, and the [field] tactic is
          registered for [F]. *)
      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.

      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** Completeness: if [g ^ x = c₁] and [h ^ x = c₂], the honest
          transcript is accepted for every [u] and [c]. Instance of
          [construct_eq_conversations_schnorr_completeness]; the proof
          discharges the index-wise relation by case analysis on [Fin.t 2]. *)
      Lemma construct_cp_conversations_schnorr_completeness
        (x : F)
        (g h c₁ c₂ : G)
        (R : g^x = c₁ ∧ h^x = c₂) :
        forall (u c : F),
        generalised_cp_accepting_conversations g h c₁ c₂
          (construct_cp_conversations_schnorr x g h u c) = true.
      Proof.
        intros *. destruct R as (Ra & Rb).
        eapply construct_eq_conversations_schnorr_completeness.
        intro f.
        destruct (fin_inv_S _ f) as [ea | (fi & ea)].
        subst; cbn. exact eq_refl.
        destruct (fin_inv_S _ fi) as [eaa | (fii & eaa)].
        subst; cbn. exact eq_refl.
        refine match (fin_inv_0 fii) with end.
      Qed.

      (** Simulator completeness: simulated transcripts are always accepted,
          for any [g], [h], [c₁], [c₂]. *)
      Lemma construct_cp_conversations_simulator_completeness
        (g h c₁ c₂ : G) :
        forall (u c : F),
        generalised_cp_accepting_conversations g h c₁ c₂
          (construct_cp_conversations_simulator g h c₁ c₂ u c) = true.
      Proof.
        intros *.
        eapply construct_eq_conversations_simulator_completeness.
      Qed.

      (** Special soundness: two accepting transcripts with the same
          announcement and distinct challenges [cr₁ ≠ cr₂] yield [y] with
          [g ^ y = c₁] and [h ^ y = c₂] (stated index-wise over [Fin.t 2]).
          Instance of [generalise_eq_sigma_soundness]. *)
      Lemma generalise_cp_sigma_soundness
        (g h c₁ c₂ : G) :
        forall (a : Vector.t G 2)
        (cr₁ cr₂ : F) (r₁ r₂ : F),
        generalised_cp_accepting_conversations g h c₁ c₂ (a; [cr₁]; [r₁]) = true ->
        generalised_cp_accepting_conversations g h c₁ c₂ (a; [cr₂]; [r₂]) = true ->
        cr₁ <> cr₂ ->
        ∃ y : F, (forall (f : Fin.t 2),
          (nth [g; h] f)^y = (nth [c₁; c₂] f)).
      Proof.
        intros * ha hb hc.
        eapply generalise_eq_sigma_soundness
        with (a := a) (c₁ := cr₁)
        (c₂ := cr₂) (r₁ := r₁) (r₂ := r₂).
        exact ha. exact hb. exact hc.
      Qed.

      (** Special honest-verifier zero-knowledge, weak form: under the
          relation, the honest and simulated distributions coincide after
          mapping each transcript to the verifier’s verdict (every entry is
          [(true, 1 / |lf|)]). *)
      Lemma generalised_cp_special_honest_verifier_zkp
        (x : F)
        (g h c₁ c₂ : G)
        (R : g^x = c₁ ∧ h^x = c₂) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.map (fun '(a, p) =>
          (generalised_cp_accepting_conversations g h c₁ c₂ a, p))
          (@generalised_cp_schnorr_distribution lf Hlfn x g h c) =
        List.map (fun '(a, p) =>
          (generalised_cp_accepting_conversations g h c₁ c₂ a, p))
          (@generalised_cp_simulator_distribution lf Hlfn g h c₁ c₂ c).
      Proof.
        intros *. destruct R as (Ra & Rb).
        eapply generalised_eq_special_honest_verifier_zkp.
        intro f.
        destruct (fin_inv_S _ f) as [ea | (fi & ea)].
        subst; cbn.  exact eq_refl.
        destruct (fin_inv_S _ fi) as [eaa | (fii & eaa)].
        subst; cbn. exact eq_refl.
        refine match (fin_inv_0 fii) with end.
      Qed.

      (** Special honest-verifier zero-knowledge, strong form: under the
          relation, if [u ↦ u + c · x] permutes [lf], then the honest and
          simulated transcript distributions are permutations of each other.
          Instance of [generalised_eq_special_honest_verifier_zkp_perm]. *)
      Theorem generalised_cp_special_honest_verifier_zkp_perm
        (x : F) (g h c₁ c₂ : G) (R : g^x = c₁ ∧ h^x = c₂) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        Permutation (List.map (fun u => u + c * x) lf) lf ->
        Permutation
          (@generalised_cp_schnorr_distribution lf Hlfn x g h c)
          (@generalised_cp_simulator_distribution lf Hlfn g h c₁ c₂ c).
      Proof.
        intros * hp; destruct R as (Ra & Rb).
        unfold generalised_cp_schnorr_distribution,
          generalised_cp_simulator_distribution.
        eapply generalised_eq_special_honest_verifier_zkp_perm; [| exact hp].
        intro f.
        destruct (fin_inv_S _ f) as [ea | (fi & ea)]; subst; cbn; [reflexivity |].
        destruct (fin_inv_S _ fi) as [eb | (fj & eb)]; subst; cbn; [reflexivity |].
        refine (match fj with end).
      Qed.

      (** Special honest-verifier zero-knowledge when [lf] enumerates the
          field without duplicates: the honest and simulated transcript
          distributions are permutations of each other. *)
      Theorem generalised_cp_special_honest_verifier_zkp_enum
        (x : F) (g h c₁ c₂ : G) (R : g^x = c₁ ∧ h^x = c₂) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.NoDup lf -> (forall y : F, List.In y lf) ->
        Permutation
          (@generalised_cp_schnorr_distribution lf Hlfn x g h c)
          (@generalised_cp_simulator_distribution lf Hlfn g h c₁ c₂ c).
      Proof.
        intros * hnd hall.
        eapply generalised_cp_special_honest_verifier_zkp_perm; [exact R |].
        eapply enumerates_perm_map with (psi := fun u => u - c * x);
        [exact hnd | exact hall | intros u; field | intros u; field].
      Qed.

    End Proofs.
  End CP.
End DL.
