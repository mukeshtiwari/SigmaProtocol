(** * Fiat–Shamir verification of multi-base (linear-relation) proofs *)

(** This file connects a non-interactive, hash-based verifier for proofs of
    knowledge of a representation to the interactive generalised Okamoto
    protocol of [Sigma.Okamoto]. The statement is

    [[
      h = g_1^{x_1} · … · g_k^{x_k}
    ]]

    written additively in an abstract vector space [V] over a field [F]
    (so [g^x] is [smul g x] and the group law is [vadd]). A published proof
    is a challenge [c] together with responses [s_1, …, s_k]. The verifier
    recomputes the announcement

    [[
      A = g_1^{s_1} · … · g_k^{s_k} · h^{d}
    ]]

    and accepts iff [c = H(A)] for a hash function [H : V -> F].

    Deployed systems differ in the sign convention of the response. Belenios,
    Verificatum and the BBS family publish [s = w − c·x] and reconstruct with
    [d = c]; U-Prove publishes [s = w + c·x] and reconstructs with [d = −c].
    The definitions are therefore parametric in [d].

    Main results:

    - [reconstruct_linrel_accepting]: for every [d] and every responses
      vector, the triple (reconstructed announcement, challenge [−d],
      responses) is an accepting transcript of
      [generalised_okamoto_accepting_conversation]. Choosing [d = c] or
      [d = −c] yields an accepting interactive transcript with challenge
      [−c] or [c] respectively.
    - [fs_verify_linrel_accepting]: the same conclusion stated under the
      hypothesis that [fs_verify_linrel] accepted.

    Caveat: the reconstruction identity holds for every [(d, ss)], so these
    theorems are purely algebraic; they do not use the hash check and say
    nothing about soundness in the random-oracle model. Their role is to
    show that the executable verifier computes exactly the announcement the
    Okamoto verification equation demands, so that the special soundness of
    the Okamoto protocol (proved in [Sigma.Okamoto]) applies to two such
    transcripts with the same announcement. The hash [H] is abstract here;
    concrete verifiers instantiate it with SHA-256 from [Utility.Sha256].

    The single-base (Schnorr and disjunctive) analogue lives in
    [Backend.BeleniosTally]; this file provides the multi-base version. The
    credential verifiers [Backend.UProveVerifier] and
    [Backend.BBSSharpVerifier] follow the same reconstruct-then-hash pattern
    with their own protocol-specific reconstruction functions. *)
From Stdlib Require Import Utf8 Vector List Bool setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Sigma Require Import Sigma Okamoto.
From Utility Require Import Util.
Import VectorNotations.

(** ** Generic development over a vector space *)

(** The field [F] of exponents (with decidable equality [Fdec], needed to
    compare the challenge with the hash) and the vector space [V] of group
    elements (with decidable equality [Vdec], needed by the Okamoto verifier).
    [HV] packages the vector-space axioms. *)
Section FiatShamirLinRel.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {Vdec : forall x y : V, {x = y} + {x <> y}}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  (** Registers [F] with the [field] tactic, used for [d + (−d) = 0]. *)
  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  (** [multi_exp gs ss] computes [g_1^{s_1} · … · g_k^{s_k}], folding from
      the right with [vid] (the identity) as the base. It is written over
      [zip_with pair] so that it matches the extracted verifiers. *)
  Definition multi_exp {k : nat} (gs : Vector.t V k) (ss : Vector.t F k) : V :=
    Vector.fold_right (fun '(g, s) acc => vadd (smul g s) acc) (zip_with pair gs ss) vid.

  (** [reconstruct_linrel gs h d ss] is the announcement a verifier
      recomputes from a published proof: [multi_exp gs ss · h^d]. With
      responses [s_i = w_i − c·x_i] and [d = c] this equals the prover's
      original commitment [∏ g_i^{w_i}]. *)
  Definition reconstruct_linrel {k : nat} (gs : Vector.t V k) (h : V) (d : F)
    (ss : Vector.t F k) : V :=
    vadd (multi_exp gs ss) (smul h d).

  (** [fs_verify_linrel H gs h d c ss] is the Fiat–Shamir check: it returns
      [true] iff the published challenge [c] equals [H] applied to the
      reconstructed announcement. The caller chooses [d = c] or [d = −c]
      according to the system's sign convention. Only the challenge equation
      is checked; membership of [h] and the [g_i] in the intended subgroup,
      and the content hashed by [H] (statement, context), are the caller's
      responsibility. *)
  Definition fs_verify_linrel {k : nat} (H : V -> F) (gs : Vector.t V k) (h : V)
    (d c : F) (ss : Vector.t F k) : bool :=
    match Fdec c (H (reconstruct_linrel gs h d ss)) with
    | left _ => true | right _ => false
    end.

  (** ** Link to the generalised Okamoto protocol *)

  (** [multi_exp] agrees with the fold used inside
      [generalised_okamoto_accepting_conversation] (which pairs bases and
      responses via [zip_with smul]). Stated for length [2 + n] because the
      Okamoto protocol in the library requires at least two bases. Proof by
      induction on the length. *)
  Lemma multi_exp_okamoto : forall (n : nat) (gs : Vector.t V (2 + n)) (ss : Vector.t F (2 + n)),
    Vector.fold_right (fun gr acc => vadd gr acc) (zip_with (fun g r => smul g r) gs ss) vid =
    multi_exp gs ss.
  Proof.
    intros n; generalize (2 + n); clear n.
    intros m; induction m as [| m ih]; intros gs ss.
    + rewrite (vector_inv_0 gs), (vector_inv_0 ss); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S ss) as (s & ss' & ->).
      unfold multi_exp in *; cbn; f_equal; apply ih.
  Qed.

  (** For any [d] and responses [ss], the transcript with announcement
      [reconstruct_linrel gs h d ss], challenge [−d] and responses [ss] is
      accepted by the generalised Okamoto verifier, i.e.
      [∏ g_i^{s_i} = A · h^{−d}]. Proof: by [multi_exp_okamoto] it suffices
      to show [multi_exp gs ss = (multi_exp gs ss · h^d) · h^{−d}], which
      follows from associativity, distributivity of scalar multiplication
      over field addition, [d + (−d) = 0], [h^0 = vid] and the right
      identity law. *)
  Theorem reconstruct_linrel_accepting : forall (n : nat) (gs : Vector.t V (2 + n)) (h : V)
    (d : F) (ss : Vector.t F (2 + n)),
    generalised_okamoto_accepting_conversation (gid := vid) (gop := vadd) (gpow := smul) (Gdec := Vdec) gs h
      (mk_sigma _ _ _ [reconstruct_linrel gs h d ss] [opp d] ss) = true.
  Proof.
    intros *; unfold generalised_okamoto_accepting_conversation;
    cbn [Vector.hd announcement challenge response].
    rewrite multi_exp_okamoto.
    (* The key identity: ∏ g_i^{s_i} = A · h^{−d}. *)
    assert (he : multi_exp gs ss = vadd (reconstruct_linrel gs h d ss) (smul h (opp d))).
    { unfold reconstruct_linrel.
      pose proof (@vector_space_commutative_group F (@eq F) zero one add mul sub div
        opp inv V (@eq V) vid vopp vadd smul HV) as hcg.
      pose proof (@associative V (@eq V) vadd (@monoid_is_associative V (@eq V) vadd vid
        (@group_monoid V (@eq V) vadd vid vopp
          (@commutative_group_group V (@eq V) vadd vid vopp hcg)))) as hassoc.
      pose proof (@right_identity V (@eq V) vadd vid (@monoid_is_right_identity V (@eq V)
        vadd vid (@group_monoid V (@eq V) vadd vid vopp
          (@commutative_group_group V (@eq V) vadd vid vopp hcg)))) as hrid.
      rewrite <-hassoc.
      pose proof (@vector_space_smul_distributive_fadd F (@eq F) zero one add mul
        sub div opp inv V (@eq V) vid vopp vadd smul HV) as hd.
      rewrite <-(hd d (opp d) h).
      assert (ha : add d (opp d) = zero) by field.
      rewrite ha.
      pose proof (@vector_space_field_zero F (@eq F) zero one add mul
        sub div opp inv V (@eq V) vid vopp vadd smul HV) as hz.
      rewrite (hz h), hrid; reflexivity. }
    (* Discharge the decidable-equality test in the verifier with [he]. *)
    simpl.
    match goal with
    | |- context [Vdec ?a ?b] => destruct (Vdec a b) as [_ | hne]; [reflexivity | exfalso; apply hne; exact he]
    end.
  Qed.

  (** Wrapper of [reconstruct_linrel_accepting] in the form used by
      verifiers: if [fs_verify_linrel] accepted, the reconstructed
      transcript is an accepting Okamoto transcript. The acceptance
      hypothesis is not actually needed (the conclusion holds
      unconditionally); see the file header. *)
  Theorem fs_verify_linrel_accepting : forall (n : nat) (H : V -> F) (gs : Vector.t V (2 + n)) (h : V)
    (d c : F) (ss : Vector.t F (2 + n)),
    fs_verify_linrel H gs h d c ss = true ->
    generalised_okamoto_accepting_conversation (gid := vid) (gop := vadd) (gpow := smul) (Gdec := Vdec) gs h
      (mk_sigma _ _ _ [reconstruct_linrel gs h d ss] [opp d] ss) = true.
  Proof. intros; apply reconstruct_linrel_accepting. Qed.

End FiatShamirLinRel.
