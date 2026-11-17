(** * Basic vector-space lemmas *)

(** Consequences of the [vector_space] class of [Hierarchy.v]. Read with
    the cryptographic convention ([V] a prime-order group [G] written
    multiplicatively, [smul g x] the exponentiation [g ^ x], [F = Z_q]),
    the lemmas say:

    - [connection_between_vopp_and_fopp]: [(g ^ x)⁻¹ = g ^ (-x)];
    - [smul_pow_up] and [smul_pow_mul]: [(g ^ x) ^ r = g ^ (x r) = g ^ (r x)];
    - [vid_identity]: [1 ^ r = 1];
    - [gid_power_zero]: [g ^ r = 1] implies [g = 1] or [r = 0].

    These identities are used throughout the Sigma-protocol, ElGamal and
    shuffle files when rearranging verification equations. *)
From Stdlib Require Import
  Morphisms Lia Utf8  setoid_ring.Field.
From Algebra Require Import
  Hierarchy Monoid Group
  Ring Integral_domain
  Field.

(** ** Lemmas *)
Section Vector_Space.

  (** The scalar field [F] and its operations. *)
  Context
    {F : Type}
    {eqf : F -> F -> Prop}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.

  (** A vector space [V] over [F]. The [Add Field] command below enables
      the [field] tactic on scalars. *)
  Context
    {V : Type}
    {eqv : V -> V -> Prop}
    {vid : V} {vopp : V -> V}
    {vadd : V -> V -> V} {smul : V -> F -> V}
    {Hvec: @vector_space F eqf zero one add mul
      sub div opp inv V eqv vid vopp vadd smul}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eqf zero one opp add mul sub inv div vector_space_field).

  Local Infix "=" := eqv : type_scope.
  Local Infix "=f=" := eqf (at level 70)  : type_scope.
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "*s" := smul (at level 40).
  Local Infix "+v" := vadd (at level 50).
  Local Notation "0" := zero.
  Local Notation "1" := one.
  Local Infix "+" := add.
  Local Infix "-" := sub.
  Local Infix "*" := mul.

  (** The additive inverse of a scaled vector is scaling by the negated
      scalar: [vopp (u *s v) = u *s (opp v)]. Proof: right-cancel by
      [u *s v] and use [u *s (opp v + v) = u *s 0 = vid]. *)
  Lemma connection_between_vopp_and_fopp :
    forall u v, vopp (u *s v) = u *s (opp v).
  Proof.
    intros ? ?.
    eapply group_cancel_right with (z := smul u v).
    rewrite group_is_left_inverse,
     <-(@vector_space_smul_distributive_fadd F eqf zero one add mul sub div
      opp inv V eqv vid vopp vadd smul),
      field_zero_iff_left,
      vector_space_field_zero;
      try reflexivity;
      exact Hvec.
  Qed.

  (** Scaling twice multiplies scalars: [(g *s x) *s r = g *s (x * r)]. *)
  Lemma smul_pow_up :
    forall g x r, (g *s x) *s r = g *s (mul x r).
  Proof.
    intros ? ? ?.
    rewrite (@vector_space_smul_associative_fmul F eqf);
    try reflexivity; exact Hvec.
  Qed.

  (** The same with the scalar product commuted:
      [(g *s x) *s r = g *s (r * x)]. *)
  Lemma smul_pow_mul :
    forall g x r, smul (smul g x) r = smul g (mul r x).
  Proof.
    intros ? ? ?.
    rewrite smul_pow_up, commutative;
    reflexivity.
  Qed.

  (** Scaling the zero vector gives the zero vector: [vid *s r = vid].
      Proof: [vid *s r = (vid +v vid) *s r = vid *s r +v vid *s r], then
      cancel one copy by adding its inverse. *)
  Theorem vid_identity : ∀ (r : F), vid *s r = vid.
  Proof.
    intros *.
    pose proof @vector_space_smul_distributive_vadd F eqf
    zero one add mul sub div opp inv V eqv vid vopp vadd smul
    Hvec r vid vid as ha.
    destruct Hvec.
    destruct vector_space_commutative_group,
    commutative_group_group, group_monoid.
    unfold is_left_identity in monoid_is_left_idenity.
    pose proof @monoid_is_left_idenity vid as hb.
    rewrite hb in ha.
    (* Cancel [vr = vid *s r] from [vr = vr +v vr] by adding [vopp vr]
       on the left of both sides. *)
    remember (vid *s r) as vr.
    assert (hc : vadd (vopp vr) vr = vadd (vopp vr) (vr +v vr)).
    rewrite <-ha. reflexivity.
    remember (vopp vr) as w.
    rewrite associative in hc.
    rewrite Heqw in hc.
    unfold is_left_inverse in group_is_left_inverse.
    rewrite group_is_left_inverse, monoid_is_left_idenity  in hc.
    rewrite hc.
    reflexivity.
  Qed.

  (** In a vector space over a field with decidable equality, if
      [g *s r = vid] then [g = vid] or [r = 0]. For [r <> 0] one computes
      [g = g *s (r * inv r) = (g *s r) *s inv r = vid *s inv r = vid].
      Used in [Frontend/Approval.v]. *)
  Theorem gid_power_zero {Fdec : ∀ (x y : F), {eqf x y} + {~eqf x y}} : forall (g : V) (r : F),
    smul g r = vid -> (g = vid) ∨ (eqf r zero).
  Proof.
    intros * ha.
    destruct (Fdec r zero) as [hb | hb].
    +
      right. exact hb.
    +
      left.
      assert (hc : (r * inv r) =f= one).
      field. exact hb.
      assert (hd : g = smul g one).
      rewrite field_one; reflexivity.
      rewrite <-hc, <-smul_pow_up, ha in hd.
      rewrite vid_identity in hd.
      exact hd.
  Qed.

End Vector_Space.
