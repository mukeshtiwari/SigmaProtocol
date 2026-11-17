(** * Field lemmas and the bridge to the [field] tactic *)

(** Elementary consequences of the [field] class of [Hierarchy.v]. The main
    item is [field_theory_for_stdlib_tactic], which packages a field as a
    standard-library [Field_theory.field_theory] record; virtually every
    cryptographic file uses it as

    [[
    Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp
      add mul sub inv div vector_space_field).
    ]]

    to obtain the [field] and [ring] tactics on the scalar field [Z_q]. The
    remaining lemmas are small identities about inverses and division, and
    the instance [integral_domain], which shows that a field with decidable
    equality has no zero divisors. *)
From Stdlib Require Import
  Morphisms Lia Field_theory
  Field_tac.
From Algebra Require Import
  Hierarchy Monoid Group
  Ring Integral_domain.

(** ** Fields *)
Section Field.

  (** An arbitrary field with inverse [inv] and division [div]. *)
  Context
    {T : Type}
    {eq : T -> T -> Prop}
    {zero one : T}
    {opp : T -> T}
    {add mul sub : T -> T -> T}
    {inv : T -> T}
    {div : T -> T -> T}
    {Hfield: @field T eq zero one opp add sub mul inv div}.
  Local Infix "=" := eq : type_scope.
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero.
  Local Notation "1" := one.
  Local Infix "+" := add.
  Local Infix "*" := mul.

  (** A field of the hierarchy satisfies the standard library's
      [field_theory]: the underlying commutative ring satisfies
      [ring_theory], [1 <> 0], [div x y = x * inv y], and
      [x <> 0 -> inv x * x = 1]. *)
  Lemma field_theory_for_stdlib_tactic :
    Field_theory.field_theory 0 1 add mul sub opp div inv eq.
  Proof.
    constructor.
    apply ring_theory_for_stdlib_tactic.
    intro Hn.
    symmetry in Hn.
    pose proof (zero_neq_one (eq:=eq)) as Ha.
    eapply Ha in Hn; assumption.
    apply field_div_definition.
    apply left_multiplicative_inverse.
  Qed.

  (** The additive inverse cancels on the left: [opp x + x = 0]. *)
  Lemma field_zero_iff_left :
    forall x, (opp x) + x = zero.
  Proof.
    intros ?; rewrite left_inverse.
    reflexivity.
  Qed.

  (** The additive inverse cancels on the right: [x + opp x = 0]. *)
  Lemma field_zero_iff_right :
    forall x, x + (opp x) = zero.
  Proof.
    intros ?; rewrite right_inverse;
    reflexivity.
  Qed.

  (** Right multiplicative inverse, from the left one by commutativity:
      [x <> 0 -> x * inv x = 1]. *)
  Lemma field_right_multiplicative_inverse :
    forall x : T, x <> 0 -> mul x (inv x) = 1.
  Proof.
    intros ? Hx.
    rewrite commutative.
    eapply left_multiplicative_inverse;
    assumption.
  Qed.

  (** Uniqueness of the multiplicative inverse, left form:
      [y * x = 1 -> y = inv x]. The hypothesis forces [x <> 0], since
      otherwise [y * x = 0 <> 1]. *)
  Lemma field_left_inv_unique :
  forall x y, y * x = one -> y = inv x.
  Proof.
    intros ? ? Hxy.
    assert (Ht : y * x * inv x = inv x).
    rewrite
      Hxy,
      left_identity;
    reflexivity.
    rewrite
      <-associative,
      field_right_multiplicative_inverse,
      right_identity in Ht; trivial.
    intros Hx.
    rewrite Hx, ring_mul_0_r in Hxy.
    apply field_is_zero_neq_one in Hxy.
    exact Hxy.
  Qed.

  (** Uniqueness of the multiplicative inverse, right form:
      [x * y = 1 -> y = inv x]. *)
  Lemma field_right_inv_unique :
    forall x y, x * y = one -> y = inv x.
  Proof.
    intros ? ? H.
    rewrite commutative in H.
    apply field_left_inv_unique.
    exact H.
  Qed.

  (** Dividing by one is the identity: [div x 1 = x]. *)
  Lemma field_div_one:
    forall x, div x one = x.
  Proof.
    intros ?.
    rewrite field_div_definition.
    rewrite <-(field_left_inv_unique 1 1);
    apply monoid_is_right_identity.
  Qed.

  (** For non-zero [y], [x * y = y] holds exactly when [x = 1]. *)
  Lemma field_mul_cancel_l_iff :
    forall x y, y <> 0 -> (x * y = y <-> x = one).
  Proof.
    intros x y Ht.
    split; intros H₁.
    + rewrite <-(field_right_multiplicative_inverse y) by assumption.
      rewrite <-H₁ at 1;
      rewrite <-associative.
      rewrite field_right_multiplicative_inverse by assumption.
      rewrite right_identity.
      reflexivity.
    + rewrite H₁;
      apply left_identity.
  Qed.

  (** The product of non-zero elements is non-zero. Proved directly from
      the inverse axiom: if [x * y = 0] then
      [1 = (x * inv x) * (y * inv y) = (x * y) * inv x * inv y = 0]. *)
  Lemma field_mul_not_zero :
    forall x y : T, x <> 0 -> y <> 0 -> x * y <> 0.
  Proof.
    intros x y Hx Hy Hn.
    apply field_right_multiplicative_inverse in Hx.
    apply field_right_multiplicative_inverse in Hy.
    assert (Ht: x * inv x * y * inv y = 1).
    rewrite Hx, left_identity, Hy; reflexivity.
    assert(Hab: x * inv x * y * inv y = x * y * inv x * inv y).
      rewrite <-!associative.
    assert (Htt: inv x * (y * inv y) = (y * inv y) * inv x).
      rewrite commutative; reflexivity.
    rewrite Htt, <-associative.
    assert (Httt: inv x * inv y = inv y * inv x)
      by (rewrite commutative; reflexivity).
    rewrite Httt.
    reflexivity.
    rewrite Hab in Ht.
    clear Hab.
    rewrite Hn in Ht.
    rewrite !ring_mul_0_l in Ht.
    apply zero_neq_one in Ht.
    exact Ht.
  Qed.

  (** For the remaining results, equality in the field is assumed
      decidable, which is the case for all concrete instances. *)
  Context {eq_dec : forall x y : T, {x = y} + {x <> y}}.

  (** A field with decidable equality has no zero divisors: case analysis on
      whether [x] and [y] are zero, using [field_mul_not_zero] in the
      remaining case. *)
  Global Instance is_mul_nonzero_nonzero :
    @is_zero_product_zero_factor T eq 0 mul.
  Proof.
    intros x y Hxy.
    assert (Hx: {x = 0} + {x <> 0}) by apply eq_dec.
    assert (Hy: {y = 0} + {y <> 0}) by apply eq_dec.
    destruct Hx as [Hx | Hx];
      destruct Hy as [Hy | Hy].
    left; exact Hx.
    left; exact Hx.
    right; exact Hy.
    pose proof (field_mul_not_zero _ _ Hx Hy).
    rewrite Hxy in H.
    unfold not in H.
    assert (Hf : 0 = 0) by reflexivity.
    pose proof (H Hf) as HF;
    inversion HF.
  Qed.

  (** A field with decidable equality is an [integral_domain]. Note that
      the instance reuses the name of the class from [Hierarchy.v]. *)
  Global Instance integral_domain :
    @integral_domain T eq zero one opp add sub mul.
  Proof.
    split;
    eauto using field_commutative_ring,
    field_is_zero_neq_one,
    is_mul_nonzero_nonzero.
  Qed.

End Field.
