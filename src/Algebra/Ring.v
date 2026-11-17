(** * Ring lemmas and the bridge to the standard-library ring tactic *)

(** This file develops the elementary theory of the [ring] and
    [commutative_ring] classes of [Hierarchy.v] and connects them to the
    Rocq standard library so that the [ring] and [field] tactics can be
    used on any instance of the hierarchy.

    - [Ncring_ops] and [Ncring_ring] make every [ring] an instance of the
      standard library's non-commutative ring class [Ncring.Ring], from
      which the basic identities ([ring_mul_0_l], [ring_mul_opp_r], ...)
      are inherited.
    - [Cring_commutative_ring] does the same for [Cring.Cring], and
      [ring_theory_for_stdlib_tactic] packages a commutative ring as a
      [Ring_theory.ring_theory] record, the argument expected by
      [Add Ring]. [Field.v] builds on it for [Add Field].
    - [of_nat] and [of_Z] are the canonical maps from [nat] and [Z] into
      any ring. *)
From Stdlib Require Import
  Ncring Cring ZArith
  PArith Morphisms Lia.
From Algebra Require Import
  Hierarchy Monoid Group.

(** ** Rings *)
Section Ring.

  (** An arbitrary (not necessarily commutative) ring. *)
  Context
    {T : Type}
    {eq : T -> T -> Prop}
    {zero one : T}
    {opp : T -> T}
    {add sub mul : T -> T -> T}
    {Hr : @ring T eq zero one opp add sub mul}.

  Local Infix "=" := eq : type_scope.
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero.
  Local Notation "1" := one.
  Local Infix "+" := add.
  Local Infix "-" := sub.
  Local Infix "*" := mul.

  (** The operations of the ring, packaged for the standard library's
      [Ncring] interface. The class has no fields beyond its parameters,
      so the instance is defined by an empty proof. *)
  Global Instance Ncring_ops :
    @Ncring.Ring_ops T 0 1 add mul sub opp eq.
  Defined.

  (** Every [ring] of the hierarchy satisfies the [Ncring.Ring] axioms.
      Each goal is discharged by the matching field of the [ring] class. *)
  Global Instance Ncring_ring :
    @Ncring.Ring T 0 1 add mul sub opp eq Ncring_ops.
  Proof.
    split; try (typeclasses eauto).
    + intros ?.
      rewrite left_identity;
      reflexivity.
    + intros ? ?.
      rewrite commutative;
      reflexivity.
    + intros ? ? ?.
      rewrite associative;
      reflexivity.
    + intros ?;
      rewrite left_identity;
      reflexivity.
    + intros ?;
      rewrite right_identity;
      reflexivity.
    + intros ? ? ?;
      rewrite associative;
      reflexivity.
    + intros ? ? ?;
      rewrite right_distributive;
      reflexivity.
    + intros ? ? ?;
      rewrite left_distributive;
      reflexivity.
    + intros ? ?;
      rewrite ring_sub_definition;
      reflexivity.
    + intros ?;
      rewrite right_inverse;
      reflexivity.
  Defined.

  (** Zero annihilates on the left: [0 * x = 0]. *)
  Lemma ring_mul_0_l : forall x, 0 * x = 0.
  Proof.
    apply Ncring.ring_mul_0_l.
  Qed.

  (** Zero annihilates on the right: [x * 0 = 0]. *)
  Lemma ring_mul_0_r : forall x, x * 0 = 0.
  Proof.
    apply Ncring.ring_mul_0_r.
  Qed.

  (** Subtracting from zero is negation: [0 - x = opp x]. *)
  Lemma ring_sub_0_l : forall x, 0 - x = opp x.
  Proof.
    intros ?.
    rewrite ring_sub_definition.
    rewrite commutative.
    apply Ncring.ring_add_0_r.
  Qed.

  (** Negation commutes out of the right factor:
      [x * opp y = opp (x * y)]. *)
  Lemma ring_mul_opp_r : forall x y, x * opp y = opp (x * y).
  Proof.
    intros ? ?.
    symmetry.
    apply Ncring.ring_opp_mul_r.
  Qed.

  (** Negation commutes out of the left factor:
      [opp x * y = opp (x * y)]. *)
  Lemma ring_mul_opp_l : forall x y, opp x * y = opp (x * y).
  Proof.
    intros ? ?.
    symmetry.
    apply Ncring.ring_opp_mul_l.
  Qed.

  (** [opp x = 0 <-> x = 0], an instance of [group_inv_id_iff] for the
      additive group. *)
  Lemma ring_opp_zero_iff : forall x, opp x = 0 <-> x = 0.
  Proof.
    apply Group.group_inv_id_iff.
  Qed.

  (** Multiplication distributes over subtraction on the left:
      [x * (y - z) = x * y - x * z]. *)
  Global Instance is_left_distributive_sub :
    is_left_distributive (eq := eq)(add := sub)(mul := mul).
  Proof.
    intros ? ? ?.
    rewrite !ring_sub_definition.
    rewrite
      left_distributive,
      ring_mul_opp_r;
    reflexivity.
  Qed.

  (** Multiplication distributes over subtraction on the right:
      [(y - z) * x = y * x - z * x]. *)
  Global Instance is_right_distributive_sub :
    is_right_distributive (eq := eq)(add := sub)(mul := mul).
  Proof.
    intros ? ? ?.
    repeat rewrite ring_sub_definition.
    rewrite
      right_distributive,
      ring_mul_opp_l;
    reflexivity.
  Qed.

  (** A difference is zero exactly when the operands are equal:
      [x - y = 0 <-> x = y]. *)
  Lemma ring_sub_zero_iff :
    forall x y, x - y = 0 <-> x = y.
  Proof.
    intros ? ?;
    split;
    intros H.
    rewrite ring_sub_definition,
    group_inv_unique,
    group_inv_inv in H.
    exact H.
    rewrite H,
    ring_sub_definition,
    right_inverse;
    reflexivity.
  Qed.

  (** Distinct elements have a non-zero difference. Used, for example,
      when dividing by a difference of two challenges in special-soundness
      extractors. *)
  Lemma ring_neq_sub_neq_zero :
    forall x y, x <> y -> x-y <> 0.
  Proof.
    intros ? ? H Hsub.
    pose proof (proj1 (ring_sub_zero_iff _ _) Hsub) as Ht.
    unfold not in H.
    apply H in Ht.
    inversion Ht.
  Qed.

  (** In a ring without zero divisors, [x * y = 0 <-> x = 0 \/ y = 0]. *)
  Lemma ring_zero_product_iff_zero_factor
    {Hzpzf : @is_zero_product_zero_factor T eq zero mul} :
    forall x y : T, x * y = 0 <-> x = 0 \/ y = 0.
  Proof.
    intros ? ?; split; intros H.
    apply zero_product_zero_factor; exact H.
    destruct H; rewrite H;
     [apply ring_mul_0_l | apply ring_mul_0_r].
  Qed.

  (** In a ring without zero divisors, a product is non-zero exactly when
      both factors are: [x * y <> 0 <-> x <> 0 /\ y <> 0]. *)
  Lemma nonzero_product_iff_nonzero_factor
    {Hzpzf : @is_zero_product_zero_factor T eq zero mul} :
    forall x y : T,  x * y <> 0 <-> x <> 0 /\ y <> 0.
  Proof.
    intros ? ?;
    split;
    intros H.
    split;
    intro Ht; apply H;
    rewrite Ht;
    [rewrite ring_mul_0_l | rewrite ring_mul_0_r];
    reflexivity.
    intro Ht.
    destruct H as [H1 H2].
    apply ring_zero_product_iff_zero_factor in Ht.
    destruct Ht as [Ht | Ht].
    apply H1 in Ht.
    exact Ht.
    apply H2 in Ht.
    exact Ht.
  Qed.

End Ring.

(** ** Commutative rings and the [ring] tactic *)
Section Cring.

  (** An arbitrary commutative ring. *)
  Context
    {T eq zero one opp add sub mul}
    {Hcring : @commutative_ring T eq zero one opp add sub mul}.

  (** Every [commutative_ring] is a standard-library [Cring.Cring]; the
      only extra obligation is commutativity of multiplication. *)
  Global Instance Cring_commutative_ring :
   @Cring.Cring T zero one add mul sub opp eq Ncring_ops Ncring_ring.
  Proof.
    intros ? ?.
    apply commutative.
  Defined.

  (** A commutative ring of the hierarchy satisfies the standard library's
      [ring_theory]. Client files use it as
      [Add Ring r : (ring_theory_for_stdlib_tactic ...)] to enable the
      [ring] tactic modulo [eq]. *)
  Lemma ring_theory_for_stdlib_tactic :
    Ring_theory.ring_theory zero one add mul sub opp eq.
  Proof.
    split; intros; try (typeclasses eauto).
    + apply left_identity.
    + apply commutative.
    + apply associative.
    + apply left_identity.
    + apply commutative.
    + apply associative.
    + apply right_distributive.
    + apply ring_sub_definition.
    + apply right_inverse.
  Qed.

End Cring.

(** ** Embedding the integers *)
Section of_Z.

  Local Open Scope Z_scope.
  (** An arbitrary ring [R]; [Req] is written [=] locally. *)
  Context {R Req Rzero Rone Ropp Radd Rsub Rmul}
        {Rring : @ring R Req Rzero Rone Ropp Radd Rsub Rmul}.
  Local Infix "=" := Req : type_scope.

  (** The image of a natural number in [R], computed by unary recursion:
      [of_nat (S n) = 1 + of_nat n]. *)
  Fixpoint of_nat (n : nat) : R :=
    match n with
    | 0%nat => Rzero
    | S n' => Radd Rone (of_nat n')
    end.

  (** The image of an integer in [R]: positive integers via [of_nat],
      negative ones as the additive inverse of the image of their absolute
      value. *)
  Definition of_Z (n : Z) : R :=
    match n with
    | Z0 => Rzero
    | Zpos p => of_nat (Pos.to_nat p)
    | Zneg p => Ropp (of_nat (Pos.to_nat p))
    end.

  (** [of_Z 0] is the ring zero (by computation). *)
  Lemma of_Z_0 : of_Z 0 = Rzero.
  Proof. reflexivity. Qed.

  (** The successor written on the right:
      [of_nat (n + 1) = of_nat n + 1]. *)
  Lemma of_nat_add : forall n,
    of_nat (Nat.add n 1) = Radd (of_nat n) Rone.
  Proof.
    unfold of_nat.
    induction n.
    + simpl. rewrite commutative; reflexivity.
    + simpl. rewrite IHn, associative; reflexivity.
  Qed.

End of_Z.
