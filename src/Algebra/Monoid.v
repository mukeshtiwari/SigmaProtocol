(** * Elementary monoid lemmas *)

(** Cancellation and inverse-uniqueness facts that hold in any [monoid]
    (see [Hierarchy.v]) once suitable one-sided inverses are supplied as
    hypotheses. They are stated for monoids rather than groups so that they
    can be reused for the additive and multiplicative structures of rings
    and fields; [Group.v] specialises them by plugging in the group inverse.
    All statements are up to the setoid equivalence [eq]. *)
From Stdlib Require Import
  Setoid Morphisms Utf8.
From Algebra Require Import
  Hierarchy.

(** ** Lemmas over an arbitrary monoid *)
Section Monoid.

  (** A monoid [(T, eq, op, id)]; [op] is written [*] locally. *)
  Context
    {T : Type}
    {eq : T -> T -> Prop}
    {op : T -> T -> T}
    {id : T}
    {Hmonoid : @monoid T eq op id}.

  Local Infix "=" := eq : type_scope.
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "*" := op.

  (** Left cancellation by an element [z] that has a left inverse [iz]
      ([iz * z = id]): [z * x = z * y <-> x = y]. *)
  Lemma monoid_cancel_left z iz (Hinv : op iz z = id) :
    forall x y, (z * x) = (z * y) <-> x = y.
  Proof.
    intros ? ?;
    split; intros H.
    assert (Hcut : (iz * (z * x))  = (iz * (z * y))).
    rewrite H. reflexivity.
    rewrite !(@monoid_is_associative T eq op id Hmonoid) in Hcut.
    rewrite Hinv in Hcut.
    rewrite !monoid_is_left_idenity in Hcut.
    exact Hcut.
    rewrite H.
    reflexivity.
  Qed.

  (** Right cancellation by an element [z] that has a right inverse [iz]
      ([z * iz = id]): [x * z = y * z <-> x = y]. *)
  Lemma monoid_cancel_right z iz (Hinv : op z iz = id) :
    forall x y, x * z = y * z <-> x = y.
  Proof.
    intros ? ?; split; intro H.
    assert (op (op x z) iz = op (op y z) iz) as Hcut.
    rewrite H; reflexivity.
    rewrite <- !(@monoid_is_associative T eq op id Hmonoid) in Hcut.
    rewrite Hinv in Hcut.
    rewrite !monoid_is_right_identity in Hcut.
    exact Hcut.
    rewrite H; reflexivity.
  Qed.

  (** If both [a] and [b] are equivalent to [id], so is [a * b]. *)
  Lemma monoid_both_identity :
    forall a b, a = id ∧ b = id -> a * b = id.
  Proof.
    intros ? ? H.
    destruct H as [H₁ H₂];
    rewrite H₁.
    rewrite monoid_is_left_idenity.
    exact H₂.
  Qed.

  (** Uniqueness of inverses: if [a] has the left inverse [b]
      ([b * a = id]) and [b] has the left inverse [c] ([c * b = id]), then
      [c = a]. Used for [inv (inv x) = x] in groups. *)
  Lemma monoid_inv_inv a b c : b * a = id -> c * b = id -> c = a.
  Proof.
    intros H₁ H₂.
    assert (Ht : c * (b * a) = c * id)
      by (rewrite H₁; reflexivity).
    rewrite (@monoid_is_associative T eq op id Hmonoid) in Ht.
    rewrite H₂,
      monoid_is_left_idenity,
      monoid_is_right_identity in Ht.
    symmetry in Ht.
    exact Ht.
  Qed.

  (** Inverse of a product: if [a] is a left inverse of [x] and [b] a
      left inverse of [y], then [b * a] is a left inverse of [x * y]. *)
  Lemma monoid_inv_op x y a b :
    a * x = id -> b * y = id -> (b * a) * (x * y) = id.
  Proof.
    intros Hx Hy.
    assert(Ht : (a * (x * y)) = ((a * x) * y))
      by (rewrite associative; reflexivity).
    rewrite <- associative.
    rewrite Ht, Hx, left_identity.
    exact Hy.
  Qed.

End Monoid.
