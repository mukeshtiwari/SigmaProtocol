(* The product of two vector spaces over the same field is a vector space,
   with componentwise operations. Used to express Chaum-Pedersen-style
   statements ((α, β) = (g, y)^r) as Schnorr statements in the product
   group, so that the Or composition of the library applies to
   disjunctions of such statements over different ciphertexts, as in
   Belenios's proofs of possibly-blank votes. *)

From Stdlib Require Import Morphisms Utf8 RelationClasses.
From Algebra Require Import Hierarchy.

Section Product.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {V1 : Type} {vid1 : V1} {vopp1 : V1 -> V1} {vadd1 : V1 -> V1 -> V1} {smul1 : V1 -> F -> V1}
    {V2 : Type} {vid2 : V2} {vopp2 : V2 -> V2} {vadd2 : V2 -> V2 -> V2} {smul2 : V2 -> F -> V2}
    {H1 : @vector_space F (@eq F) zero one add mul sub div opp inv V1 (@eq V1) vid1 vopp1 vadd1 smul1}
    {H2 : @vector_space F (@eq F) zero one add mul sub div opp inv V2 (@eq V2) vid2 vopp2 vadd2 smul2}.

  Definition pid : V1 * V2 := (vid1, vid2).
  Definition popp (x : V1 * V2) : V1 * V2 := (vopp1 (fst x), vopp2 (snd x)).
  Definition padd (x y : V1 * V2) : V1 * V2 := (vadd1 (fst x) (fst y), vadd2 (snd x) (snd y)).
  Definition psmul (x : V1 * V2) (r : F) : V1 * V2 := (smul1 (fst x) r, smul2 (snd x) r).

  Definition prod_dec (d1 : forall x y : V1, {x = y} + {x <> y})
    (d2 : forall x y : V2, {x = y} + {x <> y}) :
    forall x y : V1 * V2, {x = y} + {x <> y}.
  Proof.
    intros [a b] [c d].
    destruct (d1 a c) as [h | h]; [destruct (d2 b d) as [h' | h'] |].
    + left; subst; reflexivity.
    + right; intro e; apply h'; exact (f_equal snd e).
    + right; intro e; apply h; exact (f_equal fst e).
  Defined.

  Local Ltac pair_law :=
    intros; unfold pid, popp, padd, psmul; cbn [fst snd]; f_equal.

  Global Instance prod_comm_group :
    @commutative_group (V1 * V2) (@eq (V1 * V2)) padd pid popp.
  Proof.
    refine {|
      commutative_group_group := {|
        group_monoid := {|
          monoid_is_associative := _;
          monoid_is_left_idenity := _;
          monoid_is_right_identity := _;
          monoid_op_Proper := _;
          monoid_Equivalence := eq_equivalence |};
        group_is_left_inverse := _;
        group_is_right_inverse := _;
        group_inv_Proper := _ |};
      commutative_group_is_commutative := _ |}.
    all: try (repeat intro; subst; reflexivity).
    all: hnf; intros [a b]; try intros [c d]; try intros [e f].
    all: pair_law.
    all: first [apply associative | apply left_identity | apply right_identity |
                apply left_inverse | apply right_inverse | apply commutative].
  Qed.

  Global Instance prod_vspace :
    @vector_space F (@eq F) zero one add mul sub div opp inv
      (V1 * V2) (@eq (V1 * V2)) pid popp padd psmul.
  Proof.
    refine {|
      vector_space_commutative_group := prod_comm_group;
      vector_space_field := vector_space_field;
      vector_space_field_one := _;
      vector_space_field_zero := _;
      vector_space_smul_associative_fmul := _;
      vector_space_smul_distributive_fadd := _;
      vector_space_smul_distributive_vadd := _;
      vector_space_smul_Proper := _ |}.
    all: try (repeat intro; subst; reflexivity).
    all: hnf; intros.
    + destruct v; pair_law; apply field_one.
    + destruct v; pair_law; apply field_zero.
    + destruct v; pair_law; apply smul_associative_fmul.
    + destruct v; pair_law; apply smul_distributive_fadd.
    + destruct v1, v2; pair_law; apply smul_distributive_vadd.
  Qed.

End Product.
