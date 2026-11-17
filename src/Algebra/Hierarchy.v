(** * Algebraic hierarchy: monoids, groups, rings, fields and vector spaces *)

(** This file defines the setoid-based algebraic hierarchy on which the
    whole development rests. Every structure is a type class parameterised by
    a carrier [T], an equivalence relation [eq] used in place of Leibniz
    equality, and the operations of the structure. The design follows the
    algebra hierarchy of fiat-crypto (the vendored copy lives under
    [src/Fiat/Algebra]): each axiom is its own singleton class
    ([is_associative], [is_left_inverse], ...) and each structure bundles
    the axioms together with [Proper] morphism facts for its operations, so
    that [setoid_rewrite] works with respect to [eq].

    The chain of structures is

    - [monoid]: associative operation with a two-sided identity;
    - [group] and [commutative_group]: a monoid with two-sided inverses;
    - [ring], [commutative_ring], [integral_domain] and [field] over one
      carrier with two operations;
    - [vector_space]: a commutative group [V] together with a field [F] and
      a scalar action [smul : V -> F -> V].

    The vector-space class is the central abstraction for the cryptography in
    [src/Crypto]: a cyclic group [G] of prime order [q] is treated as a
    vector space over [Z_q], with [vadd] the group operation and [smul g x]
    the exponentiation [g ^ x]. Note the argument order: the vector comes
    first and the scalar second, matching the notation [g ^ x].

    Elementary consequences of these axioms are proved in [Monoid.v],
    [Group.v], [Ring.v], [Integral_domain.v], [Field.v] and [Vector_space.v];
    product constructions are in [Product_space.v] and
    [Vector_product_space.v]. Concrete instances include prime fields and
    Schnorr groups ([src/Examples]) and the elliptic curves of
    [src/Curve/Ed25519.v] and [src/Curve/P256.v]. *)

From Stdlib Require Import
  Morphisms.

Local Close Scope nat_scope.
Local Close Scope type_scope.
Local Close Scope core_scope.

(** ** Structures *)

Section Algebra.

  (** *** One carrier, one operation

      Monoids and groups over a carrier [T] with equivalence [eq], binary
      operation [op], identity [id] and (for groups) inverse [inv]. *)

  Section OneTypeOneOp.

    (** The carrier, its equivalence, the operation and the identity
        element. All are implicit so that they are inferred from the class
        instance at use sites. *)
    Context
      {T : Type}
      {eq : T -> T -> Prop}
      {op : T -> T -> T}
      {id : T}.

    Local Infix "=" := eq : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.

    (** Associativity: [op x (op y z) = op (op x y) z]. *)
    Class is_associative :=
      associative : forall x y z,
        op x (op y z) = op (op x y) z.

    (** [id] is a left identity: [op id x = x]. *)
    Class is_left_identity :=
      left_identity : forall x, op id x = x.

    (** [id] is a right identity: [op x id = x]. *)
    Class is_right_identity :=
      right_identity : forall x, op x id = x.

    (** A monoid: an associative operation with a two-sided identity,
        where [eq] is an equivalence relation and [op] respects it. The
        field name [monoid_is_left_idenity] carries a historical typo and is
        kept for compatibility. *)
    Class monoid :=
    {
      monoid_is_associative : is_associative;
      monoid_is_left_idenity : is_left_identity;
      monoid_is_right_identity : is_right_identity;
      monoid_op_Proper: Proper (eq ==> eq ==> eq) op;
      monoid_Equivalence : Equivalence eq
    }.

    (** The monoid fields are registered as instances so that, for example,
        [Equivalence eq] and [Proper] facts are found automatically from a
        [monoid] hypothesis. *)
    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_idenity.
    Global Existing Instance monoid_is_right_identity.
    Global Existing Instance monoid_op_Proper.
    Global Existing Instance monoid_Equivalence.

    (** The inverse operation, used by the group classes below. *)
    Context {inv : T -> T}.

    (** [inv] is a left inverse: [op (inv x) x = id]. *)
    Class is_left_inverse :=
      left_inverse : forall x, op (inv x) x = id.

    (** [inv] is a right inverse: [op x (inv x) = id]. *)
    Class is_right_inverse :=
      right_inverse : forall x, op x (inv x) = id.

    (** A group: a monoid in which every element has a two-sided inverse
        and [inv] respects [eq]. *)
    Class group :=
    {
      group_monoid : monoid;
      group_is_left_inverse : is_left_inverse;
      group_is_right_inverse : is_right_inverse;
      group_inv_Proper : Proper (eq ==> eq) inv
    }.

    Global Existing Instance group_monoid.
    Global Existing Instance group_is_left_inverse.
    Global Existing Instance group_is_right_inverse.
    Global Existing Instance group_inv_Proper.

    (** Commutativity of [op]: [op x y = op y x]. *)
    Class is_commutative :=
      commutative : forall x y, op x y = op y x.

    (** An abelian group. In the cryptographic files this is the group [G]
        in which commitments and ciphertexts live. *)
    Class commutative_group :=
    {
      commutative_group_group : group;
      commutative_group_is_commutative : is_commutative
    }.

    Global Existing Instance commutative_group_group.
    Global Existing Instance commutative_group_is_commutative.

  End OneTypeOneOp.

  (** *** One carrier, two operations

      Rings, commutative rings, integral domains and fields. The additive
      structure is a [commutative_group] and the multiplicative one a
      [monoid]; subtraction and division are separate operations tied to
      [opp] and [inv] by defining equations, which keeps them computable
      in concrete instances. *)

  Section OneTypeTwoOp.

    (** Carrier, equivalence, constants and operations of a ring. *)
    Context
      {T : Type}
      {eq : T -> T -> Prop}
      {zero one : T}
      {opp : T -> T}
      {add : T -> T -> T}
      {sub : T -> T -> T}
      {mul : T -> T -> T}.

    Local Infix "=" := eq : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero.
    Local Notation "1" := one.
    Local Notation "- x" := (opp x).
    Local Infix "+" := add.
    Local Infix "-" := sub.
    Local Infix "*" := mul.

    (** Left distributivity: [x * (y + z) = x * y + x * z]. *)
    Class is_left_distributive :=
      left_distributive : forall x y z,
        x * (y + z) = x * y + x * z.

    (** Right distributivity: [(y + z) * x = y * x + z * x]. *)
    Class is_right_distributive :=
      right_distributive : forall x y z, (y + z) * x = y * x + z * x.

    (** A (not necessarily commutative) ring with unit: an abelian group
        under [add], a monoid under [mul], both distributive laws, the
        defining equation [x - y = x + opp y], and compatibility of [mul]
        and [sub] with [eq]. *)
    Class ring :=
    {
      ring_commutative_group_add :
        commutative_group (eq := eq) (op := add) (id := zero) (inv := opp);
      ring_monoid_mul : monoid (eq := eq) (op := mul) (id := one);
      ring_is_left_distributive : is_left_distributive;
      ring_is_right_distributive : is_right_distributive;
      ring_sub_definition : forall x y, x - y = x + opp y;
      ring_mul_Proper : Proper (eq ==> eq ==> eq) mul;
      ring_sub_Proper : Proper (eq ==> eq ==> eq) sub

    }.

    Global Existing Instance ring_commutative_group_add.
    Global Existing Instance ring_monoid_mul.
    Global Existing Instance ring_is_left_distributive.
    Global Existing Instance ring_is_right_distributive.
    Global Existing Instance ring_mul_Proper.
    Global Existing Instance ring_sub_Proper.

    (** A ring whose multiplication is commutative. *)
    Class commutative_ring :=
    {
      commutative_ring_ring : ring;
      commutative_ring_is_commutative : is_commutative (eq := eq) (op := mul)
    }.

    Global Existing Instance commutative_ring_ring.
    Global Existing Instance commutative_ring_is_commutative.

    (** No zero divisors: [x * y = 0 -> x = 0 \/ y = 0]. *)
    Class is_zero_product_zero_factor :=
      zero_product_zero_factor : forall x y, x * y = 0 -> x = 0 \/ y = 0.

    (** Non-triviality: [zero <> one]. *)
    Class is_zero_neq_one :=
      zero_neq_one : zero <> one.

    (** An integral domain: a non-trivial commutative ring without zero
        divisors. Every [field] is one (see [Field.v]). *)
    Class integral_domain :=
    {
      integral_domain_commutative_ring : commutative_ring;
      integral_domain_is_zero_product_zero_factor : is_zero_product_zero_factor;
      integral_domain_is_zero_neq_one : is_zero_neq_one
    }.

    Global Existing Instance integral_domain_commutative_ring.
    Global Existing Instance integral_domain_is_zero_product_zero_factor.
    Global Existing Instance integral_domain_is_zero_neq_one.

    (** Multiplicative inverse and division, used by [field]. [inv] is a
        total function; its value at [0] is unconstrained. *)
    Context
      {inv : T -> T}
      {div : T -> T -> T}.

    (** Every non-zero element has a left multiplicative inverse:
        [x <> 0 -> inv x * x = 1]. *)
    Class is_left_multiplicative_inverse :=
      left_multiplicative_inverse : forall x, x <> 0 -> (inv x) * x = 1.

    (** A field: a non-trivial commutative ring in which every non-zero
        element is invertible, with [div x y = x * inv y] and [inv], [div]
        compatible with [eq]. In the cryptographic files the field is
        [Z_q], the exponent (scalar) field of a prime-order group. *)
    Class field :=
    {
      field_commutative_ring : commutative_ring;
      field_is_left_multiplicative_inverse : is_left_multiplicative_inverse;
      field_is_zero_neq_one : is_zero_neq_one;
      field_div_definition : forall x y , div x y = x * inv y;
      field_inv_Proper : Proper (eq ==> eq) inv;
      field_div_Proper : Proper (eq ==> eq ==> eq) div
    }.

    Global Existing Instance field_commutative_ring.
    Global Existing Instance field_is_left_multiplicative_inverse.
    Global Existing Instance field_is_zero_neq_one.
    Global Existing Instance field_inv_Proper.
    Global Existing Instance field_div_Proper.

  End OneTypeTwoOp.

  (** *** Vector spaces

      A vector space [V] over a field [F]. The scalar action is written
      [v *s r] with the vector on the left. In cryptographic use [V] is a
      prime-order group [G] written multiplicatively, [vadd] is the group
      product and [v *s r] is the exponentiation [v ^ r]; the axioms below
      then read [g ^ 1 = g], [g ^ 0 = 1], [g ^ (r1 r2) = (g ^ r1) ^ r2],
      [g ^ (r1 + r2) = g ^ r1 · g ^ r2] and [(g h) ^ r = g ^ r · h ^ r]. *)

  Section VectorSpace.

    (** The scalar field and its operations. *)
    Context
      {F : Type}
      {eqf : F -> F -> Prop}
      {zero one : F}
      {add mul sub div : F -> F -> F}
      {opp inv : F -> F}.

    Local Notation "0" := zero.
    Local Notation "1" := one.
    Local Notation "- x" := (opp x).
    Local Infix "+" := add.
    Local Infix "*" := mul.
    Local Infix "-" := sub.
    Local Infix "/" := div.

    (** The vectors: carrier [V], equivalence [eqv], zero vector [vid],
        negation [vopp], addition [vadd] and scalar action [smul]. *)
    Context
      {V : Type}
      {eqv : V -> V -> Prop}
      {vid : V}
      {vopp : V -> V}
      {vadd : V -> V -> V}
      {smul : V -> F -> V}.

    Local Infix "=" := eqv : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "*s" := smul
      (at level 40).
    Local Infix "+v" := vadd
      (at level 50).

    (** Scaling by the field's one is the identity: [v *s 1 = v]. *)
    Class is_field_one :=
      field_one : forall v, v *s 1 = v.

    (** Scaling by the field's zero gives the zero vector: [v *s 0 = vid].
        This follows from the other axioms but is included for convenience. *)
    Class is_field_zero :=
      field_zero : forall v, v *s 0 = vid.

    (** Compatibility of the action with field multiplication:
        [v *s (r1 * r2) = (v *s r1) *s r2]. *)
    Class is_smul_associative_fmul :=
      smul_associative_fmul : forall r1 r2 v,
        v *s (r1 * r2) = (v *s r1) *s r2.

    (** Distributivity over field addition:
        [v *s (r1 + r2) = v *s r1 +v v *s r2]. *)
    Class is_smul_distributive_fadd :=
      smul_distributive_fadd : forall r1 r2 v,
        v *s (r1 + r2) = (v *s r1) +v (v *s r2).

    (** Distributivity over vector addition:
        [(v1 +v v2) *s r = v1 *s r +v v2 *s r]. *)
    Class is_smul_distributive_vadd :=
      smul_distributive_vadd : forall r v1 v2,
        (v1 +v v2) *s r = (v1 *s r) +v (v2 *s r).

    (** A vector space: an abelian group of vectors, a field of scalars,
        the five action axioms above and compatibility of [smul] with both
        equivalences. This is the class that the Sigma-protocol files assume
        of the group [G] and the exponent field [F]. *)
    Class vector_space :=
    {
      vector_space_commutative_group :
        commutative_group (eq := eqv) (op := vadd) (id := vid) (inv := vopp);
      vector_space_field :
        field (eq := eqf) (zero := zero) (one := one)
        (opp := opp) (add := add) (sub := sub) (mul := mul)
        (inv := inv) (div := div);
      vector_space_field_one : is_field_one;
      vector_space_field_zero : is_field_zero;
      vector_space_smul_associative_fmul : is_smul_associative_fmul;
      vector_space_smul_distributive_fadd : is_smul_distributive_fadd;
      vector_space_smul_distributive_vadd : is_smul_distributive_vadd;
      vector_space_smul_Proper : Proper (eqv ==> eqf ==> eqv) smul;
    }.

    Global Existing Instance vector_space_commutative_group.
    Global Existing Instance vector_space_field.
    Global Existing Instance vector_space_field_one.
    Global Existing Instance vector_space_field_zero.
    Global Existing Instance vector_space_smul_associative_fmul.
    Global Existing Instance vector_space_smul_distributive_fadd.
    Global Existing Instance vector_space_smul_distributive_vadd.
    Global Existing Instance vector_space_smul_Proper.

  End VectorSpace.

End Algebra.

(** ** A derived fact *)

Section ZeroNeqOne.
  (** Any carrier with an equivalence [eq] and [zero <> one]. *)
  Context
    {T eq zero one}
    {Hne: @is_zero_neq_one T eq zero one}
    {He : @Equivalence T eq}.

  (** The symmetric form of [zero_neq_one]: [one] is not equivalent to
      [zero]. *)
  Lemma one_neq_zero : not (eq one zero).
  Proof.
    intro HH;
    symmetry in HH.
    auto using zero_neq_one.
  Qed.
End ZeroNeqOne.
