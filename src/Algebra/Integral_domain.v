(** * Integral domains *)

(** A short file connecting the [integral_domain] class of [Hierarchy.v]
    to the standard library's [Integral_domain.Integral_domain] class
    (instance [Intdom]), which is what the standard [nsatz] tactic needs,
    together with the non-zero-product characterisation
    [nonzero_product_iff_nonzero_factors]. [Field.v] shows that every field
    with decidable equality is an integral domain. *)
From Stdlib Require Import
  Morphisms Integral_domain
  Ncring Cring.
From Algebra Require Import
  Hierarchy Monoid Group
  Ring.

(** ** Lemmas and the standard-library instance *)
Section IntegralDomain.

  (** An arbitrary integral domain. *)
  Context
    {T eq zero one opp add sub mul}
    {Hi:@integral_domain T eq zero one opp add sub mul}.

  (** A product is non-zero iff both factors are non-zero; a restatement of
      [nonzero_product_iff_nonzero_factor] from [Ring.v] in terms of the
      integral-domain class. *)
  Lemma nonzero_product_iff_nonzero_factors :
      forall x y : T,
      ~eq (mul x y) zero <-> ~eq x zero /\ ~eq y zero.
  Proof.
    setoid_rewrite ring_zero_product_iff_zero_factor.
    intuition.
  Qed.

  (** Every [integral_domain] of the hierarchy is an integral domain in the
      sense of the standard library (no zero divisors and [1 <> 0]), on top
      of the [Cring] instance from [Ring.v]. *)
  Global Instance Intdom :
    @Integral_domain.Integral_domain
      T zero one add mul sub opp eq _ _ _.
  Proof.
    split.
    apply zero_product_zero_factor.
    apply one_neq_zero.
  Defined.

End IntegralDomain.
