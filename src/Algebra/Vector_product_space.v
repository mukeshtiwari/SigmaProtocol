(** * The vector space [V ^ n] of length-indexed vectors *)

(** For a vector space [V] over a field [F] (with Leibniz equality), the
    type [Vector.t V n] of length-[n] vectors with componentwise operations
    is again a vector space over [F] ([vec_vspace]). This lets the generic
    Sigma-protocol machinery be applied to tuples of group elements, for
    example to [n] commitments or ciphertexts at once (it is used by
    [Crypto/OkamotoRows.v], [Crypto/BayerGrothZK.v], [Crypto/MultiExp.v],
    [Crypto/UProve.v], [Crypto/BBSSharp.v] and the Schulze front ends).

    The file also provides the two dependent-pattern-matching inversion
    lemmas [vector_inv_0] and [vector_inv_S], used for induction on the
    length, decidable equality [vec_dec], the componentwise group and
    action laws, and [nth]-projection lemmas. *)
From Stdlib Require Import Morphisms Utf8 RelationClasses Vector VectorEq Bool.
From Algebra Require Import Hierarchy.
Import VectorNotations.

(** ** Inversion of length-indexed vectors *)
Section Inv.
  (** Element type of the vectors. *)
  Context {R : Type}.

  (** Every vector of length [0] is [nil]. Proved by a dependent match so
      that the term reduces (it is closed with [Defined]). *)
  Lemma vector_inv_0 (v : Vector.t R 0) : v = @Vector.nil R.
  Proof.
    refine
      (match v as v' in Vector.t _ n' return
        (match n' return Vector.t R n' -> Type with
         | 0 => fun (ve : Vector.t R 0) => ve = []
         | _ => fun _ => IDProp
         end v')
      with
      | @Vector.nil _ => eq_refl
      end).
  Defined.

  (** Every vector of length [S n] is a cons [h :: t]; the head and tail
      are returned as computational data. *)
  Lemma vector_inv_S : forall {n : nat} (v : Vector.t R (S n)),
    {h : R & {t : Vector.t R n | v = h :: t}}.
  Proof.
    intros n v.
    refine
      (match v as v' in Vector.t _ n' return
        (match n' return Vector.t R n' -> Type with
         | 0 => fun _ => IDProp
         | S n'' => fun (ea : Vector.t R (S n'')) =>
             {h : R & {t : Vector.t R n'' | ea = h :: t}}
         end v')
      with
      | cons _ h _ t => existT _ h (exist _ t eq_refl)
      end).
  Defined.
End Inv.

(** ** Componentwise vector-space structure on [Vector.t V n] *)
Section VectorProduct.

  (** A vector space [V] over [F], both with Leibniz equality. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  (** Componentwise operations on [Vector.t V n]: the zero vector
      [vec_id n] (all entries [vid]), negation [vec_opp], addition
      [vec_add] and scalar action [vec_smul x r], which scales every entry
      by the same scalar [r]. *)
  Definition vec_id (n : nat) : Vector.t V n := Vector.const vid n.
  Definition vec_opp {n : nat} (x : Vector.t V n) : Vector.t V n := Vector.map vopp x.
  Definition vec_add {n : nat} (x y : Vector.t V n) : Vector.t V n := Vector.map2 vadd x y.
  Definition vec_smul {n : nat} (x : Vector.t V n) (r : F) : Vector.t V n :=
    Vector.map (fun v => smul v r) x.

  (** Decidable equality on [Vector.t V n] from decidable equality on [V],
      by induction on [n]. Transparent so that it computes. *)
  Definition vec_dec (d : forall x y : V, {x = y} + {x <> y}) {n : nat} :
    forall x y : Vector.t V n, {x = y} + {x <> y}.
  Proof.
    induction n as [| n ih]; intros x y.
    + left; rewrite (vector_inv_0 x), (vector_inv_0 y); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      destruct (vector_inv_S y) as (b & ys & ->).
      destruct (d a b) as [e | ne]; [destruct (ih xs ys) as [e' | ne'] |].
      - left; subst; reflexivity.
      - right; intro h; apply ne'; exact (f_equal Vector.tl h).
      - right; intro h; apply ne; exact (f_equal Vector.hd h).
  Defined.

  (** *** Componentwise laws

      Each lemma below is proved by induction on the length [n], peeling
      off the head with [vector_inv_S] and applying the corresponding law
      of [V] to it:

      - [vec_add_assoc], [vec_add_comm]: associativity and commutativity;
      - [vec_add_id_l], [vec_add_id_r]: [vec_id n] is a two-sided identity;
      - [vec_add_opp_l], [vec_add_opp_r]: [vec_opp] gives two-sided
        inverses;
      - [vec_smul_one], [vec_smul_zero]: scaling by [1] and [0];
      - [vec_smul_assoc]: [x *s (r * s) = (x *s r) *s s];
      - [vec_smul_fadd]: [x *s (r + s) = x *s r + x *s s];
      - [vec_smul_vadd]: [(x + y) *s r = x *s r + y *s r]. *)
  Lemma vec_add_assoc : forall n (x y z : Vector.t V n),
    vec_add x (vec_add y z) = vec_add (vec_add x y) z.
  Proof.
    induction n as [| n ih]; intros x y z.
    + rewrite (vector_inv_0 x), (vector_inv_0 y), (vector_inv_0 z); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      destruct (vector_inv_S y) as (b & ys & ->).
      destruct (vector_inv_S z) as (c & zs & ->).
      unfold vec_add in *; cbn; f_equal; [apply associative | apply ih].
  Qed.

  Lemma vec_add_id_l : forall n (x : Vector.t V n), vec_add (vec_id n) x = x.
  Proof.
    induction n as [| n ih]; intros x.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_add, vec_id in *; cbn; f_equal; [apply left_identity | apply ih].
  Qed.

  Lemma vec_add_id_r : forall n (x : Vector.t V n), vec_add x (vec_id n) = x.
  Proof.
    induction n as [| n ih]; intros x.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_add, vec_id in *; cbn; f_equal; [apply right_identity | apply ih].
  Qed.

  Lemma vec_add_opp_l : forall n (x : Vector.t V n), vec_add (vec_opp x) x = vec_id n.
  Proof.
    induction n as [| n ih]; intros x.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_add, vec_opp, vec_id in *; cbn; f_equal; [apply left_inverse | apply ih].
  Qed.

  Lemma vec_add_opp_r : forall n (x : Vector.t V n), vec_add x (vec_opp x) = vec_id n.
  Proof.
    induction n as [| n ih]; intros x.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_add, vec_opp, vec_id in *; cbn; f_equal; [apply right_inverse | apply ih].
  Qed.

  Lemma vec_add_comm : forall n (x y : Vector.t V n), vec_add x y = vec_add y x.
  Proof.
    induction n as [| n ih]; intros x y.
    + rewrite (vector_inv_0 x), (vector_inv_0 y); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      destruct (vector_inv_S y) as (b & ys & ->).
      unfold vec_add in *; cbn; f_equal; [apply commutative | apply ih].
  Qed.

  Lemma vec_smul_one : forall n (x : Vector.t V n), vec_smul x one = x.
  Proof.
    induction n as [| n ih]; intros x.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_smul in *; cbn; f_equal; [apply field_one | apply ih].
  Qed.

  Lemma vec_smul_zero : forall n (x : Vector.t V n), vec_smul x zero = vec_id n.
  Proof.
    induction n as [| n ih]; intros x.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_smul, vec_id in *; cbn; f_equal; [apply field_zero | apply ih].
  Qed.

  Lemma vec_smul_assoc : forall n (x : Vector.t V n) (r s : F),
    vec_smul x (mul r s) = vec_smul (vec_smul x r) s.
  Proof.
    induction n as [| n ih]; intros x r s.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_smul in *; cbn; f_equal; [apply smul_associative_fmul | apply ih].
  Qed.

  Lemma vec_smul_fadd : forall n (x : Vector.t V n) (r s : F),
    vec_smul x (add r s) = vec_add (vec_smul x r) (vec_smul x s).
  Proof.
    induction n as [| n ih]; intros x r s.
    + rewrite (vector_inv_0 x); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      unfold vec_smul, vec_add in *; cbn; f_equal; [apply smul_distributive_fadd | apply ih].
  Qed.

  Lemma vec_smul_vadd : forall n (x y : Vector.t V n) (r : F),
    vec_smul (vec_add x y) r = vec_add (vec_smul x r) (vec_smul y r).
  Proof.
    induction n as [| n ih]; intros x y r.
    + rewrite (vector_inv_0 x), (vector_inv_0 y); reflexivity.
    + destruct (vector_inv_S x) as (a & xs & ->).
      destruct (vector_inv_S y) as (b & ys & ->).
      unfold vec_smul, vec_add in *; cbn; f_equal; [apply smul_distributive_vadd | apply ih].
  Qed.

  (** *** Instances *)

  (** [Vector.t V n] is a commutative group under [vec_add]. *)
  Global Instance vec_comm_group (n : nat) :
    @commutative_group (Vector.t V n) (@eq (Vector.t V n)) vec_add (vec_id n) vec_opp.
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
    all: hnf; intros.
    + apply vec_add_assoc.
    + apply vec_add_id_l.
    + apply vec_add_id_r.
    + apply vec_add_opp_l.
    + apply vec_add_opp_r.
    + apply vec_add_comm.
  Qed.

  (** [Vector.t V n] is a vector space over [F] under [vec_smul]. *)
  Global Instance vec_vspace (n : nat) :
    @vector_space F (@eq F) zero one add mul sub div opp inv
      (Vector.t V n) (@eq (Vector.t V n)) (vec_id n) vec_opp vec_add vec_smul.
  Proof.
    refine {|
      vector_space_commutative_group := vec_comm_group n;
      vector_space_field := vector_space_field;
      vector_space_field_one := _;
      vector_space_field_zero := _;
      vector_space_smul_associative_fmul := _;
      vector_space_smul_distributive_fadd := _;
      vector_space_smul_distributive_vadd := _;
      vector_space_smul_Proper := _ |}.
    all: try (repeat intro; subst; reflexivity).
    all: hnf; intros.
    + apply vec_smul_one.
    + apply vec_smul_zero.
    + apply vec_smul_assoc.
    + apply vec_smul_fadd.
    + apply vec_smul_vadd.
  Qed.

  (** *** Projections

      The [i]-th entry of a sum, a scaled vector and the zero vector. *)
  Lemma nth_vec_add : forall n (x y : Vector.t V n) (i : Fin.t n),
    (vec_add x y)[@i] = vadd x[@i] y[@i].
  Proof. intros; unfold vec_add; exact (Vector.nth_map2 vadd x y i i i eq_refl eq_refl). Qed.

  Lemma nth_vec_smul : forall n (x : Vector.t V n) (r : F) (i : Fin.t n),
    (vec_smul x r)[@i] = smul x[@i] r.
  Proof. intros; unfold vec_smul; exact (Vector.nth_map (fun v => smul v r) x i i eq_refl). Qed.

  Lemma nth_vec_id : forall n (i : Fin.t n), (vec_id n)[@i] = vid.
  Proof. intros; unfold vec_id; apply Vector.const_nth. Qed.

End VectorProduct.
