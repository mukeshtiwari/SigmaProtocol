(** * Multi-exponentiation in a vector space *)

(** The multi-exponentiation [∏_j gs_j ^ xs_j] (written additively, the
    linear combination [Σ_j xs_j · gs_j]) of a vector of bases [gs] by a
    vector of exponents [xs], in an arbitrary [F]-vector space [V]. When [V]
    is a prime-order group this is the left-hand side of Okamoto and
    Pedersen-style equations; when [V] is [F] itself it is an inner product.

    The file defines [mexp] and proves its basic algebra: the empty and cons
    cases, splitting over vector append, identity bases, the singleton case,
    and the equality with the fold of pointwise exponentiations used in
    Okamoto-style protocols. It also proves [smul_vid] ([vid ^ r = vid]).
    It is used by [OkamotoRows], [UProve], [BBSSharp], [ShuffleTWSound],
    the Bayer–Groth files and the Schulze frontends. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Utility Require Import Util.
Import VectorNotations.

(** ** Definition and algebra of [mexp] *)
Section MultiExp.

  (** The scalar field [F]; no field axioms are needed in this file. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}.

  (** An [F]-vector space [V] with zero [vid], negation [vopp], addition
      [vadd] and scalar multiplication [smul]. *)
  Context
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  (** [Vector.const a (k + 1) = a :: Vector.const a k], by computation. *)
  Lemma const_S : forall {A : Type} (a : A) (k : nat), Vector.const a (S k) = a :: Vector.const a k.
  Proof. reflexivity. Qed.

  (** [Vector.map2] on two cons cells, by computation. *)
  Lemma map2_cons : forall {A B C : Type} (f : A -> B -> C) (k : nat) (a : A) (v : Vector.t A k)
    (b : B) (w : Vector.t B k),
    Vector.map2 f (a :: v) (b :: w) = f a b :: Vector.map2 f v w.
  Proof. reflexivity. Qed.

  (** Mapping over a constant vector gives a constant vector. *)
  Lemma map_const : forall {A B : Type} (f : A -> B) (a : A) (k : nat),
    Vector.map f (Vector.const a k) = Vector.const (f a) k.
  Proof.
    intros A B f a k; induction k as [| k ih]; [reflexivity |].
    rewrite const_S; cbn [Vector.map]; rewrite ih, const_S; reflexivity.
  Qed.

  (** [mexp gs xs = Σ_j smul gs_j xs_j], computed as a right fold over the
      zipped vector, ending in [vid]. *)
  Definition mexp {k : nat} (gs : Vector.t V k) (xs : Vector.t F k) : V :=
    Vector.fold_right (fun '(g, x) acc => vadd (smul g x) acc) (zip_with pair gs xs) vid.

  (** Projections of the commutative-group and distributivity axioms of
      [V] out of [HV]. *)
  Local Notation vassoc := (@associative V (@eq V) vadd (@monoid_is_associative V (@eq V) vadd vid
    (@group_monoid V (@eq V) vadd vid vopp (@commutative_group_group V (@eq V) vadd vid vopp
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv V (@eq V)
        vid vopp vadd smul HV))))).
  Local Notation vid_l := (@left_identity V (@eq V) vadd vid (@monoid_is_left_idenity V (@eq V) vadd vid
    (@group_monoid V (@eq V) vadd vid vopp (@commutative_group_group V (@eq V) vadd vid vopp
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv V (@eq V)
        vid vopp vadd smul HV))))).
  Local Notation vid_r := (@right_identity V (@eq V) vadd vid (@monoid_is_right_identity V (@eq V) vadd vid
    (@group_monoid V (@eq V) vadd vid vopp (@commutative_group_group V (@eq V) vadd vid vopp
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv V (@eq V)
        vid vopp vadd smul HV))))).
  Local Notation vcomm := (@commutative V (@eq V) vadd (@commutative_group_is_commutative V (@eq V) vadd vid vopp
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv V (@eq V)
        vid vopp vadd smul HV))).
  Local Notation vinv_r := (@right_inverse V (@eq V) vadd vid vopp (@group_is_right_inverse V (@eq V) vadd vid vopp
    (@commutative_group_group V (@eq V) vadd vid vopp
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv V (@eq V)
        vid vopp vadd smul HV)))).
  Local Notation vdistr := (@vector_space_smul_distributive_vadd F (@eq F) zero one add mul sub div opp inv
    V (@eq V) vid vopp vadd smul HV).

  (** Scaling the zero vector gives the zero vector: [smul vid r = vid].
      Proof: [smul vid r = smul vid r + smul vid r] by distributivity, then
      cancel. *)
  Lemma smul_vid : forall r : F, smul vid r = vid.
  Proof.
    intro r.
    assert (h : smul vid r = vadd (smul vid r) (smul vid r)).
    { rewrite <-(vdistr r vid vid), vid_l; reflexivity. }
    assert (h2 : vadd (smul vid r) (vopp (smul vid r)) =
      vadd (vadd (smul vid r) (smul vid r)) (vopp (smul vid r))).
    { rewrite <-h; reflexivity. }
    rewrite vinv_r, <-vassoc, vinv_r, vid_r in h2. symmetry; exact h2.
  Qed.

  (** The fold [Σ_j (gs_j ^ xs_j)] over [zip_with smul gs xs], the form
      in which Okamoto-style protocols write the product, equals
      [mexp gs xs]. *)
  Lemma mexp_okamoto : forall (k : nat) (gs : Vector.t V k) (xs : Vector.t F k),
    Vector.fold_right (fun gr acc => vadd gr acc) (zip_with (fun g r => smul g r) gs xs) vid =
    mexp gs xs.
  Proof.
    induction k as [| k ih]; intros gs xs.
    + rewrite (vector_inv_0 gs), (vector_inv_0 xs); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      unfold mexp in *; cbn; f_equal; apply ih.
  Qed.

  (** The empty multi-exponentiation is [vid]. *)
  Lemma mexp_nil : forall (gs : Vector.t V 0) (xs : Vector.t F 0), mexp gs xs = vid.
  Proof. intros; rewrite (vector_inv_0 gs), (vector_inv_0 xs); reflexivity. Qed.

  (** Cons rule: [mexp (g :: gs) (x :: xs) = g ^ x · mexp gs xs]. *)
  Lemma mexp_cons : forall (k : nat) (g : V) (gs : Vector.t V k) (x : F) (xs : Vector.t F k),
    mexp (g :: gs) (x :: xs) = vadd (smul g x) (mexp gs xs).
  Proof. reflexivity. Qed.

  (** Append rule: [mexp (gs₁ ++ gs₂) (xs₁ ++ xs₂)] is the product of the
      two partial multi-exponentiations. *)
  Lemma mexp_app : forall (k1 k2 : nat) (gs1 : Vector.t V k1) (gs2 : Vector.t V k2)
    (xs1 : Vector.t F k1) (xs2 : Vector.t F k2),
    mexp (gs1 ++ gs2) (xs1 ++ xs2) = vadd (mexp gs1 xs1) (mexp gs2 xs2).
  Proof.
    induction k1 as [| k1 ih]; intros.
    + rewrite (vector_inv_0 gs1), (vector_inv_0 xs1); cbn [Vector.append].
      rewrite mexp_nil, vid_l; reflexivity.
    + destruct (vector_inv_S gs1) as (g & gs1' & ->).
      destruct (vector_inv_S xs1) as (x & xs1' & ->).
      cbn [Vector.append].
      etransitivity; [apply (mexp_cons (k1 + k2) g (gs1' ++ gs2) x (xs1' ++ xs2)) |].
      rewrite ih, (mexp_cons k1 g gs1' x xs1'), vassoc; reflexivity.
  Qed.

  (** If every base is [vid], the multi-exponentiation is [vid]. *)
  Lemma mexp_const_vid : forall (k : nat) (xs : Vector.t F k), mexp (Vector.const vid k) xs = vid.
  Proof.
    induction k as [| k ih]; intros xs.
    + apply mexp_nil.
    + destruct (vector_inv_S xs) as (x & xs' & ->).
      rewrite const_S, mexp_cons, ih, smul_vid, vid_l; reflexivity.
  Qed.

  (** Singleton rule: [mexp [g] [x] = g ^ x]. *)
  Lemma mexp_single : forall (g : V) (x : F), mexp [g] [x] = smul g x.
  Proof. intros; rewrite mexp_cons, mexp_nil, vid_r; reflexivity. Qed.

End MultiExp.
