(* Multi-exponentiation ∏_j gs_j^{xs_j} in any vector space, in the form
   used by the generalised Okamoto protocol (Crypto/Okamoto.v), with its
   basic algebra: cons, append, identity bases, and the equality with the
   fold Okamoto uses. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Utility Require Import Util.
Import VectorNotations.

Section MultiExp.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}.


  Context
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  Lemma const_S : forall {A : Type} (a : A) (k : nat), Vector.const a (S k) = a :: Vector.const a k.
  Proof. reflexivity. Qed.

  Lemma map2_cons : forall {A B C : Type} (f : A -> B -> C) (k : nat) (a : A) (v : Vector.t A k)
    (b : B) (w : Vector.t B k),
    Vector.map2 f (a :: v) (b :: w) = f a b :: Vector.map2 f v w.
  Proof. reflexivity. Qed.

  Lemma map_const : forall {A B : Type} (f : A -> B) (a : A) (k : nat),
    Vector.map f (Vector.const a k) = Vector.const (f a) k.
  Proof.
    intros A B f a k; induction k as [| k ih]; [reflexivity |].
    rewrite const_S; cbn [Vector.map]; rewrite ih, const_S; reflexivity.
  Qed.

  (* ∏_j gs_j^{xs_j}, written as Okamoto writes it *)
  Definition mexp {k : nat} (gs : Vector.t V k) (xs : Vector.t F k) : V :=
    Vector.fold_right (fun '(g, x) acc => vadd (smul g x) acc) (zip_with pair gs xs) vid.

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

  (* the Okamoto form of the same product *)
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

  Lemma mexp_nil : forall (gs : Vector.t V 0) (xs : Vector.t F 0), mexp gs xs = vid.
  Proof. intros; rewrite (vector_inv_0 gs), (vector_inv_0 xs); reflexivity. Qed.

  Lemma mexp_cons : forall (k : nat) (g : V) (gs : Vector.t V k) (x : F) (xs : Vector.t F k),
    mexp (g :: gs) (x :: xs) = vadd (smul g x) (mexp gs xs).
  Proof. reflexivity. Qed.

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

  (* bases that are all the identity contribute nothing *)
  Lemma mexp_const_vid : forall (k : nat) (xs : Vector.t F k), mexp (Vector.const vid k) xs = vid.
  Proof.
    induction k as [| k ih]; intros xs.
    + apply mexp_nil.
    + destruct (vector_inv_S xs) as (x & xs' & ->).
      rewrite const_S, mexp_cons, ih, smul_vid, vid_l; reflexivity.
  Qed.

  Lemma mexp_single : forall (g : V) (x : F), mexp [g] [x] = smul g x.
  Proof. intros; rewrite mexp_cons, mexp_nil, vid_r; reflexivity. Qed.


End MultiExp.
