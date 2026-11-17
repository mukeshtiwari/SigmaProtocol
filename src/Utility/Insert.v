(** * Inserting into and removing from length-indexed vectors *)

(** Utilities for [Vector.t A k] indexed by [Fin.t]: [insert_at k v i a]
    places [a] at position [i] of [v], producing a vector of length [S k],
    and [remove_at] is its inverse. They are used by the generalised
    OR-composition of Sigma protocols ([Crypto/OrSigmaGen.v]) and by
    [Crypto/EncProof.v], where the challenge for the real branch is inserted
    at the secret index [i] among the simulated challenges, so that all
    challenges sum to the verifier's challenge.

    Besides the round-trip lemmas ([remove_insert], [insert_remove]) the
    file contains transport lemmas for [rew] along equalities of lengths
    ([rew_cons], [rew_FS], [rew_app_cons]), using uniqueness of identity
    proofs on [nat] ([UIP_nat], which holds without axioms because equality
    on [nat] is decidable), and compatibility of [zip_with] with insertion
    and concatenation. *)
From Stdlib Require Import Vector Fin Utf8 Lia Arith Peano_dec.
From Utility Require Import Util.
Import VectorNotations EqNotations.

(** ** Insertion and removal *)
Section Insert.
  (** The element type. *)
  Context {A : Type}.

  (** [insert_at k v i a]: the vector of length [S k] that has [a] at index
      [i] and the entries of [v], in order, at the other indices. Defined by
      recursion on [k] and case analysis on [i] ([Fin.caseS']); inserting at
      [F1] conses. *)
  Fixpoint insert_at (k : nat) : Vector.t A k -> Fin.t (S k) -> A -> Vector.t A (S k) :=
    match k with
    | 0 => fun v i a => [a]
    | S k' => fun v i a =>
        Fin.caseS' i (fun _ => Vector.t A (S (S k')))
          (a :: v) (fun j => hd v :: insert_at k' (tl v) j a)
    end.

  (** [remove_at k v i]: delete the entry at index [i] from a vector of
      length [S k]. *)
  Fixpoint remove_at (k : nat) : Vector.t A (S k) -> Fin.t (S k) -> Vector.t A k :=
    match k with
    | 0 => fun v i => []
    | S k' => fun v i =>
        Fin.caseS' i (fun _ => Vector.t A (S k'))
          (tl v) (fun j => hd v :: remove_at k' (tl v) j)
    end.

  (** Removing what was just inserted gives back the original vector. *)
  Lemma remove_insert : forall k (v : Vector.t A k) (i : Fin.t (S k)) (a : A),
    remove_at k (insert_at k v i a) i = v.
  Proof.
    induction k as [| k ih]; intros v i a.
    + rewrite (vector_inv_0 v); reflexivity.
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn.
      * reflexivity.
      * destruct (vector_inv_S v) as (b & w & hv); subst; cbn.
        f_equal; apply ih.
  Qed.

  (** Re-inserting the removed entry gives back the original vector. *)
  Lemma insert_remove : forall k (v : Vector.t A (S k)) (i : Fin.t (S k)),
    insert_at k (remove_at k v i) i (Vector.nth v i) = v.
  Proof.
    induction k as [| k ih]; intros v i.
    + destruct (vector_inv_S v) as (b & w & hv);
      rewrite (vector_inv_0 w) in hv; subst.
      destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst;
      [reflexivity | inversion j].
    + destruct (vector_inv_S v) as (b & w & hv); subst.
      destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn.
      * reflexivity.
      * f_equal; apply ih.
  Qed.

  (** The inserted entry is found at the insertion index. *)
  Lemma nth_insert_at : forall k (v : Vector.t A k) (i : Fin.t (S k)) (a : A),
    Vector.nth (insert_at k v i a) i = a.
  Proof.
    induction k as [| k ih]; intros v i a.
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst;
      [reflexivity | inversion j].
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn;
      [reflexivity | apply ih].
  Qed.

  (** Insertion at the first index is [cons]. *)
  Lemma insert_at_F1 : forall k (w : Vector.t A k) (a : A),
    insert_at k w Fin.F1 a = a :: w.
  Proof.
    intros k w a; destruct k; cbn; [rewrite (vector_inv_0 w); reflexivity | reflexivity].
  Qed.

  (** Overwriting the inserted entry ([replace] from the standard
      library) is the same as inserting the new value. *)
  Lemma replace_insert_at : forall k (v : Vector.t A k) (i : Fin.t (S k)) (a b : A),
    replace (insert_at k v i a) i b = insert_at k v i b.
  Proof.
    induction k as [| k ih]; intros v i a b.
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst;
      [reflexivity | inversion j].
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn;
      [reflexivity | f_equal; apply ih].
  Qed.

  (** Transporting a cons along [e : S N = S M] transports the tail along
      the derived equality [N = M]. *)
  Lemma rew_cons : forall (N M : nat) (e : S N = S M) (a : A) (v : Vector.t A N),
    rew [Vector.t A] e in (a :: v) = a :: rew [Vector.t A] (eq_add_S _ _ e) in v.
  Proof.
    intros N M e a v.
    rewrite (UIP_nat _ _ e (f_equal S (eq_add_S _ _ e))).
    generalize (eq_add_S N M e) as e'; intros e'.
    destruct e'; reflexivity.
  Qed.

  (** Transporting [FS i] along [e : S N = S M] transports [i] along the
      derived equality [N = M]. *)
  Lemma rew_FS : forall (N M : nat) (e : S N = S M) (i : Fin.t N),
    rew [Fin.t] e in (Fin.FS i) = Fin.FS (rew [Fin.t] (eq_add_S _ _ e) in i).
  Proof.
    intros N M e i.
    rewrite (UIP_nat _ _ e (f_equal S (eq_add_S _ _ e))).
    generalize (eq_add_S N M e) as e'; intros e'.
    destruct e'; reflexivity.
  Qed.

  (** Appending [y :: w] to [v] and transporting along
      [m + S k = S (m + k)] is the same as inserting [y] at index [m] (that
      is, [Fin.R m F1] transported) into [v ++ w]. *)
  Lemma rew_app_cons : forall m k (v : Vector.t A m) (w : Vector.t A k) (y : A)
    (e : m + S k = S (m + k)),
    rew [Vector.t A] e in (v ++ y :: w) =
    insert_at (m + k) (v ++ w) (rew [Fin.t] e in Fin.R m (Fin.F1 : Fin.t (S k))) y.
  Proof.
    induction m as [| m ih]; intros k v w y e.
    + rewrite (vector_inv_0 v).
      rewrite (UIP_nat _ _ e eq_refl); cbn.
      rewrite insert_at_F1; reflexivity.
    + destruct (vector_inv_S v) as (b & v' & hv); subst; cbn.
      rewrite rew_cons, rew_FS; cbn.
      f_equal; apply ih.
  Qed.

  (** Transport along a length equality does not change the numeric value
      of a [Fin.t] index. *)
  Lemma rew_to_nat : forall (N M : nat) (e : N = M) (i : Fin.t N),
    proj1_sig (Fin.to_nat (rew [Fin.t] e in i)) = proj1_sig (Fin.to_nat i).
  Proof. intros N M e i; destruct e; reflexivity. Qed.

  (** Indices with the same numeric value are equal. *)
  Lemma fin_eq_of_to_nat : forall (N : nat) (i j : Fin.t N),
    proj1_sig (Fin.to_nat i) = proj1_sig (Fin.to_nat j) -> i = j.
  Proof.
    intros N i j h; apply Fin.to_nat_inj; exact h.
  Qed.

End Insert.

(** ** Interaction with [zip_with] *)
Section Zip.
  (** Element types of the two inputs and the output. *)
  Context {A B C : Type}.

  (** Zipping two vectors in which entries were inserted at the same index
      is inserting the zipped entry into the zipped vectors. *)
  Lemma zip_with_insert_at (f : A -> B -> C) :
    forall k (v : Vector.t A k) (w : Vector.t B k) (i : Fin.t (S k)) (a : A) (b : B),
    zip_with f (insert_at k v i a) (insert_at k w i b) =
    insert_at k (zip_with f v w) i (f a b).
  Proof.
    induction k as [| k ih]; intros v w i a b.
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst;
      [rewrite (vector_inv_0 v), (vector_inv_0 w); reflexivity | inversion j].
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn; [reflexivity |].
      destruct (vector_inv_S v) as (x & v' & hv).
      destruct (vector_inv_S w) as (y & w' & hw).
      subst; cbn; f_equal; apply ih.
  Qed.

  (** [zip_with] distributes over concatenation of equal-length
      blocks. *)
  Lemma zip_with_app (f : A -> B -> C) :
    forall m k (v1 : Vector.t A m) (v2 : Vector.t A k) (w1 : Vector.t B m) (w2 : Vector.t B k),
    zip_with f (v1 ++ v2) (w1 ++ w2) = zip_with f v1 w1 ++ zip_with f v2 w2.
  Proof.
    induction m as [| m ih]; intros k v1 v2 w1 w2.
    + rewrite (vector_inv_0 v1), (vector_inv_0 w1); reflexivity.
    + destruct (vector_inv_S v1) as (x & v1' & hv).
      destruct (vector_inv_S w1) as (y & w1' & hw).
      subst; cbn; f_equal; apply ih.
  Qed.

End Zip.
