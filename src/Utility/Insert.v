(* Insertion into and removal from a vector at a position. Used by the
   zero-knowledge bijections of the OR-style compositions, where the
   prover derives one challenge from the others and places it at the
   index of the relation it knows. *)
From Stdlib Require Import Vector Fin Utf8 Lia Arith Peano_dec.
From Utility Require Import Util.
Import VectorNotations EqNotations.

Section Insert.
  Context {A : Type}.

  (* insert a at position i of v, giving a vector one longer *)
  Fixpoint insert_at (k : nat) : Vector.t A k -> Fin.t (S k) -> A -> Vector.t A (S k) :=
    match k with
    | 0 => fun v i a => [a]
    | S k' => fun v i a => 
        Fin.caseS' i (fun _ => Vector.t A (S (S k'))) 
          (a :: v) (fun j => hd v :: insert_at k' (tl v) j a)
    end.

  (* remove the element at position i *)
  Fixpoint remove_at (k : nat) : Vector.t A (S k) -> Fin.t (S k) -> Vector.t A k :=
    match k with
    | 0 => fun v i => []
    | S k' => fun v i => 
        Fin.caseS' i (fun _ => Vector.t A (S k')) 
          (tl v) (fun j => hd v :: remove_at k' (tl v) j)
    end.

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

  Lemma nth_insert_at : forall k (v : Vector.t A k) (i : Fin.t (S k)) (a : A),
    Vector.nth (insert_at k v i a) i = a.
  Proof.
    induction k as [| k ih]; intros v i a.
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; 
      [reflexivity | inversion j].
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn; 
      [reflexivity | apply ih].
  Qed.

  Lemma insert_at_F1 : forall k (w : Vector.t A k) (a : A),
    insert_at k w Fin.F1 a = a :: w.
  Proof.
    intros k w a; destruct k; cbn; [rewrite (vector_inv_0 w); reflexivity | reflexivity].
  Qed.

  Lemma replace_insert_at : forall k (v : Vector.t A k) (i : Fin.t (S k)) (a b : A),
    replace (insert_at k v i a) i b = insert_at k v i b.
  Proof.
    induction k as [| k ih]; intros v i a b.
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; 
      [reflexivity | inversion j].
    + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn; 
      [reflexivity | f_equal; apply ih].
  Qed.

  (* --- transport along an equality of lengths --- *)

  Lemma rew_cons : forall (N M : nat) (e : S N = S M) (a : A) (v : Vector.t A N),
    rew [Vector.t A] e in (a :: v) = a :: rew [Vector.t A] (eq_add_S _ _ e) in v.
  Proof.
    intros N M e a v.
    rewrite (UIP_nat _ _ e (f_equal S (eq_add_S _ _ e))).
    generalize (eq_add_S N M e) as e'; intros e'.
    destruct e'; reflexivity.
  Qed.

  Lemma rew_FS : forall (N M : nat) (e : S N = S M) (i : Fin.t N),
    rew [Fin.t] e in (Fin.FS i) = Fin.FS (rew [Fin.t] (eq_add_S _ _ e) in i).
  Proof.
    intros N M e i.
    rewrite (UIP_nat _ _ e (f_equal S (eq_add_S _ _ e))).
    generalize (eq_add_S N M e) as e'; intros e'.
    destruct e'; reflexivity.
  Qed.

  (* A vector with an element in the middle, transported to length S (m + k),
     is an insertion at the transported index. *)
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

  Lemma rew_to_nat : forall (N M : nat) (e : N = M) (i : Fin.t N),
    proj1_sig (Fin.to_nat (rew [Fin.t] e in i)) = proj1_sig (Fin.to_nat i).
  Proof. intros N M e i; destruct e; reflexivity. Qed.

  Lemma fin_eq_of_to_nat : forall (N : nat) (i j : Fin.t N),
    proj1_sig (Fin.to_nat i) = proj1_sig (Fin.to_nat j) -> i = j.
  Proof.
    intros N i j h; apply Fin.to_nat_inj; exact h.
  Qed.

End Insert.

Section Zip.
  Context {A B C : Type}.

  (* --- zip_with, insertion and append --- *)

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
