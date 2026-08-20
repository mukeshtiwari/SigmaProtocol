From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition.

Import VectorNotations.

(*
  Wire serialization of composed transcripts (Milestone H3).

  A transcript is flattened to a list of tagged field/group
  elements (inl for scalars, inr for points); decoding is driven by
  the statement tree r, whose shape (dimensions and combiners) tells
  the decoder exactly how many elements to read at each node.  The
  round-trip theorem serialize_deserialize is what a verified
  network layer needs: decode (encode t ++ rest) = Some (t, rest).
*)
Section Serialization.

  Context
    {F : Type}
    {G : Type}.

  Definition wire : Type := list (F + G).

  Fixpoint read_points (m : nat) (l : wire) :
    option (Vector.t G m * wire) :=
    match m with
    | 0 => Some ([], l)
    | S m' =>
        match l with
        | List.cons (inr g) l' =>
            match read_points m' l' with
            | Some (v, l'') => Some (g :: v, l'')
            | None => None
            end
        | _ => None
        end
    end.

  Fixpoint read_scalars (n : nat) (l : wire) :
    option (Vector.t F n * wire) :=
    match n with
    | 0 => Some ([], l)
    | S n' =>
        match l with
        | List.cons (inl f) l' =>
            match read_scalars n' l' with
            | Some (v, l'') => Some (f :: v, l'')
            | None => None
            end
        | _ => None
        end
    end.

  Definition write_points {m : nat} (v : Vector.t G m) : wire :=
    List.map inr (Vector.to_list v).

  Definition write_scalars {n : nat} (v : Vector.t F n) : wire :=
    List.map inl (Vector.to_list v).

  Fixpoint encode (r : @comp_rel G) :
    comp_transcript r -> wire :=
    match r with
    | Leaf m n _ _ => fun t =>
        List.app (write_points (fst t)) (write_scalars (snd t))
    | CAnd rl rr => fun t =>
        List.app (encode rl (fst t)) (encode rr (snd t))
    | COr rl rr => fun t =>
        List.app (encode rl (fst (fst t)))
          (List.app (encode rr (snd (fst t)))
            (List.cons (inl (snd t)) List.nil))
    end.

  Fixpoint decode (r : @comp_rel G) (l : wire) :
    option (comp_transcript r * wire) :=
    match r with
    | Leaf m n _ _ =>
        match read_points m l with
        | Some (comm, l1) =>
            match read_scalars n l1 with
            | Some (res, l2) => Some ((comm, res), l2)
            | None => None
            end
        | None => None
        end
    | CAnd rl rr =>
        match decode rl l with
        | Some (tl, l1) =>
            match decode rr l1 with
            | Some (tr, l2) => Some ((tl, tr), l2)
            | None => None
            end
        | None => None
        end
    | COr rl rr =>
        match decode rl l with
        | Some (tl, l1) =>
            match decode rr l1 with
            | Some (tr, l2) =>
                match l2 with
                | List.cons (inl c1) l3 => Some ((tl, tr, c1), l3)
                | _ => None
                end
            | None => None
            end
        | None => None
        end
    end.

  Lemma read_write_points :
    ∀ (m : nat) (v : Vector.t G m) (rest : wire),
    read_points m (List.app (write_points v) rest) = Some (v, rest).
  Proof.
    induction m as [|m ih]; intros *.
    +
      rewrite (vector_inv_0 v).
      reflexivity.
    +
      destruct (vector_inv_S v) as (vh & vt & ha); subst.
      change (write_points (vh :: vt)) with
        (List.cons (inr vh) (write_points vt)).
      cbn [List.app read_points].
      rewrite (ih vt rest).
      reflexivity.
  Qed.

  Lemma read_write_scalars :
    ∀ (n : nat) (v : Vector.t F n) (rest : wire),
    read_scalars n (List.app (write_scalars v) rest) = Some (v, rest).
  Proof.
    induction n as [|n ih]; intros *.
    +
      rewrite (vector_inv_0 v).
      reflexivity.
    +
      destruct (vector_inv_S v) as (vh & vt & ha); subst.
      change (write_scalars (vh :: vt)) with
        (List.cons (inl vh) (write_scalars vt)).
      cbn [List.app read_scalars].
      rewrite (ih vt rest).
      reflexivity.
  Qed.

  Theorem serialize_deserialize :
    ∀ (r : @comp_rel G) (t : comp_transcript r) (rest : wire),
    decode r (List.app (encode r t) rest) = Some (t, rest).
  Proof.
    induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
    +
      intros *.
      destruct t as (comm & res).
      cbn [encode decode].
      rewrite <-List.app_assoc.
      rewrite read_write_points.
      rewrite read_write_scalars.
      reflexivity.
    +
      intros *.
      destruct t as (tl & tr); cbn.
      rewrite <-List.app_assoc.
      rewrite (ihl tl).
      rewrite (ihr tr).
      reflexivity.
    +
      intros *.
      destruct t as ((tl & tr) & c1); cbn.
      rewrite <-List.app_assoc.
      rewrite (ihl tl).
      rewrite <-List.app_assoc.
      rewrite (ihr tr).
      reflexivity.
  Qed.

  (* full-message round trip: encoding then decoding recovers the
     transcript with no leftover *)
  Corollary serialize_deserialize_full :
    ∀ (r : @comp_rel G) (t : comp_transcript r),
    decode r (encode r t) = Some (t, List.nil).
  Proof.
    intros *.
    pose proof (serialize_deserialize r t List.nil) as ha.
    rewrite List.app_nil_r in ha.
    exact ha.
  Qed.

End Serialization.
