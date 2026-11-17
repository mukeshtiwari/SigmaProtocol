(** * Root bounds for univariate polynomials over a field *)

(** This file develops just enough univariate polynomial algebra to support the
    probabilistic arguments in the shuffle and Schulze soundness proofs. A
    polynomial is represented as its list of coefficients, constant term first,
    so [[c0; c1; ...; c(n-1)]] denotes c0 + c1·X + ... + c(n-1)·X^(n-1). It is
    evaluated by Horner's rule ([eval]).

    The key fact is the classical root bound: a polynomial whose coefficient list
    is not identically zero has strictly fewer distinct roots than it has
    coefficients ([roots_bound]). The proof is by synthetic division by (X − r)
    ([divide], [divide_spec]): every root r gives a quotient of one fewer
    effective coefficient that still vanishes at all the other roots.

    From the root bound we derive [common_nonroot]: if [ps] is a family of k
    polynomials, each not identically zero and with at most d coefficients, then
    any duplicate-free list of more than k·d field elements contains a point at
    which none of them vanishes. This is the deterministic, counting form of the
    Schwartz–Zippel lemma (univariate case) used to argue that a cheating prover
    cannot answer correctly on too many challenges. Note that the hypothesis is
    stated with k·d, not k·(d−1); this is slightly weaker than optimal but
    suffices for the callers.

    Used by [PolyPerm], [SigmaK], [BayerGroth], [BayerGrothSound],
    [BayerGrothZK], [ShuffleTWSound2], and the Schulze front ends
    [SchulzeSimple] and [SchulzeBatched]. *)
From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
Import ListNotations.

(** ** Polynomials as coefficient lists

    Everything is parameterised over an arbitrary field [F] with decidable
    equality [Fdec], using the library's [field] class from [Algebra.Field]. *)
Section PolyRoots.

  (** The ambient field: carrier [F], constants [zero], [one], operations
      [add], [mul], [sub], [div], [opp], [inv], decidable equality [Fdec], and the
      field axioms [Hf]. The [Add Field] command below registers the structure
      with the standard [field] tactic. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.

  (** A polynomial is a list of coefficients, lowest degree first. Trailing zeros
      are allowed, so the representation is not canonical; [pzero] below is the
      semantic zero test. *)
  Definition poly : Type := list F.

  (** Horner evaluation: [eval [] x = zero] and
      [eval (c :: p) x = c + x · eval p x]. *)
  Fixpoint eval (p : poly) (x : F) : F :=
    match p with
    | [] => zero
    | c :: p' => c + x * eval p' x
    end.

  (** [pzero p] holds when every coefficient of [p] is zero, i.e. [p] is the
      zero polynomial (possibly with trailing zeros). *)
  Definition pzero (p : poly) : Prop := Forall (fun c => c = zero) p.

  (** Being identically zero is decidable, using decidable equality on [F]. *)
  Lemma pzero_dec : forall p, {pzero p} + {~ pzero p}.
  Proof.
    induction p as [| c p ih].
    + left; constructor.
    + destruct (Fdec c zero) as [-> | hc]; [destruct ih as [h | h] |].
      - left; constructor; [reflexivity | exact h].
      - right; intro h'; inversion h'; contradiction.
      - right; intro h'; inversion h'; contradiction.
  Qed.

  (** The zero polynomial evaluates to [zero] everywhere. *)
  Lemma eval_pzero : forall p x, pzero p -> eval p x = zero.
  Proof.
    induction p as [| c p ih]; intros x h; [reflexivity |].
    inversion h; subst; cbn; rewrite ih; [field | assumption].
  Qed.

  (** ** Synthetic division by (X − r)

      [divide p r] computes the quotient of [p] by the linear factor (X − r). The
      coefficient at position i of the result is the evaluation at [r] of the tail
      of [p] starting at position i+1. The result has the same length as [p] and
      its last coefficient is always zero (see [divide_last]), so the quotient
      effectively has one coefficient fewer. *)
  Fixpoint divide (p : poly) (r : F) : poly :=
    match p with
    | [] => []
    | c :: p' => eval p' r :: divide p' r
    end.

  (** Division preserves the length of the coefficient list. *)
  Lemma divide_length : forall p r, length (divide p r) = length p.
  Proof. induction p as [| c p ih]; intro r; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  (** The division identity (polynomial remainder theorem): for all [x],
      [eval p x = (x - r) · eval (divide p r) x + eval p r]. *)
  Lemma divide_spec : forall p r x, eval p x = (x - r) * eval (divide p r) x + eval p r.
  Proof.
    induction p as [| c p ih]; intros r x; cbn.
    + field.
    + rewrite (ih r x) at 1. field.
  Qed.

  (** For a non-empty [p], the quotient [divide p r] is [q ++ [zero]] for some
      [q] of length [length p - 1]. This is how the degree drop is made visible
      to the induction in [roots_bound]. *)
  Lemma divide_last : forall p r, p <> [] -> exists q, divide p r = q ++ [zero] /\ length q = Nat.sub (length p) 1.
  Proof.
    induction p as [| c p ih]; intros r hne; [contradiction |].
    destruct p as [| c' p'].
    + exists []; cbn; split; [reflexivity | reflexivity].
    + destruct (ih r ltac:(discriminate)) as (q & hq & hl).
      exists (eval (c' :: p') r :: q); cbn in *; rewrite hq; split; [reflexivity | lia].
  Qed.

  (** If [p] is not identically zero and [r] is a root of [p], then the quotient
      [divide p r] is not identically zero either. (If the quotient were zero, the
      division identity would force every coefficient of [p] to be zero.) *)
  Lemma divide_nonzero : forall p r, ~ pzero p -> eval p r = zero -> ~ pzero (divide p r).
  Proof.
    induction p as [| c p ih]; intros r hp hr hq.
    + apply hp; constructor.
    + cbn in hq; inversion hq as [| ? ? h1 h2]; subst.
      cbn in hr. rewrite h1 in hr.
      assert (hc : c = zero) by (rewrite <-hr; field).
      apply hp; constructor; [exact hc |].
      destruct (pzero_dec p) as [hpz | hpz]; [exact hpz |].
      exfalso; exact (ih r hpz h1 h2).
  Qed.

  (** Every root [x] of [p] other than [r] is a root of [divide p r]: from
      [0 = (x - r) · q(x)] and [x ≠ r] we cancel the non-zero factor using the
      field inverse. *)
  Lemma root_divide : forall p r x, eval p r = zero -> eval p x = zero -> x <> r -> eval (divide p r) x = zero.
  Proof.
    intros p r x hr hx hne.
    rewrite divide_spec with (r := r) in hx. rewrite hr in hx.
    assert (h : (x - r) <> zero).
    { intro e; apply hne. replace x with ((x - r) + r) by field. rewrite e; field. }
    assert (hx' : (x - r) * eval (divide p r) x = zero) by (rewrite <-hx; field).
    assert (hq : eval (divide p r) x = inv (x - r) * ((x - r) * eval (divide p r) x)).
    { field; try exact h. }
    rewrite hq, hx'. field. all: exact h.
  Qed.

  (** Appending a zero coefficient does not change whether a polynomial is
      identically zero. *)
  Lemma pzero_app_zero : forall q, pzero (q ++ [zero]) <-> pzero q.
  Proof.
    intro q; unfold pzero; rewrite Forall_app; split.
    + intros [h _]; exact h.
    + intro h; split; [exact h | constructor; [reflexivity | constructor]].
  Qed.

  (** Appending a zero coefficient does not change the evaluation. *)
  Lemma eval_app_zero : forall q x, eval (q ++ [zero]) x = eval q x.
  Proof. induction q as [| c q ih]; intro x; cbn; [field | rewrite ih; reflexivity]. Qed.

  (** ** The root bound

      Main theorem: a polynomial [p] that is not identically zero has fewer
      distinct roots than coefficients. Formally, for every duplicate-free list
      [roots] all of whose elements are roots of [p],
      [length roots < length p]. The extra natural number [n] is an upper bound
      on [length p] that drives the induction.

      Proof idea: induction on [n]. With no roots the claim is just that a
      non-zero [p] is non-empty. Otherwise take the first root [r], write
      [divide p r = q ++ [zero]] ([divide_last]); [q] is not identically zero
      ([divide_nonzero]), is one coefficient shorter, and vanishes at all the
      remaining roots ([root_divide], which uses that the roots are distinct).
      The induction hypothesis on [q] gives the bound. *)
  Theorem roots_bound : forall (n : nat) (p : poly), length p <= n -> ~ pzero p ->
    forall roots : list F, NoDup roots -> (forall r, In r roots -> eval p r = zero) ->
    length roots < length p.
  Proof.
    induction n as [| n ih]; intros p hlen hp roots hnd hroots.
    + destruct p; [exfalso; apply hp; constructor | cbn in hlen; lia].
    + destruct roots as [| r roots'].
      - destruct p; [exfalso; apply hp; constructor | cbn; lia].
      - assert (hr : eval p r = zero) by (apply hroots; left; reflexivity).
        assert (hne : p <> []) by (intro e; subst; apply hp; constructor).
        (* Peel off the root r: the quotient is q ++ [zero] with q one shorter. *)
        destruct (divide_last p r hne) as (q & hq & hql).
        assert (hqz : ~ pzero q).
        { intro hz; apply (divide_nonzero p r hp hr); rewrite hq; apply pzero_app_zero; exact hz. }
        inversion hnd as [| ? ? hnotin hnd']; subst.
        assert (hroots' : forall x, In x roots' -> eval q x = zero).
        { intros x hx. rewrite <-eval_app_zero, <-hq. apply root_divide; [exact hr | apply hroots; right; exact hx |].
          intro e; subst; contradiction. }
        assert (hlt : length roots' < length q).
        { apply (ih q); [lia | exact hqz | exact hnd' | exact hroots']. }
        cbn; lia.
  Qed.

  (** ** A common non-root for a family of polynomials

      Pigeonhole: if [lf] has no duplicates and is strictly longer than [bad],
      then some element of [lf] is not in [bad]. *)
  Lemma pigeonhole_notin : forall (lf bad : list F), NoDup lf -> length bad < length lf ->
    exists x, In x lf /\ ~ In x bad.
  Proof.
    intros lf bad hnd hlen.
    destruct (Exists_dec (fun x => ~ In x bad) lf) as [h | h].
    + intro x; destruct (in_dec Fdec x bad) as [i | i]; [right; tauto | left; exact i].
    + apply Exists_exists in h; exact h.
    + exfalso. assert (hincl : incl lf bad).
      { intros x hx. destruct (in_dec Fdec x bad) as [i | i]; [exact i |].
        exfalso; apply h; apply Exists_exists; exists x; split; assumption. }
      pose proof (NoDup_incl_length hnd hincl); lia.
  Qed.

  (** Counting Schwartz–Zippel: let [lf] be a duplicate-free list of field
      elements and [ps] a list of polynomials, each not identically zero and of
      length at most [d]. If [length ps · d < length lf], then some [x] in [lf]
      is a non-root of every polynomial in [ps].

      Proof idea: for each [p], the elements of [lf] that are roots of [p] form a
      duplicate-free list of fewer than [d] elements by [roots_bound]. The
      concatenation [bad] of all these lists has length at most [length ps · d],
      so [pigeonhole_notin] yields an element of [lf] outside [bad].

      Callers instantiate [lf] with a set of challenges answered successfully by
      a prover, and [ps] with difference polynomials that are non-zero when the
      prover cheats; the theorem then produces a challenge on which the cheating
      is detected. *)
  Theorem common_nonroot : forall (lf : list F) (ps : list poly) (d : nat),
    NoDup lf -> (forall p, In p ps -> ~ pzero p /\ length p <= d) ->
    Nat.lt (Nat.mul (length ps) d) (length lf) ->
    exists x, In x lf /\ forall p, In p ps -> eval p x <> zero.
  Proof.
    intros lf ps d hnd hps hlen.
    (* roots_of p: the elements of lf at which p vanishes; fewer than d of them. *)
    set (roots_of := fun p => filter (fun x => if Fdec (eval p x) zero then true else false) lf).
    assert (hroots : forall p, In p ps -> length (roots_of p) < d).
    { intros p hp. destruct (hps p hp) as [hnz hd].
      assert (h := roots_bound (length p) p (le_n _) hnz (roots_of p)).
      assert (hnd' : NoDup (roots_of p)) by (apply NoDup_filter; exact hnd).
      assert (hall : forall r, In r (roots_of p) -> eval p r = zero).
      { intros r hr; unfold roots_of in hr; apply filter_In in hr; destruct hr as [_ hr].
        destruct (Fdec (eval p r) zero); [assumption | discriminate]. }
      specialize (h hnd' hall). lia. }
    (* All bad points together number at most length ps · d. *)
    set (bad := flat_map roots_of ps).
    assert (hbad_gen : forall qs : list poly, (forall p, In p qs -> Nat.lt (length (roots_of p)) d) ->
      Nat.le (length (flat_map roots_of qs)) (Nat.mul (length qs) d)).
    { intro qs; induction qs as [| p qs ih]; intro hq; cbn; [lia |].
      rewrite length_app.
      specialize (ih (fun q h => hq q (or_intror h))).
      specialize (hq p (or_introl eq_refl)). lia. }
    assert (hbad : Nat.le (length bad) (Nat.mul (length ps) d)) by (apply hbad_gen; exact hroots).
    (* Pick a point of lf outside bad; it is a non-root of every p in ps. *)
    destruct (pigeonhole_notin lf bad hnd ltac:(lia)) as (x & hx & hnot).
    exists x; split; [exact hx |].
    intros p hp he. apply hnot. unfold bad; apply in_flat_map; exists p; split; [exact hp |].
    unfold roots_of; apply filter_In; split; [exact hx |].
    destruct (Fdec (eval p x) zero); [reflexivity | contradiction].
  Qed.

End PolyRoots.
