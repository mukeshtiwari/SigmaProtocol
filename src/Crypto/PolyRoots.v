(* Univariate polynomials over the library's field class, as coefficient
   lists (constant term first), with Horner evaluation, and the one theorem
   about them that the shuffle soundness needs: a polynomial that is not
   identically zero as a coefficient list has fewer roots than
   coefficients. Consequently, a family of at most k such polynomials of
   length at most d has a common non-root in any duplicate-free list of
   more than k·(d−1) field elements (common_nonroot). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring.
Import ListNotations.

Section PolyRoots.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.

  Definition poly : Type := list F.

  (* Horner: eval (c :: p) x = c + x · eval p x *)
  Fixpoint eval (p : poly) (x : F) : F :=
    match p with
    | [] => zero
    | c :: p' => c + x * eval p' x
    end.

  (* identically zero as a coefficient list *)
  Definition pzero (p : poly) : Prop := Forall (fun c => c = zero) p.

  Lemma pzero_dec : forall p, {pzero p} + {~ pzero p}.
  Proof.
    induction p as [| c p ih].
    + left; constructor.
    + destruct (Fdec c zero) as [-> | hc]; [destruct ih as [h | h] |].
      - left; constructor; [reflexivity | exact h].
      - right; intro h'; inversion h'; contradiction.
      - right; intro h'; inversion h'; contradiction.
  Qed.

  Lemma eval_pzero : forall p x, pzero p -> eval p x = zero.
  Proof.
    induction p as [| c p ih]; intros x h; [reflexivity |].
    inversion h; subst; cbn; rewrite ih; [field | assumption].
  Qed.

  (* division by (X − r): p(x) = (x − r) · q(x) + p(r), with
    q = divide p r. For p = c :: p', q = p'(r) :: divide p' r. *)
  Fixpoint divide (p : poly) (r : F) : poly :=
    match p with
    | [] => []
    | c :: p' => eval p' r :: divide p' r
    end.

  Lemma divide_length : forall p r, length (divide p r) = length p.
  Proof. induction p as [| c p ih]; intro r; cbn; [reflexivity | rewrite ih; reflexivity]. Qed.

  Lemma divide_spec : forall p r x, eval p x = (x - r) * eval (divide p r) x + eval p r.
  Proof.
    induction p as [| c p ih]; intros r x; cbn.
    + field.
    + rewrite (ih r x) at 1. field.
  Qed.

  (* the last coefficient of divide is zero (it is the evaluation of the
    empty tail), so divide p r is really of degree one less *)
  Lemma divide_last : forall p r, p <> [] -> exists q, divide p r = q ++ [zero] /\ length q = Nat.sub (length p) 1.
  Proof.
    induction p as [| c p ih]; intros r hne; [contradiction |].
    destruct p as [| c' p'].
    + exists []; cbn; split; [reflexivity | reflexivity].
    + destruct (ih r ltac:(discriminate)) as (q & hq & hl).
      exists (eval (c' :: p') r :: q); cbn in *; rewrite hq; split; [reflexivity | lia].
  Qed.

  (* if p ≠ 0 and p(r) = 0, the quotient is not identically zero *)
  Lemma divide_nonzero : forall p r, ~ pzero p -> eval p r = zero -> ~ pzero (divide p r).
  Proof.
    induction p as [| c p ih]; intros r hp hr hq.
    + apply hp; constructor.
    + cbn in hq; inversion hq as [| ? ? h1 h2]; subst.
      cbn in hr. rewrite h1 in hr.
      (* c + r * 0 = 0 so c = 0; and divide p r is zero *)
      assert (hc : c = zero) by (rewrite <-hr; field).
      apply hp; constructor; [exact hc |].
      destruct (pzero_dec p) as [hpz | hpz]; [exact hpz |].
      exfalso; exact (ih r hpz h1 h2).
  Qed.

  (* the roots of p are a root r and the roots of divide p r *)
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

  Lemma pzero_app_zero : forall q, pzero (q ++ [zero]) <-> pzero q.
  Proof.
    intro q; unfold pzero; rewrite Forall_app; split.
    + intros [h _]; exact h.
    + intro h; split; [exact h | constructor; [reflexivity | constructor]].
  Qed.

  Lemma eval_app_zero : forall q x, eval (q ++ [zero]) x = eval q x.
  Proof. induction q as [| c q ih]; intro x; cbn; [field | rewrite ih; reflexivity]. Qed.

  (* A non-zero polynomial has fewer roots than coefficients. *)
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

  (* Given k lists of roots each of length < d and a duplicate-free list lf
    with more than k·d elements, some element of lf is in none of them. *)
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

  (* Common non-root of a family of non-zero polynomials, each of length
    at most d, when lf has more than k·d elements. The roots of each
    polynomial in lf are collected as a list of length < d. *)
  Theorem common_nonroot : forall (lf : list F) (ps : list poly) (d : nat),
    NoDup lf -> (forall p, In p ps -> ~ pzero p /\ length p <= d) ->
    Nat.lt (Nat.mul (length ps) d) (length lf) ->
    exists x, In x lf /\ forall p, In p ps -> eval p x <> zero.
  Proof.
    intros lf ps d hnd hps hlen.
    set (roots_of := fun p => filter (fun x => if Fdec (eval p x) zero then true else false) lf).
    assert (hroots : forall p, In p ps -> length (roots_of p) < d).
    { intros p hp. destruct (hps p hp) as [hnz hd].
      assert (h := roots_bound (length p) p (le_n _) hnz (roots_of p)).
      assert (hnd' : NoDup (roots_of p)) by (apply NoDup_filter; exact hnd).
      assert (hall : forall r, In r (roots_of p) -> eval p r = zero).
      { intros r hr; unfold roots_of in hr; apply filter_In in hr; destruct hr as [_ hr].
        destruct (Fdec (eval p r) zero); [assumption | discriminate]. }
      specialize (h hnd' hall). lia. }
    set (bad := flat_map roots_of ps).
    assert (hbad_gen : forall qs : list poly, (forall p, In p qs -> Nat.lt (length (roots_of p)) d) ->
      Nat.le (length (flat_map roots_of qs)) (Nat.mul (length qs) d)).
    { intro qs; induction qs as [| p qs ih]; intro hq; cbn; [lia |].
      rewrite length_app.
      specialize (ih (fun q h => hq q (or_intror h))).
      specialize (hq p (or_introl eq_refl)). lia. }
    assert (hbad : Nat.le (length bad) (Nat.mul (length ps) d)) by (apply hbad_gen; exact hroots).
    destruct (pigeonhole_notin lf bad hnd ltac:(lia)) as (x & hx & hnot).
    exists x; split; [exact hx |].
    intros p hp he. apply hnot. unfold bad; apply in_flat_map; exists p; split; [exact hp |].
    unfold roots_of; apply filter_In; split; [exact hx |].
    destruct (Fdec (eval p x) zero); [reflexivity | contradiction].
  Qed.

End PolyRoots.
