From Stdlib Require Import Setoid
  setoid_ring.Field Lia List Utf8
  Psatz Bool.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.

Import ListNotations.

(*
  Lagrange interpolation over an abstract field, in evaluation form
  (no polynomial datatype): the interpolant of a list of points is a
  function F -> F, and the main theorem states that it passes
  through every point, provided the interpolation nodes are
  pairwise distinct.

  This is the constructive core of the Shamir-style THRESH(t, n)
  composition (sigma-proofs' expand_threshold_challenges): the
  verifier reconstructs all n branch challenges by evaluating the
  interpolant through (0, c) and the n - t compressed challenges.
  The remaining ingredient for the full Shamir soundness proof —
  uniqueness of low-degree interpolants, which needs a coefficient
  representation of polynomials — is future work; the verified
  THRESH available today is the monotone expansion in Dsl.v.
*)
Section Lagrange.

  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hfield : @field F (@eq F) zero one opp add sub mul inv div}.

  #[local] Infix "*" := mul.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div Hfield).

  (* Pair each element of a list with the remaining elements. *)
  Fixpoint select {A : Type} (l : list A) : list (A * list A) :=
    match l with
    | [] => []
    | x :: xs =>
        (x, xs) :: List.map (fun p => (fst p, x :: snd p)) (select xs)
    end.

  (* The Lagrange basis factor of node xi w.r.t. the other nodes,
     evaluated at x:  Π_{xj}  (x - xj) / (xi - xj). *)
  Definition lag_basis (xi : F) (xs : list F) (x : F) : F :=
    List.fold_right
      (fun xj acc => ((x - xj) * inv (xi - xj)) * acc) one xs.

  (* The interpolant:  Σ_i  yi · basis_i(x). *)
  Definition lag_interp (pts : list (F * F)) (x : F) : F :=
    List.fold_right
      (fun p acc =>
        (snd (fst p)) *
        lag_basis (fst (fst p)) (List.map fst (snd p)) x + acc)
      zero (select pts).

  Lemma sub_neq_zero : ∀ (a b : F),
    a <> b -> a - b <> zero.
  Proof.
    intros * ha hb.
    eapply ha.
    assert (hc : a = (a - b) + b). field.
    rewrite hc, hb. field.
  Qed.

  Lemma lag_basis_self : ∀ (xs : list F) (xi : F),
    (∀ xj, List.In xj xs -> xi <> xj) ->
    lag_basis xi xs xi = one.
  Proof.
    induction xs as [|xj xs ih]; intros xi ha.
    +
      reflexivity.
    +
      specialize (ih xi (fun xk hk => ha xk (or_intror hk))).
      unfold lag_basis in ih |- *; cbn.
      rewrite ih.
      field.
      eapply sub_neq_zero.
      eapply ha; left; reflexivity.
  Qed.

  Lemma lag_basis_zero : ∀ (xs : list F) (xi xz : F),
    List.In xz xs ->
    lag_basis xi xs xz = zero.
  Proof.
    induction xs as [|xj xs ih]; intros xi xz ha.
    +
      destruct ha.
    +
      destruct ha as [ha | ha].
      ++
        subst.
        unfold lag_basis; cbn.
        assert (hb : xz - xz = zero). field.
        rewrite hb.
        assert (hc : ∀ q : F, zero * q = zero).
        intros; field.
        rewrite hc, hc.
        reflexivity.
      ++
        specialize (ih xi xz ha).
        unfold lag_basis in ih |- *; cbn.
        rewrite ih.
        assert (hc : ∀ q : F, q * zero = zero).
        intros; field.
        rewrite hc.
        reflexivity.
  Qed.

  (* Folding an addition over all-zero terms keeps the accumulator. *)
  Lemma fold_add_zero : ∀ {A : Type} (f : A -> F) (l : list A)
    (init : F),
    (∀ p, List.In p l -> f p = zero) ->
    List.fold_right (fun p acc => f p + acc) init l = init.
  Proof.
    intros A f.
    induction l as [|p l ih]; intros init ha.
    +
      reflexivity.
    +
      cbn.
      rewrite (ha p (or_introl eq_refl)).
      rewrite ih.
      field.
      intros q hq; eapply ha; right; exact hq.
  Qed.

  (* Splitting select at a distinguished element: the element is
     paired with all the others, and every other entry carries the
     distinguished element among its "others". *)
  Lemma select_split : ∀ {A : Type} (l₁ l₂ : list A) (p : A),
    ∃ S₁ S₂,
      select (l₁ ++ p :: l₂) = S₁ ++ (p, l₁ ++ l₂) :: S₂ ∧
      (∀ q, List.In q (S₁ ++ S₂) -> List.In p (snd q)).
  Proof.
    induction l₁ as [|a l₁ ih]; intros l₂ p.
    +
      cbn.
      exists [], (List.map (fun q => (fst q, p :: snd q)) (select l₂)).
      split.
      ++
        reflexivity.
      ++
        intros q hq; cbn in hq.
        eapply List.in_map_iff in hq.
        destruct hq as (q' & hb & hc).
        rewrite <-hb; cbn.
        left; reflexivity.
    +
      destruct (ih l₂ p) as (S₁ & S₂ & hb & hc).
      exists ((a, l₁ ++ p :: l₂) ::
        List.map (fun q => (fst q, a :: snd q)) S₁),
        (List.map (fun q => (fst q, a :: snd q)) S₂).
      split.
      ++
        cbn.
        rewrite hb.
        rewrite List.map_app.
        cbn.
        reflexivity.
      ++
        intros q hq.
        cbn in hq.
        destruct hq as [hq | hq].
        +++
          rewrite <-hq; cbn.
          eapply List.in_or_app; right.
          left; reflexivity.
        +++
          rewrite <-List.map_app in hq.
          eapply List.in_map_iff in hq.
          destruct hq as (q' & hd & he).
          rewrite <-hd; cbn.
          right.
          eapply hc; exact he.
  Qed.

  (* Main theorem: the interpolant passes through every point. *)
  Theorem lag_interp_eval :
    ∀ (pts : list (F * F)) (xk yk : F),
    List.NoDup (List.map fst pts) ->
    List.In (xk, yk) pts ->
    lag_interp pts xk = yk.
  Proof.
    intros * hnd hin.
    destruct (List.in_split _ _ hin) as (l₁ & l₂ & hsplit); subst.
    destruct (@select_split (F * F) l₁ l₂ (xk, yk))
      as (S₁ & S₂ & hsel & hother).
    unfold lag_interp.
    rewrite hsel.
    rewrite List.fold_right_app.
    cbn [List.fold_right fst snd].
    (* the terms of S₂ vanish *)
    rewrite (fold_add_zero
      (fun p => (snd (fst p)) *
        lag_basis (fst (fst p)) (List.map fst (snd p)) xk) S₂ zero).
    +
      (* the distinguished term is yk · 1 *)
      rewrite List.map_app in hnd; cbn in hnd.
      pose proof (List.NoDup_remove_2 _ _ _ hnd) as hxk.
      rewrite lag_basis_self.
      ++
        assert (ha : yk * one + zero = yk). field.
        rewrite ha.
        (* the terms of S₁ vanish *)
        rewrite (fold_add_zero
          (fun p => (snd (fst p)) *
            lag_basis (fst (fst p)) (List.map fst (snd p)) xk) S₁ yk).
        reflexivity.
        intros p hp.
        rewrite lag_basis_zero.
        field.
        eapply List.in_map_iff.
        exists (xk, yk).
        split. reflexivity.
        eapply hother.
        eapply List.in_or_app; left; exact hp.
      ++
        intros xj hj heq; subst.
        eapply hxk.
        rewrite List.map_app in hj.
        exact hj.
    +
      intros p hp.
      rewrite lag_basis_zero.
      field.
      eapply List.in_map_iff.
      exists (xk, yk).
      split. reflexivity.
      eapply hother.
      eapply List.in_or_app; right; exact hp.
  Qed.

End Lagrange.
