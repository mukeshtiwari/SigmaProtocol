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
  The second half of the file provides the other Shamir soundness
  ingredient: a coefficient representation of polynomials with the
  root bound (roots_bound) and the resulting uniqueness of
  low-degree interpolants (poly_unique, lag_interp_unique,
  lag_interp_agree_at_zero).  What remains for the full Shamir
  THRESH is the composition-layer engineering (n-ary children with
  challenge reconstruction); the verified THRESH available today is
  the monotone expansion in Dsl.v.
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

  (* ================= Coefficient polynomials =================

     The second ingredient of the Shamir-style THRESH soundness:
     uniqueness of low-degree interpolants.  Polynomials are
     coefficient lists (low degree first); the chain is

       quot_spec    : p(x) - p(a) = (x - a) · (p / (X - a))(x)
       roots_bound  : a polynomial with more distinct roots than
                      coefficients vanishes everywhere
       poly_unique  : two polynomials of length <= n agreeing on n
                      distinct points agree everywhere
       lag_poly     : the Lagrange interpolant *is* such a
                      polynomial (lag_poly_eval, lag_poly_length)
       lag_interp_unique / lag_interp_agree_at_zero :
                      the uniqueness facts Shamir soundness needs. *)

  Definition poly : Type := list F.

  Fixpoint peval (p : poly) (x : F) : F :=
    match p with
    | [] => zero
    | c :: p' => c + x * peval p' x
    end.

  (* fields are integral domains *)
  Lemma mul_zero_factor : ∀ (a b : F),
    a * b = zero -> a = zero ∨ b = zero.
  Proof.
    intros * ha.
    destruct (Fdec a zero) as [hz | hnz].
    +
      left; exact hz.
    +
      right.
      assert (hb : b = inv a * (a * b)). field. exact hnz.
      rewrite hb, ha. field. exact hnz.
  Qed.

  (* Synthetic division by (X - a): quot returns the quotient. *)
  Fixpoint quot (a : F) (p : poly) : poly :=
    match p with
    | [] => []
    | c :: p' =>
        match p' with
        | [] => []
        | _ :: _ => peval p' a :: quot a p'
        end
    end.

  Lemma quot_length : ∀ (p : poly) (a : F),
    List.length (quot a p) = Nat.pred (List.length p).
  Proof.
    induction p as [|c p ih]; intros a.
    +
      reflexivity.
    +
      destruct p as [|c' p'].
      ++
        reflexivity.
      ++
        cbn.
        cbn in ih.
        rewrite (ih a).
        reflexivity.
  Qed.

  Lemma quot_spec : ∀ (p : poly) (a x : F),
    peval p x - peval p a = (x - a) * peval (quot a p) x.
  Proof.
    induction p as [|c p ih]; intros a x.
    +
      cbn. field.
    +
      destruct p as [|c' p'].
      ++
        cbn. field.
      ++
        specialize (ih a x).
        cbn in ih |- *.
        assert (hstep : ∀ (Px Pa B : F),
          Px - Pa = (x - a) * B ->
          (c + x * Px) - (c + a * Pa) = (x - a) * (Pa + x * B)).
        intros * hpq.
        assert (h₂ : (x - a) * (Pa + x * B) =
          (x - a) * Pa + x * ((x - a) * B)). field.
        rewrite h₂, <-hpq. field.
        eapply hstep. exact ih.
  Qed.

  Theorem roots_bound : ∀ (n : nat) (p : poly) (roots : list F),
    (List.length p <= n)%nat ->
    List.length roots = n ->
    List.NoDup roots ->
    (∀ r, List.In r roots -> peval p r = zero) ->
    ∀ x, peval p x = zero.
  Proof.
    induction n as [|n ih].
    +
      intros * hl hr hnd hz x.
      destruct p; [reflexivity | cbn in hl; lia].
    +
      intros * hl hr hnd hz x.
      destruct roots as [|r roots']; [cbn in hr; lia |].
      cbn in hr; injection hr as hr.
      inversion hnd as [| ? ? hnin hnd']; subst.
      pose proof (quot_spec p r x) as hq.
      rewrite (hz r (or_introl eq_refl)) in hq.
      assert (hpx : peval p x = (x - r) * peval (quot r p) x).
      rewrite <-hq. field.
      rewrite hpx.
      assert (hqz : peval (quot r p) x = zero).
      eapply (ih (quot r p) roots').
      rewrite quot_length. lia.
      reflexivity.
      exact hnd'.
      intros r' hr'.
      pose proof (quot_spec p r r') as hq'.
      rewrite (hz r' (or_intror hr')) in hq'.
      rewrite (hz r (or_introl eq_refl)) in hq'.
      assert (hq₂ : (r' - r) * peval (quot r p) r' = zero).
      rewrite <-hq'. field.
      destruct (mul_zero_factor _ _ hq₂) as [hz₁ | hz₂].
      exfalso.
      eapply hnin.
      assert (hrr : r' = r).
      assert (h₃ : r' = (r' - r) + r). field.
      rewrite h₃, hz₁. field.
      rewrite <-hrr. exact hr'.
      exact hz₂.
      rewrite hqz. field.
  Qed.

  (* polynomial subtraction *)
  Fixpoint pneg (p : poly) : poly :=
    match p with
    | [] => []
    | c :: p' => opp c :: pneg p'
    end.

  Fixpoint psub (p q : poly) : poly :=
    match p, q with
    | [], q => pneg q
    | p, [] => p
    | a :: p', b :: q' => (a - b) :: psub p' q'
    end.

  Lemma pneg_eval : ∀ (q : poly) (x : F),
    peval (pneg q) x = opp (peval q x).
  Proof.
    induction q as [|c q ih]; intros x; cbn.
    field.
    rewrite ih. field.
  Qed.

  Lemma pneg_length : ∀ (q : poly),
    List.length (pneg q) = List.length q.
  Proof.
    induction q; cbn; [reflexivity | rewrite IHq; reflexivity].
  Qed.

  Lemma psub_eval : ∀ (p q : poly) (x : F),
    peval (psub p q) x = peval p x - peval q x.
  Proof.
    induction p as [|a p ih]; intros q x.
    +
      cbn. rewrite pneg_eval. field.
    +
      destruct q as [|b q].
      ++
        cbn. field.
      ++
        cbn. rewrite ih. field.
  Qed.

  Lemma psub_length : ∀ (p q : poly),
    (List.length (psub p q) <=
      Nat.max (List.length p) (List.length q))%nat.
  Proof.
    induction p as [|a p ih]; intros q.
    +
      cbn. rewrite pneg_length. lia.
    +
      destruct q as [|b q]; cbn.
      lia.
      specialize (ih q). lia.
  Qed.

  Theorem poly_unique : ∀ (p q : poly) (pts : list F),
    List.NoDup pts ->
    (List.length p <= List.length pts)%nat ->
    (List.length q <= List.length pts)%nat ->
    (∀ r, List.In r pts -> peval p r = peval q r) ->
    ∀ x, peval p x = peval q x.
  Proof.
    intros * hnd hlp hlq hagree x.
    assert (hzz : peval (psub p q) x = zero).
    eapply (roots_bound (List.length pts) (psub p q) pts).
    pose proof (psub_length p q). lia.
    reflexivity.
    exact hnd.
    intros r hr. rewrite psub_eval. rewrite (hagree r hr). field.
    rewrite psub_eval in hzz.
    assert (h₂ : peval p x = (peval p x - peval q x) + peval q x).
    field.
    rewrite h₂, hzz. field.
  Qed.

  (* ------- the Lagrange interpolant as a polynomial ------- *)

  Fixpoint padd (p q : poly) : poly :=
    match p, q with
    | [], q => q
    | p, [] => p
    | a :: p', b :: q' => (a + b) :: padd p' q'
    end.

  Lemma padd_eval : ∀ (p q : poly) (x : F),
    peval (padd p q) x = peval p x + peval q x.
  Proof.
    induction p as [|a p ih]; intros q x.
    +
      cbn. field.
    +
      destruct q as [|b q]; cbn.
      field.
      rewrite ih. field.
  Qed.

  Lemma padd_length : ∀ (p q : poly),
    (List.length (padd p q) <=
      Nat.max (List.length p) (List.length q))%nat.
  Proof.
    induction p as [|a p ih]; intros q.
    +
      cbn. lia.
    +
      destruct q as [|b q]; cbn.
      lia.
      specialize (ih q). lia.
  Qed.

  Definition pscale (c : F) (p : poly) : poly :=
    List.map (mul c) p.

  Lemma pscale_eval : ∀ (p : poly) (c x : F),
    peval (pscale c p) x = c * peval p x.
  Proof.
    induction p as [|a p ih]; intros c x.
    +
      cbn. field.
    +
      specialize (ih c x).
      unfold pscale in ih |- *; cbn.
      rewrite ih. field.
  Qed.

  Lemma pscale_length : ∀ (p : poly) (c : F),
    List.length (pscale c p) = List.length p.
  Proof.
    intros; eapply List.map_length.
  Qed.

  (* multiplication by the linear factor (X - a) *)
  Definition lin_mul (a : F) (p : poly) : poly :=
    padd (pscale (opp a) p) (zero :: p).

  Lemma lin_mul_eval : ∀ (p : poly) (a x : F),
    peval (lin_mul a p) x = (x - a) * peval p x.
  Proof.
    intros *.
    unfold lin_mul.
    rewrite padd_eval, pscale_eval; cbn.
    field.
  Qed.

  Lemma lin_mul_length : ∀ (p : poly) (a : F),
    (List.length (lin_mul a p) <= S (List.length p))%nat.
  Proof.
    intros *.
    unfold lin_mul.
    pose proof (padd_length (pscale (opp a) p) (zero :: p)) as ha.
    rewrite pscale_length in ha.
    cbn in ha. lia.
  Qed.

  Definition basis_poly (xi : F) (xs : list F) : poly :=
    List.fold_right
      (fun xj acc => pscale (inv (xi - xj)) (lin_mul xj acc))
      [one] xs.

  Lemma basis_poly_eval : ∀ (xs : list F) (xi x : F),
    peval (basis_poly xi xs) x = lag_basis xi xs x.
  Proof.
    induction xs as [|xj xs ih]; intros xi x.
    +
      cbn. field.
    +
      specialize (ih xi x).
      unfold basis_poly, lag_basis in ih |- *.
      cbn [List.fold_right].
      rewrite pscale_eval, lin_mul_eval, ih.
      set (k := inv (xi - xj)).
      field.
  Qed.

  Lemma basis_poly_length : ∀ (xs : list F) (xi : F),
    (List.length (basis_poly xi xs) <= S (List.length xs))%nat.
  Proof.
    induction xs as [|xj xs ih]; intros xi.
    +
      cbn. lia.
    +
      specialize (ih xi).
      unfold basis_poly in ih |- *.
      cbn [List.fold_right].
      rewrite pscale_length.
      pose proof (lin_mul_length
        (List.fold_right
          (fun xj' acc => pscale (inv (xi - xj')) (lin_mul xj' acc))
          [one] xs) xj) as ha.
      cbn [List.length].
      lia.
  Qed.

  Definition lag_poly (pts : list (F * F)) : poly :=
    List.fold_right
      (fun p acc =>
        padd (pscale (snd (fst p))
          (basis_poly (fst (fst p)) (List.map fst (snd p)))) acc)
      [] (select pts).

  Lemma lag_poly_eval : ∀ (pts : list (F * F)) (x : F),
    peval (lag_poly pts) x = lag_interp pts x.
  Proof.
    intros *.
    unfold lag_poly, lag_interp.
    induction (select pts) as [|e sel ih]; cbn.
    +
      reflexivity.
    +
      rewrite padd_eval, pscale_eval, basis_poly_eval, ih.
      reflexivity.
  Qed.

  Lemma select_entry_length : ∀ (A : Type) (l : list A)
    (p : A) (others : list A),
    List.In (p, others) (select l) ->
    S (List.length others) = List.length l.
  Proof.
    induction l as [|x xs ih]; intros * ha.
    +
      destruct ha.
    +
      cbn in ha.
      destruct ha as [ha | ha].
      ++
        injection ha as h₁ h₂; subst.
        reflexivity.
      ++
        eapply List.in_map_iff in ha.
        destruct ha as ((p' & others') & hb & hc).
        injection hb as h₁ h₂; subst.
        cbn.
        rewrite (ih _ _ hc).
        reflexivity.
  Qed.

  Lemma lag_poly_length : ∀ (pts : list (F * F)),
    (List.length (lag_poly pts) <= List.length pts)%nat.
  Proof.
    intros *.
    unfold lag_poly.
    assert (ha : ∀ e, List.In e (select pts) ->
      S (List.length (snd e)) = List.length pts).
    intros (pe & others) he.
    eapply select_entry_length; exact he.
    induction (select pts) as [|e sel ih]; cbn.
    +
      lia.
    +
      pose proof (padd_length
        (pscale (snd (fst e))
          (basis_poly (fst (fst e)) (List.map fst (snd e))))
        (List.fold_right
          (fun p acc =>
            padd (pscale (snd (fst p))
              (basis_poly (fst (fst p)) (List.map fst (snd p)))) acc)
          [] sel)) as hb.
      rewrite pscale_length in hb.
      pose proof (basis_poly_length
        (List.map fst (snd e)) (fst (fst e))) as hc.
      rewrite List.map_length in hc.
      pose proof (ha e (or_introl eq_refl)) as hd.
      cbn in hd.
      assert (he : ∀ e', List.In e' sel ->
        S (List.length (snd e')) = List.length pts).
      intros e' he'.
      eapply ha; right; exact he'.
      specialize (ih he).
      lia.
  Qed.

  (* Uniqueness of Lagrange interpolants: two interpolants bounded
     by the same node count that agree on that many distinct inputs
     agree everywhere. *)
  Theorem lag_interp_unique :
    ∀ (pts₁ pts₂ : list (F * F)) (nodes : list F),
    List.NoDup nodes ->
    (List.length pts₁ <= List.length nodes)%nat ->
    (List.length pts₂ <= List.length nodes)%nat ->
    (∀ a, List.In a nodes ->
      lag_interp pts₁ a = lag_interp pts₂ a) ->
    ∀ x, lag_interp pts₁ x = lag_interp pts₂ x.
  Proof.
    intros * hnd hl₁ hl₂ hagree x.
    rewrite <-!lag_poly_eval.
    eapply (poly_unique (lag_poly pts₁) (lag_poly pts₂) nodes).
    exact hnd.
    pose proof (lag_poly_length pts₁). lia.
    pose proof (lag_poly_length pts₂). lia.
    intros r hr.
    rewrite !lag_poly_eval.
    eapply hagree; exact hr.
  Qed.

  (* The contrapositive Shamir-THRESH soundness uses: if two
     challenge interpolants agree on enough branch positions, their
     values at 0 — the top-level challenges — coincide.  Hence
     distinct top challenges force disagreement on more branches
     than the simulated ones, yielding enough extractable branches. *)
  Corollary lag_interp_agree_at_zero :
    ∀ (pts₁ pts₂ : list (F * F)) (nodes : list F),
    List.NoDup nodes ->
    (List.length pts₁ <= List.length nodes)%nat ->
    (List.length pts₂ <= List.length nodes)%nat ->
    (∀ a, List.In a nodes ->
      lag_interp pts₁ a = lag_interp pts₂ a) ->
    lag_interp pts₁ zero = lag_interp pts₂ zero.
  Proof.
    intros * hnd hl₁ hl₂ hagree.
    eapply lag_interp_unique.
    exact hnd. exact hl₁. exact hl₂. exact hagree.
  Qed.

End Lagrange.
