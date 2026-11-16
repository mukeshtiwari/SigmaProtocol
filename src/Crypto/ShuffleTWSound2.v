(* Soundness of the Terelius–Wikström proof of a shuffle, part 2: the
   permutation-matrix lemma and the soundness theorem.

   Permutation-matrix lemma (matrix_is_permutation). Let M be an (N+1)×(N+1)
   matrix over F whose columns sum to one and such that
   ∏_i (Mᵀ e)_i = ∏_j e_j for every e ∈ F^{N+1}. If F has more than
   (N+1)² elements, M is a permutation matrix. Proof: fix j and consider
   the vectors e with e_j = 0; then ∏ e_j = 0, so some column i of M
   satisfies ⟨col_i, e⟩ = 0. Take e = (1, t, t², …) with the j-th entry
   zeroed: ⟨col_i, e⟩ = P_i(t) for the polynomial P_i whose coefficients
   are column i without its j-th entry. If no P_i were the zero
   polynomial, the roots of all P_i would be fewer than (N+1)·N < |F|
   elements (Crypto/PolyRoots.v), so some t makes every ⟨col_i, e⟩
   non-zero, a contradiction. Hence some column i is zero off j, and its
   sum being one it is the unit vector δ_j. The map j ↦ i is injective,
   hence bijective, and the rows of M are then unit vectors.

   Soundness theorem (tw_soundness). Given witnesses of the five equations
   for every unit vector e = δ_j (which open the permutation commitment)
   and for every e (the extractor may rewind the prover with any e), either
   there is a non-trivial discrete-logarithm relation g^{x_0} ∏ h_i^{x_i} = 1
   (a break of the binding of the commitment scheme), or there is a
   permutation π such that every output w'_{π(j)} is the re-encryption
   w_j · Enc(1; f_j) of an input, with an explicit exponent f_j. The
   quantifier over all e is decided by enumerating F^{N+1}; the statistical
   version (a single random e, with the Schwartz–Zippel bound) is not
   proved here and is recorded as future work. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool List setoid_ring.Field PeanoNat Permutation.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto MultiExp ShuffleTW ShuffleTWProps ShuffleTWSound PolyRoots.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

Section Sound2.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}
    {N : nat}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Notation M := (S N).
  Local Infix "*" := mul.
  Local Infix "+" := add.

  Local Notation fsum := (fsum (zero := zero) (add := add)).
  Local Notation fprod := (fprod (mul := mul) (one := one)).
  Local Notation vzero m := (Vector.const zero m).
  Local Notation matT_mul := (matT_mul (zero := zero) (add := add) (mul := mul)).
  Local Notation colsum := (colsum (zero := zero) (one := one) (add := add) (mul := mul)).
  Local Notation unit_vec := (unit_vec (zero := zero) (one := one)).
  Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).
  Local Notation pzero := (pzero (zero := zero)).

  Lemma zero_neq_one' : zero <> one.
  Proof.
    pose proof (@field_is_zero_neq_one _ _ _ _ _ _ _ _ _ _ (@vector_space_field _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec)) as h.
    hnf in h; exact h.
  Qed.

  Lemma add_swap : forall a b c : F, a + (b + c) = b + (a + c).
  Proof. intros; field. Qed.

  Lemma mul_nonzero : forall x y : F, x <> zero -> y <> zero -> x * y <> zero.
  Proof.
    intros x y hx hy h; apply hy.
    assert (e : y = inv x * (x * y)). { field. all: exact hx. }
    rewrite e, h. field. all: exact hx.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Columns, sums, powers                                             *)
  (* ---------------------------------------------------------------- *)

  Definition col {m : nat} (mat : Vector.t (Vector.t F M) m) (i : Fin.t M) : Vector.t F m :=
    Vector.map (fun row => row[@i]) mat.

  Lemma fsum_cons : forall (m : nat) (a : F) (v : Vector.t F m), fsum (a :: v) = a + fsum v.
  Proof. reflexivity. Qed.

  Lemma matT_nth : forall (m : nat) (mat : Vector.t (Vector.t F M) m) (e : Vector.t F m) (i : Fin.t M),
    (matT_mul mat e)[@i] = fsum (Vector.map2 mul (col mat i) e).
  Proof.
    induction m as [| m ih]; intros mat e i.
    + rewrite (vector_inv_0 mat), (vector_inv_0 e); unfold matT_mul, col.
      cbn [Vector.map].
      change (Vector.map2 pair (@Vector.nil (Vector.t F M)) (@Vector.nil F)) with (@Vector.nil (Vector.t F M * F)).
      change (Vector.map2 mul (@Vector.nil F) (@Vector.nil F)) with (@Vector.nil F).
      cbn [Vector.fold_right]. rewrite Vector.const_nth; reflexivity.
    + destruct (vector_inv_S mat) as (row & mat' & ->).
      destruct (vector_inv_S e) as (ej & e' & ->).
      unfold matT_mul, col in *; rewrite map2_cons; cbn [Vector.fold_right Vector.map].
      rewrite map2_cons, fsum_cons, (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl),
        (Vector.nth_map _ _ i i eq_refl), ih; reflexivity.
  Qed.

  Lemma colsum_nth : forall (mat : Vector.t (Vector.t F M) M) (i : Fin.t M),
    (colsum mat)[@i] = fsum (col mat i).
  Proof.
    intros; unfold colsum; rewrite matT_nth; f_equal.
    apply Vector.eq_nth_iff; intros j k <-.
    rewrite (Vector.nth_map2 _ _ _ j j j eq_refl eq_refl), Vector.const_nth; field.
  Qed.

  Fixpoint fpow (t : F) (n : nat) : F :=
    match n with 0 => one | S n' => t * fpow t n' end.

  Fixpoint pows (t : F) (k : nat) (m : nat) : Vector.t F m :=
    match m with 0 => [] | S m' => fpow t k :: pows t (S k) m' end.

  Lemma eval_pows : forall (m : nat) (v : Vector.t F m) (t : F) (k : nat),
    eval (Vector.to_list v) t * fpow t k = fsum (Vector.map2 mul v (pows t k m)).
  Proof.
    induction m as [| m ih]; intros v t k.
    + rewrite (vector_inv_0 v); cbn; field.
    + destruct (vector_inv_S v) as (c & v' & ->).
      cbn [pows]. rewrite map2_cons, fsum_cons, <-ih.
      change (Vector.to_list (c :: v')) with (List.cons c (Vector.to_list v')).
      cbn [eval fpow]; field.
  Qed.

  (* v with its j-th coordinate replaced by zero *)
  Definition zero_at {m : nat} (j : Fin.t m) (v : Vector.t F m) : Vector.t F m :=
    Vector.map2 (fun j' c => if Fin.eq_dec j' j then zero else c) (fins m) v.

  Lemma zero_at_nth : forall (m : nat) (j : Fin.t m) (v : Vector.t F m) (i : Fin.t m),
    (zero_at j v)[@i] = if Fin.eq_dec i j then zero else v[@i].
  Proof.
    intros; unfold zero_at; rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), nth_fins; reflexivity.
  Qed.

  Lemma map2_mul_zero_at : forall (m : nat) (j : Fin.t m) (a b : Vector.t F m),
    Vector.map2 mul a (zero_at j b) = Vector.map2 mul (zero_at j a) b.
  Proof.
    intros; apply Vector.eq_nth_iff; intros i k <-.
    rewrite !(Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), !zero_at_nth.
    destruct (Fin.eq_dec i j); [field | reflexivity].
  Qed.

  Lemma fprod_nonzero : forall (m : nat) (v : Vector.t F m),
    (forall i, v[@i] <> zero) -> fprod v <> zero.
  Proof.
    induction m as [| m ih]; intros v h.
    + rewrite (vector_inv_0 v); cbn; intro e; apply zero_neq_one'; symmetry; exact e.
    + destruct (vector_inv_S v) as (c & v' & ->).
      rewrite fprod_cons. apply mul_nonzero; [exact (h Fin.F1) | apply ih; intro i; exact (h (Fin.FS i))].
  Qed.

  Lemma fprod_zero : forall (m : nat) (v : Vector.t F m) (j : Fin.t m), v[@j] = zero -> fprod v = zero.
  Proof.
    intros m v j; induction j as [m | m j ih]; intro h.
    + destruct (vector_inv_S v) as (c & v' & ->); cbn in h; subst; rewrite fprod_cons; field.
    + destruct (vector_inv_S v) as (c & v' & ->); cbn in h; rewrite fprod_cons, (ih v' h); field.
  Qed.

  Lemma fsum_zeros : forall (m : nat) (v : Vector.t F m), (forall i, v[@i] = zero) -> fsum v = zero.
  Proof.
    induction m as [| m ih]; intros v h.
    + rewrite (vector_inv_0 v); reflexivity.
    + destruct (vector_inv_S v) as (c & v' & ->).
      pose proof (h Fin.F1) as h0; cbn in h0.
      rewrite fsum_cons, h0, ih; [field | intro i; exact (h (Fin.FS i))].
  Qed.

  Lemma fsum_split : forall (m : nat) (j : Fin.t m) (v : Vector.t F m), fsum v = v[@j] + fsum (zero_at j v).
  Proof.
    intros m j; induction j as [m | m j ih]; intro v.
    + destruct (vector_inv_S v) as (c & v' & ->).
      unfold zero_at; cbn [fins]; rewrite map2_cons, !fsum_cons.
      replace (Vector.map2 (fun j' c0 => if Fin.eq_dec j' Fin.F1 then zero else c0) (Vector.map Fin.FS (fins m)) v')
        with v'.
      - cbn. destruct (Fin.eq_dec Fin.F1 Fin.F1) as [_ | ne]; [field | exfalso; apply ne; reflexivity].
      - apply Vector.eq_nth_iff; intros i k <-.
        rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), (Vector.nth_map _ _ i i eq_refl), nth_fins.
        destruct (Fin.eq_dec (Fin.FS i) Fin.F1) as [e | _]; [discriminate e | reflexivity].
    + destruct (vector_inv_S v) as (c & v' & ->).
      unfold zero_at in *; cbn [fins]; rewrite map2_cons, !fsum_cons.
      destruct (Fin.eq_dec Fin.F1 (Fin.FS j)) as [e | _]; [discriminate e |].
      replace (Vector.map2 (fun j' c0 => if Fin.eq_dec j' (Fin.FS j) then zero else c0) (Vector.map Fin.FS (fins m)) v')
        with (Vector.map2 (fun j' c0 => if Fin.eq_dec j' j then zero else c0) (fins m) v').
      - cbn [Vector.nth]. rewrite (ih v'). apply add_swap.
      - apply Vector.eq_nth_iff; intros i k <-.
        rewrite !(Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), (Vector.nth_map _ _ i i eq_refl), !nth_fins.
        destruct (Fin.eq_dec (Fin.FS i) (Fin.FS j)) as [e | ne]; destruct (Fin.eq_dec i j) as [e' | ne'];
          try reflexivity.
        * exfalso; apply ne'; exact (Fin.FS_inj i j e).
        * exfalso; apply ne; rewrite e'; reflexivity.
  Qed.

  Lemma Forall_to_list : forall {A : Type} (P : A -> Prop) (m : nat) (v : Vector.t A m),
    List.Forall P (Vector.to_list v) <-> (forall i, P v[@i]).
  Proof.
    intros A P m; induction m as [| m ih]; intro v.
    + rewrite (vector_inv_0 v); split; [intros _ i; exact (Fin.case0 (fun i => P ([] : Vector.t A 0)[@i]) i) | intros _; constructor].
    + destruct (vector_inv_S v) as (a & v' & ->).
      change (Vector.to_list (a :: v')) with (List.cons a (Vector.to_list v')).
      rewrite List.Forall_cons_iff, ih. split.
      - intros [h1 h2] i; apply (Fin.caseS' i); [exact h1 | exact h2].
      - intro h; split; [exact (h Fin.F1) | intro i; exact (h (Fin.FS i))].
  Qed.

  Lemma unit_vec_nth : forall (m : nat) (j i : Fin.t m), (unit_vec j)[@i] = if Fin.eq_dec i j then one else zero.
  Proof.
    intros m j; induction j as [m | m j ih]; intro i.
    + apply (Fin.caseS' i (fun i => (unit_vec Fin.F1)[@i] = if Fin.eq_dec i Fin.F1 then one else zero)).
      - destruct (Fin.eq_dec (@Fin.F1 m) Fin.F1) as [_ | ne]; [reflexivity | exfalso; apply ne; reflexivity].
      - intro i'; cbn [unit_vec].
        change ((vzero m)[@i'] = if Fin.eq_dec (Fin.FS i') Fin.F1 then one else zero).
        rewrite Vector.const_nth. destruct (Fin.eq_dec (Fin.FS i') Fin.F1) as [e | _]; [discriminate e | reflexivity].
    + apply (Fin.caseS' i (fun i => (unit_vec (Fin.FS j))[@i] = if Fin.eq_dec i (Fin.FS j) then one else zero)).
      - cbn [unit_vec]. change (zero = if Fin.eq_dec Fin.F1 (Fin.FS j) then one else zero).
        destruct (Fin.eq_dec Fin.F1 (Fin.FS j)) as [e | _]; [discriminate e | reflexivity].
      - intro i'; cbn [unit_vec].
        change ((unit_vec j)[@i'] = if Fin.eq_dec (Fin.FS i') (Fin.FS j) then one else zero).
        rewrite ih.
        destruct (Fin.eq_dec i' j) as [e | ne]; destruct (Fin.eq_dec (Fin.FS i') (Fin.FS j)) as [e' | ne']; try reflexivity.
        * exfalso; apply ne'; rewrite e; reflexivity.
        * exfalso; apply ne; exact (Fin.FS_inj i' j e').
  Qed.

  Lemma unit_vec_inj : forall (m : nat) (j j' : Fin.t m), unit_vec j = unit_vec j' -> j = j'.
  Proof.
    intros m j j' h.
    apply (f_equal (fun v => v[@j])) in h. rewrite !unit_vec_nth in h.
    destruct (Fin.eq_dec j j) as [_ | ne]; [| exfalso; apply ne; reflexivity].
    destruct (Fin.eq_dec j j') as [e | _]; [exact e | exfalso; apply zero_neq_one'; symmetry; exact h].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Every unit vector is a column                                     *)
  (* ---------------------------------------------------------------- *)

  (* the polynomial of column i with the j-th coefficient zeroed *)
  Definition colpoly (mat : Vector.t (Vector.t F M) M) (j i : Fin.t M) : list F :=
    Vector.to_list (zero_at j (col mat i)).

  Lemma colpoly_eval : forall mat j i t,
    (matT_mul mat (zero_at j (pows t 0 M)))[@i] = eval (colpoly mat j i) t.
  Proof.
    intros; rewrite matT_nth, map2_mul_zero_at. unfold colpoly.
    rewrite <-(eval_pows M (zero_at j (col mat i)) t 0). cbn [fpow]; field.
  Qed.

  Lemma colpoly_length : forall mat j i, length (colpoly mat j i) = M.
  Proof. intros; unfold colpoly; rewrite Vector.length_to_list; reflexivity. Qed.

  Theorem exists_unit_column : forall (lf : list F) (mat : Vector.t (Vector.t F M) M),
    List.NoDup lf -> (forall x, List.In x lf) -> Nat.lt (Nat.mul M M) (length lf) ->
    (forall e, fprod (matT_mul mat e) = fprod e) ->
    colsum mat = Vector.const one M ->
    forall j : Fin.t M, exists i : Fin.t M, col mat i = unit_vec j.
  Proof.
    intros lf mat hnd hall hlen hprod hcol j.
    destruct (List.Exists_dec (fun i => pzero (colpoly mat j i)) (Vector.to_list (fins M))
      (fun i => pzero_dec (Fdec := Fdec) (colpoly mat j i))) as [hex | hnex].
    + (* some column is zero off j: it is δ_j *)
      apply List.Exists_exists in hex; destruct hex as (i & _ & hz).
      exists i. apply Vector.eq_nth_iff; intros k l <-.
      unfold colpoly, PolyRoots.pzero in hz.
      pose proof (proj1 (Forall_to_list (fun c => c = zero) M (zero_at j (col mat i))) hz) as hz'; clear hz; rename hz' into hz.
      rewrite unit_vec_nth. destruct (Fin.eq_dec k j) as [-> | ne].
      - (* the column sums to one and is zero elsewhere *)
        pose proof (colsum_nth mat i) as hs. rewrite hcol, Vector.const_nth in hs.
        rewrite (fsum_split M j (col mat i)) in hs.
        rewrite (fsum_zeros M (zero_at j (col mat i)) hz) in hs.
        rewrite hs; field.
      - specialize (hz k). rewrite zero_at_nth in hz.
        destruct (Fin.eq_dec k j); [contradiction | exact hz].
    + (* otherwise every column polynomial is non-zero: find a common non-root *)
      exfalso.
      assert (hnz : forall i, ~ pzero (colpoly mat j i)).
      { intros i h; apply hnex; apply List.Exists_exists; exists i; split; [apply to_list_fins_complete | exact h]. }
      destruct (common_nonroot (Fdec := Fdec) lf (List.map (colpoly mat j) (Vector.to_list (fins M))) M hnd) as (t & _ & ht).
      { intros p hp; apply List.in_map_iff in hp; destruct hp as (i & <- & _).
        split; [apply hnz | rewrite colpoly_length; lia]. }
      { rewrite List.length_map, Vector.length_to_list; exact hlen. }
      set (e := zero_at j (pows t 0 M)).
      assert (h1 : fprod (matT_mul mat e) <> zero).
      { apply fprod_nonzero; intro i. unfold e; rewrite colpoly_eval.
        apply ht; apply List.in_map; apply to_list_fins_complete. }
      apply h1. rewrite hprod. apply (fprod_zero M e j).
      unfold e; rewrite zero_at_nth; destruct (Fin.eq_dec j j) as [_ | ne]; [reflexivity | exfalso; apply ne; reflexivity].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* From columns to a permutation                                     *)
  (* ---------------------------------------------------------------- *)

  Section Choice.

    Variable mat : Vector.t (Vector.t F M) M.
    Hypothesis hcols : forall j : Fin.t M, exists i : Fin.t M, col mat i = unit_vec j.

    Definition is_unit_col (j i : Fin.t M) : bool :=
      if vec_dec (V := F) Fdec (col mat i) (unit_vec j) then true else false.

    (* the column that is δ_j, found by search *)
    Definition iota (j : Fin.t M) : Fin.t M :=
      match List.find (is_unit_col j) (Vector.to_list (fins M)) with
      | Some i => i
      | None => j
      end.

    Lemma col_iota : forall j, col mat (iota j) = unit_vec j.
    Proof.
      intro j; unfold iota.
      destruct (List.find (is_unit_col j) (Vector.to_list (fins M))) as [i |] eqn:hf.
      + apply List.find_some in hf; destruct hf as [_ hf]; unfold is_unit_col in hf.
        destruct (vec_dec Fdec (col mat i) (unit_vec j)); [assumption | discriminate].
      + exfalso. destruct (hcols j) as (i & hi).
        pose proof (List.find_none _ _ hf i (to_list_fins_complete M i)) as h.
        unfold is_unit_col in h. destruct (vec_dec Fdec (col mat i) (unit_vec j)); [discriminate | contradiction].
    Qed.

    Lemma iota_inj : forall j j', iota j = iota j' -> j = j'.
    Proof.
      intros j j' h. apply unit_vec_inj.
      rewrite <-(col_iota j), <-(col_iota j'), h; reflexivity.
    Qed.

    (* injective on a finite type: surjective *)
    Lemma iota_surj : forall i, exists j, iota j = i.
    Proof.
      intro i.
      destruct (List.Exists_dec (fun j => iota j = i) (Vector.to_list (fins M)) (fun j => Fin.eq_dec (iota j) i)) as [h | h].
      + apply List.Exists_exists in h; destruct h as (j & _ & hj); exists j; exact hj.
      + exfalso.
        assert (hnot : forall j, iota j <> i).
        { intros j e; apply h; apply List.Exists_exists; exists j; split; [apply to_list_fins_complete | exact e]. }
        set (l := List.map iota (Vector.to_list (fins M))).
        assert (hnd : List.NoDup l).
        { apply Finite.Injective_map_NoDup; [exact iota_inj | apply to_list_fins_nodup]. }
        assert (hincl : List.incl l (List.remove Fin.eq_dec i (Vector.to_list (fins M)))).
        { intros x hx. apply List.in_map_iff in hx; destruct hx as (j & <- & _).
          apply List.in_in_remove; [exact (hnot j) | apply to_list_fins_complete]. }
        pose proof (List.NoDup_incl_length hnd hincl) as hlen.
        pose proof (List.remove_length_lt Fin.eq_dec (Vector.to_list (fins M)) i (to_list_fins_complete M i)) as hlt.
        unfold l in hlen; rewrite List.length_map in hlen. lia.
    Qed.

    Definition kappa (i : Fin.t M) : Fin.t M :=
      match List.find (fun j => if Fin.eq_dec (iota j) i then true else false) (Vector.to_list (fins M)) with
      | Some j => j
      | None => i
      end.

    Lemma iota_kappa : forall i, iota (kappa i) = i.
    Proof.
      intro i; unfold kappa.
      destruct (List.find _ (Vector.to_list (fins M))) as [j |] eqn:hf.
      + apply List.find_some in hf; destruct hf as [_ hf]; cbn in hf.
        destruct (Fin.eq_dec (iota j) i); [assumption | discriminate].
      + exfalso. destruct (iota_surj i) as (j & hj).
        pose proof (List.find_none _ _ hf j (to_list_fins_complete M j)) as h; cbn in h.
        destruct (Fin.eq_dec (iota j) i); [discriminate | contradiction].
    Qed.

    Lemma kappa_iota : forall j, kappa (iota j) = j.
    Proof. intro j; apply iota_inj; apply iota_kappa. Qed.

    Definition the_perm : perm M := mk_perm M iota kappa kappa_iota iota_kappa.

    (* the rows are unit vectors *)
    Lemma rows_unit : forall j, mat[@j] = unit_vec (iota j).
    Proof.
      intro j; apply Vector.eq_nth_iff; intros i k <-.
      rewrite unit_vec_nth.
      assert (hc : mat[@j][@i] = (col mat i)[@j]).
      { unfold col; rewrite (Vector.nth_map _ _ j j eq_refl); reflexivity. }
      rewrite hc, <-(iota_kappa i), col_iota, unit_vec_nth, iota_kappa.
      destruct (Fin.eq_dec j (kappa i)) as [e | ne]; destruct (Fin.eq_dec i (iota j)) as [e' | ne']; try reflexivity.
      + exfalso; apply ne'. rewrite e, iota_kappa; reflexivity.
      + exfalso; apply ne. rewrite e', kappa_iota; reflexivity.
    Qed.

  End Choice.

  Theorem matrix_is_permutation : forall (lf : list F) (mat : Vector.t (Vector.t F M) M),
    List.NoDup lf -> (forall x, List.In x lf) -> Nat.lt (Nat.mul M M) (length lf) ->
    (forall e, fprod (matT_mul mat e) = fprod e) ->
    colsum mat = Vector.const one M ->
    exists π : perm M, forall j, mat[@j] = unit_vec (pf M π j).
  Proof.
    intros * hnd hall hlen hprod hcol.
    pose proof (exists_unit_column lf mat hnd hall hlen hprod hcol) as hcols.
    exists (the_perm mat hcols). intro j; apply (rows_unit mat hcols).
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The soundness theorem                                             *)
  (* ---------------------------------------------------------------- *)

  Local Notation eqs := (@equations F one mul G gid ginv gop gpow N).
  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Infix "^" := gpow.

  Local Notation hcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv
    G (@eq G) gid ginv gop gpow Hvec).
  Local Notation gassoc := (@associative G (@eq G) gop (@monoid_is_associative G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv hcg)))).
  Local Notation gid_l := (@left_identity G (@eq G) gop gid (@monoid_is_left_idenity G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv hcg)))).
  Local Notation ginv_r := (@right_inverse G (@eq G) gop gid ginv (@group_is_right_inverse G (@eq G) gop gid ginv
    (@commutative_group_group G (@eq G) gop gid ginv hcg))).
  Local Notation gcomm := (@commutative G (@eq G) gop (@commutative_group_is_commutative G (@eq G) gop gid ginv hcg)).

  Lemma forallb_false_ex : forall {A : Type} (f : A -> bool) (l : list A),
    List.forallb f l = false -> exists x, List.In x l /\ f x = false.
  Proof.
    intros A f l; induction l as [| a l ih]; intro h; [discriminate |].
    cbn in h. destruct (f a) eqn:ha.
    + destruct (ih h) as (x & hx & hfx); exists x; split; [right; exact hx | exact hfx].
    + exists a; split; [left; reflexivity | exact ha].
  Qed.

  (* from w_j = b^{−f} · X to X = w_j · b^f *)
  Lemma component_eq : forall (X Wj b : G) (f : F), Wj = gop ((ginv b) ^ f) X -> X = gop Wj (b ^ f).
  Proof.
    intros * h. rewrite h, gcomm, gassoc, <-(smul_vadd (Hvec := Hvec)), ginv_r, (gid_pow (Hvec := Hvec)), gid_l.
    reflexivity.
  Qed.

  Theorem tw_soundness : forall (lf : list F) (Hlfn : lf <> List.nil)
    (g y : G) (hs us : Vector.t G M) (ws ws' : Vector.t (G * G) M)
    (wa wc wd wf : Fin.t M -> F) (wbeta : Fin.t M -> Vector.t F M) (wB : Fin.t M -> Vector.t G M)
    (mat : Vector.t (Vector.t F M) M),
    List.NoDup lf -> (forall x, List.In x lf) -> Nat.lt (Nat.mul M M) (length lf) ->
    (* a witness of the five equations for every unit vector *)
    (forall j, eqs (public_of g hs y us (unit_vec j) (wB j) ws ws') (wa j) (wc j) (wd j) (wf j) (wbeta j) mat[@j]) ->
    (* a witness of the five equations for every e *)
    (forall e, exists a c d f betas e' Bs, eqs (public_of g hs y us e Bs ws ws') a c d f betas e') ->
    (* either a non-trivial discrete-logarithm relation among g, h_0, …, h_N *)
    (exists x0 xs, ~ (x0 = zero /\ xs = vzero M) /\ dl_rel (gid := gid) (gop := gop) (gpow := gpow) g hs x0 xs) \/
    (* or a permutation with explicit re-encryption exponents *)
    (exists π : perm M, forall j, ws'[@pf M π j] = (gop (fst ws[@j]) (g ^ wf j), gop (snd ws[@j]) (y ^ wf j))).
  Proof.
    intros lf Hlfn g y hs us ws ws' wa wc wd wf wbeta wB mat hnd hall hlen hunit hany.
    (* the commitment is opened by the unit-vector rounds *)
    set (as' := Vector.map wa (fins M)).
    assert (hu : us = open (gid := gid) (gop := gop) (gpow := gpow) g hs as' mat).
    { apply Vector.eq_nth_iff; intros j k <-.
      unfold open; rewrite (Vector.nth_map2 _ _ _ j j j eq_refl eq_refl).
      unfold as'; rewrite (Vector.nth_map _ _ j j eq_refl), nth_fins.
      exact (opening_from_unit (Hvec := Hvec) g hs y us (wB j) ws ws' j _ _ _ _ _ _ (hunit j)). }
    (* the column sums, from the C equation of the first unit round *)
    pose proof (hunit Fin.F1) as hC1; rewrite hu in hC1.
    destruct (rel_cases (zero := zero) (Fdec := Fdec) g hs _ _
      (relation_C (Hvec := Hvec) g hs y as' mat (unit_vec Fin.F1) (wB Fin.F1) ws ws' _ _ _ _ _ _ hC1))
      as [[_ hcol] | [hnt hrel]].
    2: { left; eexists; eexists; split; [exact hnt | exact hrel]. }
    apply relation_C_trivial in hcol.
    (* decide the polynomial identity over all of F^{N+1} *)
    set (all := List.map fst (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) M)).
    assert (hlf : List.map fst (uniform_with_replacement lf Hlfn) = lf).
    { rewrite uniform_with_replacement_unfold, List.map_map.
      erewrite List.map_ext; [apply List.map_id | intros; reflexivity]. }
    assert (hcomplete : forall e : Vector.t F M, List.In e all).
    { intro e; apply support_repeat_complete; rewrite hlf; exact hall. }
    destruct (List.forallb (fun e => if Fdec (fprod (matT_mul mat e)) (fprod e) then true else false) all) eqn:hdec.
    + (* the identity holds everywhere: the matrix is a permutation *)
      right.
      assert (hprod : forall e, fprod (matT_mul mat e) = fprod e).
      { intro e. pose proof (proj1 (List.forallb_forall _ _) hdec e (hcomplete e)) as h; cbn in h.
        destruct (Fdec (fprod (matT_mul mat e)) (fprod e)); [assumption | discriminate]. }
      destruct (matrix_is_permutation lf mat hnd hall hlen hprod hcol) as (π & hrows).
      exists π. intro j.
      pose proof (relation_F (Hvec := Hvec) g hs y us (wB j) ws ws' j _ _ _ _ _ _ (hunit j)) as hF.
      rewrite hrows, !gexp_unit, !(Vector.nth_map _ _ (pf M π j) (pf M π j) eq_refl) in hF.
      rewrite (surjective_pairing (ws'[@pf M π j])).
      apply (f_equal fst) in hF as hF1; apply (f_equal snd) in hF as hF2; cbn [fst snd] in hF1, hF2.
      f_equal.
      - apply (component_eq _ _ g (wf j)); exact hF1.
      - apply (component_eq _ _ y (wf j)); exact hF2.
    + (* some e violates it: the witness for that e gives a relation *)
      left.
      destruct (forallb_false_ex _ _ hdec) as (e & _ & he); cbn in he.
      destruct (Fdec (fprod (matT_mul mat e)) (fprod e)) as [_ | hne]; [discriminate |].
      destruct (hany e) as (a & c & d & f & betas & e' & Bs & heq).
      rewrite hu in heq.
      destruct (rel_cases (zero := zero) (Fdec := Fdec) g hs _ _
        (relation_A (Hvec := Hvec) g hs y as' mat e Bs ws ws' a c d f betas e' heq)) as [[hA1 hA2] | [hnt hrel]].
      2: { eexists; eexists; split; [exact hnt | exact hrel]. }
      destruct (relation_A_trivial (Hvec := Hvec) as' mat e a e' hA1 hA2) as [_ he'].
      destruct (rel_cases (zero := zero) (Fdec := Fdec) g hs _ _
        (relation_D (Hvec := Hvec) g hs y _ e Bs ws ws' a c d f betas e' heq)) as [[_ hD] | [hnt hrel]].
      2: { eexists; eexists; split; [exact hnt | exact hrel]. }
      exfalso; apply hne. rewrite <-he'. apply relation_D_trivial; exact hD.
  Qed.

End Sound2.
