(* k-special soundness: the algebra behind extractors that use k accepting
   transcripts with distinct challenges.

   - Univariate polynomials over the field class, as coefficient lists with
     PolyRoots' Horner evaluation: products, the linear factors X − r,
     Lagrange basis polynomials for k distinct points and the uniqueness of
     a polynomial of length ≤ k from its values at k points
     (agree_nth, from PolyRoots.roots_bound).
   - The inverse of the Vandermonde matrix of k distinct challenges
     x_0, …, x_{k−1}: the coefficients λ_{ij} of the Lagrange basis satisfy
     Σ_j λ_{ij} x_j^m = δ_{im} (vandermonde_inv).
   - The extractor's algebra in any vector space: if a polynomial with
     vector coefficients c_0, …, c_{k−1} (a list of commitments, of
     ciphertexts, of field elements) is evaluated at k distinct challenges,
     each coefficient is the λ-combination of the k values
     (coeff_from_evals). The evaluation function is abstract, given by its
     Horner equations, so the lemma applies to BayerGroth's veval in G, in
     the ciphertext space and in F alike.
   - The soundness error of k-special soundness: a prover strategy that
     answers fewer than k challenges of the challenge set lf acceptingly is
     accepted with probability at most (k − 1)/|lf|
     (k_special_soundness_error), the analogue of Sigma.v's
     soundness_error_bound. *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith PArith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Crypto Require Import PolyRoots MultiExp.
From Probability Require Import Prob Distr.
Import ListNotations.

Section SigmaK.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).
  Local Notation pzero := (pzero (zero := zero)).

  (* ---------------------------------------------------------------- *)
  (* scalars, powers, lists                                            *)
  (* ---------------------------------------------------------------- *)

  Definition lscale (c : F) (xs : list F) : list F := map (mul c) xs.
  Definition ladd (xs ys : list F) : list F := map (fun p => add (fst p) (snd p)) (combine xs ys).

  Fixpoint fpow (x : F) (k : nat) : F :=
    match k with 0 => one | S k' => x * fpow x k' end.

  (* x^0, x^1, …, x^{k−1} *)
  Fixpoint lpows (x : F) (k : nat) : list F :=
    match k with 0 => [] | S k' => one :: lscale x (lpows x k') end.

  (* the field element k *)
  Fixpoint fnat (k : nat) : F := match k with 0 => zero | S k' => fnat k' + one end.

  (* zero-padded pointwise sum of coefficient lists *)
  Fixpoint padd (xs ys : list F) : list F :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xs', y :: ys' => (x + y) :: padd xs' ys'
    end.

  Lemma padd_nil_r : forall xs, padd xs [] = xs.
  Proof. intros xs; destruct xs; reflexivity. Qed.

  Lemma padd_length : forall xs ys, length (padd xs ys) = Nat.max (length xs) (length ys).
  Proof.
    induction xs as [| a xs ih]; intros ys; [reflexivity |].
    destruct ys as [| b ys]; [reflexivity | cbn; rewrite ih; reflexivity].
  Qed.

  Lemma lpows_length : forall x k, length (lpows x k) = k.
  Proof. intros x k; induction k as [| k ih]; [reflexivity | cbn; unfold lscale; rewrite length_map, ih; reflexivity]. Qed.

  Lemma fpow_add : forall x a b, fpow x (a + b)%nat = fpow x a * fpow x b.
  Proof. induction a as [| a ih]; intros b; cbn [fpow Nat.add]; [field | rewrite ih; field]. Qed.

  Lemma mul_nonzero : forall x y : F, x <> zero -> y <> zero -> x * y <> zero.
  Proof.
    intros x y hx hy h; apply hy.
    assert (e : y = inv x * (x * y)). { field. exact hx. }
    rewrite e, h. field. exact hx.
  Qed.

  Lemma mul_eq_zero : forall x y : F, x * y = zero -> x = zero \/ y = zero.
  Proof.
    intros x y h. destruct (Fdec x zero) as [hx | hx]; [left; exact hx | right].
    assert (e : y = inv x * (x * y)) by (field; exact hx). rewrite e, h; field; exact hx.
  Qed.

  Lemma mul_cancel_l : forall a b c : F, a <> zero -> a * b = a * c -> b = c.
  Proof.
    intros a b c ha h.
    assert (e : b = inv a * (a * b)) by (field; exact ha).
    rewrite e, h; field; exact ha.
  Qed.

  Lemma sub_eq_zero : forall a b : F, a - b = zero -> a = b.
  Proof. intros a b h. assert (e : a = (a - b) + b) by field. rewrite e, h; field. Qed.

  Lemma sub_neq_zero : forall a b : F, a <> b -> a - b <> zero.
  Proof. intros a b h e; apply h; apply sub_eq_zero; exact e. Qed.

  (* finite sums in F *)
  Fixpoint fsum (f : nat -> F) (k : nat) : F :=
    match k with 0 => zero | S k' => fsum f k' + f k' end.

  Lemma fsum_ext : forall f g k, (forall j, (j < k)%nat -> f j = g j) -> fsum f k = fsum g k.
  Proof.
    intros f g k; induction k as [| k ih]; intros h; [reflexivity |].
    cbn; rewrite ih; [rewrite h by lia; reflexivity | intros j hj; apply h; lia].
  Qed.

  Lemma fsum_fold : forall f k, fsum f k = fold_right add zero (map f (seq 0 k)).
  Proof.
    intros f k; induction k as [| k ih]; [reflexivity |].
    rewrite seq_S, Nat.add_0_l, map_app, fold_right_app; cbn [map fold_right fsum]; rewrite ih.
    generalize (seq 0 k); intro l; induction l as [| a l ihl]; cbn; [field | rewrite <-ihl; field].
  Qed.

  Lemma fsum_zero : forall k, fsum (fun _ => zero) k = zero.
  Proof. induction k as [| k ih]; cbn; [reflexivity | rewrite ih; field]. Qed.

  Lemma fsum_delta : forall (c : nat -> F) (i k : nat), (i < k)%nat ->
    fsum (fun m => c m * (if Nat.eqb i m then one else zero)) k = c i.
  Proof.
    intros c i k; induction k as [| k ih]; intros hi; [lia |].
    cbn [fsum]. destruct (Nat.eqb i k) eqn:e.
    + apply Nat.eqb_eq in e; subst k.
      rewrite (fsum_ext _ (fun _ => zero)), fsum_zero; [field |].
      intros j hj. destruct (Nat.eqb i j) eqn:e'; [apply Nat.eqb_eq in e'; lia | field].
    + apply Nat.eqb_neq in e. rewrite ih by lia; field.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* polynomial products                                               *)
  (* ---------------------------------------------------------------- *)

  Lemma eval_padd : forall p q x, eval (padd p q) x = eval p x + eval q x.
  Proof.
    induction p as [| a p ih]; intros q x; [cbn; field |].
    destruct q as [| b q]; [cbn; field |]. cbn [padd eval]; rewrite ih; field.
  Qed.

  Lemma eval_lscale : forall c q x, eval (lscale c q) x = c * eval q x.
  Proof. intros c q x; unfold lscale; induction q as [| b q ih]; cbn [map eval]; [field | rewrite ih; field]. Qed.

  Fixpoint pmulF (p q : list F) : list F :=
    match p with
    | [] => []
    | c :: p' => padd (lscale c q) (zero :: pmulF p' q)
    end.

  Lemma eval_pmulF : forall p q x, eval (pmulF p q) x = eval p x * eval q x.
  Proof.
    induction p as [| c p ih]; intros q x; [cbn; field |].
    cbn [pmulF eval]; rewrite eval_padd, eval_lscale; cbn [eval]; rewrite ih; field.
  Qed.

  (* the linear factor X − r *)
  Definition linear (r : F) : list F := [opp r; one].

  Lemma eval_linear : forall r x, eval (linear r) x = x - r.
  Proof. intros; cbn; field. Qed.

  Lemma length_pmulF : forall p q, p <> [] -> q <> [] -> length (pmulF p q) = (length p + length q - 1)%nat.
  Proof.
    induction p as [| c p ih]; intros q hp hq; [contradiction |].
    cbn [pmulF]; rewrite padd_length; unfold lscale; rewrite length_map; cbn [length].
    destruct p as [| c' p].
    + cbn [pmulF length]. destruct q; [contradiction | cbn; lia].
    + rewrite ih by (assumption || discriminate). destruct q; [contradiction | cbn; lia].
  Qed.

  Lemma length_pmulF_linear : forall r q, q <> [] -> length (pmulF (linear r) q) = S (length q).
  Proof. intros r q hq; rewrite length_pmulF by (discriminate || assumption); cbn [linear length]; lia. Qed.

  (* ∏_{r ∈ rs} (X − r) *)
  Definition prod_lin (rs : list F) : list F := fold_right (fun r acc => pmulF (linear r) acc) [one] rs.

  Lemma eval_prod_lin : forall rs x, eval (prod_lin rs) x = fold_right mul one (map (fun r => x - r) rs).
  Proof.
    induction rs as [| r rs ih]; intros x; [cbn; field |].
    cbn [prod_lin fold_right map]; rewrite eval_pmulF, eval_linear; unfold prod_lin in ih; rewrite ih; reflexivity.
  Qed.

  Lemma prod_lin_nonnil : forall rs, prod_lin rs <> [].
  Proof.
    intros rs; destruct rs as [| r rs]; [discriminate |].
    unfold prod_lin, linear; cbn [fold_right pmulF]. destruct (fold_right _ _ _) as [| a l]; discriminate.
  Qed.

  Lemma length_prod_lin : forall rs, length (prod_lin rs) = S (length rs).
  Proof.
    induction rs as [| r rs ih]; [reflexivity |].
    cbn [prod_lin fold_right]; rewrite length_pmulF_linear by apply prod_lin_nonnil.
    unfold prod_lin in ih; rewrite ih; reflexivity.
  Qed.

  Lemma prod_zero_of_in : forall (f : F -> F) (L : list F) (r : F), In r L -> f r = zero ->
    fold_right mul one (map f L) = zero.
  Proof.
    intros f L r hin hz; induction L as [| a L ih]; [destruct hin |].
    cbn [map fold_right]; destruct hin as [-> | hin]; [rewrite hz; field | rewrite ih by exact hin; field].
  Qed.

  Lemma prod_nonzero : forall (f : F -> F) (L : list F), (forall r, In r L -> f r <> zero) ->
    fold_right mul one (map f L) <> zero.
  Proof.
    intros f L h; induction L as [| a L ih]; cbn [map fold_right].
    + intro e; pose proof (@field_is_zero_neq_one _ _ _ _ _ _ _ _ _ _ Hf) as hz; hnf in hz; apply hz; symmetry; exact e.
    + apply mul_nonzero; [apply h; left; reflexivity | apply ih; intros r hr; apply h; right; exact hr].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* coefficients                                                      *)
  (* ---------------------------------------------------------------- *)

  Lemma nth_padd : forall p q i, nth i (padd p q) zero = nth i p zero + nth i q zero.
  Proof.
    induction p as [| a p ih]; intros q i.
    + cbn [padd]; destruct i; cbn [nth]; field.
    + destruct q as [| b q]; [destruct i; cbn [padd nth]; field |].
      destruct i; cbn [padd nth]; [reflexivity | apply ih].
  Qed.

  Lemma nth_lscale : forall c q i, nth i (lscale c q) zero = c * nth i q zero.
  Proof.
    intros c q; induction q as [| b q ih]; intros i.
    + destruct i; cbn; field.
    + destruct i; cbn [lscale map nth]; [reflexivity | apply ih].
  Qed.

  Lemma pzero_nth : forall p i, pzero p -> nth i p zero = zero.
  Proof.
    intros p i h; revert i; induction p as [| a p ih]; intros i; [destruct i; reflexivity |].
    inversion h; subst; destruct i; cbn [nth]; [reflexivity | apply ih; assumption].
  Qed.

  (* a polynomial of length ≤ |xs| is determined by its values on the
    duplicate-free list xs *)
  Theorem agree_nth : forall (xs : list F) (p q : list F), NoDup xs ->
    (length p <= length xs)%nat -> (length q <= length xs)%nat ->
    (forall x, In x xs -> eval p x = eval q x) ->
    forall i, nth i p zero = nth i q zero.
  Proof.
    intros xs p q hnd hp hq hev i.
    set (d := padd p (lscale (opp one) q)).
    assert (hd : forall x, In x xs -> eval d x = zero).
    { intros x hx; unfold d; rewrite eval_padd, eval_lscale, hev by exact hx; field. }
    assert (hlen : (length d <= length xs)%nat).
    { unfold d; rewrite padd_length; unfold lscale; rewrite length_map; lia. }
    destruct (pzero_dec (zero := zero) (Fdec := Fdec) d) as [hz | hz].
    + pose proof (pzero_nth d i hz) as h; unfold d in h; rewrite nth_padd, nth_lscale in h.
      apply sub_eq_zero. assert (e : nth i p zero - nth i q zero = nth i p zero + opp one * nth i q zero) by field.
      rewrite e; exact h.
    + exfalso. pose proof (roots_bound (Fdec := Fdec) (Hf := Hf) (length d) d (le_n _) hz xs hnd hd). lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Lagrange basis and the inverse Vandermonde matrix                 *)
  (* ---------------------------------------------------------------- *)

  Definition remove_nth {A : Type} (j : nat) (xs : list A) : list A := firstn j xs ++ skipn (S j) xs.

  Lemma length_remove_nth : forall {A : Type} (j : nat) (xs : list A), (j < length xs)%nat ->
    length (remove_nth j xs) = (length xs - 1)%nat.
  Proof. intros A j xs hj; unfold remove_nth; rewrite length_app, length_firstn, length_skipn; lia. Qed.

  Lemma nth_firstn_lt : forall {A : Type} (xs : list A) (i j : nat) (d : A), (i < j)%nat ->
    nth i (firstn j xs) d = nth i xs d.
  Proof.
    intros A xs; induction xs as [| a xs ih]; intros i j d h.
    + rewrite firstn_nil; reflexivity.
    + destruct j; [lia |]. destruct i; [reflexivity | cbn; apply ih; lia].
  Qed.

  Lemma nth_skipn_add : forall {A : Type} (xs : list A) (i j : nat) (d : A),
    nth i (skipn j xs) d = nth (j + i) xs d.
  Proof.
    intros A xs; induction xs as [| a xs ih]; intros i j d.
    + rewrite skipn_nil, !nth_overflow by (cbn; lia); reflexivity.
    + destruct j; [reflexivity | cbn [skipn Nat.add nth]; apply ih].
  Qed.

  Lemma In_firstn' : forall {A : Type} (n : nat) (l : list A) (x : A), In x (firstn n l) -> In x l.
  Proof. intros A n l x h; rewrite <-(firstn_skipn n l); apply in_or_app; left; exact h. Qed.

  Lemma In_remove_nth : forall {A : Type} (j i : nat) (xs : list A) (d : A), (i < length xs)%nat -> i <> j ->
    In (nth i xs d) (remove_nth j xs).
  Proof.
    intros A j i xs d hi hij; unfold remove_nth; apply in_or_app.
    destruct (Nat.lt_ge_cases i j) as [h | h].
    + left. rewrite <-(nth_firstn_lt xs i j d h). apply nth_In. rewrite length_firstn; lia.
    + right. assert (hj : (j < i)%nat) by lia.
      replace (nth i xs d) with (nth (i - S j) (skipn (S j) xs) d) by (rewrite nth_skipn_add; f_equal; lia).
      apply nth_In; rewrite length_skipn; lia.
  Qed.

  Lemma remove_nth_neq : forall (j : nat) (xs : list F), NoDup xs -> (j < length xs)%nat ->
    forall v, In v (remove_nth j xs) -> v <> nth j xs zero.
  Proof.
    intros j xs hnd hj v hv e. unfold remove_nth in hv; apply in_app_or in hv.
    assert (hex : exists i, (i < length xs)%nat /\ i <> j /\ nth i xs zero = v).
    { destruct hv as [hv | hv].
      + destruct (In_nth _ _ zero hv) as (i & hi & hv'). rewrite length_firstn in hi.
        exists i; repeat split; [lia | lia |]. rewrite <-hv'; symmetry; apply nth_firstn_lt; lia.
      + destruct (In_nth _ _ zero hv) as (i & hi & hv'). rewrite length_skipn in hi.
        exists (S j + i)%nat; repeat split; [lia | lia |]. rewrite <-hv'; symmetry; apply nth_skipn_add. }
    destruct hex as (i & hi & hij & hv').
    pose proof (proj1 (NoDup_nth xs zero) hnd) as hn.
    apply hij. apply (hn i j hi hj). rewrite hv'; exact e.
  Qed.

  Definition lag_denom (xs : list F) (j : nat) : F :=
    fold_right mul one (map (fun xl => nth j xs zero - xl) (remove_nth j xs)).

  Definition lag_basis (xs : list F) (j : nat) : list F :=
    lscale (inv (lag_denom xs j)) (prod_lin (remove_nth j xs)).

  Lemma lag_denom_nonzero : forall xs j, NoDup xs -> (j < length xs)%nat -> lag_denom xs j <> zero.
  Proof.
    intros xs j hnd hj; unfold lag_denom; apply prod_nonzero.
    intros v hv; apply sub_neq_zero; intro e; symmetry in e; revert e; apply remove_nth_neq; assumption.
  Qed.

  Lemma eval_lag_basis : forall xs j i, NoDup xs -> (j < length xs)%nat -> (i < length xs)%nat ->
    eval (lag_basis xs j) (nth i xs zero) = if Nat.eqb i j then one else zero.
  Proof.
    intros xs j i hnd hj hi; unfold lag_basis; rewrite eval_lscale, eval_prod_lin.
    destruct (Nat.eqb i j) eqn:e.
    + apply Nat.eqb_eq in e; subst. fold (lag_denom xs j).
      field. apply lag_denom_nonzero; assumption.
    + apply Nat.eqb_neq in e.
      rewrite (prod_zero_of_in _ _ (nth i xs zero)); [ring | apply In_remove_nth; assumption | field].
  Qed.

  Lemma length_lag_basis : forall xs j, (j < length xs)%nat -> length (lag_basis xs j) = length xs.
  Proof.
    intros xs j hj; unfold lag_basis, lscale; rewrite length_map, length_prod_lin, length_remove_nth by exact hj; lia.
  Qed.

  (* the coefficients of the Lagrange basis: the inverse Vandermonde matrix *)
  Definition lam (xs : list F) (i j : nat) : F := nth i (lag_basis xs j) zero.

  (* sums of polynomials *)
  Definition psum (ps : list (list F)) : list F := fold_right padd [] ps.

  Lemma eval_psum : forall ps x, eval (psum ps) x = fold_right add zero (map (fun p => eval p x) ps).
  Proof. intros ps x; unfold psum; induction ps as [| p ps ih]; cbn [fold_right map]; [reflexivity | rewrite eval_padd, ih; reflexivity]. Qed.

  Lemma nth_psum : forall ps i, nth i (psum ps) zero = fold_right add zero (map (fun p => nth i p zero) ps).
  Proof.
    intros ps i; unfold psum; induction ps as [| p ps ih]; cbn [fold_right map].
    + destruct i; reflexivity.
    + rewrite nth_padd, ih; reflexivity.
  Qed.

  Lemma length_psum : forall ps k, (forall p, In p ps -> (length p <= k)%nat) -> (length (psum ps) <= k)%nat.
  Proof.
    intros ps k h; unfold psum; induction ps as [| p ps ih]; cbn [fold_right length]; [lia |].
    rewrite padd_length. specialize (ih (fun q hq => h q (or_intror hq))). specialize (h p (or_introl eq_refl)). lia.
  Qed.

  Definition monomial (m : nat) : list F := repeat zero m ++ [one].

  Lemma eval_monomial : forall m x, eval (monomial m) x = fpow x m.
  Proof. induction m as [| m ih]; intros x; cbn [monomial repeat app eval fpow]; [field | rewrite ih; field]. Qed.

  Lemma nth_monomial : forall m i, nth i (monomial m) zero = if Nat.eqb i m then one else zero.
  Proof.
    induction m as [| m ih]; intros i; cbn [monomial repeat app].
    + destruct i as [| i]; [reflexivity | destruct i; reflexivity].
    + destruct i as [| i]; [reflexivity | cbn [nth]; apply ih].
  Qed.

  Lemma length_monomial : forall m, length (monomial m) = S m.
  Proof. intros m; unfold monomial; rewrite length_app, repeat_length; cbn; lia. Qed.

  Lemma fold_map_seq_delta : forall (f : nat -> F) (i k : nat), (i < k)%nat ->
    fold_right add zero (map (fun j => f j * (if Nat.eqb i j then one else zero)) (seq 0 k)) = f i.
  Proof. intros f i k hi; rewrite <-fsum_fold; apply fsum_delta; exact hi. Qed.

  Theorem vandermonde_inv : forall (xs : list F), NoDup xs ->
    forall i m, (i < length xs)%nat -> (m < length xs)%nat ->
    fsum (fun j => lam xs i j * fpow (nth j xs zero) m) (length xs) = if Nat.eqb i m then one else zero.
  Proof.
    intros xs hnd i m hi hm.
    set (P := psum (map (fun j => lscale (fpow (nth j xs zero) m) (lag_basis xs j)) (seq 0 (length xs)))).
    assert (hP : forall i', (i' < length xs)%nat -> eval P (nth i' xs zero) = fpow (nth i' xs zero) m).
    { intros i' hi'; unfold P; rewrite eval_psum, map_map.
      rewrite <-(fold_map_seq_delta (fun j => fpow (nth j xs zero) m) i' (length xs) hi').
      f_equal; apply map_ext_in; intros j hj; apply in_seq in hj.
      rewrite eval_lscale, eval_lag_basis by (assumption || lia). reflexivity. }
    assert (hlenP : (length P <= length xs)%nat).
    { unfold P; apply length_psum; intros p hp; apply in_map_iff in hp; destruct hp as (j & <- & hj).
      apply in_seq in hj; unfold lscale; rewrite length_map, length_lag_basis by lia; lia. }
    assert (hagree := agree_nth xs P (monomial m) hnd hlenP).
    rewrite length_monomial in hagree. specialize (hagree ltac:(lia)).
    assert (hev : forall x, In x xs -> eval P x = eval (monomial m) x).
    { intros x hx. destruct (In_nth xs x zero hx) as (i' & hi' & <-). rewrite hP, eval_monomial by exact hi'; reflexivity. }
    specialize (hagree hev i). rewrite nth_monomial in hagree. rewrite <-hagree.
    unfold P; rewrite nth_psum, map_map, fsum_fold. f_equal; apply map_ext; intros j.
    rewrite nth_lscale; unfold lam; field.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the extractor's algebra in a vector space                         *)
  (* ---------------------------------------------------------------- *)

  Section VectorCoefficients.

    Context
      {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
      {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

    Local Notation vcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vgroup := (@commutative_group_group V (@eq V) vadd vid vopp vcg).
    Local Notation vmonoid := (@group_monoid V (@eq V) vadd vid vopp vgroup).
    Local Notation vassoc := (@associative V (@eq V) vadd
      (@monoid_is_associative V (@eq V) vadd vid vmonoid)).
    Local Notation vid_l := (@left_identity V (@eq V) vadd vid
      (@monoid_is_left_idenity V (@eq V) vadd vid vmonoid)).
    Local Notation vid_r := (@right_identity V (@eq V) vadd vid
      (@monoid_is_right_identity V (@eq V) vadd vid vmonoid)).
    Local Notation vcomm := (@commutative V (@eq V) vadd
      (@commutative_group_is_commutative V (@eq V) vadd vid vopp vcg)).
    Local Notation vfadd := (@vector_space_smul_distributive_fadd F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vfmul := (@vector_space_smul_associative_fmul F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vvadd := (@vector_space_smul_distributive_vadd F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vone := (@vector_space_field_one F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vzero := (@vector_space_field_zero F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).

    Lemma vsmul_add : forall (v : V) (r s : F), smul v (r + s) = vadd (smul v r) (smul v s).
    Proof. intros; apply vfadd. Qed.
    Lemma vsmul_mul : forall (v : V) (r s : F), smul v (r * s) = smul (smul v r) s.
    Proof. intros; apply vfmul. Qed.
    Lemma vsmul_vadd : forall (u v : V) (r : F), smul (vadd u v) r = vadd (smul u r) (smul v r).
    Proof. intros; apply vvadd. Qed.
    Lemma vsmul_one : forall v : V, smul v one = v.
    Proof. intros; apply vone. Qed.
    Lemma vsmul_zero : forall v : V, smul v zero = vid.
    Proof. intros; apply vzero. Qed.
    Lemma vadd_comm : forall u v : V, vadd u v = vadd v u.
    Proof. intros; apply vcomm. Qed.
    Lemma vadd_assoc : forall u v w : V, vadd u (vadd v w) = vadd (vadd u v) w.
    Proof. intros; apply vassoc. Qed.
    Lemma vadd_vid_l : forall v : V, vadd vid v = v.
    Proof. intros; apply vid_l. Qed.
    Lemma vadd_vid_r : forall v : V, vadd v vid = v.
    Proof. intros; apply vid_r. Qed.
    Lemma vsmul_vid : forall r : F, smul vid r = vid.
    Proof. intros; apply (smul_vid (HV := HV)). Qed.

    Lemma vadd4 : forall a b c d : V, vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d).
    Proof.
      intros a b c d.
      rewrite <-(vassoc a b (vadd c d)), (vassoc b c d), (vcomm b c), <-(vassoc c b d),
        (vassoc a c (vadd b d)); reflexivity.
    Qed.

    (* finite sums in V *)
    Fixpoint vsum (f : nat -> V) (k : nat) : V :=
      match k with 0 => vid | S k' => vadd (vsum f k') (f k') end.

    Lemma vsum_ext : forall f g k, (forall j, (j < k)%nat -> f j = g j) -> vsum f k = vsum g k.
    Proof.
      intros f g k; induction k as [| k ih]; intros h; [reflexivity |].
      cbn; rewrite ih; [rewrite h by lia; reflexivity | intros j hj; apply h; lia].
    Qed.

    Lemma vsum_fold : forall f k, vsum f k = fold_right vadd vid (map f (seq 0 k)).
    Proof.
      intros f k; induction k as [| k ih]; [reflexivity |].
      rewrite seq_S, Nat.add_0_l, map_app, fold_right_app; cbn [map fold_right vsum]; rewrite ih.
      generalize (seq 0 k); intro l; induction l as [| a l ihl]; cbn.
      + rewrite vadd_vid_l, vadd_vid_r; reflexivity.
      + rewrite <-ihl, vadd_assoc; reflexivity.
    Qed.

    Lemma vsum_add : forall f g k, vsum (fun j => vadd (f j) (g j)) k = vadd (vsum f k) (vsum g k).
    Proof.
      intros f g k; induction k as [| k ih]; cbn [vsum]; [rewrite vadd_vid_l; reflexivity |].
      rewrite ih, vadd4; reflexivity.
    Qed.

    Lemma vsum_smul : forall f (c : F) k, smul (vsum f k) c = vsum (fun j => smul (f j) c) k.
    Proof.
      intros f c k; induction k as [| k ih]; cbn [vsum]; [apply vsmul_vid |].
      rewrite vsmul_vadd, ih; reflexivity.
    Qed.

    Lemma vsum_scalar : forall (v : V) (f : nat -> F) k, vsum (fun j => smul v (f j)) k = smul v (fsum f k).
    Proof.
      intros v f k; induction k as [| k ih]; cbn [vsum fsum]; [rewrite vsmul_zero; reflexivity |].
      rewrite ih, vsmul_add; reflexivity.
    Qed.

    Lemma vsum_swap : forall (f : nat -> nat -> V) k1 k2,
      vsum (fun i => vsum (fun j => f i j) k2) k1 = vsum (fun j => vsum (fun i => f i j) k1) k2.
    Proof.
      intros f k1 k2; revert k2; induction k1 as [| k1 ih]; intros k2.
      + cbn [vsum]. induction k2 as [| k2 ih2]; cbn [vsum]; [reflexivity | rewrite <-ih2, vadd_vid_l; reflexivity].
      + cbn [vsum]. rewrite ih, <-vsum_add. reflexivity.
    Qed.

    Lemma vsum_vid : forall k, vsum (fun _ => vid) k = vid.
    Proof. induction k as [| k ih]; cbn; [reflexivity | rewrite ih; apply vadd_vid_l]. Qed.

    Lemma vsum_delta : forall (c : nat -> V) (i k : nat), (i < k)%nat ->
      vsum (fun m => smul (c m) (if Nat.eqb i m then one else zero)) k = c i.
    Proof.
      intros c i k; induction k as [| k ih]; intros hi; [lia |].
      cbn [vsum]. destruct (Nat.eqb i k) eqn:e.
      + apply Nat.eqb_eq in e; subst k. rewrite vsmul_one.
        rewrite (vsum_ext _ (fun _ => vid)), vsum_vid, vadd_vid_l; [reflexivity |].
        intros j hj. destruct (Nat.eqb i j) eqn:e'; [apply Nat.eqb_eq in e'; lia | apply vsmul_zero].
      + apply Nat.eqb_neq in e. rewrite ih, vsmul_zero, vadd_vid_r by lia; reflexivity.
    Qed.

    Lemma vsum_shift : forall (g : nat -> V) k, vsum g (S k) = vadd (g 0%nat) (vsum (fun m => g (S m)) k).
    Proof.
      intros g k; induction k as [| k ih]; cbn [vsum]; [rewrite vadd_vid_l, vadd_vid_r; reflexivity |].
      cbn [vsum] in ih; rewrite ih, vadd_assoc; reflexivity.
    Qed.

    (* an evaluation function given by its Horner equations *)
    Variable ev : list V -> F -> V.
    Hypothesis ev_nil : forall x, ev [] x = vid.
    Hypothesis ev_cons : forall c cs x, ev (c :: cs) x = vadd c (smul (ev cs x) x).

    Lemma ev_expand : forall cs x, ev cs x = vsum (fun m => smul (nth m cs vid) (fpow x m)) (length cs).
    Proof.
      induction cs as [| c cs ih]; intros x; [rewrite ev_nil; reflexivity |].
      rewrite ev_cons, ih, vsum_smul; cbn [length]; rewrite vsum_shift; cbn [nth fpow].
      rewrite vsmul_one. f_equal. apply vsum_ext; intros m hm.
      rewrite <-vsmul_mul. f_equal. field.
    Qed.

    (* the coefficients from the values at k distinct points *)
    Theorem coeff_from_evals : forall (xs : list F) (cs : list V), NoDup xs -> length cs = length xs ->
      forall i, (i < length xs)%nat ->
      nth i cs vid = vsum (fun j => smul (ev cs (nth j xs zero)) (lam xs i j)) (length xs).
    Proof.
      intros xs cs hnd hlen i hi.
      rewrite (vsum_ext _ (fun j => vsum (fun m => smul (nth m cs vid) (lam xs i j * fpow (nth j xs zero) m)) (length xs))).
      2: { intros j hj. rewrite ev_expand, vsum_smul, hlen. apply vsum_ext; intros m hm.
           rewrite <-vsmul_mul. f_equal. field. }
      rewrite vsum_swap.
      rewrite (vsum_ext _ (fun m => smul (nth m cs vid) (if Nat.eqb i m then one else zero))).
      2: { intros m hm. rewrite vsum_scalar, vandermonde_inv by assumption. reflexivity. }
      rewrite vsum_delta by exact hi. reflexivity.
    Qed.

  End VectorCoefficients.

  (* ---------------------------------------------------------------- *)
  (* the soundness error of k-special soundness                        *)
  (* ---------------------------------------------------------------- *)

  Lemma NoDup_firstn : forall {A : Type} (k : nat) (l : list A), NoDup l -> NoDup (firstn k l).
  Proof.
    intros A k l h; rewrite <-(firstn_skipn k l) in h; apply NoDup_app_remove_r in h; exact h.
  Qed.

  Lemma fold_prob_bound : forall (l : list F) (d : positive),
    match fold_right (fun '(_, bx) ax => add_prob ax bx) Prob.zero (map (fun x => (x, mk_prob 1 d)) l) with
    | mk_prob a b => (a * Pos.to_nat d <= length l * Pos.to_nat b)%nat
    end.
  Proof.
    intros l d; induction l as [| x l ih]; cbn [map fold_right length]; [cbn; lia |].
    destruct (fold_right _ _ _) as [a b]; cbn [add_prob].
    rewrite Pos2Nat.inj_mul. nia.
  Qed.

  (* A prover strategy is a predicate e on challenges (accepted or not, the
    announcement being fixed). Either k distinct challenges of the challenge
    set lf are accepted, or a uniform challenge is accepted with probability
    at most (k − 1)/|lf|. *)
  Theorem k_special_soundness_error : forall (e : F -> bool) (lf : list F) (Hlfn : lf <> []) (k : nat),
    NoDup lf -> (0 < k)%nat ->
    (exists cs : list F, length cs = k /\ NoDup cs /\ (forall c, In c cs -> In c lf /\ e c = true)) \/
    leq (@prob_of_an_event F e (uniform_with_replacement lf Hlfn)) (mk_prob (k - 1) (Pos.of_nat (length lf))) = true.
  Proof.
    intros e lf Hlfn k hnd hk.
    set (fl := filter e lf).
    assert (hfnd : NoDup fl) by (apply NoDup_filter; exact hnd).
    destruct (Nat.le_gt_cases k (length fl)) as [hle | hgt].
    + left. exists (firstn k fl). split; [| split].
      - rewrite length_firstn; lia.
      - apply NoDup_firstn; exact hfnd.
      - intros c hc. apply In_firstn' in hc. unfold fl in hc; apply filter_In in hc; exact hc.
    + right.
      unfold prob_of_an_event, list_of_events.
      rewrite uniform_with_replacement_unfold, list_of_events_uniform.
      fold fl. pose proof (fold_prob_bound fl (Pos.of_nat (length lf))) as hb.
      destruct (fold_right _ _ _) as [a b]. cbn [leq]. apply Nat.leb_le. nia.
  Qed.

End SigmaK.
