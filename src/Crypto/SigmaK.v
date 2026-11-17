(** * k-special soundness: polynomial interpolation and the soundness error *)

(** A Sigma protocol is _k-special sound_ if a witness can be computed from
    [k] accepting transcripts that share the first message and have pairwise
    distinct challenges. Schnorr's protocol is 2-special sound; the
    Bayer–Groth shuffle argument and other polynomial-based arguments are
    k-special sound for larger [k], and their extractors all rest on the
    same algebra: the prover's messages are coefficients of a polynomial in
    the challenge, and [k] evaluations at distinct points determine those
    coefficients through the inverse Vandermonde matrix. This file
    develops that algebra once, independently of any particular protocol.
    It contains no protocol definitions itself.

    _Contents._

    - Univariate polynomials over [F] as coefficient lists (lowest degree
      first), evaluated with [PolyRoots.eval] (Horner): sum [padd],
      scaling [lscale], product [pmulF], linear factors [X - r]
      ([linear]) and products of them ([prod_lin]).
    - Uniqueness of interpolation [agree_nth]: two polynomials of length at
      most [|xs|] that agree on the distinct points [xs] have the same
      coefficients. Derived from [PolyRoots.roots_bound].
    - Lagrange basis polynomials [lag_basis] for distinct points and the
      inverse of the Vandermonde matrix [vandermonde_inv]: with
      [λ_ij = lam xs i j], [Σ_j λ_ij · x_j ^ m = δ_im].
    - The extractor's algebra in an arbitrary [F]-vector space [V]
      ([coeff_from_evals]): if [ev] is any evaluation function satisfying the
      Horner equations, then each coefficient [cᵢ] of a length-[k] list is
      the [λ]-combination [Σ_j λ_ij · ev cs x_j] of its [k] values. The
      evaluation is abstract so that the same lemma applies to polynomials
      with coefficients in [F], in the group [G], or in a ciphertext space.
    - The soundness error of k-special soundness
      ([k_special_soundness_error]): a prover strategy either answers [k]
      distinct challenges acceptingly, or is accepted with probability at
      most [(k - 1)/|lf|] for challenges uniform on [lf]. This is the
      [k]-ary analogue of [Sigma.soundness_error_bound].

    Small helpers [lpows] (the power vector [1, x, …, x^(k-1)]),
    [ladd] (pointwise sum) and [fnat] (the field image of a natural number)
    are not used in this file but are exported for [BayerGroth],
    [BayerGrothSound], [BayerGrothZK], [PolyPerm], [LinearSigma] and the
    Schulze frontends. [coeff_from_evals] and [lam] are used by
    [BayerGrothSound]; [k_special_soundness_error] by the
    Bayer–Groth verifier backend.

    Reference: S. Bayer and J. Groth, ‘Efficient zero-knowledge argument for
    correctness of a shuffle’, EUROCRYPT 2012, where the witness-extended
    emulation argument uses exactly this Vandermonde inversion. *)
From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith PArith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Crypto Require Import PolyRoots MultiExp.
From Probability Require Import Prob Distr.
Import ListNotations.

(** ** Polynomials and interpolation over a field *)
Section SigmaK.

  (** An abstract field [F] with decidable equality ([Fdec]) and the field
      axioms [Hf]. No group is needed until [VectorCoefficients]. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  (** Registers [F] with the [field] tactic. *)
  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  (** Local infix notations; [eval] and [pzero] are [PolyRoots]'s Horner
      evaluation and all-zero predicate, specialised to this field. *)
  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).
  Local Notation pzero := (pzero (zero := zero)).

  (** *** Lists, powers and polynomial sums *)

  (** [lscale c xs] multiplies every entry of [xs] by [c]. *)
  Definition lscale (c : F) (xs : list F) : list F := map (mul c) xs.
  (** [ladd xs ys] is the pointwise sum, truncated to the shorter list (it
      uses [combine]). *)
  Definition ladd (xs ys : list F) : list F := map (fun p => add (fst p) (snd p)) (combine xs ys).

  (** [fpow x k] is the power [x ^ k] in [F], by repeated multiplication. *)
  Fixpoint fpow (x : F) (k : nat) : F :=
    match k with 0 => one | S k' => x * fpow x k' end.

  (** [lpows x k] is the list of powers [x ^ 0], [x ^ 1], …, [x ^ (k-1)]. *)
  Fixpoint lpows (x : F) (k : nat) : list F :=
    match k with 0 => [] | S k' => one :: lscale x (lpows x k') end.

  (** [fnat k] is the field element [1 + 1 + … + 1] ([k] times). *)
  Fixpoint fnat (k : nat) : F := match k with 0 => zero | S k' => fnat k' + one end.

  (** [padd xs ys] is the sum of two coefficient lists, padding the shorter
      one with zeros; it is polynomial addition. *)
  Fixpoint padd (xs ys : list F) : list F :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x :: xs', y :: ys' => (x + y) :: padd xs' ys'
    end.

  (** [padd] with an empty right argument is the identity. *)
  Lemma padd_nil_r : forall xs, padd xs [] = xs.
  Proof. intros xs; destruct xs; reflexivity. Qed.

  (** The length of [padd xs ys] is the larger of the two lengths. *)
  Lemma padd_length : forall xs ys, length (padd xs ys) = Nat.max (length xs) (length ys).
  Proof.
    induction xs as [| a xs ih]; intros ys; [reflexivity |].
    destruct ys as [| b ys]; [reflexivity | cbn; rewrite ih; reflexivity].
  Qed.

  (** [lpows x k] has length [k]. *)
  Lemma lpows_length : forall x k, length (lpows x k) = k.
  Proof. intros x k; induction k as [| k ih]; [reflexivity | cbn; unfold lscale; rewrite length_map, ih; reflexivity]. Qed.

  (** [fpow x (a + b) = fpow x a · fpow x b]. *)
  Lemma fpow_add : forall x a b, fpow x (a + b)%nat = fpow x a * fpow x b.
  Proof. induction a as [| a ih]; intros b; cbn [fpow Nat.add]; [field | rewrite ih; field]. Qed.

  (** *** Field facts *)

  (** A product of non-zero field elements is non-zero. *)
  Lemma mul_nonzero : forall x y : F, x <> zero -> y <> zero -> x * y <> zero.
  Proof.
    intros x y hx hy h; apply hy.
    assert (e : y = inv x * (x * y)). { field. exact hx. }
    rewrite e, h. field. exact hx.
  Qed.

  (** Integral-domain property: [x · y = 0] implies [x = 0] or [y = 0]. *)
  Lemma mul_eq_zero : forall x y : F, x * y = zero -> x = zero \/ y = zero.
  Proof.
    intros x y h. destruct (Fdec x zero) as [hx | hx]; [left; exact hx | right].
    assert (e : y = inv x * (x * y)) by (field; exact hx). rewrite e, h; field; exact hx.
  Qed.

  (** Left cancellation by a non-zero factor. *)
  Lemma mul_cancel_l : forall a b c : F, a <> zero -> a * b = a * c -> b = c.
  Proof.
    intros a b c ha h.
    assert (e : b = inv a * (a * b)) by (field; exact ha).
    rewrite e, h; field; exact ha.
  Qed.

  (** [a - b = 0] implies [a = b]. *)
  Lemma sub_eq_zero : forall a b : F, a - b = zero -> a = b.
  Proof. intros a b h. assert (e : a = (a - b) + b) by field. rewrite e, h; field. Qed.

  (** Distinct elements have non-zero difference. *)
  Lemma sub_neq_zero : forall a b : F, a <> b -> a - b <> zero.
  Proof. intros a b h e; apply h; apply sub_eq_zero; exact e. Qed.

  (** [fsum f k] is the finite sum [f 0 + f 1 + … + f (k-1)]. *)
  Fixpoint fsum (f : nat -> F) (k : nat) : F :=
    match k with 0 => zero | S k' => fsum f k' + f k' end.

  (** [fsum] depends only on the values of [f] below [k]. *)
  Lemma fsum_ext : forall f g k, (forall j, (j < k)%nat -> f j = g j) -> fsum f k = fsum g k.
  Proof.
    intros f g k; induction k as [| k ih]; intros h; [reflexivity |].
    cbn; rewrite ih; [rewrite h by lia; reflexivity | intros j hj; apply h; lia].
  Qed.

  (** [fsum] agrees with the [fold_right] sum over [seq 0 k]. *)
  Lemma fsum_fold : forall f k, fsum f k = fold_right add zero (map f (seq 0 k)).
  Proof.
    intros f k; induction k as [| k ih]; [reflexivity |].
    rewrite seq_S, Nat.add_0_l, map_app, fold_right_app; cbn [map fold_right fsum]; rewrite ih.
    generalize (seq 0 k); intro l; induction l as [| a l ihl]; cbn; [field | rewrite <-ihl; field].
  Qed.

  (** A sum of zeros is zero. *)
  Lemma fsum_zero : forall k, fsum (fun _ => zero) k = zero.
  Proof. induction k as [| k ih]; cbn; [reflexivity | rewrite ih; field]. Qed.

  (** Kronecker-delta collapse: [Σ_{m<k} c m · δ_im = c i] for [i < k]. *)
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

  (** *** Polynomial products *)

  (** Evaluation is additive: [eval (padd p q) x = eval p x + eval q x]. *)
  Lemma eval_padd : forall p q x, eval (padd p q) x = eval p x + eval q x.
  Proof.
    induction p as [| a p ih]; intros q x; [cbn; field |].
    destruct q as [| b q]; [cbn; field |]. cbn [padd eval]; rewrite ih; field.
  Qed.

  (** Evaluation is homogeneous: [eval (lscale c q) x = c · eval q x]. *)
  Lemma eval_lscale : forall c q x, eval (lscale c q) x = c * eval q x.
  Proof. intros c q x; unfold lscale; induction q as [| b q ih]; cbn [map eval]; [field | rewrite ih; field]. Qed.

  (** [pmulF p q] is the product of polynomials, by the schoolbook recursion
      [(c + X·p') · q = c·q + X·(p' · q)]. *)
  Fixpoint pmulF (p q : list F) : list F :=
    match p with
    | [] => []
    | c :: p' => padd (lscale c q) (zero :: pmulF p' q)
    end.

  (** Evaluation is multiplicative: [eval (pmulF p q) x = eval p x · eval q x]. *)
  Lemma eval_pmulF : forall p q x, eval (pmulF p q) x = eval p x * eval q x.
  Proof.
    induction p as [| c p ih]; intros q x; [cbn; field |].
    cbn [pmulF eval]; rewrite eval_padd, eval_lscale; cbn [eval]; rewrite ih; field.
  Qed.

  (** [linear r] is the monic linear polynomial [X - r]. *)
  Definition linear (r : F) : list F := [opp r; one].

  (** [eval (linear r) x = x - r]. *)
  Lemma eval_linear : forall r x, eval (linear r) x = x - r.
  Proof. intros; cbn; field. Qed.

  (** For non-empty [p], [q]: the product has length
      [|p| + |q| - 1], i.e. degrees add. *)
  Lemma length_pmulF : forall p q, p <> [] -> q <> [] -> length (pmulF p q) = (length p + length q - 1)%nat.
  Proof.
    induction p as [| c p ih]; intros q hp hq; [contradiction |].
    cbn [pmulF]; rewrite padd_length; unfold lscale; rewrite length_map; cbn [length].
    destruct p as [| c' p].
    + cbn [pmulF length]. destruct q; [contradiction | cbn; lia].
    + rewrite ih by (assumption || discriminate). destruct q; [contradiction | cbn; lia].
  Qed.

  (** Multiplying by a linear factor increases the length by one. *)
  Lemma length_pmulF_linear : forall r q, q <> [] -> length (pmulF (linear r) q) = S (length q).
  Proof. intros r q hq; rewrite length_pmulF by (discriminate || assumption); cbn [linear length]; lia. Qed.

  (** [prod_lin rs] is the polynomial [∏_{r ∈ rs} (X - r)]. *)
  Definition prod_lin (rs : list F) : list F := fold_right (fun r acc => pmulF (linear r) acc) [one] rs.

  (** [eval (prod_lin rs) x = ∏_{r ∈ rs} (x - r)]. *)
  Lemma eval_prod_lin : forall rs x, eval (prod_lin rs) x = fold_right mul one (map (fun r => x - r) rs).
  Proof.
    induction rs as [| r rs ih]; intros x; [cbn; field |].
    cbn [prod_lin fold_right map]; rewrite eval_pmulF, eval_linear; unfold prod_lin in ih; rewrite ih; reflexivity.
  Qed.

  (** [prod_lin rs] is never the empty list. *)
  Lemma prod_lin_nonnil : forall rs, prod_lin rs <> [].
  Proof.
    intros rs; destruct rs as [| r rs]; [discriminate |].
    unfold prod_lin, linear; cbn [fold_right pmulF]. destruct (fold_right _ _ _) as [| a l]; discriminate.
  Qed.

  (** [prod_lin rs] has length [|rs| + 1] (degree [|rs|]). *)
  Lemma length_prod_lin : forall rs, length (prod_lin rs) = S (length rs).
  Proof.
    induction rs as [| r rs ih]; [reflexivity |].
    cbn [prod_lin fold_right]; rewrite length_pmulF_linear by apply prod_lin_nonnil.
    unfold prod_lin in ih; rewrite ih; reflexivity.
  Qed.

  (** A product with a zero factor is zero: if [r ∈ L] and [f r = 0], then
      [∏_{y ∈ L} f y = 0]. *)
  Lemma prod_zero_of_in : forall (f : F -> F) (L : list F) (r : F), In r L -> f r = zero ->
    fold_right mul one (map f L) = zero.
  Proof.
    intros f L r hin hz; induction L as [| a L ih]; [destruct hin |].
    cbn [map fold_right]; destruct hin as [-> | hin]; [rewrite hz; field | rewrite ih by exact hin; field].
  Qed.

  (** A product of non-zero factors is non-zero. *)
  Lemma prod_nonzero : forall (f : F -> F) (L : list F), (forall r, In r L -> f r <> zero) ->
    fold_right mul one (map f L) <> zero.
  Proof.
    intros f L h; induction L as [| a L ih]; cbn [map fold_right].
    + intro e; pose proof (@field_is_zero_neq_one _ _ _ _ _ _ _ _ _ _ Hf) as hz; hnf in hz; apply hz; symmetry; exact e.
    + apply mul_nonzero; [apply h; left; reflexivity | apply ih; intros r hr; apply h; right; exact hr].
  Qed.

  (** *** Coefficients and uniqueness of interpolation *)

  (** The [i]-th coefficient of a sum is the sum of the [i]-th coefficients
      (with zero as default). *)
  Lemma nth_padd : forall p q i, nth i (padd p q) zero = nth i p zero + nth i q zero.
  Proof.
    induction p as [| a p ih]; intros q i.
    + cbn [padd]; destruct i; cbn [nth]; field.
    + destruct q as [| b q]; [destruct i; cbn [padd nth]; field |].
      destruct i; cbn [padd nth]; [reflexivity | apply ih].
  Qed.

  (** The [i]-th coefficient of [lscale c q] is [c] times that of [q]. *)
  Lemma nth_lscale : forall c q i, nth i (lscale c q) zero = c * nth i q zero.
  Proof.
    intros c q; induction q as [| b q ih]; intros i.
    + destruct i; cbn; field.
    + destruct i; cbn [lscale map nth]; [reflexivity | apply ih].
  Qed.

  (** Every coefficient of an all-zero polynomial is zero. *)
  Lemma pzero_nth : forall p i, pzero p -> nth i p zero = zero.
  Proof.
    intros p i h; revert i; induction p as [| a p ih]; intros i; [destruct i; reflexivity |].
    inversion h; subst; destruct i; cbn [nth]; [reflexivity | apply ih; assumption].
  Qed.

  (** _Uniqueness of interpolation._ If [xs] are pairwise distinct, [p] and
      [q] have length at most [|xs|], and [eval p x = eval q x] for every
      [x ∈ xs], then [p] and [q] have the same [i]-th coefficient for every
      [i]. Proof: the difference [d = p - q] vanishes on [|xs|] distinct
      points; if [d] were not identically zero, [roots_bound] would give
      [|xs| < |d| ≤ |xs|]. *)
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

  (** *** Lagrange basis and the inverse Vandermonde matrix *)

  (** [remove_nth j xs] deletes the [j]-th element of [xs]. *)
  Definition remove_nth {A : Type} (j : nat) (xs : list A) : list A := firstn j xs ++ skipn (S j) xs.

  (** Removing an in-range element shortens the list by one. *)
  Lemma length_remove_nth : forall {A : Type} (j : nat) (xs : list A), (j < length xs)%nat ->
    length (remove_nth j xs) = (length xs - 1)%nat.
  Proof. intros A j xs hj; unfold remove_nth; rewrite length_app, length_firstn, length_skipn; lia. Qed.

  (** Indexing into [firstn j xs] below [j] is indexing into [xs]. *)
  Lemma nth_firstn_lt : forall {A : Type} (xs : list A) (i j : nat) (d : A), (i < j)%nat ->
    nth i (firstn j xs) d = nth i xs d.
  Proof.
    intros A xs; induction xs as [| a xs ih]; intros i j d h.
    + rewrite firstn_nil; reflexivity.
    + destruct j; [lia |]. destruct i; [reflexivity | cbn; apply ih; lia].
  Qed.

  (** Indexing into [skipn j xs] at [i] is indexing into [xs] at [j + i]. *)
  Lemma nth_skipn_add : forall {A : Type} (xs : list A) (i j : nat) (d : A),
    nth i (skipn j xs) d = nth (j + i) xs d.
  Proof.
    intros A xs; induction xs as [| a xs ih]; intros i j d.
    + rewrite skipn_nil, !nth_overflow by (cbn; lia); reflexivity.
    + destruct j; [reflexivity | cbn [skipn Nat.add nth]; apply ih].
  Qed.

  (** Membership in a prefix implies membership in the list. *)
  Lemma In_firstn' : forall {A : Type} (n : nat) (l : list A) (x : A), In x (firstn n l) -> In x l.
  Proof. intros A n l x h; rewrite <-(firstn_skipn n l); apply in_or_app; left; exact h. Qed.

  (** Every in-range element other than the [j]-th survives
      [remove_nth j]. *)
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

  (** For a duplicate-free list, no element left after [remove_nth j] equals
      the removed element [nth j xs]. *)
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

  (** [lag_denom xs j = ∏_{l ≠ j} (x_j - x_l)], the denominator of the
      [j]-th Lagrange basis polynomial. *)
  Definition lag_denom (xs : list F) (j : nat) : F :=
    fold_right mul one (map (fun xl => nth j xs zero - xl) (remove_nth j xs)).

  (** [lag_basis xs j = ∏_{l ≠ j} (X - x_l) / ∏_{l ≠ j} (x_j - x_l)], the
      [j]-th Lagrange basis polynomial: it is [1] at [x_j] and [0] at the
      other points. *)
  Definition lag_basis (xs : list F) (j : nat) : list F :=
    lscale (inv (lag_denom xs j)) (prod_lin (remove_nth j xs)).

  (** For distinct points the Lagrange denominator is non-zero. *)
  Lemma lag_denom_nonzero : forall xs j, NoDup xs -> (j < length xs)%nat -> lag_denom xs j <> zero.
  Proof.
    intros xs j hnd hj; unfold lag_denom; apply prod_nonzero.
    intros v hv; apply sub_neq_zero; intro e; symmetry in e; revert e; apply remove_nth_neq; assumption.
  Qed.

  (** Interpolation property: for distinct [xs] and in-range [i], [j],
      [eval (lag_basis xs j) x_i = δ_ij]. *)
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

  (** [lag_basis xs j] has length [|xs|] (degree [|xs| - 1]). *)
  Lemma length_lag_basis : forall xs j, (j < length xs)%nat -> length (lag_basis xs j) = length xs.
  Proof.
    intros xs j hj; unfold lag_basis, lscale; rewrite length_map, length_prod_lin, length_remove_nth by exact hj; lia.
  Qed.

  (** [lam xs i j] is the [i]-th coefficient of the [j]-th Lagrange basis
      polynomial. The matrix [(λ_ij)] is the inverse of the Vandermonde
      matrix [(x_j ^ i)]; see [vandermonde_inv]. *)
  Definition lam (xs : list F) (i j : nat) : F := nth i (lag_basis xs j) zero.

  (** [psum ps] is the sum of a list of polynomials. *)
  Definition psum (ps : list (list F)) : list F := fold_right padd [] ps.

  (** Evaluation of [psum] is the sum of evaluations. *)
  Lemma eval_psum : forall ps x, eval (psum ps) x = fold_right add zero (map (fun p => eval p x) ps).
  Proof. intros ps x; unfold psum; induction ps as [| p ps ih]; cbn [fold_right map]; [reflexivity | rewrite eval_padd, ih; reflexivity]. Qed.

  (** The [i]-th coefficient of [psum] is the sum of the [i]-th
      coefficients. *)
  Lemma nth_psum : forall ps i, nth i (psum ps) zero = fold_right add zero (map (fun p => nth i p zero) ps).
  Proof.
    intros ps i; unfold psum; induction ps as [| p ps ih]; cbn [fold_right map].
    + destruct i; reflexivity.
    + rewrite nth_padd, ih; reflexivity.
  Qed.

  (** If every summand has length at most [k], so does the sum. *)
  Lemma length_psum : forall ps k, (forall p, In p ps -> (length p <= k)%nat) -> (length (psum ps) <= k)%nat.
  Proof.
    intros ps k h; unfold psum; induction ps as [| p ps ih]; cbn [fold_right length]; [lia |].
    rewrite padd_length. specialize (ih (fun q hq => h q (or_intror hq))). specialize (h p (or_introl eq_refl)). lia.
  Qed.

  (** [monomial m] is the coefficient list of [X ^ m]. *)
  Definition monomial (m : nat) : list F := repeat zero m ++ [one].

  (** [eval (monomial m) x = x ^ m]. *)
  Lemma eval_monomial : forall m x, eval (monomial m) x = fpow x m.
  Proof. induction m as [| m ih]; intros x; cbn [monomial repeat app eval fpow]; [field | rewrite ih; field]. Qed.

  (** The [i]-th coefficient of [X ^ m] is [δ_im]. *)
  Lemma nth_monomial : forall m i, nth i (monomial m) zero = if Nat.eqb i m then one else zero.
  Proof.
    induction m as [| m ih]; intros i; cbn [monomial repeat app].
    + destruct i as [| i]; [reflexivity | destruct i; reflexivity].
    + destruct i as [| i]; [reflexivity | cbn [nth]; apply ih].
  Qed.

  (** [monomial m] has length [m + 1]. *)
  Lemma length_monomial : forall m, length (monomial m) = S m.
  Proof. intros m; unfold monomial; rewrite length_app, repeat_length; cbn; lia. Qed.

  (** List form of the Kronecker-delta collapse [fsum_delta]. *)
  Lemma fold_map_seq_delta : forall (f : nat -> F) (i k : nat), (i < k)%nat ->
    fold_right add zero (map (fun j => f j * (if Nat.eqb i j then one else zero)) (seq 0 k)) = f i.
  Proof. intros f i k hi; rewrite <-fsum_fold; apply fsum_delta; exact hi. Qed.

  (** _Inverse Vandermonde._ For pairwise distinct [xs] and indices
      [i, m < |xs|],

      [[
        Σ_{j < |xs|}  λ_ij · x_j ^ m  =  δ_im.
      ]]

      Proof: the polynomial [P = Σ_j x_j ^ m · L_j], with [L_j] the Lagrange
      basis, has length at most [|xs|] and agrees with [X ^ m] on all [xs];
      by [agree_nth] their [i]-th coefficients coincide, and the [i]-th
      coefficient of [P] is the left-hand side. *)
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

  (** ** Coefficient extraction in a vector space

      The extractor's algebra lifted from [F] to any [F]-vector space [V]
      (for example the group [G], with [smul] being exponentiation). *)
  Section VectorCoefficients.

    (** An [F]-vector space [V] with zero [vid], negation [vopp], addition
        [vadd] and scalar multiplication [smul]. The local notations below
        merely project the individual axioms out of [HV]. *)
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

    (** Named forms of the vector-space axioms used below:
        [vsmul_add], [vsmul_mul], [vsmul_vadd], [vsmul_one], [vsmul_zero],
        [vadd_comm], [vadd_assoc], [vadd_vid_l], [vadd_vid_r] and
        [vsmul_vid]. *)
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

    (** Middle-four interchange for the commutative addition of [V]. *)
    Lemma vadd4 : forall a b c d : V, vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d).
    Proof.
      intros a b c d.
      rewrite <-(vassoc a b (vadd c d)), (vassoc b c d), (vcomm b c), <-(vassoc c b d),
        (vassoc a c (vadd b d)); reflexivity.
    Qed.

    (** [vsum f k] is the finite sum [f 0 + … + f (k-1)] in [V]. *)
    Fixpoint vsum (f : nat -> V) (k : nat) : V :=
      match k with 0 => vid | S k' => vadd (vsum f k') (f k') end.

    (** [vsum] depends only on the values of [f] below [k]. *)
    Lemma vsum_ext : forall f g k, (forall j, (j < k)%nat -> f j = g j) -> vsum f k = vsum g k.
    Proof.
      intros f g k; induction k as [| k ih]; intros h; [reflexivity |].
      cbn; rewrite ih; [rewrite h by lia; reflexivity | intros j hj; apply h; lia].
    Qed.

    (** [vsum] agrees with the [fold_right] sum over [seq 0 k]. *)
    Lemma vsum_fold : forall f k, vsum f k = fold_right vadd vid (map f (seq 0 k)).
    Proof.
      intros f k; induction k as [| k ih]; [reflexivity |].
      rewrite seq_S, Nat.add_0_l, map_app, fold_right_app; cbn [map fold_right vsum]; rewrite ih.
      generalize (seq 0 k); intro l; induction l as [| a l ihl]; cbn.
      + rewrite vadd_vid_l, vadd_vid_r; reflexivity.
      + rewrite <-ihl, vadd_assoc; reflexivity.
    Qed.

    (** [vsum] is additive in the summand. *)
    Lemma vsum_add : forall f g k, vsum (fun j => vadd (f j) (g j)) k = vadd (vsum f k) (vsum g k).
    Proof.
      intros f g k; induction k as [| k ih]; cbn [vsum]; [rewrite vadd_vid_l; reflexivity |].
      rewrite ih, vadd4; reflexivity.
    Qed.

    (** Scalar multiplication distributes over [vsum]. *)
    Lemma vsum_smul : forall f (c : F) k, smul (vsum f k) c = vsum (fun j => smul (f j) c) k.
    Proof.
      intros f c k; induction k as [| k ih]; cbn [vsum]; [apply vsmul_vid |].
      rewrite vsmul_vadd, ih; reflexivity.
    Qed.

    (** Pulling a common vector out: [Σ_j v · f j = v · Σ_j f j]. *)
    Lemma vsum_scalar : forall (v : V) (f : nat -> F) k, vsum (fun j => smul v (f j)) k = smul v (fsum f k).
    Proof.
      intros v f k; induction k as [| k ih]; cbn [vsum fsum]; [rewrite vsmul_zero; reflexivity |].
      rewrite ih, vsmul_add; reflexivity.
    Qed.

    (** Exchange of a double finite sum. *)
    Lemma vsum_swap : forall (f : nat -> nat -> V) k1 k2,
      vsum (fun i => vsum (fun j => f i j) k2) k1 = vsum (fun j => vsum (fun i => f i j) k1) k2.
    Proof.
      intros f k1 k2; revert k2; induction k1 as [| k1 ih]; intros k2.
      + cbn [vsum]. induction k2 as [| k2 ih2]; cbn [vsum]; [reflexivity | rewrite <-ih2, vadd_vid_l; reflexivity].
      + cbn [vsum]. rewrite ih, <-vsum_add. reflexivity.
    Qed.

    (** A sum of zero vectors is zero. *)
    Lemma vsum_vid : forall k, vsum (fun _ => vid) k = vid.
    Proof. induction k as [| k ih]; cbn; [reflexivity | rewrite ih; apply vadd_vid_l]. Qed.

    (** Kronecker-delta collapse in [V]: [Σ_{m<k} c m · δ_im = c i]. *)
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

    (** Splitting off the first summand of a [vsum]. *)
    Lemma vsum_shift : forall (g : nat -> V) k, vsum g (S k) = vadd (g 0%nat) (vsum (fun m => g (S m)) k).
    Proof.
      intros g k; induction k as [| k ih]; cbn [vsum]; [rewrite vadd_vid_l, vadd_vid_r; reflexivity |].
      cbn [vsum] in ih; rewrite ih, vadd_assoc; reflexivity.
    Qed.

    (** An abstract evaluation function [ev] for polynomials with
        coefficients in [V] at points of [F], characterised only by the
        Horner equations [ev [] x = 0] and
        [ev (c :: cs) x = c + x · ev cs x]. Keeping it abstract lets the
        same lemma serve every concrete evaluation function. *)
    Variable ev : list V -> F -> V.
    Hypothesis ev_nil : forall x, ev [] x = vid.
    Hypothesis ev_cons : forall c cs x, ev (c :: cs) x = vadd c (smul (ev cs x) x).

    (** Any such [ev] equals the expanded sum
        [ev cs x = Σ_{m < |cs|} x ^ m · c_m]. *)
    Lemma ev_expand : forall cs x, ev cs x = vsum (fun m => smul (nth m cs vid) (fpow x m)) (length cs).
    Proof.
      induction cs as [| c cs ih]; intros x; [rewrite ev_nil; reflexivity |].
      rewrite ev_cons, ih, vsum_smul; cbn [length]; rewrite vsum_shift; cbn [nth fpow].
      rewrite vsmul_one. f_equal. apply vsum_ext; intros m hm.
      rewrite <-vsmul_mul. f_equal. field.
    Qed.

    (** _Coefficients from evaluations._ Let [xs] be pairwise distinct with
        [|cs| = |xs|]. Then for every [i < |xs|],

        [[
          c_i  =  Σ_{j < |xs|}  λ_ij · ev cs x_j.
        ]]

        This is the algebraic core of every k-special-soundness extractor:
        the [k] values the prover committed to (at [k] distinct challenges)
        determine all coefficients. Proof: expand [ev] with [ev_expand],
        swap the double sum, and collapse it with [vandermonde_inv]. *)
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

  (** ** The soundness error of k-special soundness *)

  (** The first [k] elements of a duplicate-free list are duplicate-free. *)
  Lemma NoDup_firstn : forall {A : Type} (k : nat) (l : list A), NoDup l -> NoDup (firstn k l).
  Proof.
    intros A k l h; rewrite <-(firstn_skipn k l) in h; apply NoDup_app_remove_r in h; exact h.
  Qed.

  (** Arithmetic bound on a sum of [|l|] copies of the probability
      [1/d]: the result [a/b] satisfies [a · d ≤ |l| · b], that is, it is at
      most [|l|/d]. *)
  Lemma fold_prob_bound : forall (l : list F) (d : positive),
    match fold_right (fun '(_, bx) ax => add_prob ax bx) Prob.zero (map (fun x => (x, mk_prob 1 d)) l) with
    | mk_prob a b => (a * Pos.to_nat d <= length l * Pos.to_nat b)%nat
    end.
  Proof.
    intros l d; induction l as [| x l ih]; cbn [map fold_right length]; [cbn; lia |].
    destruct (fold_right _ _ _) as [a b]; cbn [add_prob].
    rewrite Pos2Nat.inj_mul. nia.
  Qed.

  (** _Soundness error._ Let [e : F → bool] describe which challenges a
      (deterministic, fixed-first-message) prover strategy answers
      acceptingly, let challenges be uniform on the duplicate-free list
      [lf], and let [k > 0]. Then either

      - there are [k] pairwise distinct challenges in [lf], all accepted
        (so a k-special-soundness extractor applies); or
      - the acceptance probability is at most [(k - 1)/|lf|].

      Proof: if at least [k] challenges in [lf] are accepted, take the first
      [k] of them; otherwise the accepted ones number at most [k - 1] and
      [fold_prob_bound] bounds their total probability. *)
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
