(** * From polynomial identities to permutations *)

(** This file proves the two algebraic facts that turn the conclusion of the
    Bayer–Groth shuffle's product argument into an explicit permutation.

    The first is the root multiset lemma [prod_roots_perm]: if

    [[
      ∏_i (r_i − z) = ∏_i (s_i − z)
    ]]

    holds for every [z] in a duplicate-free list [Zs] that is strictly longer
    than [rs], and [rs] and [ss] have the same length, then [rs] is a
    permutation of [ss]. The two products are polynomials in [z] of degree
    [length rs], so agreement on more points forces equality as coefficient
    lists ([SigmaK.agree_nth]) and hence everywhere; then [r_0] is a root of the
    right-hand side, some [s_j = r_0], and cancelling that common factor at all
    [z ≠ r_0] lets the induction continue.

    The second is the shuffle identity [perm_of_products]: if

    [[
      ∏_i (y·a_i + b_i − z) = ∏_i (y·i + x^i − z)
    ]]

    for all [y] in a duplicate-free set [Y] with [|Y| > 2N²] and all [z] in a
    duplicate-free set [Z] with [|Z| > N], then there is a permutation σ of
    [0..N−1] with [a_i = σ(i)] (as a field element) and [b_i = x^σ(i)] for
    all [i < N]. Instead of a probabilistic Schwartz–Zippel argument, the
    proof counts roots of non-zero linear polynomials in [y]
    ([PolyRoots.common_nonroot]). It needs the field images of [0, ..., N−1]
    to be pairwise distinct, which is a hypothesis (true in a prime field of
    order larger than [N]).

    [perm_of_products] is used in [BayerGrothSound] (extraction of the
    permutation from the product argument); the file is also imported by
    [BayerGrothZK]. Reference: S. Bayer and J. Groth, Efficient zero-knowledge
    argument for correctness of a shuffle, EUROCRYPT 2012. *)
From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Sigma Require Import PolyRoots SigmaK.
Import ListNotations.

(** ** Setting

    An arbitrary field with decidable equality. The local notations
    specialise the polynomial operations of [PolyRoots] and [SigmaK]
    ([eval], [fpow] = powers, [fnat] = the image of a natural number in
    the field, [pmulF] = polynomial multiplication) and some field lemmas
    from [SigmaK] to this field. *)
Section PolyPerm.

  (** The ambient field [F] with its operations, decidable equality [Fdec]
      and field axioms [Hf]. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {Hf : @field F (@eq F) zero one opp add sub mul inv div}.

  Add Field field : (@field_theory_for_stdlib_tactic F eq zero one opp add mul sub inv div Hf).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).
  Local Notation fpow := (fpow (one := one) (mul := mul)).
  Local Notation fnat := (fnat (zero := zero) (one := one) (add := add)).
  Local Notation pmulF := (pmulF (zero := zero) (add := add) (mul := mul)).
  Local Notation agree_nth := (agree_nth (Fdec := Fdec) (Hf := Hf)).
  Local Notation mul_eq_zero := (mul_eq_zero (Fdec := Fdec) (Hf := Hf)).
  Local Notation mul_cancel_l := (mul_cancel_l (Hf := Hf)).
  Local Notation sub_eq_zero := (sub_eq_zero (Hf := Hf)).
  Local Notation sub_neq_zero := (sub_neq_zero (Hf := Hf)).
  Local Notation length_pmulF := (length_pmulF (zero := zero) (add := add) (mul := mul)).
  Local Notation eval_pmulF := (eval_pmulF (Hf := Hf)).

  (** ** Products of linear factors

      [prodz rs z] is the field element [∏_(r ∈ rs) (r − z)]. *)
  Definition prodz (rs : list F) (z : F) : F := fold_right mul one (map (fun r => r - z) rs).

  (** Unfolding [prodz] on a cons: [prodz (r :: rs) z = (r − z) · prodz rs z]. *)
  Lemma prodz_cons : forall r rs z, prodz (r :: rs) z = (r - z) * prodz rs z.
  Proof. reflexivity. Qed.

  (** [prodz] depends only on the multiset of roots: permuting [rs] does not
      change the product (commutativity of multiplication). *)
  Lemma prodz_perm : forall rs ss z, Permutation rs ss -> prodz rs z = prodz ss z.
  Proof.
    intros rs ss z hp; induction hp as [| a l l' hp ih | a b l | l l' l'' hp1 ih1 hp2 ih2].
    + reflexivity.
    + rewrite !prodz_cons, ih; reflexivity.
    + rewrite !prodz_cons; field.
    + rewrite ih1, ih2; reflexivity.
  Qed.

  (** If [prodz rs z = 0] then [z] occurs in [rs]: a field has no zero
      divisors, and the empty product is [one ≠ zero]. *)
  Lemma prodz_zero_in : forall rs z, prodz rs z = zero -> exists r, In r rs /\ r = z.
  Proof.
    induction rs as [| r rs ih]; intros z h.
    + exfalso. unfold prodz in h; cbn in h.
      pose proof (@field_is_zero_neq_one _ _ _ _ _ _ _ _ _ _ Hf) as hz; hnf in hz; apply hz; symmetry; exact h.
    + rewrite prodz_cons in h. destruct (mul_eq_zero _ _ h) as [h' | h'].
      - exists r; split; [left; reflexivity | apply sub_eq_zero; exact h'].
      - destruct (ih z h') as (s & hs & e); exists s; split; [right; exact hs | exact e].
  Qed.

  (** [prod_lin_neg rs] is the coefficient list of the polynomial
      [∏_(r ∈ rs) (r − Z)] in the variable [Z], built by repeatedly multiplying
      by the linear polynomial [[r; −1]]. *)
  Definition prod_lin_neg (rs : list F) : list F :=
    fold_right (fun r acc => pmulF [r; opp one] acc) [one] rs.

  (** Evaluating [prod_lin_neg rs] at [z] gives [prodz rs z]. *)
  Lemma eval_prod_lin_neg : forall rs z, eval (prod_lin_neg rs) z = prodz rs z.
  Proof.
    induction rs as [| r rs ih]; intros z; [cbn; field |].
    unfold prod_lin_neg; cbn [fold_right]; rewrite eval_pmulF; unfold prod_lin_neg in ih; rewrite ih, prodz_cons.
    cbn [eval]; field.
  Qed.

  (** The coefficient list [prod_lin_neg rs] is never empty. *)
  Lemma prod_lin_neg_nonnil : forall rs, prod_lin_neg rs <> [].
  Proof.
    intros rs; destruct rs as [| r rs]; [discriminate |].
    unfold prod_lin_neg; cbn [fold_right pmulF]. destruct (fold_right _ _ _) as [| a l]; discriminate.
  Qed.

  (** [prod_lin_neg rs] has exactly [length rs + 1] coefficients. *)
  Lemma length_prod_lin_neg : forall rs, length (prod_lin_neg rs) = S (length rs).
  Proof.
    induction rs as [| r rs ih]; [reflexivity |].
    unfold prod_lin_neg; cbn [fold_right]; rewrite length_pmulF by (discriminate || apply prod_lin_neg_nonnil).
    unfold prod_lin_neg in ih; rewrite ih; cbn [length]; lia.
  Qed.

  (** If two products [prodz rs] and [prodz ss] with [length rs = length ss]
      agree on more than [length rs] distinct points [Zs], they agree at every
      [z]. Both are polynomials with [length rs + 1] coefficients, so
      [SigmaK.agree_nth] shows the coefficient lists are equal. *)
  Lemma prodz_agree_all : forall (Zs : list F) (rs ss : list F), NoDup Zs ->
    length rs = length ss -> (length rs < length Zs)%nat ->
    (forall z, In z Zs -> prodz rs z = prodz ss z) -> forall z, prodz rs z = prodz ss z.
  Proof.
    intros Zs rs ss hnd hl hlen hag z.
    rewrite <-!eval_prod_lin_neg.
    assert (heq : prod_lin_neg rs = prod_lin_neg ss).
    { apply (nth_ext _ _ zero zero); [rewrite !length_prod_lin_neg; lia |].
      intros i _. apply (agree_nth Zs); [exact hnd | rewrite length_prod_lin_neg; lia | rewrite length_prod_lin_neg; lia |].
      intros x hx; rewrite !eval_prod_lin_neg; apply hag; exact hx. }
    rewrite heq; reflexivity.
  Qed.

  (** Removing all occurrences of a value [r] from a duplicate-free list [Zs]
      removes at most one element. *)
  Lemma filter_neq_length : forall (Zs : list F) (r : F), NoDup Zs ->
    (length Zs <= S (length (filter (fun z => if Fdec z r then false else true) Zs)))%nat.
  Proof.
    intros Zs r hnd; induction Zs as [| a Zs ih]; [cbn; lia |].
    inversion hnd as [| ? ? hnin hnd']; subst. specialize (ih hnd').
    cbn [filter]. destruct (Fdec a r) as [-> | hne].
    + assert (hall : filter (fun z => if Fdec z r then false else true) Zs = Zs).
      { clear ih hnd hnd'. induction Zs as [| b Zs ihS]; [reflexivity |].
        cbn [filter]. destruct (Fdec b r) as [-> | hb]; [exfalso; apply hnin; left; reflexivity |].
        rewrite ihS; [reflexivity | intro h; apply hnin; right; exact h]. }
      rewrite hall; cbn; lia.
    + cbn [length]; lia.
  Qed.

  (** ** The root multiset lemma

      If [length rs = length ss], [Zs] is duplicate-free with
      [length rs < length Zs], and [prodz rs z = prodz ss z] for every
      [z ∈ Zs], then [Permutation rs ss].

      Proof idea: induction on [rs]. For [rs = r :: rs'], agreement everywhere
      ([prodz_agree_all]) gives [prodz ss r = 0], so [ss = ss1 ++ r :: ss2]
      ([prodz_zero_in]). On the points of [Zs] different from [r] (at least
      [length rs' + 1] of them, by [filter_neq_length]) the factor [r − z] is
      non-zero and can be cancelled, giving the hypothesis for [rs'] and
      [ss1 ++ ss2]. *)
  Theorem prod_roots_perm : forall (rs ss : list F) (Zs : list F), NoDup Zs ->
    length rs = length ss -> (length rs < length Zs)%nat ->
    (forall z, In z Zs -> prodz rs z = prodz ss z) -> Permutation rs ss.
  Proof.
    induction rs as [| r rs ih]; intros ss Zs hnd hl hlen hag.
    + destruct ss; [constructor | discriminate].
    + pose proof (prodz_agree_all Zs (r :: rs) ss hnd hl hlen hag) as hall.
      assert (hr : prodz ss r = zero).
      { rewrite <-hall, prodz_cons. assert (e : r - r = zero) by field. rewrite e; field. }
      destruct (prodz_zero_in ss r hr) as (s & hs & ->).
      destruct (in_split _ _ hs) as (ss1 & ss2 & ->).
      assert (hperm : Permutation (r :: ss1 ++ ss2) (ss1 ++ r :: ss2)) by apply Permutation_middle.
      set (S' := filter (fun z => if Fdec z r then false else true) Zs).
      assert (hS' : NoDup S') by (apply NoDup_filter; exact hnd).
      assert (hlenS' : (length rs < length S')%nat).
      { pose proof (filter_neq_length Zs r hnd) as h; unfold S'; cbn [length] in hlen; lia. }
      assert (hl' : length rs = length (ss1 ++ ss2)).
      { rewrite length_app in *; cbn [length] in hl; lia. }
      assert (hag' : forall z, In z S' -> prodz rs z = prodz (ss1 ++ ss2) z).
      { intros z hz. unfold S' in hz; apply filter_In in hz; destruct hz as [hz hne].
        destruct (Fdec z r) as [| hne']; [discriminate |].
        specialize (hall z). rewrite <-(prodz_perm _ _ z hperm), !prodz_cons in hall.
        apply (mul_cancel_l (r - z)); [apply sub_neq_zero; intro e; apply hne'; symmetry; exact e | exact hall]. }
      specialize (ih (ss1 ++ ss2) S' hS' hl' hlenS' hag').
      eapply Permutation_trans; [apply perm_skip; exact ih | exact hperm].
  Qed.

  (** ** From the product identity to a permutation

      Indexing helper: the [i]-th element of [map f (seq 0 n)] is [f i] for
      [i < n]. *)
  Lemma nth_map_seq : forall {A : Type} (f : nat -> A) (n i : nat) (d : A), (i < n)%nat ->
    nth i (map f (seq 0 n)) d = f i.
  Proof.
    intros A f n i d hi.
    rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
    rewrite map_nth, seq_nth by exact hi; reflexivity.
  Qed.

  (** The linear polynomial [[c0; c1]] (meaning [c0 + c1·y]) is not identically
      zero unless both coefficients are zero. *)
  Lemma linear_nonzero : forall c0 c1 : F, ~ (c1 = zero /\ c0 = zero) -> ~ pzero (zero := zero) [c0; c1].
  Proof.
    intros c0 c1 h hz. inversion hz as [| ? ? h0 hz']; subst. inversion hz' as [| ? ? h1 _]; subst.
    apply h; split; (assumption || reflexivity).
  Qed.

  (** Evaluation of a linear polynomial: [eval [c0; c1] y = c1·y + c0]. *)
  Lemma eval_linear2 : forall c0 c1 y, eval [c0; c1] y = c1 * y + c0.
  Proof. intros; cbn; field. Qed.

  (** For one fixed [y]: if the products [∏_(i<N) (y·a_i + b_i − z)] and
      [∏_(i<N) (y·i + x^i − z)] agree on more than [N] distinct values [z],
      then the lists of values [y·a_i + b_i] and [y·i + x^i] are permutations of
      each other. A direct instance of [prod_roots_perm]. *)
  Lemma products_perm : forall (N : nat) (a b : list F) (x y : F) (Z : list F),
    NoDup Z -> (N < length Z)%nat ->
    (forall z, In z Z ->
      fold_right mul one (map (fun i => y * nth i a zero + nth i b zero - z) (seq 0 N)) =
      fold_right mul one (map (fun i => y * fnat i + fpow x i - z) (seq 0 N))) ->
    Permutation (map (fun i => y * nth i a zero + nth i b zero) (seq 0 N)) (map (fun i => y * fnat i + fpow x i) (seq 0 N)).
  Proof.
    intros N a b x y Z hnd hlen hag.
    apply (prod_roots_perm _ _ Z hnd); [rewrite !length_map; reflexivity | rewrite length_map, length_seq; exact hlen |].
    intros z hz; unfold prodz; rewrite !map_map; apply hag; exact hz.
  Qed.

  (** Main theorem. Let [a], [b] have length [N], assume the field images
      [fnat 0, ..., fnat (N−1)] are pairwise distinct, let [Y] and [Z] be
      duplicate-free with [2·N² < |Y|] and [N < |Z|], and suppose

      [[
        ∏_(i<N) (y·a_i + b_i − z) = ∏_(i<N) (y·fnat i + x^i − z)
      ]]

      for all [y ∈ Y], [z ∈ Z]. Then there is a list [σ] that is a permutation
      of [seq 0 N] such that, for all [i < N], [a_i = fnat σ(i)] and
      [b_i = x^σ(i)].

      Proof idea:

      - Step 1: for every [y ∈ Y] the values [y·a_i + b_i] are a permutation of
        the values [y·j + x^j] ([products_perm]).
      - Step 2: every pair [(a_i, b_i)] equals some [(fnat j, x^j)]. Otherwise
        the [N] linear polynomials [(a_i − j)·y + (b_i − x^j)] are all non-zero,
        so [common_nonroot] gives [y ∈ Y] at which none vanishes, contradicting
        Step 1 at that [y].
      - Step 3: for some [y ∈ Y] the right-hand values [y·j + x^j] are pairwise
        distinct, again by [common_nonroot] applied to the at most [N²]
        polynomials [(j − j')·y + (x^j − x^j')] with [j ≠ j'], which are
        non-zero because the [fnat j] are distinct.
      - Step 4: at that [y] the left-hand values are also pairwise distinct
        (they are a permutation of a duplicate-free list), so [i ↦ σ(i)],
        defined by searching for the [j] of Step 2, is injective on [0..N−1]
        and therefore a permutation. *)
  Theorem perm_of_products : forall (N : nat) (a b : list F) (x : F) (Y Z : list F),
    length a = N -> length b = N ->
    (forall i j, (i < N)%nat -> (j < N)%nat -> fnat i = fnat j -> i = j) ->
    NoDup Y -> NoDup Z -> (N < length Z)%nat -> (2 * (N * N) < length Y)%nat ->
    (forall y z, In y Y -> In z Z ->
      fold_right mul one (map (fun i => y * nth i a zero + nth i b zero - z) (seq 0 N)) =
      fold_right mul one (map (fun i => y * fnat i + fpow x i - z) (seq 0 N))) ->
    exists σ : list nat, Permutation σ (seq 0 N) /\
      forall i, (i < N)%nat -> nth i a zero = fnat (nth i σ 0%nat) /\ nth i b zero = fpow x (nth i σ 0%nat).
  Proof.
    intros N a b x Y Z hla hlb hinj hndY hndZ hlZ hlY hag.
    (* Step 1: the multiset equality at every y ∈ Y. *)
    assert (hperm : forall y, In y Y ->
      Permutation (map (fun i => y * nth i a zero + nth i b zero) (seq 0 N)) (map (fun i => y * fnat i + fpow x i) (seq 0 N))).
    { intros y hy; apply (products_perm N a b x y Z hndZ hlZ); intros z hz; apply hag; assumption. }
    (* Step 2: each (a_i, b_i) is some (fnat j, x^j). *)
    assert (hsome : forall i, (i < N)%nat -> exists j, (j < N)%nat /\ nth i a zero = fnat j /\ nth i b zero = fpow x j).
    { intros i hi.
      destruct (Exists_dec (fun j => nth i a zero = fnat j /\ nth i b zero = fpow x j) (seq 0 N)) as [hex | hnex].
      { intro j; destruct (Fdec (nth i a zero) (fnat j)), (Fdec (nth i b zero) (fpow x j)); tauto. }
      + apply Exists_exists in hex; destruct hex as (j & hj & hj'); apply in_seq in hj; exists j; split; [lia | exact hj'].
      + exfalso.
        (* Otherwise the N linear polynomials (a_i − j)·y + (b_i − x^j) are all
           non-zero and have a common non-root y ∈ Y ... *)
        set (ps := map (fun j => [nth i b zero - fpow x j; nth i a zero - fnat j]) (seq 0 N)).
        assert (hps : forall p, In p ps -> ~ pzero (zero := zero) p /\ (length p <= 2)%nat).
        { intros p hp; unfold ps in hp; apply in_map_iff in hp; destruct hp as (j & <- & hj); split; [| reflexivity].
          apply linear_nonzero; intros [h1 h0]; apply hnex; apply Exists_exists; exists j; split; [exact hj |].
          split; apply sub_eq_zero; assumption. }
        assert (hbound : (length ps * 2 < length Y)%nat) by (unfold ps; rewrite length_map, length_seq; nia).
        destruct (common_nonroot (Fdec := Fdec) (Hf := Hf) Y ps 2 hndY hps hbound) as (y & hy & hnr).
        (* ... but at that y, y·a_i + b_i is one of the y·j + x^j: contradiction. *)
        specialize (hperm y hy).
        assert (hin : In (y * nth i a zero + nth i b zero) (map (fun i => y * fnat i + fpow x i) (seq 0 N))).
        { eapply Permutation_in; [exact hperm |]. apply in_map_iff; exists i; split; [reflexivity | apply in_seq; lia]. }
        apply in_map_iff in hin; destruct hin as (j & he & hj).
        apply (hnr [nth i b zero - fpow x j; nth i a zero - fnat j]).
        - unfold ps; apply in_map_iff; exists j; split; [reflexivity | exact hj].
        - rewrite eval_linear2.
          assert (e : (nth i a zero - fnat j) * y + (nth i b zero - fpow x j) =
            (y * nth i a zero + nth i b zero) - (y * fnat j + fpow x j)) by field.
          rewrite e, <-he; field. }
    (* Step 3: a y ∈ Y at which the values y·j + x^j are pairwise distinct. *)
    assert (hdist : exists y, In y Y /\ forall j j', (j < N)%nat -> (j' < N)%nat -> j <> j' ->
      y * fnat j + fpow x j <> y * fnat j' + fpow x j').
    { set (pairs := filter (fun p => negb (Nat.eqb (fst p) (snd p))) (list_prod (seq 0 N) (seq 0 N))).
      set (qs := map (fun p => [fpow x (fst p) - fpow x (snd p); fnat (fst p) - fnat (snd p)]) pairs).
      assert (hqs : forall q, In q qs -> ~ pzero (zero := zero) q /\ (length q <= 2)%nat).
      { intros q hq; unfold qs in hq; apply in_map_iff in hq; destruct hq as ((j, j') & <- & hp); split; [| reflexivity].
        unfold pairs in hp; apply filter_In in hp; destruct hp as [hp hne]; apply in_prod_iff in hp; destruct hp as [hj hj'].
        apply in_seq in hj, hj'; cbn [fst snd] in *.
        apply linear_nonzero; intros [h1 _]; apply sub_eq_zero in h1; apply hinj in h1; [| lia | lia].
        subst; rewrite Nat.eqb_refl in hne; discriminate. }
      assert (hbound : (length qs * 2 < length Y)%nat).
      { unfold qs, pairs; rewrite length_map.
        pose proof (filter_length_le (fun p : nat * nat => negb (Nat.eqb (fst p) (snd p))) (list_prod (seq 0 N) (seq 0 N))) as h.
        rewrite prod_length, length_seq in h. nia. }
      destruct (common_nonroot (Fdec := Fdec) (Hf := Hf) Y qs 2 hndY hqs hbound) as (y & hy & hnr).
      exists y; split; [exact hy |].
      intros j j' hj hj' hne he.
      apply (hnr [fpow x j - fpow x j'; fnat j - fnat j']).
      + unfold qs; apply in_map_iff; exists (j, j'); split; [reflexivity |].
        unfold pairs; apply filter_In; split; [apply in_prod_iff; split; apply in_seq; lia |].
        cbn [fst snd]; apply Bool.negb_true_iff; apply Nat.eqb_neq; exact hne.
      + rewrite eval_linear2. assert (e : (fnat j - fnat j') * y + (fpow x j - fpow x j') = (y * fnat j + fpow x j) - (y * fnat j' + fpow x j')) by field.
        rewrite e, he; field. }
    destruct hdist as (y & hy & hdist).
    (* Step 4: at that y the left-hand values are distinct too, so i ↦ σ(i) is
       injective. *)
    assert (hinjL : forall i i', (i < N)%nat -> (i' < N)%nat ->
      y * nth i a zero + nth i b zero = y * nth i' a zero + nth i' b zero -> i = i').
    { intros i i' hi hi' he.
      assert (hndR : NoDup (map (fun i => y * fnat i + fpow x i) (seq 0 N))).
      { apply (proj2 (NoDup_nth _ zero)). rewrite length_map, length_seq. intros j j' hj hj' e.
        rewrite !nth_map_seq in e by assumption. destruct (Nat.eq_dec j j') as [| hne]; [assumption |].
        exfalso; apply (hdist j j' hj hj' hne e). }
      assert (hndL : NoDup (map (fun i => y * nth i a zero + nth i b zero) (seq 0 N))).
      { eapply Permutation_NoDup; [apply Permutation_sym; apply hperm; exact hy | exact hndR]. }
      pose proof (proj1 (NoDup_nth _ zero) hndL) as h. rewrite length_map, length_seq in h.
      apply h; [exact hi | exact hi' | rewrite !nth_map_seq by assumption; exact he]. }
    (* Define σ(i) as the first j found by Step 2, by a decidable search. *)
    set (test := fun i j => if Fdec (nth i a zero) (fnat j) then (if Fdec (nth i b zero) (fpow x j) then true else false) else false).
    set (σat := fun i => match find (test i) (seq 0 N) with Some j => j | None => 0%nat end).
    assert (hσ : forall i, (i < N)%nat -> (σat i < N)%nat /\ nth i a zero = fnat (σat i) /\ nth i b zero = fpow x (σat i)).
    { intros i hi. unfold σat.
      destruct (find (test i) (seq 0 N)) as [j |] eqn:hf.
      + apply find_some in hf; destruct hf as [hj ht]; apply in_seq in hj.
        unfold test in ht. destruct (Fdec (nth i a zero) (fnat j)) as [ha |]; [| discriminate].
        destruct (Fdec (nth i b zero) (fpow x j)) as [hb |]; [| discriminate].
        split; [lia | split; assumption].
      + exfalso. destruct (hsome i hi) as (j & hj & ha & hb).
        pose proof (find_none _ _ hf j ltac:(apply in_seq; lia)) as h.
        unfold test in h. destruct (Fdec (nth i a zero) (fnat j)); [| contradiction].
        destruct (Fdec (nth i b zero) (fpow x j)); [discriminate | contradiction]. }
    (* σ is an injective map from 0..N−1 into 0..N−1, hence a permutation. *)
    exists (map σat (seq 0 N)). split.
    + apply NoDup_Permutation_bis.
      - apply (proj2 (NoDup_nth _ 0%nat)). rewrite length_map, length_seq. intros i i' hi hi' e.
        rewrite !nth_map_seq in e by assumption.
        destruct (hσ i hi) as (_ & ha & hb), (hσ i' hi') as (_ & ha' & hb').
        apply (hinjL i i' hi hi'). rewrite ha, hb, ha', hb', e; reflexivity.
      - rewrite !length_map, !length_seq; lia.
      - intros j hj. apply in_map_iff in hj; destruct hj as (i & <- & hi); apply in_seq in hi.
        apply in_seq. destruct (hσ i ltac:(lia)) as (h & _ & _); lia.
    + intros i hi. rewrite nth_map_seq by exact hi. destruct (hσ i hi) as (_ & ha & hb); split; assumption.
  Qed.

End PolyPerm.
