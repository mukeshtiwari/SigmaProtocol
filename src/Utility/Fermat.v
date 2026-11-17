(** * Fermat's little theorem

    This file proves Fermat's little theorem from first principles, by the
    classical binomial argument, and then transfers it to the forms needed by
    the rest of the development:

    - [fermat_little_simp]: [n ^ p ≡ n (mod p)] for every natural [n] and prime [p];
    - [fermat_little_coprime]: [a ^ (p-1) ≡ 1 (mod p)] whenever [p ∤ a];
    - [fermat_little_Z] and [fermat_little_ZZ]: the same statement for the
      standard library's [Zpow_mod] (over [N]-valued and [Z]-valued inputs);
    - [fermat_bound_gen] and [fermat_bound]: [0 < a ^ n mod p < p] for
      [0 < a < p], in particular for the Fermat inverse [a ^ (p-2) mod p].

    These facts are consumed by [Zpstar.v], which builds the multiplicative
    group [Z_p^*] with inverses computed as [a ^ (p-2) mod p]: Fermat's theorem
    is exactly the statement that this is an inverse, and the bound lemmas show
    that the result lies again in [{1, …, p-1}].

    The proof structure is as follows.

    - Binomial coefficients are defined by Pascal's rule ([binomial_exp]) and
      linked to factorials: [(n+k)! = k! · n! · C(n+k, n)]
      ([connect_fact_with_binomial_exp_def]).
    - The binomial theorem [(x+y)^n = Σ_k C(n,k) x^k y^(n-k)] is proved
      ([pow_add]) by representing the expansion as an explicit list of
      triples (exponent of [x], exponent of [y], coefficient)
      ([populate_terms]); multiplying by [x] and by [y] shifts the exponents,
      and adding the two shifted lists term by term ([add_polynomials])
      yields the list for [n+1] ([add_poly_def_correct]).
    - For a prime [p], [p] divides [C(p,k)] exactly when [0 < k < p]
      ([binom_mod_p]), hence [(x+1)^p ≡ x^p + 1 (mod p)] ([prime_pow_exp]),
      and induction on [n] gives [n^p ≡ n].
    - Cancelling one factor [a] (allowed since [p ∤ a] and [p] is prime,
      [mod_simpl]) gives [a^(p-1) ≡ 1].

    The file also contains a few generic list helpers ([take], [drop],
    [zip_with], [nth_ext_error]); they are local to this proof and are distinct
    from the vector operations of the same names in [Util.v]. *)
From Stdlib Require Import
  NArith Znumtheory Lia
  Zdiv Znat Zpow_facts List
  Peano PeanoNat.
From Utility Require Import
  Functions Util.

Import ListNotations.

(** ** Binomial coefficients

    Pascal-triangle binomial coefficients on [nat] and their relationship with
    factorials. *)
Section Fermat_Little_Theorem.

  (** [binomial_exp n k] is the binomial coefficient [C(n, k)], defined by
      Pascal's rule [C(n+1, k+1) = C(n, k+1) + C(n, k)] with [C(n, 0) = 1] and
      [C(0, k+1) = 0].  The definition is structural, so values are computed by
      the kernel without division. *)
  Fixpoint binomial_exp (n k : nat) : nat :=
   match n with
   | O => match k with
    | O => S O
    | S _ => O
    end
   | S n' => match k with
    | O => S O
    | S k' => binomial_exp n' k + binomial_exp n' k'
    end
   end.

  (** [C(n, 0) = 1]. *)
  Lemma nCo : forall n, (binomial_exp n 0 = 1)%nat.
  Proof.
    destruct n; simpl; reflexivity.
  Qed.

  (** [C(n, 1) = n]. *)
  Lemma nCone : forall n, (binomial_exp n 1 = n)%nat.
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. rewrite IHn, nCo.
      lia.
  Qed.

  (** [C(n, k) = 0] when [n < k]. *)
  Lemma k_gt_n : forall (n k : nat), (n < k)%nat -> (binomial_exp n k = 0)%nat.
  Proof.
    induction n.
    - destruct k; simpl; intros Hf.
      lia. reflexivity.
    - destruct k; simpl; intros Hf;
      try lia.
      assert (Ht : (n < k)%nat) by lia.
      pose proof (IHn k Ht) as H₁.
      rewrite H₁. clear Ht; clear H₁.
      assert (Ht : (n < S k)%nat) by lia.
      pose proof (IHn (S k) Ht) as H₁.
      rewrite H₁. lia.
  Qed.

  (** [C(n, n) = 1]. *)
  Lemma nCn : forall n, (binomial_exp n n = 1)%nat.
  Proof.
    induction n.
    - simpl. reflexivity.
    - simpl. assert (Ht : (n < S n)%nat) by lia.
      pose proof (k_gt_n n (S n) Ht) as H.
      rewrite H. lia.
  Qed.

  (** Pascal's rule as an equation: [C(n+1, k+1) = C(n, k+1) + C(n, k)]. *)
  Lemma snCsk : forall (n k : nat),
    binomial_exp (S n) (S k) = (binomial_exp n (S k) + binomial_exp n k)%nat.
  Proof.
    intros ? ?; simpl;
    reflexivity.
  Qed.

  (** Factorial form of the binomial coefficient:
      [(n+k)! = k! · n! · C(n+k, n)].  The proof is a double induction on [k]
      and [n] using Pascal's rule; it is the link that lets [binom_mod_p] reason
      about divisibility of [C(p, k)] by [p]. *)
  Lemma connect_fact_with_binomial_exp_def : forall k n,
    fact (n + k) = (fact k * fact n * binomial_exp (n + k) n)%nat.
  Proof.
    induction k.
    - simpl; intros ?.
      repeat rewrite Nat.add_0_r.
      rewrite nCn. nia.
    (* Inner induction on [n]: split [(n+1+k+1)!] into two parts and match them
       with the two summands of Pascal's rule, using the outer hypothesis [IHk]
       for one and the inner hypothesis [IHn] for the other. *)
    - induction n.
      + simpl. lia.
      + assert (Ht : (S n + S k = S (S n +  k))%nat).
        nia. rewrite Ht; clear Ht.
        rewrite snCsk, Nat.mul_add_distr_l.
        eapply eq_trans with
          (y := (fact (S n + k) * S k + fact (n + S k) * S n)%nat).
        assert (Ht : (fact (S (S n + k)) = (S (S n + k)) * fact (S n + k))%nat).
        simpl. lia. rewrite Ht; clear Ht.
        assert (Ht : (S (S n + k) = S n + S k)%nat) by lia.
        rewrite Ht; clear Ht.
        rewrite Nat.mul_add_distr_r.
        rewrite <-Nat.add_comm. apply f_equal2.
        lia. assert (Ht : (n + S k = S n + k)%nat) by lia.
        rewrite Ht; clear Ht. lia.
        apply f_equal2.
        assert (Ht : (fact (S k) = (S k) * fact k)%nat).
        simpl. lia. rewrite Ht; clear Ht.
        pose proof (IHk (S n)) as Hs.
        assert (Ht : (S k * fact k * fact (S n) * binomial_exp (S n + k) (S n) =
          S k * (fact k * fact (S n) * binomial_exp (S n + k) (S n)))%nat).
        lia. rewrite Ht; clear Ht.
        rewrite <-Hs. lia.
        rewrite IHn.
        assert (Ht : (fact (S n) = (S n) * fact n)%nat).
        simpl. lia. rewrite Ht; clear Ht.
        assert (Ht : (S n + k = n + S k)%nat) by lia.
        rewrite Ht; clear Ht.
        lia.
  Qed.

  (** Symmetry of binomial coefficients: [C(n+k, n) = C(n+k, k)]. *)
  Lemma n_k_interchange : forall (n k : nat),
    (binomial_exp (n + k) n = binomial_exp (n + k) k)%nat.
  Proof.
    intros ? ?.
    pose proof (connect_fact_with_binomial_exp_def n k) as H₁.
    pose proof (connect_fact_with_binomial_exp_def k n) as H₂.
    apply Nat.mul_cancel_l with (p := (fact k * fact n)%nat).
    pose proof (fact_neq_0 n) as Hn.
    pose proof (fact_neq_0 k) as Hk.
    lia. rewrite <-H₂.
    rewrite Nat.add_comm.
    assert (Ht : (fact k * fact n * binomial_exp (k + n) k =
      fact n * fact k * binomial_exp (k + n) k)%nat) by lia.
    rewrite Ht; clear Ht.
    rewrite <-H₁.
    reflexivity.
  Qed.

  (** ** List helpers

      Small list functions and lemmas used to describe polynomial expansions as
      explicit lists of terms. *)

  (** [list_upto n] is the descending list [[n; n-1; …; 1; 0]] of length [n+1]. *)
  Fixpoint list_upto (n : nat) : list nat :=
    match n with
    | O => [O]
    | S n' => n :: list_upto n'
    end.

  (** [take n l] is the prefix of [l] of length [min n (length l)]. *)
  Fixpoint take {A : Type} (n : nat) (l : list A) : list A :=
    match n with
    | O => []
    | S n' => match l with
      | [] => []
      | h :: t => h :: (take n' t)
    end
    end.

  (** [drop n l] removes the first [n] elements of [l]. *)
  Fixpoint drop {A : Type} (n : nat) (l : list A) : list A :=
    match n with
    | O => l
    | S n' => match l with
      | [] => []
      | h :: t => drop n' t
    end
    end.

  (** [zip_with f l₁ l₂] applies [f] pointwise to two lists, truncating to the
      shorter one. *)
  Fixpoint zip_with {A B C : Type} (f : A -> B -> C) (l₁ : list A)
    (l₂ : list B) : list C :=
    match l₁, l₂ with
    | h₁ :: t₁, h₂ :: t₂ =>  (f h₁ h₂) :: (zip_with f t₁ t₂)
    | _, _ => []
    end.

  (** The length of [zip_with f l l'] is the minimum of the two lengths. *)
  Lemma zip_length_min : forall {X Y Z : Type}
    (f : X -> Y -> Z) l l',
    length (zip_with f l l') = min (length l) (length l').
  Proof.
    induction l; destruct l'; simpl; eauto.
  Qed.

  (** For lists of equal length, [zip_with] preserves the length. *)
  Lemma zip_length : forall {X Y Z : Type} (f : X -> Y -> Z)
    l l', length l = length l' -> length (zip_with f l l') = length l.
  Proof.
    intros * H. now rewrite zip_length_min,
    H, Nat.min_id.
  Qed.

  (** Indexing [zip_with] with [nth]: for equal-length lists and an in-range
      index [k], the [k]-th element of [zip_with f l₁ l₂] is [f] applied to the
      [k]-th elements of [l₁] and [l₂] (default values are irrelevant). *)
  Lemma zip_list_index {A B C : Type} (f : A -> B -> C) : forall
    (l₁ : list A) (l₂ : list B) k def₁ def₂ def₃,
    List.length l₁ = List.length l₂ ->
    (k < List.length l₁)%nat ->
    List.nth k (zip_with f l₁ l₂) def₁ =
    f (List.nth k l₁ def₂) (List.nth k l₂ def₃).
  Proof.
    induction l₁.
    - simpl; intros ? ? ? ? ? Hl Hk.
      lia.
    - simpl; intros ? ? ? ? ? Hl Hk.
      destruct l₂.
      simpl in Hl.
      lia.
      simpl in Hl.
      inversion Hl as [Hlt]; clear Hl.
      destruct k.
      simpl. reflexivity.
      simpl.
      assert (Hw : (k < List.length l₁)%nat) by lia.
      clear Hk.
      apply IHl₁; assumption.
  Qed.

  (** The [nth_error] version of [zip_list_index]: if the [k]-th elements of
      [l₁] and [l₂] are [t] and [w], the [k]-th element of the zip is [f t w]. *)
  Lemma zip_list_index_some {A B C : Type} (f : A -> B -> C) : forall
    (l₁ : list A) (l₂ : list B) k t w,
    List.length l₁ = List.length l₂ ->
    (k < List.length l₁)%nat ->
    Some t = List.nth_error l₁ k ->
    Some w = List.nth_error l₂ k ->
    List.nth_error (zip_with f l₁ l₂) k = Some (f t w).
  Proof.
    induction l₁.
    - simpl; intros ? ? ? ? ? Hl Hk Hw.
      lia.
    - simpl; intros ? ? ? ? Hl Hk Hw Hv.
      destruct l₂.
      simpl in Hl.
      lia.
      simpl in Hl.
      inversion Hl as [Hlt]; clear Hl.
      destruct k.
      simpl. simpl in Hw.
      simpl in Hv.
      inversion Hw; inversion Hv; subst.
      reflexivity.
      simpl.
      assert (Hwt : (k < List.length l₁)%nat) by lia.
      clear Hk.
      apply IHl₁; assumption.
  Qed.

  (** An in-range index always yields [Some] element under [nth_error]. *)
  Lemma index_some {A : Type} : forall (l : list A) k,
    (k < List.length l)%nat ->
    exists t, Some t = List.nth_error l k.
  Proof.
    induction l.
    + destruct k; intros Hk.
      all:(simpl in Hk; lia).
    + destruct k; intros Hk.
      exists a. simpl; reflexivity.
      simpl in Hk.
      simpl. apply IHl.
      lia.
  Qed.

  (** [take n l ++ drop n l = l]. *)
  Lemma take_drop_inv {A : Type} : forall (n : nat) (l : list A),
    (take n l ++ drop n l = l).
  Proof.
    induction n.
    - simpl; intros ?; reflexivity.
    - simpl; intros ?.
      destruct l.
      + reflexivity.
      + simpl. rewrite IHn.
        reflexivity.
  Qed.

  (** [list_upto n] has length [n+1]. *)
  Lemma list_upto_length : forall n : nat,
    List.length (list_upto n) = S n.
  Proof.
    induction n.
    - simpl; reflexivity.
    - simpl; rewrite IHn;
      reflexivity.
  Qed.

  (** Every element of [list_upto n] is at most [n]. *)
  Lemma list_elem_bound : forall n x : nat,
    In x (list_upto n) -> (x <= n)%nat.
  Proof.
    induction n.
    - simpl; intros ? [H | H]; lia.
    - simpl; intros ? [H | H]. lia.
      specialize (IHn x H).
      lia.
  Qed.

  (** The [k]-th element of [list_upto n] is [n - k]. *)
  Lemma list_elem_nth : forall n k : nat,
    (k < List.length (list_upto n))%nat ->
    (List.nth_error (list_upto n) k = Some (n - k))%nat.
  Proof.
    induction n;simpl.
    + intros [|]; intro H; simpl.
      reflexivity. lia.
    + intros ? Hk.
      destruct k.
      - simpl. reflexivity.
      - simpl. apply IHn.
        lia.
  Qed.

  (** ** The binomial theorem

      The expansion of [(x+y)^n] is represented as a list of triples
      [(a, b, v)] meaning a term with [x]-exponent [a], [y]-exponent [b] and
      value [v = C(n,a) · x^a · y^b].  Multiplying the expansion by [x + y]
      corresponds to shifting the [x]-exponents (multiplication by [x]),
      shifting the [y]-exponents (multiplication by [y]), padding the two
      lists so that equal exponents are aligned, and adding them pointwise.
      The main result is [pow_add]. *)

  (** [populate_terms x y n] is the list of terms of the binomial expansion of
      [(x+y)^n], ordered by decreasing [x]-exponent: the entry for [k] is
      [(k, n-k, C(n,k) · x^k · y^(n-k))]. *)
  Definition populate_terms (x y n : nat) : list (nat * nat * nat) :=
    List.map (fun k => (k, n - k, binomial_exp n k * Nat.pow x k *
      Nat.pow y (n - k)))%nat (list_upto n).

  (** The expansion of [(x+y)^n] has [n+1] terms. *)
  Lemma populate_terms_length : forall n x y : nat,
    List.length (populate_terms x y n) = S n.
  Proof.
    intros ? ? ?.
    unfold populate_terms.
    rewrite List.length_map.
    apply list_upto_length.
  Qed.

  (** Every term [(a, b, v)] of [populate_terms x y n] satisfies [a + b = n]
      (so both are at most [n]) and [v = C(n,a) · x^a · y^b]. *)
  Lemma populate_terms_values : forall n x y a b v : nat,
      In (a, b, v) (populate_terms x y n) ->
      (a <= n /\ b <= n /\ a + b = n /\
      v = binomial_exp n a * Nat.pow x a *
      Nat.pow y b)%nat.
  Proof.
    intros ? ? ? ? ? ? Hin.
    unfold populate_terms in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (xt & H₁ & H₂).
    inversion H₁; subst.
    apply list_elem_bound in H₂.
    split. exact H₂.
    split. lia.
    split. lia.
    lia.
  Qed.

  (** The [k]-th term of [populate_terms x y n] is
      [(n-k, k, C(n, n-k) · x^(n-k) · y^k)]. *)
  Lemma populate_term_nth : forall n k x y,
    (k < List.length (populate_terms x y n))%nat ->
    List.nth_error (populate_terms x y n) k =
    Some (n - k, k, binomial_exp n (n - k) * Nat.pow x (n - k) *
    Nat.pow y k)%nat.
  Proof.
    intros * Hk.
    unfold populate_terms.
    rewrite nth_error_map.
    rewrite list_elem_nth.
    simpl. f_equal.
    f_equal. f_equal.
    rewrite populate_terms_length in Hk.
    lia.
    rewrite populate_terms_length in Hk.
    f_equal.
    assert (Ht : (n - (n - k) = k)%nat).
    lia. rewrite Ht. reflexivity.
    rewrite populate_terms_length in Hk.
    rewrite list_upto_length.
    lia.
  Qed.

  (** [mul_x_populate_terms x y n] multiplies every term of the expansion of
      [(x+y)^n] by [x]: the [x]-exponent increases by one and the value is
      multiplied by [x]. *)
  Definition mul_x_populate_terms (x y n : nat) :=
    List.map (fun '(a, b, v) => (S a, b, x * v)%nat)
      (populate_terms x y n).

  (** Multiplying by [x] keeps [n+1] terms. *)
  Lemma mul_x_populate_terms_length : forall n x y : nat,
    List.length (mul_x_populate_terms x y n) = S n.
  Proof.
    intros *.
    unfold mul_x_populate_terms.
    rewrite List.length_map,
    populate_terms_length.
    reflexivity.
  Qed.

  (** Shape of a term [(a+1, b, v)] after multiplication by [x]:
      [a + b = n] and [v = C(n,a) · x^(a+1) · y^b]. *)
  Lemma mul_x_populate_terms_values : forall n x y a b v : nat,
    In (S a, b, v) (mul_x_populate_terms x y n) ->
    (a <= n /\ b <= n /\ a + b = n /\
    v = binomial_exp n a * Nat.pow x (S a) *
    Nat.pow y b)%nat.
  Proof.
    intros ? ? ? ? ? ? Hin.
    unfold mul_x_populate_terms in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (xt & H₁ & H₂).
    repeat destruct xt.
    destruct p.
    inversion H₁; subst.
    apply populate_terms_values in H₂.
    split. lia.
    split. lia.
    split. lia.
    destruct H₂ as (H₂ & H₃ & H₄ & H₅).
    simpl. lia.
  Qed.

  (** The [k]-th term after multiplication by [x] is
      [(n-k+1, k, x · C(n, n-k) · x^(n-k) · y^k)]. *)
  Lemma mul_x_populate_terms_nth : forall n k x y,
    (k < List.length (mul_x_populate_terms x y n))%nat ->
    List.nth_error (mul_x_populate_terms x y n) k =
    Some (S (n - k), k, x * binomial_exp n (n - k) * Nat.pow x (n - k) *
    Nat.pow y k)%nat.
  Proof.
    intros * Hk.
    unfold mul_x_populate_terms.
    rewrite nth_error_map.
    assert (Ht : (k < List.length (populate_terms x y n))%nat).
    rewrite mul_x_populate_terms_length in Hk.
    rewrite populate_terms_length.
    exact Hk.
    pose proof (populate_term_nth _ _ _ _ Ht) as Hp.
    rewrite Hp. simpl. f_equal.
    f_equal. lia.
  Qed.

  (** [mul_y_populate_terms x y n] multiplies every term of the expansion of
      [(x+y)^n] by [y], incrementing the [y]-exponent. *)
  Definition mul_y_populate_terms (x y n : nat) :=
    List.map (fun '(a, b, v) => (a, S b, y * v)%nat)
      (populate_terms x y n).

  (** Multiplying by [y] keeps [n+1] terms. *)
  Lemma mul_y_populate_terms_length : forall n x y : nat,
    List.length (mul_y_populate_terms x y n) = S n.
  Proof.
    intros *.
    unfold mul_y_populate_terms.
    rewrite List.length_map,
    populate_terms_length.
    reflexivity.
  Qed.

  (** Shape of a term [(a, b+1, v)] after multiplication by [y]:
      [a + b = n] and [v = C(n,a) · x^a · y^(b+1)]. *)
  Lemma mul_y_populate_terms_values : forall n x y a b v : nat,
    In (a, S b, v) (mul_y_populate_terms x y n) ->
    (a <= n /\ b <= n /\ a + b = n /\
    v = binomial_exp n a * Nat.pow x a *
    Nat.pow y (S b))%nat.
  Proof.
    intros ? ? ? ? ? ? Hin.
    unfold mul_y_populate_terms in Hin.
    apply in_map_iff in Hin.
    destruct Hin as (xt & H₁ & H₂).
    repeat destruct xt.
    destruct p.
    inversion H₁; subst.
    apply populate_terms_values in H₂.
    split. lia.
    split. lia.
    split. lia.
    destruct H₂ as (H₂ & H₃ & H₄ & H₅).
    simpl. lia.
  Qed.

  (** The [k]-th term after multiplication by [y] is
      [(n-k, k+1, y · C(n, n-k) · x^(n-k) · y^k)]. *)
  Lemma mul_y_populate_terms_nth : forall n k x y,
    (k < List.length (mul_y_populate_terms x y n))%nat ->
    List.nth_error (mul_y_populate_terms x y n) k =
    Some ((n - k), S k, y * binomial_exp n (n - k) * Nat.pow x (n - k) *
    Nat.pow y k)%nat.
  Proof.
    intros * Hk.
    unfold mul_y_populate_terms.
    rewrite nth_error_map.
    assert (Ht : (k < List.length (populate_terms x y n))%nat).
    rewrite mul_y_populate_terms_length in Hk.
    rewrite populate_terms_length.
    exact Hk.
    pose proof (populate_term_nth _ _ _ _ Ht) as Hp.
    rewrite Hp. simpl. f_equal.
    f_equal. lia.
  Qed.

  (** [append_mul_x_populate_terms x y n] is the [x]-shifted expansion padded at
      the end with the zero term [(0, n+1, 0)], so that it has [n+2] entries
      aligned by exponent with [append_mul_y_populate_terms]. *)
  Definition append_mul_x_populate_terms (x y n : nat) :=
    mul_x_populate_terms x y n ++ [(O, S n, O)].

  (** The padded [x]-shifted list has [n+2] entries. *)
  Lemma append_mul_x_populate_terms_length : forall n x y,
    List.length (append_mul_x_populate_terms x y n) =
    S (S n).
  Proof.
    intros *.
    unfold append_mul_x_populate_terms.
    rewrite List.length_app,
    mul_x_populate_terms_length.
    simpl. lia.
  Qed.

  (** Indexing the padded [x]-shifted list: entries [k ≤ n] come from
      [mul_x_populate_terms_nth] and entry [n+1] is the padding term
      [(0, n+1, 0)]. *)
  Lemma append_mul_x_populate_terms_nth : forall n k x y,
    (k < List.length (append_mul_x_populate_terms x y n))%nat ->
    List.nth_error (append_mul_x_populate_terms x y n) k =
    (if k <? S n then
      Some (S (n - k), k, x * binomial_exp n (n - k) * Nat.pow x (n - k) *
      Nat.pow y k)
    else Some (O, S n, O))%nat.
  Proof.
    intros * Hk.
    pose proof (append_mul_x_populate_terms_length n x y) as Hv.
    unfold append_mul_x_populate_terms.
    pose proof (mul_x_populate_terms_length n x y) as Hp.
    assert (Ht : ((k < S n) \/ (k = S n))%nat) by lia.
    destruct Ht as [Ht | Ht].
    assert (Hw : ((k <? S n) = true)%nat).
    apply Nat.ltb_lt. exact Ht.
    rewrite Hw.
    rewrite nth_error_app1.
    rewrite mul_x_populate_terms_nth.
    f_equal. lia.
    lia.
    assert (Hw : ((k <? S n) = false)%nat). rewrite Ht.
    apply Nat.ltb_ge. lia.
    rewrite Hw.
    pose proof (@nth_error_app2 _ (mul_x_populate_terms x y n)
    [(0%nat, S n, 0%nat)] k) as Hpp.
    assert (Hvw : (length (mul_x_populate_terms x y n) <= k)%nat).
    lia.
    specialize (Hpp Hvw).
    rewrite Hpp.
    rewrite Ht.
    rewrite Hp.
    simpl.
    assert (Hnn : (n - n = 0)%nat) by lia.
    rewrite Hnn.
    simpl. reflexivity.
  Qed.

  (** [append_mul_y_populate_terms x y n] is the [y]-shifted expansion padded at
      the front with the zero term [(n+1, 0, 0)], aligning it with the
      [x]-shifted list. *)
  Definition append_mul_y_populate_terms (x y n : nat) :=
    (S n, O, O) :: mul_y_populate_terms x y n.

  (** The padded [y]-shifted list has [n+2] entries. *)
  Lemma append_mul_y_populate_terms_length : forall n x y,
    List.length (append_mul_y_populate_terms x y n) =
    S (S n).
  Proof.
    intros *.
    unfold append_mul_y_populate_terms.
    simpl;
    rewrite mul_y_populate_terms_length;
    lia.
  Qed.

  (** Indexing the padded [y]-shifted list: entry [0] is the padding term
      [(n+1, 0, 0)] and entry [k ≥ 1] is the [(k-1)]-th [y]-shifted term. *)
  Lemma append_mul_y_populate_terms_nth : forall n k x y,
    (k < List.length (append_mul_y_populate_terms x y n))%nat ->
    List.nth_error (append_mul_y_populate_terms x y n) k =
    (if k =? O then Some (S n, O, O)
    else Some ((n - (k - 1)), S (k - 1), y * binomial_exp n (n - (k - 1)) *
      Nat.pow x (n - (k - 1)) * Nat.pow y (k - 1)))%nat.
  Proof.
    intros * Hk.
    unfold append_mul_y_populate_terms.
    assert (Ht : ((k = 0) \/ (0 < k))%nat). lia.
    destruct Ht as [Ht | Ht].
    rewrite Ht. simpl.
    reflexivity.
    assert (Hw : (k =? 0 = false)%nat).
    apply Nat.eqb_neq. lia.
    rewrite Hw.
    pose proof (@nth_error_app2 _ [(S n, 0, 0)]
      (mul_y_populate_terms x y n) k) as Hp.
    simpl in Hp.
    assert (Htt : (1 <= k)%nat). lia.
    specialize (Hp Htt).
    rewrite Hp.
    simpl.
    rewrite mul_y_populate_terms_nth.
    f_equal.
    pose proof (append_mul_y_populate_terms_length n x y) as Hwtt.
    unfold append_mul_y_populate_terms in Hwtt.
    simpl in Hwtt.
    rewrite mul_y_populate_terms_length.
    rewrite append_mul_y_populate_terms_length in Hk.
    lia.
  Qed.

  (** [add_polynomials x y n] adds the two aligned lists pointwise, keeping the
      exponents of the first and summing the values.  Mathematically this is
      [x · (x+y)^n + y · (x+y)^n] written term by term. *)
  Definition add_polynomials (x y n : nat) :=
    zip_with
    (fun '(x, y, a) '(_, _, b) => (x, y, a + b)%nat)
    (append_mul_x_populate_terms x y n)
    (append_mul_y_populate_terms x y n).

  (** The sum of the aligned lists has [n+2] entries. *)
  Lemma add_polynomials_length : forall x y n,
    List.length (add_polynomials x y n) = S (S n).
  Proof.
    intros *.
    unfold add_polynomials.
    rewrite zip_length.
    rewrite append_mul_x_populate_terms_length.
    reflexivity.
    rewrite append_mul_x_populate_terms_length.
    rewrite append_mul_y_populate_terms_length.
    reflexivity.
  Qed.

  (** Pointwise description of [add_polynomials]: if the [k]-th entries of the
      two aligned lists are [(a, b, c)] and [(u, v, w)] and the [k]-th entry of
      the sum is [(l, m, t)], then the exponents agree ([a = l = u],
      [b = m = v]) and [t = c + w].  The proof distinguishes [k = 0],
      [k = n+1] and [0 < k < n+1]. *)
  Lemma add_polynomials_nth : forall n x y k  a b c u v w l m t : nat,
    (k < S (S n))%nat ->
    Some (a, b, c) = List.nth_error (append_mul_x_populate_terms x y n) k ->
    Some (u, v, w) = List.nth_error (append_mul_y_populate_terms x y n) k ->
    Some (l, m, t) = List.nth_error (add_polynomials x y n) k ->
    (a = l /\ b = m /\ t = c + w /\ l = u /\ m = v)%nat.
  Proof.
    intros * Hk Ha Hb Hc.
    rewrite append_mul_x_populate_terms_nth in Ha.
    rewrite append_mul_y_populate_terms_nth in Hb.
    unfold add_polynomials in Hc.
    pose proof (append_mul_x_populate_terms_length n x y) as Hx.
    pose proof (append_mul_y_populate_terms_length n x y) as Hy.
    assert (Hxx : (k < length (append_mul_x_populate_terms x y n))%nat).
    lia.
    assert(Hyy: (k < length (append_mul_y_populate_terms x y n))%nat).
    lia.
    destruct (index_some (append_mul_x_populate_terms x y n) k Hxx) as [t₁ Ht₁].
    destruct (index_some (append_mul_y_populate_terms x y n) k Hyy) as [t₂ Ht₂].
    erewrite zip_list_index_some with (t := t₁) (w := t₂) in Hc.
    destruct t₁. destruct p.
    destruct t₂. destruct p.
    inversion Hc; subst; clear Hc.
    rewrite append_mul_x_populate_terms_nth in Ht₁.
    rewrite append_mul_y_populate_terms_nth in Ht₂.
    assert (Ht : ((k = O) \/ (k = (S n)) \/ (S O <= k < S n))%nat).
    lia.
    (* Three cases: [k = 0] (front padding of the [y]-list), [k = n+1] (end
       padding of the [x]-list) and an interior index. *)
    destruct Ht as [Ht | [Ht | Ht]].
    rewrite Ht in Hb, Ht₂.
    simpl in *.
    assert (Hkt : (k <? S n = true)%nat).
    rewrite Ht. compute. reflexivity.
    rewrite Hkt in Ha, Ht₁.
    inversion Ha; subst; clear Ha.
    inversion Hb; subst; clear Hb.
    inversion Ht₁; subst; clear Ht₁.
    inversion Ht₂; subst; clear Ht₂.
    simpl. lia.
    assert (Hkt: (k =? 0 = false)%nat).
    rewrite Ht. compute. reflexivity.
    rewrite Hkt in Hb, Ht₂.
    clear Hkt.
    assert (Hkt: (k <? S n = false)%nat).
    rewrite Ht. apply Nat.ltb_irrefl.
    rewrite Hkt in Ha, Ht₁.
    clear Hkt.
    inversion Ha; subst; clear Ha.
    inversion Hb; subst; clear Hb.
    inversion Ht₁; subst; clear Ht₁.
    inversion Ht₂; subst; clear Ht₂.
    simpl.
    repeat split; try lia.
    assert (Hn : (n - 0 = n)%nat).
    lia. clear Hn.
    destruct Ht as [Htl Htr].
    assert (Hkt : (k <? S n = true)%nat).
    apply Nat.ltb_lt. exact Htr.
    rewrite Hkt in Ha, Ht₁.
    clear Hkt.
    assert (Hkt: (k =? 0 = false)%nat).
    apply Nat.eqb_neq. lia.
    rewrite Hkt in Hb, Ht₂.
    clear Hkt.
    inversion Ha; subst; clear Ha.
    inversion Hb; subst; clear Hb.
    inversion Ht₁; subst; clear Ht₁.
    inversion Ht₂; subst; clear Ht₂.
    lia.
    all:(try assumption; try reflexivity).
    rewrite Hx, Hy. reflexivity.
    rewrite append_mul_y_populate_terms_length.
    lia.
    rewrite append_mul_x_populate_terms_length.
    lia.
  Qed.

  (** [nth]-with-default version of the pointwise definition of
      [add_polynomials]. *)
  Lemma add_polynomials_membership : forall n x y k : nat,
    (k < S (S n))%nat ->
    List.nth k (add_polynomials x y n) (O, O, O) =
    (fun '(x, y, a) '(_, _, b) => (x, y, a + b)%nat)
    (List.nth k (append_mul_x_populate_terms x y n) (O, O, O))
    (List.nth k (append_mul_y_populate_terms x y n) (O, O, O)).
  Proof.
    intros ? ? ? ? Hk.
    unfold add_polynomials.
    erewrite zip_list_index.
    reflexivity.
    unfold append_mul_x_populate_terms,
    append_mul_y_populate_terms,
    mul_x_populate_terms,
    mul_y_populate_terms.
    simpl. rewrite List.length_map,
    List.last_length. simpl.
    rewrite List.length_map.
    apply f_equal.
    reflexivity.
    rewrite append_mul_x_populate_terms_length.
    exact Hk.
  Qed.

  (** Pascal's rule on the term lists: the [k]-th entries of the two aligned
      shifted expansions of [(x+y)^n] have the same exponents as the [k]-th
      term of the expansion of [(x+y)^(n+1)], and the latter's value is the sum
      of their values. *)
  Lemma populate_terms_membership : forall n k x y a b c u v w l m t : nat,
    (k < S (S n))%nat ->
    Some (a, b, c) = List.nth_error (append_mul_x_populate_terms x y n) k ->
    Some (u, v, w) = List.nth_error (append_mul_y_populate_terms x y n) k ->
    Some (l, m, t) = List.nth_error (populate_terms x y (S n)) k ->
    (a = l /\ b = m /\ t = c + w /\ l = u /\ m = v)%nat.
  Proof.
    intros * H₁ H₂ H₃ H₄.
    unfold append_mul_x_populate_terms in H₂.
    unfold append_mul_y_populate_terms in H₃.
    assert (Ht : ((k = O) \/ (k = (S n)) \/ (S O <= k < S n))%nat).
    lia.
    (* Case [k = 0]: the leading term [x^(n+1)], with [C(n+1, n+1) = C(n, n) = 1]
       and the padding contributing [0]. *)
    destruct Ht as [Ht | [Ht | Ht]].
    rewrite Ht in H₂, H₃, H₄.
    simpl in H₃.
    rewrite populate_term_nth in H₄.
    rewrite nth_error_app1 in H₂.
    rewrite mul_x_populate_terms_nth in H₂.
    inversion H₂; inversion H₃;
    inversion H₄; subst; clear H₂; clear H₃;
    clear H₄. split.
    lia. split. lia.
    split. rewrite nCn.
    assert (Hn : (n - 0 = n)%nat).
    lia. rewrite Hn. clear Hn.
    rewrite nCn.
    rewrite k_gt_n. simpl.
    lia. lia. lia.
    rewrite mul_x_populate_terms_length.
    lia.
    rewrite mul_x_populate_terms_length.
    lia.
    rewrite populate_terms_length. lia.
    rewrite populate_term_nth in H₄.
    (* Case [k = n+1]: the trailing term [y^(n+1)], coming only from the
       [y]-shifted list. *)
    pose proof (@nth_error_app2 _ (mul_x_populate_terms x y n)
    [(0%nat, S n, 0%nat)] k) as Hpp.
    assert (Hvw : (length (mul_x_populate_terms x y n) <= k)%nat).
    rewrite mul_x_populate_terms_length.
    lia.
    specialize (Hpp Hvw).
    rewrite Hpp in H₂.
    rewrite mul_x_populate_terms_length, Ht in H₂.
    rewrite Nat.sub_diag in H₂.
    simpl in H₂.
    rewrite Ht in H₃.
    pose proof (@nth_error_app2 _ [(S n, 0, 0)]
      (mul_y_populate_terms x y n) k) as Hp.
    simpl in Hp.
    assert (Htt : (1 <= k)%nat). lia.
    specialize (Hp Htt).
    rewrite Ht in Hp.
    rewrite Hp in H₃.
    simpl in H₃.
    rewrite Nat.sub_0_r in H₃.
    clear Hpp; clear Hvw; clear Hp.
    rewrite mul_y_populate_terms_nth in H₃.
    simpl in H₃.
    rewrite Nat.sub_diag in H₃.
    rewrite Ht in H₄.
    rewrite Nat.sub_diag in H₄.
    inversion H₂; inversion H₃;
    inversion H₄; subst; clear H₂; clear H₃;
    clear H₄.
    simpl. rewrite nCo.
    lia.
    rewrite mul_y_populate_terms_length.
    lia.
    rewrite populate_terms_length.
    lia.
    (* Interior case: both lists contribute, and the values add up by Pascal's
       rule [C(n+1, n+1-k) = C(n, n-k) + C(n, n+1-k)]. *)
    destruct Ht as [Htl Htr].
    pose proof (@nth_error_app2 _ [(S n, 0, 0)]
      (mul_y_populate_terms x y n) k Htl) as Hp.
    simpl in Hp.
    rewrite Hp in H₃.
    clear Hp.
    rewrite nth_error_app1 in H₂.
    rewrite mul_x_populate_terms_nth in H₂.
    rewrite mul_y_populate_terms_nth in H₃.
    rewrite populate_term_nth in H₄.
    inversion H₂; inversion H₃;
    inversion H₄; subst; clear H₂; clear H₃;
    clear H₄. split.
    destruct k. lia.
    lia.
    split. lia.
    destruct k. lia.
    split.
    (* Rewrite [n - k] as a successor to apply Pascal's rule ([snCsk]) and
       merge the powers of [x]. *)
    destruct (n - k) eqn:Hk.
    lia.
    simpl.
    assert (Hsn : n - S k = n0).
    lia. rewrite Hsn.
    rewrite Nat.sub_0_r.
    rewrite Hk.
    rewrite <-Hk.
    rewrite <-Hsn.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.add_comm.
    f_equal. lia.
    assert (Hx : (x * x ^ (n - S k)) =
    (x ^ (n - k))).
    rewrite <-Nat.pow_succ_r.
    assert (Hss : S (n - S k) = n - k).
    lia. rewrite Hss.
    reflexivity. lia.
    rewrite Hx. lia.
    lia.
    rewrite populate_terms_length.
    lia.
    rewrite mul_y_populate_terms_length.
    lia.
    rewrite mul_x_populate_terms_length.
    lia.
    rewrite mul_x_populate_terms_length.
    lia.
  Qed.

  (** Simplified form of [populate_terms_membership]: the [k]-th term of the
      expansion of [(x+y)^(n+1)] is [(a, b, c + w)]. *)
  Lemma populate_terms_membership_simp : forall n k x y a b c u v w : nat,
    (k < S (S n))%nat ->
    Some (a, b, c) = List.nth_error (append_mul_x_populate_terms x y n) k ->
    Some (u, v, w) = List.nth_error (append_mul_y_populate_terms x y n) k ->
    Some (a, b, c + w) = List.nth_error (populate_terms x y (S n)) k.
  Proof.
    intros * H₁ H₂ H₃.
    assert (Ht : k < List.length (populate_terms x y (S n))).
    rewrite populate_terms_length. lia.
    pose proof (populate_term_nth _ k x y Ht) as Hw.
    symmetry in Hw.
    destruct (populate_terms_membership n k x y a b c u v w _ _ _
      H₁ H₂ H₃ Hw) as (Ha & Hb & Hc & Hd & He).
    rewrite <-Hw.
    f_equal. f_equal. f_equal.
    exact Ha.
    exact Hb.
    symmetry.
    exact Hc.
  Qed.

  (** At every index [k < n+2], [add_polynomials x y n] and
      [populate_terms x y (n+1)] have the same entry. *)
  Lemma add_poly_def_correct_pointwise : forall n x y k,
    k < S (S n) ->
    List.nth_error (add_polynomials x y n) k =
    List.nth_error (populate_terms x y (S n)) k.
  Proof.
    intros * Hk.
    unfold add_polynomials.
    pose proof (append_mul_x_populate_terms_length n x y) as Hx.
    pose proof (append_mul_y_populate_terms_length n x y) as Hy.
    assert (Hxx : (k < length (append_mul_x_populate_terms x y n))%nat).
    lia.
    assert(Hyy: (k < length (append_mul_y_populate_terms x y n))%nat).
    lia.
    destruct (index_some (append_mul_x_populate_terms x y n) k Hxx) as [t₁ Ht₁].
    destruct (index_some (append_mul_y_populate_terms x y n) k Hyy) as [t₂ Ht₂].
    erewrite zip_list_index_some with (t := t₁) (w := t₂).
    destruct t₁. destruct p.
    destruct t₂. destruct p.
    apply populate_terms_membership_simp with (u := n4) (v := n5).
    lia. exact Ht₁.
    exact Ht₂.
    rewrite append_mul_x_populate_terms_length.
    rewrite append_mul_y_populate_terms_length.
    reflexivity.
    rewrite append_mul_x_populate_terms_length.
    lia. exact Ht₁. exact Ht₂.
  Qed.

  (** Extensionality for lists via [nth_error]: two lists of equal length that
      agree at every in-range index are equal. *)
  Lemma nth_ext_error {A : Type} : forall (l l' : list A),
    length l = length l' ->
    (forall n, n < length l -> nth_error l n = nth_error l' n) -> l = l'.
  Proof.
    induction l.
    + destruct l'.
      simpl; intros Hl Hn.
      reflexivity.
      simpl; intros Hl Hn.
      lia.
    + destruct l'.
      simpl; intros Hl Hn.
      lia.
      simpl; intros Hl Hn.
      assert (Ht : 0 < S (length l)).
      lia.
      pose proof (Hn 0 Ht) as Hp.
      simpl in Hp.
      f_equal. inversion Hp.
      reflexivity.
      apply IHl.
      lia.
      intros ? Hnn.
      assert (Hv : S n < S (length l)).
      lia.
      pose proof (Hn _  Hv).
      simpl in H.
      exact H.
  Qed.

  (** The inductive step of the binomial theorem at the level of term lists:
      [add_polynomials x y n = populate_terms x y (n+1)]. *)
  Lemma add_poly_def_correct : forall n x y,
    add_polynomials x y n = populate_terms x y (S n).
  Proof.
    intros *.
    pose proof (@nth_ext_error (nat * nat * nat)
      (add_polynomials x y n) (populate_terms x y (S n))).
    assert (Ht : length (add_polynomials x y n) = S (S n)).
    rewrite add_polynomials_length.
    reflexivity.
    assert (Hw : length (populate_terms x y (S n)) = S (S n)).
    rewrite populate_terms_length.
    reflexivity.
    rewrite Ht, Hw in H.
    exact (H eq_refl (add_poly_def_correct_pointwise n x y)).
  Qed.

  (** [sum_xy x y n] is the sum of the values in [populate_terms x y n], that is
      [Σ_{k=0}^{n} C(n,k) · x^k · y^(n-k)]. *)
  Definition sum_xy (x y : nat) (n : nat) : nat :=
    List.fold_right (fun x acc => acc + x)%nat 0%nat
    (List.map (fun '(_, _, x) => x ) (populate_terms x y n)).

  (** A scalar factor [a] can be pushed inside a [fold_right] sum of binomial
      terms. *)
  Lemma fold_right_eq : forall l n a x y,
    a * fold_right (fun x0 acc : nat => acc + x0) 0
      (map (fun k : nat => binomial_exp n k * x ^ k * y ^ (n - k)) l) =
    fold_right (fun x0 acc : nat => acc + x0) 0
      (map (fun k : nat => a * binomial_exp n k * x ^ k * y ^ (n - k)) l).
  Proof.
    induction l.
    + intros *; simpl; lia.
    + intros *; simpl.
      specialize (IHl n a0 x y).
      rewrite Nat.mul_add_distr_l.
      rewrite IHl.
      lia.
  Qed.

  (** Two [fold_right] sums over the same index list add pointwise. *)
  Lemma fold_right_add : forall l n x y,
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun k : nat => x * binomial_exp n k * x ^ k * y ^ (n - k)) l)
    +
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun k : nat => y * binomial_exp n k * x ^ k * y ^ (n - k)) l)
    =
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun k : nat =>
      x * binomial_exp n k * x ^ k * y ^ (n - k) +
      y * binomial_exp n k * x ^ k * y ^ (n - k)) l).
  Proof.
    induction l.
    + intros *; simpl; reflexivity.
    + intros *; simpl.
      rewrite <-IHl.
      lia.
  Qed.

  (** Projecting the values out of the zipped term lists equals zipping the
      value lists with addition (a pure rearrangement used by
      [fold_right_gen]). *)
  Lemma push_fn_inside : forall l n x y att bt ct ut vt wt,
    map (fun '(y0, x0) => let '(_, _) := y0 in x0)
    (zip_with
      (fun '(y0, a) =>
        let
        '(x0, y1) := y0 in
        fun '(y2, b) => let '(_, _) := y2 in (x0, y1, a + b))
      (map
          (fun x0 : nat =>
          (S x0, n - x0, x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))))
          l ++ [(att, bt, ct)])
      ((ut, vt, wt)
        :: map
            (fun x0 : nat =>
              (x0, S (n - x0),
              y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0)))) l))
    =
    zip_with (fun a b : nat => a + b)
    (map (fun x0 : nat => x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0)))
      l ++ [ct])
    (wt ::
    map (fun x0 : nat => y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l).
  Proof.
    induction l.
    + intros *; simpl; reflexivity.
    + intros *; simpl.
      f_equal.
      rewrite IHl.
      reflexivity.
  Qed.

  (** Peeling off the padding entries [u] and [v] from the sum of a zipped,
      padded pair of lists. *)
  Lemma fold_right_simp : forall l n x y u v,
    fold_right (fun x0 acc : nat => acc + x0) 0
    (zip_with (fun a b : nat => a + b)
      (map (fun x0 : nat => x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l ++
        [u])
      (v :: map (fun x0 : nat => y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0)))
        l))
    =
    u + v +
    fold_right (fun x0 acc : nat => acc + x0) 0
    (zip_with (fun a b : nat => a + b)
     (map (fun x0 : nat => x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l)
     (map (fun x0 : nat => y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))) l)).
  Proof.
    induction l.
    + intros *; simpl. lia.
    + intros *; simpl.
      rewrite IHl.
      lia.
  Qed.

  (** The pointwise-added sums of [x · term] and [y · term] equal the sum of
      the values of the explicit [add_polynomials] list (with its two padding
      terms of value [0]). *)
  Lemma fold_right_gen : forall l n x y,
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map
      (fun k : nat =>
        x * binomial_exp n k * x ^ k * y ^ (n - k) +
        y * binomial_exp n k * x ^ k * y ^ (n - k)) l)
    =
    fold_right (fun x0 acc : nat => acc + x0) 0
    (map (fun '(y0, x0) => let '(_, _) := y0 in x0)
      (zip_with
          (fun '(y0, a) =>
          let
          '(x0, y1) := y0 in
            fun '(y2, b) => let '(_, _) := y2 in (x0, y1, a + b))
          (map
            (fun x0 : nat =>
              (S x0, n - x0, x * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))))
            l ++ [(0, S n, 0)])
          ((S n, 0, 0)
          :: map
                (fun x0 : nat =>
                (x0, S (n - x0),
                y * (binomial_exp n x0 * x ^ x0 * y ^ (n - x0))))
                l))).
  Proof.
    intros *.
    rewrite push_fn_inside.
    rewrite fold_right_simp.
    simpl.
    revert l n x y.
    induction l.
    + intros *; simpl; reflexivity.
    + intros *; simpl.
      rewrite IHl. lia.
  Qed.

  (** The binomial theorem on [nat]: [(x+y)^n = Σ_{k=0}^{n} C(n,k) x^k y^(n-k)]
      ([sum_xy x y n]).  Induction on [n]: [(x+y)^(n+1) = x·(x+y)^n + y·(x+y)^n],
      then the induction hypothesis and [add_poly_def_correct] rewrite the
      right-hand side into the term list for [n+1]. *)
  Lemma pow_add : forall (n x y : nat),
    (Nat.pow (x + y) n = sum_xy x y n)%nat.
  Proof.
    induction n.
    + unfold sum_xy; intros *; simpl;
      reflexivity.
    + simpl; intros *.
      unfold sum_xy.
      rewrite <-add_poly_def_correct.
      unfold add_polynomials,
      append_mul_x_populate_terms,
      append_mul_y_populate_terms,
      mul_x_populate_terms,
      mul_y_populate_terms,
      populate_terms.
      repeat rewrite map_map.
      unfold sum_xy, populate_terms in IHn.
      assert (Hxy: (x + y) * (x + y) ^ n =
        x * (x + y) ^ n + y * (x + y) ^ n).
      lia. rewrite Hxy; clear Hxy.
      rewrite IHn.
      rewrite map_map.
      repeat rewrite fold_right_eq.
      rewrite fold_right_add.
      rewrite fold_right_gen.
      reflexivity.
  Qed.

  (** ** Divisibility by a prime

      Elementary divisibility facts on [nat] for a prime [p] (primality is the
      standard library's [Znumtheory.prime] on [Z.of_nat p]). *)

  (** [p ∣ n ↔ n mod p = 0]. *)
  Lemma connection_between_divide_and_mod : forall n p : nat,
    prime (Z.of_nat p) ->
    Nat.divide p n <-> Nat.modulo n p = 0.
  Proof.
    intros * Hp; split; intro H.
    unfold Nat.divide in H.
    destruct H as [z Hz].
    rewrite Hz.
    rewrite Nat.Div0.mod_mul.
    reflexivity.
    apply prime_ge_2 in Hp.
    apply Nat.Div0.mod_divides in H.
    destruct H as [c Hn].
    econstructor.
    instantiate (1 := c).
    lia.
  Qed.

  (** [p ∤ n ↔ n mod p ≠ 0]. *)
  Lemma connection_between_not_divide_and_mod : forall n p : nat,
    prime (Z.of_nat p) ->
    ~Nat.divide p n <-> Nat.modulo n p <> 0.
  Proof.
    intros n p Hp; split; intros Hnd.
    intro H. apply Hnd.
    apply connection_between_divide_and_mod.
    exact Hp.
    exact H.
    intros H.
    apply Hnd.
    apply connection_between_divide_and_mod.
    exact Hp.
    exact H.
  Qed.

  (** Euclid's lemma on [nat]: if a prime [p] divides [a · b] then [p ∣ a] or
      [p ∣ b] (transported from [prime_mult] over [Z]). *)
  Lemma prime_div_mul : forall p a b : nat,
    prime (Z.of_nat p) -> Nat.divide p (a * b) ->
    Nat.divide p a \/ Nat.divide p b.
  Proof.
    intros * Hp Hpab.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hpf.
    apply connection_between_divide_and_mod in Hpab.
    pose proof prime_mult (Z.of_nat p) Hp
    (Z.of_nat a) (Z.of_nat b).
    assert (Hz : (Z.divide (Z.of_nat p) (Z.of_nat a * Z.of_nat b)%Z)).
    apply Z.mod_divide. lia.
    rewrite <-Nat2Z.inj_mul,
    <-Nat2Z.inj_mod.
    lia.
    destruct (H Hz) as [Hl | Hl].
    left.
    apply Z.mod_divide in Hl.
    rewrite <-Nat2Z.inj_mod in Hl.
    apply connection_between_divide_and_mod.
    exact Hp. lia.
    lia.
    apply Z.mod_divide in Hl.
    rewrite <-Nat2Z.inj_mod in Hl.
    right.
    apply connection_between_divide_and_mod.
    exact Hp. lia.
    lia.
    exact Hp.
  Qed.

  (** A divisor of a nonzero natural is at most that natural. *)
  Theorem divide_is_le : forall a b : nat, b <> 0 -> Nat.divide a b -> a <= b.
  Proof.
    intros * Hb Hn.
    unfold Nat.divide in Hn.
    destruct Hn as [z Hn].
    rewrite Hn.
    assert (Hza : z * a <> 0).
    lia.
    destruct z; lia.
  Qed.

  (** For [1 ≤ k < p], [p ∤ k!]: no factor of [k!] is divisible by [p]. *)
  Lemma fact_k_nt_zero : forall k p : nat,
    prime (Z.of_nat p) -> 1 <= k < p -> Nat.modulo (fact k) p <> 0.
  Proof.
    induction k; simpl.
    - intros * Hp Hk; lia.
    - intros * Hp Hk.
      destruct k.
      + simpl.
        rewrite Nat.mod_1_l.
        lia. lia.
      + remember (S k) as t.
        assert (Ht : 1 <= t < p).
        lia.
        pose proof (IHk p Hp Ht) as Hs.
        intro H.
        assert (Hf : fact t + t * fact t = (1 + t) * fact t).
        lia. rewrite Hf in H; clear Hf.
        apply connection_between_divide_and_mod in H.
        apply prime_div_mul in H.
        destruct H as [H | H].
        apply divide_is_le in H.
        lia. lia.
        apply connection_between_divide_and_mod in H.
        lia.
        all:exact Hp.
  Qed.

  (** For [1 ≤ k < p], [p ∤ (p-k)!]. *)
  Lemma fact_pk_nt_zero : forall k p : nat,
    prime (Z.of_nat p) -> 1 <= k < p -> Nat.modulo (fact (p - k)) p <> 0.
  Proof.
    intros * Hp Hk.
    assert (1 <= p - k < p).
    lia.
    apply fact_k_nt_zero.
    exact Hp.
    exact H.
  Qed.

  (** [p ∣ p!]. *)
  Lemma fact_p_zero : forall p : nat,
    prime (Z.of_nat p) ->  Nat.modulo (fact p) p = 0.
  Proof.
    intros p Hp.
    apply prime_ge_2 in Hp.
    destruct p.
    lia. destruct p.
    lia.
    assert (Hf : fact (S (S p)) = S (S p) * fact (S p)).
    simpl. reflexivity.
    rewrite Hf; clear Hf.
    rewrite Nat.mul_comm,
    Nat.Div0.mod_mul.
    reflexivity.
  Qed.

  (** For a prime [p], [p ∣ C(p,k)] exactly when [k ≠ 0] and [k ≠ p].  The
      interesting direction uses [p! = k! · (p-k)! · C(p,k)]: [p] divides the
      left side but neither [k!] nor [(p-k)!], so by Euclid's lemma it divides
      [C(p,k)]. *)
  Lemma binom_mod_p : forall p k : nat,
    prime (Z.of_nat p) ->
    Nat.modulo (binomial_exp p k) p = 0 <->
    k <> 0 /\ k <> p.
  Proof.
    intros * Hp.
    split; intro Hb.
    split; intro Hk.
    rewrite Hk in Hb.
    rewrite nCo in Hb.
    rewrite Nat.mod_1_l in Hb.
    lia.
    apply prime_ge_2 in Hp.
    lia.
    rewrite Hk in Hb.
    rewrite nCn in Hb.
    rewrite Nat.mod_1_l in Hb.
    lia.
    apply prime_ge_2 in Hp.
    lia.
    (* Converse direction: [k > p] gives [C(p,k) = 0]; otherwise [1 ≤ k < p]. *)
    destruct Hb as [Hbl Hbr].
    assert (Hpp: (2 <= Z.of_nat p)%Z).
    eapply prime_ge_2; assumption.
    assert (Hk : (p < k) \/ (k <= p)).
    lia.
    destruct Hk as [Hk | Hk].
    pose proof k_gt_n p k Hk as Hppp.
    rewrite Hppp.
    rewrite Nat.Div0.mod_0_l.
    reflexivity.
    assert (Hkp: 1 <= k < p).
    lia.
    (* [p! = k! · (p-k)! · C(p,k)] and [p ∣ p!]; apply Euclid's lemma twice and
       rule out [p ∣ k!] and [p ∣ (p-k)!]. *)
    pose proof connect_fact_with_binomial_exp_def k (p - k) as Hvt.
    rewrite n_k_interchange in Hvt.
    assert (Hw : p - k + k = p).
    lia. rewrite Hw in Hvt; clear Hw.
    assert (Hmp: Nat.modulo (fact p) p =
      Nat.modulo (fact k * fact (p - k) * binomial_exp p k) p).
    rewrite Hvt. reflexivity.
    symmetry in Hmp.
    rewrite fact_p_zero in Hmp.
    pose proof fact_k_nt_zero k p Hp Hkp as Hf.
    pose proof fact_pk_nt_zero k p Hp Hkp as Hpf.
    apply connection_between_divide_and_mod.
    exact Hp.
    apply connection_between_divide_and_mod  in Hmp.
    apply prime_div_mul in Hmp.
    destruct Hmp as [Hmp | Hmp].
    apply prime_div_mul in Hmp.
    destruct Hmp as [Hmp | Hmp].
    apply connection_between_not_divide_and_mod in Hf.
    congruence.
    exact Hp.
    apply connection_between_not_divide_and_mod in Hpf.
    congruence.
    exact Hp. exact Hp.
    exact Hmp.
    all:exact Hp.
  Qed.

  (** Restriction of [binom_mod_p] to [k ≤ p]: [p ∣ C(p,k) ↔ 1 ≤ k < p]. *)
  Lemma binom_mod_p_bound : forall p k : nat,
    prime (Z.of_nat p) -> k <= p ->
    Nat.modulo (binomial_exp p k) p = 0 <->
    1 <= k < p.
  Proof.
    intros * Hp Hk; split; intro H.
    apply binom_mod_p in H.
    lia.
    exact Hp.
    apply binom_mod_p.
    exact Hp.
    lia.
  Qed.

  (** [list_upto n] has no duplicates. *)
  Lemma list_upto_no_dup : forall n,
    NoDup (list_upto n).
  Proof.
    induction n.
    + simpl. constructor.
      intros H. inversion H.
      constructor.
    + simpl. constructor.
      intros H.
      pose proof list_elem_bound n (S n) H as Hf.
      lia.
      exact IHn.
  Qed.

  (** For [n ≥ 2], [list_upto n] decomposes as [n :: l ++ [0]] where every
      element of the middle part [l] lies strictly between [0] and [n]. *)
  Lemma split_upto_hd_tl : forall n : nat,
    2 <= n -> exists l : list nat,
    list_upto n = n :: l ++ [0] /\
    (forall x, In x l -> 1 <= x < n).
  Proof.
    induction n.
    + intros H; lia.
    + destruct n.
      - intros H; lia.
      - intros H; destruct n.
        ++
          simpl. exists [1].
          split. reflexivity.
          intros ? Hx. simpl in Hx.
          destruct Hx as [Hx | Hx];
          lia.
        ++ assert (Hp: 1 < S (S n)) by lia.
           destruct (IHn Hp) as [lp [Hl Hr]].
           simpl in * |- *.
           exists (S (S n) :: lp).
           split. f_equal.
           rewrite Hl. simpl.
           reflexivity.
           intros x [Hx | Hx].
           lia. specialize (Hr x Hx).
           lia.
  Qed.

  (** ** Fermat's little theorem *)

  (** The ‘freshman's dream’ for [+1]: [(x+1)^p ≡ x^p + 1 (mod p)] for prime
      [p].  Expanding with [pow_add] and splitting the index list with
      [split_upto_hd_tl], the two extreme terms give [x^p] and [1] and every
      middle term has coefficient [C(p,k)] with [1 ≤ k < p], which vanishes
      modulo [p] by [binom_mod_p_bound]. *)
  Lemma prime_pow_exp : forall (x p : nat),
    prime (Z.of_nat p) ->
    Nat.modulo (Nat.pow (x + 1) p) p = Nat.modulo (Nat.pow x p + 1) p.
  Proof.
    intros * Hp.
    rewrite pow_add.
    unfold sum_xy, populate_terms.
    rewrite map_map.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hpp.
    assert (Hpt : 2 <= p). lia.
    destruct (split_upto_hd_tl p Hpt) as [l [Hl Hr]].
    rewrite Hl. simpl.
    rewrite map_last. simpl.
    rewrite nCn, nCo.
    simpl. rewrite Nat.sub_diag,
    Nat.sub_0_r, Nat.pow_1_l,
    Nat.add_0_r. simpl.
    rewrite Nat.add_0_r,
    Nat.mul_1_r.
    rewrite fold_right_app.
    simpl. clear Hl.
    (* Induction over the middle indices: each middle term is [0] modulo [p]. *)
    induction l.
    + simpl. f_equal. lia.
    + simpl in * |- *.
      pose proof (Hr a (or_introl eq_refl)) as Hw.
      apply binom_mod_p_bound in Hw.
      rewrite
      Nat.pow_1_l, Nat.mul_1_r.
      remember
      ((fold_right (fun x0 acc : nat => acc + x0) 1
      (map (fun x0 : nat => binomial_exp p x0 * x ^ x0 * 1 ^ (p - x0)) l))) as t.
      rewrite <-Nat.Div0.add_mod_idemp_l.
      assert (Hv : (t + binomial_exp p a * x ^ a) mod p =
        t mod p).
      rewrite <-Nat.Div0.add_mod_idemp_r,
      Nat.Div0.mul_mod, Hw.
      simpl.
      rewrite Nat.Div0.mod_0_l,
      Nat.add_0_r. reflexivity.
      rewrite Hv.
      rewrite Nat.Div0.add_mod_idemp_l.
      apply IHl.
      intros y Hy.
      apply Hr. right.
      exact Hy.
      exact Hp.
      lia.
  Qed.

  (** Fermat's little theorem, general form: [n^p ≡ n (mod p)] for every
      natural [n] and prime [p].  Induction on [n] using [prime_pow_exp]. *)
  Lemma fermat_little_simp : forall n p : nat, prime (Z.of_nat p) ->
    Nat.modulo (Nat.pow n p) p = Nat.modulo n p.
  Proof.
    induction n.
    - simpl; intros * Hp.
      apply prime_ge_2 in Hp.
      assert (Hz : 0 ^ p = 0).
      destruct p. lia.
      destruct p. simpl.
      lia. simpl. lia.
      rewrite Hz. lia.
    - simpl; intros * Hp.
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hpp.
      assert (Hs : S n = n + 1) by lia.
      rewrite Hs; clear Hs.
      rewrite prime_pow_exp.
      specialize (IHn p Hp).
      rewrite <-Nat.Div0.add_mod_idemp_l.
      rewrite IHn.
      rewrite Nat.Div0.add_mod_idemp_l.
      reflexivity.
      exact Hp.
  Qed.

  (** For [a ≤ b], [a ≡ b (mod p) ↔ p ∣ b - a]. *)
  Lemma mod_div_same : forall p a b,
    prime (Z.of_nat p) -> a <= b ->
    a mod p = b mod p <-> Nat.divide p (b - a).
  Proof.
    intros * Hp Hab; split; intros Ht.
    - exists ((b / p) - (a / p)).
      rewrite Nat.mul_comm,
      Nat.mul_sub_distr_l.
      assert (Hpt : p <> 0).
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
      lia.
      rewrite (Nat.div_mod a p Hpt) at 1.
      rewrite (Nat.div_mod b p Hpt) at 1.
      lia.
    - destruct Ht as [z Hz].
      assert (b = a + z * p) by lia.
      assert (Hbb: b mod p = (a + z * p) mod p).
      congruence.
      rewrite Hbb.
      rewrite Nat.Div0.mod_add.
      reflexivity.
  Qed.

  (** Cancellation modulo a prime: if [p ∤ a] and [a · b ≡ a (mod p)] then
      [b ≡ 1 (mod p)].  From [p ∣ a·b - a = a·(b-1)] and Euclid's lemma,
      [p ∣ b - 1]. *)
  Lemma mod_simpl : forall a b p : nat,
    prime (Z.of_nat p) ->
    Nat.modulo a p <> 0 ->
    Nat.modulo (a * b) p = Nat.modulo a p ->
    Nat.modulo b p = 1.
  Proof.
    intros * Hp Ha Hab.
    assert (Hn : a <> 0).
    intros H. rewrite H in Ha.
    rewrite Nat.Div0.mod_0_l in Ha.
    lia.
    assert (Ht : b <> 0).
    intro H. rewrite H in Hab.
    rewrite Nat.mul_comm in Hab.
    rewrite Nat.Div0.mod_0_l in Hab.
    lia.
    assert (Hu : a <= a * b).
    destruct a. lia.
    destruct b. lia.
    lia. symmetry in Hab.
    apply mod_div_same in Hab.
    assert(Hsimp: a * b - a = a * (b - 1)).
    rewrite Nat.mul_sub_distr_l.
    lia. rewrite Hsimp in Hab;
    clear Hsimp.
    (* [p ∣ a · (b-1)]; the case [p ∣ a] contradicts the hypothesis, the case
       [p ∣ b - 1] gives [b ≡ 1]. *)
    apply prime_div_mul in Hab.
    destruct Hab as [Hab | Hab].
    apply connection_between_divide_and_mod in Hab.
    lia. exact Hp.
    apply connection_between_divide_and_mod in Hab.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
    assert (Hadd :  (1 + (b - 1)) mod p = 1 mod p).
    rewrite <-Nat.Div0.add_mod_idemp_r.
    rewrite Hab, Nat.add_0_r.
    reflexivity.
    assert (Hbt : 1 + (b - 1) = b).
    lia. rewrite Hbt in Hadd.
    rewrite Nat.mod_1_l in Hadd.
    exact Hadd.
    lia. exact Hp.
    exact Hp. exact Hp.
    exact Hu.
  Qed.

  (** Fermat's little theorem, coprime form, on [nat]:
      if [p ∤ a] then [a^(p-1) ≡ 1 (mod p)].  Write [a^p = a · a^(p-1)] and
      cancel [a] in [fermat_little_simp] with [mod_simpl]. *)
  Theorem fermat_little_coprime : forall (a p : nat),
    prime (Z.of_nat p) ->
    Nat.modulo a p <> 0 ->
    Nat.modulo (Nat.pow a (p - 1)) p = 1.
  Proof.
    intros * Hp Hn.
    pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
    assert (Hnp : a ^ p = a * a ^ (p - 1)).
    destruct p. lia.
    destruct p. lia.
    simpl. lia.
    pose proof fermat_little_simp a p Hp as Ha.
    rewrite Hnp in Ha.
    apply mod_simpl with (a := a).
    exact Hp.
    exact Hn.
    exact Ha.
  Qed.

  (** Fermat's little theorem for the standard library's [Zpow_mod] on
      non-negative inputs given as [N]:
      if [Z.of_N a mod Z.of_N p ≠ 0] then [Zpow_mod a (p-1) p = 1].
      The proof converts [Zpow_mod] to the executable [Npow_mod] ([zmod_nmod]),
      then to the unary model and to [nat] ([npow_mod_nat]), where
      [fermat_little_coprime] applies. *)
  Theorem fermat_little_Z : forall (a : N) (p : N),
    prime (Z.of_N p) ->
    Z.modulo (Z.of_N a) (Z.of_N p) <> 0%Z ->
    Zpow_mod (Z.of_N a) (Z.of_N (p - 1)) (Z.of_N p) = 1%Z.
  Proof.
    intros * Hp Hna.
    rewrite <-zmod_nmod,
    <-npow_mod_exp_unary_binary_eqv.
    pose proof npow_mod_nat
      (N.to_nat (p - 1)) (N.to_nat a)  (N.to_nat p).
    pose proof prime_ge_2 (Z.of_N p) Hp as Hf.
    rewrite !N_nat_Z in H.
    specialize (H Hp).
    repeat rewrite N2Nat.id in H.
    rewrite H.
    rewrite <-N2Nat.inj_pow,
    <-N2Nat.inj_mod,
    N2Nat.id.
    assert (Hz : Z.of_N 1 = 1%Z). lia.
    rewrite <-Hz.
    apply N2Z.inj_iff.
    rewrite N_to_nat_exp.
    (* Apply the [nat] version; it remains to transport [p ∤ a] to [nat]. *)
    pose proof fermat_little_coprime
    (N.to_nat a) (N.to_nat p) as Hc.
    rewrite N_nat_Z in Hc.
    specialize (Hc Hp).
    assert (Hnz : N.to_nat a mod N.to_nat p <> 0).
    intro Htf. apply Hna.
    rewrite <-N2Nat.inj_mod in Htf.
    rewrite <-N2Z.inj_mod. lia.
    specialize (Hc Hnz).
    assert (Hnt: (N.to_nat p - 1) =
    (N.to_nat (p - 1))). lia.
    rewrite Hnt in Hc.
    rewrite Hc. lia.
    exact Hp.
    exact Hp.
    exact Hp.
  Qed.

  (** Fermat's little theorem on [Z], in the form used by [Zpstar.v]:
      for a prime [p] and [0 < a < p], [Zpow_mod a (p-1) p = 1].  All
      integers are non-negative, so they are converted to [N] and
      [fermat_little_Z] is applied; the side condition [a mod p ≠ 0] comes from
      [mod_not_zero_one] in [Util.v]. *)
  Theorem fermat_little_ZZ :
    forall (a : Z) (p : Z),
    prime p ->
    (0 < a < p)%Z ->
    Zpow_mod a (p - 1) p = 1%Z.
  Proof.
    intros * Hp Ha.
    assert (Hw : a = Z.of_N (Z.to_N a)).
    rewrite Z2N.id;
    try reflexivity.
    nia.
    rewrite Hw;
    clear Hw.
    assert (Hw : (p - 1 = Z.of_N (Z.to_N (p - 1)))%Z).
    rewrite Z2N.id;
    try reflexivity.
    nia.
    rewrite Hw;
    clear Hw.
    assert (Hw : (p = Z.of_N (Z.to_N p))%Z).
    rewrite Z2N.id;
    try reflexivity.
    nia.
    rewrite Hw;
    clear Hw.
    assert (Hw : (Z.of_N (Z.to_N (Z.of_N (Z.to_N p) - 1))) =
    (Z.of_N (Z.to_N p - 1))).
    nia.
    rewrite Hw; clear Hw.
    (* All arguments are now of the form [Z.of_N _]; apply the [N] version. *)
    rewrite fermat_little_Z.
    reflexivity.
    rewrite Z2N.id.
    exact Hp.
    nia.
    rewrite !Z2N.id.
    intro Hf.
    pose proof @mod_not_zero_one p a Ha as Hw.
    all:nia.
  Qed.

  (** ** Range of modular powers

      For [p ∤ a] the powers of [a] stay in [{1, …, p-1}] modulo [p]; this
      shows that the Fermat inverse is a valid element of [Z_p^*]. *)

  (** [0 < a^n mod p < p] whenever [p ∤ a].  Induction on [n]; in the step,
      [a] and [a^n] are both written as [k·p + w] with [0 < w < p], and the
      product of two nonzero residues is nonzero modulo a prime
      ([znot_zero_mul_proof] in [Util.v]). *)
  Lemma fermat_bound_nat :
    forall (n a p : nat),
    prime (Z.of_nat p) ->
    Nat.modulo a p <> 0 ->
    0 < Nat.modulo (Nat.pow a n) p < p.
  Proof.
    induction n;
    intros ? ? Hp Ha.
    pose proof @Hp_2_p (Z.of_nat p) Hp.
    + cbn.
      rewrite Nat.mod_1_l.
      all:nia.
    + cbn.
      specialize (IHn a p Hp Ha).
      remember (a^n) as b.
      assert (Hvt : b mod p <> 0).
      nia.
      (* Decompose [a = k₁·p + w₁] and [a^n = k₂·p + w₂] with nonzero remainders. *)
      pose proof @mod_not_eq_zero (Z.of_nat p) Hp (Z.of_nat a) as Ht.
      assert (Hwt: (Z.of_nat a mod Z.of_nat p)%Z <> 0%Z).
      intro Hf.
      rewrite <-Nat2Z.inj_mod in Hf.
      nia.
      destruct Ht as [Htl _].
      destruct (Htl Hwt) as (k1 & w1 & H1 & H2).
      pose proof @mod_not_eq_zero (Z.of_nat p) Hp (Z.of_nat b) as Htt.
      assert (Hwtt: (Z.of_nat b mod Z.of_nat p)%Z <> 0%Z).
      intro Hf.
      rewrite <-Nat2Z.inj_mod in Hf.
      nia.
      destruct Htt as [Httl _].
      destruct (Httl Hwtt) as (k2 & w2 & H3 & H4).
      split.
      eapply Nat2Z.inj_lt.
      rewrite Nat2Z.inj_mod, Nat2Z.inj_mul.
      rewrite H1, H3.
      (* Expand the product: modulo [p] only [w₁ · w₂] survives. *)
      assert (Hab : (((k1 * Z.of_nat p + w1) * (k2 * Z.of_nat p + w2)) =
        ((w1 * w2) + ((k1  * k2 * Z.of_nat p + k1 * w2 +
          w1 * k2) * Z.of_nat p)))%Z).
      nia.
      rewrite Hab; clear Hab.
      rewrite <-Zplus_mod_idemp_r.
      rewrite Z_mod_mult.
      rewrite Z.add_comm.
      cbn.
      pose proof @znot_zero_mul_proof (Z.of_nat p) Hp _ _ H2 H4 as Hf.
      nia.
      apply Nat.mod_upper_bound.
      nia.
  Qed.

  (** The [Z] version: for prime [p], [0 ≤ n] and [0 < a < p],
      [0 < Zpow_mod a n p < p].  Obtained from [fermat_bound_nat] via [Z.to_nat]
      and [Zpow_mod_correct]. *)
  Lemma fermat_bound_gen :
    forall (a n p : Z),
    prime p ->
    (0 <= n)%Z ->
    (0 < a < p)%Z ->
    (0 < Zpow_mod a n p < p)%Z.
  Proof.
    intros ? ? ? Hp Hn Ha.
    pose proof fermat_bound_nat
      (Z.to_nat n)
      (Z.to_nat a) (Z.to_nat p) as Hw.
    rewrite Z2Nat.id in Hw.
    specialize (Hw Hp).
    assert (Hv : (Z.modulo a p <> 0)%Z).
    eapply mod_single_not_zero.
    nia.
    assert (Hvt : Z.to_nat a mod Z.to_nat p <> 0).
    rewrite <-Z2Nat.inj_mod.
    intro Hf.
    assert (Hff : 0 = Z.to_nat 0).
    nia. rewrite Hff in Hf;
    clear Hff.
    apply Z2Nat.inj_iff in Hf.
    nia.
    apply Z_mod_nonneg_nonneg.
    all:try nia.
    specialize (Hw Hvt).
    rewrite <-Z2Nat.inj_pow, <-Z2Nat.inj_mod in Hw.
    rewrite Zpow_mod_correct.
    all:try nia.
    Unshelve.
    exact Hp.
  Qed.

  (** The Fermat inverse is in range: for prime [p] and [0 < a < p],
      [0 < Zpow_mod a (p-2) p < p].  (This needs [p - 2 ≥ 0], which holds since
      [p ≥ 2].) *)
  Lemma fermat_bound :
    forall (a : Z) (p : Z),
    prime p ->
    (0 < a < p)%Z ->
    (0 < Zpow_mod a (p - 2) p < p)%Z.
  Proof.
    intros ? ? Hp Ha.
    apply fermat_bound_gen;
    try assumption.
    nia.
  Qed.

End Fermat_Little_Theorem.
