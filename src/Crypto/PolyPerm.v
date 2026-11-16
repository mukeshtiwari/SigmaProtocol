(* Polynomials and permutations (Step 4.3 of plans/ZK_APPLICATIONS_PLAN.md):
   the two facts that turn the product argument's conclusion of the
   Bayer–Groth shuffle into a permutation.

   - The root multiset lemma: if ∏_i (r_i − z) = ∏_i (s_i − z) for more
     values of z than there are factors (z in a duplicate-free list), the
     lists r and s are permutations of each other (prod_roots_perm). The
     proof is by induction: the polynomials agree as coefficient lists
     (SigmaK.agree_nth), so at z = r_0 some factor of the right-hand side
     vanishes; cancelling it leaves the identity on all z ≠ r_0.
   - The shuffle's identity: if ∏_i (y a_i + b_i − z) = ∏_i (y·i + x^i − z)
     for all y in a set Y with |Y| > 2N² and all z in a set Z with |Z| > N,
     then a is a permutation σ of 0..N−1 (as field elements) and
     b_i = x^{σ(i)} (perm_of_products). The counting replaces
     Schwartz–Zippel: each linear polynomial in y that is not identically
     zero has at most one root, so a common non-root exists in Y
     (PolyRoots.common_nonroot); it requires the field elements
     0, 1, …, N−1 to be distinct (a hypothesis, true for prime fields of
     order > N). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Crypto Require Import PolyRoots SigmaK.
Import ListNotations.

Section PolyPerm.

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

  (* ---------------------------------------------------------------- *)
  (* products of linear factors r − z                                  *)
  (* ---------------------------------------------------------------- *)

  Definition prodz (rs : list F) (z : F) : F := fold_right mul one (map (fun r => r - z) rs).

  Lemma prodz_cons : forall r rs z, prodz (r :: rs) z = (r - z) * prodz rs z.
  Proof. reflexivity. Qed.

  Lemma prodz_perm : forall rs ss z, Permutation rs ss -> prodz rs z = prodz ss z.
  Proof.
    intros rs ss z hp; induction hp as [| a l l' hp ih | a b l | l l' l'' hp1 ih1 hp2 ih2].
    + reflexivity.
    + rewrite !prodz_cons, ih; reflexivity.
    + rewrite !prodz_cons; field.
    + rewrite ih1, ih2; reflexivity.
  Qed.

  Lemma prodz_zero_in : forall rs z, prodz rs z = zero -> exists r, In r rs /\ r = z.
  Proof.
    induction rs as [| r rs ih]; intros z h.
    + exfalso. unfold prodz in h; cbn in h.
      pose proof (@field_is_zero_neq_one _ _ _ _ _ _ _ _ _ _ Hf) as hz; hnf in hz; apply hz; symmetry; exact h.
    + rewrite prodz_cons in h. destruct (mul_eq_zero _ _ h) as [h' | h'].
      - exists r; split; [left; reflexivity | apply sub_eq_zero; exact h'].
      - destruct (ih z h') as (s & hs & e); exists s; split; [right; exact hs | exact e].
  Qed.

  (* ∏ (r_i − z) as a polynomial in z *)
  Definition prod_lin_neg (rs : list F) : list F :=
    fold_right (fun r acc => pmulF [r; opp one] acc) [one] rs.

  Lemma eval_prod_lin_neg : forall rs z, eval (prod_lin_neg rs) z = prodz rs z.
  Proof.
    induction rs as [| r rs ih]; intros z; [cbn; field |].
    unfold prod_lin_neg; cbn [fold_right]; rewrite eval_pmulF; unfold prod_lin_neg in ih; rewrite ih, prodz_cons.
    cbn [eval]; field.
  Qed.

  Lemma prod_lin_neg_nonnil : forall rs, prod_lin_neg rs <> [].
  Proof.
    intros rs; destruct rs as [| r rs]; [discriminate |].
    unfold prod_lin_neg; cbn [fold_right pmulF]. destruct (fold_right _ _ _) as [| a l]; discriminate.
  Qed.

  Lemma length_prod_lin_neg : forall rs, length (prod_lin_neg rs) = S (length rs).
  Proof.
    induction rs as [| r rs ih]; [reflexivity |].
    unfold prod_lin_neg; cbn [fold_right]; rewrite length_pmulF by (discriminate || apply prod_lin_neg_nonnil).
    unfold prod_lin_neg in ih; rewrite ih; cbn [length]; lia.
  Qed.

  (* agreement on more than n points gives agreement everywhere *)
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

  (* removing one value from a duplicate-free list loses at most one element *)
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

  (* the root multiset lemma *)
  Theorem prod_roots_perm : forall (rs ss : list F) (Zs : list F), NoDup Zs ->
    length rs = length ss -> (length rs < length Zs)%nat ->
    (forall z, In z Zs -> prodz rs z = prodz ss z) -> Permutation rs ss.
  Proof.
    induction rs as [| r rs ih]; intros ss Zs hnd hl hlen hag.
    + destruct ss; [constructor | discriminate].
    + pose proof (prodz_agree_all Zs (r :: rs) ss hnd hl hlen hag) as hall.
      (* r is a root of the right-hand side *)
      assert (hr : prodz ss r = zero).
      { rewrite <-hall, prodz_cons. assert (e : r - r = zero) by field. rewrite e; field. }
      destruct (prodz_zero_in ss r hr) as (s & hs & ->).
      destruct (in_split _ _ hs) as (ss1 & ss2 & ->).
      assert (hperm : Permutation (r :: ss1 ++ ss2) (ss1 ++ r :: ss2)) by apply Permutation_middle.
      (* cancel the common factor on z ≠ r *)
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

  (* ---------------------------------------------------------------- *)
  (* from the product identity to a permutation                        *)
  (* ---------------------------------------------------------------- *)

  Lemma nth_map_seq : forall {A : Type} (f : nat -> A) (n i : nat) (d : A), (i < n)%nat ->
    nth i (map f (seq 0 n)) d = f i.
  Proof.
    intros A f n i d hi.
    rewrite (nth_indep _ d (f 0%nat)) by (rewrite length_map, length_seq; exact hi).
    rewrite map_nth, seq_nth by exact hi; reflexivity.
  Qed.

  (* a linear polynomial c1·y + c0 that is not identically zero *)
  Lemma linear_nonzero : forall c0 c1 : F, ~ (c1 = zero /\ c0 = zero) -> ~ pzero (zero := zero) [c0; c1].
  Proof.
    intros c0 c1 h hz. inversion hz as [| ? ? h0 hz']; subst. inversion hz' as [| ? ? h1 _]; subst.
    apply h; split; (assumption || reflexivity).
  Qed.

  Lemma eval_linear2 : forall c0 c1 y, eval [c0; c1] y = c1 * y + c0.
  Proof. intros; cbn; field. Qed.

  (* the multiset equality at one y *)
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
    (* the multiset equality, for every y ∈ Y *)
    assert (hperm : forall y, In y Y ->
      Permutation (map (fun i => y * nth i a zero + nth i b zero) (seq 0 N)) (map (fun i => y * fnat i + fpow x i) (seq 0 N))).
    { intros y hy; apply (products_perm N a b x y Z hndZ hlZ); intros z hz; apply hag; assumption. }
    (* step 2: every (a_i, b_i) is some (j, x^j) *)
    assert (hsome : forall i, (i < N)%nat -> exists j, (j < N)%nat /\ nth i a zero = fnat j /\ nth i b zero = fpow x j).
    { intros i hi.
      destruct (Exists_dec (fun j => nth i a zero = fnat j /\ nth i b zero = fpow x j) (seq 0 N)) as [hex | hnex].
      { intro j; destruct (Fdec (nth i a zero) (fnat j)), (Fdec (nth i b zero) (fpow x j)); tauto. }
      + apply Exists_exists in hex; destruct hex as (j & hj & hj'); apply in_seq in hj; exists j; split; [lia | exact hj'].
      + exfalso.
        (* the N linear polynomials (a_i − j)·y + (b_i − x^j) are all non-zero *)
        set (ps := map (fun j => [nth i b zero - fpow x j; nth i a zero - fnat j]) (seq 0 N)).
        assert (hps : forall p, In p ps -> ~ pzero (zero := zero) p /\ (length p <= 2)%nat).
        { intros p hp; unfold ps in hp; apply in_map_iff in hp; destruct hp as (j & <- & hj); split; [| reflexivity].
          apply linear_nonzero; intros [h1 h0]; apply hnex; apply Exists_exists; exists j; split; [exact hj |].
          split; apply sub_eq_zero; assumption. }
        assert (hbound : (length ps * 2 < length Y)%nat) by (unfold ps; rewrite length_map, length_seq; nia).
        destruct (common_nonroot (Fdec := Fdec) (Hf := Hf) Y ps 2 hndY hps hbound) as (y & hy & hnr).
        (* but y a_i + b_i is some y j + x^j *)
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
    (* step 3: at some y ∈ Y the right-hand values are pairwise distinct *)
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
    (* injectivity of i ↦ y a_i + b_i *)
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
    (* the permutation *)
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
