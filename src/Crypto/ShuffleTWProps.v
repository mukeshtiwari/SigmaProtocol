(* The Terelius–Wikström proof of a shuffle as a whole (Step 1.3 of
   plans/ZK_APPLICATIONS_PLAN.md): the theorems about the five-move
   protocol that are not instances of the library's Okamoto theorems.

   Crypto/ShuffleTW.v treats round 2 (the Okamoto protocol at the statement
   space V) and shows that its relation is the conjunction of the five
   equations. This file adds:

   - the honest prover: from a permutation π, commitment randomness r,
     re-encryption randomness s and chain randomness β, the permutation
     commitment u_j = g^{r_j} h_{π⁻¹(j)}, the outputs
     w'_i = w_{π(i)} · Enc(1; s_{π(i)}), the bridging chain
     B_i = g^{β_i} B_{i−1}^{e'_i} with e'_i = e_{π(i)}, and the derived
     witness a = ⟨r, e⟩, c = Σ r, d = Σ_i β_i ∏_{k>i} e'_k, f = ⟨s, e⟩;
   - completeness: this witness satisfies the five equations
     (tw_derived_witness_correct), so round 2 accepts
     (tw_full_completeness);
   - honest-verifier zero knowledge of the whole protocol
     (tw_full_shvzk): for uniformly random β and ω, the bridging chain and
     the round-2 transcript of the honest prover have the same distribution
     as the output of a simulator that knows neither the permutation nor
     the re-encryption randomness. The simulator builds the chain with the
     unpermuted e and runs the Okamoto simulator. The proof is a change of
     variables: the map β ↦ β' with B_i(β, e') = B_i(β', e) is a bijection
     of F^{N+1} (reshift), which needs h_0 = g^{t_0} for some t_0 (in a
     prime-order group every h_0 is; the hypothesis is stated because the
     vector-space class does not say so), composed with the Okamoto change
     of variables ω ↦ ω + v·x.

   The algebra is that of permuting the factors of a product: a fold of
   a commutative, associative operation over a vector is invariant under
   reindexing the vector by a bijection of Fin.t. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool List Permutation setoid_ring.Field
  RelationClasses Morphisms.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto MultiExp ShuffleTW.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
From ExtLib Require Import Monad.
Import VectorNotations MonadNotation.
#[local] Open Scope monad_scope.

(* ------------------------------------------------------------------ *)
(* Enumerating Fin.t, and permutations                                  *)
(* ------------------------------------------------------------------ *)

Section Fins.

  Fixpoint fins (n : nat) : Vector.t (Fin.t n) n :=
    match n with
    | 0 => []
    | S n' => Fin.F1 :: Vector.map Fin.FS (fins n')
    end.

  Lemma nth_fins : forall (n : nat) (i : Fin.t n), (fins n)[@i] = i.
  Proof.
    induction n as [| n ih]; intro i.
    + exact (Fin.case0 _ i).
    + apply (Fin.caseS' i (fun i => (fins (S n))[@i] = i)).
      - reflexivity.
      - intro j; cbn [fins].
        change ((Vector.map Fin.FS (fins n))[@j] = Fin.FS j).
        rewrite (Vector.nth_map Fin.FS (fins n) j j eq_refl), ih; reflexivity.
  Qed.

  (* every vector is the map of its coordinates over fins *)
  Lemma vector_map_nth_fins : forall {A : Type} (n : nat) (v : Vector.t A n),
    Vector.map (fun i => v[@i]) (fins n) = v.
  Proof.
    intros A n v; apply Vector.eq_nth_iff; intros i j <-.
    rewrite (Vector.nth_map _ _ i i eq_refl), nth_fins; reflexivity.
  Qed.

  Lemma to_list_fins_nodup : forall n, List.NoDup (Vector.to_list (fins n)).
  Proof.
    induction n as [| n ih]; cbn [fins].
    + constructor.
    + change (Vector.to_list (Fin.F1 :: Vector.map Fin.FS (fins n)))
        with (List.cons Fin.F1 (Vector.to_list (Vector.map Fin.FS (fins n)))).
      constructor.
      - rewrite Vector.to_list_map. intro h. apply List.in_map_iff in h.
        destruct h as (i & h & _). discriminate h.
      - rewrite Vector.to_list_map. apply Finite.Injective_map_NoDup; [| exact ih].
        intros x y h; exact (Fin.FS_inj x y h).
  Qed.

  Lemma to_list_fins_complete : forall n (i : Fin.t n), List.In i (Vector.to_list (fins n)).
  Proof.
    induction n as [| n ih]; intro i.
    + exact (Fin.case0 _ i).
    + apply (Fin.caseS' i (fun i => List.In i (Vector.to_list (fins (S n))))).
      - left; reflexivity.
      - intro j; cbn [fins].
        change (List.In (Fin.FS j) (List.cons Fin.F1 (Vector.to_list (Vector.map Fin.FS (fins n))))).
        right. rewrite Vector.to_list_map. apply List.in_map, ih.
  Qed.

  (* a permutation of Fin.t n: a bijection with its inverse *)
  Record perm (n : nat) : Type := mk_perm {
    pf : Fin.t n -> Fin.t n;
    pinv : Fin.t n -> Fin.t n;
    pinv_pf : forall i, pinv (pf i) = i;
    pf_pinv : forall i, pf (pinv i) = i
  }.

  Definition perm_inverse {n} (π : perm n) : perm n :=
    mk_perm n (pinv n π) (pf n π) (pf_pinv n π) (pinv_pf n π).

  (* v reindexed by π: (permute π v)_i = v_{π i} *)
  Definition permute {A : Type} {n : nat} (π : perm n) (v : Vector.t A n) : Vector.t A n :=
    Vector.map (fun i => v[@pf n π i]) (fins n).

  Lemma nth_permute : forall {A : Type} {n : nat} (π : perm n) (v : Vector.t A n) (i : Fin.t n),
    (permute π v)[@i] = v[@pf n π i].
  Proof.
    intros; unfold permute; rewrite (Vector.nth_map _ _ i i eq_refl), nth_fins; reflexivity.
  Qed.

  Lemma permute_inverse : forall {A : Type} {n : nat} (π : perm n) (v : Vector.t A n),
    permute π (permute (perm_inverse π) v) = v.
  Proof.
    intros; apply Vector.eq_nth_iff; intros i j <-.
    rewrite !nth_permute; cbn [pf perm_inverse]. rewrite pinv_pf; reflexivity.
  Qed.

  Lemma permute_map : forall {A B : Type} {n : nat} (f : A -> B) (π : perm n) (v : Vector.t A n),
    permute π (Vector.map f v) = Vector.map f (permute π v).
  Proof.
    intros; apply Vector.eq_nth_iff; intros i j <-.
    rewrite (Vector.nth_map _ _ i i eq_refl), !nth_permute, (Vector.nth_map _ _ _ _ eq_refl); reflexivity.
  Qed.

  Lemma permute_map2 : forall {A B C : Type} {n : nat} (f : A -> B -> C) (π : perm n)
    (v : Vector.t A n) (w : Vector.t B n),
    permute π (Vector.map2 f v w) = Vector.map2 f (permute π v) (permute π w).
  Proof.
    intros; apply Vector.eq_nth_iff; intros i j <-.
    rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), !nth_permute,
      (Vector.nth_map2 _ _ _ _ _ _ eq_refl eq_refl); reflexivity.
  Qed.

  (* the list of coordinates of a permuted vector is a permutation of the
    list of coordinates *)
  Lemma to_list_permute : forall {A : Type} {n : nat} (π : perm n) (v : Vector.t A n),
    Permutation (Vector.to_list (permute π v)) (Vector.to_list v).
  Proof.
    intros A n π v.
    unfold permute. rewrite Vector.to_list_map.
    apply Permutation_trans with (l' := List.map (fun j => v[@j]) (Vector.to_list (fins n))).
    + change (fun i => v[@pf n π i]) with (fun i => (fun j => v[@j]) (pf n π i)).
      rewrite <-List.map_map.
      apply Permutation_map.
      apply (enumerates_perm_map (Vector.to_list (fins n)) (pf n π) (pinv n π)).
      - apply to_list_fins_nodup.
      - apply to_list_fins_complete.
      - apply pinv_pf.
      - apply pf_pinv.
    + rewrite <-Vector.to_list_map, vector_map_nth_fins. apply Permutation_refl.
  Qed.

End Fins.

(* ------------------------------------------------------------------ *)
(* Folds of commutative operations are invariant under permutation       *)
(* ------------------------------------------------------------------ *)

Section Folds.

  Context {A : Type} {op : A -> A -> A} {id : A}
    {assoc : forall x y z, op x (op y z) = op (op x y) z}
    {comm : forall x y, op x y = op y x}
    {idl : forall x, op id x = x}.

  Lemma fold_right_perm : forall (l l' : list A), Permutation l l' ->
    List.fold_right op id l = List.fold_right op id l'.
  Proof.
    intros l l' h; induction h as [| x l l' _ ih | x y l | l l' l'' _ ih1 _ ih2]; cbn.
    + reflexivity.
    + rewrite ih; reflexivity.
    + rewrite !assoc, (comm y x); reflexivity.
    + rewrite ih1, ih2; reflexivity.
  Qed.

  Lemma vector_fold_right_to_list : forall (n : nat) (v : Vector.t A n),
    Vector.fold_right op v id = List.fold_right op id (Vector.to_list v).
  Proof.
    induction n as [| n ih]; intro v.
    + rewrite (vector_inv_0 v); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->); cbn; rewrite ih; reflexivity.
  Qed.

  Lemma vector_fold_permute : forall (n : nat) (π : perm n) (v : Vector.t A n),
    Vector.fold_right op (permute π v) id = Vector.fold_right op v id.
  Proof.
    intros; rewrite !vector_fold_right_to_list; apply fold_right_perm, to_list_permute.
  Qed.

  (* a fold over map2 of a commutative monoid operation is the product of
    the folds *)
  Lemma vector_fold_map2 : forall (n : nat) (v w : Vector.t A n),
    Vector.fold_right op (Vector.map2 op v w) id = op (Vector.fold_right op v id) (Vector.fold_right op w id).
  Proof.
    induction n as [| n ih]; intros v w.
    + rewrite (vector_inv_0 v), (vector_inv_0 w); cbn; rewrite idl; reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (b & w' & ->).
      cbn; rewrite ih.
      rewrite !assoc; f_equal. rewrite <-!assoc; f_equal; apply comm.
  Qed.

End Folds.

(* ------------------------------------------------------------------ *)
(* The honest prover and completeness                                   *)
(* ------------------------------------------------------------------ *)

Section Honest.

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
  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.

  (* the group laws, as explicit terms *)
  Local Notation hcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv
    G (@eq G) gid ginv gop gpow Hvec).
  Local Notation gassoc := (@associative G (@eq G) gop (@monoid_is_associative G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv hcg)))).
  Local Notation gid_l := (@left_identity G (@eq G) gop gid (@monoid_is_left_idenity G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv hcg)))).
  Local Notation gid_r := (@right_identity G (@eq G) gop gid (@monoid_is_right_identity G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv hcg)))).
  Local Notation ginv_l := (@left_inverse G (@eq G) gop gid ginv (@group_is_left_inverse G (@eq G) gop gid ginv
    (@commutative_group_group G (@eq G) gop gid ginv hcg))).
  Local Notation ginv_r := (@right_inverse G (@eq G) gop gid ginv (@group_is_right_inverse G (@eq G) gop gid ginv
    (@commutative_group_group G (@eq G) gop gid ginv hcg))).
  Local Notation gcomm := (@commutative G (@eq G) gop (@commutative_group_is_commutative G (@eq G) gop gid ginv hcg)).
  (* the vector-space laws, as lemmas *)
  Lemma smul_fadd : forall (r1 r2 : F) (x : G), x ^ (r1 + r2) = gop (x ^ r1) (x ^ r2).
  Proof. pose proof (@vector_space_smul_distributive_fadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_vadd : forall (r : F) (x y : G), (gop x y) ^ r = gop (x ^ r) (y ^ r).
  Proof. pose proof (@vector_space_smul_distributive_vadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_fmul : forall (r1 r2 : F) (x : G), x ^ (r1 * r2) = (x ^ r1) ^ r2.
  Proof. pose proof (@vector_space_smul_associative_fmul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_zero : forall x : G, x ^ zero = gid.
  Proof. pose proof (@vector_space_field_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.

  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation cexp := (mexp (vid := (gid, gid)) (vadd := fun x y : G * G => (gop (fst x) (fst y), gop (snd x) (snd y)))
    (smul := fun (x : G * G) (r : F) => (gpow (fst x) r, gpow (snd x) r))).

  Lemma gid_pow : forall r, gid ^ r = gid.
  Proof. intro r; exact (smul_vid (HV := Hvec) r). Qed.

  Lemma ginv_pow : forall (x : G) (r : F), (ginv x) ^ r = ginv (x ^ r).
  Proof.
    intros x r.
    assert (h : gop (x ^ r) ((ginv x) ^ r) = gid).
    { rewrite <-smul_vadd, ginv_r; apply gid_pow. }
    rewrite <-(gid_r ((ginv x) ^ r)), <-(ginv_r (x ^ r)), gassoc, (gcomm ((ginv x) ^ r) (x ^ r)), h, gid_l.
    reflexivity.
  Qed.

  Lemma gop_cancel : forall x y : G, gop (gop x y) (ginv y) = x.
  Proof. intros; rewrite <-gassoc, ginv_r, gid_r; reflexivity. Qed.

  (* folds over F and G *)
  Definition fsum {m : nat} (v : Vector.t F m) : F := Vector.fold_right add v zero.
  Definition inner {m : nat} (rs xs : Vector.t F m) : F := fsum (Vector.map2 mul rs xs).
  Local Notation fprod := (fprod (mul := mul) (one := one)).
  Local Notation gprod := (gprod (gid := gid) (gop := gop)).

  Lemma mul_assoc' : forall x y z : F, x * (y * z) = (x * y) * z. Proof. intros; field. Qed.
  Lemma mul_comm' : forall x y : F, x * y = y * x. Proof. intros; field. Qed.
  Lemma mul_1_l' : forall x : F, one * x = x. Proof. intros; field. Qed.
  Lemma add_assoc' : forall x y z : F, x + (y + z) = (x + y) + z. Proof. intros; field. Qed.
  Lemma add_comm' : forall x y : F, x + y = y + x. Proof. intros; field. Qed.
  Lemma add_0_l' : forall x : F, zero + x = x. Proof. intros; field. Qed.

  Lemma fprod_permute : forall (π : perm M) (v : Vector.t F M), fprod (permute π v) = fprod v.
  Proof. intros; apply (vector_fold_permute (assoc := mul_assoc') (comm := mul_comm')). Qed.

  Lemma fsum_permute : forall (π : perm M) (v : Vector.t F M), fsum (permute π v) = fsum v.
  Proof. intros; apply (vector_fold_permute (assoc := add_assoc') (comm := add_comm')). Qed.

  Lemma gprod_permute : forall (π : perm M) (v : Vector.t G M), gprod (permute π v) = gprod v.
  Proof. intros; apply (vector_fold_permute (assoc := gassoc) (comm := gcomm)). Qed.

  Lemma inner_permute : forall (π : perm M) (rs xs : Vector.t F M),
    inner (permute π rs) (permute π xs) = inner rs xs.
  Proof. intros; unfold inner; rewrite <-permute_map2; apply fsum_permute. Qed.

  Lemma gprod_map2 : forall (m : nat) (v w : Vector.t G m),
    gprod (Vector.map2 gop v w) = gop (gprod v) (gprod w).
  Proof. intros; apply (vector_fold_map2 (assoc := gassoc) (comm := gcomm) (idl := gid_l)). Qed.

  (* multi-exponentiation as a product of powers *)
  Lemma gexp_as_gprod : forall (m : nat) (gs : Vector.t G m) (xs : Vector.t F m),
    gexp gs xs = gprod (Vector.map2 gpow gs xs).
  Proof.
    induction m as [| m ih]; intros gs xs.
    + rewrite (vector_inv_0 gs), (vector_inv_0 xs); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      rewrite mexp_cons, ih; reflexivity.
  Qed.

  Lemma gexp_permute : forall (π : perm M) (gs : Vector.t G M) (xs : Vector.t F M),
    gexp (permute π gs) (permute π xs) = gexp gs xs.
  Proof. intros; rewrite !gexp_as_gprod, <-permute_map2; apply gprod_permute. Qed.

  Lemma gexp_map2_gop : forall (m : nat) (gs gs' : Vector.t G m) (xs : Vector.t F m),
    gexp (Vector.map2 gop gs gs') xs = gop (gexp gs xs) (gexp gs' xs).
  Proof.
    induction m as [| m ih]; intros gs gs' xs.
    + rewrite (vector_inv_0 gs), (vector_inv_0 gs'), (vector_inv_0 xs); cbn; rewrite gid_l; reflexivity.
    + destruct (vector_inv_S gs) as (g & gs1 & ->).
      destruct (vector_inv_S gs') as (g' & gs1' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      rewrite map2_cons, !mexp_cons, ih, smul_vadd.
      rewrite <-!gassoc; f_equal. rewrite !gassoc; f_equal; apply gcomm.
  Qed.

  Lemma gexp_pow : forall (m : nat) (g : G) (rs xs : Vector.t F m),
    gexp (Vector.map (fun r => g ^ r) rs) xs = g ^ inner rs xs.
  Proof.
    induction m as [| m ih]; intros g rs xs.
    + rewrite (vector_inv_0 rs), (vector_inv_0 xs); cbn; unfold inner, fsum; cbn.
      rewrite smul_zero; reflexivity.
    + destruct (vector_inv_S rs) as (r & rs' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      cbn [Vector.map]; rewrite mexp_cons, ih.
      unfold inner, fsum; rewrite map2_cons; cbn [Vector.fold_right].
      rewrite smul_fadd, smul_fmul; reflexivity.
  Qed.

  Lemma gprod_pow : forall (m : nat) (g : G) (rs : Vector.t F m),
    gprod (Vector.map (fun r => g ^ r) rs) = g ^ fsum rs.
  Proof.
    induction m as [| m ih]; intros g rs.
    + rewrite (vector_inv_0 rs); cbn; unfold fsum; cbn. rewrite smul_zero; reflexivity.
    + destruct (vector_inv_S rs) as (r & rs' & ->).
      cbn [Vector.map]; unfold gprod, fsum; cbn [Vector.fold_right].
      change (Vector.fold_right gop (Vector.map (fun r => g ^ r) rs') gid) with (gprod (Vector.map (fun r => g ^ r) rs')).
      rewrite ih, smul_fadd; reflexivity.
  Qed.

  (* ---- the honest prover ---- *)

  (* u_j = g^{r_j} h_{π⁻¹(j)} *)
  Definition commit_perm (g : G) (hs : Vector.t G M) (π : perm M) (rs : Vector.t F M) : Vector.t G M :=
    Vector.map2 gop (Vector.map (fun r => g ^ r) rs) (permute (perm_inverse π) hs).

  (* w'_i = w_{π(i)} · Enc(1; s_{π(i)}) = (u_{π(i)} g^{s_{π(i)}}, v_{π(i)} y^{s_{π(i)}}) *)
  Definition shuffle_outputs (g y : G) (π : perm M) (ws : Vector.t (G * G) M) (ss : Vector.t F M) :
    Vector.t (G * G) M :=
    Vector.map2 (fun w s => (gop (fst w) (g ^ s), gop (snd w) (y ^ s))) (permute π ws) (permute π ss).

  (* the bridging chain B_i = g^{β_i} B_{i-1}^{e'_i} *)
  Fixpoint chain (g : G) (prev : G) {m : nat} (betas : Vector.t F m) : Vector.t F m -> Vector.t G m :=
    match betas with
    | [] => fun _ => []
    | b :: betas' => fun es' =>
        let B := gop (g ^ b) (prev ^ (Vector.hd es')) in
        B :: chain g B betas' (Vector.tl es')
    end.

  (* d = Σ_i β_i ∏_{k>i} e'_k *)
  Fixpoint chain_exp {m : nat} (betas : Vector.t F m) : Vector.t F m -> F :=
    match betas with
    | [] => fun _ => zero
    | b :: betas' => fun es' => b * fprod (Vector.tl es') + chain_exp betas' (Vector.tl es')
    end.

  Lemma shiftout_cons : forall {A : Type} (m : nat) (a b : A) (v : Vector.t A m),
    Vector.shiftout (a :: b :: v) = a :: Vector.shiftout (b :: v).
  Proof. reflexivity. Qed.

  Lemma chain_eq : forall (g : G) (m : nat) (prev : G) (betas es' : Vector.t F m),
    chain g prev betas es' =
    Vector.map2 gop (Vector.map2 gpow (Vector.const g m) betas)
      (Vector.map2 gpow (Vector.shiftout (prev :: chain g prev betas es')) es').
  Proof.
    intros g m; induction m as [| m ih]; intros prev betas es'.
    + rewrite (vector_inv_0 betas), (vector_inv_0 es'); reflexivity.
    + destruct (vector_inv_S betas) as (b & betas' & ->).
      destruct (vector_inv_S es') as (e & es1 & ->).
      cbn [chain Vector.hd Vector.tl Vector.caseS].
      rewrite const_S, shiftout_cons, !map2_cons. f_equal.
      apply ih.
  Qed.

  Lemma fprod_cons : forall (m : nat) (e : F) (v : Vector.t F m), fprod (e :: v) = e * fprod v.
  Proof. reflexivity. Qed.

  Lemma chain_last : forall (g : G) (m : nat) (prev : G) (betas es' : Vector.t F (S m)),
    Vector.last (chain g prev betas es') = gop (g ^ chain_exp betas es') (prev ^ fprod es').
  Proof.
    intros g m; induction m as [| m ih]; intros prev betas es'.
    + destruct (vector_inv_S betas) as (b & betas' & ->).
      destruct (vector_inv_S es') as (e & es1 & ->).
      rewrite (vector_inv_0 betas'), (vector_inv_0 es1).
      cbn [chain chain_exp Vector.hd Vector.tl Vector.caseS].
      change (Vector.last [gop (g ^ b) (prev ^ e)]) with (gop (g ^ b) (prev ^ e)).
      unfold fprod; cbn [Vector.fold_right].
      assert (h1 : b * one + zero = b) by field.
      assert (h2 : e * one = e) by field.
      rewrite h1, h2; reflexivity.
    + destruct (vector_inv_S betas) as (b & betas' & ->).
      destruct (vector_inv_S es') as (e & es1 & ->).
      cbn [chain chain_exp Vector.hd Vector.tl Vector.caseS].
      change (Vector.last (?x :: ?v)) with (Vector.last v).
      rewrite ih, fprod_cons.
      rewrite smul_vadd, <-!smul_fmul, smul_fadd.
      rewrite gassoc, (gcomm (g ^ chain_exp betas' es1) (g ^ (b * fprod es1))); reflexivity.
  Qed.

  (* fst and snd of the shuffled outputs *)
  Lemma map_fst_shuffle : forall (g y : G) (π : perm M) (ws : Vector.t (G * G) M) (ss : Vector.t F M),
    Vector.map fst (shuffle_outputs g y π ws ss) =
    Vector.map2 gop (permute π (Vector.map fst ws)) (Vector.map (fun s => g ^ s) (permute π ss)).
  Proof.
    intros; apply Vector.eq_nth_iff; intros i j <-.
    unfold shuffle_outputs.
    rewrite (Vector.nth_map _ _ i i eq_refl), !(Vector.nth_map2 _ _ _ i i i eq_refl eq_refl),
      (Vector.nth_map _ _ i i eq_refl), permute_map, (Vector.nth_map _ _ i i eq_refl).
    reflexivity.
  Qed.

  Lemma map_snd_shuffle : forall (g y : G) (π : perm M) (ws : Vector.t (G * G) M) (ss : Vector.t F M),
    Vector.map snd (shuffle_outputs g y π ws ss) =
    Vector.map2 gop (permute π (Vector.map snd ws)) (Vector.map (fun s => y ^ s) (permute π ss)).
  Proof.
    intros; apply Vector.eq_nth_iff; intros i j <-.
    unfold shuffle_outputs.
    rewrite (Vector.nth_map _ _ i i eq_refl), !(Vector.nth_map2 _ _ _ i i i eq_refl eq_refl),
      (Vector.nth_map _ _ i i eq_refl), permute_map, (Vector.nth_map _ _ i i eq_refl).
    reflexivity.
  Qed.

  (* the public data of the honest run, in the form of ShuffleTW *)
  Definition honest_public (g y : G) (hs : Vector.t G M) (π : perm M) (rs ss betas es : Vector.t F M)
    (ws : Vector.t (G * G) M) : @public F G N :=
    @ShuffleTW.mk_public F G N g (Vector.hd hs) hs y (commit_perm g hs π rs) es
      (chain g (Vector.hd hs) betas (permute π es)) ws (shuffle_outputs g y π ws ss).

  (* The derived witness satisfies the five equations. *)
  Theorem tw_derived_witness_correct : forall (g y : G) (hs : Vector.t G M) (π : perm M)
    (rs ss betas es : Vector.t F M) (ws : Vector.t (G * G) M),
    equations (one := one) (mul := mul)
      (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
      (honest_public g y hs π rs ss betas es ws)
      (inner rs es) (fsum rs) (chain_exp betas (permute π es)) (inner ss es) betas (permute π es).
  Proof.
    intros; unfold equations, honest_public; cbn [ShuffleTW.g ShuffleTW.h0 ShuffleTW.hs ShuffleTW.pk
      ShuffleTW.us ShuffleTW.es ShuffleTW.Bs ShuffleTW.ws ShuffleTW.ws'].
    repeat split.
    + (* A *)
      unfold commit_perm. rewrite gexp_map2_gop, gexp_pow.
      f_equal. rewrite <-(gexp_permute π), permute_inverse; reflexivity.
    + (* C *)
      unfold commit_perm. rewrite gprod_map2, gprod_pow, gprod_permute, gop_cancel; reflexivity.
    + (* D *)
      rewrite chain_last, fprod_permute, gop_cancel; reflexivity.
    + (* B *)
      unfold Bprev; cbn [ShuffleTW.h0 ShuffleTW.Bs]. apply chain_eq.
    + (* F *)
      rewrite cexp_components, map_fst_shuffle, map_snd_shuffle, !gexp_map2_gop, !gexp_permute, !gexp_pow,
        inner_permute, !ginv_pow.
      f_equal.
      - rewrite gcomm, gop_cancel; reflexivity.
      - rewrite gcomm, gop_cancel; reflexivity.
  Qed.

  (* Completeness of the whole protocol: the honest prover's round 2 is
    accepted, for every batching vector e and every challenge v. *)
  Theorem tw_full_completeness : forall (g y : G) (hs : Vector.t G M) (π : perm M)
    (rs ss betas es : Vector.t F M) (ws : Vector.t (G * G) M) (omega : Vector.t F (Nat.add 4 (Nat.add M M))) (v : F),
    tw_verify (one := one) (mul := mul) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)
      (honest_public g y hs π rs ss betas es ws)
      (tw_real_protocol (one := one) (add := add) (mul := mul) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
        (honest_public g y hs π rs ss betas es ws)
        (witness (inner rs es) (fsum rs) (chain_exp betas (permute π es)) (inner ss es) betas (permute π es))
        omega v) = true.
  Proof.
    intros; apply (tw_completeness (Hvec := Hvec)); apply tw_derived_witness_correct.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Honest-verifier zero knowledge of the whole protocol              *)
  (* ---------------------------------------------------------------- *)

  Local Notation nwit := (Nat.add 4 (Nat.add M M)).
  Local Notation V := (@ShuffleTW.V G N).

  (* the change of variables on the chain randomness: with B_{-1} = g^t,
    the chain of β along e1 equals the chain of (reshift t β e1 e2) along
    e2; the accumulator is the discrete logarithm of the current B_i *)
  Fixpoint reshift (t : F) {m : nat} (betas : Vector.t F m) : Vector.t F m -> Vector.t F m -> Vector.t F m :=
    match betas with
    | [] => fun _ _ => []
    | b :: betas' => fun es1 es2 =>
        let bb := b + t * Vector.hd es1 in
        (bb + opp (t * Vector.hd es2)) :: reshift bb betas' (Vector.tl es1) (Vector.tl es2)
    end.

  Lemma reshift_inverse : forall (m : nat) (t : F) (betas es1 es2 : Vector.t F m),
    reshift t (reshift t betas es1 es2) es2 es1 = betas.
  Proof.
    induction m as [| m ih]; intros t betas es1 es2.
    + rewrite (vector_inv_0 betas); reflexivity.
    + destruct (vector_inv_S betas) as (b & betas' & ->).
      destruct (vector_inv_S es1) as (e1 & es1' & ->).
      destruct (vector_inv_S es2) as (e2 & es2' & ->).
      cbn [reshift Vector.hd Vector.tl Vector.caseS].
      assert (h1 : b + t * e1 + opp (t * e2) + t * e2 = b + t * e1) by field.
      assert (h2 : b + t * e1 + opp (t * e1) = b) by field.
      rewrite h1, h2, ih; reflexivity.
  Qed.

  Lemma chain_head : forall (g : G) (t b e : F), gop (g ^ b) ((g ^ t) ^ e) = g ^ (b + t * e).
  Proof. intros; rewrite smul_fadd, smul_fmul; reflexivity. Qed.

  Lemma chain_reshift : forall (g : G) (m : nat) (t : F) (betas es1 es2 : Vector.t F m),
    chain g (g ^ t) betas es1 = chain g (g ^ t) (reshift t betas es1 es2) es2.
  Proof.
    intros g m; induction m as [| m ih]; intros t betas es1 es2.
    + rewrite (vector_inv_0 betas), (vector_inv_0 es1), (vector_inv_0 es2); reflexivity.
    + destruct (vector_inv_S betas) as (b & betas' & ->).
      destruct (vector_inv_S es1) as (e1 & es1' & ->).
      destruct (vector_inv_S es2) as (e2 & es2' & ->).
      cbn [chain reshift Vector.hd Vector.tl Vector.caseS].
      rewrite !chain_head.
      assert (h : b + t * e1 + opp (t * e2) + t * e2 = b + t * e1) by field.
      rewrite h. f_equal. apply ih.
  Qed.

  Lemma bind_ext : forall {A B : Type} (d : dist A) (f g : A -> dist B),
    (forall a, f a = g a) -> Bind d f = Bind d g.
  Proof.
    intros A B d f g h; induction d as [| [a p] d ih]; cbn; [reflexivity | rewrite h, ih; reflexivity].
  Qed.

  (* the real run: uniformly random chain randomness β and Okamoto
    randomness ω; output the bridging chain and the round-2 transcript *)
  Definition tw_real_full_distribution (lf : list F) (Hlfn : lf <> List.nil)
    (g y : G) (hs : Vector.t G M) (π : perm M) (rs ss es : Vector.t F M) (ws : Vector.t (G * G) M) (v : F) :
    dist (Vector.t G M * @sigma_proto F V 1 1 nwit) :=
    betas <- repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) M ;;
    omega <- repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) nwit ;;
    Ret (chain g (Vector.hd hs) betas (permute π es),
         tw_real_protocol (one := one) (add := add) (mul := mul) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
           (honest_public g y hs π rs ss betas es ws)
           (witness (inner rs es) (fsum rs) (chain_exp betas (permute π es)) (inner ss es) betas (permute π es))
           omega v).

  (* the simulator: knows g, hs, y, the permutation commitment, the input
    and output ciphertexts, e and v, but neither π nor s *)
  Definition tw_sim_full_distribution (lf : list F) (Hlfn : lf <> List.nil)
    (g y : G) (hs : Vector.t G M) (us : Vector.t G M) (ws ws' : Vector.t (G * G) M) (es : Vector.t F M) (v : F) :
    dist (Vector.t G M * @sigma_proto F V 1 1 nwit) :=
    betas <- repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) M ;;
    k <- repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) nwit ;;
    Ret (chain g (Vector.hd hs) betas es,
         tw_simulator (one := one) (mul := mul) (opp := opp) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
           (@ShuffleTW.mk_public F G N g (Vector.hd hs) hs y us es (chain g (Vector.hd hs) betas es) ws ws') k v).

  Theorem tw_full_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (t0 : F)
    (g y : G) (hs : Vector.t G M) (π : perm M) (rs ss es : Vector.t F M) (ws : Vector.t (G * G) M) (v : F),
    Vector.hd hs = g ^ t0 ->
    List.NoDup lf -> (forall x : F, List.In x lf) ->
    Permutation
      (tw_real_full_distribution lf Hlfn g y hs π rs ss es ws v)
      (tw_sim_full_distribution lf Hlfn g y hs (commit_perm g hs π rs) ws (shuffle_outputs g y π ws ss) es v).
  Proof.
    intros * ht hnd hall.
    unfold tw_real_full_distribution, tw_sim_full_distribution.
    set (Db := repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) M).
    set (Dw := repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) nwit).
    set (e' := permute π es).
    set (phi := fun betas => reshift t0 betas e' es).
    set (psi := fun betas => reshift t0 betas es e').
    set (P := fun betas => @ShuffleTW.mk_public F G N g (g ^ t0) hs y (commit_perm g hs π rs) es
      (chain g (g ^ t0) betas es) ws (shuffle_outputs g y π ws ss)).
    set (x := fun betas => witness (inner rs es) (fsum rs) (chain_exp betas e') (inner ss es) betas e').
    change (Permutation
      (Bind Db (fun betas => Bind Dw (fun omega => Ret (chain g (Vector.hd hs) betas e',
        tw_real_protocol (one := one) (add := add) (mul := mul) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
          (honest_public g y hs π rs ss betas es ws) (x betas) omega v))))
      (Bind Db (fun betas => Bind Dw (fun k => Ret (chain g (Vector.hd hs) betas es,
        tw_simulator (one := one) (mul := mul) (opp := opp) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
          (@ShuffleTW.mk_public F G N g (Vector.hd hs) hs y (commit_perm g hs π rs) es
            (chain g (Vector.hd hs) betas es) ws (shuffle_outputs g y π ws ss)) k v))))).
    (* the honest public data of β is the simulator's public data of φ β *)
    assert (hP : forall betas, honest_public g y hs π rs ss betas es ws = P (phi betas)).
    { intro betas; unfold honest_public, P, phi; rewrite ht.
      rewrite (chain_reshift g M t0 betas (permute π es) es); reflexivity. }
    assert (hB : forall betas, chain g (Vector.hd hs) betas e' = chain g (Vector.hd hs) (phi betas) es).
    { intro betas; rewrite ht; apply chain_reshift. }
    apply Permutation_trans with (l' := Bind Db (fun betas => Bind Dw (fun k => Ret (chain g (Vector.hd hs) (phi betas) es,
        tw_simulator (one := one) (mul := mul) (opp := opp) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
          (@ShuffleTW.mk_public F G N g (Vector.hd hs) hs y (commit_perm g hs π rs) es
            (chain g (Vector.hd hs) (phi betas) es) ws (shuffle_outputs g y π ws ss)) k v)))).
    + apply bind_perm_right; intros betas p _.
      rewrite hB, hP.
      replace (@ShuffleTW.mk_public F G N g (Vector.hd hs) hs y (commit_perm g hs π rs) es
        (chain g (Vector.hd hs) (phi betas) es) ws (shuffle_outputs g y π ws ss)) with (P (phi betas))
        by (unfold P; rewrite ht; reflexivity).
      (* the Okamoto zero-knowledge theorem at P (phi betas), paired with the chain *)
      pose proof (tw_special_honest_verifier_zkp_enum (Hvec := Hvec) (P (phi betas)) lf Hlfn
        (inner rs es) (fsum rs) (chain_exp betas e') (inner ss es) betas e' v) as hz.
      unfold tw_real_distribution, tw_simulator_distribution, generalised_okamoto_real_distribution,
        generalised_okamoto_simulator_distribution in hz.
      specialize (hz ltac:(rewrite <-hP; apply tw_derived_witness_correct) hnd hall).
      change (Permutation (Bind Dw (fun us => Ret (tw_real_protocol (one := one) (add := add) (mul := mul) (gid := gid)
          (ginv := ginv) (gop := gop) (gpow := gpow) (P (phi betas)) (x betas) us v)))
        (Bind Dw (fun us => Ret (tw_simulator (one := one) (mul := mul) (opp := opp) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
          (P (phi betas)) us v)))) in hz.
      set (B := chain g (Vector.hd hs) (phi betas) es).
      apply Permutation_trans with (l' := List.map (fun '(t, q) => ((B, t), q))
        (Bind Dw (fun a => Ret (tw_real_protocol (one := one) (add := add) (mul := mul) (gid := gid)
          (ginv := ginv) (gop := gop) (gpow := gpow) (P (phi betas)) (x betas) a v)))).
      { rewrite map_bind. apply Permutation_refl'. apply bind_ext; intro a; reflexivity. }
      apply Permutation_trans with (l' := List.map (fun '(t, q) => ((B, t), q))
        (Bind Dw (fun a => Ret (tw_simulator (one := one) (mul := mul) (opp := opp) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
          (P (phi betas)) a v)))).
      { apply Permutation_map; exact hz. }
      rewrite map_bind. apply Permutation_refl'. apply bind_ext; intro a; reflexivity.
    + apply Permutation_trans with (l' := Bind (List.map (fun '(a, p) => (phi a, p)) Db)
        (fun betas => Bind Dw (fun k => Ret (chain g (Vector.hd hs) betas es,
          tw_simulator (one := one) (mul := mul) (opp := opp) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)
            (@ShuffleTW.mk_public F G N g (Vector.hd hs) hs y (commit_perm g hs π rs) es
              (chain g (Vector.hd hs) betas es) ws (shuffle_outputs g y π ws ss)) k v)))).
      { rewrite bind_map_left. apply Permutation_refl. }
      apply bind_perm_left.
      apply (repeat_uniform_bijection_perm lf Hlfn M phi psi hnd hall).
      - intro betas; unfold psi, phi; apply reshift_inverse.
      - intro betas; unfold psi, phi; apply reshift_inverse.
  Qed.

End Honest.
