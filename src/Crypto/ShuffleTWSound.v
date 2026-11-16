(* Soundness of the Terelius–Wikström proof of a shuffle, part 1: the
   algebra of extraction (Step 1.3 of plans/ZK_APPLICATIONS_PLAN.md).

   The round-2 protocol is special sound (tw_special_soundness in
   Crypto/ShuffleTW.v): two accepting transcripts with distinct challenges
   for the same e give a witness of the five equations. This file works
   with such witnesses directly, as hypotheses "the five equations hold",
   and derives what Terelius and Wikström derive from them:

   - from a witness for each unit vector e = δ_j, an opening of every
     component u_j = g^{a_j} ∏_i h_i^{m_ji} of the permutation commitment
     (openings_from_unit_rounds); the rows m_j form a matrix over F;
   - from a witness for any further e, either the discrete-logarithm
     relation g^{x_0} ∏ h_i^{x_i} = 1 with a non-zero exponent vector (a
     binding break of the Pedersen commitment), or
       e' = Mᵀ e            (relation_A)
       ∏_i (Mᵀ e)_i = ∏_j e_j and the column sums of M are 1  (relation_C,
                                                              relation_D)
   - from the unit-vector rounds also w_j = Enc(1; −f_j) ∏_i w'_i^{m_ji}
     (relation_F), which for a permutation matrix is the re-encryption
     witness w'_{π(j)} = w_j · Enc(1; f_j).

   Crypto/ShuffleTWSound2.v turns the polynomial identity into a
   permutation matrix and assembles the soundness theorem. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool List setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto MultiExp ShuffleTW ShuffleTWProps.
From Utility Require Import Util.
Import VectorNotations.

Section Sound.

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

  Lemma smul_fadd : forall (r1 r2 : F) (x : G), x ^ (r1 + r2) = gop (x ^ r1) (x ^ r2).
  Proof. pose proof (@vector_space_smul_distributive_fadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_vadd : forall (r : F) (x y : G), (gop x y) ^ r = gop (x ^ r) (y ^ r).
  Proof. pose proof (@vector_space_smul_distributive_vadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_fmul : forall (r1 r2 : F) (x : G), x ^ (r1 * r2) = (x ^ r1) ^ r2.
  Proof. pose proof (@vector_space_smul_associative_fmul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_zero : forall x : G, x ^ zero = gid.
  Proof. pose proof (@vector_space_field_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.
  Lemma smul_one : forall x : G, x ^ one = x.
  Proof. pose proof (@vector_space_field_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h; exact h. Qed.

  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation cexp := (mexp (vid := (gid, gid)) (vadd := fun x y : G * G => (gop (fst x) (fst y), gop (snd x) (snd y)))
    (smul := fun (x : G * G) (r : F) => (gpow (fst x) r, gpow (snd x) r))).
  Local Notation gprod := (gprod (gid := gid) (gop := gop)).
  Local Notation fprod := (fprod (mul := mul) (one := one)).
  Local Notation fsum := (fsum (zero := zero) (add := add)).
  Local Notation inner := (inner (zero := zero) (add := add) (mul := mul)).
  Local Notation gid_pow := (gid_pow (Hvec := Hvec)).
  Local Notation ginv_pow := (ginv_pow (Hvec := Hvec)).
  Local Notation gop_cancel := (gop_cancel (Hvec := Hvec)).
  Local Notation chain := (ShuffleTWProps.chain (gop := gop) (gpow := gpow)).

  (* ---------------------------------------------------------------- *)
  (* Vectors of exponents                                             *)
  (* ---------------------------------------------------------------- *)

  Local Notation vzero m := (Vector.const zero m).
  Local Notation vadd := (Vector.map2 add).
  Local Notation vscale := (fun (v : Vector.t F M) (c : F) => Vector.map (fun x => x * c) v).
  Definition vsub {m} (v w : Vector.t F m) : Vector.t F m := Vector.map2 (fun x y => x + opp y) v w.

  Fixpoint unit_vec {m : nat} (j : Fin.t m) : Vector.t F m :=
    match j with
    | Fin.F1 => one :: vzero _
    | Fin.FS j' => zero :: unit_vec j'
    end.

  Lemma gexp_zeros : forall (m : nat) (gs : Vector.t G m), gexp gs (vzero m) = gid.
  Proof.
    induction m as [| m ih]; intro gs.
    + rewrite (vector_inv_0 gs); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      rewrite const_S, mexp_cons, ih, smul_zero, gid_l; reflexivity.
  Qed.

  Lemma gexp_unit : forall (m : nat) (j : Fin.t m) (gs : Vector.t G m), gexp gs (unit_vec j) = gs[@j].
  Proof.
    intros m j; induction j as [m | m j ih]; intro gs.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      cbn [unit_vec]; rewrite mexp_cons, gexp_zeros, smul_one, gid_r; reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      cbn [unit_vec]; rewrite mexp_cons, ih, smul_zero, gid_l; reflexivity.
  Qed.

  Lemma gexp_exp_add : forall (m : nat) (gs : Vector.t G m) (x y : Vector.t F m),
    gexp gs (vadd x y) = gop (gexp gs x) (gexp gs y).
  Proof.
    induction m as [| m ih]; intros gs x y.
    + rewrite (vector_inv_0 gs), (vector_inv_0 x), (vector_inv_0 y); cbn; rewrite gid_l; reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S x) as (a & x' & ->).
      destruct (vector_inv_S y) as (b & y' & ->).
      rewrite map2_cons, !mexp_cons, ih, smul_fadd.
      rewrite <-!gassoc; f_equal. rewrite !gassoc; f_equal; apply gcomm.
  Qed.

  Lemma gexp_exp_scale : forall (m : nat) (gs : Vector.t G m) (x : Vector.t F m) (c : F),
    gexp gs (Vector.map (fun e => e * c) x) = (gexp gs x) ^ c.
  Proof.
    induction m as [| m ih]; intros gs x c.
    + rewrite (vector_inv_0 gs), (vector_inv_0 x); cbn; rewrite gid_pow; reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S x) as (a & x' & ->).
      cbn [Vector.map]; rewrite !mexp_cons, ih, smul_vadd, smul_fmul; reflexivity.
  Qed.

  (* group helpers *)
  Lemma inv_unique : forall a b : G, gop a b = gid -> b = ginv a.
  Proof.
    intros a b h.
    rewrite <-(gid_l b), <-(ginv_l a), <-gassoc, h, gid_r; reflexivity.
  Qed.

  Lemma gop4 : forall a b c d : G, gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
  Proof.
    intros. rewrite <-!gassoc; f_equal. rewrite !gassoc; f_equal; apply gcomm.
  Qed.

  Lemma ginv_gop : forall a b : G, ginv (gop a b) = gop (ginv a) (ginv b).
  Proof.
    intros; symmetry; apply inv_unique.
    rewrite gop4, !ginv_r, gid_l; reflexivity.
  Qed.

  Lemma pow_opp_one : forall z : G, z ^ (opp one) = ginv z.
  Proof.
    intro z; apply inv_unique.
    assert (h : gop (z ^ one) (z ^ opp one) = gid).
    { rewrite <-smul_fadd. replace (one + opp one) with zero by field. apply smul_zero. }
    rewrite smul_one in h; exact h.
  Qed.

  Lemma pow_opp : forall (z : G) (r : F), z ^ (opp r) = ginv (z ^ r).
  Proof.
    intros; rewrite <-pow_opp_one, <-smul_fmul; f_equal; field.
  Qed.

  Lemma gexp_exp_sub : forall (m : nat) (gs : Vector.t G m) (x y : Vector.t F m),
    gexp gs (vsub x y) = gop (gexp gs x) (ginv (gexp gs y)).
  Proof.
    intros; unfold vsub.
    replace (Vector.map2 (fun a b => a + opp b) x y) with (vadd x (Vector.map (fun e => e * opp one) y)).
    + rewrite gexp_exp_add, gexp_exp_scale, pow_opp_one; reflexivity.
    + apply Vector.eq_nth_iff; intros i j <-.
      rewrite !(Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), (Vector.nth_map _ _ i i eq_refl).
      f_equal; field.
  Qed.

  Lemma gprod_ones : forall (m : nat) (gs : Vector.t G m), gexp gs (Vector.const one m) = gprod gs.
  Proof.
    induction m as [| m ih]; intro gs.
    + rewrite (vector_inv_0 gs); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      rewrite const_S, mexp_cons, ih, smul_one; reflexivity.
  Qed.

  (* Mᵀ e = Σ_j e_j m_j, for a matrix given by its rows *)
  Definition matT_mul {m : nat} (mat : Vector.t (Vector.t F M) m) (e : Vector.t F m) : Vector.t F M :=
    Vector.fold_right (fun '(row, ej) acc => vadd (Vector.map (fun x => x * ej) row) acc)
      (Vector.map2 pair mat e) (vzero M).

  Definition colsum {m : nat} (mat : Vector.t (Vector.t F M) m) : Vector.t F M := matT_mul mat (Vector.const one m).

  (* the product of the openings of the commitments *)
  Definition open (g : G) (hs : Vector.t G M) {m : nat} (as' : Vector.t F m) (mat : Vector.t (Vector.t F M) m) : Vector.t G m :=
    Vector.map2 (fun a row => gop (g ^ a) (gexp hs row)) as' mat.

  Lemma gexp_open : forall (g : G) (hs : Vector.t G M) (m : nat) (as' : Vector.t F m)
    (mat : Vector.t (Vector.t F M) m) (e : Vector.t F m),
    gexp (open g hs as' mat) e = gop (g ^ inner as' e) (gexp hs (matT_mul mat e)).
  Proof.
    intros g hs m; induction m as [| m ih]; intros as' mat e.
    + rewrite (vector_inv_0 as'), (vector_inv_0 mat), (vector_inv_0 e).
      unfold open, matT_mul, inner, fsum; cbn. rewrite gexp_zeros, smul_zero, gid_l; reflexivity.
    + destruct (vector_inv_S as') as (a & as1 & ->).
      destruct (vector_inv_S mat) as (row & mat' & ->).
      destruct (vector_inv_S e) as (ej & e' & ->).
      unfold open, matT_mul, inner, fsum in *; rewrite !map2_cons, mexp_cons.
      cbn [Vector.fold_right]. rewrite ih, gexp_exp_add, gexp_exp_scale, smul_vadd, smul_fadd, smul_fmul.
      rewrite <-!gassoc; f_equal. rewrite !gassoc; f_equal; apply gcomm.
  Qed.

  Lemma gprod_open : forall (g : G) (hs : Vector.t G M) (m : nat) (as' : Vector.t F m) (mat : Vector.t (Vector.t F M) m),
    gprod (open g hs as' mat) = gop (g ^ fsum as') (gexp hs (colsum mat)).
  Proof.
    intros. rewrite <-gprod_ones, gexp_open. unfold colsum. f_equal. f_equal.
    unfold inner. f_equal. apply Vector.eq_nth_iff; intros i j <-.
    rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), Vector.const_nth; field.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Discrete-logarithm relations                                      *)
  (* ---------------------------------------------------------------- *)

  (* g^{x_0} ∏ h_i^{x_i} = 1 *)
  Definition dl_rel (g : G) (hs : Vector.t G M) (x0 : F) (xs : Vector.t F M) : Prop :=
    gop (g ^ x0) (gexp hs xs) = gid.

  Definition trivial (x0 : F) (xs : Vector.t F M) : Prop := x0 = zero /\ xs = vzero M.

  Lemma trivial_dec : forall x0 xs, {trivial x0 xs} + {~ trivial x0 xs}.
  Proof.
    intros x0 xs; unfold trivial.
    destruct (Fdec x0 zero) as [-> | h]; [| right; intros [e _]; contradiction].
    destruct (vec_dec (V := F) Fdec xs (vzero M)) as [-> | h]; [left; split; reflexivity | right; intros [_ e]; contradiction].
  Qed.

  (* two representations of the same element give a relation *)
  Lemma rel_of_eq : forall g hs x0 xs y0 ys,
    gop (g ^ x0) (gexp hs xs) = gop (g ^ y0) (gexp hs ys) ->
    dl_rel g hs (x0 + opp y0) (vsub xs ys).
  Proof.
    intros * h; unfold dl_rel.
    rewrite gexp_exp_sub, smul_fadd, pow_opp, gop4, <-ginv_gop, h, ginv_r; reflexivity.
  Qed.

  Lemma rel_cases : forall g hs x0 xs, dl_rel g hs x0 xs ->
    (x0 = zero /\ xs = vzero M) \/ (~ (x0 = zero /\ xs = vzero M) /\ dl_rel g hs x0 xs).
  Proof. intros * h; destruct (trivial_dec x0 xs) as [t | t]; [left; exact t | right; split; assumption]. Qed.

  Lemma vsub_zero_r : forall (m : nat) (v : Vector.t F m), vsub v (Vector.const zero m) = v.
  Proof.
    intros; apply Vector.eq_nth_iff; intros i j <-; unfold vsub.
    rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), Vector.const_nth; field.
  Qed.

  Lemma vsub_eq_zero : forall (m : nat) (v w : Vector.t F m), vsub v w = Vector.const zero m -> v = w.
  Proof.
    intros m v w h; apply Vector.eq_nth_iff; intros i j <-.
    apply (f_equal (fun x => x[@i])) in h; unfold vsub in h.
    rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), Vector.const_nth in h.
    replace v[@i] with (v[@i] + opp w[@i] + w[@i]) by field. rewrite h; field.
  Qed.

  Lemma add_opp_eq_zero : forall x y : F, x + opp y = zero -> x = y.
  Proof. intros x y h; replace x with (x + opp y + y) by field; rewrite h; field. Qed.

  (* ---------------------------------------------------------------- *)
  (* The five equations, exploited                                     *)
  (* ---------------------------------------------------------------- *)

  Definition public_of (g : G) (hs : Vector.t G M) (y : G) (us : Vector.t G M) (e : Vector.t F M)
    (Bs : Vector.t G M) (ws ws' : Vector.t (G * G) M) : @public F G N :=
    @ShuffleTW.mk_public F G N g (Vector.hd hs) hs y us e Bs ws ws'.

  Local Notation eqs := (@equations F one mul G gid ginv gop gpow N).

  (* a witness for the unit vector δ_j opens u_j *)
  Lemma opening_from_unit : forall g hs y us Bs ws ws' (j : Fin.t M) a c d f betas e',
    eqs (public_of g hs y us (unit_vec j) Bs ws ws') a c d f betas e' ->
    us[@j] = gop (g ^ a) (gexp hs e').
  Proof.
    intros * [hA _]; unfold public_of in hA; cbn [ShuffleTW.us ShuffleTW.es ShuffleTW.g ShuffleTW.hs] in hA.
    rewrite gexp_unit in hA; exact hA.
  Qed.

  (* with the commitments opened, the A equation at e is a relation *)
  Lemma relation_A : forall g hs y (as' : Vector.t F M) (mat : Vector.t (Vector.t F M) M) e Bs ws ws' a c d f betas e',
    eqs (public_of g hs y (open g hs as' mat) e Bs ws ws') a c d f betas e' ->
    dl_rel g hs (a + opp (inner as' e)) (vsub e' (matT_mul mat e)).
  Proof.
    intros * [hA _]; unfold public_of in hA; cbn [ShuffleTW.us ShuffleTW.es ShuffleTW.g ShuffleTW.hs] in hA.
    rewrite gexp_open in hA. apply rel_of_eq; symmetry; exact hA.
  Qed.

  (* the C equation: the column sums *)
  Lemma relation_C : forall g hs y (as' : Vector.t F M) (mat : Vector.t (Vector.t F M) M) e Bs ws ws' a c d f betas e',
    eqs (public_of g hs y (open g hs as' mat) e Bs ws ws') a c d f betas e' ->
    dl_rel g hs (fsum as' + opp c) (vsub (colsum mat) (Vector.const one M)).
  Proof.
    intros * [_ [hC _]]; unfold public_of in hC; cbn [ShuffleTW.us ShuffleTW.g ShuffleTW.hs] in hC.
    rewrite gprod_open, <-gprod_ones, <-gassoc, <-gexp_exp_sub in hC.
    rewrite <-(vsub_zero_r M (vsub (colsum mat) (Vector.const one M))).
    apply rel_of_eq. rewrite hC, gexp_zeros, gid_r; reflexivity.
  Qed.

  (* the B equations determine the chain *)
  Lemma chain_unique : forall (g : G) (m : nat) (h0 : G) (Bs : Vector.t G m) (betas e' : Vector.t F m),
    Bs = Vector.map2 gop (Vector.map2 gpow (Vector.const g m) betas)
           (Vector.map2 gpow (Vector.shiftout (h0 :: Bs)) e') ->
    Bs = chain g h0 betas e'.
  Proof.
    intros g m; induction m as [| m ih]; intros h0 Bs betas e' h.
    + rewrite (vector_inv_0 Bs), (vector_inv_0 betas), (vector_inv_0 e'); reflexivity.
    + destruct (vector_inv_S Bs) as (B0 & Bs' & ->).
      destruct (vector_inv_S betas) as (b & betas' & ->).
      destruct (vector_inv_S e') as (e0 & e'' & ->).
      rewrite const_S, shiftout_cons, !map2_cons in h.
      apply Vector.cons_inj in h; destruct h as [hB0 hBs].
      cbn [chain Vector.hd Vector.tl Vector.caseS].
      rewrite <-hB0. f_equal. apply ih; exact hBs.
  Qed.

  Lemma nth_hd : forall (m : nat) (v : Vector.t G (S m)), v[@Fin.F1] = Vector.hd v.
  Proof. intros m v; destruct (vector_inv_S v) as (a & v' & ->); reflexivity. Qed.

  (* the D equation: the product of the e' equals the product of the e *)
  Lemma relation_D : forall g hs y us e Bs ws ws' a c d f betas e',
    eqs (public_of g hs y us e Bs ws ws') a c d f betas e' ->
    dl_rel g hs (chain_exp (zero := zero) (one := one) (add := add) (mul := mul) betas e' + opp d)
      (Vector.map (fun x => x * (fprod e' + opp (fprod e))) (unit_vec Fin.F1)).
  Proof.
    intros * [_ [_ [hD [hB _]]]]; unfold public_of in *.
    cbn [ShuffleTW.g ShuffleTW.h0 ShuffleTW.hs ShuffleTW.es ShuffleTW.Bs] in hD, hB.
    unfold Bprev in hB; cbn [ShuffleTW.h0 ShuffleTW.Bs] in hB.
    apply chain_unique in hB. rewrite hB, (chain_last (Hvec := Hvec)) in hD.
    rewrite <-(vsub_zero_r M (Vector.map _ (unit_vec Fin.F1))).
    apply rel_of_eq.
    rewrite gexp_exp_scale, gexp_unit, nth_hd, gexp_zeros, gid_r, <-hD.
    rewrite smul_fadd, pow_opp, gassoc; reflexivity.
  Qed.

  (* the F equation at δ_j: w_j = Enc(1; −f) ∏_i w'_i^{e'_i} *)
  Lemma relation_F : forall g hs y us Bs ws ws' (j : Fin.t M) a c d f betas e',
    eqs (public_of g hs y us (unit_vec j) Bs ws ws') a c d f betas e' ->
    ws[@j] = (gop ((ginv g) ^ f) (gexp (Vector.map fst ws') e'), gop ((ginv y) ^ f) (gexp (Vector.map snd ws') e')).
  Proof.
    intros * [_ [_ [_ [_ hF]]]]; unfold public_of in hF.
    cbn [ShuffleTW.g ShuffleTW.pk ShuffleTW.es ShuffleTW.ws ShuffleTW.ws'] in hF.
    rewrite cexp_components, !gexp_unit, !(Vector.nth_map _ _ j j eq_refl) in hF.
    rewrite <-hF; destruct (ws[@j]); reflexivity.
  Qed.

  (* the consequences when the relations are trivial *)
  Lemma relation_A_trivial : forall (as' : Vector.t F M) (mat : Vector.t (Vector.t F M) M) e a e',
    a + opp (inner as' e) = zero -> vsub e' (matT_mul mat e) = vzero M ->
    a = inner as' e /\ e' = matT_mul mat e.
  Proof. intros * h1 h2; split; [apply add_opp_eq_zero; exact h1 | apply vsub_eq_zero; exact h2]. Qed.

  Lemma relation_C_trivial : forall (mat : Vector.t (Vector.t F M) M),
    vsub (colsum mat) (Vector.const one M) = vzero M -> colsum mat = Vector.const one M.
  Proof. intros * h; apply vsub_eq_zero; exact h. Qed.

  Lemma relation_D_trivial : forall (e e' : Vector.t F M),
    Vector.map (fun x => x * (fprod e' + opp (fprod e))) (unit_vec Fin.F1) = vzero M -> fprod e' = fprod e.
  Proof.
    intros e e' h. apply (f_equal (fun v => v[@Fin.F1])) in h.
    rewrite (Vector.nth_map _ _ Fin.F1 Fin.F1 eq_refl), Vector.const_nth in h.
    cbn [unit_vec Vector.nth] in h.
    apply add_opp_eq_zero. rewrite <-h; field.
  Qed.

End Sound.
