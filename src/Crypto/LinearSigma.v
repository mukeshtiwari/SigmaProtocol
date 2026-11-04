(* A Σ-protocol for the preimage of a linear map: the prover knows a
   witness w ∈ F^W with φ(w) = T, for a map φ from lists of scalars of
   length W to a vector space V over F that is additive and homogeneous
   (φ(w + w') = φ(w) + φ(w'), φ(c·w) = c·φ(w)). The prover draws a uniform
   a ∈ F^W, announces φ(a), receives c, and answers z = a + c·w; the
   verifier checks φ(z) = φ(a) + c·T. This is the generalised Okamoto
   protocol with the bases replaced by an arbitrary linear map, so that an
   instance may mix group equations (V = G^k, φ a multi-exponentiation) and
   scalar equations (V = F^k, φ an inner product) in one product space
   (Algebra/Product_space.v), which is the shape of the linear-relation
   proof of the batched Schulze ballot (Frontend/SchulzeBatched.v).
   Completeness, special soundness (the witness (z − z')/(c − c') from two
   accepting transcripts with the same announcement) and perfect special
   honest-verifier zero-knowledge (the simulator draws z and solves for
   the announcement; the shift a ↦ a + c·w is a bijection of F^W). *)

From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Crypto Require Import SigmaK BayerGrothZK.
From Probability Require Import Prob Distr.
Import ListNotations.

Section LinearSigma.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {Vdec : forall x y : V, {x = y} + {x <> y}}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation lscale := (lscale (mul := mul)).
  Local Notation ladd := (ladd (add := add)).

  (* the vector-space laws as explicit terms *)
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
  Local Notation vinv_l := (@left_inverse V (@eq V) vadd vid vopp
    (@group_is_left_inverse V (@eq V) vadd vid vopp vgroup)).
  Local Notation vinv_r := (@right_inverse V (@eq V) vadd vid vopp
    (@group_is_right_inverse V (@eq V) vadd vid vopp vgroup)).
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

  Lemma smul_add : forall (v : V) (r s : F), smul v (r + s) = vadd (smul v r) (smul v s).
  Proof. intros; apply vfadd. Qed.
  Lemma smul_mul : forall (v : V) (r s : F), smul v (r * s) = smul (smul v r) s.
  Proof. intros; apply vfmul. Qed.
  Lemma vadd_smul : forall (u v : V) (r : F), smul (vadd u v) r = vadd (smul u r) (smul v r).
  Proof. intros; apply vvadd. Qed.
  Lemma smul_one : forall v : V, smul v one = v.
  Proof. intros; apply vone. Qed.
  Lemma smul_zero : forall v : V, smul v zero = vid.
  Proof. intros; apply vzero. Qed.

  (* a + (b + (-b)) = a and friends *)
  Lemma vadd_cancel_r : forall a b : V, vadd (vadd a b) (vopp b) = a.
  Proof. intros; rewrite <-vassoc, vinv_r, vid_r; reflexivity. Qed.
  Lemma vadd_cancel_opp_r : forall a b : V, vadd (vadd a (vopp b)) b = a.
  Proof. intros; rewrite <-vassoc, vinv_l, vid_r; reflexivity. Qed.
  Lemma vinv_unique : forall x y : V, vadd x y = vid -> vopp x = y.
  Proof.
    intros x y h.
    rewrite <-(vid_r (vopp x)), <-h, vassoc, vinv_l, vid_l; reflexivity.
  Qed.
  Lemma vadd4 : forall a b c d : V, vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d).
  Proof.
    intros a b c d.
    rewrite <-(vassoc a b (vadd c d)), (vassoc b c d), (vcomm b c), <-(vassoc c b d),
      (vassoc a c (vadd b d)); reflexivity.
  Qed.
  Lemma vopp_vadd : forall a b : V, vopp (vadd a b) = vadd (vopp a) (vopp b).
  Proof.
    intros a b; apply vinv_unique.
    rewrite vadd4, vinv_r, vinv_r, vid_l; reflexivity.
  Qed.
  Lemma smul_opp : forall (v : V) (r : F), smul v (opp r) = vopp (smul v r).
  Proof.
    intros v r; symmetry; apply vinv_unique.
    rewrite <-smul_add. replace (r + opp r) with zero by field. apply smul_zero.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* list helpers                                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma lscale_length : forall c xs, length (lscale c xs) = length xs.
  Proof. intros; unfold SigmaK.lscale; apply map_length. Qed.
  Lemma ladd_length : forall xs ys, length xs = length ys -> length (ladd xs ys) = length xs.
  Proof. intros; unfold SigmaK.ladd; rewrite map_length, combine_length; lia. Qed.
  Lemma nth_lscale : forall c xs i, (i < length xs)%nat -> nth i (lscale c xs) zero = c * nth i xs zero.
  Proof.
    intros c xs; induction xs as [| x xs ih]; intros i hi; [cbn in hi; lia |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.lscale map nth]; apply ih; cbn in hi; lia].
  Qed.
  Lemma nth_ladd : forall xs ys i, length xs = length ys -> (i < length xs)%nat ->
    nth i (ladd xs ys) zero = nth i xs zero + nth i ys zero.
  Proof.
    induction xs as [| x xs ih]; intros ys i hl hi; [cbn in hi; lia |].
    destruct ys as [| y ys]; [discriminate |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.ladd combine map nth fst snd]; apply ih; cbn in *; lia].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the protocol                                                       *)
  (* ---------------------------------------------------------------- *)

  Variable W : nat.
  Variable phi : list F -> V.
  Hypothesis phi_add : forall w w', length w = W -> length w' = W ->
    phi (ladd w w') = vadd (phi w) (phi w').
  Hypothesis phi_scale : forall c w, length w = W -> phi (lscale c w) = smul (phi w) c.

  Record lin_proof : Type := mk_lin { lin_a : V; lin_z : list F }.

  (* statement T, challenge c *)
  Definition lin_verify (T : V) (c : F) (pf : lin_proof) : bool :=
    (Nat.eqb (length (lin_z pf)) W) &&
    (if Vdec (phi (lin_z pf)) (vadd (lin_a pf) (smul T c)) then true else false).

  (* the honest prover with randomness a *)
  Definition lin_prove (w a : list F) (c : F) : lin_proof := mk_lin (phi a) (ladd a (lscale c w)).

  (* the simulator with randomness z *)
  Definition lin_sim (T : V) (c : F) (z : list F) : lin_proof :=
    mk_lin (vadd (phi z) (vopp (smul T c))) z.

  Theorem lin_completeness : forall (w a : list F) (c : F), length w = W -> length a = W ->
    lin_verify (phi w) c (lin_prove w a c) = true.
  Proof.
    intros w a c hw ha; unfold lin_verify, lin_prove; cbn [lin_a lin_z].
    apply andb_true_iff; split.
    + apply Nat.eqb_eq; rewrite ladd_length; [exact ha | rewrite lscale_length; lia].
    + destruct (Vdec _ _) as [_ | hne]; [reflexivity | exfalso; apply hne].
      rewrite phi_add; [| exact ha | rewrite lscale_length; exact hw].
      rewrite phi_scale by exact hw; reflexivity.
  Qed.

  Theorem lin_sim_accepting : forall (T : V) (c : F) (z : list F), length z = W ->
    lin_verify T c (lin_sim T c z) = true.
  Proof.
    intros T c z hz; unfold lin_verify, lin_sim; cbn [lin_a lin_z].
    apply andb_true_iff; split; [apply Nat.eqb_eq; exact hz |].
    destruct (Vdec _ _) as [_ | hne]; [reflexivity | exfalso; apply hne].
    rewrite vadd_cancel_opp_r; reflexivity.
  Qed.

  (* the extracted witness *)
  Definition lin_extract (c c' : F) (z z' : list F) : list F :=
    lscale (inv (c - c')) (ladd z (lscale (opp one) z')).

  Theorem lin_soundness : forall (T A : V) (c c' : F) (z z' : list F),
    c <> c' ->
    lin_verify T c (mk_lin A z) = true -> lin_verify T c' (mk_lin A z') = true ->
    length (lin_extract c c' z z') = W /\ phi (lin_extract c c' z z') = T.
  Proof.
    intros T A c c' z z' hc hv hv'.
    unfold lin_verify in hv, hv'; cbn [lin_a lin_z] in hv, hv'.
    apply andb_true_iff in hv; destruct hv as (hz & hv).
    apply andb_true_iff in hv'; destruct hv' as (hz' & hv').
    apply Nat.eqb_eq in hz, hz'.
    destruct (Vdec (phi z) _) as [e | ne]; [| discriminate].
    destruct (Vdec (phi z') _) as [e' | ne']; [| discriminate].
    assert (hl : length (ladd z (lscale (opp one) z')) = W)
      by (rewrite ladd_length; [exact hz | rewrite lscale_length; lia]).
    split; [unfold lin_extract; rewrite lscale_length; exact hl |].
    unfold lin_extract.
    rewrite phi_scale by exact hl.
    rewrite phi_add; [| exact hz | rewrite lscale_length; exact hz'].
    rewrite phi_scale by exact hz'.
    rewrite e, e', smul_opp, smul_one.
    (* (A + cT) − (A + c'T) = (c − c') T *)
    assert (hd : vadd (vadd A (smul T c)) (vopp (vadd A (smul T c'))) = smul T (c - c')).
    { rewrite vopp_vadd, vadd4, vinv_r, vid_l, <-smul_opp, <-smul_add.
      f_equal; field. }
    rewrite hd, <-smul_mul.
    replace ((c - c') * inv (c - c')) with one; [apply smul_one |].
    field; apply sub_neq_zero; exact hc.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* zero-knowledge                                                     *)
  (* ---------------------------------------------------------------- *)

  Local Notation rand := (rand (F := F)).

  Definition lin_real_distribution (lf : list F) (Hlfn : lf <> []) (w : list F) (c : F) : dist lin_proof :=
    Bind (rand lf Hlfn W) (fun a => Ret (lin_prove w a c)).
  Definition lin_sim_distribution (lf : list F) (Hlfn : lf <> []) (T : V) (c : F) : dist lin_proof :=
    Bind (rand lf Hlfn W) (fun z => Ret (lin_sim T c z)).

  Definition lin_phi (w : list F) (c : F) (a : list F) : list F := ladd a (lscale c w).
  Definition lin_psi (w : list F) (c : F) (z : list F) : list F := ladd z (lscale (opp c) w).

  Lemma lin_phi_length : forall w c a, length w = W -> length a = W -> length (lin_phi w c a) = W.
  Proof. intros; unfold lin_phi; rewrite ladd_length; [assumption | rewrite lscale_length; lia]. Qed.
  Lemma lin_psi_length : forall w c z, length w = W -> length z = W -> length (lin_psi w c z) = W.
  Proof. intros; unfold lin_psi; rewrite ladd_length; [assumption | rewrite lscale_length; lia]. Qed.

  Lemma lin_psi_phi : forall w c a, length w = W -> length a = W -> lin_psi w c (lin_phi w c a) = a.
  Proof.
    intros w c a hw ha; unfold lin_psi, lin_phi.
    assert (hl1 : length (lscale c w) = W) by (rewrite lscale_length; exact hw).
    assert (hl2 : length (ladd a (lscale c w)) = W) by (rewrite ladd_length; lia).
    assert (hl3 : length (lscale (opp c) w) = W) by (rewrite lscale_length; exact hw).
    apply (nth_ext _ _ zero zero).
    + rewrite ladd_length; lia.
    + intros i hi; rewrite ladd_length in hi by lia.
      rewrite nth_ladd by lia; rewrite nth_ladd by lia; rewrite !nth_lscale by lia; field.
  Qed.

  Lemma lin_phi_psi : forall w c z, length w = W -> length z = W -> lin_phi w c (lin_psi w c z) = z.
  Proof.
    intros w c z hw hz; unfold lin_psi, lin_phi.
    assert (hl1 : length (lscale (opp c) w) = W) by (rewrite lscale_length; exact hw).
    assert (hl2 : length (ladd z (lscale (opp c) w)) = W) by (rewrite ladd_length; lia).
    assert (hl3 : length (lscale c w) = W) by (rewrite lscale_length; exact hw).
    apply (nth_ext _ _ zero zero).
    + rewrite ladd_length; lia.
    + intros i hi; rewrite ladd_length in hi by lia.
      rewrite nth_ladd by lia; rewrite nth_ladd by lia; rewrite !nth_lscale by lia; field.
  Qed.

  Lemma lin_prove_eq_sim : forall w c a, length w = W -> length a = W ->
    lin_prove w a c = lin_sim (phi w) c (lin_phi w c a).
  Proof.
    intros w c a hw ha; unfold lin_prove, lin_sim, lin_phi; f_equal.
    rewrite phi_add; [| exact ha | rewrite lscale_length; exact hw].
    rewrite phi_scale by exact hw.
    rewrite vadd_cancel_r; reflexivity.
  Qed.

  Theorem lin_shvzk : forall (lf : list F) (Hlfn : lf <> []) (w : list F) (c : F),
    length w = W -> NoDup lf -> (forall v : F, In v lf) ->
    Permutation (lin_real_distribution lf Hlfn w c) (lin_sim_distribution lf Hlfn (phi w) c).
  Proof.
    intros lf Hlfn w c hw hnd hall; unfold lin_real_distribution, lin_sim_distribution.
    apply (zk_of_bijection (zero := zero) lf Hlfn W (fun a => lin_prove w a c) (lin_sim (phi w) c)
      (lin_phi w c) (lin_psi w c) hnd hall).
    + intros l hl; apply lin_phi_length; assumption.
    + intros l hl; apply lin_psi_length; assumption.
    + intros l hl; apply lin_psi_phi; assumption.
    + intros l hl; apply lin_phi_psi; assumption.
    + intros l hl; apply lin_prove_eq_sim; assumption.
  Qed.

End LinearSigma.
