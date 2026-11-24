(** * A Sigma protocol for preimages of a linear map *)

(** This file defines and verifies the generic ‘linear relation’ Sigma
    protocol (sometimes called the Maurer or homomorphism-preimage
    protocol). Fix a length [W] and a map [phi] from lists of [W] scalars
    to an [F]-vector space [V] that is additive and homogeneous on lists of
    length [W]:

    [[
      phi (w + w') = phi w + phi w',     phi (c · w) = c · phi w.
    ]]

    The prover knows a witness [w ∈ F^W] with [phi w = T].

    - Announcement: for uniform [a ∈ F^W], send [A = phi a].
    - Challenge: [c ∈ F].
    - Response: [z = a + c · w].
    - Verification ([lin_verify]): [|z| = W] and [phi z = A + c · T].

    Mathematically, Schnorr, Okamoto, Chaum–Pedersen and their conjunctions
    are all special cases (this file does not derive them): [V] can be a power of the group [G] with [phi] a
    multi-exponentiation, a power of [F] with [phi] an inner product, or a
    product space mixing both (see [Algebra/Product_space.v]). The batched
    Schulze ballot ([Frontend/SchulzeBatched.v]) and the simplified Schulze
    ballot ([Frontend/SchulzeSimple.v]) use exactly such a mixed instance.

    _Results._

    - Completeness [lin_completeness].
    - Simulator completeness [lin_sim_accepting].
    - Special soundness [lin_soundness]: two accepting transcripts with the
      same announcement and challenges [c ≠ c'] give the explicit witness
      [(z - z') / (c - c')] of length [W] with [phi] of it equal to [T].
    - Perfect special HVZK [lin_shvzk]: when the scalars are drawn
      uniformly from a duplicate-free list [lf] enumerating all of [F], the
      real and simulated transcript distributions are permutations of each
      other. The proof uses the bijection [a ↦ a + c · w] of [F^W] and the
      generic lemma [BayerGrothZK.zk_of_bijection].

    Note that [Vdec] (decidable equality on [V]) is needed only to make the
    verifier boolean. *)
From Stdlib Require Import Utf8 List Lia Bool setoid_ring.Field Permutation PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Sigma Require Import SigmaK BayerGrothZK.
From Probability Require Import Prob Distr.
Import ListNotations.

(** ** The linear-relation protocol *)
Section LinearSigma.

  (** A field [F] with decidable equality and an [F]-vector space [V] (zero
      [vid], negation [vopp], addition [vadd], scalar multiplication
      [smul]) with decidable equality [Vdec]. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {Vdec : forall x y : V, {x = y} + {x <> y}}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  (** Registers [F] with the [field] tactic. *)
  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  (** Local notations: field infixes, and [SigmaK]'s list scaling
      [lscale] and pointwise addition [ladd] specialised to [F]. *)
  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.
  Local Notation lscale := (lscale (mul := mul)).
  Local Notation ladd := (ladd (add := add)).

  (** Projections of the individual vector-space axioms out of [HV]. *)
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

  (** *** Vector-space and list helpers

      [smul_add], [smul_mul], [vadd_smul], [smul_one], [smul_zero]: the
      vector-space axioms in named form. *)
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

  (** Cancellation: [(a + b) - b = a] ([vadd_cancel_r]) and
      [(a - b) + b = a] ([vadd_cancel_opp_r]). *)
  Lemma vadd_cancel_r : forall a b : V, vadd (vadd a b) (vopp b) = a.
  Proof. intros; rewrite <-vassoc, vinv_r, vid_r; reflexivity. Qed.
  Lemma vadd_cancel_opp_r : forall a b : V, vadd (vadd a (vopp b)) b = a.
  Proof. intros; rewrite <-vassoc, vinv_l, vid_r; reflexivity. Qed.
  (** Uniqueness of additive inverses: [x + y = 0] implies [-x = y]. *)
  Lemma vinv_unique : forall x y : V, vadd x y = vid -> vopp x = y.
  Proof.
    intros x y h.
    rewrite <-(vid_r (vopp x)), <-h, vassoc, vinv_l, vid_l; reflexivity.
  Qed.
  (** Middle-four interchange for the commutative addition of [V]. *)
  Lemma vadd4 : forall a b c d : V, vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d).
  Proof.
    intros a b c d.
    rewrite <-(vassoc a b (vadd c d)), (vassoc b c d), (vcomm b c), <-(vassoc c b d),
      (vassoc a c (vadd b d)); reflexivity.
  Qed.
  (** Negation distributes over addition. *)
  Lemma vopp_vadd : forall a b : V, vopp (vadd a b) = vadd (vopp a) (vopp b).
  Proof.
    intros a b; apply vinv_unique.
    rewrite vadd4, vinv_r, vinv_r, vid_l; reflexivity.
  Qed.
  (** Scalar negation: [smul v (-r) = - smul v r]. *)
  Lemma smul_opp : forall (v : V) (r : F), smul v (opp r) = vopp (smul v r).
  Proof.
    intros v r; symmetry; apply vinv_unique.
    rewrite <-smul_add. replace (r + opp r) with zero by field. apply smul_zero.
  Qed.

  (** [lscale] preserves length. *)
  Lemma lscale_length : forall c xs, length (lscale c xs) = length xs.
  Proof. intros; unfold SigmaK.lscale; apply map_length. Qed.
  (** [ladd] of two equal-length lists has that length. *)
  Lemma ladd_length : forall xs ys, length xs = length ys -> length (ladd xs ys) = length xs.
  Proof. intros; unfold SigmaK.ladd; rewrite map_length, combine_length; lia. Qed.
  (** Indexing commutes with [lscale] within bounds. *)
  Lemma nth_lscale : forall c xs i, (i < length xs)%nat -> nth i (lscale c xs) zero = c * nth i xs zero.
  Proof.
    intros c xs; induction xs as [| x xs ih]; intros i hi; [cbn in hi; lia |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.lscale map nth]; apply ih; cbn in hi; lia].
  Qed.
  (** Indexing commutes with [ladd] within bounds, for equal-length
      lists. *)
  Lemma nth_ladd : forall xs ys i, length xs = length ys -> (i < length xs)%nat ->
    nth i (ladd xs ys) zero = nth i xs zero + nth i ys zero.
  Proof.
    induction xs as [| x xs ih]; intros ys i hl hi; [cbn in hi; lia |].
    destruct ys as [| y ys]; [discriminate |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.ladd combine map nth fst snd]; apply ih; cbn in *; lia].
  Qed.

  (** *** The protocol

      The section variables fix the witness length [W] and the linear map
      [phi]; linearity is assumed only for arguments of length [W]. *)
  Variable W : nat.
  Variable phi : list F -> V.
  Hypothesis phi_add : forall w w', length w = W -> length w' = W ->
    phi (ladd w w') = vadd (phi w) (phi w').
  Hypothesis phi_scale : forall c w, length w = W -> phi (lscale c w) = smul (phi w) c.

  (** A transcript without the challenge: announcement [lin_a] in [V] and
      response [lin_z], a list of scalars. *)
  Record lin_proof : Type := mk_lin { lin_a : V; lin_z : list F }.

  (** Verifier for statement [T] and challenge [c]: accepts iff the
      response has length [W] and [phi z = A + c · T]. *)
  Definition lin_verify (T : V) (c : F) (pf : lin_proof) : bool :=
    (Nat.eqb (length (lin_z pf)) W) &&
    (if Vdec (phi (lin_z pf)) (vadd (lin_a pf) (smul T c)) then true else false).

  (** Honest prover with witness [w], randomness [a] and challenge [c]:
      announcement [phi a], response [a + c · w]. *)
  Definition lin_prove (w a : list F) (c : F) : lin_proof := mk_lin (phi a) (ladd a (lscale c w)).

  (** Simulator for statement [T] and challenge [c] with random response
      [z]: announcement [phi z - c · T], response [z]. *)
  Definition lin_sim (T : V) (c : F) (z : list F) : lin_proof :=
    mk_lin (vadd (phi z) (vopp (smul T c))) z.

  (** _Completeness._ For [|w| = |a| = W], the honest transcript is
      accepted for the statement [phi w] and every challenge [c]:
      [phi (a + c · w) = phi a + c · phi w] by linearity. *)
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

  (** _Simulator completeness._ For every statement [T], challenge [c] and
      response [z] of length [W], the simulated transcript is accepted. *)
  Theorem lin_sim_accepting : forall (T : V) (c : F) (z : list F), length z = W ->
    lin_verify T c (lin_sim T c z) = true.
  Proof.
    intros T c z hz; unfold lin_verify, lin_sim; cbn [lin_a lin_z].
    apply andb_true_iff; split; [apply Nat.eqb_eq; exact hz |].
    destruct (Vdec _ _) as [_ | hne]; [reflexivity | exfalso; apply hne].
    rewrite vadd_cancel_opp_r; reflexivity.
  Qed.

  (** The knowledge extractor: [(z - z') · (c - c')⁻¹], computed as
      [lscale (inv (c - c')) (ladd z (lscale (-1) z'))]. *)
  Definition lin_extract (c c' : F) (z z' : list F) : list F :=
    lscale (inv (c - c')) (ladd z (lscale (opp one) z')).

  (** _Special soundness._ If [(A; c; z)] and [(A; c'; z')] are accepting
      for statement [T] with [c ≠ c'], then [lin_extract c c' z z'] has
      length [W] and maps to [T] under [phi]. Proof: by linearity,
      [phi (z - z') = (A + c · T) - (A + c' · T) = (c - c') · T]; scale by
      [(c - c')⁻¹]. *)
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
    (* The key identity: (A + c·T) - (A + c'·T) = (c - c')·T. *)
    assert (hd : vadd (vadd A (smul T c)) (vopp (vadd A (smul T c'))) = smul T (c - c')).
    { rewrite vopp_vadd, vadd4, vinv_r, vid_l, <-smul_opp, <-smul_add.
      f_equal; field. }
    rewrite hd, <-smul_mul.
    replace ((c - c') * inv (c - c')) with one; [apply smul_one |].
    field; apply sub_neq_zero; exact hc.
  Qed.

  (** *** Zero knowledge *)

  (** [rand lf _ W] (from [BayerGrothZK]) is the distribution of lists of
      [W] independent uniform draws from [lf]. *)
  Local Notation rand := (rand (F := F)).

  (** Real transcript distribution: uniform [a] of length [W], then the
      honest prover with witness [w] and challenge [c]. *)
  Definition lin_real_distribution (lf : list F) (Hlfn : lf <> []) (w : list F) (c : F) : dist lin_proof :=
    Bind (rand lf Hlfn W) (fun a => Ret (lin_prove w a c)).
  (** Simulated transcript distribution: uniform response [z] of length
      [W], then the simulator for statement [T] and challenge [c]. *)
  Definition lin_sim_distribution (lf : list F) (Hlfn : lf <> []) (T : V) (c : F) : dist lin_proof :=
    Bind (rand lf Hlfn W) (fun z => Ret (lin_sim T c z)).

  (** The randomness bijection used for HVZK: [lin_phi w c a = a + c · w]
      maps the prover's randomness to its response, with inverse
      [lin_psi w c z = z - c · w]. *)
  Definition lin_phi (w : list F) (c : F) (a : list F) : list F := ladd a (lscale c w).
  Definition lin_psi (w : list F) (c : F) (z : list F) : list F := ladd z (lscale (opp c) w).

  (** [lin_phi] and [lin_psi] preserve length [W]. *)
  Lemma lin_phi_length : forall w c a, length w = W -> length a = W -> length (lin_phi w c a) = W.
  Proof. intros; unfold lin_phi; rewrite ladd_length; [assumption | rewrite lscale_length; lia]. Qed.
  Lemma lin_psi_length : forall w c z, length w = W -> length z = W -> length (lin_psi w c z) = W.
  Proof. intros; unfold lin_psi; rewrite ladd_length; [assumption | rewrite lscale_length; lia]. Qed.

  (** [lin_psi] is a left inverse of [lin_phi] on lists of length [W]. *)
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

  (** [lin_psi] is a right inverse of [lin_phi] on lists of length [W]. *)
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

  (** The honest transcript with randomness [a] equals the simulated
      transcript (for statement [phi w]) with response [a + c · w]. *)
  Lemma lin_prove_eq_sim : forall w c a, length w = W -> length a = W ->
    lin_prove w a c = lin_sim (phi w) c (lin_phi w c a).
  Proof.
    intros w c a hw ha; unfold lin_prove, lin_sim, lin_phi; f_equal.
    rewrite phi_add; [| exact ha | rewrite lscale_length; exact hw].
    rewrite phi_scale by exact hw.
    rewrite vadd_cancel_r; reflexivity.
  Qed.

  (** _Perfect special HVZK._ If [|w| = W] and [lf] enumerates [F] without
      duplicates, then for every challenge [c] the real distribution and the
      simulated distribution for statement [phi w] are permutations of each
      other, i.e. equal as distributions. Proof: [zk_of_bijection] with the
      bijection [lin_phi w c] and [lin_prove_eq_sim]. *)
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
