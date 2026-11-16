(* BBS# (Desmoulins, Dumanois, Kane, Traoré, "Making BBS Anonymous
   Credentials eIDAS 2.0 Compliant", ePrint 2025/619, Sections 2.7, 3.3, 4,
   5.1 and Appendices B–D), built from the library's protocols.

   The credential is the pairing-free algebraic MAC MAC_BBS: with public
   generators g, g̃, g_0, g_1..g_n of a group of prime order p, the Issuer's
   key x (pk_I = g̃^x), the holder's key pk = g^{sk} and attributes m_i,

     Cm = g_0 · pk · ∏ g_i^{m_i},     A = Cm^{1/(x+e)},     σ = (A, e),

   and B = Cm · A^{−e} = A^x. To present the credential the holder blinds
   the key, pk_Blind = g^{sk+r}, and randomises the MAC with r_1, r_2:

     Ā = A^{r_1 r_2},   D = Cm^{r_2},   B̄ = Ā^{−e} D^{r_1} = Ā^x,   r_3 = r_2^{−1},

   and proves (Figure 8 of the paper) knowledge of (−e, r_1, r_3, r, {−m_i}_{i∉D})
   with

     B̄ = Ā^{−e} D^{r_1}    and    g_0 · pk_Blind · ∏_{i∈D} g_i^{m_i} = D^{r_3} g^{r} ∏_{i∉D} g_i^{−m_i},

   two linear equations over one witness vector with one challenge: one
   Okamoto statement in G² (Crypto/OkamotoRows.v). Holder binding is the
   Schnorr proof of knowledge of the discrete logarithm of pk_Blind
   (Figure 7, an ECSDSA signature), and the pairing-free replacement of the
   BBS pairing check is the Chaum–Pedersen proof π_DLEQ of B̄ = Ā^x ∧
   pk_I = g̃^x (Figure 6), produced by the Issuer online (Option 1) or as a
   blind proof through Orrù et al.'s oblivious issuance (Options 2 and 3);
   in all three cases the verifier checks the same Chaum–Pedersen
   transcript with the Issuer's public key.

   This file has the algebra of the MAC and of its randomisation, the three
   proofs as library instances with completeness, special soundness and
   honest-verifier zero knowledge, the extraction of Appendix C (a witness
   of the validity proof together with the discrete logarithm of the DLEQ
   proof gives a MAC on the blinded key and the attributes, or the Issuer's
   key), and the statistical anonymity of the randomised credential (the
   distribution of (Ā, D) over uniform (r_1, r_2) does not depend on the
   credential). The Fiat–Shamir verifier is in Backend/BBSSharpVerifier.v
   and the P-256 instantiation in Examples/BBSSharpIns.v. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

Section BBSSharp.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Infix "^" := gpow.
  Local Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).
  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation VG m := (Vector.t G m).

  Local Notation gcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation ggroup := (@commutative_group_group G (@eq G) gop gid ginv gcg).
  Local Notation gmonoid := (@group_monoid G (@eq G) gop gid ginv ggroup).
  Local Notation gassoc := (@associative G (@eq G) gop
    (@monoid_is_associative G (@eq G) gop gid gmonoid)).
  Local Notation gid_l := (@left_identity G (@eq G) gop gid
    (@monoid_is_left_idenity G (@eq G) gop gid gmonoid)).
  Local Notation gid_r := (@right_identity G (@eq G) gop gid
    (@monoid_is_right_identity G (@eq G) gop gid gmonoid)).
  Local Notation gcomm := (@commutative G (@eq G) gop
    (@commutative_group_is_commutative G (@eq G) gop gid ginv gcg)).
  Local Notation ginv_l := (@left_inverse G (@eq G) gop gid ginv
    (@group_is_left_inverse G (@eq G) gop gid ginv ggroup)).
  Local Notation ginv_r := (@right_inverse G (@eq G) gop gid ginv
    (@group_is_right_inverse G (@eq G) gop gid ginv ggroup)).

  (* the shared lemmas of Crypto/OkamotoRows.v at this instance *)
  Local Notation pow_opp := (pow_opp (Hvec := Hvec)).
  Local Notation ginv_gop := (ginv_gop (Hvec := Hvec)).
  Local Notation ginv_gid := (ginv_gid (Hvec := Hvec)).
  Local Notation gpow_add := (gpow_add (Hvec := Hvec)).
  Local Notation gpow_mul := (gpow_mul (Hvec := Hvec)).
  Local Notation gpow_one := (gpow_one (Hvec := Hvec)).
  Local Notation gpow_zero := (gpow_zero (Hvec := Hvec)).
  Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
  Local Notation gop4 := (gop4 (Hvec := Hvec)).
  Local Notation mexp_map_opp := (mexp_map_opp (Hvec := Hvec)).
  Local Notation gid_pow := (smul_vid (HV := Hvec)).

  Lemma nth_F1 : forall {A : Type} (k : nat) (a : A) (v : Vector.t A k), (a :: v)[@Fin.F1] = a.
  Proof. reflexivity. Qed.
  Lemma nth_FS : forall {A : Type} (k : nat) (a : A) (v : Vector.t A k) (p : Fin.t k),
    (a :: v)[@Fin.FS p] = v[@p].
  Proof. reflexivity. Qed.

  Lemma mul_nonzero : forall a b : F, a <> zero -> b <> zero -> mul a b <> zero.
  Proof.
    intros a b ha hb h; apply hb.
    assert (e : b = mul (inv a) (mul a b)) by (field; exact ha).
    rewrite e, h; field; exact ha.
  Qed.

  (* discharges the non-zero side conditions of [field] *)
  Local Ltac nz := repeat (first [split | apply mul_nonzero | assumption]).

  (* a^z = 1 with a ≠ 1 forces z = 0 (the group has prime order) *)
  Lemma pow_eq_gid : forall (a : G) (z : F), a <> gid -> a ^ z = gid -> z = zero.
  Proof.
    intros a z ha hz; destruct (Fdec z zero) as [e | ne]; [exact e | exfalso; apply ha].
    assert (e : a = (a ^ z) ^ (inv z)).
    { rewrite <-gpow_mul; replace (mul z (inv z)) with one by (field; exact ne); symmetry; apply gpow_one. }
    rewrite e, hz; apply gid_pow.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* MAC_BBS and its randomisation                                     *)
  (* ---------------------------------------------------------------- *)

  Section Credential.

    (* Cm = g_0 · pk · ∏ g_i^{m_i}, with the attributes split into the
      disclosed ones (gD, mD) and the undisclosed ones (gU, mU) *)
    Definition Cm {d u : nat} (g0 pk : G) (gD : VG d) (mD : Vector.t F d) (gU : VG u) (mU : Vector.t F u) : G :=
      gop g0 (gop pk (gexp (gD ++ gU) (mD ++ mU))).

    Definition mac (C : G) (x e : F) : G := C ^ (inv (add x e)).
    Definition mac_B (C A : G) (e : F) : G := gop C (A ^ (opp e)).

    Lemma mac_pow : forall (C : G) (x e : F), add x e <> zero -> (mac C x e) ^ (add x e) = C.
    Proof.
      intros * h; unfold mac; rewrite <-gpow_mul.
      replace (mul (inv (add x e)) (add x e)) with one by (field; exact h).
      apply gpow_one.
    Qed.

    (* B = Cm · A^{−e} = A^x *)
    Lemma mac_relation : forall (C : G) (x e : F), add x e <> zero ->
      mac_B C (mac C x e) e = (mac C x e) ^ x.
    Proof.
      intros * h; unfold mac_B.
      set (A := mac C x e).
      assert (hC : gop (A ^ x) (A ^ e) = C) by (rewrite <-gpow_add; apply mac_pow; exact h).
      transitivity (gop (gop (A ^ x) (A ^ e)) (A ^ (opp e))); [rewrite hC; reflexivity |].
      rewrite <-gassoc, pow_opp, ginv_r, gid_r; reflexivity.
    Qed.

    Definition rand_A (A : G) (r1 r2 : F) : G := A ^ (mul r1 r2).
    Definition rand_D (C : G) (r2 : F) : G := C ^ r2.
    Definition rand_B (Abar D : G) (e r1 : F) : G := gop (Abar ^ (opp e)) (D ^ r1).

    (* B̄ = Ā^{−e} D^{r_1} = Ā^x *)
    Lemma rand_relation : forall (C : G) (x e r1 r2 : F), add x e <> zero ->
      rand_B (rand_A (mac C x e) r1 r2) (rand_D C r2) e r1 = (rand_A (mac C x e) r1 r2) ^ x.
    Proof.
      intros * h; unfold rand_B, rand_A, rand_D, mac.
      repeat rewrite <-gpow_mul; rewrite <-gpow_add; f_equal; field; exact h.
    Qed.

    (* D^{r_3} = Cm for r_3 = r_2^{−1} *)
    Lemma rand_D_inv : forall (C : G) (r2 : F), r2 <> zero -> (rand_D C r2) ^ (inv r2) = C.
    Proof.
      intros * h; unfold rand_D; rewrite <-gpow_mul.
      replace (mul r2 (inv r2)) with one by (field; exact h); apply gpow_one.
    Qed.

  End Credential.

  (* ---------------------------------------------------------------- *)
  (* The validity proof: one Okamoto statement in G²                   *)
  (* ---------------------------------------------------------------- *)

  Section Validity.

    (* additive key blinding (the ECSchnorr variant, Section 5.1) *)
    Definition pk_blind (g : G) (sk r : F) : G := g ^ (add sk r).

    (* the public target of the second equation: g_0 · pk_Blind · ∏_{i∈D} g_i^{m_i} *)
    Definition target_P {d : nat} (g0 pkB : G) (gD : VG d) (mD : Vector.t F d) : G :=
      gop g0 (gop pkB (gexp gD mD)).

    (* witness coordinates: (−e, r_1, r_3, r, −m_i for i ∉ D) *)
    Definition validity_witness {u : nat} (e r1 r3 r : F) (mU : Vector.t F u) : Vector.t F (S (S (S (S u)))) :=
      opp e :: r1 :: r3 :: r :: Vector.map opp mU.

    Definition row1 {u : nat} (Abar D : G) : VG (S (S (S (S u)))) := Abar :: D :: Vector.const gid (S (S u)).
    Definition row2 {u : nat} (D g : G) (gU : VG u) : VG (S (S (S (S u)))) := gid :: gid :: D :: g :: gU.

    Definition validity_rows {u : nat} (Abar D g : G) (gU : VG u) : Vector.t (VG (S (S (S (S u))))) 2 :=
      [row1 Abar D; row2 D g gU].
    Definition validity_targets (Bbar P : G) : VG 2 := [Bbar; P].

    Lemma row1_relation : forall (u : nat) (Abar D : G) (e r1 r3 r : F) (mU : Vector.t F u),
      gexp (row1 Abar D) (validity_witness e r1 r3 r mU) = rand_B Abar D e r1.
    Proof.
      intros; unfold row1, validity_witness, rand_B.
      rewrite mexp_cons, mexp_cons, (mexp_const_vid (HV := Hvec)), gid_r; reflexivity.
    Qed.

    Lemma row2_relation : forall (d u : nat) (g g0 : G) (sk r e r1 r2 : F) (gD : VG d) (mD : Vector.t F d)
      (gU : VG u) (mU : Vector.t F u),
      r2 <> zero ->
      gexp (row2 (rand_D (Cm g0 (g ^ sk) gD mD gU mU) r2) g gU) (validity_witness e r1 (inv r2) r mU) =
      target_P g0 (pk_blind g sk r) gD mD.
    Proof.
      intros * hr2; unfold row2, validity_witness, target_P, pk_blind.
      rewrite mexp_cons, mexp_cons, mexp_cons, mexp_cons, mexp_map_opp, gid_pow, gid_pow, gid_l, gid_l.
      rewrite rand_D_inv; [| exact hr2].
      unfold Cm; rewrite mexp_app, gpow_add.
      set (MD := gexp gD mD); set (MU := gexp gU mU).
      rewrite gop4, <-(gassoc (g ^ sk) (gop MD MU) (ginv MU)), <-(gassoc MD MU (ginv MU)),
        (ginv_r MU), (gid_r MD), <-(gassoc g0 (g ^ r) (gop (g ^ sk) MD)), (gassoc (g ^ r) (g ^ sk) MD),
        (gcomm (g ^ r) (g ^ sk)); reflexivity.
    Qed.

    (* the Okamoto instance in G² *)
    Definition validity_verify {u : nat} (Abar D g : G) (gU : VG u) (Bbar P : G)
      (t : @sigma_proto F (VG 2) 1 1 (S (S (S (S u))))) : bool :=
      ext_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)
        (validity_rows Abar D g gU) (validity_targets Bbar P) t.

    Definition validity_real {u : nat} (e r1 r3 r : F) (mU : Vector.t F u) (Abar D g : G) (gU : VG u)
      (Bbar P : G) (us : Vector.t F (S (S (S (S u))))) (c : F) : @sigma_proto F (VG 2) 1 1 (S (S (S (S u)))) :=
      ext_real (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        (validity_witness e r1 r3 r mU) (validity_rows Abar D g gU) (validity_targets Bbar P) us c.

    Definition validity_simulator {u : nat} (Abar D g : G) (gU : VG u) (Bbar P : G)
      (us : Vector.t F (S (S (S (S u))))) (c : F) : @sigma_proto F (VG 2) 1 1 (S (S (S (S u)))) :=
      ext_simulator (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        (validity_rows Abar D g gU) (validity_targets Bbar P) us c.

    Definition validity_real_distribution {u : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (e r1 r3 r : F) (mU : Vector.t F u) (Abar D g : G) (gU : VG u) (Bbar P : G) (c : F) :
      dist (@sigma_proto F (VG 2) 1 1 (S (S (S (S u))))) :=
      ext_real_distribution (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        lf Hlfn (validity_witness e r1 r3 r mU) (validity_rows Abar D g gU) (validity_targets Bbar P) c.

    Definition validity_simulator_distribution {u : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (Abar D g : G) (gU : VG u) (Bbar P : G) (c : F) : dist (@sigma_proto F (VG 2) 1 1 (S (S (S (S u))))) :=
      ext_simulator_distribution (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        lf Hlfn (validity_rows Abar D g gU) (validity_targets Bbar P) c.

    (* the honest holder's witness satisfies both rows *)
    Lemma validity_relation : forall (d u : nat) (g g0 : G) (sk r x e r1 r2 : F) (gD : VG d) (mD : Vector.t F d)
      (gU : VG u) (mU : Vector.t F u),
      add x e <> zero -> r2 <> zero ->
      let C := Cm g0 (g ^ sk) gD mD gU mU in
      let Abar := rand_A (mac C x e) r1 r2 in
      let D := rand_D C r2 in
      forall j : Fin.t 2,
        gexp (validity_rows Abar D g gU)[@j] (validity_witness e r1 (inv r2) r mU) =
        (validity_targets (rand_B Abar D e r1) (target_P g0 (pk_blind g sk r) gD mD))[@j].
    Proof.
      intros * hx hr2; cbv zeta; intro j; unfold validity_rows, validity_targets.
      destruct (fin_inv_S _ j) as [-> | (j' & ->)].
      + rewrite nth_F1, nth_F1; apply row1_relation.
      + destruct (fin_inv_S _ j') as [-> | (j'' & ->)]; [| refine (match fin_inv_0 j'' with end)].
        rewrite nth_FS, nth_F1, nth_FS, nth_F1; apply row2_relation; exact hr2.
    Qed.

    Theorem validity_completeness : forall (d u : nat) (g g0 : G) (sk r x e r1 r2 : F) (gD : VG d)
      (mD : Vector.t F d) (gU : VG u) (mU : Vector.t F u) (us : Vector.t F (S (S (S (S u))))) (c : F),
      add x e <> zero -> r2 <> zero ->
      let C := Cm g0 (g ^ sk) gD mD gU mU in
      let Abar := rand_A (mac C x e) r1 r2 in
      let D := rand_D C r2 in
      let Bbar := rand_B Abar D e r1 in
      let P := target_P g0 (pk_blind g sk r) gD mD in
      validity_verify Abar D g gU Bbar P (validity_real e r1 (inv r2) r mU Abar D g gU Bbar P us c) = true.
    Proof.
      intros * hx hr2; cbv zeta; unfold validity_verify, validity_real.
      apply ext_completeness; apply validity_relation; assumption.
    Qed.

    Theorem validity_simulator_completeness : forall (u : nat) (Abar D g : G) (gU : VG u) (Bbar P : G)
      (us : Vector.t F (S (S (S (S u))))) (c : F),
      validity_verify Abar D g gU Bbar P (validity_simulator Abar D g gU Bbar P us c) = true.
    Proof. intros *; apply ext_simulator_completeness. Qed.

    (* special soundness: a witness for both equations *)
    Theorem validity_special_soundness : forall (u : nat) (Abar D g : G) (gU : VG u) (Bbar P : G)
      (a : VG 2) (c1 c2 : F) (rs1 rs2 : Vector.t F (S (S (S (S u))))),
      c1 <> c2 ->
      validity_verify Abar D g gU Bbar P ([a]; [c1]; rs1) = true ->
      validity_verify Abar D g gU Bbar P ([a]; [c2]; rs2) = true ->
      exists w : Vector.t F (S (S (S (S u)))), gexp (row1 Abar D) w = Bbar /\ gexp (row2 D g gU) w = P.
    Proof.
      intros * hc h1 h2; unfold validity_verify in h1, h2.
      destruct (ext_special_soundness _ _ _ _ _ _ _ _ _ hc h1 h2) as (w & hw).
      exists w; split; [exact (hw Fin.F1) | exact (hw (Fin.FS Fin.F1))].
    Qed.

    Theorem validity_shvzk : forall (d u : nat) (lf : list F) (Hlfn : lf <> List.nil) (g g0 : G)
      (sk r x e r1 r2 : F) (gD : VG d) (mD : Vector.t F d) (gU : VG u) (mU : Vector.t F u) (c : F),
      add x e <> zero -> r2 <> zero ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      let C := Cm g0 (g ^ sk) gD mD gU mU in
      let Abar := rand_A (mac C x e) r1 r2 in
      let D := rand_D C r2 in
      let Bbar := rand_B Abar D e r1 in
      let P := target_P g0 (pk_blind g sk r) gD mD in
      Permutation (validity_real_distribution lf Hlfn e r1 (inv r2) r mU Abar D g gU Bbar P c)
        (validity_simulator_distribution lf Hlfn Abar D g gU Bbar P c).
    Proof.
      intros * hx hr2 hnd hall; cbv zeta.
      unfold validity_real_distribution, validity_simulator_distribution.
      apply ext_shvzk; [apply validity_relation; assumption | exact hnd | exact hall].
    Qed.

    (* ---- multiplicative key blinding (the ECDSA variant, Section 5.3) ---- *)

    Definition pk_blind_mul (g : G) (sk r : F) : G := g ^ (mul sk r).
    Definition target_F {d : nat} (g0 : G) (gD : VG d) (mD : Vector.t F d) : G := gop g0 (gexp gD mD).
    Definition row2_mul {u : nat} (D pkB : G) (gU : VG u) : VG (S (S (S (S u)))) := gid :: gid :: D :: pkB :: gU.

    (* witness (−e, r_1, r_3, −r^{−1}, −m_i): D^{r_3} pk_Blind^{−1/r} ∏ g_i^{−m_i} = g_0 ∏_{D} g_i^{m_i} *)
    Lemma row2_mul_relation : forall (d u : nat) (g g0 : G) (sk r e r1 r2 : F) (gD : VG d) (mD : Vector.t F d)
      (gU : VG u) (mU : Vector.t F u),
      r <> zero -> r2 <> zero ->
      gexp (row2_mul (rand_D (Cm g0 (g ^ sk) gD mD gU mU) r2) (pk_blind_mul g sk r) gU)
        (validity_witness e r1 (inv r2) (opp (inv r)) mU) = target_F g0 gD mD.
    Proof.
      intros * hr hr2; unfold row2_mul, validity_witness, target_F, pk_blind_mul.
      rewrite mexp_cons, mexp_cons, mexp_cons, mexp_cons, mexp_map_opp, gid_pow, gid_pow, gid_l, gid_l.
      rewrite rand_D_inv; [| exact hr2].
      rewrite <-gpow_mul; replace (mul (mul sk r) (opp (inv r))) with (opp sk) by (field; exact hr).
      rewrite pow_opp.
      unfold Cm; rewrite mexp_app.
      set (MD := gexp gD mD); set (MU := gexp gU mU).
      rewrite <-gassoc, (gop4 (g ^ sk) (gop MD MU) (ginv (g ^ sk)) (ginv MU)), (ginv_r (g ^ sk)), gid_l,
        <-(gassoc MD MU (ginv MU)), (ginv_r MU), (gid_r MD); reflexivity.
    Qed.

  End Validity.

  (* ---------------------------------------------------------------- *)
  (* Holder binding (π_HB, Figure 7): Schnorr                          *)
  (* ---------------------------------------------------------------- *)

  Section HolderBinding.

    Definition hb_verify (g pkB : G) (t : @sigma_proto F G 1 1 1) : bool :=
      accepting_conversation (gop := gop) (gpow := gpow) (Gdec := Gdec) g pkB t.

    Definition hb_real (g : G) (sk r u c : F) : @sigma_proto F G 1 1 1 :=
      schnorr_protocol (add := add) (mul := mul) (gpow := gpow) (add sk r) g u c.

    Theorem hb_completeness : forall (g : G) (sk r u c : F),
      hb_verify g (pk_blind g sk r) (hb_real g sk r u c) = true.
    Proof. intros; apply schnorr_completeness; reflexivity. Qed.

    Theorem hb_special_soundness : forall (g pkB a : G) (c1 r1 c2 r2 : F),
      c1 <> c2 ->
      hb_verify g pkB ([a]; [c1]; [r1]) = true ->
      hb_verify g pkB ([a]; [c2]; [r2]) = true ->
      exists skB : F, g ^ skB = pkB.
    Proof. intros * hc h1 h2; exact (special_soundness_berry g pkB a c1 r1 c2 r2 hc h1 h2). Qed.

    Theorem hb_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (g : G) (sk r c : F),
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation (schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn (add sk r) g c)
        (simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn g (pk_blind g sk r) c).
    Proof.
      intros * hnd hall.
      exact (special_honest_verifier_zkp_enum (add sk r) g (pk_blind g sk r) eq_refl lf Hlfn c hnd hall).
    Qed.

  End HolderBinding.

  (* ---------------------------------------------------------------- *)
  (* π_DLEQ (Figure 6): Chaum–Pedersen for B̄ = Ā^x ∧ pk_I = g̃^x          *)
  (* ---------------------------------------------------------------- *)

  Section DLEQ.

    Definition dleq_verify (gt pkI Abar Bbar : G) (t : @sigma_proto F G 2 1 1) : bool :=
      cp_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) gt pkI Abar Bbar t.

    (* the verifier's reconstruction g̃^ρ pk_I^{−c}, Ā^ρ B̄^{−c} with challenge c *)
    Theorem dleq_reconstruct_accepting : forall (gt pkI Abar Bbar : G) (c ρ : F),
      dleq_verify gt pkI Abar Bbar (cp_transcript (opp := opp) (gop := gop) (gpow := gpow) gt pkI Abar Bbar c ρ) = true.
    Proof. intros; apply cp_reconstruct_accepting. Qed.

    Theorem dleq_special_soundness : forall (gt pkI Abar Bbar : G) (a : VG 2) (ca ra cb rb : F),
      ca <> cb ->
      dleq_verify gt pkI Abar Bbar (a; [ca]; [ra]) = true ->
      dleq_verify gt pkI Abar Bbar (a; [cb]; [rb]) = true ->
      exists x : F, gt ^ x = pkI /\ Abar ^ x = Bbar.
    Proof. intros * hc h1 h2; exact (cp_special_soundness gt pkI Abar Bbar a ca ra cb rb hc h1 h2). Qed.

    Theorem dleq_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (gt pkI Abar Bbar : G) (x c : F),
      gt ^ x = pkI -> Abar ^ x = Bbar ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation
        (generalised_cp_schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn x gt Abar c)
        (generalised_cp_simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn gt Abar pkI Bbar c).
    Proof. intros * h1 h2 hnd hall; exact (cp_shvzk lf Hlfn gt pkI Abar Bbar x c h1 h2 hnd hall). Qed.

  End DLEQ.

  (* ---------------------------------------------------------------- *)
  (* Extraction of a credential (Appendix C)                           *)
  (* ---------------------------------------------------------------- *)

  Section Extraction.

    (* From a witness (w_0, w_1, w_2, w_3, w_U) of the two validity equations,
      the discrete logarithm x of the DLEQ proof and the discrete logarithm
      sk_B of pk_Blind: with w_1, w_2 ≠ 0, (Ā^{w_2/w_1}, −w_0) is a MAC_BBS tag
      on the key sk_B − w_3, the disclosed attributes and the attributes −w_U;
      the paper's (Ā^{r_3 r_1^{−1}}, e) on (sk_Blind − r, {m_i}). *)
    Theorem credential_extraction : forall (d u : nat) (g g0 Abar Bbar D pkB : G) (gD : VG d)
      (mD : Vector.t F d) (gU : VG u) (x skB w0 w1 w2 w3 : F) (wU : Vector.t F u),
      Abar ^ x = Bbar ->
      g ^ skB = pkB ->
      gop (Abar ^ w0) (D ^ w1) = Bbar ->
      gop (D ^ w2) (gop (g ^ w3) (gexp gU wU)) = target_P g0 pkB gD mD ->
      w1 <> zero -> w2 <> zero ->
      (Abar ^ (mul w2 (inv w1))) ^ (add x (opp w0)) =
      Cm g0 (g ^ (sub skB w3)) gD mD gU (Vector.map opp wU).
    Proof.
      intros * hx hpk h1 h2 hw1 hw2.
      (* Ā^{x − w_0} = D^{w_1} *)
      assert (hAD : Abar ^ (add x (opp w0)) = D ^ w1).
      { rewrite gpow_add, hx, <-h1, (gcomm (Abar ^ w0) (D ^ w1)), <-gassoc, pow_opp, ginv_r, gid_r;
        reflexivity. }
      rewrite <-gpow_mul.
      replace (mul (mul w2 (inv w1)) (add x (opp w0))) with (mul (add x (opp w0)) (mul w2 (inv w1)))
        by (field; exact hw1).
      rewrite gpow_mul, hAD, <-gpow_mul.
      replace (mul w1 (mul w2 (inv w1))) with w2 by (field; exact hw1).
      (* D^{w_2} = P · (g^{w_3} ∏ g_i^{w_i})^{−1} *)
      set (Y := gop (g ^ w3) (gexp gU wU)) in *.
      assert (hD : D ^ w2 = gop (target_P g0 pkB gD mD) (ginv Y)).
      { rewrite <-h2, <-gassoc, ginv_r, gid_r; reflexivity. }
      rewrite hD; unfold target_P, Cm, Y; rewrite mexp_app, ginv_gop, mexp_map_opp, <-hpk.
      set (MD := gexp gD mD); set (MU := gexp gU wU).
      assert (hs : g ^ (sub skB w3) = gop (g ^ skB) (ginv (g ^ w3))).
      { rewrite <-pow_opp, <-gpow_add; f_equal; field. }
      rewrite hs, <-(gassoc g0 (gop (g ^ skB) MD) (gop (ginv (g ^ w3)) (ginv MU))),
        (gop4 (g ^ skB) MD (ginv (g ^ w3)) (ginv MU)); reflexivity.
    Qed.

    (* if w_1 = 0 the witness reveals the Issuer's key: x = w_0 *)
    Theorem issuer_key_extraction : forall (Abar Bbar D : G) (x w0 w1 : F),
      Abar <> gid ->
      Abar ^ x = Bbar ->
      gop (Abar ^ w0) (D ^ w1) = Bbar ->
      w1 = zero -> x = w0.
    Proof.
      intros * hA hx h1 hw1; subst w1.
      rewrite gpow_zero, gid_r in h1.
      assert (hz : Abar ^ (sub x w0) = gid).
      { replace (sub x w0) with (add x (opp w0)) by field.
        rewrite gpow_add, hx, <-h1, pow_opp, ginv_r; reflexivity. }
      pose proof (pow_eq_gid Abar (sub x w0) hA hz) as h.
      assert (e : x = add (sub x w0) w0) by field.
      rewrite e, h; field.
    Qed.

    (* Soundness of the whole presentation (Appendix C): two accepting
      transcripts of each proof with distinct challenges give the Issuer's
      key x behind pk_I and the key sk_B behind pk_Blind, and either a
      MAC_BBS tag on (sk_B − w_3, disclosed attributes, −w_U), or the Issuer's
      key (w_1 = 0), or a representation of g_0 · pk_Blind · ∏_{D} g_i^{m_i} in the
      bases g, g_i (w_2 = 0); the last two break the discrete logarithm. *)
    Theorem presentation_soundness : forall (d u : nat) (g gt g0 pkI Abar Bbar D pkB : G) (gD : VG d)
      (mD : Vector.t F d) (gU : VG u) (av : VG 2) (c1 c2 : F) (rs1 rs2 : Vector.t F (S (S (S (S u)))))
      (ad : VG 2) (ca ra cb rb : F) (ah : G) (ch1 rh1 ch2 rh2 : F),
      Abar <> gid ->
      c1 <> c2 ->
      validity_verify Abar D g gU Bbar (target_P g0 pkB gD mD) ([av]; [c1]; rs1) = true ->
      validity_verify Abar D g gU Bbar (target_P g0 pkB gD mD) ([av]; [c2]; rs2) = true ->
      ca <> cb ->
      dleq_verify gt pkI Abar Bbar (ad; [ca]; [ra]) = true ->
      dleq_verify gt pkI Abar Bbar (ad; [cb]; [rb]) = true ->
      ch1 <> ch2 ->
      hb_verify g pkB ([ah]; [ch1]; [rh1]) = true ->
      hb_verify g pkB ([ah]; [ch2]; [rh2]) = true ->
      exists (x skB w0 w1 w2 w3 : F) (wU : Vector.t F u),
        gt ^ x = pkI /\ g ^ skB = pkB /\
        ((w1 = zero /\ x = w0) \/
         (w2 = zero /\ gop (g ^ w3) (gexp gU wU) = target_P g0 pkB gD mD) \/
         (Abar ^ (mul w2 (inv w1))) ^ (add x (opp w0)) =
           Cm g0 (g ^ (sub skB w3)) gD mD gU (Vector.map opp wU)).
    Proof.
      intros * hA hc h1 h2 hcd hd1 hd2 hch hh1 hh2.
      destruct (validity_special_soundness _ _ _ _ _ _ _ _ _ _ _ _ hc h1 h2) as (w & hw1 & hw2).
      destruct (dleq_special_soundness _ _ _ _ _ _ _ _ _ hcd hd1 hd2) as (x & hx1 & hx2).
      destruct (hb_special_soundness _ _ _ _ _ _ _ hch hh1 hh2) as (skB & hsk).
      destruct (vector_inv_S w) as (w0 & wa & ->); destruct (vector_inv_S wa) as (w1 & wb & ->).
      destruct (vector_inv_S wb) as (w2 & wc & ->); destruct (vector_inv_S wc) as (w3 & wU & ->).
      unfold row1, row2 in hw1, hw2.
      rewrite mexp_cons, mexp_cons, (mexp_const_vid (HV := Hvec)), gid_r in hw1.
      rewrite mexp_cons, mexp_cons, mexp_cons, mexp_cons, gid_pow, gid_pow, gid_l, gid_l in hw2.
      exists x, skB, w0, w1, w2, w3, wU; split; [exact hx1 | split; [exact hsk |]].
      destruct (Fdec w1 zero) as [hz1 | hn1].
      + left; split; [exact hz1 |].
        exact (issuer_key_extraction Abar Bbar D x w0 w1 hA hx2 hw1 hz1).
      + destruct (Fdec w2 zero) as [hz2 | hn2].
        * right; left; split; [exact hz2 |]; rewrite hz2, gpow_zero, gid_l in hw2; exact hw2.
        * right; right; exact (credential_extraction d u g g0 Abar Bbar D pkB gD mD gU x skB w0 w1 w2 w3 wU hx2 hsk hw1 hw2 hn1 hn2).
    Qed.

  End Extraction.

  (* ---------------------------------------------------------------- *)
  (* Statistical anonymity of the randomised credential                *)
  (* ---------------------------------------------------------------- *)

  Section Anonymity.

    (* the randomised pair (Ā, D) = (A^{r_1 r_2}, Cm^{r_2}) as a function of
      the uniformly chosen (r_1, r_2) *)
    Definition randomise (A C : G) (v : Vector.t F 2) : G * G :=
      (A ^ (mul (Vector.hd v) (Vector.hd (Vector.tl v))), C ^ (Vector.hd (Vector.tl v))).

    Definition randomised_distribution (lf : list F) (Hlfn : lf <> List.nil) (A C : G) : dist (G * G) :=
      List.map (fun '(v, p) => (randomise A C v, p))
        (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) 2).

    Lemma map_pair_compose : forall {A B C P : Type} (f : A -> B) (k : B -> C) (l : list (A * P)),
      List.map (fun '(v, p) => (k (f v), p)) l =
      List.map (fun '(v, p) => (k v, p)) (List.map (fun '(v, p) => (f v, p)) l).
    Proof. intros; induction l as [| (v & p) l ih]; [reflexivity | cbn; rewrite ih; reflexivity]. Qed.

    Lemma eta2 : forall v : Vector.t F 2, v = [Vector.hd v; Vector.hd (Vector.tl v)].
    Proof.
      intro v; destruct (vector_inv_S v) as (r1 & v' & ->).
      destruct (vector_inv_S v') as (r2 & v'' & ->); rewrite (vector_inv_0 v''); reflexivity.
    Qed.

    (* Two credentials A = g^a, Cm = g^c and A' = g^{a'}, Cm' = g^{c'} (all
      non-trivial) give the same distribution of (Ā, D): the randomised
      credential carries no information about the credential, and B̄ = Ā^x is
      a function of it. This is Game 5 of the paper's anonymity proof. *)
    Theorem randomisation_uniform : forall (lf : list F) (Hlfn : lf <> List.nil) (g : G) (a c a' c' : F),
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      a <> zero -> c <> zero -> a' <> zero -> c' <> zero ->
      Permutation (randomised_distribution lf Hlfn (g ^ a) (g ^ c))
        (randomised_distribution lf Hlfn (g ^ a') (g ^ c')).
    Proof.
      intros * hnd hall ha hc ha' hc'.
      set (Phi := fun v : Vector.t F 2 =>
        [mul (Vector.hd v) (div (mul a c') (mul a' c)); mul (Vector.hd (Vector.tl v)) (div c c')]).
      set (Psi := fun v : Vector.t F 2 =>
        [mul (Vector.hd v) (div (mul a' c) (mul a c')); mul (Vector.hd (Vector.tl v)) (div c' c)]).
      assert (hrand : forall v, randomise (g ^ a) (g ^ c) v = randomise (g ^ a') (g ^ c') (Phi v)).
      { intro v; unfold randomise, Phi; cbn [Vector.hd Vector.tl Vector.caseS].
        rewrite <-!gpow_mul; f_equal; f_equal; field; nz. }
      unfold randomised_distribution.
      assert (hmap : List.map (fun '(v, p) => (randomise (g ^ a) (g ^ c) v, p))
          (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) 2) =
        List.map (fun '(v, p) => (randomise (g ^ a') (g ^ c') (Phi v), p))
          (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) 2)).
      { apply List.map_ext; intros (v & p); rewrite hrand; reflexivity. }
      rewrite hmap, map_pair_compose.
      apply Permutation_map.
      apply (repeat_uniform_bijection_perm lf Hlfn 2 Phi Psi hnd hall).
      + intro v; rewrite (eta2 v); unfold Phi, Psi; cbn [Vector.hd Vector.tl Vector.caseS].
        apply (f_equal2 (fun x y : F => [x; y])); field; nz.
      + intro v; rewrite (eta2 v); unfold Phi, Psi; cbn [Vector.hd Vector.tl Vector.caseS].
        apply (f_equal2 (fun x y : F => [x; y])); field; nz.
    Qed.

  End Anonymity.

End BBSSharp.
