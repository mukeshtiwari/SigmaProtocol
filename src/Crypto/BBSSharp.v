(** * BBS♯: pairing-free BBS anonymous credentials *)

(** This file formalises the zero-knowledge core of BBS♯ (S. Desmoulins,
    A. Dumanois, S. Kane, J. Traoré, Making BBS Anonymous Credentials eIDAS
    2.0 Compliant, IACR ePrint 2025/619), a variant of BBS credentials that
    replaces the pairing check by an algebraic MAC and a discrete-log
    equality proof, so that it runs on standard elliptic curves such as
    P-256.

    The credential is the algebraic MAC [MAC_BBS]. With public generators
    [g], [g̃], [g_0], [g_1 .. g_n] of a prime-order group, the Issuer's secret
    key [x] (public key [pk_I = g̃^x]), the holder's key [pk = g^(sk)] and
    attributes [m_i]:

    [[
      Cm = g_0 · pk · ∏_i g_i^(m_i),    A = Cm^(1/(x+e)),    σ = (A, e),
      B  = Cm · A^(−e) = A^x.
    ]]

    For a presentation the holder blinds the key, [pk_Blind = g^(sk+r)], and
    randomises the MAC with fresh [r_1], [r_2]:

    [[
      Ā = A^(r_1·r_2),   D = Cm^(r_2),   B̄ = Ā^(−e) · D^(r_1) = Ā^x,   r_3 = r_2⁻¹.
    ]]

    The presentation consists of three Sigma proofs:

    - the validity proof: knowledge of [(−e, r_1, r_3, r, −m_U)] with
      [B̄ = Ā^(−e) · D^(r_1)] and
      [g_0 · pk_Blind · ∏_(i ∈ D) g_i^(m_i) = D^(r_3) · g^r · ∏_(i ∉ D) g_i^(−m_i)],
      two equations over one witness, hence one Okamoto statement in [G²]
      via [OkamotoRows] (section [Validity]);
    - holder binding: a Schnorr proof of knowledge of the discrete
      logarithm of [pk_Blind] (section [HolderBinding]);
    - the Issuer's DLEQ proof [B̄ = Ā^x ∧ pk_I = g̃^x], a Chaum–Pedersen proof
      that replaces the BBS pairing check (section [DLEQ]).

    Beyond completeness, special soundness and special honest-verifier zero
    knowledge for each proof (inherited from [Okamoto], [OkamotoRows],
    [Sigma] and [ChaumPedersen]), the file proves:

    - [presentation_soundness]: from two accepting transcripts of each of
      the three proofs one extracts either a valid MAC on the blinded key and
      the attributes, or the Issuer's key, or a discrete-log relation among
      the public bases (the extraction argument of the paper's Appendix C);
    - [randomisation_uniform]: the randomised pair [(Ā, D)] has the same
      distribution for any two credentials with non-trivial components, so it
      carries no information about the credential (statistical anonymity).

    The Fiat–Shamir verifier is in [Backend/BBSSharpVerifier.v] and a P-256
    instantiation in [Examples/BBSSharpIns.v]. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Sigma Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

(** ** Setting and auxiliary facts *)
Section BBSSharp.

  (** A field [F] of exponents and a group [G] forming a vector space, each
      with decidable equality. The local notations name the group laws and
      import the shared lemmas of [OkamotoRows] at this instance; [VG m] is
      the product group [G^m]. *)
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

  (** Indexing a cons vector at the first and at a successor position, by
      computation. *)
  Lemma nth_F1 : forall {A : Type} (k : nat) (a : A) (v : Vector.t A k), (a :: v)[@Fin.F1] = a.
  Proof. reflexivity. Qed.
  Lemma nth_FS : forall {A : Type} (k : nat) (a : A) (v : Vector.t A k) (p : Fin.t k),
    (a :: v)[@Fin.FS p] = v[@p].
  Proof. reflexivity. Qed.

  (** A product of non-zero field elements is non-zero. *)
  Lemma mul_nonzero : forall a b : F, a <> zero -> b <> zero -> mul a b <> zero.
  Proof.
    intros a b ha hb h; apply hb.
    assert (e : b = mul (inv a) (mul a b)) by (field; exact ha).
    rewrite e, h; field; exact ha.
  Qed.

  (** Discharge the non-zero side conditions produced by [field]. *)
  Local Ltac nz := repeat (first [split | apply mul_nonzero | assumption]).

  (** If [a ≠ gid] and [a^z = gid] then [z = 0]: otherwise
      [a = (a^z)^(z⁻¹) = gid]. In a prime-order group this says every
      non-identity element generates the group. *)
  Lemma pow_eq_gid : forall (a : G) (z : F), a <> gid -> a ^ z = gid -> z = zero.
  Proof.
    intros a z ha hz; destruct (Fdec z zero) as [e | ne]; [exact e | exfalso; apply ha].
    assert (e : a = (a ^ z) ^ (inv z)).
    { rewrite <-gpow_mul; replace (mul z (inv z)) with one by (field; exact ne); symmetry; apply gpow_one. }
    rewrite e, hz; apply gid_pow.
  Qed.

  (** ** The MAC and its randomisation *)
  Section Credential.

    (** The credential message [Cm = g_0 · pk · ∏ g_i^(m_i)], with the
        attributes split into disclosed ([gD], [mD]) and undisclosed ([gU],
        [mU]) parts. *)
    Definition Cm {d u : nat} (g0 pk : G) (gD : VG d) (mD : Vector.t F d) (gU : VG u) (mU : Vector.t F u) : G :=
      gop g0 (gop pk (gexp (gD ++ gU) (mD ++ mU))).

    (** The MAC tag [A = C^(1/(x+e))] and the derived value
        [B = C · A^(−e)] ([mac_B]). *)
    Definition mac (C : G) (x e : F) : G := C ^ (inv (add x e)).
    Definition mac_B (C A : G) (e : F) : G := gop C (A ^ (opp e)).

    (** [A^(x+e) = C] when [x + e ≠ 0]. *)
    Lemma mac_pow : forall (C : G) (x e : F), add x e <> zero -> (mac C x e) ^ (add x e) = C.
    Proof.
      intros * h; unfold mac; rewrite <-gpow_mul.
      replace (mul (inv (add x e)) (add x e)) with one by (field; exact h).
      apply gpow_one.
    Qed.

    (** [B = C · A^(−e) = A^x]: the relation that the pairing check of plain
        BBS would verify, and that the DLEQ proof certifies here. *)
    Lemma mac_relation : forall (C : G) (x e : F), add x e <> zero ->
      mac_B C (mac C x e) e = (mac C x e) ^ x.
    Proof.
      intros * h; unfold mac_B.
      set (A := mac C x e).
      assert (hC : gop (A ^ x) (A ^ e) = C) by (rewrite <-gpow_add; apply mac_pow; exact h).
      transitivity (gop (gop (A ^ x) (A ^ e)) (A ^ (opp e))); [rewrite hC; reflexivity |].
      rewrite <-gassoc, pow_opp, ginv_r, gid_r; reflexivity.
    Qed.

    (** The randomised credential: [Ā = A^(r_1·r_2)], [D = C^(r_2)] and
        [B̄ = Ā^(−e) · D^(r_1)]. *)
    Definition rand_A (A : G) (r1 r2 : F) : G := A ^ (mul r1 r2).
    Definition rand_D (C : G) (r2 : F) : G := C ^ r2.
    Definition rand_B (Abar D : G) (e r1 : F) : G := gop (Abar ^ (opp e)) (D ^ r1).

    (** The randomisation preserves the MAC relation: [B̄ = Ā^x], as
        [Ā^(−e) · C^(r_1·r_2) = A^(r_1·r_2·(x+e) − r_1·r_2·e)]. *)
    Lemma rand_relation : forall (C : G) (x e r1 r2 : F), add x e <> zero ->
      rand_B (rand_A (mac C x e) r1 r2) (rand_D C r2) e r1 = (rand_A (mac C x e) r1 r2) ^ x.
    Proof.
      intros * h; unfold rand_B, rand_A, rand_D, mac.
      repeat rewrite <-gpow_mul; rewrite <-gpow_add; f_equal; field; exact h.
    Qed.

    (** [D^(r_2⁻¹) = C] for [r_2 ≠ 0]; this is why [r_3 = r_2⁻¹] appears in the
        witness. *)
    Lemma rand_D_inv : forall (C : G) (r2 : F), r2 <> zero -> (rand_D C r2) ^ (inv r2) = C.
    Proof.
      intros * h; unfold rand_D; rewrite <-gpow_mul.
      replace (mul r2 (inv r2)) with one by (field; exact h); apply gpow_one.
    Qed.

  End Credential.

  (** ** The validity proof: one Okamoto statement in [G²] *)
  Section Validity.

    (** Additive key blinding [pk_Blind = g^(sk + r)] (the ECSchnorr variant of
        the paper). *)
    Definition pk_blind (g : G) (sk r : F) : G := g ^ (add sk r).

    (** Public target of the second equation:
        [g_0 · pk_Blind · ∏_(i ∈ D) g_i^(m_i)]. *)
    Definition target_P {d : nat} (g0 pkB : G) (gD : VG d) (mD : Vector.t F d) : G :=
      gop g0 (gop pkB (gexp gD mD)).

    (** The witness vector [(−e, r_1, r_3, r, −m_U)]. *)
    Definition validity_witness {u : nat} (e r1 r3 r : F) (mU : Vector.t F u) : Vector.t F (S (S (S (S u)))) :=
      opp e :: r1 :: r3 :: r :: Vector.map opp mU.

    (** The bases of the two equations: [row1 = (Ā, D, 1, 1, 1, ...)] for
        [B̄ = Ā^(−e) · D^(r_1)], and [row2 = (1, 1, D, g, g_U)] for
        [P = D^(r_3) · g^r · ∏ g_U^(−m_U)]. *)
    Definition row1 {u : nat} (Abar D : G) : VG (S (S (S (S u)))) := Abar :: D :: Vector.const gid (S (S u)).
    Definition row2 {u : nat} (D g : G) (gU : VG u) : VG (S (S (S (S u)))) := gid :: gid :: D :: g :: gU.

    (** The two rows and the two targets [(B̄, P)], in the format of
        [OkamotoRows]. *)
    Definition validity_rows {u : nat} (Abar D g : G) (gU : VG u) : Vector.t (VG (S (S (S (S u))))) 2 :=
      [row1 Abar D; row2 D g gU].
    Definition validity_targets (Bbar P : G) : VG 2 := [Bbar; P].

    (** The first row evaluates to [B̄] on the honest witness. *)
    Lemma row1_relation : forall (u : nat) (Abar D : G) (e r1 r3 r : F) (mU : Vector.t F u),
      gexp (row1 Abar D) (validity_witness e r1 r3 r mU) = rand_B Abar D e r1.
    Proof.
      intros; unfold row1, validity_witness, rand_B.
      rewrite mexp_cons, mexp_cons, (mexp_const_vid (HV := Hvec)), gid_r; reflexivity.
    Qed.

    (** The second row evaluates to [target_P] on the honest witness with
        [r_3 = r_2⁻¹], for a credential message [Cm] built with [pk = g^(sk)]. *)
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

    (** Verifier of the validity proof: [ext_verify] of [OkamotoRows] on the two
        rows. *)
    Definition validity_verify {u : nat} (Abar D g : G) (gU : VG u) (Bbar P : G)
      (t : @sigma_proto F (VG 2) 1 1 (S (S (S (S u))))) : bool :=
      ext_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)
        (validity_rows Abar D g gU) (validity_targets Bbar P) t.

    (** Honest validity transcript. *)
    Definition validity_real {u : nat} (e r1 r3 r : F) (mU : Vector.t F u) (Abar D g : G) (gU : VG u)
      (Bbar P : G) (us : Vector.t F (S (S (S (S u))))) (c : F) : @sigma_proto F (VG 2) 1 1 (S (S (S (S u)))) :=
      ext_real (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        (validity_witness e r1 r3 r mU) (validity_rows Abar D g gU) (validity_targets Bbar P) us c.

    (** Simulated validity transcript. *)
    Definition validity_simulator {u : nat} (Abar D g : G) (gU : VG u) (Bbar P : G)
      (us : Vector.t F (S (S (S (S u))))) (c : F) : @sigma_proto F (VG 2) 1 1 (S (S (S (S u)))) :=
      ext_simulator (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        (validity_rows Abar D g gU) (validity_targets Bbar P) us c.

    (** Distribution of honest validity transcripts. *)
    Definition validity_real_distribution {u : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (e r1 r3 r : F) (mU : Vector.t F u) (Abar D g : G) (gU : VG u) (Bbar P : G) (c : F) :
      dist (@sigma_proto F (VG 2) 1 1 (S (S (S (S u))))) :=
      ext_real_distribution (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        lf Hlfn (validity_witness e r1 r3 r mU) (validity_rows Abar D g gU) (validity_targets Bbar P) c.

    (** Distribution of simulated validity transcripts. *)
    Definition validity_simulator_distribution {u : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (Abar D g : G) (gU : VG u) (Bbar P : G) (c : F) : dist (@sigma_proto F (VG 2) 1 1 (S (S (S (S u))))) :=
      ext_simulator_distribution (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        lf Hlfn (validity_rows Abar D g gU) (validity_targets Bbar P) c.

    (** The honest holder's witness satisfies both rows, for the randomised
        credential [(Ā, D, B̄)] derived from a valid MAC, provided [x + e ≠ 0]
        and [r_2 ≠ 0]. *)
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

    (** Completeness of the validity proof for an honestly randomised
        credential. *)
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

    (** Simulated validity transcripts are always accepted. *)
    Theorem validity_simulator_completeness : forall (u : nat) (Abar D g : G) (gU : VG u) (Bbar P : G)
      (us : Vector.t F (S (S (S (S u))))) (c : F),
      validity_verify Abar D g gU Bbar P (validity_simulator Abar D g gU Bbar P us c) = true.
    Proof. intros *; apply ext_simulator_completeness. Qed.

    (** Special soundness: two accepting transcripts with the same announcement
        and distinct challenges yield a witness [w] for both equations. *)
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

    (** Special honest-verifier zero knowledge of the validity proof, as a
        permutation of distributions when [lf] enumerates the field. *)
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

    (** *** Multiplicative key blinding

        The ECDSA variant of the paper blinds the key multiplicatively,
        [pk_Blind = g^(sk·r)]. The second equation becomes
        [D^(r_3) · pk_Blind^(−1/r) · ∏ g_U^(−m_U) = g_0 · ∏_(i ∈ D) g_i^(m_i)]
        with target [target_F] and bases [row2_mul]. *)
    Definition pk_blind_mul (g : G) (sk r : F) : G := g ^ (mul sk r).
    Definition target_F {d : nat} (g0 : G) (gD : VG d) (mD : Vector.t F d) : G := gop g0 (gexp gD mD).
    Definition row2_mul {u : nat} (D pkB : G) (gU : VG u) : VG (S (S (S (S u)))) := gid :: gid :: D :: pkB :: gU.

    (** The multiplicative-blinding second row evaluates to [target_F] on the
        witness [(−e, r_1, r_2⁻¹, −r⁻¹, −m_U)], for [r ≠ 0] and [r_2 ≠ 0]. Only
        the relation is proved; the protocol instance is the same as above with
        [row2_mul]. *)
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

  (** ** Holder binding: Schnorr proof for [pk_Blind] *)
  Section HolderBinding.

    (** Schnorr verifier for [pk_Blind = g^(sk_B)]. *)
    Definition hb_verify (g pkB : G) (t : @sigma_proto F G 1 1 1) : bool :=
      accepting_conversation (gop := gop) (gpow := gpow) (Gdec := Gdec) g pkB t.

    (** Honest holder-binding transcript with witness [sk + r]. *)
    Definition hb_real (g : G) (sk r u c : F) : @sigma_proto F G 1 1 1 :=
      schnorr_protocol (add := add) (mul := mul) (gpow := gpow) (add sk r) g u c.

    (** Completeness of holder binding. *)
    Theorem hb_completeness : forall (g : G) (sk r u c : F),
      hb_verify g (pk_blind g sk r) (hb_real g sk r u c) = true.
    Proof. intros; apply schnorr_completeness; reflexivity. Qed.

    (** Special soundness of holder binding: extracts [sk_B] with
        [g^(sk_B) = pk_Blind]. *)
    Theorem hb_special_soundness : forall (g pkB a : G) (c1 r1 c2 r2 : F),
      c1 <> c2 ->
      hb_verify g pkB ([a]; [c1]; [r1]) = true ->
      hb_verify g pkB ([a]; [c2]; [r2]) = true ->
      exists skB : F, g ^ skB = pkB.
    Proof. intros * hc h1 h2; exact (special_soundness g pkB a c1 r1 c2 r2 hc h1 h2). Qed.

    (** Special HVZK of holder binding (distributions equal up to
        permutation). *)
    Theorem hb_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (g : G) (sk r c : F),
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation (schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn (add sk r) g c)
        (simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn g (pk_blind g sk r) c).
    Proof.
      intros * hnd hall.
      exact (special_honest_verifier_zkp_enum (add sk r) g (pk_blind g sk r) eq_refl lf Hlfn c hnd hall).
    Qed.

  End HolderBinding.

  (** ** The Issuer's DLEQ proof: Chaum–Pedersen for [B̄ = Ā^x ∧ pk_I = g̃^x]

      The paper's three issuance options (Issuer online, or blind proofs via
      oblivious issuance) all leave the verifier with the same Chaum–Pedersen
      transcript, which is what is modelled here. *)
  Section DLEQ.

    (** Chaum–Pedersen verifier for bases [g̃], [Ā] and values [pk_I], [B̄]. *)
    Definition dleq_verify (gt pkI Abar Bbar : G) (t : @sigma_proto F G 2 1 1) : bool :=
      cp_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) gt pkI Abar Bbar t.

    (** The transcript with the reconstructed announcement
        [(g̃^ρ · pk_I^(−c), Ā^ρ · B̄^(−c))] always verifies. *)
    Theorem dleq_reconstruct_accepting : forall (gt pkI Abar Bbar : G) (c ρ : F),
      dleq_verify gt pkI Abar Bbar (cp_transcript (opp := opp) (gop := gop) (gpow := gpow) gt pkI Abar Bbar c ρ) = true.
    Proof. intros; apply cp_reconstruct_accepting. Qed.

    (** Special soundness: extracts [x] with [g̃^x = pk_I] and [Ā^x = B̄]. *)
    Theorem dleq_special_soundness : forall (gt pkI Abar Bbar : G) (a : VG 2) (ca ra cb rb : F),
      ca <> cb ->
      dleq_verify gt pkI Abar Bbar (a; [ca]; [ra]) = true ->
      dleq_verify gt pkI Abar Bbar (a; [cb]; [rb]) = true ->
      exists x : F, gt ^ x = pkI /\ Abar ^ x = Bbar.
    Proof. intros * hc h1 h2; exact (cp_special_soundness gt pkI Abar Bbar a ca ra cb rb hc h1 h2). Qed.

    (** Special HVZK of the DLEQ proof. *)
    Theorem dleq_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (gt pkI Abar Bbar : G) (x c : F),
      gt ^ x = pkI -> Abar ^ x = Bbar ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation
        (generalised_cp_schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn x gt Abar c)
        (generalised_cp_simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn gt Abar pkI Bbar c).
    Proof. intros * h1 h2 hnd hall; exact (cp_shvzk lf Hlfn gt pkI Abar Bbar x c h1 h2 hnd hall). Qed.

  End DLEQ.

  (** ** Extraction of a credential (Appendix C) *)
  Section Extraction.

    (** From a witness [(w_0, w_1, w_2, w_3, w_U)] of the two validity equations,
        the DLEQ key [x] ([Ā^x = B̄]) and the blinded key [sk_B]
        ([g^(sk_B) = pk_Blind]), with [w_1 ≠ 0] and [w_2 ≠ 0]:

        [[
          (Ā^(w_2/w_1))^(x − w_0) = Cm(g_0, g^(sk_B − w_3), disclosed, −w_U),
        ]]

        i.e. [(Ā^(w_2/w_1), −w_0)] is a valid MAC with key [x] on the
        holder key [sk_B − w_3], the disclosed attributes and the undisclosed
        attributes [−w_U]. For the honest witness this is
        [(A, e)] on [(sk, m)].

        Proof idea: [Ā^(x − w_0) = D^(w_1)] from the first equation and
        [Ā^x = B̄]; and [D^(w_2) = P · (g^(w_3) · ∏ g_U^(w_U))⁻¹] from the second.
        Combining the two after raising to [w_2/w_1] gives the claim. *)
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
      (* Ā^(x − w_0) = D^(w_1), from Ā^x = B̄ = Ā^(w_0) · D^(w_1). *)
      assert (hAD : Abar ^ (add x (opp w0)) = D ^ w1).
      { rewrite gpow_add, hx, <-h1, (gcomm (Abar ^ w0) (D ^ w1)), <-gassoc, pow_opp, ginv_r, gid_r;
        reflexivity. }
      rewrite <-gpow_mul.
      replace (mul (mul w2 (inv w1)) (add x (opp w0))) with (mul (add x (opp w0)) (mul w2 (inv w1)))
        by (field; exact hw1).
      rewrite gpow_mul, hAD, <-gpow_mul.
      replace (mul w1 (mul w2 (inv w1))) with w2 by (field; exact hw1).
      set (Y := gop (g ^ w3) (gexp gU wU)) in *.
      (* D^(w_2) = P · (g^(w_3) · ∏ g_U^(w_U))⁻¹, from the second equation. *)
      assert (hD : D ^ w2 = gop (target_P g0 pkB gD mD) (ginv Y)).
      { rewrite <-h2, <-gassoc, ginv_r, gid_r; reflexivity. }
      rewrite hD; unfold target_P, Cm, Y; rewrite mexp_app, ginv_gop, mexp_map_opp, <-hpk.
      set (MD := gexp gD mD); set (MU := gexp gU wU).
      (* Expand P and Cm and match the factors. *)
      assert (hs : g ^ (sub skB w3) = gop (g ^ skB) (ginv (g ^ w3))).
      { rewrite <-pow_opp, <-gpow_add; f_equal; field. }
      rewrite hs, <-(gassoc g0 (gop (g ^ skB) MD) (gop (ginv (g ^ w3)) (ginv MU))),
        (gop4 (g ^ skB) MD (ginv (g ^ w3)) (ginv MU)); reflexivity.
    Qed.

    (** The degenerate case [w_1 = 0]: then [B̄ = Ā^(w_0)] and [Ā^x = B̄] with
        [Ā ≠ gid] force [x = w_0], so the witness reveals the Issuer's secret
        key. *)
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

    (** Soundness of the whole presentation. Assume [Ā ≠ gid] and, for each of
        the validity, DLEQ and holder-binding proofs, two accepting transcripts
        with the same announcement and distinct challenges. Then there are
        [x], [sk_B] and a validity witness [(w_0, w_1, w_2, w_3, w_U)] with
        [g̃^x = pk_I], [g^(sk_B) = pk_Blind], and one of:

        - [w_1 = 0] and [x = w_0]: the Issuer's key is extracted;
        - [w_2 = 0] and [g^(w_3) · ∏ g_U^(w_U) = target_P]: a representation of
          the public target in the bases [g], [g_U], which breaks discrete
          logarithm assumptions on the generators;
        - a valid MAC on [(sk_B − w_3, disclosed attributes, −w_U)]
          ([credential_extraction]), i.e. a forgery unless the holder owns a
          credential.

        Proof: combine the three special-soundness results and split on
        whether [w_1] and [w_2] are zero. *)
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
      (* Extract the three witnesses. *)
      destruct (validity_special_soundness _ _ _ _ _ _ _ _ _ _ _ _ hc h1 h2) as (w & hw1 & hw2).
      destruct (dleq_special_soundness _ _ _ _ _ _ _ _ _ hcd hd1 hd2) as (x & hx1 & hx2).
      destruct (hb_special_soundness _ _ _ _ _ _ _ hch hh1 hh2) as (skB & hsk).
      destruct (vector_inv_S w) as (w0 & wa & ->); destruct (vector_inv_S wa) as (w1 & wb & ->).
      destruct (vector_inv_S wb) as (w2 & wc & ->); destruct (vector_inv_S wc) as (w3 & wU & ->).
      unfold row1, row2 in hw1, hw2.
      rewrite mexp_cons, mexp_cons, (mexp_const_vid (HV := Hvec)), gid_r in hw1.
      rewrite mexp_cons, mexp_cons, mexp_cons, mexp_cons, gid_pow, gid_pow, gid_l, gid_l in hw2.
      exists x, skB, w0, w1, w2, w3, wU; split; [exact hx1 | split; [exact hsk |]].
      (* Case analysis on w_1 = 0 and w_2 = 0. *)
      destruct (Fdec w1 zero) as [hz1 | hn1].
      + left; split; [exact hz1 |].
        exact (issuer_key_extraction Abar Bbar D x w0 w1 hA hx2 hw1 hz1).
      + destruct (Fdec w2 zero) as [hz2 | hn2].
        * right; left; split; [exact hz2 |]; rewrite hz2, gpow_zero, gid_l in hw2; exact hw2.
        * right; right; exact (credential_extraction d u g g0 Abar Bbar D pkB gD mD gU x skB w0 w1 w2 w3 wU hx2 hsk hw1 hw2 hn1 hn2).
    Qed.

  End Extraction.

  (** ** Statistical anonymity of the randomised credential *)
  Section Anonymity.

    (** The randomised pair [(Ā, D) = (A^(r_1·r_2), C^(r_2))] as a function of
        the random vector [(r_1, r_2)]. *)
    Definition randomise (A C : G) (v : Vector.t F 2) : G * G :=
      (A ^ (mul (Vector.hd v) (Vector.hd (Vector.tl v))), C ^ (Vector.hd (Vector.tl v))).

    (** The distribution of [(Ā, D)] when [(r_1, r_2)] is drawn uniformly (with
        replacement) from [lf]. *)
    Definition randomised_distribution (lf : list F) (Hlfn : lf <> List.nil) (A C : G) : dist (G * G) :=
      List.map (fun '(v, p) => (randomise A C v, p))
        (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn) 2).

    (** Mapping a composite function over the first components of a
        distribution equals mapping twice. *)
    Lemma map_pair_compose : forall {A B C P : Type} (f : A -> B) (k : B -> C) (l : list (A * P)),
      List.map (fun '(v, p) => (k (f v), p)) l =
      List.map (fun '(v, p) => (k v, p)) (List.map (fun '(v, p) => (f v, p)) l).
    Proof. intros; induction l as [| (v & p) l ih]; [reflexivity | cbn; rewrite ih; reflexivity]. Qed.

    (** Eta law for vectors of length two. *)
    Lemma eta2 : forall v : Vector.t F 2, v = [Vector.hd v; Vector.hd (Vector.tl v)].
    Proof.
      intro v; destruct (vector_inv_S v) as (r1 & v' & ->).
      destruct (vector_inv_S v') as (r2 & v'' & ->); rewrite (vector_inv_0 v''); reflexivity.
    Qed.

    (** Anonymity: for credentials [A = g^a], [C = g^c] and [A' = g^(a')],
        [C' = g^(c')] with [a, c, a', c'] all non-zero, and [lf] enumerating
        the field without duplicates, the distributions of the randomised pair
        [(Ā, D)] are equal up to permutation. Since [B̄ = Ā^x] is determined by
        [Ā], the randomised credential reveals nothing about which credential
        was used (Game 5 of the paper's anonymity proof).

        Proof idea: the map
        [(r_1, r_2) ↦ (r_1 · a·c'/(a'·c), r_2 · c/c')] is a bijection of [F²]
        that turns the randomisation of [(A, C)] into that of [(A', C')];
        [repeat_uniform_bijection_perm] shows it permutes the uniform
        distribution. *)
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
