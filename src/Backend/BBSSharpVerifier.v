(** * Fiat–Shamir verifier for [BBS#] credential presentations *)

(** This file defines the executable verifier for presentations of [BBS#]
    anonymous credentials (Desmoulins, Dumanois, Kane, Traoré, ePrint
    2025/619: Section 3.3 Show/Verify, Section 4 for the pairing-free check,
    Appendix B Figures 6–8) and links each of its checks to an interactive
    Sigma protocol proved correct in [Crypto.BBSSharp].

    A presentation consists of the disclosed attributes [m_D], a blinded
    holder key [pk_B], the randomised MAC components [Ā], [B̄], [D], and three
    non-interactive proofs, each published as a challenge and responses:

    - π_HB (holder binding), a Schnorr proof of knowledge of [log_g pk_B];
      the verifier reconstructs [com' = g^ρ · pk_B^{−c}] (Figure 7);
    - π_validity, an Okamoto-style proof for two linear relations in [G²]:
      [B̄ = Ā^{ρ_1} D^{ρ_2}] and [P = D^{ρ_3} · g^{resp} · ∏ g_i^{resp_i}],
      where [P] is the public target built from the issuer base [g_0], the
      holder key and the disclosed attributes ([target_P]); the verifier
      reconstructs both announcements with exponent [−c] (Figure 8);
    - π_DLEQ, a Chaum–Pedersen proof that [log_{g̃} pk_I = log_Ā B̄], i.e.
      that [B̄ = Ā^x] for the issuer secret key [x]; the verifier
      reconstructs [g̃^ρ pk_I^{−c}] and [Ā^ρ B̄^{−c}] (Figure 6). This replaces
      the pairing check of plain BBS and can be obtained from the issuer
      online or as a blind proof in advance; the verifier's check is the
      same.

    Each proof is accepted iff its challenge equals the hash of the
    reconstructed announcement(s). The verifier additionally checks
    [Ā ≠ 1].

    How the challenges are derived. The hash functions [H_2], [H_3],
    [H_4] of the paper are parameters ([G -> G -> F], [G -> F],
    [VG 2 -> F]) of the verifier. They receive only the reconstructed
    announcements; the nonce, disclosed attributes and other public data are
    expected to be closed over by the caller. In the extracted driver
    (src/Executable/Bbssharpverifier/main.ml, instance in
    [Examples.BBSSharpIns] over P-256) they are implemented in OCaml as
    [hash_to_scalar] from the IETF BBS draft on top of SHA-256
    (expand_message_xmd), so the hashing and serialisation are trusted,
    unverified code.

    What is proved. [verify_presentation_accepting]: if
    [verify_presentation] returns [true], then [Ā ≠ 1], each challenge
    equals the oracle value on the reconstructed announcement, and each
    reconstructed triple is an accepting transcript of the corresponding
    interactive protocol of [Crypto.BBSSharp] ([hb_verify],
    [validity_verify], [dleq_verify]). The accepting-transcript part holds
    for every challenge and response by construction; the security content
    therefore comes from the interactive theorems in [Crypto.BBSSharp]
    ([hb_special_soundness], [validity_special_soundness],
    [dleq_special_soundness], [presentation_soundness],
    [credential_extraction], and the SHVZK results), which talk about pairs
    of accepting transcripts with a common announcement.

    What is NOT verified. The Fiat–Shamir transformation itself (random
    oracle, forking lemma) is not formalised, so no theorem says that a
    cheating prover cannot produce an accepted presentation. Group
    membership of the received points, the correct encoding of the hash
    inputs, and the binding of the proofs to the nonce/context are outside
    the formal statements. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool List setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows BBSSharp.
From Utility Require Import Util.
Import VectorNotations.

(** ** Verifier over an abstract prime-order group *)

(** [F] is the scalar field and [G] the group, presented as an
    [F]-vector space (written multiplicatively via the local notations:
    [g ^ x] is [gpow g x], [gop] the group law, [gid] the identity). [Fdec]
    and [Gdec] decide equality and make the checks executable. *)
Section BBSSharpVerifier.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  (** Local notations: [^] for exponentiation, [(a; c; r)] for a Sigma
      transcript, [gexp] for multi-exponentiation and [VG m] for vectors of
      [m] group elements; the remaining ones name group laws used in the
      proofs. *)
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
  Local Notation gid_r := (@right_identity G (@eq G) gop gid
    (@monoid_is_right_identity G (@eq G) gop gid gmonoid)).
  Local Notation ginv_l := (@left_inverse G (@eq G) gop gid ginv
    (@group_is_left_inverse G (@eq G) gop gid ginv ggroup)).
  Local Notation pow_opp := (pow_opp (Hvec := Hvec)).

  (** Converts a decision procedure result into a boolean (true on [left]). *)
  Definition bool_of_dec {P Q : Prop} (d : {P} + {Q}) : bool :=
    match d with left _ => true | right _ => false end.

  (** If [bool_of_dec (dec x y)] is [true], then [x = y]. *)
  Lemma bool_of_dec_true : forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (x y : A),
    bool_of_dec (dec x y) = true -> x = y.
  Proof. intros * h; destruct (dec x y); [assumption | discriminate]. Qed.

  (** *** Holder binding (π_HB): Schnorr proof *)

  (** [schnorr_reconstruct g h c ρ = g^ρ · h^{−c}], the announcement implied
      by challenge [c] and response [ρ] under the convention [ρ = w + c·x]
      for the statement [h = g^x]. *)
  Definition schnorr_reconstruct (g h : G) (c ρ : F) : G := gop (g ^ ρ) (h ^ (opp c)).

  (** The reconstructed announcement with challenge [c] and response [ρ]
      is accepted by the Schnorr verifier [accepting_conversation]:
      [g^ρ = (g^ρ h^{−c}) · h^c], by associativity, [h^{−c} = (h^c)⁻¹] and
      the inverse law. Holds for all [c], [ρ]. *)
  Lemma schnorr_reconstruct_accepting : forall (g h : G) (c ρ : F),
    accepting_conversation (gop := gop) (gpow := gpow) (Gdec := Gdec) g h
      ([schnorr_reconstruct g h c ρ]; [c]; [ρ]) = true.
  Proof.
    intros; unfold accepting_conversation; cbn [Vector.hd Vector.caseS]; rewrite dec_true.
    unfold schnorr_reconstruct; rewrite <-gassoc, pow_opp, ginv_l, gid_r; reflexivity.
  Qed.

  (** Checks the holder-binding proof [(c, ρ)] for [pk_B]: accept iff
      [c = H3(g^ρ · pk_B^{−c})]. *)
  Definition verify_hb (H3 : G -> F) (g pkB : G) (c ρ : F) : bool :=
    bool_of_dec (Fdec c (H3 (schnorr_reconstruct g pkB c ρ))).

  (** If [verify_hb] accepts, then the challenge is the oracle value on the
      reconstruction and the reconstructed transcript is accepted by
      [hb_verify] (the Schnorr verifier of [Crypto.BBSSharp]). *)
  Theorem verify_hb_accepting : forall (H3 : G -> F) (g pkB : G) (c ρ : F),
    verify_hb H3 g pkB c ρ = true ->
    c = H3 (schnorr_reconstruct g pkB c ρ) /\
    hb_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) g pkB ([schnorr_reconstruct g pkB c ρ]; [c]; [ρ]) = true.
  Proof.
    intros * hv; unfold verify_hb in hv; apply bool_of_dec_true in hv.
    split; [exact hv | apply schnorr_reconstruct_accepting].
  Qed.

  (** *** Issuer key (π_DLEQ): Chaum–Pedersen proof *)

  (** Checks a DLEQ proof [(c, ρ)] for [log_{g̃} pk_I = log_Ā B̄]: accept iff
      [c = H2(g̃^ρ pk_I^{−c}, Ā^ρ B̄^{−c})]. *)
  Definition verify_dleq (H2 : G -> G -> F) (gt pkI Abar Bbar : G) (c ρ : F) : bool :=
    bool_of_dec (Fdec c (H2 (gop (gt ^ ρ) (pkI ^ (opp c))) (gop (Abar ^ ρ) (Bbar ^ (opp c))))).

  (** If [verify_dleq] accepts, then the challenge is the oracle value on
      the two reconstructed announcements, and [cp_transcript] (the
      reconstructed Chaum–Pedersen transcript) is accepted by
      [dleq_verify]; the second part is [dleq_reconstruct_accepting]. *)
  Theorem verify_dleq_accepting : forall (H2 : G -> G -> F) (gt pkI Abar Bbar : G) (c ρ : F),
    verify_dleq H2 gt pkI Abar Bbar c ρ = true ->
    c = H2 (gop (gt ^ ρ) (pkI ^ (opp c))) (gop (Abar ^ ρ) (Bbar ^ (opp c))) /\
    dleq_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) gt pkI Abar Bbar
      (cp_transcript (opp := opp) (gop := gop) (gpow := gpow) gt pkI Abar Bbar c ρ) = true.
  Proof.
    intros * hv; unfold verify_dleq in hv; apply bool_of_dec_true in hv.
    split; [exact hv | apply dleq_reconstruct_accepting].
  Qed.

  (** *** Validity proof (π_validity): multi-row Okamoto proof *)

  (** Generic check for a proof of knowledge of one exponent vector [rs]
      satisfying [m] linear relations [Ts_j = ∏_i (Bs_j)_i^{rs_i}]: accept iff
      [c = H(A)] where [A = ext_reconstruct c Bs Ts rs] is the vector of [m]
      reconstructed announcements [∏_i (Bs_j)_i^{rs_i} · Ts_j^{−c}]
      (from [Crypto.OkamotoRows]). *)
  Definition verify_rows {K m : nat} (H : VG m -> F) (Bs : Vector.t (VG K) m) (Ts : VG m) (c : F)
    (rs : Vector.t F K) : bool :=
    bool_of_dec (Fdec c (H (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c Bs Ts rs))).

  (** If [verify_rows] accepts, the challenge is [H] of the reconstruction
      and the reconstructed transcript is accepted by [ext_verify]
      ([ext_reconstruct_accepting]). Needs at least two exponents
      ([S (S n)]), as the Okamoto protocol does. *)
  Theorem verify_rows_accepting : forall (n m : nat) (H : VG m -> F) (Bs : Vector.t (VG (S (S n))) m)
    (Ts : VG m) (c : F) (rs : Vector.t F (S (S n))),
    verify_rows H Bs Ts c rs = true ->
    c = H (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c Bs Ts rs) /\
    ext_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) Bs Ts
      ([ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c Bs Ts rs]; [c]; rs) = true.
  Proof.
    intros * hv; unfold verify_rows in hv; apply bool_of_dec_true in hv.
    split; [exact hv | apply ext_reconstruct_accepting].
  Qed.

  (** The validity check of a presentation: [verify_rows] with the two rows
      [validity_rows Ā D g g_U] and targets [validity_targets B̄ P] defined in
      [Crypto.BBSSharp]. The response vector has length [4 + u], where [u]
      is the number of undisclosed attributes. *)
  Definition verify_validity {u : nat} (H4 : VG 2 -> F) (Abar D g : G) (gU : VG u) (Bbar P : G) (c : F)
    (rs : Vector.t F (S (S (S (S u))))) : bool :=
    verify_rows H4 (validity_rows (gid := gid) Abar D g gU) (validity_targets Bbar P) c rs.

  (** Specialisation of [verify_rows_accepting]: acceptance of
      [verify_validity] gives [c = H4(A)] and an accepting
      [validity_verify] transcript. *)
  Theorem verify_validity_accepting : forall (u : nat) (H4 : VG 2 -> F) (Abar D g : G) (gU : VG u) (Bbar P : G)
    (c : F) (rs : Vector.t F (S (S (S (S u))))),
    verify_validity H4 Abar D g gU Bbar P c rs = true ->
    let A := ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c
      (validity_rows (gid := gid) Abar D g gU) (validity_targets Bbar P) rs in
    c = H4 A /\
    validity_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) Abar D g gU Bbar P ([A]; [c]; rs) = true.
  Proof. intros * hv; cbv zeta; exact (verify_rows_accepting _ _ _ _ _ _ _ hv). Qed.

  (** ** Full presentation *)

  (** A [BBS#] presentation with [d] disclosed and [u] undisclosed
      attributes: the disclosed attribute values [pr_mD], the blinded holder
      key [pr_pkB], the holder-binding proof [(pr_hb_c, pr_hb_r)], the
      randomised credential [(pr_Abar, pr_Bbar, pr_D)], the validity proof
      [(pr_c, pr_rs)] and the DLEQ proof [(pr_dleq_c, pr_dleq_r)]. *)
  Record presentation {d u : nat} : Type := mk_presentation {
    pr_mD : Vector.t F d;
    pr_pkB : G;
    pr_hb_c : F; pr_hb_r : F;
    pr_Abar : G; pr_Bbar : G; pr_D : G;
    pr_c : F; pr_rs : Vector.t F (S (S (S (S u))));
    pr_dleq_c : F; pr_dleq_r : F
  }.

  (** [verify_presentation] accepts iff [Ā ≠ 1] and all three proofs verify,
      with the validity target [P = target_P g0 pk_B g_D m_D] recomputed from
      the disclosed attributes. [g], [g̃], [g0] and [g_D], [g_U] are the
      public generators and [pk_I] the issuer public key. *)
  Definition verify_presentation {d u : nat} (H2 : G -> G -> F) (H3 : G -> F) (H4 : VG 2 -> F)
    (g gt g0 pkI : G) (gD : VG d) (gU : VG u) (pr : @presentation d u) : bool :=
    let P := target_P (gid := gid) (gop := gop) (gpow := gpow) g0 (pr_pkB pr) gD (pr_mD pr) in
    negb (bool_of_dec (Gdec (pr_Abar pr) gid)) &&
    verify_hb H3 g (pr_pkB pr) (pr_hb_c pr) (pr_hb_r pr) &&
    verify_validity H4 (pr_Abar pr) (pr_D pr) g gU (pr_Bbar pr) P (pr_c pr) (pr_rs pr) &&
    verify_dleq H2 gt pkI (pr_Abar pr) (pr_Bbar pr) (pr_dleq_c pr) (pr_dleq_r pr).

  (** Main link theorem. If [verify_presentation] returns [true], then
      [Ā ≠ 1] and, for each of π_HB, π_validity and π_DLEQ, the published
      challenge equals the oracle value on the reconstructed announcement(s)
      and the reconstructed transcript is accepting for the interactive
      protocol of [Crypto.BBSSharp]. Proof: split the conjunction computed by
      [verify_presentation] and apply the three per-proof theorems. Two
      such transcripts with equal announcements and distinct challenges are
      exactly the hypotheses of [presentation_soundness] in
      [Crypto.BBSSharp]. *)
  Theorem verify_presentation_accepting : forall (d u : nat) (H2 : G -> G -> F) (H3 : G -> F) (H4 : VG 2 -> F)
    (g gt g0 pkI : G) (gD : VG d) (gU : VG u) (pr : @presentation d u),
    verify_presentation H2 H3 H4 g gt g0 pkI gD gU pr = true ->
    let P := target_P (gid := gid) (gop := gop) (gpow := gpow) g0 (pr_pkB pr) gD (pr_mD pr) in
    let A := ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (pr_c pr)
      (validity_rows (gid := gid) (pr_Abar pr) (pr_D pr) g gU) (validity_targets (pr_Bbar pr) P) (pr_rs pr) in
    pr_Abar pr <> gid /\
    (pr_hb_c pr = H3 (schnorr_reconstruct g (pr_pkB pr) (pr_hb_c pr) (pr_hb_r pr)) /\
     hb_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) g (pr_pkB pr)
       ([schnorr_reconstruct g (pr_pkB pr) (pr_hb_c pr) (pr_hb_r pr)]; [pr_hb_c pr]; [pr_hb_r pr]) = true) /\
    (pr_c pr = H4 A /\
     validity_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) (pr_Abar pr) (pr_D pr) g gU
       (pr_Bbar pr) P ([A]; [pr_c pr]; pr_rs pr) = true) /\
    (pr_dleq_c pr = H2 (gop (gt ^ pr_dleq_r pr) (pkI ^ (opp (pr_dleq_c pr))))
        (gop (pr_Abar pr ^ pr_dleq_r pr) (pr_Bbar pr ^ (opp (pr_dleq_c pr)))) /\
     dleq_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) gt pkI (pr_Abar pr) (pr_Bbar pr)
       (cp_transcript (opp := opp) (gop := gop) (gpow := gpow) gt pkI (pr_Abar pr) (pr_Bbar pr)
         (pr_dleq_c pr) (pr_dleq_r pr)) = true).
  Proof.
    intros * hv; cbv zeta; unfold verify_presentation in hv.
    apply andb_true_iff in hv; destruct hv as (hv & hd).
    apply andb_true_iff in hv; destruct hv as (hv & hval).
    apply andb_true_iff in hv; destruct hv as (hne & hhb).
    split; [| split; [| split]].
    + intro e; destruct (Gdec (pr_Abar pr) gid); [discriminate | contradiction].
    + exact (verify_hb_accepting _ _ _ _ _ hhb).
    + exact (verify_validity_accepting _ _ _ _ _ _ _ _ _ _ hval).
    + exact (verify_dleq_accepting _ _ _ _ _ _ _ hd).
  Qed.

End BBSSharpVerifier.
