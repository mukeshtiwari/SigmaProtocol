(* Fiat–Shamir verification of BBS# presentations (Desmoulins, Dumanois,
   Kane, Traoré, ePrint 2025/619: Section 3.3 Show/Verify, Section 4 for the
   pairing-free check, Appendix B Figures 6–8), linked to the protocol
   instances of Crypto/BBSSharp.v.

   A presentation VP = ({m_i}_{i∈D}, pk_Blind, π_HB, Ā, B̄, D, π_validity) comes
   with the discrete-logarithm-equality proof π_DLEQ that B̄ = Ā^x for the
   Issuer's key (from the Issuer online, or a blind proof obtained in
   advance; the verifier's check is the same). The verifier receives the
   published values only and reconstructs the announcements from the
   responses and the challenges:

     π_HB       = (c, ρ)                 com' = g^ρ pk_Blind^{−c}          (Figure 7)
     π_validity = (c, ρ_1, ρ_2, ρ_3, {resp_i}, resp)
                  com'_1 = Ā^{ρ_1} D^{ρ_2} B̄^{−c},
                  com'_2 = D^{ρ_3} ∏ g_i^{resp_i} g^{resp} P^{−c}          (Figure 8)
     π_DLEQ     = (c, ρ)                 com'_1 = g̃^ρ pk_I^{−c}, com'_2 = Ā^ρ B̄^{−c}  (Figure 6)

   and checks each challenge against the hash of its reconstruction. The
   hash functions H_2, H_3, H_4 of the paper are oracles supplied by the
   driver (they take the reconstructed announcements; the nonce, the
   disclosed attributes and the other public data are fixed in the
   closures). The link theorems: a verified proof yields an accepting
   transcript of the library protocol (Schnorr, the Okamoto statement in
   G², Chaum–Pedersen) whose challenge is the oracle's value on the
   reconstructed announcement. As everywhere in this development the
   theorems are about the interactive protocols. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool List setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows BBSSharp.
From Utility Require Import Util.
Import VectorNotations.

Section BBSSharpVerifier.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

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

  Definition bool_of_dec {P Q : Prop} (d : {P} + {Q}) : bool :=
    match d with left _ => true | right _ => false end.

  Lemma bool_of_dec_true : forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (x y : A),
    bool_of_dec (dec x y) = true -> x = y.
  Proof. intros * h; destruct (dec x y); [assumption | discriminate]. Qed.

  (* ---- Schnorr reconstruction (π_HB) ---- *)

  Definition schnorr_reconstruct (g h : G) (c ρ : F) : G := gop (g ^ ρ) (h ^ (opp c)).

  Lemma schnorr_reconstruct_accepting : forall (g h : G) (c ρ : F),
    accepting_conversation (gop := gop) (gpow := gpow) (Gdec := Gdec) g h
      ([schnorr_reconstruct g h c ρ]; [c]; [ρ]) = true.
  Proof.
    intros; unfold accepting_conversation; cbn [Vector.hd Vector.caseS]; rewrite dec_true.
    unfold schnorr_reconstruct; rewrite <-gassoc, pow_opp, ginv_l, gid_r; reflexivity.
  Qed.

  Definition verify_hb (H3 : G -> F) (g pkB : G) (c ρ : F) : bool :=
    bool_of_dec (Fdec c (H3 (schnorr_reconstruct g pkB c ρ))).

  Theorem verify_hb_accepting : forall (H3 : G -> F) (g pkB : G) (c ρ : F),
    verify_hb H3 g pkB c ρ = true ->
    c = H3 (schnorr_reconstruct g pkB c ρ) /\
    hb_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) g pkB ([schnorr_reconstruct g pkB c ρ]; [c]; [ρ]) = true.
  Proof.
    intros * hv; unfold verify_hb in hv; apply bool_of_dec_true in hv.
    split; [exact hv | apply schnorr_reconstruct_accepting].
  Qed.

  (* ---- Chaum–Pedersen reconstruction (π_DLEQ) ---- *)

  Definition verify_dleq (H2 : G -> G -> F) (gt pkI Abar Bbar : G) (c ρ : F) : bool :=
    bool_of_dec (Fdec c (H2 (gop (gt ^ ρ) (pkI ^ (opp c))) (gop (Abar ^ ρ) (Bbar ^ (opp c))))).

  Theorem verify_dleq_accepting : forall (H2 : G -> G -> F) (gt pkI Abar Bbar : G) (c ρ : F),
    verify_dleq H2 gt pkI Abar Bbar c ρ = true ->
    c = H2 (gop (gt ^ ρ) (pkI ^ (opp c))) (gop (Abar ^ ρ) (Bbar ^ (opp c))) /\
    dleq_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) gt pkI Abar Bbar
      (cp_transcript (opp := opp) (gop := gop) (gpow := gpow) gt pkI Abar Bbar c ρ) = true.
  Proof.
    intros * hv; unfold verify_dleq in hv; apply bool_of_dec_true in hv.
    split; [exact hv | apply dleq_reconstruct_accepting].
  Qed.

  (* ---- rows with a scalar challenge (π_validity) ---- *)

  Definition verify_rows {K m : nat} (H : VG m -> F) (Bs : Vector.t (VG K) m) (Ts : VG m) (c : F)
    (rs : Vector.t F K) : bool :=
    bool_of_dec (Fdec c (H (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c Bs Ts rs))).

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

  Definition verify_validity {u : nat} (H4 : VG 2 -> F) (Abar D g : G) (gU : VG u) (Bbar P : G) (c : F)
    (rs : Vector.t F (S (S (S (S u))))) : bool :=
    verify_rows H4 (validity_rows (gid := gid) Abar D g gU) (validity_targets Bbar P) c rs.

  Theorem verify_validity_accepting : forall (u : nat) (H4 : VG 2 -> F) (Abar D g : G) (gU : VG u) (Bbar P : G)
    (c : F) (rs : Vector.t F (S (S (S (S u))))),
    verify_validity H4 Abar D g gU Bbar P c rs = true ->
    let A := ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c
      (validity_rows (gid := gid) Abar D g gU) (validity_targets Bbar P) rs in
    c = H4 A /\
    validity_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) Abar D g gU Bbar P ([A]; [c]; rs) = true.
  Proof. intros * hv; cbv zeta; exact (verify_rows_accepting _ _ _ _ _ _ _ hv). Qed.

  (* ---- the whole presentation ---- *)

  Record presentation {d u : nat} : Type := mk_presentation {
    pr_mD : Vector.t F d;          (* disclosed attributes *)
    pr_pkB : G;                    (* pk_Blind *)
    pr_hb_c : F; pr_hb_r : F;      (* π_HB *)
    pr_Abar : G; pr_Bbar : G; pr_D : G;
    pr_c : F; pr_rs : Vector.t F (S (S (S (S u))));   (* π_validity: (c, ρ_1, ρ_2, ρ_3, resp, {resp_i}) *)
    pr_dleq_c : F; pr_dleq_r : F   (* π_DLEQ *)
  }.

  Definition verify_presentation {d u : nat} (H2 : G -> G -> F) (H3 : G -> F) (H4 : VG 2 -> F)
    (g gt g0 pkI : G) (gD : VG d) (gU : VG u) (pr : @presentation d u) : bool :=
    let P := target_P (gid := gid) (gop := gop) (gpow := gpow) g0 (pr_pkB pr) gD (pr_mD pr) in
    negb (bool_of_dec (Gdec (pr_Abar pr) gid)) &&
    verify_hb H3 g (pr_pkB pr) (pr_hb_c pr) (pr_hb_r pr) &&
    verify_validity H4 (pr_Abar pr) (pr_D pr) g gU (pr_Bbar pr) P (pr_c pr) (pr_rs pr) &&
    verify_dleq H2 gt pkI (pr_Abar pr) (pr_Bbar pr) (pr_dleq_c pr) (pr_dleq_r pr).

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
