(** * [BBS#] anonymous credentials at P-256 *)

(** This file instantiates [BBS#] ([Crypto/BBSSharp.v] and
[Backend/BBSSharpVerifier.v]) at NIST P-256 (secp256r1, the curve of the
paper's implementation), over the curve group of [Curve/P256.v] with
[Z/nZ] as scalar field. Both sides are exported: the Issuer's and holder's
computations (the MAC, its randomisation and the three real provers) and
the verifier, so that the OCaml driver [Executable/Bbssharpverifier] can
produce presentations with the extracted prover and check them with the
extracted verifier. There are no published [BBS#] test vectors. The
hash-to-scalar oracles and the derivation of the generators are done by
the driver and are trusted. The file is extracted by
[src/Extraction/BBSSharplib]. *)

(** ** How a [BBS#] credential works

[BBS#] (Desmoulins, Dumanois, Kane and Traoré, ePrint 2025/619) is a
pairing-free variant of BBS anonymous credentials, so that the holder's
key can live in the secure element of a phone, and its showings are
unlinkable.

The credential is an algebraic MAC. With generators [g], [g̃], [g₀],
[g₁ … g_n], the Issuer's key [x] ([pk_I = g̃^x]), the holder's key
[pk = g^sk] and attributes [mᵢ]:
[Cm = g₀·pk·∏ gᵢ^mᵢ], [A = Cm^(1/(x+e))], and the identity
[B = Cm·A^(-e) = A^x]. To show it, the holder picks fresh [r], [r₁], [r₂]
and computes [pk_Blind = g^(sk+r)], [Ā = A^(r₁r₂)], [D = Cm^r₂],
[B̄ = Ā^(-e)·D^r₁ = Ā^x] and [r₃ = r₂⁻¹]. Three proofs are attached:

- validity: one Okamoto statement in [G²] with witness
  [(-e, r₁, r₃, r, (-mᵢ)_(i∉D))] for [B̄ = Ā^(-e)·D^r₁] and
  [g₀·pk_Blind·∏_(i∈D) gᵢ^mᵢ = D^r₃·g^r·∏_(i∉D) gᵢ^(-mᵢ)];
- holder binding: a Schnorr proof for [pk_Blind = g^(sk+r)];
- the replacement of the pairing check: a Chaum–Pedersen proof by the
  Issuer of [B̄ = Ā^x ∧ pk_I = g̃^x].

[Crypto/BBSSharp.v] proves the algebra of the MAC and its randomisation,
completeness, special soundness and honest-verifier zero knowledge of the
three proofs, the extraction argument (a validity witness together with
the Issuer's discrete logarithm gives a MAC on the blinded key and the
attributes, or the Issuer's key), and the statistical anonymity of the
randomised credential. *)
From Stdlib Require Import Utf8 ZArith Zmod Vector Fin List Lia.
From Algebra Require Import Hierarchy Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen MultiExp OkamotoRows BBSSharp.
From Backend Require Import BBSSharpVerifier.
From Curve Require Import P256.
From Examples Require Import UProveIns.
From Utility Require Import Util.
Import VectorNotations.

Section BBSSharpIns.

  Import P256.

  (** [F = Z/nZ] and [G] the P-256 group. *)
  Local Notation F := Zn.F.
  Local Notation G := Wp.G.

  (** The P-256 base point, used as the generator [g]. *)
  Definition g : G := Wp.B.

  (** ** Conversions for the driver

      Scalar and point conversions, reused from [UProveIns.v]: [of_Z],
      [to_Z], [point_to_Z] and the checked point constructor [mk_G] (on the
      curve and in the order-[n] group). *)
  Definition of_Z (z : Z) : F := UProveIns.of_Z z.
  Definition to_Z (k : F) : Z := UProveIns.to_Z k.
  Definition point_to_Z (P : G) : option (Z * Z) := UProveIns.point_to_Z P.
  Definition mk_G (x y : Z) : option G := UProveIns.mk_G x y.

  (** ** The credential (Issuer and holder side)

      [Cm = g₀·pk·∏_(i∈D) gᵢ^mᵢ·∏_(i∈U) gᵢ^mᵢ], with the attributes split into
      disclosed ([D]) and undisclosed ([U]) ones. *)
  Definition cm_ins {d u : nat} (g0 pk : G) (gD : Vector.t G d) (mD : Vector.t F d)
    (gU : Vector.t G u) (mU : Vector.t F u) : G :=
    Cm (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast) g0 pk gD mD gU mU.

  (** The MAC [A = Cm^(1/(x+e))], computed by the Issuer with key [x]. *)
  Definition mac_ins (C : G) (x e : F) : G := mac (add := Zn.add) (inv := Zn.inv) (gpow := Wp.gpow_fast) C x e.
  (** [B = Cm·A^(-e)], which equals [A^x] for a valid MAC. *)
  Definition mac_B_ins (C A : G) (e : F) : G := mac_B (opp := Zn.opp) (gop := Wp.gop) (gpow := Wp.gpow_fast) C A e.

  (** Randomisation: [Ā = A^(r₁·r₂)]. *)
  Definition rand_A_ins (A : G) (r1 r2 : F) : G := rand_A (mul := Zn.mul) (gpow := Wp.gpow_fast) A r1 r2.
  (** Randomisation: [D = Cm^r₂]. *)
  Definition rand_D_ins (C : G) (r2 : F) : G := rand_D (gpow := Wp.gpow_fast) C r2.
  (** Randomisation: [B̄ = Ā^(-e)·D^r₁]. *)
  Definition rand_B_ins (Abar D : G) (e r1 : F) : G :=
    rand_B (opp := Zn.opp) (gop := Wp.gop) (gpow := Wp.gpow_fast) Abar D e r1.

  (** The blinded holder key [pk_Blind = g^(sk + r)]. *)
  Definition pk_blind_ins (sk r : F) : G := pk_blind (add := Zn.add) (gpow := Wp.gpow_fast) g sk r.
  (** The public target of the validity proof's second equation,
      [g₀·pk_Blind·∏_(i∈D) gᵢ^mᵢ]. *)
  Definition target_P_ins {d : nat} (g0 pkB : G) (gD : Vector.t G d) (mD : Vector.t F d) : G :=
    target_P (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast) g0 pkB gD mD.

  (** ** The three proofs, prover side

      The validity proof: the honest Okamoto transcript in [G²] with witness
      [(-e, r₁, r₃, r, -m_U)], randomness [us] and challenge [c]. *)
  Definition validity_prove_ins {u : nat} (e r1 r3 r : F) (mU : Vector.t F u) (Abar D : G)
    (gU : Vector.t G u) (Bbar P : G) (us : Vector.t F (S (S (S (S u))))) (c : F) :
    @sigma_proto F (Vector.t G 2) 1 1 (S (S (S (S u)))) :=
    validity_real (add := Zn.add) (mul := Zn.mul) (opp := Zn.opp) (gid := Wp.gid) (gop := Wp.gop)
      (gpow := Wp.gpow_fast) e r1 r3 r mU Abar D g gU Bbar P us c.

  (** The holder-binding proof: Schnorr for [pk_Blind = g^(sk+r)]. *)
  Definition hb_prove_ins (sk r u c : F) : @sigma_proto F G 1 1 1 :=
    hb_real (add := Zn.add) (mul := Zn.mul) (gpow := Wp.gpow_fast) g sk r u c.

  (** The Issuer's equality proof: Chaum–Pedersen for
      [(pk_I, B̄) = (g̃, Ā)^x]. *)
  Definition dleq_prove_ins (gt Abar : G) (x u c : F) : @sigma_proto F G 2 1 1 :=
    construct_cp_conversations_schnorr (add := Zn.add) (mul := Zn.mul) (gpow := Wp.gpow_fast) x gt Abar u c.

  (** A presentation: disclosed attributes, blinded key, the three proofs
      and the randomised credential [(Ā, B̄, D)]. *)
  Definition presentation_ins (d u : nat) := @presentation F G d u.

  (** Its constructor. *)
  Definition mk_presentation_ins {d u : nat} (mD : Vector.t F d) (pkB : G) (hb_c hb_r : F) (Abar Bbar D : G)
    (c : F) (rs : Vector.t F (S (S (S (S u))))) (dleq_c dleq_r : F) : presentation_ins d u :=
    mk_presentation d u mD pkB hb_c hb_r Abar Bbar D c rs dleq_c dleq_r.

  (** ** The verifier

      Checks the holder-binding Schnorr proof [(c, ρ)] with the hash [H3]. *)
  Definition verify_hb_ins (H3 : G -> F) (pkB : G) (c ρ : F) : bool :=
    verify_hb (opp := Zn.opp) (Fdec := Zn.Fdec) (gop := Wp.gop) (gpow := Wp.gpow_fast) H3 g pkB c ρ.

  (** Checks the Issuer's Chaum–Pedersen proof [(c, ρ)] with the hash [H2]. *)
  Definition verify_dleq_ins (H2 : G -> G -> F) (gt pkI Abar Bbar : G) (c ρ : F) : bool :=
    verify_dleq (opp := Zn.opp) (Fdec := Zn.Fdec) (gop := Wp.gop) (gpow := Wp.gpow_fast) H2 gt pkI Abar Bbar c ρ.

  (** Checks the validity proof [(c, rs)] with the hash [H4] of the
      reconstructed announcement pair. *)
  Definition verify_validity_ins {u : nat} (H4 : Vector.t G 2 -> F) (Abar D : G) (gU : Vector.t G u) (Bbar P : G)
    (c : F) (rs : Vector.t F (S (S (S (S u))))) : bool :=
    verify_validity (opp := Zn.opp) (Fdec := Zn.Fdec) (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast)
      H4 Abar D g gU Bbar P c rs.

  (** Accepts a presentation iff [Ā ≠ 1] and all three proofs verify, with
      the validity target recomputed from the disclosed attributes. This is
      the entry point used by the driver. *)
  Definition verify_presentation_ins {d u : nat} (H2 : G -> G -> F) (H3 : G -> F) (H4 : Vector.t G 2 -> F)
    (gt g0 pkI : G) (gD : Vector.t G d) (gU : Vector.t G u) (pr : presentation_ins d u) : bool :=
    verify_presentation (opp := Zn.opp) (Fdec := Zn.Fdec) (gid := Wp.gid) (gop := Wp.gop)
      (gpow := Wp.gpow_fast) (Gdec := Wp.Gdec) H2 H3 H4 g gt g0 pkI gD gU pr.

End BBSSharpIns.
