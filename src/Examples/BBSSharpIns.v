(* BBS# at P-256 (secp256r1, the curve of the paper's implementation), as an
   instance of Crypto/BBSSharp.v and Backend/BBSSharpVerifier.v over the
   curve group of Curve/P256.v with Z/nZ as the scalar field. Both sides are
   exported: the holder's and Issuer's computations (the MAC, its
   randomisation, the three real protocols) so that the OCaml driver
   (Executable/Bbssharpverifier) can produce presentations with the
   certified prover code, and the verifier. The hash functions H_2, H_3, H_4
   of the paper are oracles computed by the driver (hash_to_scalar of
   RFC 9380 over SHA-256, see the driver); the group arithmetic, the
   reconstruction of the announcements and the comparisons are extracted
   from Rocq. Points and scalars cross the boundary as integers through
   Examples/UProveIns.v (of_Z, to_Z, point_to_Z, mk_G). *)

(* How a BBS# credential works, and what this code checks.

   BBS# (Desmoulins, Dumanois, Kane and Traoré, ePrint 2025/619) is a
   variant of BBS anonymous credentials that needs no pairings, so that
   the holder's key can live in the secure hardware of a phone, and that
   can be shown many times without the showings being linkable.

   The credential is an algebraic MAC. With generators g, g̃, g_0, g_1..g_n,
   the Issuer's key x (pk_I = g̃^x), the holder's key pk = g^{sk} and the
   attributes m_i,

     Cm = g_0 · pk · ∏ g_i^{m_i},     A = Cm^{1/(x+e)},     σ = (A, e).

   Raising A to the power x + e gives the identity on which everything
   rests:

     B = Cm · A^{−e} = A^x.

   Showing the credential. The holder blinds the key and randomises the
   MAC with fresh r, r_1, r_2:

     pk_Blind = g^{sk+r},   Ā = A^{r_1 r_2},   D = Cm^{r_2},
     B̄ = Ā^{−e} · D^{r_1} = Ā^x,   r_3 = r_2⁻¹.

   Every showing uses new randomness, so two showings cannot be linked.

   Three proofs.
   1. Validity, one Okamoto statement in G² with one challenge: knowledge
      of (−e, r_1, r_3, r, {−m_i}_{i∉D}) with

        B̄ = Ā^{−e} · D^{r_1}
        g_0 · pk_Blind · ∏_{i∈D} g_i^{m_i}
          = D^{r_3} · g^r · ∏_{i∉D} g_i^{−m_i}.

      The second equation holds because D^{r_3} = Cm and
      pk_Blind = pk · g^r.
   2. Holder binding, the Schnorr proof of knowledge of the discrete
      logarithm of pk_Blind, an ordinary signature that a secure element
      can produce.
   3. The replacement of the pairing check. BBS confirms B̄ = Ā^x with a
      pairing; BBS# replaces it with a Chaum–Pedersen proof by the Issuer
      of

        B̄ = Ā^x   ∧   pk_I = g̃^x.

   What is proved. Crypto/BBSSharp.v has the algebra of the MAC and of its
   randomisation, the three proofs as instances of the library with
   completeness, special soundness and honest-verifier zero knowledge, the
   extraction argument (a witness of the validity proof with the discrete
   logarithm of the equality proof gives a MAC on the blinded key and the
   attributes, or the Issuer's key), and the statistical anonymity of the
   randomised credential: the distribution of (Ā, D) over uniform
   (r_1, r_2) does not depend on the credential. There are no published
   test vectors for BBS#, so the driver runs the extracted prover against
   the extracted verifier. What is trusted: the hash-to-scalar oracles and
   the derivation of the generators, done by the driver. *)

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

  Local Notation F := Zn.F.
  Local Notation G := Wp.G.

  Definition g : G := Wp.B.

  (* scalars and points as integers, for the driver (from Examples/UProveIns.v) *)
  Definition of_Z (z : Z) : F := UProveIns.of_Z z.
  Definition to_Z (k : F) : Z := UProveIns.to_Z k.
  Definition point_to_Z (P : G) : option (Z * Z) := UProveIns.point_to_Z P.
  Definition mk_G (x y : Z) : option G := UProveIns.mk_G x y.

  (* ---- the credential (Issuer and holder side) ---- *)

  (* Cm = g_0 · pk · ∏ g_i^{m_i}, attributes split into disclosed and undisclosed *)
  Definition cm_ins {d u : nat} (g0 pk : G) (gD : Vector.t G d) (mD : Vector.t F d)
    (gU : Vector.t G u) (mU : Vector.t F u) : G :=
    Cm (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast) g0 pk gD mD gU mU.

  (* A = Cm^{1/(x+e)} and B = Cm · A^{−e} *)
  Definition mac_ins (C : G) (x e : F) : G := mac (add := Zn.add) (inv := Zn.inv) (gpow := Wp.gpow_fast) C x e.
  Definition mac_B_ins (C A : G) (e : F) : G := mac_B (opp := Zn.opp) (gop := Wp.gop) (gpow := Wp.gpow_fast) C A e.

  (* the randomised credential Ā = A^{r_1 r_2}, D = Cm^{r_2}, B̄ = Ā^{−e} D^{r_1} *)
  Definition rand_A_ins (A : G) (r1 r2 : F) : G := rand_A (mul := Zn.mul) (gpow := Wp.gpow_fast) A r1 r2.
  Definition rand_D_ins (C : G) (r2 : F) : G := rand_D (gpow := Wp.gpow_fast) C r2.
  Definition rand_B_ins (Abar D : G) (e r1 : F) : G :=
    rand_B (opp := Zn.opp) (gop := Wp.gop) (gpow := Wp.gpow_fast) Abar D e r1.

  Definition pk_blind_ins (sk r : F) : G := pk_blind (add := Zn.add) (gpow := Wp.gpow_fast) g sk r.
  Definition target_P_ins {d : nat} (g0 pkB : G) (gD : Vector.t G d) (mD : Vector.t F d) : G :=
    target_P (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast) g0 pkB gD mD.

  (* ---- the three proofs, prover side (the library's real protocols) ---- *)

  (* π_validity: the Okamoto statement in G² with witness (−e, r_1, r_3, r, −m_U) *)
  Definition validity_prove_ins {u : nat} (e r1 r3 r : F) (mU : Vector.t F u) (Abar D : G)
    (gU : Vector.t G u) (Bbar P : G) (us : Vector.t F (S (S (S (S u))))) (c : F) :
    @sigma_proto F (Vector.t G 2) 1 1 (S (S (S (S u)))) :=
    validity_real (add := Zn.add) (mul := Zn.mul) (opp := Zn.opp) (gid := Wp.gid) (gop := Wp.gop)
      (gpow := Wp.gpow_fast) e r1 r3 r mU Abar D g gU Bbar P us c.

  (* π_HB: Schnorr for pk_Blind = g^{sk+r} *)
  Definition hb_prove_ins (sk r u c : F) : @sigma_proto F G 1 1 1 :=
    hb_real (add := Zn.add) (mul := Zn.mul) (gpow := Wp.gpow_fast) g sk r u c.

  (* π_DLEQ: Chaum–Pedersen for (pk_I, B̄) = (g̃, Ā)^x, produced by the Issuer *)
  Definition dleq_prove_ins (gt Abar : G) (x u c : F) : @sigma_proto F G 2 1 1 :=
    construct_cp_conversations_schnorr (add := Zn.add) (mul := Zn.mul) (gpow := Wp.gpow_fast) x gt Abar u c.

  (* ---- the verifier ---- *)

  Definition presentation_ins (d u : nat) := @presentation F G d u.

  Definition mk_presentation_ins {d u : nat} (mD : Vector.t F d) (pkB : G) (hb_c hb_r : F) (Abar Bbar D : G)
    (c : F) (rs : Vector.t F (S (S (S (S u))))) (dleq_c dleq_r : F) : presentation_ins d u :=
    mk_presentation d u mD pkB hb_c hb_r Abar Bbar D c rs dleq_c dleq_r.

  Definition verify_hb_ins (H3 : G -> F) (pkB : G) (c ρ : F) : bool :=
    verify_hb (opp := Zn.opp) (Fdec := Zn.Fdec) (gop := Wp.gop) (gpow := Wp.gpow_fast) H3 g pkB c ρ.

  Definition verify_dleq_ins (H2 : G -> G -> F) (gt pkI Abar Bbar : G) (c ρ : F) : bool :=
    verify_dleq (opp := Zn.opp) (Fdec := Zn.Fdec) (gop := Wp.gop) (gpow := Wp.gpow_fast) H2 gt pkI Abar Bbar c ρ.

  Definition verify_validity_ins {u : nat} (H4 : Vector.t G 2 -> F) (Abar D : G) (gU : Vector.t G u) (Bbar P : G)
    (c : F) (rs : Vector.t F (S (S (S (S u))))) : bool :=
    verify_validity (opp := Zn.opp) (Fdec := Zn.Fdec) (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast)
      H4 Abar D g gU Bbar P c rs.

  Definition verify_presentation_ins {d u : nat} (H2 : G -> G -> F) (H3 : G -> F) (H4 : Vector.t G 2 -> F)
    (gt g0 pkI : G) (gD : Vector.t G d) (gU : Vector.t G u) (pr : presentation_ins d u) : bool :=
    verify_presentation (opp := Zn.opp) (Fdec := Zn.Fdec) (gid := Wp.gid) (gop := Wp.gop)
      (gpow := Wp.gpow_fast) (Gdec := Wp.Gdec) H2 H3 H4 g gt g0 pkI gD gU pr.

End BBSSharpIns.
