(** * The U-Prove verifier at P-256 *)

(** This file instantiates the U-Prove verifier ([Backend/UProveVerifier.v],
over [Crypto/UProve.v]) at NIST P-256, the elliptic-curve construction of
the U-Prove Recommended Parameters Profile (OID 1.3.6.1.4.1.311.75.1.2.1,
with SHA-256): the group is the curve group of [Curve/P256.v] and the
scalar field is [Z/nZ]. The hash formatting of the specification
(section 2.2) and the parsing of tokens and proofs are done by the OCaml
driver [Executable/Uproveverifier], which passes the hash functions in as
oracles; the group operations, the reconstruction of the announcements and
all comparisons run in the extracted code ([src/Extraction/UProvelib]).
Digests are handed over as integers (the big-endian value of the SHA-256
output). *)

(** ** How a U-Prove token is checked

U-Prove is Brands' anonymous credential scheme as specified by
Microsoft. With the Issuer's generators [g₀ … g_n], [g_t], the attribute
values [xᵢ] and the hash [x_t] of the token information, the token public
key is [h = γ^α] with [γ = g₀·∏ gᵢ^xᵢ·g_t^x_t] (optionally times a device
key), where [α] is the holder's blinding factor and [α⁻¹] the token's
private key.

- The Issuer's signature [(σ_z, σ_c, σ_r)] is a Chaum–Pedersen proof, for
  the Issuer's private key [y₀], of [g₀ = g^y₀ ∧ σ_z = h^y₀]; the verifier
  reconstructs [(g^σ_r·g₀^(-σ_c), h^σ_r·σ_z^(-σ_c))] and checks that its
  hash is [σ_c].
- A presentation with disclosed set [D] is an Okamoto proof of
  [g₀·g_t^x_t·∏_(i∈D) gᵢ^xᵢ = h^(α⁻¹)·∏_(i∉D) gᵢ^(-xᵢ)], with bases [h]
  and the undisclosed [gᵢ] and witness [(α⁻¹, -xᵢ)].
- The scope-exclusive pseudonym [P_s = g_s^x_p] and the attribute
  commitments [c̃ᵢ = g^xᵢ·g₁^õᵢ] use the same challenge and responses;
  together with the presentation equation they form one Okamoto
  statement in a product group, one row per equation.

[Crypto/UProve.v] proves completeness, special soundness (extraction of
[α⁻¹], the hidden attributes, and [y₀] for the signature) and
honest-verifier zero knowledge, inherited from the library's Okamoto and
Chaum–Pedersen protocols. The unforgeability and unlinkability of the
credential scheme as a whole are not proved. *)
From Stdlib Require Import Utf8 ZArith Zmod Vector Fin List Lia.
From Algebra Require Import Hierarchy Vector_space Vector_product_space.
From Sigma Require Import Sigma MultiExp OkamotoRows UProve.
From Backend Require Import UProveVerifier.
From Curve Require Import P256.
From Fiat.Spec Require Import WeierstrassCurve.
From Utility Require Import Util.
Import VectorNotations.

Section UProveIns.

  Import P256.

  (** [F = Z/nZ], [G] the P-256 group and [n] its order. *)
  Local Notation F := Zn.F.
  Local Notation G := Wp.G.
  Local Notation n := P256.n.

  (** ** Scalars, points and digests for the driver

      [of_Z] reduces an integer modulo [n]. *)
  Definition of_Z (z : Z) : F := Zmod.of_Z n z.
  (** The canonical integer representative of a scalar. *)
  Definition to_Z (k : F) : Z := Zmod.unsigned k.
  (** The affine coordinates of a point, or [None] for the point at
      infinity. *)
  Definition point_to_Z (P : G) : option (Z * Z) := Wp.coords (proj1_sig P).

  (** Builds a curve point from affine coordinates [(x, y)], reduced modulo
      the field prime [p]: [Some] point iff [y² = x³ + a·x + b] holds in
      [Z/pZ], the decision also providing the on-curve proof. *)
  Definition mk_point (x y : Z) : option Wp.point.
  Proof.
    refine (let xf := Zmod.of_Z p x in let yf := Zmod.of_Z p y in
      match Wp.Fp_dec (Zmod.mul yf yf)
        (Zmod.add (Zmod.add (Zmod.mul xf (Zmod.mul xf xf)) (Zmod.mul Wp.a xf)) Wp.b) with
      | left h => Some (exist _ (inl (xf, yf)) _)
      | right _ => None
      end).
    exact h.
  Defined.

  (** Builds a group element from affine coordinates: the point must be on
      the curve ([mk_point]) and satisfy [n·P = 0], decided by computation
      with the fast scalar multiplication. Untrusted input from the driver
      enters the group only through this check. *)
  Definition mk_G (x y : Z) : option G :=
    match mk_point x y with
    | Some P =>
      match Wp.point_dec (Wp.fast_smul n P) Wp.pzero with
      | left h => Some (exist _ P (eq_trans (eq_sym (Wp.fast_smul_eq _ _)) h))
      | right _ => None
      end
    | None => None
    end.

  (** Hash digests, as integers. *)
  Definition Digest : Type := Z.
  (** The P-256 base point, the generator of the profile. *)
  Definition g : G := Wp.B.

  (** ** The verifier

      The Issuer's signature on a token (figure 4 of the specification):
      rejects [h = 1] and otherwise accepts iff
      [σ_c = Hs(g^σ_r·g₀^(-σ_c), h^σ_r·σ_z^(-σ_c))]. *)
  Definition verify_signature_ins (Hs : G -> G -> F) (g0 h σz : G) (σc σr : F) : bool :=
    verify_signature (opp := Zn.opp) (Fdec := Zn.Fdec) (gid := Wp.gid) (gop := Wp.gop)
      (gpow := Wp.gpow_fast) (Gdec := Wp.Gdec) Hs g g0 h σz σc σr.

  (** The public side of the presentation equation,
      [g₀·g_t^x_t·∏_(i∈D) gᵢ^xᵢ], for the disclosed generators [gD] and
      values [xD]. *)
  Definition target_ins {d : nat} (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d) : G :=
    pres_target (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast) g0 gt xt gD xD.

  (** A presentation proof without pseudonym or commitments (figure 10 of the
      specification): with the challenge [C a] computed from the published
      digest [a], accepts iff [a] is the hash [Ha] of the reconstructed
      announcement [target^(-c)·h^r₀·∏ restᵢ^rᵢ]. *)
  Definition verify_presentation_ins {k : nat} (Ha : G -> Digest) (C : Digest -> F) (h : G)
    (rest : Vector.t G k) (target : G) (a : Digest) (rs : Vector.t F (S k)) : bool :=
    verify_presentation (opp := Zn.opp) (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast)
      (Ddec := Z.eq_dec) Ha C h rest target a rs.

  (** Converts an index to a coordinate [Fin.t K], or [None] if out of range;
      used by the driver to build rows from parsed indices. *)
  Definition coord_ins (K p : nat) : option (Fin.t K) := coord K p.

  (** Assembles the rows of a presentation with extensions: the core row, an
      optional pseudonym row and one row per committed attribute (each with
      its attribute and opening coordinates, commitment and digest). *)
  Definition components_ins {k e : nat} (h : G) (rest : Vector.t G k) (target : G) (a : Digest)
    (nym : option (Fin.t (S k + e) * G * G * Digest))
    (coms : list (Fin.t (S k + e) * Fin.t (S k + e) * G * Digest)) (g1 : G) :
    list (component (G := G) (Digest := Digest) (S k + e)) :=
    uprove_components (gid := Wp.gid) (ginv := Wp.ginv) (gop := Wp.gop) h rest target a nym coms g g1.

  (** The full presentation check with pseudonym and commitments (figure 10):
      the rows share the responses [rs], and the challenge is [C] applied to
      the list of row digests [(a, a_p, ãᵢ)]. *)
  Definition verify_uprove_ins {K : nat} (Ha : G -> Digest) (C : list Digest -> F)
    (cs : list (component (G := G) (Digest := Digest) K)) (rs : Vector.t F K) : bool :=
    verify_uprove (opp := Zn.opp) (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast)
      (Ddec := Z.eq_dec) Ha C cs rs.

End UProveIns.
