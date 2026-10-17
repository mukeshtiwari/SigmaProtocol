(* The U-Prove verifier at P-256 (the elliptic-curve construction of the
   U-Prove Recommended Parameters Profile, OID 1.3.6.1.4.1.311.75.1.2.1,
   with SHA-256), as an instance of Backend/UProveVerifier.v over the curve
   group of Curve/P256.v with Z/nZ as the scalar field. The hash formatting
   of the spec (section 2.2) and the parsing of tokens and proofs are done by
   the OCaml driver (Executable/Uproveverifier), which passes the hash
   functions as oracles; the group operations, the reconstruction of the
   announcements and all comparisons happen in the extracted code. Digests
   are handed over as integers (the big-endian value of the SHA-256 output). *)

(* How a U-Prove token works, and what this verifier checks.

   U-Prove is Brands' anonymous credential scheme, as specified by
   Microsoft. A token carries attributes; its holder discloses some of
   them and proves knowledge of the others. A token is shown once: two
   showings of the same token can be linked.

   The token. With the Issuer's generators g_0..g_n, g_t, the attribute
   values x_i, the hash x_t of the token information and the optional
   Device key g_d^{x_d},

     γ = g_0 · g_1^{x_1} ⋯ g_n^{x_n} · g_t^{x_t} · [g_d^{x_d}],     h = γ^α.

   h is the public key of the token, α the holder's blinding factor and
   α⁻¹ the private key of the token.

   The Issuer's signature (σ_z', σ_c', σ_r') is a Chaum–Pedersen proof, for
   the Issuer's private key y_0, of

     g_0 = g^{y_0}   ∧   σ_z' = h^{y_0}.

   The verifier reconstructs the announcement

     (g^{σ_r'} · g_0^{−σ_c'},  h^{σ_r'} · σ_z'^{−σ_c'})

   and checks that hashing it with the token data gives σ_c'.

   Presentation with the disclosed set D. Rearranging h = γ^α puts the
   disclosed attributes on the left and the hidden ones on the right:

     g_0 · g_t^{x_t} · ∏_{i∈D} g_i^{x_i}
       = h^{α⁻¹} · ∏_{i∉D} g_i^{−x_i} · [g_d^{−x_d}].

   This is one statement of the generalised Okamoto protocol with bases
   (h, g_i for i ∉ D, [g_d]) and witness (α⁻¹, −x_i, [−x_d]). The responses
   and the verifier's reconstruction are

     r_0 = c·α⁻¹ + w_0,     r_i = −c·x_i + w_i,
     A = (g_0 · g_t^{x_t} · ∏_{i∈D} g_i^{x_i})^{−c}
           · h^{r_0} · ∏_{i∉D} g_i^{r_i} · [g_d^{r_d}].

   Two further components use the same challenge and the same responses:
   the scope-exclusive pseudonym P_s = g_s^{x_p}, one stable name per scope
   that is unlinkable across scopes, and the attribute commitments
   c̃_i = g^{x_i} · g_1^{õ_i}. Together with the equation above they are a
   single Okamoto statement in the product space G^m, one component per
   equation.

   What is proved. Crypto/UProve.v gives completeness, special soundness
   (extraction of α⁻¹ and of the hidden attributes, and of y_0 for the
   signature) and honest-verifier zero knowledge, inherited from the
   library's Okamoto and Chaum–Pedersen protocols. Not proved here: the
   unforgeability and the unlinkability of the credential scheme as a
   whole. What is trusted: the hash formatting of the specification and
   the parsing of the test vectors, done by the driver. *)

From Stdlib Require Import Utf8 ZArith Zmod Vector Fin List Lia.
From Algebra Require Import Hierarchy Vector_space Vector_product_space.
From Crypto Require Import Sigma MultiExp OkamotoRows UProve.
From Backend Require Import UProveVerifier.
From Curve Require Import P256.
From Fiat.Spec Require Import WeierstrassCurve.
From Utility Require Import Util.
Import VectorNotations.

Section UProveIns.

  Import P256.

  Local Notation F := Zn.F.
  Local Notation G := Wp.G.
  Local Notation n := P256.n.

  (* ---- scalars, points and digests as integers, for the driver ---- *)

  Definition of_Z (z : Z) : F := Zmod.of_Z n z.
  Definition to_Z (k : F) : Z := Zmod.unsigned k.
  Definition point_to_Z (P : G) : option (Z * Z) := Wp.coords (proj1_sig P).

  (* a curve point from its affine coordinates: the curve equation is
    decided in Z/pZ, the subgroup membership n·P = 0 by computation *)
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

  Definition mk_G (x y : Z) : option G :=
    match mk_point x y with
    | Some P =>
      match Wp.point_dec (Wp.fast_smul n P) Wp.pzero with
      | left h => Some (exist _ P (eq_trans (eq_sym (Wp.fast_smul_eq _ _)) h))
      | right _ => None
      end
    | None => None
    end.

  Definition Digest : Type := Z.
  Definition g : G := Wp.B.

  (* ---- the verifier ---- *)

  (* Figure 4: the Issuer's signature; Hs computes σ_c' from the reconstructed
    (σ_a', σ_b') *)
  Definition verify_signature_ins (Hs : G -> G -> F) (g0 h σz : G) (σc σr : F) : bool :=
    verify_signature (opp := Zn.opp) (Fdec := Zn.Fdec) (gid := Wp.gid) (gop := Wp.gop)
      (gpow := Wp.gpow_fast) (Gdec := Wp.Gdec) Hs g g0 h σz σc σr.

  (* g_0 · g_t^{x_t} · ∏_{i∈D} g_i^{x_i} *)
  Definition target_ins {d : nat} (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d) : G :=
    pres_target (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast) g0 gt xt gD xD.

  (* Figure 10 without pseudonym or commitments: Ha hashes a group element,
    C computes the challenge from the digest a *)
  Definition verify_presentation_ins {k : nat} (Ha : G -> Digest) (C : Digest -> F) (h : G)
    (rest : Vector.t G k) (target : G) (a : Digest) (rs : Vector.t F (S k)) : bool :=
    verify_presentation (opp := Zn.opp) (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast)
      (Ddec := Z.eq_dec) Ha C h rest target a rs.

  (* Figure 10 with pseudonym and commitments: the components, and their
    verification with C computing the challenge from the list of digests
    (a, [a_p], ã_i) *)
  Definition coord_ins (K p : nat) : option (Fin.t K) := coord K p.

  Definition components_ins {k e : nat} (h : G) (rest : Vector.t G k) (target : G) (a : Digest)
    (nym : option (Fin.t (S k + e) * G * G * Digest))
    (coms : list (Fin.t (S k + e) * Fin.t (S k + e) * G * Digest)) (g1 : G) :
    list (component (G := G) (Digest := Digest) (S k + e)) :=
    uprove_components (gid := Wp.gid) (ginv := Wp.ginv) (gop := Wp.gop) h rest target a nym coms g g1.

  Definition verify_uprove_ins {K : nat} (Ha : G -> Digest) (C : list Digest -> F)
    (cs : list (component (G := G) (Digest := Digest) K)) (rs : Vector.t F K) : bool :=
    verify_uprove (opp := Zn.opp) (gid := Wp.gid) (gop := Wp.gop) (gpow := Wp.gpow_fast)
      (Ddec := Z.eq_dec) Ha C cs rs.

End UProveIns.
