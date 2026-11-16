(* The Verificatum verifier (Backend/VerificatumVerifier.v) at the group of
   the Helios instantiation (Examples/HeliosTallyIns.v): the 2048-bit prime
   p and 256-bit prime q with their Pocklington certificates
   (Examples/primeP.v, primeQ.v) and the standard generator g. The demo of
   Verificatum 3.1.0 shipped in Executable/Vmnverifier/data was run with
   exactly this group (vog -gen ModPGroup -explic -roenc p g q). The
   random oracles and the byte-tree formats are computed by the driver
   (Executable/Vmnverifier) and passed in through the oracle records. *)

(* How a Verificatum mixing session works, and what this verifier checks.

   Verificatum is Wikström's mix-net. A mix-net takes a list of ElGamal
   ciphertexts and outputs the same plaintexts, re-encrypted and in a
   secret order, so that no output can be linked to an input. Each
   mix-server must prove that it did exactly this: a proof of a shuffle.
   The proof used here is that of Terelius and Wikström.

   The claim. For the input w_0..w_N and the output w'_0..w'_N there are a
   permutation π and exponents s_i with

     w'_i = Enc(1; s_i) · w_{π(i)},      Enc(1; r) = (g^r, pk^r),

   and π stays secret.

   1. Commitment to the permutation. With independent generators h_0..h_N
      the prover publishes u_i = g^{r_i} · h_{π(i)}.
   2. Batching. The verifier sends a random vector e; let e' be e permuted
      by π.
   3. Bridging commitments. The prover publishes the chain

        B_i = g^{β_i} · B_{i-1}^{e'_i},      B_{-1} = h_0,

      which accumulates the product of the e'_i.
   4. The verifier derives

        A = ∏ u_i^{e_i}     C = ∏ u_i / ∏ h_i     D = B_N · h_0^{−∏ e_i}
        F = ∏ w_i^{e_i}  (componentwise).

   5. The prover proves knowledge of (a, c, d, f, β, e') with

        A   = g^a · ∏ h_i^{e'_i}
        C   = g^c
        D   = g^d
        B_i = g^{β_i} · B_{i-1}^{e'_i}          (i = 0..N)
        F   = Enc(1; −f) · ∏ w'_i^{e'_i}.

   Why this is a proof of a shuffle. The first equation says that u
   commits to a matrix that maps e to e'. The second says that this matrix
   maps the all-ones vector to itself. The third and fourth say that
   ∏ e'_i = ∏ e_i. For a random e, a matrix with these two properties is a
   permutation matrix. The fifth says that the outputs are the inputs,
   re-encrypted, under that permutation.

   One statement. Once e is fixed the five equations are linear in the
   witness and share the e'_i, so they are a single statement
   Y = ∏_j gs_j^{x_j} of the generalised Okamoto protocol in the space

     V = G × G × G × G^{N+1} × (G × G)

   (Crypto/ShuffleTW.v, tw_relation_iff). Verificatum publishes the
   announcement (A', C', D', B', F'), derives the challenge v by hashing
   and publishes the response k = ω + v·x. The verifier accepts if

     A^v · A' = g^{k_A} · ∏ h_i^{k_E,i}
     C^v · C' = g^{k_C}
     D^v · D' = g^{k_D}
     B_i^v · B'_i = g^{k_B,i} · B_{i-1}^{k_E,i}
     F^v · F' = Enc(1; −k_F) · ∏ w'_i^{k_E,i},

   which is the Okamoto acceptance test at V (verify_pos_accepting).

   Joint decryption. Party l publishes the factors f_l,i = u_i^{−x_l/α}
   with a Chaum–Pedersen proof. The verifier combines the parties with
   their Lagrange coefficients and checks

     y^{−v} · y' = g^k     and     B^v · B' = U^k,     U = ∏ u_i^{e_i},

   and the plaintexts are m_i = v_i · f_i.

   What is trusted: the byte-tree parser, the SHA-256 random oracles and
   the derivation of the generators h_i, all computed by the driver. *)

From Stdlib Require Import Utf8 ZArith Vector List.
From Crypto Require Import Sigma Okamoto MultiExp ShuffleTW.
From Backend Require Import VerificatumVerifier.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns.
Import Vspace Schnorr Zpfield Zpgroup.

Section VerificatumIns.

  (* the group of HeliosTallyIns: p, q, k with p = k q + 1, and g *)
  Local Notation p := HeliosTallyIns.p.
  Local Notation q := HeliosTallyIns.q.
  Local Notation F := (@Zp q).
  Local Notation G := (@Schnorr_group p q).

  Definition Fzero : F := @Zpfield.zero q HeliosTallyIns.prime_q.
  Definition Fone : F := @Zpfield.one q HeliosTallyIns.prime_q.
  Definition Fadd : F -> F -> F := @zp_add q.
  Definition Fmul : F -> F -> F := @zp_mul q.
  Definition Fopp : F -> F := @zp_opp q HeliosTallyIns.prime_q.
  Definition Fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  Definition Gone : G := @Schnorr.one p q HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Ginv : G -> G := @inv_schnorr_group HeliosTallyIns.k p q HeliosTallyIns.safe_prime HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Gmul : G -> G -> G := @mul_schnorr_group p q HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Gpow : G -> F -> G := @pow HeliosTallyIns.k p q HeliosTallyIns.safe_prime HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.

  Definition generator : G := HeliosTallyIns.g.

  (* the types, for N + 1 ciphertexts *)
  Definition ciphertext : Type := (G * G)%type.
  Definition pos_proof (N : nat) := @pos_proof (@Zp q) G N.
  Definition pos_oracles (N : nat) := @pos_oracles (@Zp q) G N.
  Definition mk_pos_proof {N : nat} := @mk_pos_proof (@Zp q) G N.
  Definition mk_pos_oracles {N : nat} := @mk_pos_oracles (@Zp q) G N.

  Definition verify_pos_ins {N : nat} (hs : Vector.t G (S N)) (pk : ciphertext)
    (O : pos_oracles N) (w w' : Vector.t ciphertext (S N)) (pf : pos_proof N) : bool :=
    verify_pos (one := Fone) (mul := Fmul)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator hs pk O w w' pf.

  Definition verify_shuffling_ins {N : nat} (hs : Vector.t G (S N)) (pk : ciphertext)
    (O : pos_oracles N) (L0 : Vector.t ciphertext (S N))
    (steps : list (Vector.t ciphertext (S N) * pos_proof N)) : bool :=
    verify_shuffling (one := Fone) (mul := Fmul)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator hs pk O L0 steps.

  Definition dec_proof (N : nat) := @dec_proof (@Zp q) G N.
  Definition dec_oracles (N : nat) := @dec_oracles (@Zp q) G N.
  Definition mk_dec_proof {N : nat} := @mk_dec_proof (@Zp q) G N.
  Definition mk_dec_oracles {N : nat} := @mk_dec_oracles (@Zp q) G N.

  Definition verify_decryption_ins {N : nat} (y : G) (OD : dec_oracles N)
    (L : Vector.t ciphertext (S N)) (Gamma : list G) (parties : list (nat * dec_proof N))
    (delta : list nat) (m : Vector.t G (S N)) : bool :=
    verify_decryption (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := @zp_sub q) (opp := Fopp) (inv := @zp_inv q)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator y OD L Gamma parties delta m.

  (* Algorithm 28 for a mixing session *)
  Definition verify_mixing_ins {N : nat} (hs : Vector.t G (S N)) (pk : ciphertext)
    (O : pos_oracles N) (OD : dec_oracles N) (L0 : Vector.t ciphertext (S N))
    (steps : list (Vector.t ciphertext (S N) * pos_proof N)) (Gamma : list G)
    (parties : list (nat * dec_proof N)) (delta : list nat) (m : Vector.t G (S N)) : bool :=
    verify_mixing (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := @zp_sub q) (opp := Fopp) (inv := @zp_inv q)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator hs pk O OD L0 steps Gamma parties delta m.

  (* scalars and elements as integers, for the driver *)
  Definition of_Z (z : Z) : F.
  Proof. refine (Zpfield.mk_zp (Z.modulo z q) _). apply Z.mod_mod. vm_compute; discriminate. Defined.
  Definition to_Z (x : F) : Z := Zpfield.v x.
  Definition elem_to_Z (x : G) : Z := Schnorr.v x.

End VerificatumIns.
