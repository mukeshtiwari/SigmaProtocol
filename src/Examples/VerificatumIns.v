(** * The Verificatum verifier at the Helios group *)

(** This file instantiates the verifier of the Verificatum mix-net
([Backend/VerificatumVerifier.v]) at the group of the Helios instance
([Examples/HeliosTallyIns.v]): the order-[q] subgroup of [Z_p^*] for the
2048-bit prime [p] and the 256-bit prime [q] with [p = k·q + 1], whose
primality is certified by [primeP.v] and [primeQ.v], and the standard
Helios generator [g]. The demo of Verificatum 3.1.0 shipped in
[Executable/Vmnverifier/data] was run with exactly this group (via
[vog -gen ModPGroup -explic -roenc p g q]).

The file is extracted to OCaml by [src/Extraction/Verificatumlib]. *)

(** ** How a Verificatum mixing session is checked

A mix-net takes a list of ElGamal ciphertexts and outputs the same
plaintexts, re-encrypted and in a secret order. Each mix-server proves
that it did so with the proof of a shuffle of Terelius and Wikström
(AFRICACRYPT 2010; [Crypto/ShuffleTW.v]). For inputs [w₀ … w_N] and
outputs [w'₀ … w'_N] the claim is that there are a permutation [π] and
exponents [sᵢ] with [w'ᵢ = Enc(1; sᵢ)·w_π(i)], where
[Enc(1; r) = (g^r, pk^r)].

- The prover commits to the permutation, [uᵢ = g^rᵢ·h_π(i)], with
  independent generators [h₀ … h_N].
- The verifier sends a random vector [e]; let [e'] be [e] permuted by [π].
- The prover publishes the bridging commitments
  [Bᵢ = g^βᵢ·B_(i-1)^e'ᵢ] with [B_(-1) = h₀], which accumulate [∏ e'ᵢ].
- With [A = ∏ uᵢ^eᵢ], [C = ∏ uᵢ / ∏ hᵢ], [D = B_N·h₀^(-∏ eᵢ)] and
  [F = ∏ wᵢ^eᵢ], the prover shows knowledge of [(a, c, d, f, β, e')]
  satisfying
  [A = g^a·∏ hᵢ^e'ᵢ], [C = g^c], [D = g^d], [Bᵢ = g^βᵢ·B_(i-1)^e'ᵢ] and
  [F = Enc(1; -f)·∏ w'ᵢ^e'ᵢ].

The first equation says that [u] commits to a matrix mapping [e] to [e'],
the second that it maps the all-ones vector to itself, the third and
fourth that [∏ e'ᵢ = ∏ eᵢ]; for random [e] such a matrix is a permutation
matrix, and the fifth equation says that the outputs are re-encrypted
inputs under it. Once [e] is fixed the five equations are one linear
statement, an instance of the generalised Okamoto protocol
([tw_relation_iff] in [Crypto/ShuffleTW.v]); the verifier's final check is
its acceptance test ([verify_pos_accepting]).

Joint decryption: party [l] publishes decryption factors with a
Chaum–Pedersen proof; the verifier combines the selected parties with
their Lagrange coefficients, checks the batched Chaum–Pedersen equations,
and checks that each claimed plaintext is [mᵢ = vᵢ·fᵢ].

The algorithm numbers below refer to Wikström's document ‘How to
implement a stand-alone verifier for the Verificatum mix-net’. The
byte-tree parser, the SHA-256 based random oracles and the derivation of
the generators [hᵢ] are computed by the OCaml driver [Executable/Vmnverifier]
and are trusted; they enter through the [pos_oracles] and [dec_oracles]
records. *)
From Stdlib Require Import Utf8 ZArith Vector List.
From Sigma Require Import Sigma Okamoto MultiExp ShuffleTW.
From Backend Require Import VerificatumVerifier.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns.
Import Vspace Schnorr Zpfield Zpgroup.

(** ** The group and its operations *)
Section VerificatumIns.

  (** [p], [q], the scalar field [F = Z_q] and the group [G] of order [q],
      all taken from [HeliosTallyIns]. *)
  Local Notation p := HeliosTallyIns.p.
  Local Notation q := HeliosTallyIns.q.
  Local Notation F := (@Zp q).
  Local Notation G := (@Schnorr_group p q).

  (** The field operations of [Z_q]: [Fzero], [Fone], [Fadd], [Fmul],
      [Fopp] and the decidable equality [Fdec]. *)
  Definition Fzero : F := @Zpfield.zero q HeliosTallyIns.prime_q.
  Definition Fone : F := @Zpfield.one q HeliosTallyIns.prime_q.
  Definition Fadd : F -> F -> F := @zp_add q.
  Definition Fmul : F -> F -> F := @zp_mul q.
  Definition Fopp : F -> F := @zp_opp q HeliosTallyIns.prime_q.
  Definition Fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  (** The group operations at [(p, q)]: [Gone], [Ginv], [Gmul], [Gpow] and
      [Gdec]. [Ginv] and [Gpow] use the cofactor [k] and [safe_prime] of
      [HeliosTallyIns]. *)
  Definition Gone : G := @Schnorr.one p q HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Ginv : G -> G := @inv_schnorr_group HeliosTallyIns.k p q HeliosTallyIns.safe_prime HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Gmul : G -> G -> G := @mul_schnorr_group p q HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Gpow : G -> F -> G := @pow HeliosTallyIns.k p q HeliosTallyIns.safe_prime HeliosTallyIns.prime_p HeliosTallyIns.prime_q.
  Definition Gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.

  (** The generator [g] of [HeliosTallyIns]. *)
  Definition generator : G := HeliosTallyIns.g.

  (** ** Proofs of shuffle

      An ElGamal ciphertext, a pair of group elements. *)
  Definition ciphertext : Type := (G * G)%type.
  (** The proof-of-shuffle record of [Backend/VerificatumVerifier.v] for
      [N + 1] ciphertexts, the record of its random-oracle values (computed
      by the driver), and their constructors [mk_pos_proof] and
      [mk_pos_oracles]. *)
  Definition pos_proof (N : nat) := @pos_proof (@Zp q) G N.
  Definition pos_oracles (N : nat) := @pos_oracles (@Zp q) G N.
  Definition mk_pos_proof {N : nat} := @mk_pos_proof (@Zp q) G N.
  Definition mk_pos_oracles {N : nat} := @mk_pos_oracles (@Zp q) G N.

  (** Verifies one proof of shuffle from [w] to [w'] under the shuffle public
      key [pk] and generators [hs] (Algorithm 19 of Wikström's document). *)
  Definition verify_pos_ins {N : nat} (hs : Vector.t G (S N)) (pk : ciphertext)
    (O : pos_oracles N) (w w' : Vector.t ciphertext (S N)) (pf : pos_proof N) : bool :=
    verify_pos (one := Fone) (mul := Fmul)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator hs pk O w w' pf.

  (** Verifies the whole shuffling phase (Algorithm 25): [L0] is the input
      list and [steps] the output list and proof of each mix-server. It
      accepts iff every rejected proof left its list unchanged and at least
      one proof is valid. *)
  Definition verify_shuffling_ins {N : nat} (hs : Vector.t G (S N)) (pk : ciphertext)
    (O : pos_oracles N) (L0 : Vector.t ciphertext (S N))
    (steps : list (Vector.t ciphertext (S N) * pos_proof N)) : bool :=
    verify_shuffling (one := Fone) (mul := Fmul)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator hs pk O L0 steps.

  (** ** Decryption

      The decryption-proof record, its oracle record (computed by the
      driver) and their constructors. *)
  Definition dec_proof (N : nat) := @dec_proof (@Zp q) G N.
  Definition dec_oracles (N : nat) := @dec_oracles (@Zp q) G N.
  Definition mk_dec_proof {N : nat} := @mk_dec_proof (@Zp q) G N.
  Definition mk_dec_oracles {N : nat} := @mk_dec_oracles (@Zp q) G N.

  (** Verifies the joint decryption of [L] to the plaintexts [m] (Algorithm 22
      with the plaintext check of Algorithm 27), for the joint public key [y],
      the parties' public keys [Gamma], their proofs [parties] and the
      selected set [delta]. *)
  Definition verify_decryption_ins {N : nat} (y : G) (OD : dec_oracles N)
    (L : Vector.t ciphertext (S N)) (Gamma : list G) (parties : list (nat * dec_proof N))
    (delta : list nat) (m : Vector.t G (S N)) : bool :=
    verify_decryption (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := @zp_sub q) (opp := Fopp) (inv := @zp_inv q)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator y OD L Gamma parties delta m.

  (** Verifies a complete mixing session (Algorithm 28): the shuffling, the
      agreement of the joint public key with [pk], and the decryption of the
      final list to [m]. This is the entry point used by the driver. *)
  Definition verify_mixing_ins {N : nat} (hs : Vector.t G (S N)) (pk : ciphertext)
    (O : pos_oracles N) (OD : dec_oracles N) (L0 : Vector.t ciphertext (S N))
    (steps : list (Vector.t ciphertext (S N) * pos_proof N)) (Gamma : list G)
    (parties : list (nat * dec_proof N)) (delta : list nat) (m : Vector.t G (S N)) : bool :=
    verify_mixing (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := @zp_sub q) (opp := Fopp) (inv := @zp_inv q)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      generator hs pk O OD L0 steps Gamma parties delta m.

  (** ** Conversions for the driver

      [of_Z] reduces an integer modulo [q]; [to_Z] and [elem_to_Z] return the
      integer representative of a scalar or group element. *)
  Definition of_Z (z : Z) : F.
  Proof. refine (Zpfield.mk_zp (Z.modulo z q) _). apply Z.mod_mod. vm_compute; discriminate. Defined.
  Definition to_Z (x : F) : Z := Zpfield.v x.
  Definition elem_to_Z (x : G) : Z := Schnorr.v x.

End VerificatumIns.
