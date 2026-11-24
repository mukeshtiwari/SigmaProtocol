(** * Schnorr, Chaum–Pedersen and approval ballots at Ed25519 *)

(** The library at Ed25519 (RFC 8032): the group is the order-[l] subgroup of
the twisted Edwards curve birationally equivalent to Curve25519
([Curve/Ed25519.v], module [Ed]), with
[l = 2^252 + 27742317777372353535851937790883648493], and the scalar field
is [Z/lZ] (module [Zl]). The file mirrors [P256Ins.v].

Everything is an instance of the generic definitions of [Crypto/Sigma.v],
[Crypto/ChaumPedersen.v], [Crypto/EncProof.v] and [Frontend/Approval.v];
the only curve-specific inputs are the group operations, the fast
scalar multiplication and the base point. The file provides

- Schnorr proofs of knowledge of [x] with [h = g^x];
- Chaum–Pedersen proofs of [c₁ = g^x ∧ c₂ = h^x];
- approval-voting ballots: exponential ElGamal encryptions of 0/1 votes
  under [h], each with a disjunctive proof that it encrypts [g^0] or [g^1],
  and an overall proof that the product of the ciphertexts encrypts
  [g^k] for some [k] between [0] and the number of candidates.

The interactive provers take their randomness and challenges as
arguments. In the non-interactive ballot the challenges are produced by
hash functions supplied by the OCaml driver ([Executable/Ed25519code]), and the
helpers at the end of the file flatten announcements so they can be
hashed. The file is extracted by [src/Extraction/Ed25519lib] and used for
tests and benchmarks.

Group elements carry a proof of membership in the order-[l] subgroup;
[point_to_Z] exposes the affine coordinates [(x, y)] of the underlying
point (fiat-crypto's affine Edwards points). *)
From Stdlib Require Import Utf8 ZArith Zmod Vector Lia.
From Sigma Require Import Sigma ChaumPedersen EncProof.
From Frontend Require Import Approval.
From Curve Require Import Ed25519.
From Utility Require Import Util.
Import VectorNotations.

Section Ed25519Ins.

  Import Ed25519.

  (** [F] is the scalar field and [G] the prime-order group of the curve; the
      third notation names the group order. *)
  Local Notation F := Zl.F.
  Local Notation G := Ed.G.
  Local Notation l := (2^252 + 27742317777372353535851937790883648493)%Z.

  (** ** Conversions for the driver

      [of_Z] reduces an integer modulo the group order into [F]. *)
  Definition of_Z (z : Z) : F := Zl.of_Z z.
  (** The canonical integer representative of a scalar. *)
  Definition to_Z (k : F) : Z := Zl.to_Z k.
  (** The affine coordinates [(x, y)] of a point, as integers. *)
  Definition point_to_Z (P : G) : Z * Z :=
    (Zmod.unsigned (fst (proj1_sig (proj1_sig P))),
     Zmod.unsigned (snd (proj1_sig (proj1_sig P)))).

  (** ** Keys

      The standard base point of the curve. *)
  Definition g : G := Ed.B.
  (** A fixed test secret key, [x = 3]. *)
  Definition x : F := of_Z 3.
  (** The corresponding public key [h = g^x]. *)
  Definition h : G := Ed.gpow_fast g x.

  (** ** Schnorr: knowledge of [x] with [h = g^x]

      The prover's first message [g^u]. *)
  Definition schnorr_protocol_commitment_ins (u : F) : G :=
    @schnorr_protocol_commitment F G Ed.gpow_fast g u.

  (** The honest transcript [(g^u, c, u + c·x)]. *)
  Definition schnorr_protocol_construction_ins (u c : F) :
    @sigma_proto F G 1 1 1 :=
    @schnorr_protocol F Zl.add Zl.mul G Ed.gpow_fast x g u c.

  (** The verifier: accepts [(a, c, r)] iff [g^r = a·h^c]. *)
  Definition schnorr_protocol_verification_ins
    (t : @sigma_proto F G 1 1 1) : bool :=
    @accepting_conversation F G Ed.gop Ed.gpow_fast Ed.Gdec g h t.

  (** ** Chaum–Pedersen: [c₁ = g^x ∧ c₂ = h^x]

      The first public value [c₁ = g^x]. *)
  Definition c₁ : G := Ed.gpow_fast g x.
  (** The second public value [c₂ = h^x]. *)
  Definition c₂ : G := Ed.gpow_fast h x.

  (** The commitment pair [[g^u; h^u]]. *)
  Definition construct_cp_conversations_schnorr_commitment_ins (u : F) :
    Vector.t G 2 :=
    @construct_cp_conversations_schnorr_commitment F G Ed.gpow_fast g h u.

  (** The honest transcript [([g^u; h^u], c, u + c·x)]. *)
  Definition construct_cp_conversations_schnorr_ins (u c : F) :
    @sigma_proto F G 2 1 1 :=
    @construct_cp_conversations_schnorr F Zl.add Zl.mul G Ed.gpow_fast x g h u c.

  (** The verifier: [g^r = a₁·c₁^c] and [h^r = a₂·c₂^c]. *)
  Definition generalised_cp_accepting_conversations_ins
    (t : @sigma_proto F G 2 1 1) : bool :=
    @generalised_cp_accepting_conversations F G Ed.gop Ed.gpow_fast Ed.Gdec
      g h c₁ c₂ t.

  (** ** Approval ballots

      Encrypts each vote [mᵢ] as [(g^rᵢ, g^mᵢ·h^rᵢ)] with randomness [rᵢ]. *)
  Definition encrypt_ballot_ins {n : nat} (rs ms : Vector.t F n) :
    Vector.t (G * G) n :=
    @encrypt_ballot F G Ed.gop Ed.gpow_fast n g h rs ms.

  (** The announcements of the per-vote 0/1 proofs, from the prover
      randomness [uscs] (for each vote, two commitment exponents and one
      simulated challenge). *)
  Definition generate_ballot_commitment_ins {n : nat}
    (rs ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n) :
    Vector.t (Vector.t (G * G) 2) n :=
    @generate_ballot_commitment F Zl.zero Zl.one Zl.opp Zl.Fdec
      G Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs.

  (** Encrypts every vote and attaches its 0/1 disjunctive proof, given the
      vector [c] of per-vote challenges. *)
  Definition encrypt_ballot_and_generate_enc_proof_ins {n : nat}
    (rs ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n)
    (c : Vector.t F n) :
    Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n :=
    @encrypt_ballot_and_generate_enc_proof F Zl.zero Zl.one Zl.add Zl.mul
      Zl.sub Zl.opp Zl.Fdec G Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs c.

  (** The same ballot computed without a case analysis on the votes
      ([encrypt_ballot_and_generate_enc_proof_ct] of [Frontend/Approval.v]);
      it equals [encrypt_ballot_and_generate_enc_proof_ins] when every vote
      is [0] or [1] ([encrypt_ballot_and_generate_enc_proof_ct_eq]). *)
  Definition encrypt_ballot_and_generate_enc_proof_ct_ins {n : nat}
    (rs ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n)
    (c : Vector.t F n) :
    Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n :=
    @encrypt_ballot_and_generate_enc_proof_ct F Zl.zero Zl.one Zl.add Zl.mul
      Zl.sub Zl.opp G Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs c.

  Lemma encrypt_ballot_and_generate_enc_proof_ct_ins_eq {n : nat}
    (rs ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n) (c : Vector.t F n) :
    (∀ i : Fin.t n, Vector.nth ms i = Zl.zero ∨ Vector.nth ms i = Zl.one) ->
    encrypt_ballot_and_generate_enc_proof_ct_ins rs ms uscs c =
    encrypt_ballot_and_generate_enc_proof_ins rs ms uscs c.
  Proof.
    intro hm.
    exact (@encrypt_ballot_and_generate_enc_proof_ct_eq F Zl.zero Zl.one Zl.add Zl.mul
      Zl.sub Zl.div Zl.opp Zl.inv Zl.Fdec G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast
      Ed.ed25519_vspace_fast n rs g h ms uscs c hm).
  Qed.

  (** Checks every per-vote 0/1 proof of a ballot. *)
  Definition verify_encryption_ballot_proof_ins {n : nat}
    (proof : Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n) : bool :=
    @verify_encryption_ballot_proof F Zl.zero Zl.one Zl.add Zl.Fdec
      G Ed.ginv Ed.gop Ed.gpow_fast Ed.Gdec n g h proof.

  (** The overall proof for [n + 1] votes: the product of the ciphertexts
      encrypts [g^k] with [k] the number of ones, as an [(n + 2)]-branch
      disjunctive proof over [g^0, …, g^(n+1)] with witness [Σ rᵢ]. *)
  Definition generate_overall_proof_ins {n : nat}
    (rs ms : Vector.t F (S n)) (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) :
    @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n) :=
    @generate_overall_proof F Zl.zero Zl.one Zl.add Zl.mul Zl.sub Zl.opp Zl.Fdec
      G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs c.

  (** Checks the overall proof against the product of the ciphertexts [cps]. *)
  Definition verify_overall_proof_ins {n : nat}
    (cps : Vector.t (G * G) n)
    (pf : @sigma_proto F (G * G) (S n) (S (S n)) (S n)) : bool :=
    @verify_overall_proof F Zl.zero Zl.add Zl.Fdec
      G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast Ed.Gdec n g h cps pf.

  (** Accepts a full ballot iff all per-vote proofs and the overall proof are
      accepting. *)
  Definition verify_ballot_ins {n : nat}
    (b : Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n *
         @sigma_proto F (G * G) (S n) (S (S n)) (S n)) : bool :=
    @verify_ballot F Zl.zero Zl.one Zl.add Zl.Fdec
      G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast Ed.Gdec n g h b.

  (** ** Non-interactive ballots

      Flattens the per-vote announcements, two pairs of points per vote, into
      a vector of [4·n] points for hashing. *)
  Definition vector_unfold : ∀ {n : nat}, Vector.t (Vector.t (G * G) 2) n ->
    Vector.t G (4 * n).
  Proof.
    refine
    (fix fn {n : nat} (v : Vector.t (Vector.t (G * G) 2) n) :
      Vector.t G (4 * n) :=
      match v as v' in Vector.t _ n' return Vector.t G (4 * n') with
      | [] =>  []
      | @Vector.cons _ vh nt vt =>
         let ret := fn vt in _
      end).
    assert (ha : 4 * S nt = 4 + 4 * nt) by nia.
    rewrite ha; clear ha.
    destruct (vector_inv_S vh) as ((vha, vhb) & vht & _).
    destruct (vector_inv_S vht) as ((vhta, vhtb) & _ & _).
    exact (vha :: vhb :: vhta :: vhtb :: ret).
  Defined.

  (** Flattens a vector of announcement pairs into a list of points. *)
  Definition announcement_to_list {k : nat} (a : Vector.t (G * G) k) : list G :=
    Vector.fold_right (fun '(u, v) acc => (u :: v :: acc)%list) a List.nil.

  (** The non-interactive ballot. [fn] returns the [n + 1] per-vote challenges
      from [g], [h] and all per-vote announcements; [fo] returns the overall
      challenge from [g], [h] and the overall proof's announcement. That
      announcement does not depend on the challenge, so it is first computed
      with the challenge zero ([pf0]) and the proof is then recomputed with
      the real challenge. Note that neither hash input includes the
      ciphertexts themselves. *)
  Definition nizk_encrypt_ballot_with_overall_proof_ins {n : nat}
    (fn : ∀ {m : nat}, Vector.t G m -> Vector.t F (S n))
    (fo : ∀ {m : nat}, Vector.t G m -> F)
    (rs ms : Vector.t F (S n))
    (uscs : Vector.t (Vector.t F 3) (S n))
    (uscs' : Vector.t F ((2 + n) + (1 + n))) :
    Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) (S n) *
    @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n) :=
    let comm := generate_ballot_commitment_ins rs ms uscs in
    let c := fn ([g; h] ++ vector_unfold comm) in
    let b := encrypt_ballot_and_generate_enc_proof_ins rs ms uscs c in
    let pf0 := generate_overall_proof_ins rs ms uscs' Zl.zero in
    let co := fo (Vector.of_list
      ((g :: h :: announcement_to_list (announcement pf0))%list)) in
    (b, generate_overall_proof_ins rs ms uscs' co).

End Ed25519Ins.
