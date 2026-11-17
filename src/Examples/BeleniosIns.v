(** * The Belenios verifier at Ed25519 *)

(** This file instantiates the certified Belenios verifier
([Backend/BeleniosTally.v]) at Ed25519, the group used by Belenios 3.x
([Curve/Ed25519.v], scalar field [Z/lZ]). The hash functions of Belenios
(SHA-256 over its serialisation of points and strings) are computed by the
OCaml driver [Executable/Beleniosverifier] and passed in through the
[ballot_hashes] and [trustee_hashes] records; they are trusted, together
with the parser of the election archive. The file is extracted by
[src/Extraction/Belenioslib]. *)

(** ** How a Belenios election is checked

Belenios (Cortier, Gaudry and Glondu, Inria) is a descendant of Helios.
The election public key [y = g^x] is the product of the trustees' keys,
and a vote [m] is encrypted with exponential ElGamal,
[Enc(m; r) = (α, β) = (g^r, y^r·g^m)], so that the componentwise product of
ciphertexts encrypts the sum of the votes. All the proofs are Schnorr
proofs or Cramer–Damgård–Schoenmakers disjunctions of Schnorr proofs in
[G × G] with base [(g, y)], each branch stating that a ciphertext encrypts
a value [k]: [(α, β/g^k) = (g, y)^r].

- Individual proof: each answer bit [mᵢ] is in [{0, 1}].
- Overall proof: [Σ mᵢ ∈ [min, max]], on the product ciphertext.
- With blank votes, an extra blank bit [m₀] and the proofs
  [m₀ = 0 ∨ Σ mᵢ = 0] and [m₀ = 1 ∨ Σ mᵢ ∈ [min, max]].
- The ballot is signed with the voter's credential: a Schnorr proof of
  knowledge of [s] with [cred = g^s], bound to the ballot.

Belenios stores a (challenge, response) pair per branch; the verifier
reconstructs the announcements and accepts if the hash of the statement and
announcements equals the sum of the challenges. Belenios writes the
response as [w - x·c] where the library writes [u + c·x], hence negated
challenges in the backend.

The tally is the product of the valid ballots, keeping the last ballot of
each credential, each raised to the weight of its credential. Each trustee
publishes a decryption factor [α_Σ^x] with a Chaum–Pedersen proof, and the
result [g^v = β_Σ / ∏ F] is checked against the published result.

[Backend/BeleniosTally.v] proves that every accepted proof is an accepting
transcript of the library's Schnorr protocol or OR composition
([fs_verify_schnorr_accepting], [fs_verify_or_accepting]), so completeness,
special soundness and honest-verifier zero knowledge are the library's
theorems, and [compute_final_count] returns a certificate of the counting
relation [count]. *)
From Stdlib Require Import Utf8 ZArith Zmod List.
From Backend Require Import BeleniosTally.
From Utility Require Import Util.
From Curve Require Import Ed25519.
From Examples Require Import Ed25519Ins.

Section BeleniosIns.

  Import Ed25519.

  (** [F = Z/lZ] and [G] the order-[l] subgroup of Ed25519. *)
  Local Notation F := Zl.F.
  Local Notation G := Ed.G.

  (** ** The data types at Ed25519

      The records of [Backend/BeleniosTally.v] specialised to this group, for
      the driver: a proof (one challenge/response pair), a ciphertext,
      a question, an answer (ciphertexts and their proofs), a ballot, the
      driver-computed ballot hashes, an election, a trustee and the
      driver-computed trustee hashes. *)
  Definition proof := @proof F.
  Definition ciphertext := @ciphertext G.
  Definition question := question.
  Definition answer := @answer F G.
  Definition ballot := @ballot F G.
  Definition ballot_hashes := @ballot_hashes F G.
  Definition election := @election F G.
  Definition trustee := @trustee F G.
  Definition trustee_hashes := @trustee_hashes F G.

  (** The constructors of the records above. *)
  Definition mk_question := mk_question.
  Definition mk_answer := @mk_answer F G.
  Definition mk_ballot := @mk_ballot F G.
  Definition mk_ballot_hashes := @mk_ballot_hashes F G.
  Definition mk_election := @mk_election F G.
  Definition mk_trustee := @mk_trustee F G.
  Definition mk_trustee_hashes := @mk_trustee_hashes F G.

  (** ** The verifier

      Checks one ballot: the credential signature and every individual,
      overall and blank proof, with the hashes [hs] supplied by the driver. *)
  Definition verify_ballot_ins (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    verify_ballot (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
      (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec)
      E hs b.

  (** The encrypted tally: for every question and choice, the product of the
      weighted ciphertexts of the given ballots. *)
  Definition encrypted_tally_ins (E : election) (bs : list ballot) : list (list ciphertext) :=
    encrypted_tally (zero := Zl.zero) (gid := Ed.gid) (gop := Ed.gop) (gpow := Ed.gpow_fast)
      (Gdec := Ed.Gdec) E bs.

  (** Keeps, for each credential, only its last ballot (Belenios's revoting
      policy). *)
  Definition last_per_credential_ins (bs : list ballot) : list ballot :=
    last_per_credential (Gdec := Ed.Gdec) bs.

  (** The certified verifier and entry point of the extracted code: given the
      ballots in casting order, the published encrypted tally, the trustees
      and the published result, it returns the lists of valid and invalid
      ballots, the final flag (encrypted tally, every trustee's decryption
      proof and the result all check) and a proof that these are related by
      the counting relation [count]. *)
  Definition compute_final_count_ins (E : election) (hs : ballot -> ballot_hashes)
    (th : trustee_hashes) (bs : list ballot) (published : list (list ciphertext))
    (trs : list trustee) (result : list (list F)) :
    existsT (vbs inbs : list ballot) (bfinal : bool),
      count (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
        (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec)
        E hs (finished (List.rev bs) vbs inbs bfinal) :=
    compute_final_count (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
      (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec)
      E hs th bs published trs result.

  (** The Ed25519 base point, exported for the driver. *)
  Definition base : G := Ed.B.

End BeleniosIns.
