(* The Belenios verifier (Backend/BeleniosTally.v) at Ed25519, the group
   used by Belenios 3.x. The hash functions of Belenios (SHA-256 over its
   serialisation of points and strings) are computed by the driver
   (Executable/Beleniosverifier) and passed in through the ballot_hashes
   and trustee_hashes records. *)

(* How a Belenios election works, and what this verifier checks.

   Belenios is the open-source voting system developed at Inria, a
   descendant of Helios. All of its proofs are Schnorr proofs or
   disjunctions of Schnorr proofs, so the whole verifier is an instance of
   two protocols of the library.

   Setting. G is a group of prime order q with generator g (here Ed25519),
   and y = g^x is the election public key, the product of the trustees'
   keys. A vote is encrypted with exponential ElGamal:

     Enc(m; r) = (α, β) = (g^r, y^r · g^m).

   The componentwise product of ciphertexts encrypts the sum of the votes,
   so the tally is computed without opening any ballot.

   Ballot. For every answer i of a question the voter encrypts a bit m_i
   as (α_i, β_i) and attaches three kinds of proof. Each is a disjunction
   in G × G with the common base (g, y), and each branch states that a
   ciphertext encrypts a given value k:

     (α, β / g^k) = (g, y)^r.

   - individual proof: m_i ∈ {0, 1}, the two branches k = 0 and k = 1;
   - overall proof: Σ m_i ∈ [min, max], on the product ciphertext
     (∏ α_i, ∏ β_i), one branch per admissible total;
   - with blank votes, a blank bit m_0 is added: the blank proof states
     m_0 = 0 ∨ m_Σ = 0 and the overall proof m_0 = 1 ∨ m_Σ ∈ [min, max],
     whose branches talk about different ciphertexts.

   The ballot is signed with the voter's credential, a Schnorr proof of
   knowledge of s with cred = g^s bound to the ballot, which is what
   prevents the server from adding ballots.

   Verification of a proof. Belenios stores (challenge, response) for
   every branch. The verifier reconstructs the announcements

     A_k = (g, y)^{response_k} · (α, β / g^k)^{challenge_k}

   and accepts if the hash of the statement and of the A_k equals the sum
   of the challenges. This is the Or composition of Cramer, Damgård and
   Schoenmakers: the prover runs the real protocol on the true branch,
   simulates the others, and the branch challenges are forced to add up
   to the hash.

   Tally. The valid ballots, the last one of each credential, are
   multiplied, each raised to the weight w_b of its credential:

     (α_Σ, β_Σ) = ∏_b (α_b, β_b)^{w_b}.

   Decryption. Every trustee with key X = g^x publishes the factor
   F = α_Σ^x with a Chaum–Pedersen proof, a Schnorr proof in G × G, of

     (X, F) = (g, α_Σ)^x.

   The result is g^v = β_Σ / ∏ F, and v is recovered by a search for the
   discrete logarithm, which is small.

   What is proved. Backend/BeleniosTally.v shows that a proof accepted by
   this verifier is an accepting transcript of the library's Schnorr
   protocol or Or composition (fs_verify_schnorr_accepting,
   fs_verify_or_accepting), so completeness, special soundness and
   honest-verifier zero knowledge are the library's theorems. Belenios
   writes the response as w − x·c where the library writes u + c·x, hence
   the negated challenges. What is trusted: the parser of the archive and
   the SHA-256 hashes computed by the driver. *)

From Stdlib Require Import Utf8 ZArith Zmod List.
From Backend Require Import BeleniosTally.
From Utility Require Import Util.
From Curve Require Import Ed25519.
From Examples Require Import Ed25519Ins.

Section BeleniosIns.

  Import Ed25519.

  Local Notation F := Zl.F.
  Local Notation G := Ed.G.

  (* the types, at Ed25519 *)
  Definition proof := @proof F.
  Definition ciphertext := @ciphertext G.
  Definition question := question.
  Definition answer := @answer F G.
  Definition ballot := @ballot F G.
  Definition ballot_hashes := @ballot_hashes F G.
  Definition election := @election F G.
  Definition trustee := @trustee F G.
  Definition trustee_hashes := @trustee_hashes F G.

  Definition mk_question := mk_question.
  Definition mk_answer := @mk_answer F G.
  Definition mk_ballot := @mk_ballot F G.
  Definition mk_ballot_hashes := @mk_ballot_hashes F G.
  Definition mk_election := @mk_election F G.
  Definition mk_trustee := @mk_trustee F G.
  Definition mk_trustee_hashes := @mk_trustee_hashes F G.

  Definition verify_ballot_ins (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    verify_ballot (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
      (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec) 
      E hs b.

  Definition encrypted_tally_ins (E : election) (bs : list ballot) : list (list ciphertext) :=
    encrypted_tally (zero := Zl.zero) (gid := Ed.gid) (gop := Ed.gop) (gpow := Ed.gpow_fast) 
      (Gdec := Ed.Gdec) E bs.

  Definition last_per_credential_ins (bs : list ballot) : list ballot :=
    last_per_credential (Gdec := Ed.Gdec) bs.

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

  (* the base point, for the driver *)
  Definition base : G := Ed.B.

End BeleniosIns.
