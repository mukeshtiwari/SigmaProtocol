From Stdlib Require Import Utf8 ZArith Vector Psatz.
From Sigma Require Import Sigma EncProof Elgamal.
From Frontend Require Import Approval.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns.
Import Vspace Schnorr Zpfield Zpgroup VectorNotations.

(** * Helios voting client at the IACR election parameters

    This file contains the voter-side (front end) functions of
    [Frontend/Approval.v], instantiated at the 2048-bit Helios group of
    [Examples/HeliosTallyIns.v]. Each answer is encrypted as
    [Enc(g^m; r)] with [m ∈ {0, 1}] and proved to be 0 or 1 with a
    two-branch disjunctive encryption proof. The election key [h] is a
    parameter, so the same code serves any of the IACR elections (or a
    fresh key).

    The functions are extracted with [Examples/HeliosTallyIns.v] by
    [src/Extraction/HeliosTallylib/Extraction.v]. They are used to benchmark
    ballot encryption and proof generation at real-world parameters
    ([src/Executable/HeliosBenchcode], and the JavaScript build in
    [src/Executable/HeliosJscode]). Nothing is proved here. The
    correctness results are those of [Frontend/Approval.v]. *)
Section HeliosFrontend.

  (** Entrywise encryption [Enc(g^m_i; r_i)] of an answer vector under [h]. *)
  Definition helios_encrypt_ballot {n : nat} (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n) :
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@encrypt_ballot (@Zp q) (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q)
      _ g h rs ms).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

  (** Encryption together with the 0-or-1 proofs, one challenge per answer.
      [uscs] holds each proof's commitment randomness and simulated
      challenge. *)
  Definition helios_encrypt_ballot_and_generate_enc_proof {n : nat}
    (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n)
    (c : Vector.t (@Zp q) n) :
    Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) *
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n.
  Proof.
    refine(@encrypt_ballot_and_generate_enc_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_mul zp_sub
      zp_opp zp_dec (@Schnorr_group p q)
      (@inv_schnorr_group k p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q) _
      g h rs ms uscs c).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

  (** The announcements of the ballot's proofs. The non-interactive ballot
      derives its challenges from them, and
      [Approval.ballot_commitment_announcement] shows that they are exactly
      the announcements of the proofs produced by
      [helios_encrypt_ballot_and_generate_enc_proof]. *)
  Definition helios_generate_ballot_commitment {n : nat}
    (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) :
    Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n.
  Proof.
    refine(@generate_ballot_commitment (@Zp q) Zpfield.zero Zpfield.one
      zp_opp zp_dec (@Schnorr_group p q)
      (@inv_schnorr_group k p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q) n g h rs ms uscs).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

  (** Flattens [n] announcements (two pairs each) into [4n] group elements,
      the input to the hash. *)
  Definition helios_vector_unfold : ∀ {n : nat},
    Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n ->
    Vector.t (@Schnorr_group p q) (4 * n).
  Proof.
    refine
    (fix fn {n : nat} (v : Vector.t (Vector.t (@Schnorr_group p q * @Schnorr_group p q) 2) n) :
      Vector.t ((@Schnorr_group p q)) (4 * n) :=
      match v as v' in Vector.t _ n' return
        Vector.t ((@Schnorr_group p q)) (4 * n')
      with
      | [] =>  []
      | @Vector.cons _ vh nt vt =>
         let ret := fn vt in _
      end).
    assert (ha : 4 * S nt = 4 + 4 * nt). nia.
    rewrite ha; clear ha.
    destruct (vector_inv_S vh) as ((vha, vhb) & vht & _).
    destruct (vector_inv_S vht) as ((vhta, vhtb) & _ & _).
    exact (vha :: vhb :: vhta :: vhtb :: ret).
  Defined.

  (** The non-interactive ballot. The [n] challenges are [fn] applied to
      [(p, q, g, h)] and all announcements. [fn] is the hash, supplied by the
      caller. *)
  Definition helios_nizk_encrypt_ballot_and_generate_enc_proof {n : nat}
    (fn : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> Vector.t (@Zp q) n)
    (h : @Schnorr_group p q)
    (rs ms : Vector.t (@Zp q) n)
    (uscs : Vector.t (Vector.t (@Zp q) 3) n) :
    Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) *
      @Sigma.sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n.
  Proof.
    set (comm := helios_generate_ballot_commitment h rs ms uscs).
    set (c := fn _ ([inl p; inl q; inr g; inr h] ++
      Vector.map inr (helios_vector_unfold comm))).
    exact(helios_encrypt_ballot_and_generate_enc_proof h rs ms uscs c).
  Defined.

  (** Verification of the 0-or-1 proofs of a ballot under key [h]. *)
  Definition helios_verify_encryption_ballot_proof {n : nat}
    (h : @Schnorr_group p q)
    (proof : Vector.t ((@Schnorr_group p q) * (@Schnorr_group p q) *
    @Sigma.sigma_proto (@Zp q)
    (@Schnorr_group p q * @Schnorr_group p q) 2 3 2) n) : bool.
  Proof.
    refine(@verify_encryption_ballot_proof (@Zp q)
      Zpfield.zero Zpfield.one zp_add zp_dec
      (@Schnorr_group p q)
      (@inv_schnorr_group k p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      (@pow k p q safe_prime prime_p prime_q)
      Schnorr.dec_zpstar _ g h proof).
    all: (try eapply prime_q).
    all: (try eapply prime_p).
    all: (try eapply safe_prime).
  Defined.

End HeliosFrontend.
