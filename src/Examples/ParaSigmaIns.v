(** * Parallel Schnorr protocol over a toy Schnorr group *)

(** A concrete instance of the parallel composition of Schnorr's protocol
([Crypto/ParallelSigma.v]): two independent runs of the protocol for the
same statement [h = g^x], with two commitments, two challenges and two
responses. (Parallel repetition is the standard way to shrink the
soundness error of a protocol with a small challenge space.) The file is extracted to OCaml by
[src/Extraction/ParaSigmalib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The file defines the two commitments, the honest transcript for given
challenges, a non-interactive variant whose challenge vector is produced by
a caller-supplied hash of the statement and the commitments, and the
verifier, which checks each of the two Schnorr equations. *)
From Stdlib Require Import Utf8 ZArith
Vector.
From Sigma Require Import Sigma
  ParallelSigma.
From Utility Require Import Zpstar.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup
  VectorNotations.

(** ** Parameters and the instance *)
Section Ins.

  (** The subgroup order [q = 2963]. *)
  Definition q : Z := 2963.

  (** The modulus [p = 2q + 1 = 5927], a safe prime. *)
  Definition p : Z := 2 * q + 1.

  (** [q] is prime, by trial division ([is_prime_sqrt_correct]). *)
  Theorem prime_q : Znumtheory.prime q : Prop : Type.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  (** [p] is prime, by trial division. *)
  Theorem prime_p : Znumtheory.prime p : Prop : Type.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  (** [p = 2q + 1], the shape required by the [Zpstar] group operations. *)
  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.

  (** The prover's secret exponent [x = 3]. *)
  Definition x : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  (** The generator [g = 4 = 2²]: a quadratic residue, hence of order [q];
      membership ([4^q mod p = 1]) is checked by [vm_compute]. *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  (** The public key [h = g^x], computed at definition time. *)
  Definition h : @Schnorr_group p q :=
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x.

  (** The two commitments [[g^u₁; g^u₂]] for randomness [us = [u₁; u₂]]. *)
  Definition construct_parallel_conversations_schnorr_commitment_ins
    (us :  Vector.t (@Zp q) 2) : Vector.t (@Schnorr_group p q) 2.
  Proof.
    refine(@construct_parallel_conversations_schnorr_commitment
      (@Zp q) (@Schnorr_group p q) pow 2 g us).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** The honest parallel transcript: commitments [g^uᵢ], challenges [cᵢ]
      and responses [uᵢ + cᵢ·x] for [i = 1, 2]. *)
  Definition construct_parallel_conversations_schnorr_ins
    (us cs : Vector.t (@Zp q) 2) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 2 2.
  Proof.
    refine
    (@construct_parallel_conversations_schnorr (@Zp q)
    zp_add zp_mul (@Schnorr_group p q) pow 2 x g us cs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** The non-interactive proof: the two challenges are [fn] applied to
      [[p; q; g; h]] followed by the two commitments. [fn] is supplied by the
      OCaml caller as a hash function (strong Fiat–Shamir). *)
  Definition nizk_construct_parallel_conversations_schnorr_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> Vector.t (@Zp q) 2)
    (us : Vector.t (@Zp q) 2) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 2 2.
  Proof.
    set (comm := construct_parallel_conversations_schnorr_commitment_ins us).
    set (cs := fn _ ([inl p; inl q;
      inr g; inr h] ++ Vector.map inr comm)).
    refine(construct_parallel_conversations_schnorr_ins us cs).
  Defined.

  (** The verifier: accepts iff [g^rᵢ = aᵢ·h^cᵢ] for both coordinates
      ([generalised_parallel_accepting_conversations]). *)
  Definition generalised_parallel_accepting_conversations_ins :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 2 2 -> bool.
  Proof.
    intro transcript.
    refine
    (@generalised_parallel_accepting_conversations (@Zp q) (@Schnorr_group p q)
    mul_schnorr_group pow Schnorr.dec_zpstar _ g h transcript).
    eapply prime_p.
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
