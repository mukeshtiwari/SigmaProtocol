(** * Schnorr's protocol over a toy Schnorr group *)

(** A concrete instance of the generic Schnorr protocol of
[Crypto/Sigma.v] (module [Schnorr]), used to exercise the code and to
extract a small OCaml library ([src/Extraction/Sigmalib], which runs
[Separate Extraction SigmaIns]).

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]).

The statement is knowledge of the discrete logarithm [x] of [h = g^x], with
generator [g = 4] and secret [x = 3]. The file builds the prover's
commitment [g^u], the full transcript for a given challenge, a
non-interactive transcript whose challenge is obtained from a caller-supplied
hash function (strong Fiat–Shamir: the hash covers [p], [q], [g], [h] and
the commitment) and the verifier's acceptance check. Nothing is proved
here: the security properties are those of [Crypto/Sigma.v]. *)
From Stdlib Require Import Utf8 ZArith
Vector.
From Crypto Require Import Sigma.
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

  (** The prover's secret exponent [x = 3] in [Z_q]. *)
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

  (** The prover's first message [g^u] for the commitment randomness [u]. *)
  Definition schnorr_protocol_commitment_ins (u : @Zp q) : (@Schnorr_group p q).
  Proof.
    refine(@schnorr_protocol_commitment (@Zp q) (@Schnorr_group p q)
      pow g u).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** The honest interactive transcript [(g^u, c, u + c·x)] for randomness [u]
      and challenge [c]. *)
  Definition schnorr_protocol_construction_ins (u c : @Zp q) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1.
  Proof.
    refine (@schnorr_protocol Zp zp_add zp_mul
      Schnorr_group pow x g u c).
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The non-interactive proof: the challenge is [fn] applied to the
      statement and the commitment, [[p; q; g; h; g^u]] (strong Fiat–Shamir).
      [fn] is a parameter, supplied as a hash function by the OCaml caller;
      it is treated as a random oracle only informally. *)
  Definition nizk_schnorr_protocol_construction_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (u : @Zp q) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1.
  Proof.
    set (comm := schnorr_protocol_commitment_ins u).
    set (c := fn _ [inl p; inl q;
    inr g; inr h; inr comm]).
    refine (schnorr_protocol_construction_ins u c).
  Defined.

  (** The verifier: a transcript [(a, c, r)] is accepted iff [g^r = a·h^c]
      ([accepting_conversation]). *)
  Definition schnorr_protocol_verification_ins :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 1 1 1 -> bool.
  Proof.
    intro transcript.
    refine (@accepting_conversation (@Zp q) (@Schnorr_group p q)
      mul_schnorr_group pow Schnorr.dec_zpstar g h transcript).
    eapply prime_p.
    eapply prime_q.
    instantiate (1 := 2%Z).
    compute; reflexivity.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
