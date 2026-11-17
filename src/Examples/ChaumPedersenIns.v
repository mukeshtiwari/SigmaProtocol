(** * Chaum–Pedersen protocol over a toy Schnorr group *)

(** A concrete instance of the Chaum–Pedersen protocol
([Crypto/ChaumPedersen.v]; Chaum and Pedersen, CRYPTO 1992), a Sigma
protocol for equality of discrete logarithms: knowledge of [x] with
[c₁ = g^x] and [c₂ = h^x] for two generators [g] and [h]. The prover sends
[(g^u, h^u)], receives [c] and answers [u + c·x]; the verifier checks
[g^r = g^u·c₁^c] and [h^r = h^u·c₂^c]. It is the proof of correct
decryption used by threshold ElGamal tallies. The file is extracted to OCaml
by [src/Extraction/ChaumPedersenlib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The generators are [g = 4] and [h = 7] and the witness is [x = 30]. *)
From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma
  ChaumPedersen.
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

  (** The second generator [h = 7], also of order [q] (checked by
      [vm_compute]). *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 7;
    Ha := conj eq_refl eq_refl : (0 < 7 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 7 q p)).
  Defined.

  (** The common discrete logarithm [x = 30]. *)
  Definition x : @Zp q :=
    {| Zpfield.v := 30; Zpfield.Hv := eq_refl : (30 mod q)%Z = 30%Z |}.

  (** The first public value [c₁ = g^x]. It is closed with [Qed], so it is
      opaque inside Rocq; extraction still produces its value. *)
  Definition c₁ : @Schnorr_group p q.
  Proof.
    refine(pow g x).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Qed.

  (** The second public value [c₂ = h^x], also opaque. *)
  Definition c₂ : @Schnorr_group p q.
  Proof.
    refine(pow h x).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Qed.

  (** The commitment pair [[g^u; h^u]] for randomness [u]. *)
  Definition construct_cp_conversations_schnorr_commitment_ins
    (u : @Zp q) : Vector.t (@Schnorr_group p q) 2.
  Proof.
    refine(@construct_cp_conversations_schnorr_commitment
      (@Zp q) (@Schnorr_group p q) pow g h u).
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The honest transcript [([g^u; h^u], c, u + c·x)] for randomness [u]
      and challenge [c]. *)
  Definition construct_cp_conversations_schnorr_ins
    (u c : @Zp q ) : @sigma_proto (@Zp q) (@Schnorr_group p q) 2 1 1.
  Proof.
    refine(@construct_cp_conversations_schnorr (@Zp q)
    zp_add zp_mul (@Schnorr_group p q) pow x g h u c).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Defined.

  (** The non-interactive proof: the challenge is [fn] applied to
      [[p; q; g; h; c₁; c₂]] followed by the two commitments (strong
      Fiat–Shamir); [fn] is a hash function supplied by the OCaml caller. *)
  Definition nizk_construct_cp_conversations_schnorr_ins
    (fn : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (u : (@Zp q)) : @sigma_proto (@Zp q) (@Schnorr_group p q) 2 1 1.
  Proof.
    set (comm := construct_cp_conversations_schnorr_commitment_ins u).
    set (c := fn _ ([inl p; inl q; inr g; inr h; inr c₁; inr c₂] ++
    Vector.map inr comm)).
    exact(construct_cp_conversations_schnorr_ins u c).
  Defined.

  (** The verifier: accepts iff [g^r = a₁·c₁^c] and [h^r = a₂·c₂^c]. *)
  Definition generalised_cp_accepting_conversations_ins :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 2 1 1 -> bool.
  Proof.
    intros s.
    refine(@generalised_cp_accepting_conversations (@Zp q)
    (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q) pow
    Schnorr.dec_zpstar g h c₁ c₂ s).
    all:(try eapply safe_prime).
    all:(try eapply prime_p).
    all:(try eapply prime_q).
  Defined.

End Ins.
