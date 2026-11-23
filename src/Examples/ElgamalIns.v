(** * ElGamal encryption over a toy Schnorr group *)

(** A concrete instance of the exponential ElGamal scheme of
[Crypto/Elgamal.v], extracted to OCaml by [src/Extraction/Elgamallib].
A message [m ∈ Z_q] is encrypted with randomness [r] under the public key
[h = g^x] as [(g^r, g^m·h^r)]; decryption recovers [g^m], not [m]. The
scheme is additively homomorphic (componentwise product of ciphertexts adds
the plaintexts) and supports re-encryption, multiplying by a fresh
encryption of [0]. These are exactly the operations used by homomorphic
tallies and re-encryption mix-nets.

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

Besides single ciphertexts the file lifts every operation pointwise to
ballots, that is vectors of [n] ciphertexts. Nothing is proved here; the
correctness lemmas (decryption of an encryption, homomorphism) are in
[Crypto/Elgamal.v]. *)
From Stdlib Require Import Utf8 ZArith.
From Sigma Require Import Elgamal.
From Utility Require Import Zpstar.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup.

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

  (** The decryption key [x = 3]. *)
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

  (** The public key [h = g^x]. *)
  Definition h : @Schnorr_group p q :=
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x.

  (** [encrypt m r = (g^r, g^m·h^r)]. *)
  Definition encrypt (m r : @Zp q) :
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@Elgamal.enc (@Zp q) (@Schnorr_group p q)
     (@mul_schnorr_group p q prime_p prime_q) pow g h m r).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** [decrypt (c₁, c₂) = c₂·(c₁^x)⁻¹], which is [g^m] on an honest
      ciphertext. *)
  Definition decrypt (c :  @Schnorr_group p q * @Schnorr_group p q) : @Schnorr_group p q.
  Proof.
    refine(@Elgamal.dec (@Zp q) (@Schnorr_group p q)
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    pow x c).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** [re_encryption (c₁, c₂) r = (c₁·g^r, c₂·h^r)]: a fresh-looking
      ciphertext of the same plaintext. *)
  Definition re_encryption (c :  @Schnorr_group p q * @Schnorr_group p q) (r : @Zp q) :
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@Elgamal.re_enc (@Zp q) (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q) pow
    g h c r).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** Componentwise product of two ciphertexts; it encrypts the sum of the
      plaintexts (in the exponent). *)
  Definition multiply_cipher (c₁ c₂ : @Schnorr_group p q * @Schnorr_group p q) :
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@Elgamal.mul_cipher (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q)
      c₁ c₂).
  Defined.

  (** Encrypts a vector of [n] messages [ms] with the randomness vector [rs],
      pointwise. *)
  Definition encrypt_ballot {n : nat} (ms rs : Vector.t (@Zp q) n) :
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.encrypted_ballot (@Zp q) (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q) pow g h n ms rs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** Decrypts a vector of [n] ciphertexts pointwise, giving the [g^mᵢ]. *)
  Definition decrypt_ballot {n : nat}  (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.decrypted_ballot (@Zp q) (@Schnorr_group p q)
     (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
     (@mul_schnorr_group p q prime_p prime_q) pow x n cs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** Re-encrypts a vector of [n] ciphertexts pointwise with the randomness
      vector [rs]. *)
  Definition reencrypt_ballots {n : nat} (cs :  Vector.t (@Schnorr_group p q * @Schnorr_group p q) n)
    (rs : Vector.t (@Zp q) n) :  Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.re_encryption_ballot (@Zp q) (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q) pow g h n cs rs).
    exact safe_prime.
    exact prime_p.
    exact prime_q.
  Defined.

  (** Pointwise product of two encrypted ballots: the homomorphic sum of two
      ballots, as used to accumulate a tally. *)
  Definition multiply_encrypted_ballots {n : nat} (cs₁ cs₂ : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@Elgamal.mul_encrypted_ballots (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q) n cs₁ cs₂).
  Defined.

End Ins.
