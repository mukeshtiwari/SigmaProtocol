(** * Distributed (n-out-of-n) ElGamal over a toy Schnorr group *)

(** A concrete instance of the distributed ElGamal scheme of
[Crypto/DistElgamal.v] with three trustees, as used by Helios-style
elections. Trustee [i] holds a secret share [xᵢ] and publishes
[hᵢ = g^xᵢ]; the joint public key is [h = h₁·h₂·h₃], whose secret
[x₁ + x₂ + x₃] no single trustee knows. Encryption is exponential ElGamal under [h]:
[(c₁, c₂) = (g^r, g^m·h^r)]. To decrypt, every trustee publishes a
decryption factor [c₁^xᵢ], and anyone combines them as
[c₂·(c₁^x₁·c₁^x₂·c₁^x₃)⁻¹ = g^m]. All three trustees are needed; this is
not a threshold scheme. The file is extracted to OCaml by
[src/Extraction/DistElgamallib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The trustees' shares are [x₁ = 3], [x₂ = 5] and [x₃ = 7]. Each operation
is given for a single value and pointwise for a ballot of [n] values. The
proofs of correct decryption that normally accompany each factor are not
part of this file (see [ChaumPedersenIns.v]). *)
From Stdlib Require Import Utf8 ZArith Vector.
From Sigma Require Import DistElgamal.
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

  (** Secret share of trustee 1, [x₁ = 3]. *)
  Definition x₁ : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  (** Public share of trustee 1, [h₁ = g^x₁]. *)
  Definition h₁ : @Schnorr_group p q :=
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x₁.

  (** Secret share of trustee 2, [x₂ = 5]. *)
  Definition x₂ : @Zp q :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  (** Public share of trustee 2, [h₂ = g^x₂]. *)
  Definition h₂ : @Schnorr_group p q :=
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x₂.

  (** Secret share of trustee 3, [x₃ = 7]. *)
  Definition x₃ : @Zp q :=
    {| Zpfield.v := 7; Zpfield.Hv := eq_refl : (7 mod q)%Z = 7%Z |}.

  (** Public share of trustee 3, [h₃ = g^x₃]. *)
  Definition h₃ : @Schnorr_group p q :=
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x₃.

  (** The joint public key [h = h₁·(h₂·h₃) = g^(x₁+x₂+x₃)]. It is not used
      below: the encryption functions recompute the product from [[h₁; h₂; h₃]]. *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine(@mul_schnorr_group p q prime_p prime_q h₁
      (@mul_schnorr_group p q prime_p prime_q h₂ h₃)).
  Defined.

  (** Encrypts the value [m] (as [g^m]) with randomness [r] under the joint
      key computed from [[h₁; h₂; h₃]]. *)
  Definition encrypt_dist_value_ins (m r : @Zp q) :
    @Schnorr_group p q * @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.encrypt_value_dist (@Zp q)
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q)
    _ g [h₁; h₂; h₃] m r).
  Defined.

  (** The first trustee's decryption factor [c₁^x₁] for ciphertext [c]. *)
  Definition decryption_factor_value_first_ins (c :  @Schnorr_group p q * @Schnorr_group p q) :
    @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value_partial (@Zp q)
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) c x₁).
  Defined.

  (** The second trustee's decryption factor [c₁^x₂] for ciphertext [c]. *)
  Definition decryption_factor_value_second_ins (c :  @Schnorr_group p q * @Schnorr_group p q) :
    @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value_partial (@Zp q)
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) c x₂).
  Defined.

  (** The third trustee's decryption factor [c₁^x₃] for ciphertext [c]. *)
  Definition decryption_factor_value_third_ins (c :  @Schnorr_group p q * @Schnorr_group p q) :
    @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value_partial (@Zp q)
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) c x₃).
  Defined.

  (** Combines the three factors: [c₂·(df₁·df₂·df₃)⁻¹], equal to [g^m] when the
      factors are honest. *)
  Definition decrypt_dist_value_ins (c :  @Schnorr_group p q * @Schnorr_group p q)
    (df₁ df₂ df₃ : @Schnorr_group p q) : @Schnorr_group p q.
  Proof.
    refine(@DistElgamal.decrypt_value (@Schnorr_group p q)
    (@Schnorr.one p q prime_p prime_q)
    (@inv_schnorr_group p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) _ c [df₁; df₂; df₃]).
  Defined.

  (** Encrypts a vector of [n] values under the joint key, pointwise with the
      randomness vector [rs]. *)
  Definition encrypt_dist_ballot_ins {n : nat} (ms : Vector.t (@Zp q) n)
    (rs : Vector.t (@Zp q) n) :  Vector.t (@Schnorr_group p q * @Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.encrypt_ballot_dist (@Zp q)
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ n g [h₁; h₂; h₃] ms rs).
  Defined.

  (** The first trustee's decryption factors for a ballot, pointwise. *)
  Definition decrypt_ballot_partial_first_ins {n : nat}
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_partial (@Zp q)
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) n cs x₁).
  Defined.

  (** The second trustee's decryption factors for a ballot, pointwise. *)
  Definition decrypt_ballot_partial_second_ins {n : nat}
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_partial (@Zp q)
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) n cs x₂).
  Defined.

  (** The third trustee's decryption factors for a ballot, pointwise. *)
  Definition decrypt_ballot_partial_third_ins {n : nat}
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_partial (@Zp q)
    (@Schnorr_group p q)
    (@pow 2 p q safe_prime prime_p prime_q) n cs x₃).
  Defined.

  (** Combines the three trustees' factor vectors with the ballot, pointwise,
      giving [g^mᵢ] for each entry. *)
  Definition decrypt_ballot_value_ins {n : nat}
    (cs : Vector.t (@Schnorr_group p q * @Schnorr_group p q) n)
    (dfs₁ dfs₂ dfs₃ : Vector.t (@Schnorr_group p q) n) :
    Vector.t (@Schnorr_group p q) n.
  Proof.
    refine(@DistElgamal.decrypt_ballot_value (@Schnorr_group p q)
    (@inv_schnorr_group p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q) _ n cs [dfs₁; dfs₂; dfs₃]).
  Defined.

End Ins.
