(** * Proof that an ElGamal ciphertext encrypts one of a list of messages *)

(** A concrete instance of the disjunctive encryption proof of
[Crypto/EncProof.v]: given a ciphertext [cp = (c₁, c₂)] under public key
[h] and a public list of candidate plaintexts [[m₀; m₁; m₂]] (group
elements), the prover shows that [cp] encrypts one of them without
revealing which. Statement [i] is the Chaum–Pedersen relation

[[
∃ r,  c₁ = g^r  ∧  c₂·mᵢ⁻¹ = h^r,
]]

and the proof is their OR-composition in the style of Cramer, Damgård and
Schoenmakers (CRYPTO 1994): two branches are simulated with self-chosen
challenges, the real one is run with the remaining share of the
verifier's challenge. This is the ballot-validity proof of Helios-like
systems. The file is extracted to OCaml by [src/Extraction/EncProoflib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

Here [g = 12], the public key is [h = 25], and the ciphertext [cp]
encrypts [m₂ = 38] with randomness [r = 1876]; the prover knows that it is
branch 2 ([Fin.FS (Fin.FS Fin.F1)]). The transcript has three commitments
(pairs of group elements), four challenges and three responses. *)
From Stdlib Require Import Utf8 ZArith
Vector Fin.
From Sigma Require Import Sigma EncProof.
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

  (** The generator [g = 12], an element of the order-[q] subgroup
      (membership checked by [vm_compute]). *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 12;
    Ha := conj eq_refl eq_refl : (0 < 12 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 12 q p)).
  Defined.

  (** The encryption public key [h = 25]; its secret key is not used. *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  (** Candidate plaintext [m₀ = 28], a group element. *)
  Definition m₀ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 28;
    Ha := conj eq_refl eq_refl : (0 < 28 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 28 q p)).
  Defined.

  (** Candidate plaintext [m₁ = 134], a group element. *)
  Definition m₁ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 134;
    Ha := conj eq_refl eq_refl : (0 < 134 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 134 q p)).
  Defined.

  (** Candidate plaintext [m₂ = 38], a group element. *)
  Definition m₂ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 38;
    Ha := conj eq_refl eq_refl : (0 < 38 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 38 q p)).
  Defined.

  (** A fourth element ([25]) not encrypted by [cp]; substituting it for one of
      the candidates makes an honest proof fail when the real branch is
      replaced. *)
  Definition mfake : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  (** The encryption randomness [r = 1876]. *)
  Definition r : @Zp q.
  Proof.
    refine {| Zpfield.v := 1876; Zpfield.Hv := _ |}.
    vm_cast_no_check (eq_refl ((1876 mod q)%Z)).
  Defined.

  (** The ciphertext [cp = (g^r, m₂·h^r)]: plain (not exponential) ElGamal
      encryption of [m₂]. *)
  Definition cp : (@Schnorr_group p q * @Schnorr_group p q).
  Proof.
    exact (@pow _ _ _ safe_prime prime_p prime_q g r,
     (@mul_schnorr_group p q prime_p prime_q m₂
     (@pow _ _ _ safe_prime prime_p prime_q h r))).
  Defined.

  (** The three commitments, each a pair: [(g^u, h^u)] for the branch treated
      as real and a simulated [(g^uᵢ·c₁^(-cᵢ), h^uᵢ·(c₂·mᵢ⁻¹)^(-cᵢ))] for the
      others, computed from [uscs] (three [u]s followed by the two simulated
      challenges). The split [m = 2, n = 0] places the real branch at
      position 2 ([m₂]), the same position the prover below uses
      ([Fin.FS (Fin.FS Fin.F1)]). The two must agree: the non-interactive
      prover hashes these commitments, and with any other split the hashed
      commitments would differ from the announcement in its transcript, so a
      verifier could not recompute the Fiat–Shamir challenge. The test
      [src/Executable/EncProofcode/fs_binding_test.ml] checks this. *)
  Definition construct_encryption_proof_elgamal_commitment_ins
    (uscs : Vector.t (@Zp q) 5) :
    Vector.t (@Schnorr_group p q * @Schnorr_group p q) 3.
  Proof.
    refine(@construct_encryption_proof_elgamal_commitment
    (@Zp q) zp_opp (@Schnorr_group p q)
    (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    pow 2 0 (uscs) [m₀; m₁; m₂] g h cp).
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The full proof for the verifier's challenge [c], with real branch 2 and
      witness [r]. *)
  Definition generalised_construct_encryption_proof_elgamal_real_ins
    (uscs : Vector.t (@Zp q) 5) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 3 4 3.
  Proof.
    refine(@generalised_construct_encryption_proof_elgamal_real (@Zp q)
      Zpfield.zero zp_add zp_mul zp_sub zp_opp (@Schnorr_group p q)
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q)
      pow 1 (Fin.FS (Fin.FS Fin.F1)) r (uscs)
      [m₀; m₁; m₂] g h cp c).
    eapply prime_q.
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The non-interactive proof: [c] is [fn] applied to [p], [q], [g], [h],
      the candidates, the ciphertext and the commitments; [fn] is a hash
      function supplied by the OCaml caller (strong Fiat–Shamir). *)
  Definition nizk_generalised_construct_encryption_proof_elgamal_real_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + ((@Schnorr_group p q) +
      (@Schnorr_group p q * @Schnorr_group p q))) m -> (@Zp q))
    (uscs : Vector.t (@Zp q) 5) :
    @sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 3 4 3.
  Proof.
    set (comm := construct_encryption_proof_elgamal_commitment_ins uscs).
    set (c := fn _ ([inl p; inl q; inr (inl g); inr (inl h);
      inr (inl m₀); inr (inl m₁); inr (inl m₂)] ++
      Vector.map (fun x => inr (inr x)) (cp :: comm))).
    refine(generalised_construct_encryption_proof_elgamal_real_ins uscs c).
  Defined.

  (** The verifier: the sub-challenges sum to the main challenge and each
      branch is an accepting Chaum–Pedersen transcript for [(g, h)] and
      [(c₁, c₂·mᵢ⁻¹)]. *)
  Definition generalised_accepting_encryption_proof_elgamal_ins
    (proof : @sigma_proto (@Zp q) (@Schnorr_group p q * @Schnorr_group p q) 3 4 3) : bool.
  Proof.
    refine(@generalised_accepting_encryption_proof_elgamal
      (@Zp q) Zpfield.zero zp_add zp_dec
      (@Schnorr_group p q)
      (@inv_schnorr_group 2 p q safe_prime prime_p prime_q)
      (@mul_schnorr_group p q prime_p prime_q) pow
      Schnorr.dec_zpstar _  [m₀; m₁; m₂] g h cp proof).
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
