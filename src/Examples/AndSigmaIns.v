(** * AND-composition of Schnorr protocols over a toy Schnorr group *)

(** A concrete instance of the AND-composition of Schnorr protocols
([Crypto/AndSigma.v]): a proof of knowledge of three discrete logarithms
[x₁], [x₂], [x₃] with [hᵢ = g^xᵢ], all answered with one shared challenge.
The prover sends [g^uᵢ] for each statement, receives [c] and answers
[rᵢ = uᵢ + c·xᵢ]; the verifier checks [g^rᵢ = (g^uᵢ)·hᵢ^c] for every [i].
The file is extracted to OCaml by [src/Extraction/AndSigmalib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The secrets are [x₁ = 3], [x₂ = 5] and [x₃ = 8]. *)
From Stdlib Require Import Utf8 ZArith Vector.
From Sigma Require Import Sigma
  AndSigma.
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

  (** First secret, [x₁ = 3]. *)
  Definition x₁ : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  (** Second secret, [x₂ = 5]. *)
  Definition x₂ : @Zp q :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  (** Third secret, [x₃ = 8]. *)
  Definition x₃ : @Zp q :=
    {| Zpfield.v := 8; Zpfield.Hv := eq_refl : (8 mod q)%Z = 8%Z |}.

  (** [h₁ = g^x₁], built directly from [Zpow_mod]. Its membership
      obligation is discharged by a cast of the proof term for [g^q mod p = 1];
      the kernel accepts it because both sides compute to the same value. *)
  Definition h₁ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₁) p;
    Ha := conj eq_refl eq_refl :
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₁) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g) q p)).
  Defined.

  (** [h₂ = g^x₂], built directly from [Zpow_mod]. Its membership
      obligation is discharged by a cast of the proof term for [g^q mod p = 1];
      the kernel accepts it because both sides compute to the same value. *)
  Definition h₂ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₂) p;
    Ha := conj eq_refl eq_refl :
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₂) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g) q p)).
  Defined.

  (** [h₃ = g^x₃], built directly from [Zpow_mod]. Its membership
      obligation is discharged by a cast of the proof term for [g^q mod p = 1];
      the kernel accepts it because both sides compute to the same value. *)
  Definition h₃ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₃) p;
    Ha := conj eq_refl eq_refl :
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g) (Zpfield.v x₃) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g) q p)).
  Defined.

  (** The commitments [[g^u₁; g^u₂; g^u₃]] for the randomness vector [us]. *)
  Definition construct_and_conversations_schnorr_commitment_ins
    (us : Vector.t (@Zp q) 3) : Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@construct_and_conversations_schnorr_commitment
      (@Zp q) (@Schnorr_group p q) pow _ g us).
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The honest transcript: three commitments, the single challenge [c] and
      the three responses [uᵢ + c·xᵢ]. *)
  Definition construct_and_conversations_schnorr_ins (us : Vector.t (@Zp q) 3) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 3.
  Proof.
    refine(@construct_and_conversations_schnorr (@Zp q)
    zp_add zp_mul (@Schnorr_group p q) pow 3 [x₁; x₂; x₃] g us c).
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The non-interactive proof: [c] is [fn] applied to [[p; q; g; h₁; h₂; h₃]]
      followed by the commitments; [fn] is a hash function supplied by the
      OCaml caller (strong Fiat–Shamir). *)
  Definition nizk_construct_and_conversations_schnorr_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (us : Vector.t (@Zp q) 3)  :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 3.
  Proof.
    set (comm := construct_and_conversations_schnorr_commitment_ins us).
    set (c := fn _ ([inl p; inl q; inr g; inr h₁; inr h₂; inr h₃] ++
      Vector.map inr comm)).
    refine(construct_and_conversations_schnorr_ins us c).
  Defined.

  (** The verifier: accepts iff [g^rᵢ = aᵢ·hᵢ^c] for [i = 1, 2, 3]. *)
  Definition generalised_and_accepting_conversations_ins :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 3 ->  bool.
  Proof.
    intro proof.
    refine (@generalised_and_accepting_conversations (@Zp q) (@Schnorr_group p q)
    mul_schnorr_group pow Schnorr.dec_zpstar _ g [h₁; h₂; h₃] proof).
    eapply prime_p.
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
