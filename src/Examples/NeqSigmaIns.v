(** * Pairwise inequality of discrete logarithms, toy instance *)

(** A concrete instance of the inequality protocol of [Crypto/NeqSigma.v]:
a proof of knowledge of [x₁], [x₂], [x₃] with [hᵢ = gᵢ^xᵢ] such that the
[xᵢ] are pairwise distinct. The file is extracted to OCaml by
[src/Extraction/NeqSigmalib].

The protocol is the AND-composition of the three Schnorr statements
together with, for every pair [i < j], an Okamoto proof (Okamoto, CRYPTO
1992) of a representation

[[
gⱼ = (gᵢ·gⱼ)^a · (hᵢ·hⱼ)^b,   a = xᵢ/(xᵢ - xⱼ),   b = 1/(xⱼ - xᵢ).
]]

Indeed [(gᵢ·gⱼ)^a·(hᵢ·hⱼ)^b = gᵢ^(a + b·xᵢ)·gⱼ^(a + b·xⱼ) = gⱼ], and these
[a], [b] exist only when [xᵢ ≠ xⱼ]. All the sub-proofs share one challenge.
With three statements there are 3 pairs, hence 3 + 3 = 6 commitments, one
challenge and 3 + 3·2 = 9 responses, and the prover needs 9 random scalars.

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The bases are [g₁ = 4], [g₂ = 7], [g₃ = 13] and the secrets [x₁ = 3],
[x₂ = 5], [x₃ = 8]. Replacing [x₂] by [x₁] or [x₃] (so that two secrets
coincide) makes the honest prover's transcript fail verification. *)
From Stdlib Require Import Utf8 ZArith Vector.
From Sigma Require Import Sigma
  NeqSigma.
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

  (** The base [g₁ = 4], an element of the order-[q] subgroup
      (membership checked by [vm_compute]). *)
  Definition g₁ : @Schnorr_group p q.
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

  (** [h₁ = g₁^x₁], built directly from [Zpow_mod]; its membership
      obligation is discharged by casting the proof term for [g₁^q mod p = 1],
      which the kernel accepts because both sides compute to the same value. *)
  Definition h₁ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g₁) (Zpfield.v x₁) p;
    Ha := conj eq_refl eq_refl :
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g₁) (Zpfield.v x₁) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g₁) q p)).
  Defined.

  (** The base [g₂ = 7], an element of the order-[q] subgroup
      (membership checked by [vm_compute]). *)
  Definition g₂ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 7;
    Ha := conj eq_refl eq_refl : (0 < 7 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 7 q p)).
  Defined.

  (** Second secret, [x₂ = 5]. *)
  Definition x₂ : @Zp q :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  (** [h₂ = g₂^x₂], built directly from [Zpow_mod]; its membership
      obligation is discharged by casting the proof term for [g₂^q mod p = 1],
      which the kernel accepts because both sides compute to the same value. *)
  Definition h₂ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g₂) (Zpfield.v x₂) p;
    Ha := conj eq_refl eq_refl :
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g₂) (Zpfield.v x₂) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g₂) q p)).
  Defined.

  (** The base [g₃ = 13], an element of the order-[q] subgroup
      (membership checked by [vm_compute]). *)
  Definition g₃ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 13;
    Ha := conj eq_refl eq_refl : (0 < 13 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 13 q p)).
  Defined.

  (** Third secret, [x₃ = 8]. *)
  Definition x₃ : @Zp q :=
    {| Zpfield.v := 8; Zpfield.Hv := eq_refl : (8 mod q)%Z = 8%Z |}.

  (** [h₃ = g₃^x₃], built directly from [Zpow_mod]; its membership
      obligation is discharged by casting the proof term for [g₃^q mod p = 1],
      which the kernel accepts because both sides compute to the same value. *)
  Definition h₃ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := Zpow_facts.Zpow_mod (Schnorr.v g₃) (Zpfield.v x₃) p;
    Ha := conj eq_refl eq_refl :
      (0 < Zpow_facts.Zpow_mod (Schnorr.v g₃) (Zpfield.v x₃) p < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod (Schnorr.v g₃) q p)).
  Defined.

  (** The six commitments: [gᵢ^uᵢ] for the AND part, then one Okamoto
      commitment [(gᵢ·gⱼ)^v·(hᵢ·hⱼ)^w] per pair, from the 9 random scalars
      [us]. *)
  Definition generalised_construct_neq_commitment_ins
    (us : Vector.t (@Zp q) 9) : Vector.t (@Schnorr_group p q) 6.
  Proof.
    refine(@generalised_construct_neq_commitment (@Zp q)
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _
    [g₁; g₂; g₃] [h₁; h₂; h₃] us).
  Defined.

  (** The honest transcript for challenge [c]: the commitments, [c], and the
      nine responses (three Schnorr responses [uᵢ + c·xᵢ], then two Okamoto
      responses per pair). *)
  Definition generalised_construct_neq_conversations_real_transcript_ins
    (us : Vector.t (@Zp q) 9) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 6 1 9.
  Proof.
    refine (@generalised_construct_neq_conversations_real_transcript
    (@Zp q) zp_add zp_mul zp_sub zp_inv
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _
    [x₁; x₂; x₃] [g₁; g₂; g₃] [h₁; h₂; h₃] us c).
  Defined.

  (** The non-interactive proof: [c] is [fn] applied to [p], [q], all the
      pairs [(gᵢ, hᵢ)] and the commitments; [fn] is a hash function supplied
      by the OCaml caller (strong Fiat–Shamir). *)
  Definition nizk_generalised_construct_neq_conversations_real_transcript_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (us : Vector.t (@Zp q) 9) : @sigma_proto (@Zp q) (@Schnorr_group p q) 6 1 9.
  Proof.
    set (comm := generalised_construct_neq_commitment_ins us).
    set (c := fn _ ([inl p; inl q; inr g₁; inr h₁; inr g₂; inr h₂;
      inr g₃; inr h₃] ++ Vector.map inr comm)).
    exact (generalised_construct_neq_conversations_real_transcript_ins us c).
  Defined.

  (** The verifier: the AND part is accepting for [(gᵢ, hᵢ)] and every pair's
      Okamoto transcript is accepting for the bases [[gᵢ·gⱼ; hᵢ·hⱼ]] and the
      target [gⱼ]. *)
  Definition generalised_neq_accepting_conversations_ins :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 6 1 9 -> bool.
  Proof.
    intro pf.
    refine(@generalised_neq_accepting_conversations (@Zp q)
    (@Schnorr_group p q) (@Schnorr.one p q prime_p prime_q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q)
    Schnorr.dec_zpstar _ [g₁; g₂; g₃] [h₁; h₂; h₃]
    pf).
  Defined.

End Ins.
