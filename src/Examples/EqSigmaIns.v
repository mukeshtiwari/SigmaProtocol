(** * Equality of discrete logarithms across three bases, toy instance *)

(** A concrete instance of the generalised equality protocol of
[Crypto/EqSigma.v]: a proof of knowledge of a single [x] with
[h₁ = g₁^x], [h₂ = g₂^x] and [h₃ = g₃^x]. It generalises Chaum–Pedersen
to [n] bases (here [n = 3]). The prover sends [gᵢ^u] for every base,
receives one challenge [c] and answers [r = u + c·x]; the verifier checks
[gᵢ^r = (gᵢ^u)·hᵢ^c] for each [i]. The file is extracted to OCaml by
[src/Extraction/EqSigmalib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The bases are [12], [16] and [18], the witness is [x = 3], and [hfake] is
an unrelated element that can be substituted for one of the [hᵢ] to watch
the verifier reject. *)
From Stdlib Require Import Utf8 ZArith
Vector Fin.
From Crypto Require Import Sigma EqSigma.
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

  (** The common witness [x = 3]. *)
  Definition x : @Zp q :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.

  (** The base [g₁ = 12], an element of the order-[q] subgroup
      (membership checked by [vm_compute]). *)
  Definition g₁ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 12;
    Ha := conj eq_refl eq_refl : (0 < 12 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 12 q p)).
  Defined.

  (** [h₁ = g₁^x]. *)
  Definition h₁ : @Schnorr_group p q :=
    Eval vm_compute in @pow _ _ _ safe_prime prime_p prime_q g₁ x.

  (** The base [g₂ = 16], an element of the order-[q] subgroup
      (membership checked by [vm_compute]). *)
  Definition g₂ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 16;
    Ha := conj eq_refl eq_refl : (0 < 16 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 16 q p)).
  Defined.

  (** [h₂ = g₂^x]. *)
  Definition h₂ : @Schnorr_group p q :=
    Eval vm_compute in @pow _ _ _ safe_prime prime_p prime_q g₂ x.

(** The base [g₃ = 18], an element of the order-[q] subgroup
    (membership checked by [vm_compute]). *)
Definition g₃ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 18;
    Ha := conj eq_refl eq_refl : (0 < 18 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 18 q p)).
  Defined.

  (** [h₃ = g₃^x]. *)
  Definition h₃ : @Schnorr_group p q :=
    Eval vm_compute in @pow _ _ _ safe_prime prime_p prime_q g₃ x.

  (** A group element [25] that is not [gᵢ^x] for the bases above; replacing
      one of the [hᵢ] by it in the verifier makes an honest proof fail. *)
  Definition hfake : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  (** The commitments [[g₁^u; g₂^u; g₃^u]] for randomness [u]. *)
  Definition construct_eq_conversations_schnorr_commitment_ins
    (u : @Zp q) : Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@construct_eq_conversations_schnorr_commitment
      (@Zp q) (@Schnorr_group p q) pow 1 [g₁; g₂; g₃] u).
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The honest transcript: the three commitments, challenge [c] and the
      single response [u + c·x]. *)
  Definition construct_eq_conversations_schnorr_ins (u c : @Zp q) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 1.
  Proof.
    refine(@construct_eq_conversations_schnorr (@Zp q)
      zp_add zp_mul (@Schnorr_group p q) pow 1 x [g₁; g₂; g₃] u c).
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

  (** The non-interactive proof: [c] is [fn] applied to [p], [q], all the
      pairs [(gᵢ, hᵢ)] and the commitments; [fn] is a hash function supplied
      by the OCaml caller. *)
  Definition nizk_construct_eq_conversations_schnorr_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (u : @Zp q) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 1.
  Proof.
    set (comm := construct_eq_conversations_schnorr_commitment_ins u).
    set (c := fn _ ([inl p; inl q; inr g₁; inr h₁; inr g₂; inr h₂; inr g₃;
      inr h₃] ++ Vector.map inr comm)).
    refine(construct_eq_conversations_schnorr_ins u c).
  Defined.

  (** The verifier: accepts iff [gᵢ^r = aᵢ·hᵢ^c] for [i = 1, 2, 3]. *)
  Definition generalised_eq_accepting_conversations_ins
    (proof :  @sigma_proto (@Zp q) (@Schnorr_group p q) 3 1 1) : bool.
  Proof.
    refine(@generalised_eq_accepting_conversations (@Zp q) (@Schnorr_group p q)
      (@mul_schnorr_group p q prime_p prime_q) pow
      Schnorr.dec_zpstar 1 [g₁; g₂; g₃] [h₁; h₂; h₃] proof).
    eapply safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
