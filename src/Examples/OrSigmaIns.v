(** * OR-composition of Schnorr protocols over a toy Schnorr group *)

(** A concrete instance of the OR-composition of Schnorr protocols
([Crypto/OrSigma.v]; Cramer, Damgård and Schoenmakers, CRYPTO 1994): a
proof that the prover knows the discrete logarithm of at least one of
[h₁], [h₂], [h₃] to the base [g], without revealing which. The file is
extracted to OCaml by [src/Extraction/OrSigmalib].

The prover knows [x] with [h₂ = g^x] (index [Fin.FS Fin.F1]). For the
other two statements it simulates transcripts with self-chosen challenges;
for the real one it runs Schnorr's protocol, with the challenge set to the
verifier's challenge [c] minus the two simulated ones. The transcript has
three commitments, four challenges ([c] followed by the three
sub-challenges) and three responses. The verifier accepts iff the
sub-challenges sum to [c] and every sub-transcript is an accepting Schnorr
conversation.

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The public keys are [h₁ = 12], [h₂ = g^3] and [h₃ = 25]; the
randomness vector [uscs] holds three commitment randomnesses followed by
the two simulated challenges. *)
From Stdlib Require Import Utf8 ZArith
Vector Fin.
From Sigma Require Import Sigma OrSigma.
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

  (** First public key [h₁ = 12], a group element whose discrete logarithm
      the prover does not use. *)
  Definition h₁ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 12;
    Ha := conj eq_refl eq_refl : (0 < 12 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 12 q p)).
  Defined.

  (** The prover's secret [x = 3], the logarithm of [h₂]. *)
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

  (** Second public key [h₂ = g^x]: the statement the prover can prove. *)
  Definition h₂ : @Schnorr_group p q :=
    Eval compute in @pow _ _ _ safe_prime prime_p prime_q g x.

  (** Third public key [h₃ = 25 = 5²], another quadratic residue whose
      logarithm the prover does not use. *)
  Definition h₃ : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 25;
    Ha := conj eq_refl eq_refl : (0 < 25 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 25 q p)).
  Defined.

  (** The three commitments: [g^u] for the real statement and the
      simulated [g^uᵢ·hᵢ^(-cᵢ)] for the other two, computed from [uscs]
      (three [u]s followed by two simulated challenges). *)
  Definition construct_or_conversations_schnorr_commitment_ins
     (uscs : Vector.t (@Zp q) 5)  :
     Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@construct_or_conversations_schnorr_commitment (@Zp q)
      zp_opp (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q)
      pow 1 1 g [h₁; h₂; h₃] (uscs)).
      eapply prime_q.
      exact safe_prime.
      eapply prime_p.
      eapply prime_q.
  Defined.

  (** The full OR transcript for the verifier's challenge [c]: the real
      branch gets challenge [c - c₁ - c₃] and response [u + (c - c₁ - c₃)·x]. *)
  Definition generalised_construct_or_conversations_schnorr_ins
    (uscs : Vector.t (@Zp q) 5) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 4 3.
  Proof.
    refine(@generalised_construct_or_conversations_schnorr
      (@Zp q) zero zp_add zp_mul zp_sub zp_opp
      (@Schnorr_group p q) (@mul_schnorr_group p q prime_p prime_q)
      pow _ (Fin.FS Fin.F1) x g [h₁; h₂; h₃] (uscs) c).
      eapply prime_q.
      eapply prime_q.
      exact safe_prime.
      eapply prime_p.
      eapply prime_q.
  Defined.

  (** The non-interactive proof: [c] is [fn] applied to
      [[p; q; h₁; g; h₂; h₃]] followed by the three commitments; [fn] is a
      hash function supplied by the OCaml caller (strong Fiat–Shamir). *)
  Definition nizk_generalised_construct_or_conversations_schnorr_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (uscs : Vector.t (@Zp q) 5) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 3 4 3.
  Proof.
    set (comm := construct_or_conversations_schnorr_commitment_ins uscs).
    set (c := fn _ ([inl p; inl q; inr h₁; inr g; inr h₂;
      inr h₃] ++ Vector.map inr comm)).
    refine(generalised_construct_or_conversations_schnorr_ins uscs c).
  Defined.

  (** The verifier: the sub-challenges sum to the main challenge and each of
      the three sub-transcripts is an accepting Schnorr conversation for
      [(g, hᵢ)]. *)
  Definition generalised_or_accepting_conversations_ins
    (pf :  @sigma_proto (@Zp q) (@Schnorr_group p q) 3 4 3) : bool.
  Proof.
    refine(@generalised_or_accepting_conversations
    (@Zp q) zero zp_add zp_dec (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q) pow
    Schnorr.dec_zpstar 3 g [h₁; h₂; h₃] pf).
    eapply prime_q.
    exact safe_prime.
    eapply prime_p.
    eapply prime_q.
  Defined.

End Ins.
