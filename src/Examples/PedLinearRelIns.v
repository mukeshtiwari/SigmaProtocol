(** * Linear relation between Pedersen-committed values, toy instance *)

(** A concrete instance of [Crypto/PedLinearRel.v]: for Pedersen
commitments [Cᵢ = g^vᵢ·h^rᵢ] ([i = 1..3]), a proof of knowledge of all the
openings [(vᵢ, rᵢ)] such that the committed values satisfy the public linear
relation [Σᵢ αᵢ·vᵢ = z]. The prover commits to [g^uᵢ·h^wᵢ] for every [i]
and to [g^(Σ αᵢ·uᵢ)], receives [c] and answers [uᵢ + c·vᵢ] and
[wᵢ + c·rᵢ]. The verifier checks [g^(vᵢ')·h^(rᵢ') = Aᵢ·Cᵢ^c] for every [i]
and [g^(Σ αᵢ·vᵢ') = A·g^(c·z)]. The file is extracted to OCaml by
[src/Extraction/PedLinearRellib].

The group is the order-[q] subgroup of [Z_p^*] for the toy safe prime
[p = 2q + 1 = 5927] with [q = 2963] (from [Utility/Zpstar.v]: [Zp q] is
the scalar field and [Schnorr_group p q] the group of quadratic residues
mod [p]). The parameters are far too small to be secure; they are chosen so
that primality can be proved by trial division ([Examples/Prime.v]) and
the extracted code runs instantly.

The instance uses [αs = (1, -1, -1)] and [z = 0], that is
[v₁ = v₂ + v₃]. A typical application is a confidential transaction: the
committed old balance equals the committed amount sent plus the committed
new balance, so no value is created, while all three amounts stay hidden.
For the binding property of the commitments the discrete logarithm of [h]
to the base [g] must be unknown; here [g = 4] and [h = 7] are simply fixed
small elements, not generated verifiably. *)
From Stdlib Require Import Utf8 ZArith Vector.
From Crypto Require Import Sigma
  PedLinearRel.
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

  (** The second Pedersen generator [h = 7], an element of the order-[q]
      subgroup. *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 7;
    Ha := conj eq_refl eq_refl : (0 < 7 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 7 q p)).
  Defined.

  (** The coefficients of the linear relation, [αs = (1, -1, -1)]. *)
  Definition αs : Vector.t (@Zp q) 3.
  Proof.
    refine ([Zpfield.one; @zp_opp q prime_q Zpfield.one; @zp_opp q prime_q Zpfield.one]);
    try (exact prime_q).
  Defined.

  (** The right-hand side of the relation, [z = 0]. *)
  Definition z : @Zp q := @zero q prime_q.

  (** The four commitments: [g^uᵢ·h^wᵢ] for [i = 1..3] and [g^(Σ αᵢ·uᵢ)],
      from the six random scalars [usws = us ++ ws]. *)
  Definition construct_pedersen_linear_relation_commitment_ins
    (usws : Vector.t (@Zp q) 6) : Vector.t (@Schnorr_group p q) 4.
  Proof.
    refine(@construct_pedersen_linear_relation_commitment (@Zp q)
    (@zero q prime_q) zp_add zp_mul (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ g h αs usws).
  Defined.

  (** The Pedersen commitments [Cᵢ = g^vᵢ·h^rᵢ] to the values [vs] with
      blinding factors [rs]. *)
  Definition pedersen_commitment_vector_ins
    (vs rs : Vector.t (@Zp q) 3) : Vector.t (@Schnorr_group p q) 3.
  Proof.
    refine(@pedersen_commitment_vector (@Zp q) (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ g h vs rs).
  Defined.

  (** The honest transcript: the four commitments, challenge [c], and the six
      responses [uᵢ + c·vᵢ] followed by [wᵢ + c·rᵢ]. *)
  Definition construct_pedersen_linear_relation_generalised_real_proof_ins
    (vs rs : Vector.t (@Zp q) 3) (usws : Vector.t (@Zp q) 6) (c : (@Zp q)) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 4 1 6.
  Proof.
    refine(@construct_pedersen_linear_relation_generalised_real_proof (@Zp q)
    (@zero q prime_q) zp_add zp_mul (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q) _ g h αs
    usws vs rs c).
  Defined.

   (** The non-interactive proof: [c] is [fn] applied to [[p; q; g; h]], the
       four announcements and the three commitments [Cᵢ]; [fn] is a hash
       function supplied by the OCaml caller (strong Fiat–Shamir). *)
   Definition nizk_construct_pedersen_linear_relation_generalised_real_proof_ins
    (fn  : ∀ {m : nat}, Vector.t (Z + (@Schnorr_group p q)) m -> (@Zp q))
    (vs rs : Vector.t (@Zp q) 3) (usws : Vector.t (@Zp q) 6) :
    @sigma_proto (@Zp q) (@Schnorr_group p q) 4 1 6.
  Proof.
    set (comm₁ := construct_pedersen_linear_relation_commitment_ins usws).
    set (comm₂ := pedersen_commitment_vector_ins vs rs).
    set (c := fn _ ([inl p; inl q; inr g; inr h] ++
    Vector.map inr (comm₁ ++ comm₂))).
    refine(construct_pedersen_linear_relation_generalised_real_proof_ins
    vs rs usws c).
  Defined.

  (** The verifier for commitments [cs]: checks the three opening equations and
      the linear-relation equation, with [αs] and [z] above. *)
  Definition verify_pedersen_linear_relation_generalised_proof_ins
    (cs : Vector.t (@Schnorr_group p q) 3)
    (pf : @sigma_proto (@Zp q) (@Schnorr_group p q) 4 1 6) : bool.
  Proof.
    refine(@verify_pedersen_linear_relation_generalised_proof (@Zp q)
    (@zero q prime_q) zp_add zp_mul (@Schnorr_group p q)
    (@mul_schnorr_group p q prime_p prime_q)
    (@pow 2 p q safe_prime prime_p prime_q)
    Schnorr.dec_zpstar _ g h z αs cs pf).
  Defined.

End Ins.
