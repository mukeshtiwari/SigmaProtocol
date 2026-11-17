(** * NIST P-256 as a vector space over [Z_n] *)

(** This file instantiates the [vector_space] class of
    [Algebra/Hierarchy.v] with the elliptic curve NIST P-256 (FIPS 186-4,
    also known as secp256r1 or prime256v1), building on the verified
    Weierstrass-curve arithmetic of fiat-crypto vendored under [src/Fiat].
    The curve is [y ^ 2 = x ^ 3 - 3 x + b] over [F_p] with
    [p = 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1]; its group of points has
    prime order [n] (cofactor one). Primality of [p] and [n] is proved by
    Pocklington certificates in [Curve/P256Primes.v].

    The structure mirrors [Curve/Ed25519.v]:

    - [Zn]: the scalar field [Z_n] via the standard library's [Zmod n], with
      the [field] instance [zn_field].
    - [Wp]: the curve. Points are fiat-crypto's affine Weierstrass points,
      either [inl (x, y)] on the curve or [inr tt] for the point at
      infinity. fiat-crypto's commutative group, proved up to a
      coordinate-wise equivalence, is transferred to Leibniz equality.
      [G] is the set of points [P] with [n · P = 0]; since the cofactor is
      one this is every point, but membership is carried as a proof so that
      the construction matches the Ed25519 one. [p256_vspace] makes
      [(G, Z_n)] a vector space with fiat-crypto's reference scalar
      multiplication.
    - [fast_smul]: double-and-add in Jacobian coordinates, proved equal to
      the reference implementation, giving the instance [p256_vspace_fast]
      intended for extraction. It is not constant time.
    - The standard base point [B] with coordinates [(Gx, Gy)] from the
      standard, and a computational proof that [n · B = 0].

    The instance is used by [Examples/P256Ins.v] and other example files. *)
From Stdlib Require Import
  ZArith Znumtheory Zmod Lia Utf8 Eqdep_dec Morphisms RelationClasses.
From Fiat Require
  Spec.WeierstrassCurve Curves.Weierstrass.Affine Curves.Weierstrass.AffineProofs
  Curves.Weierstrass.Jacobian.Jacobian Algebra.ScalarMult Algebra.Hierarchy
  Algebra.Ring Arithmetic.PrimeFieldTheorems Arithmetic.ModularArithmeticTheorems
  Util.Decidable.
From Algebra Require Import Hierarchy.
From Curve Require Import P256Primes.

(** ** The module [P256] *)
Module P256.

  (** Short names for the fiat-crypto modules used below: the Weierstrass
      specification, affine group proofs, Jacobian coordinates, scalar
      multiplication and fiat's algebraic hierarchy. *)
  Module W := Fiat.Spec.WeierstrassCurve.W.
  Module WA := Fiat.Curves.Weierstrass.Affine.W.
  Module WP := Fiat.Curves.Weierstrass.AffineProofs.W.
  Module J := Fiat.Curves.Weierstrass.Jacobian.Jacobian.Jacobian.
  Module SM := Fiat.Algebra.ScalarMult.
  Module FH := Fiat.Algebra.Hierarchy.

  Local Open Scope Z_scope.
  (** The field modulus [p] and the group order [n] (hexadecimal, as in the
      standard). *)
  Definition p : Z := 2^256 - 2^224 + 2^192 + 2^96 - 1.
  Definition n : Z := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551.

  (** Primality of [p] and [n], from [Curve/P256Primes.v]. *)
  Lemma prime_p : prime p.
  Proof. exact prime_p256_p. Qed.
  Lemma prime_n : prime n.
  Proof. exact prime_p256_n. Qed.

  (** [n > 0], [n ≠ 0] and [|n| ≥ 2], by computation. *)
  Lemma n_pos : 0 < n.
  Proof. vm_compute; reflexivity. Qed.
  Lemma n_nonzero : n <> 0.
  Proof. intro h; vm_compute in h; discriminate h. Qed.
  Lemma n_ge_2 : 2 <= Z.abs n.
  Proof. vm_compute; intro h; discriminate h. Qed.

  (** *** The scalar field [Z_n] *)

  (** Integers modulo [n] using the standard library's [Zmod]. *)
  Module Zn.

    (** Carrier and operations of [Z_n]; division is [mdiv]. *)
    Definition F : Type := Zmod n.
    Definition zero : F := Zmod.zero.
    Definition one : F := Zmod.one.
    Definition add : F -> F -> F := Zmod.add.
    Definition mul : F -> F -> F := Zmod.mul.
    Definition sub : F -> F -> F := Zmod.sub.
    Definition opp : F -> F := Zmod.opp.
    Definition inv : F -> F := Zmod.inv.
    Definition div : F -> F -> F := Zmod.mdiv.

    (** Decidable equality, by comparing canonical representatives. *)
    Definition Fdec : forall x y : F, {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct (Z.eq_dec (Zmod.unsigned x) (Zmod.unsigned y)) as [h | h].
      + left; apply (Zmod.unsigned_inj n); exact h.
      + right; intro e; apply h; rewrite e; reflexivity.
    Defined.

    (** [unsigned_nonneg], [unsigned_one], [unsigned_zero], [unsigned_add]
        and [unsigned_mul]: the canonical representative [u] (with
        [0 ≤ u < n]) of constants, sums and products. *)
    Lemma unsigned_nonneg : forall x : F, 0 <= Zmod.unsigned x.
    Proof. intro x. pose proof (Zmod.unsigned_pos_bound x n_pos) as h; lia. Qed.
    Lemma unsigned_one : Zmod.unsigned one = 1.
    Proof. unfold one; rewrite Zmod.unsigned_1; vm_compute; reflexivity. Qed.
    Lemma unsigned_zero : Zmod.unsigned zero = 0.
    Proof. unfold zero; apply Zmod.unsigned_0. Qed.
    Lemma unsigned_add : forall x y : F,
      Zmod.unsigned (add x y) = (Zmod.unsigned x + Zmod.unsigned y) mod n.
    Proof. intros; apply Zmod.unsigned_add. Qed.
    Lemma unsigned_mul : forall x y : F,
      Zmod.unsigned (mul x y) = (Zmod.unsigned x * Zmod.unsigned y) mod n.
    Proof. intros; apply Zmod.unsigned_mul. Qed.

    (** The field axioms of [Z_n], one lemma per axiom, each a direct
        consequence of the corresponding [Zmod] lemma; the inverse axiom
        uses primality of [n]. *)
    Lemma add_assoc : @is_associative F eq add.
    Proof. intros x y z; apply Zmod.add_assoc. Qed.
    Lemma add_0_l : @is_left_identity F eq add zero.
    Proof. intro x; apply Zmod.add_0_l. Qed.
    Lemma add_0_r : @is_right_identity F eq add zero.
    Proof. intro x; unfold add, zero; rewrite Zmod.add_comm; apply Zmod.add_0_l. Qed.
    Lemma add_opp_l : @is_left_inverse F eq add zero opp.
    Proof. intro x; unfold add, zero, opp; rewrite Zmod.add_comm; apply Zmod.add_opp_same_r. Qed.
    Lemma add_opp_r : @is_right_inverse F eq add zero opp.
    Proof. intro x; apply Zmod.add_opp_same_r. Qed.
    Lemma add_comm : @is_commutative F eq add.
    Proof. intros x y; apply Zmod.add_comm. Qed.
    Lemma mul_assoc : @is_associative F eq mul.
    Proof. intros x y z; apply Zmod.mul_assoc. Qed.
    Lemma mul_1_l : @is_left_identity F eq mul one.
    Proof. intro x; apply Zmod.mul_1_l. Qed.
    Lemma mul_1_r : @is_right_identity F eq mul one.
    Proof. intro x; unfold mul, one; rewrite Zmod.mul_comm; apply Zmod.mul_1_l. Qed.
    Lemma mul_comm : @is_commutative F eq mul.
    Proof. intros x y; apply Zmod.mul_comm. Qed.
    Lemma mul_add_distr_l : @is_left_distributive F eq add mul.
    Proof.
      intros x y z; unfold add, mul.
      rewrite Zmod.mul_comm, Zmod.mul_add_l, (Zmod.mul_comm y), (Zmod.mul_comm z).
      reflexivity.
    Qed.
    Lemma mul_add_distr_r : @is_right_distributive F eq add mul.
    Proof. intros x y z; apply Zmod.mul_add_l. Qed.
    Lemma sub_def : forall x y : F, sub x y = add x (opp y).
    Proof. intros; symmetry; apply Zmod.add_opp_r. Qed.
    Lemma inv_mul_l : @is_left_multiplicative_inverse F eq zero one mul inv.
    Proof. intros x hx; apply (@Fiat.Arithmetic.PrimeFieldTheorems.Zmod.inv_nonzero n prime_n x hx). Qed.
    Lemma zero_neq_one : @is_zero_neq_one F eq zero one.
    Proof. intro h; symmetry in h; revert h; apply (Zmod.one_neq_zero n_ge_2). Qed.
    Lemma div_def : forall x y : F, div x y = mul x (inv y).
    Proof. intros; symmetry; apply Zmod.mul_inv_r. Qed.

    (** [Z_n] is a [field] in the sense of [Algebra/Hierarchy.v]. *)
    Global Instance zn_field :
      @field F (@eq F) zero one opp add sub mul inv div.
    Proof.
      refine {|
        field_commutative_ring := {|
          commutative_ring_ring := {|
            ring_commutative_group_add := {|
              commutative_group_group := {|
                group_monoid := {|
                  monoid_is_associative := add_assoc;
                  monoid_is_left_idenity := add_0_l;
                  monoid_is_right_identity := add_0_r;
                  monoid_op_Proper := _;
                  monoid_Equivalence := eq_equivalence |};
                group_is_left_inverse := add_opp_l;
                group_is_right_inverse := add_opp_r;
                group_inv_Proper := _ |};
              commutative_group_is_commutative := add_comm |};
            ring_monoid_mul := {|
              monoid_is_associative := mul_assoc;
              monoid_is_left_idenity := mul_1_l;
              monoid_is_right_identity := mul_1_r;
              monoid_op_Proper := _;
              monoid_Equivalence := eq_equivalence |};
            ring_is_left_distributive := mul_add_distr_l;
            ring_is_right_distributive := mul_add_distr_r;
            ring_sub_definition := sub_def;
            ring_mul_Proper := _;
            ring_sub_Proper := _ |};
          commutative_ring_is_commutative := mul_comm |};
        field_is_left_multiplicative_inverse := inv_mul_l;
        field_is_zero_neq_one := zero_neq_one;
        field_div_definition := div_def;
        field_inv_Proper := _;
        field_div_Proper := _ |}.
      all: repeat intro; subst; reflexivity.
    Qed.

  End Zn.

  (** *** Curve points *)
  Module Wp.

    (** The base field [F_p] and its decidable equality. *)
    Definition Fp : Type := Zmod p.

    Definition Fp_dec : forall x y : Fp, {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct (Z.eq_dec (Zmod.unsigned x) (Zmod.unsigned y)) as [h | h].
      + left; apply (Zmod.unsigned_inj p); exact h.
      + right; intro e; apply h; rewrite e; reflexivity.
    Defined.

    (** [F_p] is a field (fiat-crypto's [Zmod.field_modulo] with
        primality of [p]) of characteristic at least 3, respectively 12;
        these are side conditions of fiat-crypto's Weierstrass group
        proof. The characteristic bounds are checked by [vm_decide]. *)
    Lemma field : @FH.field Fp eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul Zmod.inv Zmod.mdiv.
    Proof. apply Fiat.Arithmetic.PrimeFieldTheorems.Zmod.field_modulo, prime_p. Qed.
    Lemma char_ge_3 : @Fiat.Algebra.Ring.char_ge Fp eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul 3.
    Proof.
      eapply FH.char_ge_weaken;
      try apply Fiat.Arithmetic.ModularArithmeticTheorems.Zmod.char_gt; Fiat.Util.Decidable.vm_decide.
    Qed.
    Lemma char_ge_12 : @Fiat.Algebra.Ring.char_ge Fp eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub Zmod.mul 12.
    Proof.
      eapply FH.char_ge_weaken;
      try apply Fiat.Arithmetic.ModularArithmeticTheorems.Zmod.char_gt; Fiat.Util.Decidable.vm_decide.
    Qed.

    (** The curve coefficients [a = -3] and [b] (from the standard). *)
    Definition a : Fp := Zmod.opp (Zmod.of_Z _ 3).
    Definition b : Fp := Zmod.of_Z _ 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B.

    (** Points (affine or infinity), addition, identity, negation and the
        coordinate-wise equivalence [peq], from fiat-crypto. *)
    Definition point : Type := @W.point Fp eq Zmod.add Zmod.mul a b.
    Definition padd : point -> point -> point :=
      W.add (field := field) (char_ge_3 := char_ge_3) (a := a) (b := b).
    Definition pzero : point := W.zero (a := a) (b := b).
    Definition popp : point -> point := WA.opp (field := field) (a := a) (b := b).
    Definition peq : point -> point -> Prop := @W.eq Fp eq Zmod.add Zmod.mul a b.

    (** fiat-crypto's proof that the points form a commutative group. The
        remaining side condition (non-vanishing discriminant) is discharged
        by [vm_decide]. *)
    Definition fiat_group : @FH.commutative_group point peq padd pzero popp.
    Proof.
      unshelve refine (@WP.commutative_group Fp eq Zmod.zero Zmod.one Zmod.opp Zmod.add Zmod.sub
        Zmod.mul Zmod.inv Zmod.mdiv a b field _ char_ge_3 char_ge_12 _).
      all: try exact _.
      cbv [id]; Fiat.Util.Decidable.vm_decide.
    Defined.
    Definition fiat_grp : @FH.group point peq padd pzero popp :=
      FH.commutative_group_group fiat_group.

    (** [peq] coincides with Leibniz equality on points: the on-curve proofs
        are irrelevant by UIP on [F_p], and the point at infinity is
        unique. *)
    Lemma peq_leibniz : forall P Q : point, peq P Q -> P = Q.
    Proof.
      intros [[[x1 y1] | []] h1] [[[x2 y2] | []] h2] h; cbv [peq W.eq W.coordinates] in h.
      + destruct h as [hx hy]; subst.
        f_equal; apply Eqdep_dec.UIP_dec; exact Fp_dec.
      + contradiction.
      + contradiction.
      + destruct h1, h2; reflexivity.
    Qed.

    Lemma leibniz_peq : forall P Q : point, P = Q -> peq P Q.
    Proof.
      intros P Q h; subst; destruct Q as [[[x y] | []] h]; cbv [peq W.eq W.coordinates].
      + split; reflexivity.
      + exact I.
    Qed.

    (** Decidable equality on points. *)
    Definition point_dec : forall P Q : point, {P = Q} + {P <> Q}.
    Proof.
      intros [[[x1 y1] | []] h1] [[[x2 y2] | []] h2].
      + destruct (Fp_dec x1 x2) as [hx | hx]; [destruct (Fp_dec y1 y2) as [hy | hy] |].
        - subst; left; f_equal; apply Eqdep_dec.UIP_dec; exact Fp_dec.
        - right; intro h; apply hy.
          exact (f_equal (fun z => match proj1_sig z with inl c => snd c | inr _ => y1 end) h).
        - right; intro h; apply hx.
          exact (f_equal (fun z => match proj1_sig z with inl c => fst c | inr _ => x1 end) h).
      + right; intro h; discriminate (f_equal (fun z => match proj1_sig z with inl _ => true | inr _ => false end) h).
      + right; intro h; discriminate (f_equal (fun z => match proj1_sig z with inl _ => true | inr _ => false end) h).
      + left; destruct h1, h2; reflexivity.
    Defined.

    Local Notation fmon := (@FH.group_monoid point peq padd pzero popp fiat_grp).
    (** The group laws of fiat-crypto transferred to Leibniz equality:
        associativity, identities, inverses and commutativity of [padd],
        and [popp pzero = pzero]. *)
    Lemma padd_assoc : forall x y z : point, padd x (padd y z) = padd (padd x y) z.
    Proof.
      intros; apply peq_leibniz.
      apply (@FH.associative point peq padd (@FH.monoid_is_associative point peq padd pzero fmon)).
    Qed.
    Lemma padd_zero_l : forall x : point, padd pzero x = x.
    Proof.
      intros; apply peq_leibniz.
      apply (@FH.left_identity point peq padd pzero (@FH.monoid_is_left_identity point peq padd pzero fmon)).
    Qed.
    Lemma padd_zero_r : forall x : point, padd x pzero = x.
    Proof.
      intros; apply peq_leibniz.
      apply (@FH.right_identity point peq padd pzero (@FH.monoid_is_right_identity point peq padd pzero fmon)).
    Qed.
    Lemma padd_opp_l : forall x : point, padd (popp x) x = pzero.
    Proof.
      intros; apply peq_leibniz.
      apply (@FH.left_inverse point peq padd pzero popp (@FH.group_is_left_inverse point peq padd pzero popp fiat_grp)).
    Qed.
    Lemma padd_opp_r : forall x : point, padd x (popp x) = pzero.
    Proof.
      intros; apply peq_leibniz.
      apply (@FH.right_inverse point peq padd pzero popp (@FH.group_is_right_inverse point peq padd pzero popp fiat_grp)).
    Qed.
    Lemma padd_comm : forall x y : point, padd x y = padd y x.
    Proof.
      intros; apply peq_leibniz.
      apply (@FH.commutative point peq padd (@FH.commutative_group_is_commutative point peq padd pzero popp fiat_group)).
    Qed.
    Lemma popp_zero : popp pzero = pzero.
    Proof. rewrite <-(padd_zero_r (popp pzero)); apply padd_opp_l. Qed.

    (** Scalar multiplication [smul k P] (for [k : Z]) is fiat-crypto's
        reference implementation, which satisfies its [is_scalarmult]
        specification. *)
    Local Notation smul := (@SM.scalarmult_ref point padd pzero popp).
    Definition smul_is : @SM.is_scalarmult point peq padd pzero popp smul :=
      @SM.scalarmult_ref_is_scalarmult point peq padd pzero popp fiat_grp.

    (** Properties of [smul] transferred to Leibniz equality: [0 · P = 0],
        [1 · P = P], [(k + 1) · P = P + k · P], [(k + m) · P = k · P + m · P],
        [k · (m · P) = (m k) · P], [k · 0 = 0], [k · (-P) = -(k · P)], and,
        for [P] with [n · P = 0], [(k mod n) · P = k · P] and
        [(n k) · P = 0]. *)
    Lemma smul_0_l : forall P : point, smul 0 P = pzero.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_0_l point peq padd pzero popp smul smul_is). Qed.
    Lemma smul_1_l : forall P : point, smul 1 P = P.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_1_l point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_succ_l : forall (k : Z) (P : point), smul (Z.succ k) P = padd P (smul k P).
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_succ_l point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_add_l : forall (k m : Z) (P : point), smul (k + m) P = padd (smul k P) (smul m P).
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_add_l point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_assoc : forall (k m : Z) (P : point), smul k (smul m P) = smul (m * k) P.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_assoc point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_zero_r : forall k : Z, smul k pzero = pzero.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_zero_r point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_opp_r : forall (k : Z) (P : point), smul k (popp P) = popp (smul k P).
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_opp_r point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_mod_order : forall (P : point), smul n P = pzero ->
      forall k : Z, smul (k mod n) P = smul k P.
    Proof.
      intros P hP k; apply peq_leibniz.
      apply (@SM.scalarmult_mod_order point peq padd pzero popp fiat_grp smul smul_is n P n_nonzero).
      apply leibniz_peq; exact hP.
    Qed.
    Lemma smul_times_order : forall (P : point), smul n P = pzero ->
      forall k : Z, smul (n * k) P = pzero.
    Proof.
      intros P hP k; apply peq_leibniz.
      apply (@SM.scalarmult_times_order point peq padd pzero popp fiat_grp smul smul_is n P).
      apply leibniz_peq; exact hP.
    Qed.
    (** [k · (P + Q) = k · P + k · Q] for [k ≥ 0], by induction on [k]. *)
    Lemma smul_add_r : forall (k : Z) (P Q : point), 0 <= k ->
      smul k (padd P Q) = padd (smul k P) (smul k Q).
    Proof.
      intros k P Q hk.
      pattern k; apply natlike_ind; [| | exact hk].
      + rewrite !smul_0_l, padd_zero_l; reflexivity.
      + intros m hm ih. rewrite !smul_succ_l, ih.
        rewrite <-!padd_assoc. f_equal.
        rewrite !padd_assoc, (padd_comm Q). reflexivity.
    Qed.

    (** *** The group [G] and the vector-space instance *)

    (** Membership in the order-[n] subgroup: [n · P = 0]. *)
    Definition in_subgroup (P : point) : Prop := smul n P = pzero.

    (** Proofs of subgroup membership are unique. *)
    Lemma in_subgroup_irrel : forall (P : point) (h1 h2 : in_subgroup P), h1 = h2.
    Proof. intros; apply Eqdep_dec.UIP_dec; exact point_dec. Qed.

    (** The group [G] of points killed by [n], as a sigma type. *)
    Definition G : Type := { P : point | in_subgroup P }.

    (** Elements of [G] are equal when their underlying points are. *)
    Lemma G_eq : forall x y : G, proj1_sig x = proj1_sig y -> x = y.
    Proof.
      intros [x hx] [y hy] h; cbn in h; subst.
      f_equal; apply in_subgroup_irrel.
    Qed.

    (** Decidable equality on [G]. *)
    Definition Gdec : forall x y : G, {x = y} + {x <> y}.
    Proof.
      intros [x hx] [y hy]; destruct (point_dec x y) as [h | h].
      + subst; left; f_equal; apply in_subgroup_irrel.
      + right; intro e; apply h; exact (f_equal (@proj1_sig _ _) e).
    Defined.

    (** The subgroup is closed under the identity, addition, negation and
        scalar multiplication. *)
    Lemma closed_zero : in_subgroup pzero.
    Proof. unfold in_subgroup; apply smul_zero_r. Qed.
    Lemma closed_add : forall P Q, in_subgroup P -> in_subgroup Q -> in_subgroup (padd P Q).
    Proof.
      unfold in_subgroup; intros P Q hP hQ.
      rewrite smul_add_r, hP, hQ, padd_zero_l; [reflexivity | pose proof n_pos; lia].
    Qed.
    Lemma closed_opp : forall P, in_subgroup P -> in_subgroup (popp P).
    Proof. unfold in_subgroup; intros P hP; rewrite smul_opp_r, hP; apply popp_zero. Qed.
    Lemma closed_smul : forall k P, in_subgroup P -> in_subgroup (smul k P).
    Proof.
      unfold in_subgroup; intros k P hP.
      rewrite smul_assoc, Z.mul_comm. apply smul_times_order; exact hP.
    Qed.

    (** The group operations on [G] and the scalar action
        [gpow x k = (unsigned k) · x]. *)
    Definition gid : G := exist _ pzero closed_zero.
    Definition gop (x y : G) : G :=
      exist _ (padd (proj1_sig x) (proj1_sig y)) (closed_add _ _ (proj2_sig x) (proj2_sig y)).
    Definition ginv (x : G) : G :=
      exist _ (popp (proj1_sig x)) (closed_opp _ (proj2_sig x)).
    Definition gpow (x : G) (k : Zn.F) : G :=
      exist _ (smul (Zmod.unsigned k) (proj1_sig x)) (closed_smul _ _ (proj2_sig x)).

    (** [G] is a commutative group. *)
    Global Instance p256_comm_group : @commutative_group G (@eq G) gop gid ginv.
    Proof.
      refine {|
        commutative_group_group := {|
          group_monoid := {|
            monoid_is_associative := _;
            monoid_is_left_idenity := _;
            monoid_is_right_identity := _;
            monoid_op_Proper := _;
            monoid_Equivalence := eq_equivalence |};
          group_is_left_inverse := _;
          group_is_right_inverse := _;
          group_inv_Proper := _ |};
        commutative_group_is_commutative := _ |}.
      all: try (repeat intro; subst; reflexivity).
      all: hnf; intros; apply G_eq; cbn;
        first [apply padd_assoc | apply padd_zero_l | apply padd_zero_r |
               apply padd_opp_l | apply padd_opp_r | apply padd_comm].
    Qed.

    (** The action axioms for [gpow]. Associativity and distributivity over
        scalar addition reduce modulo [n], which is sound because every
        element of [G] is killed by [n] ([smul_mod_order]). *)
    Lemma gpow_one : forall x : G, gpow x Zn.one = x.
    Proof.
      intros x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig]. rewrite Zn.unsigned_one; apply smul_1_l.
    Qed.
    Lemma gpow_zero : forall x : G, gpow x Zn.zero = gid.
    Proof.
      intros x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig]. rewrite Zn.unsigned_zero; apply smul_0_l.
    Qed.
    Lemma gpow_assoc : forall (r1 r2 : Zn.F) (x : G), gpow x (Zn.mul r1 r2) = gpow (gpow x r1) r2.
    Proof.
      intros r1 r2 x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig].
      rewrite Zn.unsigned_mul, smul_mod_order, smul_assoc; [reflexivity | exact (proj2_sig x)].
    Qed.
    Lemma gpow_distr_fadd : forall (r1 r2 : Zn.F) (x : G), gpow x (Zn.add r1 r2) = gop (gpow x r1) (gpow x r2).
    Proof.
      intros r1 r2 x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig].
      rewrite Zn.unsigned_add, smul_mod_order, smul_add_l; [reflexivity | exact (proj2_sig x)].
    Qed.
    Lemma gpow_distr_vadd : forall (r : Zn.F) (x y : G), gpow (gop x y) r = gop (gpow x r) (gpow y r).
    Proof.
      intros r x y; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig].
      apply smul_add_r; apply Zn.unsigned_nonneg.
    Qed.

    (** _P-256 as a vector space._ [G] is a vector space over [Z_n] with
        the reference scalar multiplication. *)
    Global Instance p256_vspace :
      @vector_space Zn.F (@eq Zn.F) Zn.zero Zn.one Zn.add Zn.mul Zn.sub Zn.div Zn.opp Zn.inv
        G (@eq G) gid ginv gop gpow.
    Proof.
      econstructor.
      all: try (repeat intro; subst; reflexivity).
      all: hnf; first [apply p256_comm_group | apply Zn.zn_field | apply gpow_one |
                  apply gpow_zero | apply gpow_assoc | apply gpow_distr_fadd |
                  apply gpow_distr_vadd].
    Qed.

    (** *** Fast scalar multiplication in Jacobian coordinates *)

    (** Points in Jacobian coordinates [(X : Y : Z)], representing
        [(X / Z ^ 2, Y / Z ^ 3)]. *)
    Definition jpoint : Type :=
      J.point (F := Fp) (Feq := eq) (Fzero := Zmod.zero) (Fadd := Zmod.add) (Fmul := Zmod.mul)
        (a := a) (b := b).

    (** Conversion between affine and Jacobian coordinates. *)
    Definition from_affine : point -> jpoint :=
      J.of_affine (field := field) (a := a) (b := b).
    Definition to_affine : jpoint -> point :=
      J.to_affine (field := field) (a := a) (b := b).
    (** Addition and doubling in Jacobian coordinates (fiat-crypto's
        verified formulas). *)
    Definition jadd : jpoint -> jpoint -> jpoint :=
      J.add (field := field) (char_ge_3 := char_ge_3) (a := a) (b := b).
    Definition jdouble : jpoint -> jpoint :=
      J.double (field := field) (a := a) (b := b).

    (** Multiplication by a positive integer, by recursion on its binary
        representation, most significant bit first. *)
    Fixpoint jmul_pos (k : positive) (P : jpoint) : jpoint :=
      match k with
      | xH => P
      | xO k' => jdouble (jmul_pos k' P)
      | xI k' => jadd P (jdouble (jmul_pos k' P))
      end.

    (** Scalar multiplication through Jacobian coordinates for positive
        scalars, falling back to [smul] for zero and negative ones. *)
    Definition fast_smul (k : Z) (P : point) : point :=
      match k with
      | Zpos q => to_affine (jmul_pos q (from_affine P))
      | _ => smul k P
      end.

    (** Converting back to affine coordinates commutes with addition and
        doubling, and inverts [from_affine]. *)
    Lemma to_affine_jadd : forall P Q : jpoint,
      to_affine (jadd P Q) = padd (to_affine P) (to_affine Q).
    Proof. intros; apply peq_leibniz; apply J.to_affine_add. Qed.
    Lemma to_affine_jdouble : forall P : jpoint,
      to_affine (jdouble P) = padd (to_affine P) (to_affine P).
    Proof. intros; apply peq_leibniz; apply J.to_affine_double. Qed.
    Lemma to_from_affine : forall P : point, to_affine (from_affine P) = P.
    Proof. intros; apply peq_leibniz; apply J.to_affine_of_affine. Qed.

    (** [jmul_pos] computes [q · P], by induction on [q]. *)
    Lemma jmul_pos_correct : forall (q : positive) (P : jpoint),
      to_affine (jmul_pos q P) = smul (Zpos q) (to_affine P).
    Proof.
      induction q as [q ih | q ih |]; intro P; cbn [jmul_pos].
      + rewrite to_affine_jadd, to_affine_jdouble, ih, <-smul_add_l.
        replace (Zpos q~1) with (Z.succ (Zpos q + Zpos q)) by lia.
        rewrite smul_succ_l; reflexivity.
      + rewrite to_affine_jdouble, ih, <-smul_add_l.
        replace (Zpos q~0) with (Zpos q + Zpos q) by lia.
        reflexivity.
      + rewrite smul_1_l; reflexivity.
    Qed.

    (** _Correctness of fast scalar multiplication:_
        [fast_smul k P = smul k P]. *)
    Lemma fast_smul_eq : forall (k : Z) (P : point), fast_smul k P = smul k P.
    Proof.
      intros [| q | q] P; cbn [fast_smul]; try reflexivity.
      rewrite jmul_pos_correct, to_from_affine; reflexivity.
    Qed.

    (** The subgroup is closed under [fast_smul]. *)
    Lemma closed_fast_smul : forall k P, in_subgroup P -> in_subgroup (fast_smul k P).
    Proof. intros k P hP; rewrite fast_smul_eq; apply closed_smul; exact hP. Qed.

    (** The scalar action using [fast_smul], and its agreement with
        [gpow]. *)
    Definition gpow_fast (x : G) (k : Zn.F) : G :=
      exist _ (fast_smul (Zmod.unsigned k) (proj1_sig x)) (closed_fast_smul _ _ (proj2_sig x)).

    Lemma gpow_fast_eq : forall (x : G) (k : Zn.F), gpow_fast x k = gpow x k.
    Proof. intros; apply G_eq; unfold gpow_fast, gpow; cbn [proj1_sig]; apply fast_smul_eq. Qed.

    (** [G] is a vector space over [Z_n] with the fast scalar
        multiplication; all laws are inherited through [gpow_fast_eq]. *)
    Global Instance p256_vspace_fast :
      @vector_space Zn.F (@eq Zn.F) Zn.zero Zn.one Zn.add Zn.mul Zn.sub Zn.div Zn.opp Zn.inv
        G (@eq G) gid ginv gop gpow_fast.
    Proof.
      refine {|
        vector_space_commutative_group := p256_comm_group;
        vector_space_field := Zn.zn_field;
        vector_space_field_one := _;
        vector_space_field_zero := _;
        vector_space_smul_associative_fmul := _;
        vector_space_smul_distributive_fadd := _;
        vector_space_smul_distributive_vadd := _;
        vector_space_smul_Proper := _ |}.
      all: try (repeat intro; subst; reflexivity).
      all: hnf; intros; rewrite ?gpow_fast_eq;
        first [apply gpow_one | apply gpow_zero | apply gpow_assoc |
               apply gpow_distr_fadd | apply gpow_distr_vadd].
    Qed.

    (** *** The base point *)

    (** Affine coordinates of the standard P-256 base point. *)
    Definition Gx : Fp := Zmod.of_Z _ 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296.
    Definition Gy : Fp := Zmod.of_Z _ 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5.

    (** The base point as a curve point; the on-curve condition is checked
        by [vm_decide]. *)
    Definition Bpt : point.
    Proof.
      refine (exist _ (inl (Gx, Gy)) _).
      cbv [W.coordinates]; Fiat.Util.Decidable.vm_decide.
    Defined.

    (** Canonical integer coordinates of a point, [None] for infinity. *)
    Definition coords (P : point) : option (Z * Z) :=
      match proj1_sig P with
      | inl (x, y) => Some (Zmod.unsigned x, Zmod.unsigned y)
      | inr _ => None
      end.

    (** Points with the same canonical coordinates are equal. *)
    Lemma point_coords_eq : forall P Q : point, coords P = coords Q -> P = Q.
    Proof.
      intros [[[x1 y1] | []] h1] [[[x2 y2] | []] h2] h; cbv [coords proj1_sig] in h;
        try discriminate.
      + injection h as hx hy.
        apply (Zmod.unsigned_inj p) in hx; apply (Zmod.unsigned_inj p) in hy; subst.
        f_equal; apply Eqdep_dec.UIP_dec; exact Fp_dec.
      + destruct h1, h2; reflexivity.
    Qed.

    (** [n · B = 0], checked by computing with [fast_smul] under
        [vm_compute]. *)
    Lemma B_in_subgroup : in_subgroup Bpt.
    Proof.
      unfold in_subgroup; rewrite <-fast_smul_eq.
      apply point_coords_eq; vm_compute; reflexivity.
    Qed.

    (** The base point as an element of [G]. *)
    Definition B : G := exist _ Bpt B_in_subgroup.

  End Wp.

End P256.
