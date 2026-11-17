(** * Ed25519 as a vector space over [Z_l] *)

(** This file instantiates the [vector_space] class of
    [Algebra/Hierarchy.v] with the prime-order subgroup of the Edwards
    curve Ed25519 (Bernstein, Duif, Lange, Schwabe, Yang 2012; RFC 8032),
    building on the verified curve arithmetic of fiat-crypto vendored under
    [src/Fiat]. The curve is the twisted Edwards curve
    [-x ^ 2 + y ^ 2 = 1 + d x ^ 2 y ^ 2] over [F_p] with [p = 2 ^ 255 - 19];
    its group of points has order [8 l] where
    [l = 2 ^ 252 + 27742317777372353535851937790883648493] is prime.

    Structure of the file:

    - [Zl]: the scalar field [Z_l], implemented with the standard library's
      [Zmod l], and its [field] instance [zl_field].
    - [Ed]: the curve. fiat-crypto's affine points and their commutative
      group (proved there with respect to a coordinate-wise equivalence
      [peq]) are transferred to Leibniz equality ([peq_leibniz]). Scalar
      multiplication is fiat-crypto's reference implementation
      [scalarmult_ref]. The type [G] is the subgroup of points [P] with
      [l · P = 0] (a sigma type, with proof irrelevance from decidable
      equality), and [gpow x k] multiplies [x] by the canonical
      representative of [k ∈ Z_l]. The instance [ed25519_vspace] makes
      [(G, Z_l)] a vector space, so every generic Sigma-protocol, ElGamal
      and shuffle result applies to Ed25519.
    - A faster scalar multiplication [fast_smul] by double-and-add in
      extended twisted Edwards coordinates (fiat-crypto's [m1add] and
      [m1double], valid since [a = -1]), proved equal to the reference
      implementation ([fast_smul_eq]); the instance [ed25519_vspace_fast]
      uses it and is the one to extract. The double-and-add loop is not
      constant time.
    - The standard base point [B] and a proof, by computation, that it lies
      in the order-[l] subgroup ([B_in_subgroup]).

    Instances are used in [Examples/Ed25519Ins.v] and other example files.
    [Curve/P256.v] follows the same structure for NIST P-256. *)
From Stdlib Require Import
  ZArith Znumtheory Zmod Lia Utf8 Eqdep_dec Morphisms RelationClasses.
From Fiat Require
  Spec.Curve25519 Spec.CompleteEdwardsCurve Curves.Edwards.AffineProofs
  Curves.Edwards.XYZT.Basic Algebra.ScalarMult Algebra.Hierarchy
  Arithmetic.PrimeFieldTheorems Util.Decidable.
From Algebra Require Import Hierarchy.

(** ** The module [Ed25519] *)
Module Ed25519.

  (** Short names for the fiat-crypto modules used below: the Curve25519
      specification, affine Edwards proofs, scalar multiplication, extended
      coordinates and fiat's algebraic hierarchy. *)
  Module C := Fiat.Spec.Curve25519.
  Module CE := Fiat.Spec.Curve25519.E.
  Module AP := Fiat.Curves.Edwards.AffineProofs.E.
  Module SM := Fiat.Algebra.ScalarMult.
  Module X := Fiat.Curves.Edwards.XYZT.Basic.Extended.
  Module FH := Fiat.Algebra.Hierarchy.

  Local Open Scope Z_scope.
  (** The base-field modulus [p] and the prime subgroup order [l]. *)
  Local Notation p := (2^255 - 19).
  Local Notation l := (2^252 + 27742317777372353535851937790883648493).

  (** [l > 0], [l ≠ 0] and [|l| ≥ 2], by computation. *)
  Lemma l_pos : 0 < l.
  Proof. vm_compute; reflexivity. Qed.

  Lemma l_nonzero : l <> 0.
  Proof. intro h; vm_compute in h; discriminate h. Qed.

  Lemma l_ge_2 : 2 <= Z.abs l.
  Proof. vm_compute; intro h; discriminate h. Qed.

  (** *** The scalar field [Z_l] *)

  (** Integers modulo [l] using the standard library's [Zmod]. The
      operations are the [Zmod] ones; division is [mdiv]. *)
  Module Zl.

    (** Carrier and operations of [Z_l]. *)
    Definition F : Type := Zmod l.
    Definition zero : F := Zmod.zero.
    Definition one : F := Zmod.one.
    Definition add : F -> F -> F := Zmod.add.
    Definition mul : F -> F -> F := Zmod.mul.
    Definition sub : F -> F -> F := Zmod.sub.
    Definition opp : F -> F := Zmod.opp.
    Definition inv : F -> F := Zmod.inv.
    Definition div : F -> F -> F := Zmod.mdiv.

    (** Primality of [l], taken from fiat-crypto's Curve25519
        specification. *)
    Definition prime_l : prime l := C.prime_l.

    (** Decidable equality, by comparing canonical representatives. *)
    Definition Fdec : forall x y : F, {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct (Z.eq_dec (Zmod.unsigned x) (Zmod.unsigned y)) as [h | h].
      + left; apply (Zmod.unsigned_inj l); exact h.
      + right; intro e; apply h; rewrite e; reflexivity.
    Defined.

    (** [unsigned_nonneg], [unsigned_one], [unsigned_zero], [unsigned_add]
        and [unsigned_mul]: the canonical representative [u] (with [0 ≤ u < l]) of
        constants, sums and products. Used to relate [gpow] to integer
        scalar multiplication. *)
    Lemma unsigned_nonneg : forall x : F, 0 <= Zmod.unsigned x.
    Proof.
      intro x. pose proof (Zmod.unsigned_pos_bound x l_pos) as h; lia.
    Qed.

    Lemma unsigned_one : Zmod.unsigned one = 1.
    Proof. unfold one; rewrite Zmod.unsigned_1; vm_compute; reflexivity. Qed.

    Lemma unsigned_zero : Zmod.unsigned zero = 0.
    Proof. unfold zero; apply Zmod.unsigned_0. Qed.

    Lemma unsigned_add : forall x y : F,
      Zmod.unsigned (add x y) = (Zmod.unsigned x + Zmod.unsigned y) mod l.
    Proof. intros; apply Zmod.unsigned_add. Qed.

    Lemma unsigned_mul : forall x y : F,
      Zmod.unsigned (mul x y) = (Zmod.unsigned x * Zmod.unsigned y) mod l.
    Proof. intros; apply Zmod.unsigned_mul. Qed.

    (** The field axioms of [Z_l], one lemma per axiom, each a direct
        consequence of the corresponding [Zmod] lemma; the inverse axiom
        uses primality of [l] via fiat-crypto's [Zmod.inv_nonzero]. *)
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
    Proof. intros x hx; apply (@Fiat.Arithmetic.PrimeFieldTheorems.Zmod.inv_nonzero l prime_l x hx). Qed.
    Lemma zero_neq_one : @is_zero_neq_one F eq zero one.
    Proof. intro h; symmetry in h; revert h; apply (Zmod.one_neq_zero l_ge_2). Qed.
    Lemma div_def : forall x y : F, div x y = mul x (inv y).
    Proof. intros; symmetry; apply Zmod.mul_inv_r. Qed.

    (** [Z_l] is a [field] in the sense of [Algebra/Hierarchy.v]. *)
    Global Instance zl_field :
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

  End Zl.

  (** *** Curve points and the order-[l] subgroup *)
  Module Ed.

    (** The base field [F_p] and its decidable equality. *)
    Definition Fp : Type := Zmod p.

    Definition Fp_dec : forall x y : Fp, {x = y} + {x <> y}.
    Proof.
      intros x y.
      destruct (Z.eq_dec (Zmod.unsigned x) (Zmod.unsigned y)) as [h | h].
      + left; apply (Zmod.unsigned_inj p); exact h.
      + right; intro e; apply h; rewrite e; reflexivity.
    Defined.

    (** Affine points (with an on-curve proof), addition, identity,
        negation and the coordinate-wise equivalence [peq], all taken
        from fiat-crypto. *)
    Definition point : Type := CE.point.
    Definition padd : point -> point -> point := CE.add.
    Definition pzero : point := CE.zero.
    Definition popp : point -> point :=
      AP.opp (field := C.field) (a := CE.a) (d := CE.d) (nonzero_a := CE.nonzero_a).
    Definition peq : point -> point -> Prop :=
      @Fiat.Spec.CompleteEdwardsCurve.E.eq Fp eq Zmod.one Zmod.add Zmod.mul CE.a CE.d.

    (** fiat-crypto's proof that the affine points form a commutative group
        (for [a] a square and [d] a non-square). *)
    Definition fiat_group : @FH.commutative_group point peq padd pzero popp :=
      AP.edwards_curve_commutative_group (field := C.field) (char_ge_3 := C.char_ge_3)
        (a := CE.a) (d := CE.d) (nonzero_a := CE.nonzero_a)
        (square_a := CE.square_a) (nonsquare_d := CE.nonsquare_d).
    Definition fiat_grp : @FH.group point peq padd pzero popp :=
      FH.commutative_group_group fiat_group.

    (** [peq] coincides with Leibniz equality on points, because the
        on-curve proofs are irrelevant (UIP on a type with decidable
        equality). *)
    Lemma peq_leibniz : forall P Q : point, peq P Q -> P = Q.
    Proof.
      intros [[x1 y1] h1] [[x2 y2] h2] [hx hy]; cbn in hx, hy; subst.
      f_equal; apply Eqdep_dec.UIP_dec; exact Fp_dec.
    Qed.

    Lemma leibniz_peq : forall P Q : point, P = Q -> peq P Q.
    Proof. intros P Q h; subst; destruct Q as [[x y] h]; split; reflexivity. Qed.

    (** Decidable equality on points. *)
    Definition point_dec : forall P Q : point, {P = Q} + {P <> Q}.
    Proof.
      intros [[x1 y1] h1] [[x2 y2] h2].
      destruct (Fp_dec x1 x2) as [hx | hx]; [destruct (Fp_dec y1 y2) as [hy | hy] |].
      + subst; left; f_equal; apply Eqdep_dec.UIP_dec; exact Fp_dec.
      + right; intro h; apply hy.
        exact (f_equal (fun z => snd (proj1_sig z)) h).
      + right; intro h; apply hx.
        exact (f_equal (fun z => fst (proj1_sig z)) h).
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

    (** Scalar multiplication [smul n P] (for [n : Z]) is fiat-crypto's
        reference implementation, which satisfies its [is_scalarmult]
        specification. *)
    Local Notation smul := (@SM.scalarmult_ref point padd pzero popp).
    Definition smul_is : @SM.is_scalarmult point peq padd pzero popp smul :=
      @SM.scalarmult_ref_is_scalarmult point peq padd pzero popp fiat_grp.

    (** Properties of [smul] transferred to Leibniz equality: [0 · P = 0],
        [1 · P = P], [(n + 1) · P = P + n · P], [(n + m) · P = n · P + m · P],
        [n · (m · P) = (m n) · P], [n · 0 = 0], [n · (-P) = -(n · P)], and,
        for [P] with [l · P = 0], [(n mod l) · P = n · P] and
        [(l n) · P = 0]. *)
    Lemma smul_0_l : forall P : point, smul 0 P = pzero.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_0_l point peq padd pzero popp smul smul_is). Qed.
    Lemma smul_1_l : forall P : point, smul 1 P = P.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_1_l point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_succ_l : forall (n : Z) (P : point), smul (Z.succ n) P = padd P (smul n P).
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_succ_l point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_add_l : forall (n m : Z) (P : point), smul (n + m) P = padd (smul n P) (smul m P).
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_add_l point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_assoc : forall (n m : Z) (P : point), smul n (smul m P) = smul (m * n) P.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_assoc point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_zero_r : forall n : Z, smul n pzero = pzero.
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_zero_r point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_opp_r : forall (n : Z) (P : point), smul n (popp P) = popp (smul n P).
    Proof. intros; apply peq_leibniz; apply (@SM.scalarmult_opp_r point peq padd pzero popp fiat_grp smul smul_is). Qed.
    Lemma smul_mod_order : forall (P : point), smul l P = pzero ->
      forall n : Z, smul (n mod l) P = smul n P.
    Proof.
      intros P hP n; apply peq_leibniz.
      apply (@SM.scalarmult_mod_order point peq padd pzero popp fiat_grp smul smul_is l P l_nonzero).
      apply leibniz_peq; exact hP.
    Qed.
    Lemma smul_times_order : forall (P : point), smul l P = pzero ->
      forall n : Z, smul (l * n) P = pzero.
    Proof.
      intros P hP n; apply peq_leibniz.
      apply (@SM.scalarmult_times_order point peq padd pzero popp fiat_grp smul smul_is l P).
      apply leibniz_peq; exact hP.
    Qed.

    (** [n · (P + Q) = n · P + n · Q] for [n ≥ 0], by induction on [n]
        using commutativity. *)
    Lemma smul_add_r : forall (n : Z) (P Q : point), 0 <= n ->
      smul n (padd P Q) = padd (smul n P) (smul n Q).
    Proof.
      intros n P Q hn.
      pattern n; apply natlike_ind; [| | exact hn].
      + rewrite !smul_0_l, padd_zero_l; reflexivity.
      + intros m hm ih. rewrite !smul_succ_l, ih.
        rewrite <-!padd_assoc. f_equal.
        rewrite !padd_assoc, (padd_comm Q). reflexivity.
    Qed.

    (** Membership in the prime-order subgroup: [l · P = 0]. *)
    Definition in_subgroup (P : point) : Prop := smul l P = pzero.

    (** Proofs of subgroup membership are unique. *)
    Lemma in_subgroup_irrel : forall (P : point) (h1 h2 : in_subgroup P), h1 = h2.
    Proof. intros; apply Eqdep_dec.UIP_dec; exact point_dec. Qed.

    (** The prime-order subgroup [G] of Ed25519, as a sigma type. *)
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
      rewrite smul_add_r, hP, hQ, padd_zero_l; [reflexivity | pose proof l_pos; lia].
    Qed.
    Lemma closed_opp : forall P, in_subgroup P -> in_subgroup (popp P).
    Proof. unfold in_subgroup; intros P hP; rewrite smul_opp_r, hP; apply popp_zero. Qed.
    Lemma closed_smul : forall n P, in_subgroup P -> in_subgroup (smul n P).
    Proof.
      unfold in_subgroup; intros n P hP.
      rewrite smul_assoc, Z.mul_comm. apply smul_times_order; exact hP.
    Qed.

    (** The group operations on [G] and the scalar action
        [gpow x k = (unsigned k) · x], using the canonical representative
        of [k ∈ Z_l]. *)
    Definition gid : G := exist _ pzero closed_zero.
    Definition gop (x y : G) : G :=
      exist _ (padd (proj1_sig x) (proj1_sig y)) (closed_add _ _ (proj2_sig x) (proj2_sig y)).
    Definition ginv (x : G) : G :=
      exist _ (popp (proj1_sig x)) (closed_opp _ (proj2_sig x)).
    Definition gpow (x : G) (k : Zl.F) : G :=
      exist _ (smul (Zmod.unsigned k) (proj1_sig x)) (closed_smul _ _ (proj2_sig x)).

    (** [G] is a commutative group. *)
    Global Instance ed25519_comm_group : @commutative_group G (@eq G) gop gid ginv.
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
        scalar addition reduce modulo [l], which is sound because every
        element of [G] is killed by [l] ([smul_mod_order]). *)
    Lemma gpow_one : forall x : G, gpow x Zl.one = x.
    Proof.
      intros x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig]. rewrite Zl.unsigned_one; apply smul_1_l.
    Qed.
    Lemma gpow_zero : forall x : G, gpow x Zl.zero = gid.
    Proof.
      intros x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig]. rewrite Zl.unsigned_zero; apply smul_0_l.
    Qed.
    Lemma gpow_assoc : forall (r1 r2 : Zl.F) (x : G), gpow x (Zl.mul r1 r2) = gpow (gpow x r1) r2.
    Proof.
      intros r1 r2 x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig].
      rewrite Zl.unsigned_mul, smul_mod_order, smul_assoc; [reflexivity | exact (proj2_sig x)].
    Qed.
    Lemma gpow_distr_fadd : forall (r1 r2 : Zl.F) (x : G), gpow x (Zl.add r1 r2) = gop (gpow x r1) (gpow x r2).
    Proof.
      intros r1 r2 x; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig].
      rewrite Zl.unsigned_add, smul_mod_order, smul_add_l; [reflexivity | exact (proj2_sig x)].
    Qed.
    Lemma gpow_distr_vadd : forall (r : Zl.F) (x y : G), gpow (gop x y) r = gop (gpow x r) (gpow y r).
    Proof.
      intros r x y; apply G_eq; unfold gpow, gop, gid; cbn [proj1_sig].
      apply smul_add_r; apply Zl.unsigned_nonneg.
    Qed.

    (** _Ed25519 as a vector space._ [G] is a vector space over [Z_l] with
        the reference scalar multiplication. *)
    Global Instance ed25519_vspace :
      @vector_space Zl.F (@eq Zl.F) Zl.zero Zl.one Zl.add Zl.mul Zl.sub Zl.div Zl.opp Zl.inv
        G (@eq G) gid ginv gop gpow.
    Proof.
      econstructor.
      all: try (repeat intro; subst; reflexivity).
      all: hnf; first [apply ed25519_comm_group | apply Zl.zl_field | apply gpow_one |
                  apply gpow_zero | apply gpow_assoc | apply gpow_distr_fadd |
                  apply gpow_distr_vadd].
    Qed.

    (** *** Fast scalar multiplication

        Double-and-add in extended twisted Edwards coordinates
        [(X : Y : Z : T)], using fiat-crypto's verified formulas for
        [a = -1], and its proof of agreement with [smul]. *)

    (** Points in extended coordinates. *)
    Definition xpoint : Type := @X.point Fp eq Zmod.zero Zmod.add Zmod.mul CE.a CE.d.

    (** Conversion between affine and extended coordinates. *)
    Definition from_affine : point -> xpoint :=
      X.from_affine (field := C.field) (a := CE.a) (d := CE.d) (nonzero_a := CE.nonzero_a).
    Definition to_affine : xpoint -> point :=
      X.to_affine (field := C.field) (a := CE.a) (d := CE.d) (nonzero_a := CE.nonzero_a).

    (** The curve parameter [a] is [-1], and [twice_d = 2 d]; both are
        side conditions of the [a = -1] formulas. *)
    Lemma a_eq_minus1 : CE.a = Zmod.opp Zmod.one.
    Proof. reflexivity. Qed.
    Definition twice_d : Fp := Zmod.add CE.d CE.d.
    Lemma k_eq_2d : twice_d = Zmod.add CE.d CE.d.
    Proof. reflexivity. Qed.

    (** Addition and doubling in extended coordinates. *)
    Definition xadd : xpoint -> xpoint -> xpoint :=
      X.m1add (field := C.field) (char_ge_3 := C.char_ge_3) (a := CE.a) (d := CE.d)
        (nonzero_a := CE.nonzero_a) (square_a := CE.square_a) (nonsquare_d := CE.nonsquare_d)
        (a_eq_minus1 := a_eq_minus1) (twice_d := twice_d) (k_eq_2d := k_eq_2d).
    Definition xdouble : xpoint -> xpoint :=
      X.m1double (field := C.field) (char_ge_3 := C.char_ge_3) (a := CE.a) (d := CE.d)
        (nonzero_a := CE.nonzero_a) (square_a := CE.square_a) (nonsquare_d := CE.nonsquare_d)
        (a_eq_minus1 := a_eq_minus1) (twice_d := twice_d) (k_eq_2d := k_eq_2d).

    (** Multiplication by a positive integer, by recursion on its binary
        representation, most significant bit first: [xO n] doubles,
        [xI n] doubles and adds [P]. *)
    Fixpoint xmul_pos (n : positive) (P : xpoint) : xpoint :=
      match n with
      | xH => P
      | xO n' => xdouble (xmul_pos n' P)
      | xI n' => xadd P (xdouble (xmul_pos n' P))
      end.

    (** Scalar multiplication through extended coordinates for positive
        scalars, falling back to [smul] for zero and negative ones. *)
    Definition fast_smul (n : Z) (P : point) : point :=
      match n with
      | Zpos q => to_affine (xmul_pos q (from_affine P))
      | _ => smul n P
      end.

    (** Converting back to affine coordinates commutes with addition and
        doubling, and inverts [from_affine]. *)
    Lemma to_affine_xadd : forall P Q : xpoint,
      to_affine (xadd P Q) = padd (to_affine P) (to_affine Q).
    Proof. intros; apply peq_leibniz; apply X.to_affine_m1add. Qed.
    Lemma to_affine_xdouble : forall P : xpoint,
      to_affine (xdouble P) = padd (to_affine P) (to_affine P).
    Proof. intros; apply peq_leibniz; apply X.to_affine_m1double. Qed.
    Lemma to_from_affine : forall P : point, to_affine (from_affine P) = P.
    Proof. intros; apply peq_leibniz; apply X.to_affine_from_affine. Qed.

    (** [xmul_pos] computes [q · P], by induction on [q]. *)
    Lemma xmul_pos_correct : forall (q : positive) (P : xpoint),
      to_affine (xmul_pos q P) = smul (Zpos q) (to_affine P).
    Proof.
      induction q as [q ih | q ih |]; intro P; cbn [xmul_pos].
      + rewrite to_affine_xadd, to_affine_xdouble, ih, <-smul_add_l.
        replace (Zpos q~1) with (Z.succ (Zpos q + Zpos q)) by lia.
        rewrite smul_succ_l; reflexivity.
      + rewrite to_affine_xdouble, ih, <-smul_add_l.
        replace (Zpos q~0) with (Zpos q + Zpos q) by lia.
        reflexivity.
      + rewrite smul_1_l; reflexivity.
    Qed.

    (** _Correctness of fast scalar multiplication:_
        [fast_smul n P = smul n P]. *)
    Lemma fast_smul_eq : forall (n : Z) (P : point), fast_smul n P = smul n P.
    Proof.
      intros [| q | q] P; cbn [fast_smul]; try reflexivity.
      rewrite xmul_pos_correct, to_from_affine; reflexivity.
    Qed.

    (** The subgroup is closed under [fast_smul]. *)
    Lemma closed_fast_smul : forall n P, in_subgroup P -> in_subgroup (fast_smul n P).
    Proof. intros n P hP; rewrite fast_smul_eq; apply closed_smul; exact hP. Qed.

    (** The scalar action using [fast_smul], and its agreement with
        [gpow]. *)
    Definition gpow_fast (x : G) (k : Zl.F) : G :=
      exist _ (fast_smul (Zmod.unsigned k) (proj1_sig x)) (closed_fast_smul _ _ (proj2_sig x)).

    Lemma gpow_fast_eq : forall (x : G) (k : Zl.F), gpow_fast x k = gpow x k.
    Proof. intros; apply G_eq; unfold gpow_fast, gpow; cbn [proj1_sig]; apply fast_smul_eq. Qed.

    (** [G] is a vector space over [Z_l] with the fast scalar
        multiplication; all laws are inherited from [ed25519_vspace]
        through [gpow_fast_eq]. *)
    Global Instance ed25519_vspace_fast :
      @vector_space Zl.F (@eq Zl.F) Zl.zero Zl.one Zl.add Zl.mul Zl.sub Zl.div Zl.opp Zl.inv
        G (@eq G) gid ginv gop gpow_fast.
    Proof.
      refine {|
        vector_space_commutative_group := ed25519_comm_group;
        vector_space_field := Zl.zl_field;
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

    (** Points are equal when the canonical representatives of their
        coordinates are equal. Used to check equalities of concrete points
        by computation. *)
    Lemma point_coords_eq : forall P Q : point,
      (Zmod.unsigned (fst (proj1_sig P)), Zmod.unsigned (snd (proj1_sig P))) =
      (Zmod.unsigned (fst (proj1_sig Q)), Zmod.unsigned (snd (proj1_sig Q))) ->
      P = Q.
    Proof.
      intros [[x1 y1] h1] [[x2 y2] h2] h; cbn in h.
      injection h as hx hy.
      apply (Zmod.unsigned_inj p) in hx; apply (Zmod.unsigned_inj p) in hy; subst.
      f_equal; apply Eqdep_dec.UIP_dec; exact Fp_dec.
    Qed.

    (** The standard Ed25519 base point lies in the order-[l] subgroup,
        checked by computing [l · B] with [fast_smul] under
        [vm_compute]. *)
    Lemma B_in_subgroup : in_subgroup CE.B.
    Proof.
      unfold in_subgroup; rewrite <-fast_smul_eq.
      apply point_coords_eq; vm_compute; reflexivity.
    Qed.

    (** The base point as an element of [G]. *)
    Definition B : G := exist _ CE.B B_in_subgroup.

  End Ed.

End Ed25519.
