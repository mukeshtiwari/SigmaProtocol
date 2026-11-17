(** * The groups [Z_p^*], the field [Z_p] and Schnorr groups

    This file provides the concrete algebraic structures over which most
    protocols of the development are instantiated (see the [*Ins.v] files in
    [Examples], for example [ElgamalIns.v], [ChaumPedersenIns.v] or
    [BayerGrothIns.v]).  It contains four modules, each parameterised over
    primes given as section [Context] variables:

    - [Zpgroup]: the multiplicative group [Z_p^*] = [{1, …, p-1}] for a prime
      [p], with multiplication modulo [p] and inverse [a ↦ a^(p-2) mod p];
      the main result is the instance [zpstar_comm] of [commutative_group]
      (from [Algebra/Hierarchy.v]).
    - [Zpfield]: the prime field [Z_p], with elements represented as integers
      [v] satisfying [v mod p = v]; the main result is the instance
      [zp_field] of [field].
    - [Schnorr]: the Schnorr group, that is, the subgroup of order [q] of
      [Z_p^*] for primes [p = k·q + 1], described as the set of [v] with
      [0 < v < p] and [v^q ≡ 1 (mod p)]; the main result is [schnorr_comm].
    - [Vspace]: exponentiation [g ↦ g^x] makes the Schnorr group a vector
      space over [Z_q] in the sense of [Algebra/Hierarchy.v] (written
      additively, it is a [Z_q]-module); the instance is [pow_vspace].  This
      is the form in which a prime-order group enters the generic Sigma
      protocol and ElGamal developments: scalars are [Zpfield.Zp q] and group
      elements are [Schnorr.Schnorr_group p q].

    Elements are dependent records that pair an integer with a proof of its
    range condition.  Because the conditions are decidable equalities on [Z]
    or [comparison], their proofs are unique (by [Eqdep_dec]), so two
    elements are equal as soon as their integer components are equal
    ([construct_zpstar], [construct_zp], [construct_schnorr_group]).
    Operations are defined with [refine] and closed with [Defined], so that
    they compute after extraction; side conditions are discharged with
    [abstract], which keeps the proof terms out of the computational code.
    Equality deciders such as [dec_zpstar] are also closed with [Defined]
    because the extracted verifiers use them to compare group elements.

    Inverses are computed with Fermat's little theorem: for [0 < a < p],
    [a · a^(p-2) = a^(p-1) ≡ 1 (mod p)] ([Fermat.fermat_little_ZZ]), and
    [Fermat.fermat_bound] shows [a^(p-2) mod p] is again in [{1, …, p-1}].
    The exponentiation itself is the executable square-and-multiply
    [Functions.Npow_mod] on [N], related to [Zpow_mod] by
    [Functions.zmod_nmod].  Several arithmetic facts ([multiplication_bound],
    [Hp_2_p], [mod_more_gen_bound], [mod_exists_pos]) come from the
    prime-modulus section at the end of [Util.v]. *)
From Stdlib Require Import
  PArith ZArith Lia
  Znumtheory
  Eqdep_dec Arith
  Zpow_facts Morphisms
  NArith Utf8.
From Utility Require Import
  Util Functions Fermat.
From Algebra Require Import
  Hierarchy.

(** ** The multiplicative group [Z_p^*] *)
Module Zpgroup.

  (** The section is parameterised by a prime [p]. *)
  Section ZpstarGroup.
    Context
      {p : Z}
      {Hp : prime p}.

    (** An element of [Z_p^*]: an integer [v] with a proof that [0 < v < p]. *)
    Record Zpstar :=
      mk_zpstar {v : Z; Hv : 0 < v < p}.

    (** Proof irrelevance for [<] on [Z]: since [x < y] unfolds to the
        equation [Z.compare x y = Lt] on a type with decidable equality, any two
        proofs are equal. *)
    Lemma dec_lt_general :
      forall x y (Hx Hy: (x < y)),  Hx = Hy.
    Proof.
      intros; apply Eqdep_dec.eq_proofs_unicity;
      intros u v; destruct u; destruct v; auto;
      try (right; intro Hpp; inversion Hpp).
    Qed.

    (** Any two proofs of [0 < x < p] are equal. *)
    Lemma uniqueness_zpstar_proof :
      forall x (Hx Hy : (0 < x < p)), Hx = Hy.
    Proof.
      intros ? [Hxl Hxr] [Hyl Hyr];
      f_equal; apply dec_lt_general.
    Qed.

    (** Decidable equality of [Z_p^*] elements, by comparing the integers.
        Closed with [Defined] so that it reduces and extracts. *)
    Lemma dec_zpstar : forall x y : Zpstar, {x = y} + {x <> y}.
    Proof.
      intros [x Hx] [y Hy].
      destruct (Z.eq_dec x y) as [Hl | Hr].
      left. subst. f_equal.
      apply uniqueness_zpstar_proof.
      right. intro H; inversion H;
      contradiction.
    Defined.

    (** Two elements with equal integer components are equal, whatever their
        range proofs. *)
    Lemma construct_zpstar :
      forall x y
      (Hx : 0 < x < p)
      (Hy : 0 < y < p),
      x = y ->
      mk_zpstar x Hx = mk_zpstar y Hy.
    Proof.
      intros; subst; f_equal.
      apply uniqueness_zpstar_proof.
    Qed.

    (** The identity element [1]. *)
    Definition one : Zpstar.
      refine (mk_zpstar 1 _).
      pose proof (prime_ge_2 _ Hp).
      abstract nia.
    Defined.

    (** Group multiplication: [(a, b) ↦ a · b mod p].  The result is nonzero
        because [p] is prime ([multiplication_bound] in [Util.v]). *)
    Definition mul_zpstar (u v : Zpstar) : Zpstar.
      refine(
        match u, v with
        | mk_zpstar au Hu, mk_zpstar av Hv =>
          mk_zpstar
            (Z.modulo (au * av) p)
            (@multiplication_bound p Hp _ _ Hu Hv)
        end).
    Defined.

    (** Fermat's little theorem for the executable exponentiation:
        [a^(p-1) mod p = 1] for [0 < a < p], computed with [Npow_mod]. *)
    Lemma fermat_theorem :
      forall au,
      0 < au < p ->
      Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 1)) (Z.to_N p)) = 1.
    Proof.
      intros ? Hau.
      rewrite zmod_nmod,
      !Z2N.id.
      rewrite fermat_little_ZZ;
      try nia; try assumption.
      all:try nia.
      rewrite !Z2N.id.
      exact Hp.
      nia.
    Qed.

    (** The Fermat inverse [a^(p-2) mod p], computed with [Npow_mod], lies in
        [{1, …, p-1}] when [0 < a < p]. *)
    Lemma mod_bound : forall au,
      0 < au < p ->
      0 < Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)) < p.
    Proof.
      intros ? Ha.
      rewrite zmod_nmod,
      !Z2N.id.
      apply fermat_bound.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.

    (** Group inverse: [a ↦ a^(p-2) mod p], computed by square-and-multiply on
        [N].  That it is an inverse is [zpstar_left_inv]. *)
    Definition inv_zpstar (u : Zpstar) : Zpstar.
      refine(
        match u with
        | mk_zpstar au Hu => mk_zpstar
            (Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)))
            (mod_bound _ Hu)
        end).
    Defined.

    (** Multiplication modulo [p] is associative. *)
    Lemma zpstar_mul_associative :
      forall x y z : Zpstar,
      mul_zpstar x (mul_zpstar y z) =
      mul_zpstar (mul_zpstar x y) z.
    Proof.
      pose proof @H_0_p p Hp.
      intros ? ? ?;
      destruct x as [x Hx];
      destruct y as [y Hy];
      destruct z as [z Hz];
      simpl in * |- *.
      eapply construct_zpstar.
      rewrite Z.mul_mod_idemp_l.
      rewrite Z.mul_mod_idemp_r.
      rewrite Z.mul_assoc.
      reflexivity.
      all:nia.
    Qed.

    (** [1 · x = x]. *)
    Lemma one_is_left_identity :
      forall x, mul_zpstar one x = x.
    Proof.
      intro x.
      unfold mul_zpstar, one.
      destruct x as [x Hx].
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_1_l.
      apply mod_not_zero_one.
      exact Hx.
    Qed.

    (** [x · 1 = x]. *)
    Lemma one_is_right_identity :
      forall x, mul_zpstar x one = x.
    Proof.
      intro x.
      unfold mul_zpstar, one.
      destruct x as [x Hx].
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_1_r.
      apply mod_not_zero_one.
      exact Hx.
    Qed.

    (** Multiplication modulo [p] is commutative. *)
    Lemma zpstar_mul_commutative :
      forall x y : Zpstar,
      mul_zpstar x y =  mul_zpstar y x.
    Proof.
      destruct x as [x Hx];
      destruct y as [y Hy]; simpl.
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_comm.
      reflexivity.
    Qed.

    (** [mul_zpstar] respects Leibniz equality (a trivial [Proper] instance
        required by the algebraic hierarchy). *)
    Global Instance zpstar_mul_proper :
      Proper (eq ==> eq ==> eq) mul_zpstar.
    Proof.
      intros x y Hxy z u Hzu.
      destruct x as [x Hx]; destruct y as [y Hy];
      destruct z as [z Hz]; destruct u as [u Hu]; simpl in * |- *.
      refine(construct_zpstar _ _ _ _ _).
      inversion Hxy; inversion Hzu; subst; reflexivity.
    Defined.

    (** Left inverse law: [a^(p-2) · a ≡ 1 (mod p)].  After converting
        [Npow_mod] to [Zpow_mod], the product is [a^(p-1) mod p], which is [1]
        by [fermat_little_ZZ]. *)
    Lemma zpstar_left_inv :
      forall x, mul_zpstar (inv_zpstar x) x = one.
    Proof.
      intros ?.
      unfold mul_zpstar, inv_zpstar, one.
      destruct x as (v & Hv).
      apply construct_zpstar.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia.
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp.
      rewrite Z.pow_add_r.
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp.
      exact Hv.
      nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.

    (** Right inverse law: [a · a^(p-2) ≡ 1 (mod p)], by the same argument. *)
    Lemma zpstar_right_inv :
      forall x, mul_zpstar x (inv_zpstar x) = one.
    Proof.
      intros ?.
      unfold mul_zpstar, inv_zpstar, one.
      destruct x as (v & Hv).
      apply construct_zpstar.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia.
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp.
      rewrite Z.pow_add_r.
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp.
      exact Hv.
      nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.

    (** [Z_p^*] with [mul_zpstar], [one] and [inv_zpstar] is a commutative group
        (with Leibniz equality). *)
    Global Instance zpstar_comm : @commutative_group
      Zpstar (@eq Zpstar) mul_zpstar one inv_zpstar.
    Proof.
      repeat econstructor.
      + unfold is_associative;
        intros ? ? ?.
        apply zpstar_mul_associative.
      + intro x. apply one_is_left_identity.
      + intro x. apply one_is_right_identity.
      + apply zpstar_mul_proper.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y z Hxy Hyz. rewrite Hxy. exact Hyz.
      + intro x. apply zpstar_left_inv.
      + intro x. apply zpstar_right_inv.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y. apply zpstar_mul_commutative.
    Qed.

  End ZpstarGroup.
End Zpgroup.

(** ** The prime field [Z_p] *)
Module Zpfield.

  (** The section is parameterised by a prime [p]. *)
  Section ZpField.

    Context
      {p : Z}
      {Hp : prime p}.

    (** An element of [Z_p]: an integer [v] in canonical form, witnessed by
        [v mod p = v] (equivalently [0 ≤ v < p], see [mod_more_gen_bound]).
        The canonical-form condition is an equation on [Z], so its proofs are
        unique ([zple_gen]). *)
    Record Zp :=
      mk_zp {v : Z; Hv : Z.modulo v p = v}.

    (** The additive identity [0]. *)
    Definition zero : Zp.
      refine (mk_zp 0 (Z.mod_0_l _ _)).
      pose proof prime_ge_2 _ Hp as Ht.
      abstract nia.
    Defined.

    (** The multiplicative identity [1] (canonical because [p ≥ 2]). *)
    Definition one : Zp.
      refine(mk_zp 1 (Z.mod_1_l _ _ )).
      pose proof prime_ge_2 _ Hp as Ht.
      abstract nia.
    Defined.

    (** Addition modulo [p]. *)
    Definition zp_add (x y : Zp) : Zp.
      refine (match x, y with
        | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax + ay) p) _
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.

    (** Subtraction modulo [p] ([Z.modulo] always returns a value in
        [{0, …, p-1}] for [p > 0]). *)
    Definition zp_sub (x y : Zp) : Zp.
      refine (match x, y with
      | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax - ay) p) _
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.

    (** Additive inverse, defined as [0 - x mod p]. *)
    Definition zp_opp (x : Zp) : Zp :=
      zp_sub zero x.

    (** Multiplication modulo [p]. *)
    Definition zp_mul (x y : Zp) : Zp.
      refine (match x, y with
        | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax * ay) p) _
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.

    (** Multiplicative inverse [x ↦ x^(p-2) mod p], computed with [Npow_mod].
        It is an inverse for [x ≠ 0] ([zp_mul_left_inv]); on [0] it returns
        [0^(p-2) mod p], which is [0] for [p > 2] and [1] for [p = 2]. *)
    Definition zp_inv (x : Zp) : Zp.
      refine (match x with
        | mk_zp ax Hu => mk_zp
          (Z.modulo
            (Z.of_N (Npow_mod (Z.to_N ax) (Z.to_N (p - 2)) (Z.to_N p)))
            p) _
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.

    (** Division [x / y = x · y⁻¹]. *)
    Definition zp_div (x y : Zp) : Zp :=
      zp_mul x (zp_inv y).

    (** Any two proofs of [v mod p = v] are equal (uniqueness of identity
        proofs on [Z]). *)
    Lemma zple_gen :
      forall v
      (H₁ H₂ : Z.modulo v p = v),
      H₁ = H₂.
    Proof.
      intros v ? ?.
      apply UIP_dec,
      Z.eq_dec.
    Qed.

    (** Two field elements with equal integer components are equal. *)
    Lemma construct_zp :
      forall x y
      (Hx : Z.modulo x p = x)
      (Hy : Z.modulo y p = y),
      x = y ->
      mk_zp x Hx = mk_zp y Hy.
    Proof.
      intros; subst; f_equal.
      apply zple_gen.
    Qed.

    (** Decidable equality on [Z_p], closed with [Defined] so that it computes. *)
    Lemma zp_dec: forall x y : Zp, {x = y} + {x <> y}.
    Proof.
      intros x y. destruct x as [x Hx]; destruct y as [y Hy]; simpl.
      destruct (Z.eq_dec x y) as [Hl | Hr]. left.
      refine(construct_zp _ _ _ _ Hl).
      right. intro H; inversion H; contradiction.
    Defined.

    (** [zp_opp x = zp_sub zero x] (true by definition). *)
    Lemma zp_opp_sub :
      forall x, zp_opp x = zp_sub zero x.
    Proof.
      intros [x Hx]; unfold zero, zp_opp, zp_sub; simpl.
      refine(construct_zp _ _ _ _ _); reflexivity.
    Qed.

    (** [x · y⁻¹ = x / y] (true by definition). *)
    Lemma zp_mul_inv_div :
    forall x y, zp_mul x (zp_inv y) = zp_div x y.
    Proof.
      intros [x Hx] [y Hy]; simpl.
      refine(construct_zp _ _ _ _ _).
      reflexivity.
    Qed.

    (** ** Field axioms

        Each axiom of [field] from [Algebra/Hierarchy.v] is proved separately by
        unfolding the operations and using the arithmetic of [mod]. *)

    (** Addition modulo [p] is associative. *)
    Lemma zp_add_assoc:
      forall x y z : Zp,
      zp_add x (zp_add y z) = zp_add (zp_add x y) z.
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.add_mod_idemp_l.
      rewrite Z.add_mod_idemp_r.
      rewrite Z.add_assoc.
      reflexivity.
      all:nia.
    Qed.

    (** [0 + x = x]. *)
    Lemma zp_add_zero_left_identity :
      forall x, zp_add zero x = x.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      exact Hx.
    Qed.

    (** [x + 0 = x]. *)
    Lemma zp_add_zero_right_identity :
      forall x, zp_add x zero = x.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.add_0_r.
      exact Hx.
    Qed.

    (** [zp_add] respects equality. *)
    Global Instance zp_add_proper : Proper (eq ==> eq ==> eq) zp_add.
    Proof.
      intros x y Hxy u v Huv; subst; reflexivity.
    Qed.

    (** Symmetry and transitivity of Leibniz equality on [Zp], packaged as
        instances for the hierarchy. *)
    Global Instance eq_sym : @Symmetric Zp eq.
    Proof.
      intros x y Hxy. subst; reflexivity.
    Qed.

    Global Instance eq_trans : @Transitive Zp eq.
    Proof.
      intros x y z Hxy Hyz; subst; reflexivity.
    Qed.

    (** [(-x) + x = 0]. *)
    Lemma zp_add_opp_left_inv :
      forall x, zp_add (zp_opp x) x = zero.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Zplus_mod_idemp_l.
      rewrite Z.add_opp_diag_l.
      rewrite Zmod_0_l; reflexivity.
    Qed.

    (** [x + (-x) = 0]. *)
    Lemma zp_add_opp_right_inv :
      forall x, zp_add x (zp_opp x) = zero.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Zplus_mod_idemp_r.
      rewrite Z.add_opp_diag_r.
      rewrite Zmod_0_l; reflexivity.
    Qed.

    (** [zp_opp] respects equality. *)
    Global Instance zp_opp_proper : Proper (eq ==> eq) zp_opp.
    Proof.
      intros x y Hx; subst; reflexivity.
    Qed.

    (** Addition is commutative. *)
    Lemma zp_add_comm :
      forall x y, zp_add x y = zp_add y x.
    Proof.
      intros [x Hx] [y Hy]; simpl;
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.add_comm; reflexivity.
    Qed.

    (** Multiplication is associative. *)
    Lemma zp_mul_assoc :
      forall x y z,
      zp_mul x (zp_mul y z) = zp_mul (zp_mul x y) z.
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz]; simpl;
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_mod_idemp_l.
      rewrite Z.mul_mod_idemp_r.
      rewrite Z.mul_assoc. reflexivity.
      all:nia.
    Qed.

    (** [1 · x = x]. *)
    Lemma zp_mul_one_left_id :
      forall x, zp_mul one x = x.
    Proof.
      intros [x Hx];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_1_l.
      exact Hx.
    Qed.

    (** [x · 1 = x]. *)
    Lemma zp_mul_one_right_id :
      forall x, zp_mul x one = x.
    Proof.
      intros [x Hx];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_1_r; exact Hx.
    Qed.

    (** [zp_mul] respects equality. *)
    Global Instance zp_mul_proper: Proper (eq ==> eq ==> eq) zp_mul.
    Proof.
      intros x y Hxy u v Huv; subst; reflexivity.
    Qed.

    (** Left distributivity: [x · (y + z) = x·y + x·z]. *)
    Lemma mul_dist_add_left :
      forall x y z,
      zp_mul x (zp_add y z) = zp_add (zp_mul x y) (zp_mul x z).
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_mod_idemp_r,
        Z.add_mod_idemp_l,
        Z.add_mod_idemp_r,
        Z.mul_add_distr_l;
        try reflexivity;
        try nia.
    Qed.

    (** Right distributivity: [(y + z) · x = y·x + z·x]. *)
    Lemma mul_dist_add_right :
      forall x y z,
      zp_mul (zp_add y z) x = zp_add (zp_mul y x) (zp_mul z x).
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_mod_idemp_l,
      Z.add_mod_idemp_r,  Z.mul_add_distr_r,
      Zplus_mod_idemp_l;
      try reflexivity; try nia.
    Qed.

    (** Subtraction is addition of the opposite: [x - y = x + (-y)]. *)
    Lemma zp_sub_add_opp :
      forall x y : Zp, zp_sub x y = zp_add x (zp_opp y).
    Proof.
      intros [x Hx] [y Hy]; simpl;
      refine (construct_zp  _ _ _ _ _).
      rewrite Zplus_mod_idemp_r, Z.add_opp_r;
      reflexivity.
    Qed.

    (** [zp_sub] respects equality. *)
    Global Instance zp_sub_proper : Proper (eq ==> eq ==> eq) zp_sub.
    Proof.
      intros x y Hxy u v Huv; subst; reflexivity.
    Qed.

    (** Distinct field elements have distinct integer components. *)
    Lemma zp_not_eq :
      forall x y : Zp,
      x <> y -> v x <> v y.
    Proof.
      intros [x Hx] [y Hy] Hpp;
      cbn.
      intro Hf.
      apply Hpp.
      refine (construct_zp  _ _ _ _ _).
      exact Hf.
    Qed.

    (** Multiplication is commutative. *)
    Lemma zp_mul_comm : forall x y, zp_mul x y = zp_mul y x.
    Proof.
      intros [x Hx] [y Hy];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_comm; reflexivity.
    Qed.

    (** Multiplicative inverse law: for [x ≠ 0], [x^(p-2) · x ≡ 1 (mod p)].
        As for [Z_p^*], the product is [x^(p-1) mod p], which is [1] by
        [fermat_little_ZZ]; the hypothesis [x ≠ 0] together with the canonical
        form gives [0 < x < p]. *)
    Lemma zp_mul_left_inv:
      forall x, x <> zero ->
      zp_mul (zp_inv x) x = one.
    Proof.
      intros x Hx.
      unfold zp_mul, zp_inv.
      destruct x as (v & Hv).
      apply construct_zp.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmod_mod.
      rewrite Zmult_mod_idemp_r.
      (* The product equals [x^(p-1) mod p]; reduce to Fermat's little theorem. *)
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia.
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp.
      rewrite Z.pow_add_r.
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp.
      (* Side condition of Fermat: [0 < x < p], from canonical form and [x ≠ 0]. *)
      unfold zero in Hx.
      pose proof (proj2 (@mod_more_gen_bound p Hp v) Hv) as Htt.
      assert (Hvnz : v <> 0).
      pose proof (zp_not_eq _ _ Hx) as Hppw.
      cbn in Hppw.
      exact Hppw.
      all:try nia.
      pose proof @Hp_2_p p Hp.
      nia.
      pose proof @Hp_2_p p Hp.
      nia.
      pose proof (proj2 (@mod_more_gen_bound p Hp v) Hv) as Htt.
      nia.
      rewrite Z2N.id.
      pose proof @Hp_2_p p Hp.
      nia.
      pose proof @Hp_2_p p Hp.
      nia.
      rewrite Z2N.id.
      exact Hp.
      pose proof @Hp_2_p p Hp.
      nia.
    Qed.

    (** [0 ≠ 1] in [Z_p]. *)
    Lemma zero_neq_one : zero <> one.
    Proof.
      intro Hx.
      unfold zero, one in Hx.
      inversion Hx.
    Qed.

    (** [zp_inv] and [zp_div] respect equality. *)
    Global Instance zp_inv_proper: Proper (eq ==> eq) zp_inv.
    Proof.
      intros x y Hxy; subst; reflexivity.
    Qed.

    Global Instance zp_div_proper : Proper (eq ==> eq ==> eq) zp_div.
    Proof.
      intros x y Hxy; subst; reflexivity.
    Qed.

    (** [Z_p] is a field: the axioms above assembled into an instance of
        [field] with Leibniz equality. *)
    Global Instance zp_field : @field Zp (@eq Zp) zero
      one zp_opp zp_add zp_sub zp_mul zp_inv zp_div.
    Proof.
      repeat constructor.
      + intros x y z. apply zp_add_assoc.
      + intro x. apply zp_add_zero_left_identity.
      + intro x. apply zp_add_zero_right_identity.
      + apply zp_add_proper.
      + apply eq_sym.
      + apply eq_trans.
      + intros x. apply zp_add_opp_left_inv.
      + intros x; apply zp_add_opp_right_inv.
      + apply zp_opp_proper.
      + intros x y; apply zp_add_comm.
      + intros x y z; apply zp_mul_assoc.
      + intro x; apply zp_mul_one_left_id.
      + intro x; apply zp_mul_one_right_id.
      + apply zp_mul_proper.
      + apply eq_sym.
      + apply eq_trans.
      + intros x y z; apply mul_dist_add_left.
      + intros x y z; apply mul_dist_add_right.
      + intros x y; apply zp_sub_add_opp.
      + apply zp_mul_proper.
      + apply zp_sub_proper.
      + intros x y. apply zp_mul_comm.
      + intros x y; apply zp_mul_left_inv; exact y.
      + exact zero_neq_one.
      + intros x y. symmetry. subst. exact eq_refl.
      + exact zp_div_proper.
    Qed.

  End ZpField.

End Zpfield.

(** ** Schnorr groups

    For primes [p] and [q] with [p = k·q + 1], the Schnorr group is the
    unique subgroup of order [q] of [Z_p^*].  It equals the set of [k]-th
    powers modulo [p], because [(w^k)^q = w^(p-1) ≡ 1]; here it is described
    directly by the condition [v^q ≡ 1 (mod p)].  This is the
    prime-order group used for discrete-log based protocols (Schnorr,
    Chaum–Pedersen, ElGamal, and so on). *)
Module Schnorr.

  (** Section parameters: the cofactor [k] and primes [p] and [q] with
      [p = k·q + 1].  The equation [Hk] is not needed by the group-law proofs
      themselves, but [abstract nia] captures the whole context, so some
      definitions (for example [inv_schnorr_group]) end up depending on it. *)
  Section SchnorrGroup.
    Context
      {k p q : Z}
      {Hk : p = k * q + 1}
      {Hp : prime p}
      {Hq : prime q}.

    (** An element of the Schnorr group: an integer [v] with [0 < v < p] and
        [v^q mod p = 1] (computed with [Zpow_mod]). *)
    Record Schnorr_group :=
      mk_schnorr
      {v : Z; Ha : 0 < v < p; Hb : (Zpow_mod v q p = 1)}.

    (** Decidable equality on [comparison], needed for uniqueness of proofs of
        [<] on [Z]. *)
    Lemma comparison_dec :
      ∀ x y : comparison, {x = y} + {x ≠ y}.
    Proof.
      intros x y.
      refine
        match x, y with
        | Eq, Eq
        | Lt, Lt
        | Gt, Gt => left eq_refl
        | _, _ => right _
        end.
        all: try (intro Hf; congruence).
    Defined.

    (** Any two proofs of [0 < v < p] are equal. *)
    Lemma uniqueness_of_schnorr_proof_first :
      forall v (Hx Hy : 0 < v < p),
      Hx = Hy.
    Proof.
      intros v [Hxa Hxb] [Hya Hyb];
      f_equal;
      apply UIP_dec,
      comparison_dec.
    Qed.

    (** Any two proofs of [Zpow_mod v q p = 1] are equal. *)
    Lemma uniqueness_of_schnorr_proof_second :
      forall v (Hx Hy : Zpow_mod v q p = 1),
      Hx = Hy.
    Proof.
      intros v Hx Hy;
      f_equal;
      apply UIP_dec, Z.eq_dec.
    Qed.

    (** Two Schnorr-group elements with equal integer components are equal. *)
    Lemma construct_schnorr_group :
      forall x y
      (Hxa : (0 < x < p))
      (Hxb : (Zpow_mod x q p = 1))
      (Hya : (0 < y < p))
      (Hyb : (Zpow_mod y q p = 1)),
      x = y ->
      mk_schnorr x Hxa Hxb = mk_schnorr y Hya Hyb.
    Proof.
      intros; subst; f_equal.
      apply uniqueness_of_schnorr_proof_first.
      apply uniqueness_of_schnorr_proof_second.
    Qed.

    (** Decidable equality on the Schnorr group (the name is inherited from the
        [Z_p^*] module).  Closed with [Defined] so that it computes. *)
    Lemma dec_zpstar :
      forall x y : Schnorr_group,
      {x = y} + {x <> y}.
    Proof.
      intros [x Hxa Hxb] [y Hya Hyb].
      destruct (Z.eq_dec x y) as [Hl | Hr].
      + left; subst.
        apply construct_schnorr_group;
        reflexivity.
      + right; subst.
        intros Hf.
        inversion Hf as (Hft).
        congruence.
    Defined.

    (** [0 < 1 < p]. *)
    Lemma one_mod_p : 0 < 1 < p.
    Proof.
      pose proof @Hp_2_p p Hp as Ha.
      nia.
    Qed.

    (** [1^q mod p = 1]. *)
    Lemma one_pow_mod_q : Zpow_mod 1 q p = 1.
    Proof.
      pose proof @Hp_2_p p Hp as Ha.
      pose proof @Hp_2_p q Hq as Hb.
      rewrite Zpow_mod_correct.
      rewrite Z.pow_1_l,
      Z.mod_1_l.
      + exact eq_refl.
      + abstract nia.
      + abstract nia.
      + abstract nia.
    Qed.

    (** The identity element [1]. *)
    Definition one : Schnorr_group.
      refine
        (mk_schnorr 1 one_mod_p one_pow_mod_q).
    Defined.

    (** Multiplication modulo [p].  The subgroup is closed under it since
        [(a·b)^q ≡ a^q · b^q ≡ 1 (mod p)]. *)
    Definition mul_schnorr_group
      (u v : Schnorr_group) : Schnorr_group.
      refine(
        match u, v with
        | mk_schnorr au Hua Hub,
          mk_schnorr av Hva Hvb =>
            mk_schnorr (Z.modulo (au * av) p)
            (@multiplication_bound p Hp au av Hua Hva)  _
        end).
        + pose proof @Hp_2_p p Hp.
          pose proof @Hp_2_p q Hq.
          rewrite Zpow_mod_correct in Hub, Hvb |- *.
          rewrite <-Zpower_mod,
          Zmult_power,
          Zmult_mod, Hub, Hvb,
          Z.mod_1_l;
          try reflexivity.
        all: try (abstract nia).
    Defined.

    (** The Fermat inverse [a^(p-2) mod p] lies in [{1, …, p-1}]. *)
    Lemma inv_schnorr_group_subproof_first :
      forall au,
      0 < au < p ->
      0 <
        Z.of_N
        (Npow_mod
          (Z.to_N au)
          (Z.to_N (p - 2))
          (Z.to_N p)) < p.
    Proof.
      intros ? Ha.
      rewrite zmod_nmod,
      !Z2N.id.
      apply fermat_bound.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.

    (** The Fermat inverse stays in the subgroup: if [a^q ≡ 1] then
        [(a^(p-2))^q = (a^q)^(p-2) ≡ 1 (mod p)]. *)
    Lemma inv_schnorr_group_subproof_second_aux :
      forall au,
      0 < au < p ->
      au ^ q mod p = 1 ->
      Z.of_N
      (Npow_mod
        (Z.to_N au)
        (Z.to_N (p - 2))
        (Z.to_N p)) ^ q mod p = 1.
    Proof.
      intros ? Hu Hv.
      pose proof @Hp_2_p p Hp as Ha.
      pose proof @Hp_2_p q Hq as Hb.
      rewrite zmod_nmod,
      Zpow_mod_correct,
      !Z2N.id,
      <-Zpower_mod,
      <-Z.pow_mul_r,
      Z.mul_comm,
      Z.pow_mul_r,
      Zpower_mod,
      Hv, Z.pow_1_l,
      Z.mod_1_l;
      try reflexivity.
      all: try (abstract nia).
      rewrite !Z2N.id.
      exact Hp.
      abstract nia.
    Qed.

    (** The same statement phrased with [Zpow_mod]. *)
    Lemma inv_schnorr_group_subproof_second :
      forall (au : Z), 0 < au < p -> Zpow_mod au q p = 1 ->
      Zpow_mod
      (Z.of_N (Npow_mod
        (Z.to_N au)
        (Z.to_N (p - 2))
        (Z.to_N p))) q p = 1.
    Proof.
      intros * ha hb.
      rewrite Zpow_mod_correct in hb |- *.
      eapply inv_schnorr_group_subproof_second_aux;
      try assumption.
      all:nia.
    Qed.

    (** Group inverse [a ↦ a^(p-2) mod p], computed with [Npow_mod]. *)
    Definition inv_schnorr_group (u : Schnorr_group) : Schnorr_group.
      refine(
        match u with
        | mk_schnorr au Hu Hv => mk_schnorr
            (Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)))
            (@inv_schnorr_group_subproof_first au Hu)
            (inv_schnorr_group_subproof_second au Hu Hv)
        end).
    Defined.

    (** Multiplication is associative. *)
    Lemma schnorr_mul_associative :
      forall x y z : Schnorr_group,
      mul_schnorr_group x (mul_schnorr_group y z) =
      mul_schnorr_group (mul_schnorr_group x y) z.
    Proof.
      pose proof @H_0_p p Hp.
      intros ? ? ?;
      destruct x as [x Hxa Hxb];
      destruct y as [y Hya Hyb];
      destruct z as [z Hza Hzb].
      refine (construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_mod_idemp_l,
      Z.mul_mod_idemp_r,
      Z.mul_assoc.
      reflexivity.
      all:nia.
    Qed.

    (** [1 · x = x]. *)
    Lemma one_is_left_identity :
      forall x, mul_schnorr_group one x = x.
    Proof.
      intros [x Hxa Hxb].
      unfold mul_schnorr_group, one.
      refine (construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_1_l.
      apply mod_not_zero_one.
      exact Hxa.
    Qed.

    (** [x · 1 = x]. *)
    Lemma one_is_right_identity :
      forall x, mul_schnorr_group x one = x.
    Proof.
      intros [x Hxa Hxb].
      unfold mul_schnorr_group, one.
      refine(construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_1_r.
      apply mod_not_zero_one.
      exact Hxa.
    Qed.

    (** Multiplication is commutative. *)
    Lemma schnorr_mul_commutative :
      forall x y : Schnorr_group,
      mul_schnorr_group x y =  mul_schnorr_group y x.
    Proof.
      destruct x as [x Hx];
      destruct y as [y Hy].
      refine(construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_comm.
      reflexivity.
    Qed.

    (** [mul_schnorr_group] respects equality. *)
    Global Instance schnorr_mul_proper :
      Proper (eq ==> eq ==> eq) mul_schnorr_group.
    Proof.
      intros x y Hxy z u Hzu.
      destruct x as [x Hx]; destruct y as [y Hy];
      destruct z as [z Hz]; destruct u as [u Hu].
      refine(construct_schnorr_group _ _ _ _ _ _ _).
      inversion Hxy; inversion Hzu; subst; reflexivity.
    Defined.

    (** Left inverse law [a^(p-2) · a ≡ 1 (mod p)], by Fermat's little theorem
        as in [Zpgroup.zpstar_left_inv]. *)
    Lemma schnorr_left_inv :
      forall x, mul_schnorr_group (inv_schnorr_group x) x = one.
    Proof.
      intros [x Hxa Hxb].
      unfold mul_schnorr_group,
      inv_schnorr_group, one.
      apply construct_schnorr_group.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia.
      assert (Ht : x * x ^ (p - 2) = x ^ (p - 1)).
      rewrite Hpp.
      rewrite Z.pow_add_r.
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp.
      exact Hxa.
      nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.

    (** Right inverse law, from the left one and commutativity. *)
    Lemma schnorr_right_inv :
      forall x, mul_schnorr_group x (inv_schnorr_group x) = one.
    Proof.
      intros ?.
      rewrite schnorr_mul_commutative.
      apply schnorr_left_inv.
    Qed.

    (** The Schnorr group is a commutative group. *)
    Global Instance schnorr_comm : @commutative_group
      Schnorr_group (@eq Schnorr_group)
      mul_schnorr_group one inv_schnorr_group.
    Proof.
      repeat econstructor.
      + unfold is_associative;
        intros ? ? ?.
        apply schnorr_mul_associative.
      + intro x. apply one_is_left_identity.
      + intro x. apply one_is_right_identity.
      + apply schnorr_mul_proper.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y z Hxy Hyz. rewrite Hxy. exact Hyz.
      + intro x. apply schnorr_left_inv.
      + intro x. apply schnorr_right_inv.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y. apply schnorr_mul_commutative.
    Qed.

  End SchnorrGroup.
End Schnorr.

(** ** The Schnorr group as a vector space over [Z_q]

    Scalars are elements of the field [Zpfield.Zp q] and vectors are
    elements of [Schnorr.Schnorr_group p q]; scalar multiplication is
    exponentiation [pow g x = g^x mod p].  Since every element has order
    dividing [q], exponents may be reduced modulo [q], which is what makes
    [g^(u·v mod q) = (g^u)^v] and [g^((u+v) mod q) = g^u · g^v] hold. *)
Module Vspace.

  (** The same parameters as the Schnorr-group section: [p = k·q + 1] with [p]
      and [q] prime. *)
  Section VectorSpace.

    Context
      {k p q : Z}
      {Hk : p = k * q + 1}
      {Hp : prime p}
      {Hq : prime q}.

    (** For [0 < a < p] and an exponent [y] in canonical form modulo [q],
        [a^y mod p] (computed with [Npow_mod]) lies in [{1, …, p-1}]. *)
    Lemma pow_subproof_first :
      forall au yt,
      0 < au < p ->
      yt mod q = yt ->
      0 <
        Z.of_N
        (Npow_mod
          (Z.to_N au)
          (Z.to_N yt)
          (Z.to_N p)) < p.
    Proof.
      intros ? ? Ha Hb.
      eapply mod_more_gen_bound in Hb.
      rewrite zmod_nmod,
      !Z2N.id.
      apply fermat_bound_gen.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
      Unshelve.
      exact Hq.
    Qed.

    (** Powers stay in the subgroup: if [a^q ≡ 1] then
        [(a^y)^q = (a^q)^y ≡ 1 (mod p)]. *)
    Lemma pow_subproof_second_aux :
      forall au yt,
      yt mod q = yt ->
      0 < au < p ->
      au ^ q mod p = 1 ->
      Z.of_N
      (Npow_mod
        (Z.to_N au)
        (Z.to_N yt)
        (Z.to_N p)) ^ q mod p = 1.
    Proof.
      intros ? ? Ht Hu Hv.
      eapply mod_more_gen_bound in Ht.
      pose proof @Hp_2_p p Hp as Ha.
      pose proof @Hp_2_p q Hq as Hb.
      rewrite zmod_nmod,
      Zpow_mod_correct,
      !Z2N.id,
      <-Zpower_mod,
      <-Z.pow_mul_r,
      Z.mul_comm,
      Z.pow_mul_r,
      Zpower_mod,
      Hv, Z.pow_1_l,
      Z.mod_1_l;
      try reflexivity.
      all: try (abstract nia).
      rewrite !Z2N.id.
      exact Hp.
      abstract nia.
      Unshelve.
      exact Hq.
    Qed.

     (** The same statement phrased with [Zpow_mod]. *)
     Lemma pow_subproof_second :
      forall au yt,
      yt mod q = yt ->
      0 < au < p ->
      Zpow_mod au q p = 1 ->
      Zpow_mod
      (Z.of_N (Npow_mod
        (Z.to_N au)
        (Z.to_N yt)
        (Z.to_N p))) q p = 1.
    Proof.
      intros * ha hb hc.
      rewrite Zpow_mod_correct in hc |- *.
      eapply pow_subproof_second_aux;
      try assumption.
      all:nia.
    Qed.

    (** Scalar multiplication: [pow g y = g^y mod p] for a group element [g] and
        a scalar [y ∈ Z_q], computed with square-and-multiply [Npow_mod]. *)
    Definition pow (g : @Schnorr.Schnorr_group p q)
      (y : @Zpfield.Zp q) : @Schnorr.Schnorr_group p q.
      refine
        match g, y with
        | Schnorr.mk_schnorr gt Hgta Hgtb, Zpfield.mk_zp yt Hyt =>
            Schnorr.mk_schnorr
                (Z.of_N (Npow_mod (Z.to_N gt) (Z.to_N yt) (Z.to_N p)))
                (pow_subproof_first gt yt Hgta Hyt)
                (pow_subproof_second _ _  Hyt Hgta Hgtb)
        end.
    Defined.

    (** [g^1 = g]. *)
    Lemma is_field_one_proof :
      forall (u : @Schnorr.Schnorr_group p q),
      pow u (@Zpfield.one q Hq) = u.
    Proof.
      intros [u Hu].
      unfold Zpfield.one, pow.
      apply Schnorr.construct_schnorr_group.
      cbn.
      rewrite <-!Z2N.inj_mod,
      Z2N.id.
      apply (@mod_more_gen_bound p Hp u);
      try assumption.
      all:try nia.
      assert (Hut : 0 <= u). nia.
      pose proof Z.mod_bound_pos u p Hut (@H_0_p p Hp).
      nia.
    Qed.

    (** [g^0 = 1]. *)
    Lemma is_field_zero_proof :
      forall (u : @Schnorr.Schnorr_group p q),
      pow u (@Zpfield.zero q Hq) = @Schnorr.one p q Hp Hq.
    Proof.
      intros [u Hu].
      apply Schnorr.construct_schnorr_group;
      cbn.
      exact eq_refl.
    Qed.

    (** Compatibility of scalar multiplication with field multiplication:
        [g^(u·v mod q) = (g^u)^v].  Write [u·v = k₁·q + w₁] with
        [w₁ = u·v mod q]; then [g^(u·v) = (g^q)^k₁ · g^w₁ ≡ g^w₁] since
        [g^q ≡ 1]. *)
    Lemma is_smul_associative_fmul_proof :
      forall
      (g : @Schnorr.Schnorr_group p q)
      (u v : @Zpfield.Zp q),
      pow g (Zpfield.zp_mul u v) = pow (pow g u) v.
    Proof.
      intros [g Hg] [u Hu] [v Hv].
      apply Schnorr.construct_schnorr_group.
      rewrite !zmod_nmod,
      !Z2N.id, !Zpow_mod_correct,
      <-Zpower_mod,
      <-Z.pow_mul_r.
      eapply mod_more_gen_bound in Hu, Hv.
      assert (Htt : 0 <= u * v) by nia.
      (* Euclidean division [u · v = k₁ · q + w₁] with [0 ≤ w₁ < q]. *)
      destruct (@mod_exists_pos q Hq (u * v) Htt) as
      [k₁ [w₁ [Hl [Hr Hw]]]].
      rewrite Hl.
      eapply mod_more_gen_bound in Hr.
      replace (k₁ * q + w₁) with
      (w₁ + k₁ * q).
      rewrite Z_mod_plus_full,
      Hr,
      Z.pow_add_r,
      Zmult_mod.
      replace (k₁ * q) with (q * k₁).
      rewrite Z.pow_mul_r.
      (* The factor [(g^q)^k₁] reduces to [1] because [g^q ≡ 1 (mod p)]. *)
      assert (Hvt : (g ^ q) ^ k₁ mod p =
        (g ^ q mod p) ^ k₁ mod p).
      rewrite Zpower_mod;
      try reflexivity.
      nia.
      rewrite Zpow_mod_correct in Hb.
      rewrite Hvt, Hb.
      rewrite Z.pow_1_l,
      Z.mod_1_l,
      Z.mul_1_r,
      Zmod_mod;
      try reflexivity.
      all: try nia.
      eapply mod_more_gen_bound in Hr;
      try nia.
      try (eapply mod_more_gen_bound in Hu;
      try nia).
      all : (eapply mod_more_gen_bound in Hv;
      try nia).
      eapply mod_more_gen_bound in Hu;
      try nia.
      rewrite Z2N.id.
      eapply mod_more_gen_bound in Hu.
      destruct Hu as [Hul Hur].
      pose proof fermat_bound_gen
        g u p Hp Hul Hg.
      nia.
      eapply mod_more_gen_bound in Hu;
      try nia.
      eapply Z_mod_nonneg_nonneg;
      try nia.
      eapply mod_more_gen_bound in Hu.
      try nia.
      all: rewrite Z2N.id;
        try nia; exact Hp.
      Unshelve.
      all: try (exact Hp); try (exact Hq).
    Qed.

    (** Distributivity over field addition: [g^((u+v) mod q) = g^u · g^v],
        by the same reduction of the exponent modulo [q]. *)
    Lemma is_smul_distributive_fadd_proof :
      forall
      (g : @Schnorr.Schnorr_group p q)
      (u v : @Zpfield.Zp q),
      pow g (Zpfield.zp_add u v) =
      @Schnorr.mul_schnorr_group p q Hp Hq (pow g u) (pow g v).
    Proof.
      intros [g Hg] [u Hu] [v Hv].
      apply Schnorr.construct_schnorr_group.
      rewrite !zmod_nmod,
      !Z2N.id, !Zpow_mod_correct,
      <-Zmult_mod,
      <-Z.pow_add_r.
      eapply mod_more_gen_bound in Hu, Hv.
      assert (Htt : 0 <= u +  v) by nia.
      (* Euclidean division [u + v = k₁ · q + w₁] with [0 ≤ w₁ < q]. *)
      destruct (@mod_exists_pos q Hq (u +  v) Htt) as
      [k₁ [w₁ [Hl [Hr Hw]]]].
      rewrite Hl.
      eapply mod_more_gen_bound in Hr.
      replace (k₁ * q + w₁) with
      (w₁ + k₁ * q).
      rewrite Z_mod_plus_full,
      Hr,
      Z.pow_add_r,
      Zmult_mod.
      replace (k₁ * q) with (q * k₁).
      rewrite Z.pow_mul_r.
      (* The factor [(g^q)^k₁] reduces to [1] because [g^q ≡ 1 (mod p)]. *)
      assert (Hvt : (g ^ q) ^ k₁ mod p =
        (g ^ q mod p) ^ k₁ mod p).
      rewrite Zpower_mod;
      try reflexivity.
      nia.
      rewrite Zpow_mod_correct in Hb.
      rewrite Hvt, Hb.
      rewrite Z.pow_1_l,
      Z.mod_1_l,
      Z.mul_1_r,
      Zmod_mod;
      try reflexivity.
      all: try nia.
      eapply mod_more_gen_bound in Hr;
      try nia.
      try (eapply mod_more_gen_bound in Hu;
      try nia).
      all : (eapply mod_more_gen_bound in Hv;
      try nia).
      eapply mod_more_gen_bound in Hu;
      try nia.
      all: eapply mod_more_gen_bound in Hu, Hv; try nia.
      all: try rewrite Z2N.id;
        try nia; try (exact Hp).
      eapply mod_more_gen_bound in Hu, Hv;
      eapply Z_mod_nonneg_nonneg;
      try nia.
      eapply mod_more_gen_bound in Hu.
      nia.
      Unshelve.
      all: try (exact Hp); try (exact Hq).
    Qed.

    (** Distributivity over group multiplication: [(u·v)^r = u^r · v^r]
        modulo [p]. *)
    Lemma is_smul_distributive_vadd_proof :
      forall
      (u v : @Schnorr.Schnorr_group p q)
      (r : @Zpfield.Zp q),
      pow (@Schnorr.mul_schnorr_group p q Hp Hq u v) r =
      @Schnorr.mul_schnorr_group p q Hp Hq (pow u r) (pow v r).
    Proof.
      intros [u Hua Hub] [v Hva Hvb] [r Hr].
      apply Schnorr.construct_schnorr_group.
      rewrite !zmod_nmod,
      !Z2N.id, !Zpow_mod_correct,
      <-Zpower_mod,
      Z.pow_mul_l,
      Zmult_mod;
      try reflexivity.
      all: try nia.
      eapply mod_more_gen_bound in Hr.
      try nia.
      pose proof @multiplication_bound p Hp u v Hua Hva.
      try nia.
      all: rewrite Z2N.id;
      [exact Hp | nia].
      Unshelve.
      exact Hq.
    Qed.

    (** The Schnorr group with exponentiation is a vector space over [Z_q]:
        the group axioms come from [Schnorr.schnorr_comm], the field axioms from
        [Zpfield.zp_field] and the action axioms from the four lemmas above. *)
    Global Instance pow_vspace :
      @vector_space
        (@Zpfield.Zp q)
        (@eq (@Zpfield.Zp q))
        (@Zpfield.zero q Hq)
        (@Zpfield.one q Hq)
        (@Zpfield.zp_add q)
        (@Zpfield.zp_mul q)
        (@Zpfield.zp_sub q)
        (@Zpfield.zp_div q)
        (@Zpfield.zp_opp q Hq)
        (@Zpfield.zp_inv q)
        (@Schnorr.Schnorr_group p q)
        (@eq (@Schnorr.Schnorr_group p q))
        (@Schnorr.one p q Hp Hq)
        (@Schnorr.inv_schnorr_group k p q Hk Hp Hq)
        (@Schnorr.mul_schnorr_group p q Hp Hq)
        pow.
    Proof.
      econstructor.
      + apply Schnorr.schnorr_comm.
      + apply Zpfield.zp_field.
      + intros ?; apply is_field_one_proof.
      + intros ?; apply is_field_zero_proof.
      + intros ? ? ?;
        apply is_smul_associative_fmul_proof.
      + intros ? ? ?;
        apply is_smul_distributive_fadd_proof.
      + intros ? ? ?;
        apply is_smul_distributive_vadd_proof.
      + intros x y Heq u v Huv.
        subst. reflexivity.
    Qed.

  End VectorSpace.
End Vspace.
