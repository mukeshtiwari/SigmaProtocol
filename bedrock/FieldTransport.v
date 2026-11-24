(** Transport of the Edwards extended-coordinate operations along the field
    isomorphism between SigmaProtocol's coordinates [Zmod p] (vendored
    fiat-crypto, root [Fiat], standard-library [Zmod]) and AUCurves'
    [F p = {z | z = z mod p}] (fiat-crypto at root [Crypto]). *)

From Stdlib Require Import ZArith Zmod Lia.
From Curve Require Ed25519.
Require Fiat.Spec.Curve25519 Fiat.Curves.Edwards.XYZT.Basic
        Fiat.Arithmetic.PrimeFieldTheorems.
Require Crypto.Spec.ModularArithmetic Crypto.Arithmetic.ModularArithmeticTheorems
        Crypto.Arithmetic.PrimeFieldTheorems Crypto.Spec.Curve25519
        Crypto.Spec.CompleteEdwardsCurve Crypto.Curves.Edwards.XYZT.Basic
        Crypto.Curves.Edwards.XYZT.Readdition Crypto.Algebra.Hierarchy Crypto.Algebra.Ring Crypto.Algebra.Field
        Crypto.Util.Decidable.

Module SP := Curve.Ed25519.Ed25519.Ed.
Module SC := Fiat.Spec.Curve25519.
Module SX := Fiat.Curves.Edwards.XYZT.Basic.Extended.
Module AF := Crypto.Spec.ModularArithmetic.F.
Module AFT := Crypto.Arithmetic.ModularArithmeticTheorems.F.
Module APF := Crypto.Arithmetic.PrimeFieldTheorems.F.
Module AC := Crypto.Spec.Curve25519.
Module AX := Crypto.Curves.Edwards.XYZT.Basic.Extended.
Module AE := Crypto.Spec.CompleteEdwardsCurve.E.
Module AR := Crypto.Curves.Edwards.XYZT.Readdition.

Local Open Scope Z_scope.

(** The two moduli: [SC.p] is the integer [2^255 - 19], [AC.p] the
    positive [2^255 - 19]. *)
Notation Zp := (Zmod SC.p).
Notation Fp := (AF.F AC.p).

Lemma p_eq : Z.pos AC.p = SC.p.
Proof. reflexivity. Qed.

(** ** The coordinate map *)

Definition phi (x : Zp) : Fp := AF.of_Z AC.p (Zmod.unsigned x).

Lemma of_Z_modp z : AF.of_Z AC.p (z mod SC.p) = AF.of_Z AC.p z.
Proof. change SC.p with (Z.pos AC.p). symmetry; apply AFT.of_Z_mod. Qed.

Lemma phi_of_Z z : phi (Zmod.of_Z SC.p z) = AF.of_Z AC.p z.
Proof. unfold phi; rewrite Zmod.unsigned_of_Z; apply of_Z_modp. Qed.

Lemma phi_zero : phi Zmod.zero = AF.zero.
Proof. unfold phi; rewrite Zmod.unsigned_0; reflexivity. Qed.

Lemma phi_one : phi Zmod.one = AF.one.
Proof. unfold phi; rewrite Zmod.unsigned_1, of_Z_modp; reflexivity. Qed.

Lemma phi_add x y : phi (Zmod.add x y) = AF.add (phi x) (phi y).
Proof. unfold phi; rewrite Zmod.unsigned_add, of_Z_modp; apply AFT.of_Z_add. Qed.

Lemma phi_sub x y : phi (Zmod.sub x y) = AF.sub (phi x) (phi y).
Proof. unfold phi; rewrite Zmod.unsigned_sub, of_Z_modp; apply AFT.of_Z_sub. Qed.

Lemma phi_mul x y : phi (Zmod.mul x y) = AF.mul (phi x) (phi y).
Proof. unfold phi; rewrite Zmod.unsigned_mul, of_Z_modp; apply AFT.of_Z_mul. Qed.

Lemma phi_opp x : phi (Zmod.opp x) = AF.opp (phi x).
Proof. unfold phi; rewrite Zmod.unsigned_opp, of_Z_modp; apply AFT.of_Z_opp. Qed.

Lemma phi_inj x y : phi x = phi y -> x = y.
Proof.
  unfold phi; intro h; apply (f_equal AF.to_Z) in h.
  rewrite !AFT.to_Z_of_Z in h; change (Z.pos AC.p) with SC.p in h.
  rewrite !Zmod.mod_unsigned in h; apply Zmod.unsigned_inj; exact h.
Qed.

(** The inverse of [phi]. *)
Definition psi (x : Fp) : Zp := Zmod.of_Z SC.p (AF.to_Z x).

Lemma phi_psi x : phi (psi x) = x.
Proof. unfold psi; rewrite phi_of_Z; apply AFT.of_Z_to_Z. Qed.

Lemma phi_nonzero x : x <> Zmod.zero -> phi x <> AF.zero.
Proof. intros hx h; apply hx, phi_inj; rewrite h, phi_zero; reflexivity. Qed.

Lemma Zinv_zero : Zmod.inv (Zmod.zero : Zp) = Zmod.zero.
Proof. apply Zmod.unsigned_inj; vm_compute; reflexivity. Qed.

Lemma phi_inv x : phi (Zmod.inv x) = AF.inv (phi x).
Proof.
  destruct (SP.Fp_dec x Zmod.zero) as [-> | hx].
  - rewrite Zinv_zero, phi_zero, (APF.inv_0 AC.p); reflexivity.
  - apply (@Crypto.Algebra.Field.left_inv_unique _ _ _ _ _ _ _ _ _ _ AC.field).
    rewrite <-phi_mul, (@Fiat.Arithmetic.PrimeFieldTheorems.Zmod.inv_nonzero SC.p SC.prime_p x hx).
    apply phi_one.
Qed.

Lemma phi_mdiv x y : phi (Zmod.mdiv x y) = AF.div (phi x) (phi y).
Proof. unfold Zmod.mdiv, AF.div; rewrite phi_mul, phi_inv; reflexivity. Qed.

(** The curve constants correspond. *)
Lemma phi_a : phi SC.E.a = AC.E.a.
Proof. unfold SC.E.a, AC.E.a; rewrite phi_opp, phi_one; reflexivity. Qed.

Lemma phi_d : phi SC.E.d = AC.E.d.
Proof. unfold SC.E.d, AC.E.d; rewrite phi_mdiv, phi_opp, !phi_of_Z; reflexivity. Qed.

Lemma phi_twice_d : phi SP.twice_d = AF.add AC.E.d AC.E.d.
Proof. unfold SP.twice_d; rewrite phi_add, phi_d; reflexivity. Qed.

#[local] Hint Rewrite phi_add phi_sub phi_mul phi_opp phi_one phi_zero phi_inv
  phi_a phi_d phi_psi : phi.

(** ** Maps on coordinate tuples and points *)

Definition phi2 (c : Zp * Zp) : Fp * Fp := let '(x, y) := c in (phi x, phi y).

Definition phi5 (c : Zp * Zp * Zp * Zp * Zp) : Fp * Fp * Fp * Fp * Fp :=
  let '(X, Y, Z, Ta, Tb) := c in (phi X, phi Y, phi Z, phi Ta, phi Tb).

(** Cached coordinates [(half_YmX, half_YpX, Z, Td)] of [Readdition]. *)
Definition phi4 (c : Zp * Zp * Zp * Zp) : Fp * Fp * Fp * Fp :=
  let '(hm, hp, Z, Td) := c in (phi hm, phi hp, phi Z, phi Td).

Definition psi5 (c : Fp * Fp * Fp * Fp * Fp) : Zp * Zp * Zp * Zp * Zp :=
  let '(X, Y, Z, Ta, Tb) := c in (psi X, psi Y, psi Z, psi Ta, psi Tb).

Lemma phi5_psi5 c : phi5 (psi5 c) = c.
Proof. destruct c as [[[[X Y] Z] Ta] Tb]; cbn [phi5 psi5]; rewrite !phi_psi; reflexivity. Qed.

(** AUCurves' affine and extended point types over [F p]. *)
Notation Apoint := (@AE.point Fp eq AF.one AF.add AF.mul AC.E.a AC.E.d).
Notation Axpoint := (@AX.point Fp eq AF.zero AF.add AF.mul AC.E.a AC.E.d).

Definition phiA (P : SP.point) : Apoint.
Proof.
  refine (exist _ (phi2 (proj1_sig P)) _).
  destruct P as [[x y] h]; cbn in h |- *.
  apply (f_equal phi) in h; autorewrite with phi in h; exact h.
Defined.

Definition phiX (P : SP.xpoint) : Axpoint.
Proof.
  refine (exist _ (phi5 (proj1_sig P)) _).
  destruct P as [[[[[X Y] Z] Ta] Tb] (h1 & h2 & h3)]; cbn in h1, h2, h3 |- *.
  apply (f_equal phi) in h1, h2; autorewrite with phi in h1, h2.
  split; [exact h1 | split; [exact h2 | apply phi_nonzero; exact h3]].
Defined.

(** The phi-preimage of an AUCurves extended point. *)
Definition psiX (Q : Axpoint) : SP.xpoint.
Proof.
  refine (exist _ (psi5 (proj1_sig Q)) _).
  destruct Q as [[[[[X Y] Z] Ta] Tb] (h1 & h2 & h3)]; cbn [psi5 proj1_sig] in h1, h2, h3 |- *.
  split; [| split].
  - apply phi_inj; autorewrite with phi; exact h1.
  - apply phi_inj; autorewrite with phi; exact h2.
  - intro hz; apply h3; rewrite <-(phi_psi Z), hz; apply phi_zero.
Defined.

Lemma phiX_psiX Q : proj1_sig (phiX (psiX Q)) = proj1_sig Q.
Proof. exact (phi5_psi5 (proj1_sig Q)). Qed.

(** Projective equality of extended points in the two libraries. *)
Notation SXeq := (@SX.eq Zp eq Zmod.zero Zmod.add Zmod.mul SC.E.a SC.E.d).
Notation AXeq := (@AX.eq Fp eq AF.zero AF.add AF.mul AC.E.a AC.E.d).

Lemma SXeq_of_AXeq (R S : SP.xpoint) : AXeq (phiX R) (phiX S) -> SXeq R S.
Proof.
  destruct R as [[[[[X1 Y1] Z1] Ta1] Tb1] h1], S as [[[[[X2 Y2] Z2] Ta2] Tb2] h2].
  cbv [AX.eq SX.eq phiX phi5 proj1_sig]; intros [e1 e2].
  rewrite <-!phi_mul in e1, e2; split; apply phi_inj; assumption.
Qed.

(** [AX.eq] depends on the coordinates only. *)
Lemma AXeq_coords (P1 P1' P2 P2' : Axpoint) :
  proj1_sig P1 = proj1_sig P1' -> proj1_sig P2 = proj1_sig P2' ->
  AXeq P1 P2 -> AXeq P1' P2'.
Proof.
  destruct P1 as [c1 h1], P1' as [c1' h1'], P2 as [c2 h2], P2' as [c2' h2'].
  cbn [proj1_sig]; intros e1 e2; subst; exact (fun h => h).
Qed.

(** SigmaProtocol's [to_affine] is invariant under projective equality. *)
Lemma SXeq_to_affine (R S : SP.xpoint) : SXeq R S -> SP.to_affine R = SP.to_affine S.
Proof. intro h; apply SP.peq_leibniz; exact (SX.Proper_to_affine R S h). Qed.

Lemma phiA_coords P : proj1_sig (phiA P) = phi2 (proj1_sig P).
Proof. reflexivity. Qed.
Lemma phiX_coords P : proj1_sig (phiX P) = phi5 (proj1_sig P).
Proof. reflexivity. Qed.

(** ** Commutation with the Edwards operations

    Stated for every choice of AUCurves' instance arguments (field
    structure, characteristic, decidability, the curve side conditions,
    [twice_d] with its defining equation), so that the lemmas apply to the
    instances fixed in AUCurves' [Ed25519XYZT64] module. *)

Section Transport.
  Context {fld : @Crypto.Algebra.Hierarchy.field Fp eq AF.zero AF.one AF.opp AF.add AF.sub
                   AF.mul AF.inv AF.div}
          {c3 : @Crypto.Algebra.Ring.char_ge Fp eq AF.zero AF.one AF.opp AF.add AF.sub AF.mul
                  (BinNat.N.succ_pos BinNat.N.two)}
          {dec : Crypto.Util.Decidable.DecidableRel (@eq Fp)}
          {nza : AC.E.a <> AF.zero}
          {sqa : exists s, AF.mul s s = AC.E.a}
          {nsd : forall x, AF.mul x x <> AC.E.d}
          {am1 : AC.E.a = AF.opp AF.one}
          {td : Fp} {k2d : td = AF.add AC.E.d AC.E.d}
          {nzd : AC.E.d <> AF.zero}.

  Local Notation Am1double :=
    (AX.m1double (field:=fld) (char_ge_3:=c3) (Feq_dec:=dec) (a:=AC.E.a) (d:=AC.E.d)
       (nonzero_a:=nza) (square_a:=sqa) (nonsquare_d:=nsd)
       (a_eq_minus1:=am1) (twice_d:=td) (k_eq_2d:=k2d)).
  Local Notation Am1add :=
    (AX.m1add (field:=fld) (char_ge_3:=c3) (Feq_dec:=dec) (a:=AC.E.a) (d:=AC.E.d)
       (nonzero_a:=nza) (square_a:=sqa) (nonsquare_d:=nsd)
       (a_eq_minus1:=am1) (twice_d:=td) (k_eq_2d:=k2d)).
  Local Notation Afrom_affine :=
    (AX.from_affine (field:=fld) (Feq_dec:=dec) (a:=AC.E.a) (d:=AC.E.d)
       (nonzero_a:=nza)).
  Local Notation Ato_affine :=
    (AX.to_affine (field:=fld) (Feq_dec:=dec) (a:=AC.E.a) (d:=AC.E.d)
       (nonzero_a:=nza)).
  (** The coordinate formulas of [m1add], [m1double], [from_affine] and
      [to_affine], generic in the field operations. Both fiat-crypto copies
      define their operations by these formulas (the [*_coords] lemmas
      below hold by [reflexivity]). *)
  Definition m1add_coords {T} (add sub mul : T -> T -> T) (k : T)
    (c1 c2 : T * T * T * T * T) : T * T * T * T * T :=
    let '(X1, Y1, Z1, Ta1, Tb1) := c1 in
    let '(X2, Y2, Z2, Ta2, Tb2) := c2 in
    let A := mul (sub Y1 X1) (sub Y2 X2) in
    let B := mul (add Y1 X1) (add Y2 X2) in
    let C := mul (mul (mul Ta1 Tb1) k) (mul Ta2 Tb2) in
    let D := mul Z1 (add Z2 Z2) in
    let E := sub B A in let F := sub D C in let G := add D C in let H := add B A in
    (mul E F, mul G H, mul F G, E, H).

  Definition m1double_coords {T} (add sub mul : T -> T -> T)
    (c : T * T * T * T * T) : T * T * T * T * T :=
    let '(X, Y, Z, _, _) := c in
    let trX := mul X X in
    let trZ := mul Y Y in
    let trT := (let t0 := mul Z Z in add t0 t0) in
    let rY := add X Y in
    let t0 := mul rY rY in
    let cY := add trZ trX in
    let cZ := sub trZ trX in
    let cX := sub t0 cY in
    let cT := sub trT cZ in
    (mul cX cT, mul cY cZ, mul cZ cT, cX, cY).

  Definition from_affine_coords {T} (one : T) (c : T * T) : T * T * T * T * T :=
    let '(x, y) := c in (x, y, one, x, y).

  Definition to_affine_coords {T} (mul : T -> T -> T) (inv : T -> T)
    (c : T * T * T * T * T) : T * T :=
    let '(X, Y, Z, Ta, Tb) := c in let iZ := inv Z in (mul X iZ, mul Y iZ).

  Lemma SP_xadd_coords (P1 P2 : SP.xpoint) :
    proj1_sig (SP.xadd P1 P2) =
    m1add_coords Zmod.add Zmod.sub Zmod.mul SP.twice_d (proj1_sig P1) (proj1_sig P2).
  Proof.
    destruct P1 as [[[[[X1 Y1] Z1] Ta1] Tb1] hP1], P2 as [[[[[X2 Y2] Z2] Ta2] Tb2] hP2].
    reflexivity.
  Qed.
  Lemma A_m1add_coords (Q1 Q2 : Axpoint) :
    proj1_sig (Am1add Q1 Q2) =
    m1add_coords AF.add AF.sub AF.mul td (proj1_sig Q1) (proj1_sig Q2).
  Proof.
    destruct Q1 as [[[[[X1 Y1] Z1] Ta1] Tb1] hQ1], Q2 as [[[[[X2 Y2] Z2] Ta2] Tb2] hQ2].
    reflexivity.
  Qed.
  Lemma SP_xdouble_coords (P : SP.xpoint) :
    proj1_sig (SP.xdouble P) = m1double_coords Zmod.add Zmod.sub Zmod.mul (proj1_sig P).
  Proof. destruct P as [[[[[X Y] Z] Ta] Tb] hP]; reflexivity. Qed.
  Lemma A_m1double_coords (Q : Axpoint) :
    proj1_sig (Am1double Q) = m1double_coords AF.add AF.sub AF.mul (proj1_sig Q).
  Proof. destruct Q as [[[[[X Y] Z] Ta] Tb] hQ]; reflexivity. Qed.
  Lemma SP_from_affine_coords (P : SP.point) :
    proj1_sig (SP.from_affine P) = from_affine_coords Zmod.one (proj1_sig P).
  Proof. destruct P as [[x y] hP]; reflexivity. Qed.
  Lemma A_from_affine_coords (Q : Apoint) :
    proj1_sig (Afrom_affine Q) = from_affine_coords AF.one (proj1_sig Q).
  Proof. destruct Q as [[x y] hQ]; reflexivity. Qed.
  Lemma SP_to_affine_coords (P : SP.xpoint) :
    proj1_sig (SP.to_affine P) = to_affine_coords Zmod.mul Zmod.inv (proj1_sig P).
  Proof. destruct P as [[[[[X Y] Z] Ta] Tb] hP]; reflexivity. Qed.
  Lemma A_to_affine_coords (Q : Axpoint) :
    proj1_sig (Ato_affine Q) = to_affine_coords AF.mul AF.inv (proj1_sig Q).
  Proof. destruct Q as [[[[[X Y] Z] Ta] Tb] hQ]; reflexivity. Qed.

  (** [phi] commutes with the coordinate formulas. *)
  Lemma m1add_coords_phi c1 c2 :
    phi5 (m1add_coords Zmod.add Zmod.sub Zmod.mul SP.twice_d c1 c2) =
    m1add_coords AF.add AF.sub AF.mul (AF.add AC.E.d AC.E.d) (phi5 c1) (phi5 c2).
  Proof.
    destruct c1 as [[[[X1 Y1] Z1] Ta1] Tb1], c2 as [[[[X2 Y2] Z2] Ta2] Tb2].
    cbv beta iota zeta delta [m1add_coords phi5].
    autorewrite with phi; rewrite phi_twice_d; reflexivity.
  Qed.
  Lemma m1double_coords_phi c :
    phi5 (m1double_coords Zmod.add Zmod.sub Zmod.mul c) =
    m1double_coords AF.add AF.sub AF.mul (phi5 c).
  Proof.
    destruct c as [[[[X Y] Z] Ta] Tb].
    cbv beta iota zeta delta [m1double_coords phi5].
    autorewrite with phi; reflexivity.
  Qed.
  Lemma from_affine_coords_phi c :
    phi5 (from_affine_coords Zmod.one c) = from_affine_coords AF.one (phi2 c).
  Proof.
    destruct c as [x y]; cbv beta iota zeta delta [from_affine_coords phi5 phi2].
    rewrite phi_one; reflexivity.
  Qed.
  Lemma to_affine_coords_phi c :
    phi2 (to_affine_coords Zmod.mul Zmod.inv c) = to_affine_coords AF.mul AF.inv (phi5 c).
  Proof.
    destruct c as [[[[X Y] Z] Ta] Tb].
    cbv beta iota zeta delta [to_affine_coords phi5 phi2].
    autorewrite with phi; reflexivity.
  Qed.

  (** ** Transport lemmas *)
  Lemma m1double_transport (P : SP.xpoint) (Q : Axpoint) :
    proj1_sig Q = phi5 (proj1_sig P) ->
    proj1_sig (Am1double Q) = phi5 (proj1_sig (SP.xdouble P)).
  Proof.
    intro h; rewrite A_m1double_coords, SP_xdouble_coords, h, m1double_coords_phi.
    reflexivity.
  Qed.

  Lemma m1add_transport (P1 P2 : SP.xpoint) (Q1 Q2 : Axpoint) :
    proj1_sig Q1 = phi5 (proj1_sig P1) ->
    proj1_sig Q2 = phi5 (proj1_sig P2) ->
    proj1_sig (Am1add Q1 Q2) = phi5 (proj1_sig (SP.xadd P1 P2)).
  Proof.
    intros h1 h2; rewrite A_m1add_coords, SP_xadd_coords, h1, h2, m1add_coords_phi, k2d.
    reflexivity.
  Qed.

  Lemma from_affine_transport (P : SP.point) (Q : Apoint) :
    proj1_sig Q = phi2 (proj1_sig P) ->
    proj1_sig (Afrom_affine Q) = phi5 (proj1_sig (SP.from_affine P)).
  Proof.
    intro h; rewrite A_from_affine_coords, SP_from_affine_coords, h, from_affine_coords_phi.
    reflexivity.
  Qed.

  Lemma to_affine_transport (P : SP.xpoint) (Q : Axpoint) :
    proj1_sig Q = phi5 (proj1_sig P) ->
    proj1_sig (Ato_affine Q) = phi2 (proj1_sig (SP.to_affine P)).
  Proof.
    intro h; rewrite A_to_affine_coords, SP_to_affine_coords, h, to_affine_coords_phi.
    reflexivity.
  Qed.

  (** The same statements through the point maps [phiX] and [phiA]. *)
  Corollary m1double_phiX P :
    proj1_sig (Am1double (phiX P)) = proj1_sig (phiX (SP.xdouble P)).
  Proof. apply m1double_transport; reflexivity. Qed.
  Corollary m1add_phiX P1 P2 :
    proj1_sig (Am1add (phiX P1) (phiX P2)) = proj1_sig (phiX (SP.xadd P1 P2)).
  Proof. apply m1add_transport; reflexivity. Qed.
  Corollary from_affine_phiA P :
    proj1_sig (Afrom_affine (phiA P)) = proj1_sig (phiX (SP.from_affine P)).
  Proof. apply from_affine_transport; reflexivity. Qed.
  Corollary to_affine_phiX P :
    proj1_sig (Ato_affine (phiX P)) = proj1_sig (phiA (SP.to_affine P)).
  Proof. apply to_affine_transport; reflexivity. Qed.

  (** ** Readdition

      AUCurves' addition is [m1_readd P (m1_prep Q)] ([Readdition]), which
      [readd_correct] relates to [m1add P Q] up to projective equality.
      SigmaProtocol's vendored fiat-crypto has no [Readdition]; the cached
      coordinates of a SigmaProtocol point are given by [prep_coords]. *)
  Local Notation Acached :=
    (@AR.cached Fp eq AF.zero AF.add AF.sub AF.mul AF.div AC.E.a AC.E.d).
  Local Notation Am1_prep :=
    (AR.m1_prep (field:=fld) (char_ge_3:=c3) (Feq_dec:=dec) (a:=AC.E.a) (d:=AC.E.d)
       (nonzero_a:=nza) (a_eq_minus1:=am1) (twice_d:=td) (k_eq_2d:=k2d) (nonzero_d:=nzd)).
  Local Notation Am1_readd :=
    (AR.m1_readd (field:=fld) (char_ge_3:=c3) (Feq_dec:=dec) (a:=AC.E.a) (d:=AC.E.d)
       (nonzero_a:=nza) (square_a:=sqa) (nonsquare_d:=nsd)
       (a_eq_minus1:=am1) (twice_d:=td) (k_eq_2d:=k2d) (nonzero_d:=nzd)).

  Definition prep_coords {T} (add sub mul div : T -> T -> T) (one d : T)
    (c : T * T * T * T * T) : T * T * T * T :=
    let '(X, Y, Z, Ta, Tb) := c in
    (div (sub Y X) (add one one), div (add Y X) (add one one), Z, mul (mul Ta Tb) d).

  Definition readd_coords {T} (add sub mul : T -> T -> T)
    (c1 : T * T * T * T * T) (c2 : T * T * T * T) : T * T * T * T * T :=
    let '(X1, Y1, Z1, Ta1, Tb1) := c1 in
    let '(hYmX, hYpX, Z2, Td) := c2 in
    let A := mul (sub Y1 X1) hYmX in
    let B := mul (add Y1 X1) hYpX in
    let C := mul (mul Ta1 Tb1) Td in
    let D := mul Z1 Z2 in
    let E := sub B A in let F := sub D C in let G := add D C in let H := add B A in
    (mul E F, mul G H, mul F G, E, H).

  Lemma A_m1_prep_coords (Q : Axpoint) :
    proj1_sig (Am1_prep Q) =
    prep_coords AF.add AF.sub AF.mul AF.div AF.one AC.E.d (proj1_sig Q).
  Proof. destruct Q as [[[[[X Y] Z] Ta] Tb] hQ]; reflexivity. Qed.
  Lemma A_m1_readd_coords (Q : Axpoint) (C : Acached) :
    proj1_sig (Am1_readd Q C) = readd_coords AF.add AF.sub AF.mul (proj1_sig Q) (proj1_sig C).
  Proof.
    destruct Q as [[[[[X Y] Z] Ta] Tb] hQ], C as [[[[hm hp] Z2] Td] hC]; reflexivity.
  Qed.

  Lemma prep_coords_phi c :
    phi4 (prep_coords Zmod.add Zmod.sub Zmod.mul Zmod.mdiv Zmod.one SC.E.d c) =
    prep_coords AF.add AF.sub AF.mul AF.div AF.one AC.E.d (phi5 c).
  Proof.
    destruct c as [[[[X Y] Z] Ta] Tb].
    cbv beta iota zeta delta [prep_coords phi4 phi5].
    rewrite !phi_mdiv; autorewrite with phi; reflexivity.
  Qed.

  (** If [A] represents [P] and [C] holds the cached coordinates of [Q],
      every extended point [S] with the coordinates of [m1_readd A C] is
      projectively equal to [phiX (SP.xadd P Q)]. *)
  Lemma readd_transport (P Q : SP.xpoint) (A : Axpoint) (C : Acached) (S : Axpoint) :
    proj1_sig A = phi5 (proj1_sig P) ->
    proj1_sig C =
      phi4 (prep_coords Zmod.add Zmod.sub Zmod.mul Zmod.mdiv Zmod.one SC.E.d (proj1_sig Q)) ->
    proj1_sig (Am1_readd A C) = proj1_sig S ->
    AXeq S (phiX (SP.xadd P Q)).
  Proof.
    intros hA hC hS.
    pose proof (@AR.readd_correct Fp eq AF.zero AF.one AF.opp AF.add AF.sub AF.mul AF.inv
                  AF.div fld c3 dec AC.E.a AC.E.d nza sqa nsd am1 td k2d nzd
                  (phiX P) (phiX Q)) as h.
    eapply AXeq_coords; [ | | exact h].
    - rewrite <-hS, !A_m1_readd_coords, A_m1_prep_coords, hA, hC, prep_coords_phi.
      reflexivity.
    - apply m1add_phiX.
  Qed.
End Transport.

(** Cached coordinates of a SigmaProtocol extended point. *)
Definition xprep (Q : SP.xpoint) : Zp * Zp * Zp * Zp :=
  prep_coords Zmod.add Zmod.sub Zmod.mul Zmod.mdiv Zmod.one SC.E.d (proj1_sig Q).

(** The affine form: a point projectively equal to [SP.xadd P Q] has the
    affine image [padd (to_affine P) (to_affine Q)], which is the group
    operation [gop] on the order-[l] subgroup [G]. *)
Corollary readd_affine (P Q S : SP.xpoint) :
  SXeq S (SP.xadd P Q) -> SP.to_affine S = SP.padd (SP.to_affine P) (SP.to_affine Q).
Proof. intro h; rewrite (SXeq_to_affine _ _ h); apply SP.to_affine_xadd. Qed.

Corollary readd_gop (g h : SP.G) (P Q S : SP.xpoint) :
  SP.to_affine P = proj1_sig g -> SP.to_affine Q = proj1_sig h ->
  SXeq S (SP.xadd P Q) -> SP.to_affine S = proj1_sig (SP.gop g h).
Proof. intros hP hQ hS; rewrite (readd_affine _ _ _ hS), hP, hQ; reflexivity. Qed.

Print Assumptions m1double_transport.
Print Assumptions m1add_transport.
Print Assumptions from_affine_transport.
Print Assumptions to_affine_transport.
Print Assumptions phi_d.
Print Assumptions readd_transport.
Print Assumptions readd_affine.
Print Assumptions readd_gop.
