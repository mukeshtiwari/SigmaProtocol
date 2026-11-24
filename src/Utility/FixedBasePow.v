(** * Fixed-base exponentiation in Schnorr groups

    Most exponentiations of the protocols have one of a few fixed bases (the
    generator [g] and the election key [h]).  For such a base [c] a table of
    the powers [c^(j·16^i) mod p] for [0 ≤ j < 16] and [i < r] turns an
    exponentiation [c^e mod p] with [e < 16^r] into [r] modular
    multiplications, one per base-16 digit of [e] ([fb_eval]), instead of
    about [1.5·log2 e] for square-and-multiply.

    [pow_fb tabs] is the scalar multiplication of the Schnorr group that uses
    the table of [tabs] whose base is the argument when there is one, and
    [Vspace.pow] otherwise.  It is equal to [Vspace.pow] ([pow_fb_pow]), so it
    gives the same vector space ([pow_fb_vspace]), and every theorem stated
    for an arbitrary vector space holds for it.  The tables are checked by
    construction: [fb_tables_ok tabs] says that each table is [fb_table] of
    its base, which an instance proves by [eq_refl]. *)

From Stdlib Require Import ZArith Lia List Znumtheory Zpow_facts.
From Utility Require Import Util Functions Zpstar.
From Algebra Require Import Hierarchy.
Import ListNotations.

Local Open Scope Z_scope.

(** ** Tables and their evaluation *)

Section Table.
  Variable p : Z.
  Hypothesis Hp1 : 1 < p.

  (** [acc · c^0, acc · c^1, …] modulo [p], [n] entries. *)
  Fixpoint row_aux (c acc : Z) (n : nat) : list Z :=
    match n with
    | O => []
    | S n' => acc :: row_aux c ((acc * c) mod p) n'
    end.

  (** [c^j mod p] for [0 ≤ j < 16]. *)
  Definition row16 (c : Z) : list Z := row_aux c (1 mod p) 16.

  (** Rows [i < r]: the row of [c^(16^i)]. *)
  Fixpoint fb_table (c : Z) (r : nat) : list (list Z) :=
    match r with
    | O => []
    | S r' => row16 c :: fb_table (Zpow_mod c 16 p) r'
    end.

  (** [acc · c^e mod p] from the table of [c], one base-16 digit of [e] per
      row. *)
  Fixpoint fb_eval (t : list (list Z)) (e acc : Z) : Z :=
    match t with
    | [] => acc
    | row :: t' => fb_eval t' (e / 16) ((acc * nth (Z.to_nat (e mod 16)) row 1) mod p)
    end.

  Lemma nth_row_aux :
    forall n c acc j, (j < n)%nat -> acc mod p = acc ->
    nth j (row_aux c acc n) 1 = (acc * c ^ Z.of_nat j) mod p.
  Proof.
    induction n as [|n IHn]; intros c acc j Hj Hacc; [lia|].
    destruct j as [|j]; cbn [row_aux nth].
    - rewrite Z.pow_0_r, Z.mul_1_r. now rewrite Hacc.
    - rewrite IHn; [|lia|apply Z.mod_mod; lia].
      rewrite Z.mul_mod_idemp_l by lia.
      rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
      f_equal. ring.
  Qed.

  Lemma nth_row16 :
    forall c d, 0 <= d < 16 ->
    nth (Z.to_nat d) (row16 c) 1 = c ^ d mod p.
  Proof.
    intros c d Hd. unfold row16.
    rewrite nth_row_aux; [|lia|apply Z.mod_mod; lia].
    rewrite Z2Nat.id by lia.
    rewrite Z.mul_mod_idemp_l by lia.
    now rewrite Z.mul_1_l.
  Qed.

  Lemma fb_eval_correct :
    forall r c e acc,
    0 <= c -> 0 <= e < 16 ^ Z.of_nat r -> acc mod p = acc ->
    fb_eval (fb_table c r) e acc = (acc * c ^ e) mod p.
  Proof.
    induction r as [|r IHr]; intros c e acc Hc He Hacc; cbn [fb_table fb_eval].
    - assert (e = 0) by (cbn in He; lia). subst e.
      rewrite Z.pow_0_r, Z.mul_1_r. now rewrite Hacc.
    - rewrite Nat2Z.inj_succ, Z.pow_succ_r in He by lia.
      assert (Hd : 0 <= e mod 16 < 16) by (apply Z.mod_pos_bound; lia).
      assert (Hq : 0 <= e / 16 < 16 ^ Z.of_nat r).
      { split; [apply Z.div_pos; lia|].
        apply Z.div_lt_upper_bound; lia. }
      rewrite IHr.
      + rewrite nth_row16 by exact Hd.
        rewrite Zpow_mod_correct by lia.
        assert (H16 : (c ^ 16 mod p) ^ (e / 16) mod p = c ^ (16 * (e / 16)) mod p).
        { rewrite <- Zpower_mod by lia.
          rewrite Z.pow_mul_r by (lia || (apply Z.div_pos; lia)). reflexivity. }
        rewrite Z.mul_mod_idemp_l by lia.
        rewrite <- Z.mul_assoc.
        rewrite Z.mul_mod by lia. rewrite (Z.mul_mod (c ^ (e mod 16) mod p)) by lia.
        rewrite H16, Z.mod_mod by lia.
        rewrite <- Z.mul_mod by lia.
        rewrite Z.mul_mod by lia.
        rewrite <- (Z.mul_mod (c ^ (e mod 16))) by lia.
        rewrite <- Z.mul_mod by lia.
        rewrite <- Z.pow_add_r by (lia || (apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia])).
        f_equal. f_equal. f_equal.
        rewrite Z.add_comm. symmetry. apply Z.div_mod. lia.
      + rewrite Zpow_mod_correct by lia. apply Z.mod_pos_bound. lia.
      + exact Hq.
      + apply Z.mod_mod. lia.
  Qed.

End Table.

(** ** Fixed-base scalar multiplication in a Schnorr group *)

Section FixedBase.
  Context
    {k p q : Z}
    {Hk : p = k * q + 1}
    {Hp : prime p}
    {Hq : prime q}.

  Local Notation G := (@Schnorr.Schnorr_group p q).
  Local Notation F := (@Zpfield.Zp q).
  Local Notation pow := (@Vspace.pow k p q Hk Hp Hq).

  (** A table: its base, its number of rows and its rows. *)
  Definition fb_tables := list (Z * nat * list (list Z)).

  Definition fb_tables_ok (tabs : fb_tables) : Prop :=
    Forall (fun '(b, r, t) => t = fb_table p b r) tabs.

  Fixpoint fb_find (tabs : fb_tables) (b : Z) : option (nat * list (list Z)) :=
    match tabs with
    | [] => None
    | (b', r, t) :: tabs' => if Z.eqb b b' then Some (r, t) else fb_find tabs' b
    end.

  (** The power [b^e mod p] from a table of [b], when there is one that
      covers [e]. *)
  Definition fb_value (tabs : fb_tables) (b e : Z) : option Z :=
    match fb_find tabs b with
    | Some (r, t) =>
        if ((0 <=? e) && (e <? Z.shiftl 1 (4 * Z.of_nat r)))%bool
        then Some (fb_eval p t e 1) else None
    | None => None
    end.

  Lemma fb_find_ok :
    forall tabs b r t, fb_tables_ok tabs -> fb_find tabs b = Some (r, t) ->
    t = fb_table p b r.
  Proof.
    induction tabs as [|[[b' r'] t'] tabs IH]; intros b r t Hok Hf; [discriminate|].
    inversion Hok as [|x l Hx Hl]; subst.
    cbn in Hf. destruct (Z.eqb_spec b b') as [->|_].
    - now inversion Hf; subst.
    - now apply IH.
  Qed.

  Lemma fb_value_correct :
    forall tabs b e z, fb_tables_ok tabs -> 0 <= b ->
    fb_value tabs b e = Some z -> z = b ^ e mod p.
  Proof.
    intros tabs b e z Hok Hb Hv. unfold fb_value in Hv.
    destruct (fb_find tabs b) as [[r t]|] eqn:Hf; [|discriminate].
    destruct ((0 <=? e) && (e <? Z.shiftl 1 (4 * Z.of_nat r)))%bool eqn:He; [|discriminate].
    inversion Hv; subst z.
    apply andb_prop in He as [He1 He2].
    apply Z.leb_le in He1. apply Z.ltb_lt in He2.
    rewrite (fb_find_ok _ _ _ _ Hok Hf).
    pose proof (prime_ge_2 p Hp) as Hp2.
    rewrite fb_eval_correct by
      (lia || (split; [lia|]; rewrite Z.shiftl_1_l in He2;
               replace (2 ^ (4 * Z.of_nat r)) with (16 ^ Z.of_nat r) in He2
                 by (rewrite Z.pow_mul_r by lia; reflexivity); lia)
           || (apply Z.mod_small; lia)).
    now rewrite Z.mul_1_l.
  Qed.

  (** The value of [Vspace.pow]. *)
  Lemma pow_value :
    forall (g : G) (y : F), Schnorr.v (pow g y) = (Schnorr.v g) ^ (Zpfield.v y) mod p.
  Proof.
    intros [gt Hga Hgb] [yt Hyt]. cbn.
    pose proof (prime_ge_2 p Hp) as Hp2.
    assert (0 <= yt) by (rewrite <- Hyt; apply Z.mod_pos_bound; pose proof (prime_ge_2 q Hq); lia).
    rewrite zmod_nmod by (rewrite Z2N.id; [exact Hp|lia]).
    rewrite !Z2N.id by lia.
    apply Zpow_mod_correct. lia.
  Qed.

  Lemma fb_value_pow :
    forall tabs (Ht : fb_tables_ok tabs) (g : G) (y : F) z,
    fb_value tabs (Schnorr.v g) (Zpfield.v y) = Some z -> z = Schnorr.v (pow g y).
  Proof.
    intros tabs Ht g y z Hv.
    rewrite pow_value.
    apply (fb_value_correct tabs); [exact Ht| |exact Hv].
    destruct g as [gt Hga Hgb]; cbn; lia.
  Qed.

  (** Scalar multiplication with the tables of [tabs]. *)
  Definition pow_fb (tabs : fb_tables) (Ht : fb_tables_ok tabs) (g : G) (y : F) : G :=
    match fb_value tabs (Schnorr.v g) (Zpfield.v y) as o
      return fb_value tabs (Schnorr.v g) (Zpfield.v y) = o -> G with
    | Some z => fun E =>
        Schnorr.mk_schnorr z
          (eq_ind_r (fun w => 0 < w < p) (Schnorr.Ha (pow g y)) (fb_value_pow tabs Ht g y z E))
          (eq_ind_r (fun w => Zpow_mod w q p = 1) (Schnorr.Hb (pow g y)) (fb_value_pow tabs Ht g y z E))
    | None => fun _ => pow g y
    end eq_refl.

  Lemma pow_fb_pow :
    forall tabs Ht g y, pow_fb tabs Ht g y = pow g y.
  Proof.
    intros tabs Ht g y. unfold pow_fb.
    generalize (fb_value_pow tabs Ht g y).
    destruct (fb_value tabs (Schnorr.v g) (Zpfield.v y)) as [z|]; intros Hz; [|reflexivity].
    destruct (pow g y) as [w Hwa Hwb] eqn:Hpow.
    apply Schnorr.construct_schnorr_group.
    specialize (Hz z eq_refl). cbn in Hz. exact Hz.
  Qed.

  (** [pow_fb tabs] makes the Schnorr group a vector space over [Z_q], the
      same as [Vspace.pow_vspace]. *)
  Global Instance pow_fb_vspace (tabs : fb_tables) (Ht : fb_tables_ok tabs) :
    @vector_space
      (@Zpfield.Zp q) (@eq (@Zpfield.Zp q))
      (@Zpfield.zero q Hq) (@Zpfield.one q Hq)
      (@Zpfield.zp_add q) (@Zpfield.zp_mul q) (@Zpfield.zp_sub q) (@Zpfield.zp_div q)
      (@Zpfield.zp_opp q Hq) (@Zpfield.zp_inv q)
      (@Schnorr.Schnorr_group p q) (@eq (@Schnorr.Schnorr_group p q))
      (@Schnorr.one p q Hp Hq) (@Schnorr.inv_schnorr_group p q Hp Hq)
      (@Schnorr.mul_schnorr_group p q Hp Hq)
      (pow_fb tabs Ht).
  Proof.
    pose proof (@Vspace.pow_vspace k p q Hk Hp Hq) as V.
    destruct V as [Vg Vf V1 V0 Va Vd Vv VP].
    econstructor; try exact Vg; try exact Vf.
    - intros v. rewrite pow_fb_pow. apply V1.
    - intros v. rewrite pow_fb_pow. apply V0.
    - intros r1 r2 v. rewrite !pow_fb_pow. apply Va.
    - intros r1 r2 v. rewrite !pow_fb_pow. apply Vd.
    - intros r v1 v2. rewrite !pow_fb_pow. apply Vv.
    - intros x y Hxy u v Huv. subst. reflexivity.
  Qed.

End FixedBase.
