(** Fourth bridge theorem: a bedrock2 scalar multiplication [scalarmult]
    by most-significant-bit-first double-and-add over the 256 bits of a
    32-byte little-endian scalar, with AUCurves' verified [double] and the
    addition [add] of [ToCached2], related to SigmaProtocol's
    [Ed.gpow_fast].

    The loop body is the bedrock2 function [step]: [double] into a scratch
    buffer, then [add] of the base point (bit 1) or [pcopy] (bit 0) back
    into the accumulator. After the bits [255 .. i] are processed, the
    affine image of the accumulator is [(k >> i) . P]
    ([step_affine]); this is the image of SigmaProtocol's [xmul_pos] on the
    processed prefix ([xsmul_affine]). *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Crypto.Algebra.Field.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Word.LittleEndianList.
From Stdlib Require Import Zmod.
Require Fiat.Algebra.ScalarMult.
Require Import Bridge.FieldTransport Bridge.ExecReadd Bridge.ExecDouble Bridge.ToCached2.
Import ProgramLogic.Coercions ListNotations.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.
Module SM := Fiat.Algebra.ScalarMult.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* The notations of [Ed25519XYZT64] (module-local there), restated. *)
Local Notation word := (Naive.word 64).
Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation felem_size := 40.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Notation "c 'p5@' p" := (let '(X,Y,Z,Ta,Tb) := proj1_sig c in sep (sep (sep (sep
                              (FElem (p) X)
                              (FElem (p .+ felem_size) Y))
                              (FElem (p .+ (felem_size + felem_size)) Z))
                              (FElem (p .+ (felem_size + felem_size + felem_size)) Ta))
                              (FElem (p .+ (felem_size + felem_size + felem_size + felem_size)) Tb))
                              (at level 10, format "c 'p5@' p").
Local Notation "c 'p4@' p" := (let '(half_ymx, half_ypx ,z,td) := proj1_sig c in sep (sep (sep
                              (FElem (p) half_ymx)
                              (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) z))
                              (FElem (p .+ (felem_size + felem_size + felem_size)) td))
                              (at level 10, format "c 'p4@' p").

(* Member access for projective points (X, Y, Z, Ta, Tb) and cached points
   (half_YmX, half_YpX, Z, Td), as in fiat-crypto's [EdwardsXYZT]. *)
Local Notation "A .X" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Y" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Z" := (expr.op Syntax.bopname.add A (felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Ta" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Tb" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_YmX" := (A) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .half_YpX" := (expr.op Syntax.bopname.add A (felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).
Local Notation "A .Td" := (expr.op Syntax.bopname.add A (felem_size + felem_size + felem_size)) (in custom bedrock_expr at level 2, left associativity, only parsing).

Local Notation Fa := Crypto.Spec.Curve25519.E.a.
Local Notation Fd := Crypto.Spec.Curve25519.E.d.

Add Ring Fp_ring : (Crypto.Arithmetic.ModularArithmeticTheorems.F.ring_theory Crypto.Spec.Curve25519.p).

(* The tactics of [Ed25519XYZT64] (module-local there), restated. *)
Local Ltac destruct_points :=
  repeat match goal with
    | _ => progress destruct_head' B.projective_coords
    | _ => progress destruct_head' B.cached_coords
    | _ => progress destruct_head' prod
    | _ => progress destruct_head' and
    | _ => progress lazy beta match zeta delta [Readdition.cached_coordinates proj1_sig] in *
  end.

Local Ltac cbv_bounds H :=
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds] in H;
  cbv [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub bin_carry_sub un_outbounds bin_outbounds].

Local Ltac solve_bounds :=
  repeat match goal with
  | H: bounded_by loose_bounds ?x |- bounded_by loose_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by tight_bounds ?x => apply H
  | H: bounded_by tight_bounds ?x |- bounded_by loose_bounds ?x => apply relax_bounds
  | H: bounded_by _ ?x |- bounded_by _ ?x => cbv_bounds H
  end.

Local Ltac solve_length :=
  try lia;
  try (match goal with
       | |- (Z.of_nat (Datatypes.length ?l) <= 2 ^ _)%Z =>
           apply Z.le_trans with (Z.pow 2 7);
             [ change felem_size_in_bytes with 40 in *;
               rewrite ?length_firstn, ?length_skipn;
               try (match goal with
                    | H : Datatypes.length l = _ |- _ => rewrite H
                    end);
               try listZnWords; try lia
             | apply Z.pow_le_mono_r; lia ]
       end);
  match goal with
    | |- Datatypes.length _ = _ =>
      solve [rewrite ?ws2bs_felem_length; try lia;
          change felem_size_in_bytes with 40 in *; try listZnWords; lia]
  end.

Local Ltac ecancel_assumption_fast :=
  multimatch goal with
  | |- _ ?m1 =>
    multimatch goal with
    | H: _ ?m2 |- _ =>
      syntactic_unify_deltavar m1 m2;
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
      solve [ecancel]
    end
  end.
Local Ltac ecancel_assumption ::= first [ecancel_assumption_fast | ecancel_assumption_impl].

Local Ltac solve_mem :=
  repeat match goal with
    | |- exists _ : _ -> Prop, _%sep _ => eexists
    | H: ?P%sep ?m |- ?G%sep ?m => progress ecancel_assumption_preprocess_with solve_length
    | H : _ %sep ?m |- _ %sep ?m => bottom_up_simpl_in_goal
    | |- _%sep _ => ecancel_assumption
  end.

Local Ltac single_step :=
  repeat straightline; straightline_call; ssplit; try solve_mem; try solve_bounds; try solve_length.

(* [B.split_stack_at_n_in] with [bottom_up_simpl_in_hyp] made optional: on
   a precondition without address arithmetic it has nothing to simplify. *)
Local Ltac split_at stack p n_nat n_z H :=
  rewrite <- (firstn_skipn n_nat stack) in H;
  rewrite (map.of_list_word_at_app_n _ _ _ n_z) in H by
    (rewrite length_firstn; cbv [felem_size_in_bytes] in *; listZnWords);
  let D := fresh in
  unshelve(epose (sep_eq_putmany _ _ (map.adjacent_arrays_disjoint_n p (ListDef.firstn n_nat stack) (ListDef.skipn n_nat stack) n_z _ _)) as D);
    [ rewrite length_firstn; cbv [felem_size_in_bytes] in *; listZnWords
    | rewrite length_firstn, length_skipn; cbv [felem_size_in_bytes] in *; listZnWords
    | seprewrite_in D H; rewrite ?skipn_skipn in H;
      try bottom_up_simpl_in_hyp H; clear D ].

(** ** Double-and-add over the bits of a scalar, in affine terms *)

Module ZL := Curve.Ed25519.Ed25519.Zl.
Local Notation smul := (@SM.scalarmult_ref SP.point SP.padd SP.pzero SP.popp).

(** One iteration on the affine image [Q] of the accumulator: double, then
    add [P] if the bit is set. *)
Definition dbl_add (b : bool) (Q P : SP.point) : SP.point :=
  if b then SP.padd (SP.padd Q Q) P else SP.padd Q Q.

Lemma shiftr_step (k i : Z) : 0 <= i ->
  Z.shiftr k i = 2 * Z.shiftr k (i + 1) + Z.b2z (Z.testbit k i).
Proof.
  intro hi.
  rewrite <-(Z.shiftr_shiftr k i 1) by lia.
  rewrite <-Z.div2_spec.
  replace (Z.testbit k i) with (Z.odd (Z.shiftr k i))
    by (rewrite <-Z.bit0_odd, Z.shiftr_spec by lia; f_equal; lia).
  apply Z.div2_odd.
Qed.

(** The step lemma: if the accumulator represents [(k >> (i+1)) . P], one
    iteration on bit [i] of [k] gives [(k >> i) . P]. *)
Lemma step_affine (k i : Z) (P Q : SP.point) : 0 <= i ->
  Q = smul (Z.shiftr k (i + 1)) P ->
  dbl_add (Z.testbit k i) Q P = smul (Z.shiftr k i) P.
Proof.
  intros hi ->; rewrite (shiftr_step k i hi).
  set (n := Z.shiftr k (i + 1)).
  destruct (Z.testbit k i); cbn [dbl_add Z.b2z].
  - replace (2 * n + 1) with ((n + n) + 1) by lia.
    rewrite !SP.smul_add_l, SP.smul_1_l; reflexivity.
  - replace (2 * n + 0) with (n + n) by lia.
    rewrite SP.smul_add_l; reflexivity.
Qed.

Lemma shiftr_large (k n : Z) : 0 <= n -> 0 <= k < 2 ^ n -> Z.shiftr k n = 0.
Proof. intros hn hk; rewrite Z.shiftr_div_pow2 by lia; apply Z.div_small; lia. Qed.

(** The extended scalar multiple of SigmaProtocol: [xmul_pos] for a
    positive scalar, the image of the neutral element otherwise. *)
Definition xsmul (n : Z) (P : SP.xpoint) : SP.xpoint :=
  match n with
  | Zpos q => SP.xmul_pos q P
  | _ => SP.from_affine SP.pzero
  end.

Lemma xsmul_affine (n : Z) (P : SP.xpoint) : 0 <= n ->
  SP.to_affine (xsmul n P) = smul n (SP.to_affine P).
Proof.
  destruct n as [| q | q]; intro hn; cbn [xsmul].
  - rewrite SP.to_from_affine, SP.smul_0_l; reflexivity.
  - apply SP.xmul_pos_correct.
  - lia.
Qed.

(** The loop invariant in projective form: the accumulator is projectively
    equal to [xsmul] of the processed prefix of the scalar. *)
Lemma invariant_iff (A P : SP.xpoint) (n : Z) : 0 <= n ->
  SXeq A (xsmul n P) <-> SP.to_affine A = smul n (SP.to_affine P).
Proof.
  intro hn; rewrite <-(xsmul_affine n P hn); split.
  - apply SXeq_to_affine.
  - apply SXeq_of_to_affine.
Qed.

(** The result of the loop, stated against [Ed.gpow_fast]. *)
Lemma gpow_fast_affine (x : SP.G) (s : ZL.F) (A : SP.xpoint) :
  SP.to_affine A = smul (Zmod.unsigned s) (proj1_sig x) ->
  SXeq A (xsmul (Zmod.unsigned s) (SP.from_affine (proj1_sig x))) /\
  SP.to_affine A = proj1_sig (SP.gpow_fast x s).
Proof.
  intro h; split.
  - pose proof (Zmod.unsigned_range s) as hr.
    apply invariant_iff; [lia |]; rewrite SP.to_from_affine; exact h.
  - unfold SP.gpow_fast; cbn [proj1_sig]; rewrite SP.fast_smul_eq; exact h.
Qed.

(** ** Extended points as byte buffers *)

Lemma array_app40_5 (p : word) (b1 b2 b3 b4 b5 : list byte) :
  Datatypes.length b1 = 40%nat -> Datatypes.length b2 = 40%nat ->
  Datatypes.length b3 = 40%nat -> Datatypes.length b4 = 40%nat ->
  Lift1Prop.iff1 (array ptsto (word.of_Z 1) p (b1 ++ b2 ++ b3 ++ b4 ++ b5))
    (sep (sep (sep (sep (array ptsto (word.of_Z 1) p b1)
                        (array ptsto (word.of_Z 1) (p .+ felem_size) b2))
                   (array ptsto (word.of_Z 1) (p .+ (felem_size + felem_size)) b3))
              (array ptsto (word.of_Z 1) (p .+ (felem_size + felem_size + felem_size)) b4))
         (array ptsto (word.of_Z 1) (p .+ (felem_size + felem_size + felem_size + felem_size)) b5)).
Proof.
  intros h1 h2 h3 h4.
  rewrite (array_app40_4 p b1 b2 b3 (b4 ++ b5) h1 h2 h3).
  rewrite (array_app40 (p .+ (felem_size + felem_size + felem_size))
             (p .+ (felem_size + felem_size + felem_size + felem_size)) b4 b5 h4
             (add_40_40 p (40 + 40 + 40))).
  cancel.
Qed.

(** The memory of an extended point is a 200-byte buffer. *)
Lemma p5_to_bytes (c : B.projective_coords) (p : word) (R : _ -> Prop) m :
  sep (c p5@ p) R m ->
  exists bs, Datatypes.length bs = 200%nat /\ sep (bs $@ p) R m.
Proof.
  destruct c as [[[[[c1 c2] c3] c4] c5] hc]; cbn [proj1_sig]; intro H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) p c1) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) (p .+ felem_size) c2) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) (p .+ (felem_size + felem_size)) c3) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519)
                   (p .+ (felem_size + felem_size + felem_size)) c4) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519)
                   (p .+ (felem_size + felem_size + felem_size + felem_size)) c5) H.
  pose proof (ws2bs_felem_length c1) as l1.
  pose proof (ws2bs_felem_length c2) as l2.
  pose proof (ws2bs_felem_length c3) as l3.
  pose proof (ws2bs_felem_length c4) as l4.
  pose proof (ws2bs_felem_length c5) as l5.
  change felem_size_in_bytes with 40 in l1, l2, l3, l4, l5.
  lazymatch type of l1 with Datatypes.length ?b = _ => set (b1 := b) in * end.
  lazymatch type of l2 with Datatypes.length ?b = _ => set (b2 := b) in * end.
  lazymatch type of l3 with Datatypes.length ?b = _ => set (b3 := b) in * end.
  lazymatch type of l4 with Datatypes.length ?b = _ => set (b4 := b) in * end.
  lazymatch type of l5 with Datatypes.length ?b = _ => set (b5 := b) in * end.
  change (Z.to_nat 40) with 40%nat in l1, l2, l3, l4, l5.
  exists (b1 ++ b2 ++ b3 ++ b4 ++ b5)%list.
  assert (hl : Datatypes.length (b1 ++ b2 ++ b3 ++ b4 ++ b5)%list = 200%nat)
    by (rewrite !length_app, l1, l2, l3, l4, l5; reflexivity).
  split; [exact hl |].
  pose proof (array_app40_5 p b1 b2 b3 b4 b5 l1 l2 l3 l4) as Hi.
  assert (Harr : sep (array ptsto (word.of_Z 1) p (b1 ++ b2 ++ b3 ++ b4 ++ b5)%list) R m)
    by (apply (proj2 (Proper_sep_iff1 _ _ Hi R R (iff1_refl R) m)); ecancel_assumption).
  assert (Hb : Lift1Prop.iff1 (array ptsto (word.of_Z 1) p (b1 ++ b2 ++ b3 ++ b4 ++ b5)%list)
                 ((b1 ++ b2 ++ b3 ++ b4 ++ b5)%list $@ p))
    by (apply Array.array1_iff_eq_of_list_word_at; try typeclasses eauto; first [exact BasicC64Semantics.mapok | rewrite hl; cbn; lia]).
  exact (proj1 (Proper_sep_iff1 _ _ Hb R R (iff1_refl R) m) Harr).
Qed.

(** ** [pcopy]: copy an extended point *)

Definition pcopy := func! (p_out, p_a) {
  fe25519_copy(p_out.X, p_a.X);
  fe25519_copy(p_out.Y, p_a.Y);
  fe25519_copy(p_out.Z, p_a.Z);
  fe25519_copy(p_out.Ta, p_a.Ta);
  fe25519_copy(p_out.Tb, p_a.Tb)
}.

#[local] Existing Instances B.spec_of_fe25519_copy64 B.spec_of_fe25519_from_word64.

Global Instance spec_of_pcopy : spec_of "pcopy" :=
  fnspec! "pcopy"
    (p_out p_a: word) / (a: B.projective_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\ m' =* a p5@ p_out * a p5@ p_a * R
  }.

Lemma pcopy_ok : program_logic_goal_for_function! pcopy.
Proof.
  repeat straightline.
  destruct a as [[[[[X Y] Z] Ta] Tb] ha]; cbn [proj1_sig] in *.
  pose proof BasicC64Semantics.wordok as Hwok.
  lazymatch goal with H : context [map.of_list_word_at p_out out] |- _ => rename H into Hm end.
  split_at out p_out 40%nat 40 Hm.
  split_at (ListDef.skipn 40 out) (p_out .+ 40) 40%nat 40 Hm.
  split_at (ListDef.skipn 80 out) (p_out .+ 80) 40%nat 40 Hm.
  split_at (ListDef.skipn 120 out) (p_out .+ 120) 40%nat 40 Hm.
  repeat straightline.
  repeat single_step.
  repeat straightline.
  change (40 + 40 + 40 + 40) with 160; change (40 + 40 + 40) with 120; change (40 + 40) with 80.
  ecancel_assumption.
Qed.

(** ** [set_identity]: the extended neutral element [(0, 1, 1, 0, 1)] *)

Definition set_identity := func! (p_out) {
  fe25519_from_word(p_out.X, $0);
  fe25519_from_word(p_out.Y, $1);
  fe25519_from_word(p_out.Z, $1);
  fe25519_from_word(p_out.Ta, $0);
  fe25519_from_word(p_out.Tb, $1)
}.

Lemma feval_zero_word : F.of_Z Crypto.Spec.Curve25519.p (word.unsigned (word.of_Z 0 : word)) = F.zero.
Proof. reflexivity. Qed.

Global Instance spec_of_set_identity : spec_of "set_identity" :=
  fnspec! "set_identity"
    (p_out: word) / (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists a : B.projective_coords,
          m' =* a p5@ p_out * R /\
          B.feval_projective_coords a = phi5 (proj1_sig (SP.from_affine SP.pzero))
  }.

Lemma set_identity_ok : program_logic_goal_for_function! set_identity.
Proof.
  repeat straightline.
  pose proof BasicC64Semantics.wordok as Hwok.
  lazymatch goal with H : context [map.of_list_word_at p_out out] |- _ => rename H into Hm end.
  split_at out p_out 40%nat 40 Hm.
  split_at (ListDef.skipn 40 out) (p_out .+ 40) 40%nat 40 Hm.
  split_at (ListDef.skipn 80 out) (p_out .+ 80) 40%nat 40 Hm.
  split_at (ListDef.skipn 120 out) (p_out .+ 120) 40%nat 40 Hm.
  repeat straightline.
  repeat single_step.
  repeat straightline.
  lazymatch goal with Hm : _ ?m |- exists _, _ ?m /\ _ =>
  lazymatch type of Hm with context [FElem p_out ?X] =>
  lazymatch type of Hm with context [FElem (p_out .+ 40) ?Y] =>
  lazymatch type of Hm with context [FElem (p_out .+ 80) ?Z] =>
  lazymatch type of Hm with context [FElem (p_out .+ 120) ?Ta] =>
  lazymatch type of Hm with context [FElem (p_out .+ 160) ?Tb] =>
    unshelve eexists (exist _ (X, Y, Z, Ta, Tb) _)
  end end end end end end.
  all: repeat match goal with H : feval _ = F.of_Z _ _ |- _ =>
         progress rewrite H, ?feval_zero_word, ?feval_one_word in * end.
  - cbv [B.valid_projective_coords]; ssplit; try solve_bounds.
    all: repeat match goal with H : feval _ = _ |- _ => rewrite H end.
    all: Decidable.vm_decide.
  - split.
    + lazy beta iota delta [proj1_sig].
      change (40 + 40 + 40 + 40) with 160; change (40 + 40 + 40) with 120;
        change (40 + 40) with 80.
      ecancel_assumption.
    + rewrite SP_from_affine_coords, from_affine_coords_phi.
      unfold B.feval_projective_coords; cbn [proj1_sig].
      change (proj1_sig SP.pzero) with (Zmod.zero (m:=SC.p), Zmod.one (m:=SC.p)).
      cbn [phi2]; rewrite phi_zero.
      repeat match goal with H : feval _ = _ |- _ => rewrite H end.
      reflexivity.
Qed.

(** ** Specifications with extended points in place of byte buffers

    [double] with its output packaged as [B.projective_coords]; [add] and
    [pcopy] overwriting a buffer that holds an extended point. *)

Definition spec_of_double_p5 : spec_of "double" :=
  fnspec! "double"
    (p_out p_a: word) /
    (P : SP.xpoint) (a: B.projective_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        B.feval_projective_coords a = phi5 (proj1_sig P);
      ensures t' m' :=
        t = t' /\
        exists d : B.projective_coords,
          m' =* d p5@ p_out * a p5@ p_a * R /\
          B.feval_projective_coords d = phi5 (proj1_sig (SP.xdouble P))
    }.

Lemma double_spec_p5 functions :
  spec_of_double_sigma functions -> spec_of_double_p5 functions.
Proof.
  intros H p_out p_a P a out R t m Hpre.
  eapply WeakestPreconditionProperties.Proper_call; [| apply (H p_out p_a P a out R t m Hpre)].
  intros t' m' rets (Hrets & Ht & X & Y & Z & Ta & Tb & Hv & HX & HY & HZ & HTa & HTb & Hm' & Hc).
  split; [exact Hrets |]. split; [exact Ht |].
  exists (exist _ (X, Y, Z, Ta, Tb) (conj Hv (conj HX (conj HY (conj HZ (conj HTa HTb)))))).
  split; [exact Hm' | exact Hc].
Qed.

Definition spec_of_add_ow : spec_of "add" :=
  fnspec! "add"
    (p_out p_a p_b p_d: word) /
    (P Q : SP.xpoint) (o a b: B.projective_coords) (d2: felem) (R: _ -> Prop), {
      requires t m :=
        m =* o p5@ p_out * a p5@ p_a * b p5@ p_b * FElem p_d d2 * R /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2 /\
        B.feval_projective_coords a = phi5 (proj1_sig P) /\
        B.feval_projective_coords b = phi5 (proj1_sig Q);
      ensures t' m' :=
        t = t' /\
        exists (s : B.projective_coords) (S : SP.xpoint),
          m' =* s p5@ p_out * a p5@ p_a * b p5@ p_b * FElem p_d d2 * R /\
          B.feval_projective_coords s = phi5 (proj1_sig S) /\
          SXeq S (SP.xadd P Q) /\
          SP.to_affine S = SP.padd (SP.to_affine P) (SP.to_affine Q)
  }.

Lemma add_spec_ow functions : spec_of_add_sigma functions -> spec_of_add_ow functions.
Proof.
  intros H p_out p_a p_b p_d P Q o a b d2 R t m (Hm & Hd & Hb & Ha & HbQ).
  assert (Hm' : sep (o p5@ p_out) (sep (sep (sep (a p5@ p_a) (b p5@ p_b)) (FElem p_d d2)) R) m)
    by ecancel_assumption.
  destruct (p5_to_bytes _ _ _ _ Hm') as (bs & hl & Hbs).
  apply (H p_out p_a p_b p_d P Q a b d2 bs R t m).
  ssplit; [ecancel_assumption | rewrite hl; reflexivity | assumption ..].
Qed.

Definition spec_of_pcopy_ow : spec_of "pcopy" :=
  fnspec! "pcopy"
    (p_out p_a: word) / (o a: B.projective_coords) (R: _ -> Prop), {
      requires t m := m =* o p5@ p_out * a p5@ p_a * R;
      ensures t' m' := t = t' /\ m' =* a p5@ p_out * a p5@ p_a * R
  }.

Lemma pcopy_spec_ow functions : spec_of_pcopy functions -> spec_of_pcopy_ow functions.
Proof.
  intros H p_out p_a o a R t m Hm.
  assert (Hm' : sep (o p5@ p_out) (sep (a p5@ p_a) R) m) by ecancel_assumption.
  destruct (p5_to_bytes _ _ _ _ Hm') as (bs & hl & Hbs).
  apply (H p_out p_a a bs R t m).
  ssplit; [ecancel_assumption | rewrite hl; reflexivity].
Qed.

(** ** [step]: one iteration of double-and-add

    The accumulator at [p_acc] is doubled into the scratch buffer at
    [p_t]; if [b] is nonzero the base point at [p_P] is added to the
    result back into [p_acc], otherwise the result is copied back. *)

Definition step := func! (p_acc, p_t, p_P, p_d, b) {
  double(p_t, p_acc);
  if b { add(p_acc, p_t, p_P, p_d) } else { pcopy(p_acc, p_t) }
}.

#[local] Existing Instance spec_of_double_p5 | 0.
#[local] Existing Instance spec_of_add_ow | 0.
#[local] Existing Instance spec_of_pcopy_ow | 0.

Global Instance spec_of_step : spec_of "step" :=
  fnspec! "step"
    (p_acc p_t p_P p_d b: word) /
    (A P : SP.xpoint) (a pP: B.projective_coords) (d2: felem) (tb : list byte)
    (R: _ -> Prop), {
      requires t m :=
        m =* a p5@ p_acc * tb $@ p_t * pP p5@ p_P * FElem p_d d2 * R /\
        Datatypes.length tb = Z.to_nat (5 * felem_size) /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2 /\
        B.feval_projective_coords a = phi5 (proj1_sig A) /\
        B.feval_projective_coords pP = phi5 (proj1_sig P);
      ensures t' m' :=
        t = t' /\
        exists (a' : B.projective_coords) (tb' : list byte) (A' : SP.xpoint),
          m' =* a' p5@ p_acc * tb' $@ p_t * pP p5@ p_P * FElem p_d d2 * R /\
          Datatypes.length tb' = Z.to_nat (5 * felem_size) /\
          B.feval_projective_coords a' = phi5 (proj1_sig A') /\
          SP.to_affine A' =
            dbl_add (negb (word.unsigned b =? 0)) (SP.to_affine A) (SP.to_affine P)
  }.

Lemma step_ok : program_logic_goal_for_function! step.
Proof.
  repeat straightline.
  straightline_call; ssplit; try ecancel_assumption; try eassumption.
  repeat straightline.
  subst c0. unfold1_cmd_goal; cbv beta match delta [cmd_body].
  eexists; split; [repeat straightline |]. split; intro Hbit.
  - (* bit set: add *)
    repeat straightline.
    straightline_call; ssplit; try ecancel_assumption; try eassumption.
    repeat straightline.
    lazymatch goal with
    | Haff : SP.to_affine ?S = SP.padd (SP.to_affine (SP.xdouble A)) _ |- _ =>
    lazymatch goal with
    | Hd : B.feval_projective_coords ?d = phi5 (proj1_sig (SP.xdouble A)),
      Hs : B.feval_projective_coords ?s = phi5 (proj1_sig S), Hm : _ ?m
      |- exists _ _ _, _ ?m /\ _ =>
        assert (Hm' : sep (d p5@ p_t) (sep (sep (sep (s p5@ p_acc) (pP p5@ p_P)) (FElem p_d d2)) R) m)
          by ecancel_assumption;
        destruct (p5_to_bytes _ _ _ _ Hm') as (bs & hl & Hbs);
        exists s, bs, S; ssplit; [ecancel_assumption | rewrite hl; reflexivity | exact Hs |];
        rewrite Haff, SP.to_affine_xdouble
    end end.
    destruct (word.unsigned b =? 0) eqn:E; [apply Z.eqb_eq in E; contradiction |].
    reflexivity.
  - (* bit clear: copy *)
    repeat straightline.
    straightline_call; [ecancel_assumption |].
    repeat straightline.
    lazymatch goal with
    | Hd : B.feval_projective_coords ?d = phi5 (proj1_sig (SP.xdouble A)), Hm : _ ?m
      |- exists _ _ _, _ ?m /\ _ =>
        assert (Hm' : sep (d p5@ p_t) (sep (sep (sep (d p5@ p_acc) (pP p5@ p_P)) (FElem p_d d2)) R) m)
          by ecancel_assumption;
        destruct (p5_to_bytes _ _ _ _ Hm') as (bs & hl & Hbs);
        exists d, bs, (SP.xdouble A); ssplit; [ecancel_assumption | rewrite hl; reflexivity | exact Hd |];
        rewrite SP.to_affine_xdouble
    end.
    destruct (word.unsigned b =? 0) eqn:E; [reflexivity |].
    apply Z.eqb_neq in E; contradiction.
Qed.

(** ** [scalarmult]: the loop over the 256 bits of the scalar

    [p_k] holds the 32-byte little-endian scalar; bit [i] is bit [i mod 8]
    of byte [i / 8]. The bits are processed from bit 255 down to bit 0. *)

Definition scalarmult := func! (p_out, p_P, p_k, p_d) {
  stackalloc 200 as p_t;
  set_identity(p_out);
  b = $0;
  i = $256;
  while ($0 < i) {
    i = i - $1;
    b = (load1(p_k + (i >> $3)) >> (i & $7)) & $1;
    step(p_out, p_t, p_P, p_d, b)
  }
}.

(** Bit [8 n + r] of the little-endian value of a byte list is bit [r] of
    byte [n]; the loop reads bit [i] of the scalar this way. *)
Lemma testbit_le_combine (kb : list byte) (n : nat) (r : Z) : 0 <= r < 8 ->
  Z.testbit (le_combine kb) (8 * Z.of_nat n + r) =
  Z.testbit (byte.unsigned (List.nth n kb Byte.x00)) r.
Proof.
  revert n; induction kb as [| h kb ih]; intros n hr; cbn [le_combine].
  - destruct n; cbn [List.nth]; change (byte.unsigned Byte.x00) with 0; rewrite !Z.testbit_0_l; reflexivity.
  - rewrite Z.lor_spec, Z.shiftl_spec by lia.
    pose proof (byte.unsigned_range h) as hh.
    destruct n as [| n]; cbn [List.nth].
    + rewrite (Z.testbit_neg_r _ (8 * Z.of_nat 0 + r - 8)) by lia.
      rewrite Bool.orb_false_r; f_equal; lia.
    + replace (8 * Z.of_nat (S n) + r - 8) with (8 * Z.of_nat n + r) by lia.
      rewrite ih by lia.
      rewrite (Z.bits_above_log2 (byte.unsigned h)); [reflexivity | lia |].
      destruct (Z.eq_dec (byte.unsigned h) 0) as [e | e]; [rewrite e; cbn; lia |].
      apply Z.log2_lt_pow2; [lia |].
      eapply Z.lt_le_trans; [apply hh |].
      apply Z.pow_le_mono_r; lia.
Qed.

(** The value of the scalar fits in its 256 bits; after all of them are
    processed the prefix value [k >> 0] is [k], before any is processed it
    is [k >> 256 = 0]. *)
Lemma scalar_bound (kb : list byte) :
  Datatypes.length kb = 32%nat -> 0 <= le_combine kb < 2 ^ 256.
Proof.
  intro hl; pose proof (LittleEndianList.le_combine_bound kb) as hb; rewrite hl in hb; exact hb.
Qed.

Global Instance spec_of_scalarmult : spec_of "scalarmult" :=
  fnspec! "scalarmult"
    (p_out p_P p_k p_d: word) /
    (P : SP.xpoint) (pP : B.projective_coords) (d2 : felem) (kb out : list byte)
    (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        Datatypes.length kb = 32%nat /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2 /\
        B.feval_projective_coords pP = phi5 (proj1_sig P);
      ensures t' m' :=
        t = t' /\
        exists (a : B.projective_coords) (A : SP.xpoint),
          m' =* a p5@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
          B.feval_projective_coords a = phi5 (proj1_sig A) /\
          SP.to_affine A = smul (le_combine kb) (SP.to_affine P)
  }.

(** Reading one bit of the scalar from memory. *)

Lemma hd_skipn_nth {A} (d : A) (l : list A) (n : nat) : hd d (skipn n l) = nth n l d.
Proof. revert l; induction n as [| n ih]; intros [| x l]; cbn; auto. Qed.

Lemma load_byte (kb : list byte) (p : word) (n : nat) (R : _ -> Prop) m :
  sep (kb $@ p) R m -> (n < Datatypes.length kb)%nat ->
  Z.of_nat (Datatypes.length kb) <= 2 ^ 64 ->
  Memory.load Syntax.access_size.one m (word.add p (word.of_Z (Z.of_nat n))) =
  Some (word.of_Z (byte.unsigned (nth n kb Byte.x00))).
Proof.
  intros H hn hl.
  pose proof (Array.array1_iff_eq_of_list_word_at (map:=BasicC64Semantics.mem) p kb hl) as Hi.
  apply (proj2 (Proper_sep_iff1 _ _ Hi R R (iff1_refl R) m)) in H.
  pose proof (Array.array_index_nat_inbounds (mem:=BasicC64Semantics.mem) ptsto (word.of_Z 1) (default:=Byte.x00) kb p n hn) as Hj.
  apply (proj1 (Proper_sep_iff1 _ _ Hj R R (iff1_refl R) m)) in H.
  rewrite hd_skipn_nth in H.
  change (word.unsigned (word.of_Z 1 : word)) with 1 in H; rewrite Z.mul_1_l in H.
  eapply Scalars.load_one_of_sep.
  ecancel_assumption.
Qed.

Lemma bit_word (bt : byte) (i : word) :
  word.and (word.sru (word.of_Z (byte.unsigned bt)) (word.and i (word.of_Z 7))) (word.of_Z 1) =
  word.of_Z (Z.b2z (Z.testbit (byte.unsigned bt) (word.unsigned i mod 8))).
Proof.
  pose proof (byte.unsigned_range bt) as hb.
  pose proof (Properties.word.unsigned_range i) as hi.
  assert (h7 : word.unsigned (word.and i (word.of_Z 7)) = word.unsigned i mod 8).
  { rewrite Properties.word.unsigned_and_nowrap, Properties.word.unsigned_of_Z_nowrap by lia.
    change 7 with (Z.ones 3); rewrite Z.land_ones by lia; reflexivity. }
  apply Properties.word.unsigned_inj.
  rewrite Properties.word.unsigned_and_nowrap, Properties.word.unsigned_sru_nowrap; rewrite ?h7.
  2: { pose proof (Z.mod_pos_bound (word.unsigned i) 8 ltac:(lia)); lia. }
  rewrite Properties.word.unsigned_of_Z_nowrap by lia.
  rewrite (Properties.word.unsigned_of_Z_nowrap 1) by lia.
  rewrite Properties.word.unsigned_of_Z_nowrap by (destruct Z.testbit; cbn; lia).
  change 1 with (Z.ones 1); rewrite Z.land_ones by lia.
  rewrite Z.shiftr_div_pow2 by (pose proof (Z.mod_pos_bound (word.unsigned i) 8 ltac:(lia)); lia).
  rewrite Z.testbit_spec' by (pose proof (Z.mod_pos_bound (word.unsigned i) 8 ltac:(lia)); lia).
  reflexivity.
Qed.

Lemma sru3 (i : word) : word.unsigned (word.sru i (word.of_Z 3)) = word.unsigned i / 8.
Proof.
  rewrite Properties.word.unsigned_sru_nowrap; rewrite Properties.word.unsigned_of_Z_nowrap by lia; [| lia].
  rewrite Z.shiftr_div_pow2 by lia; reflexivity.
Qed.

Lemma arr_to_map (tb : list byte) (p : word) (R : _ -> Prop) m :
  Datatypes.length tb = 200%nat ->
  sep (array ptsto (word.of_Z 1) p tb) R m -> sep (tb $@ p) R m.
Proof.
  intros hl H.
  assert (hz : Z.of_nat (Datatypes.length tb) <= 2 ^ 64) by (rewrite hl; cbn; lia).
  pose proof (Array.array1_iff_eq_of_list_word_at (map:=BasicC64Semantics.mem) p tb hz) as Hi.
  exact (proj1 (Proper_sep_iff1 _ _ Hi R R (iff1_refl R) m) H).
Qed.

Lemma map_to_arr (tb : list byte) (p : word) (R : _ -> Prop) m :
  Datatypes.length tb = 200%nat ->
  sep (tb $@ p) R m -> sep (array ptsto (word.of_Z 1) p tb) R m.
Proof.
  intros hl H.
  assert (hz : Z.of_nat (Datatypes.length tb) <= 2 ^ 64) by (rewrite hl; cbn; lia).
  pose proof (Array.array1_iff_eq_of_list_word_at (map:=BasicC64Semantics.mem) p tb hz) as Hi.
  exact (proj2 (Proper_sep_iff1 _ _ Hi R R (iff1_refl R) m) H).
Qed.

(** The loop invariant, for [v] bits left: [i] holds [v], the accumulator
    at [p_out] is the image of some [A] with [Ed.to_affine A = (k >> v) . P]
    ([step_affine]), and the scratch buffer at [p_t] is 200 bytes. *)
Lemma scalarmult_ok : program_logic_goal_for_function! scalarmult.
Proof.
  repeat straightline.
  straightline_call; ssplit; try ecancel_assumption; try eassumption.
  repeat straightline.
  rename a into p_t, a0 into t0.
  refine ((Loops.tailrec HList.polymorphic_list.nil
    ("p_out" :: "p_P" :: "p_k" :: "p_d" :: "p_t" :: "b" :: "i" :: nil)%list
    (fun (v : nat) t' m' p_out' p_P' p_k' p_d' p_t' b' i' => PrimitivePair.pair.mk
      (word.unsigned i' = Z.of_nat v /\ (v <= 256)%nat /\ p_out' = p_out /\ p_P' = p_P /\
       p_k' = p_k /\ p_d' = p_d /\ p_t' = p_t /\ t' = t0 /\
       exists (acc : ScalarMult.B.projective_coords) (tb : list byte) (A : SP.xpoint),
         m' =* acc p5@ p_out * tb $@ p_t * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
         Datatypes.length tb = 200%nat /\
         ScalarMult.B.feval_projective_coords acc = phi5 (proj1_sig A) /\
         SP.to_affine A = smul (Z.shiftr (le_combine kb) (Z.of_nat v)) (SP.to_affine P))
      (fun t'' m'' _ _ _ _ _ _ _ => t'' = t0 /\
       exists (acc : ScalarMult.B.projective_coords) (tb : list byte) (A : SP.xpoint),
         m'' =* acc p5@ p_out * tb $@ p_t * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
         Datatypes.length tb = 200%nat /\
         ScalarMult.B.feval_projective_coords acc = phi5 (proj1_sig A) /\
         SP.to_affine A = smul (le_combine kb) (SP.to_affine P)))
    lt _ 256%nat _ _ _));
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  { repeat straightline. }
  { exact lt_wf. }
  { (* initialisation *)
    cbn [PrimitivePair.pair._1 PrimitivePair.pair._2 HList.tuple.apply] in *.
    match goal with
    | Hx : ScalarMult.B.feval_projective_coords ?x0 = phi5 (proj1_sig (SP.from_affine SP.pzero)),
      Hm : ?Pm ?mm |- _ =>
      lazymatch Pm with context [array ptsto _ p_t stack] => idtac end;
      subst i; ssplit; try reflexivity; try lia;
      exists x0, stack, (SP.from_affine SP.pzero); ssplit;
      [ assert (Hm2 : sep (stack $@ p_t) (sep (x0 p5@ p_out) (sep (pP p5@ p_P)
                  (sep (kb $@ p_k) (sep (FElem p_d d2) R)))) mm)
          by (apply arr_to_map; [rewrite length_stack; reflexivity | ecancel_assumption]);
        ecancel_assumption
      | rewrite length_stack; reflexivity
      | exact Hx
      | ]
    end.
    rewrite SP.to_from_affine; change (Z.of_nat 256) with 256.
    rewrite shiftr_large; [rewrite SP.smul_0_l; reflexivity | lia | apply scalar_bound; assumption]. }
  { (* loop body *)
    intros v t' m' p_out' p_P' p_k' p_d' p_t' b' i'.
    repeat straightline.
    - (* bit [i' - 1] *)
      assert (hv : (0 < v)%nat).
      { subst br; destruct (word.ltu (word.of_Z 0) i') eqn:E; [| contradiction].
        rewrite word.unsigned_ltu, Properties.word.unsigned_of_Z_0 in E.
        apply Z.ltb_lt in E; lia. }
      assert (hi : word.unsigned i = Z.of_nat (v - 1)).
      { subst i; rewrite Properties.word.unsigned_sub_nowrap; rewrite ?Properties.word.unsigned_of_Z_1; lia. }
      set (n := Z.to_nat (word.unsigned i / 8)).
      assert (hn : (n < Datatypes.length kb)%nat).
      { subst n; rewrite H3. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
      exists (word.of_Z (Z.b2z (Z.testbit (le_combine kb) (word.unsigned i)))); split.
      { cbv [dexpr]. repeat straightline.        exists (word.of_Z (byte.unsigned (nth n kb Byte.x00))); split.
        - match goal with |- context [word.sru i ?s] => subst s end.
          replace (word.sru i (word.of_Z 3)) with (word.of_Z (Z.of_nat n) : word).
          +            lazymatch goal with
            | Hacc : ScalarMult.B.feval_projective_coords ?acc = phi5 (proj1_sig ?A),
              Hlen : Datatypes.length ?tb = 200%nat |- _ =>
              assert (Hk : sep (kb $@ p_k) (sep (acc p5@ p_out) (sep (tb $@ p_t)
                             (sep (pP p5@ p_P) (sep (FElem p_d d2) R)))) m')
                by ecancel_assumption
            end.
            exact (load_byte kb p_k n _ m' Hk hn ltac:(rewrite H3; cbn; lia)).
          + apply Properties.word.unsigned_inj.
            rewrite sru3, Properties.word.unsigned_of_Z_nowrap; subst n;
              rewrite ?Z2Nat.id; try (apply Z.div_pos; lia); try reflexivity.
            pose proof (Properties.word.unsigned_range i); split; [lia |].
            pose proof (Z.div_le_upper_bound (word.unsigned i) 8 (2 ^ 64) ltac:(lia) ltac:(lia)); lia.
        - repeat straightline.          rewrite bit_word.
          f_equal; f_equal.
          assert (hdm : word.unsigned i = 8 * Z.of_nat n + word.unsigned i mod 8)
            by (subst n; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_mod; lia).
          pose proof (testbit_le_combine kb n (word.unsigned i mod 8)
                        (Z.mod_pos_bound _ 8 ltac:(lia))) as Ht.
          rewrite <-hdm in Ht.
          first [exact Ht | symmetry; exact Ht]. }
      repeat straightline.
      straightline_call; ssplit; try ecancel_assumption; try eassumption.
      lazymatch goal with
      | Hp : ?r = [] /\ _ |- _ => destruct Hp as (-> & Ht & acc' & tb' & A' & Hm' & Hl' & Hf' & Ha')
      end.
      eexists; split; [reflexivity |].
      cbv [Markers.unique Markers.left Markers.split Markers.right].
      set (bv := word.of_Z (Z.b2z (Z.testbit (le_combine kb) (word.unsigned i))) : word) in *.
      assert (hbv : bv = word.of_Z (Z.b2z (Z.testbit (le_combine kb) (word.unsigned i))))
        by reflexivity.
      clearbody bv i.
      exists p_out, p_P, p_k, p_d, p_t, bv, i.
      split; [exact (conj eq_refl eq_refl) |].
      exists (v - 1)%nat.
      lazymatch goal with
      | Hinv : SP.to_affine ?A0 = smul (Z.shiftr (le_combine kb) (Z.of_nat v)) _ |- _ =>
        split;
        [ ssplit; try reflexivity; try lia; try congruence;
          exists acc', tb', A'; ssplit; [ecancel_assumption | assumption | assumption |];
          rewrite Ha', hbv;
          rewrite Properties.word.unsigned_of_Z_nowrap
            by (destruct (Z.testbit (le_combine kb) (word.unsigned i)); cbn; lia);
          replace (negb (Z.b2z (Z.testbit (le_combine kb) (word.unsigned i)) =? 0))
            with (Z.testbit (le_combine kb) (word.unsigned i))
            by (destruct (Z.testbit (le_combine kb) (word.unsigned i)); reflexivity);
          rewrite hi; apply step_affine; [lia |];
          replace (Z.of_nat (v - 1) + 1) with (Z.of_nat v) by lia; exact Hinv
        | split; [lia | intros ? ? ? ? ? ? ? ? ? Hp; exact Hp] ]
      end.
    - (* exit of the loop *)
      assert (hv : v = 0%nat).
      { subst br; destruct (word.ltu (word.of_Z 0) i') eqn:E.
        - exfalso; match goal with Hz : word.unsigned (word.of_Z 1) = 0 |- _ => cbv in Hz; discriminate Hz end.
        - rewrite word.unsigned_ltu, Properties.word.unsigned_of_Z_0 in E.
          apply Z.ltb_ge in E. pose proof (Properties.word.unsigned_range i'); lia. }
      subst v.
      lazymatch goal with
      | Hinv : SP.to_affine ?A0 = smul (Z.shiftr (le_combine kb) (Z.of_nat 0)) _,
        Hf : ScalarMult.B.feval_projective_coords ?acc0 = phi5 (proj1_sig ?A0),
        Hl : Datatypes.length ?tb0 = 200%nat |- _ =>
        exists acc0, tb0, A0; ssplit; [ecancel_assumption | exact Hl | exact Hf |];
        rewrite Hinv; reflexivity
      end. }
  { (* after the loop: release the scratch buffer *)
    intros t' m' ? ? ? ? ? ? ? (Ht & acc & tb & A & Hm & Hl & Hf & Ha).
    assert (Hm2 : sep (array ptsto (word.of_Z 1) p_t tb)
                    (sep (acc p5@ p_out) (sep (pP p5@ p_P) (sep (kb $@ p_k) (sep (FElem p_d d2) R)))) m')
      by (apply map_to_arr; [exact Hl | ecancel_assumption]).
    destruct Hm2 as (mS & mR & Hsplit & HmS & HmR).
    exists mR, mS; ssplit;
      [ pose proof (Array.array_1_to_anybytes _ _ _ HmS) as Hany; rewrite Hl in Hany; exact Hany
      | apply Properties.map.split_comm; exact Hsplit | ].
    cbv beta match fix delta [WeakestPrecondition.list_map WeakestPrecondition.list_map_body].
    split; [reflexivity |]. split; [congruence |].
    exists acc, A; ssplit; [ecancel_assumption | exact Hf | exact Ha]. }
Qed.


(** ** The top-level theorem

    For a group element [x] of SigmaProtocol, held at [p_P] as the image of
    [Ed.from_affine x], and a scalar [s] held at [p_k] as the 32 bytes of
    its unsigned value, [scalarmult] writes at [p_out] the image of an
    extended point [A] that is projectively equal to the extended scalar
    multiple [xsmul s (Ed.from_affine x)] (SigmaProtocol's [xmul_pos] for
    [s <> 0]) and whose affine image is [Ed.gpow_fast x s]. *)
Theorem ed25519_exec_scalarmult functions :
  map.get functions "scalarmult" = Some scalarmult ->
  map.get functions "step" = Some step ->
  map.get functions "set_identity" = Some set_identity ->
  map.get functions "pcopy" = Some pcopy ->
  map.get functions "add" = Some add ->
  map.get functions "to_cached2" = Some to_cached2 ->
  map.get functions "readd" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.readd ->
  map.get functions "double" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.double ->
  B.spec_of_fe25519_square64 functions ->
  B.spec_of_fe25519_carry_add64 functions ->
  B.spec_of_fe25519_add64 functions ->
  B.spec_of_fe25519_carry_sub64 functions ->
  B.spec_of_fe25519_sub64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  B.spec_of_fe25519_copy64 functions ->
  B.spec_of_fe25519_from_word64 functions ->
  forall (p_out p_P p_k p_d : word) (x : SP.G) (s : ZL.F) (pP : B.projective_coords)
         (d2 : felem) (kb out : list byte) (R : _ -> Prop) t m,
    m =* out $@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R ->
    Datatypes.length out = Z.to_nat (5 * felem_size) ->
    Datatypes.length kb = 32%nat ->
    le_combine kb = Zmod.unsigned s ->
    F.add Fd Fd = feval d2 -> bounded_by tight_bounds d2 ->
    B.feval_projective_coords pP = phi5 (proj1_sig (SP.from_affine (proj1_sig x))) ->
    WeakestPrecondition.call functions "scalarmult" t m [p_out; p_P; p_k; p_d]
      (fun t' m' rets => rets = [] /\ t' = t /\
         exists (a : B.projective_coords) (A : SP.xpoint),
           m' =* a p5@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
           B.feval_projective_coords a = phi5 (proj1_sig A) /\
           SXeq A (xsmul (Zmod.unsigned s) (SP.from_affine (proj1_sig x))) /\
           SP.to_affine A = proj1_sig (SP.gpow_fast x s)).
Proof.
  intros Hsm Hst Hid Hpc Hadd_fn Htc Hrd Hdbl Hsq Hcadd Hadd Hcsub Hsub Hmul Hcopy Hfw
    p_out p_P p_k p_d x s pP d2 kb out R t m Hm Hlo Hlk Hk Hd Hb HP.
  assert (Hstep : spec_of_step functions).
  { pose proof step_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; [exact Hst | | |].
    - apply double_spec_p5, ed25519_exec_double; assumption.
    - apply add_spec_ow, ed25519_exec_add_fn; assumption.
    - apply pcopy_spec_ow.
      pose proof pcopy_ok as H'; cbv [ProgramLogic.program_logic_goal_for] in H'.
      apply H'; assumption. }
  assert (Hsi : spec_of_set_identity functions).
  { pose proof set_identity_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; assumption. }
  assert (Hsmul : spec_of_scalarmult functions).
  { pose proof scalarmult_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; assumption. }
  eapply WeakestPreconditionProperties.Proper_call;
    [| apply (Hsmul p_out p_P p_k p_d (SP.from_affine (proj1_sig x)) pP d2 kb out R t m);
       ssplit; assumption].
  intros t' m' rets (Hrets & Ht & a & A & Hm' & Ha & HA).
  split; [exact Hrets |]. split; [symmetry; exact Ht |].
  rewrite SP.to_from_affine, Hk in HA.
  destruct (gpow_fast_affine x s A HA) as [Heq Haff].
  exists a, A; ssplit; assumption.
Qed.

Print Assumptions pcopy_ok.
Print Assumptions set_identity_ok.
Print Assumptions step_ok.
Print Assumptions scalarmult_ok.
Print Assumptions ed25519_exec_scalarmult.
