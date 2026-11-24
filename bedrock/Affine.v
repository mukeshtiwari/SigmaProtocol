(** Conversions between affine and extended Ed25519 points in bedrock2.

    [from_affine] writes the extended point [(x, y, 1, x, y)] of an affine
    point [(x, y)] with the synthesised [fe25519_copy] and
    [fe25519_from_word]. [to_affine] computes [(X/Z, Y/Z)] with fiat-crypto's
    verified inversion [fe25519_inv] (an addition chain for [x^(p-2)] over
    [fe25519_square] and [fe25519_mul], [AdditionChains.fe_inv_correct]) and
    [fe25519_mul]. Both are related to SigmaProtocol's [Ed.from_affine] and
    [Ed.to_affine] through [phi2] and [phi5]. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Crypto.Algebra.Field.
Require Import coqutil.Tactics.syntactic_unify.
From Stdlib Require Import Zmod.
Require Crypto.Bedrock.Group.AdditionChains.
Require Import Bridge.FieldTransport.
Import ProgramLogic.Coercions ListNotations.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.
Module AddC := Crypto.Bedrock.Group.AdditionChains.

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

(** ** [from_affine] *)

Definition from_affine := func! (p_out, p_x, p_y) {
  fe25519_copy(p_out.X, p_x);
  fe25519_copy(p_out.Y, p_y);
  fe25519_from_word(p_out.Z, $1);
  fe25519_copy(p_out.Ta, p_x);
  fe25519_copy(p_out.Tb, p_y)
}.

#[local] Existing Instances B.spec_of_fe25519_copy64 B.spec_of_fe25519_from_word64.

(** [(x, y, 1, x, y)] satisfies the extended-coordinate invariants when
    [(x, y)] is on the curve. *)
Lemma from_affine_valid_F (X Y Z : F Crypto.Spec.Curve25519.p) :
  F.add (F.mul Fa (F.mul X X)) (F.mul Y Y) =
  F.add F.one (F.mul (F.mul Fd (F.mul X X)) (F.mul Y Y)) ->
  Z = F.one ->
  F.add (F.mul (F.mul Fa (F.mul X X)) (F.mul Z Z)) (F.mul (F.mul Y Y) (F.mul Z Z)) =
  F.add (F.mul (F.mul Z Z) (F.mul Z Z)) (F.mul (F.mul Fd (F.mul X X)) (F.mul Y Y)) /\
  F.mul X Y = F.mul (F.mul Z X) Y /\ Z <> F.zero.
Proof.
  intros h ->; split; [| split].
  - transitivity (F.add (F.mul Fa (F.mul X X)) (F.mul Y Y)); [ring |].
    rewrite h; ring.
  - ring.
  - Decidable.vm_decide.
Qed.

Lemma from_affine_valid (x y z : felem) :
  F.add (F.mul Fa (F.mul (feval x) (feval x))) (F.mul (feval y) (feval y)) =
  F.add F.one (F.mul (F.mul Fd (F.mul (feval x) (feval x))) (F.mul (feval y) (feval y))) ->
  feval z = F.one ->
  B.valid_projective_coords x y z x y.
Proof. exact (from_affine_valid_F (feval x) (feval y) (feval z)). Qed.

Lemma feval_one_word : F.of_Z Crypto.Spec.Curve25519.p (word.unsigned (word.of_Z 1 : word)) = F.one.
Proof. reflexivity. Qed.

Global Instance spec_of_from_affine64 : spec_of "from_affine" :=
  fnspec! "from_affine"
    (p_out p_x p_y: word) /
    (P : Apoint) (x y: felem) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * FElem p_x x * FElem p_y y * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        bounded_by tight_bounds x /\ bounded_by tight_bounds y /\
        proj1_sig P = (feval x, feval y);
      ensures t' m' :=
        t = t' /\
        exists a : B.projective_coords,
          m' =* a p5@ p_out * FElem p_x x * FElem p_y y * R /\
          B.feval_projective_coords a = from_affine_coords F.one (proj1_sig P)
  }.

Lemma from_affine64_ok : program_logic_goal_for_function! from_affine.
Proof.
  repeat straightline.
  lazymatch goal with HP : proj1_sig P = _ |- _ =>
    destruct P as [[px py] hP]; cbn [proj1_sig] in HP |- *; inversion HP; subst px py; clear HP
  end.
  pose proof BasicC64Semantics.wordok as Hwok.
  split_at out p_out 40%nat 40 H4.
  split_at (ListDef.skipn 40 out) (p_out .+ 40) 40%nat 40 H4.
  split_at (ListDef.skipn 80 out) (p_out .+ 80) 40%nat 40 H4.
  split_at (ListDef.skipn 120 out) (p_out .+ 120) 40%nat 40 H4.
  repeat straightline.
  repeat single_step.
  repeat straightline.
  (* The output is [(x, y, z, x, y)] with [z] the result of
     [fe25519_from_word]. *)
  lazymatch goal with Hz : feval (felem_to_list ?z) = F.of_Z _ _ |- _ =>
    unshelve eexists (exist _ (x, y, z, x, y) _);
    [ split; [ apply from_affine_valid; [exact hP | rewrite Hz; reflexivity]
             | ssplit; solve_bounds ]
    | split; [ lazy beta iota delta [proj1_sig]; ecancel_assumption
             | lazy [B.feval_projective_coords proj1_sig from_affine_coords];
               rewrite Hz; reflexivity ] ]
  end.
Qed.

(** *** Against SigmaProtocol's points

    If the limbs at [p_x] and [p_y] represent the coordinates of the affine
    point [P], the output limbs represent [Ed.from_affine P]. *)
Definition spec_of_from_affine_sigma : spec_of "from_affine" :=
  fnspec! "from_affine"
    (p_out p_x p_y: word) /
    (P : SP.point) (x y: felem) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * FElem p_x x * FElem p_y y * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        bounded_by tight_bounds x /\ bounded_by tight_bounds y /\
        phi2 (proj1_sig P) = (feval x, feval y);
      ensures t' m' :=
        t = t' /\
        exists a : B.projective_coords,
          m' =* a p5@ p_out * FElem p_x x * FElem p_y y * R /\
          B.feval_projective_coords a = phi5 (proj1_sig (SP.from_affine P))
  }.

Lemma from_affine_spec_sigma functions :
  spec_of_from_affine64 functions -> spec_of_from_affine_sigma functions.
Proof.
  intros H p_out p_x p_y P x y out R t m (Hm & Hlen & Hx & Hy & HP).
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (H p_out p_x p_y (phiA P) x y out R t m); ssplit; assumption ].
  intros t' m' rets (Hrets & Ht & a & Hm' & Ha).
  split; [exact Hrets |]. split; [exact Ht |].
  exists a; split; [exact Hm' |].
  rewrite Ha, SP_from_affine_coords, from_affine_coords_phi; reflexivity.
Qed.

(** [ed25519_exec_from_affine]: if the environment maps "from_affine" to
    the bedrock2 function and [fe25519_copy] and [fe25519_from_word] meet
    AUCurves' 64-bit specifications, a call of [from_affine] satisfies
    [spec_of_from_affine_sigma]. *)
Theorem ed25519_exec_from_affine functions :
  map.get functions "from_affine" = Some from_affine ->
  B.spec_of_fe25519_copy64 functions ->
  B.spec_of_fe25519_from_word64 functions ->
  spec_of_from_affine_sigma functions.
Proof.
  intros Henv Hcopy Hfw.
  apply from_affine_spec_sigma.
  pose proof from_affine64_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; assumption.
Qed.


(** ** Field inversion

    fiat-crypto's [fe25519_inv], instantiated at AUCurves' 64-bit field.
    [AdditionChains.fe_inv_correct] states its result as [x^(2^255-21)]
    with the bounded-felem predicate of [Compilation2]; [spec_of_fe25519_inv64]
    restates it with [F.inv] (Fermat) and the plain [FElem] of the other
    specifications. The specification of [fe_inv_correct] leaves the
    limbs at [p_x] determined only up to [feval] and bounds, so the
    restatement does as well. *)
Definition fe25519_inv : Syntax.func :=
  AddC.fe25519_inv (word:=BasicC64Semantics.word) (field_parameters:=field_parameters).

Global Instance spec_of_fe25519_inv64 : spec_of "fe25519_inv" :=
  fnspec! "fe25519_inv"
    (p_out p_x: word) / (x old: felem) (R: _ -> Prop), {
      requires t m :=
        m =* FElem p_x x * FElem p_out old * R /\
        bounded_by tight_bounds x;
      ensures t' m' :=
        t = t' /\
        exists x' y : felem,
          feval x' = feval x /\ bounded_by tight_bounds x' /\
          feval y = F.inv (feval x) /\ bounded_by tight_bounds y /\
          m' =* FElem p_x x' * FElem p_out y * R
  }.

Lemma inv_exp (x : F Crypto.Spec.Curve25519.p) : AddC.exp (2^255-21) x = F.inv x.
Proof.
  unfold AddC.exp.
  rewrite (Crypto.Arithmetic.PrimeFieldTheorems.F.Fq_inv_fermat
             (prime_q := Crypto.Spec.Curve25519.prime_p) (two_lt_q := ltac:(vm_compute; reflexivity))).
  reflexivity.
Qed.

Lemma to_C2 (bnd : option bounds) (p : word) (x : felem) :
  Crypto.Bedrock.Field.Interface.Compilation2.maybe_bounded bnd x ->
  Lift1Prop.impl1 (FElem p x)
    (Crypto.Bedrock.Field.Interface.Compilation2.FElem bnd p (feval x)).
Proof.
  intros hb m H; exists x.
  apply sep_emp_l; split; [split; [reflexivity | exact hb] | exact H].
Qed.

Lemma fe25519_inv_ok64 functions :
  map.get functions "fe25519_inv" = Some fe25519_inv ->
  B.spec_of_fe25519_square64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  spec_of_fe25519_inv64 functions.
Proof.
  intros Hget Hsq Hmul p_out p_x x old R t m (Hm & Hb).
  pose proof (AddC.fe_inv_correct (field_parameters:=field_parameters)
                (field_representaton:=frep25519) ltac:(vm_compute; reflexivity)
                functions Hget Hsq Hmul) as H.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (H p_out p_x (feval old) (feval x) R t m) ].
  - intros t' m' rets (Hrets & Ht & Hm').
    split; [exact Hrets |]. split; [exact Ht |].
    cbv [Crypto.Bedrock.Field.Interface.Compilation2.FElem] in Hm'.
    extract_ex1_and_emp_in Hm'.
    destruct Hm'_emp0 as [e0 b0], Hm'_emp1 as [e1 b1].
    exists v', v'0; ssplit; [exact e0 | exact b0 | rewrite e1; apply inv_exp | exact b1 |].
    ecancel_assumption.
  - refine (Proper_sep_impl1 _ _ _ _ _ _ _ Hm); [| reflexivity].
    refine (Proper_sep_impl1 _ _ _ _ _ _); apply to_C2; [exact Hb | exact I].
Qed.

(** ** [to_affine]

    The first output slot receives a copy of [Z], which [fe25519_inv]
    inverts into the second slot; the two multiplications then overwrite
    both slots. The input point is left unchanged. *)
Definition to_affine := func! (p_out, p_a) {
  fe25519_copy(p_out, p_a.Z);
  fe25519_inv(p_out + $40, p_out);
  fe25519_mul(p_out, p_a.X, p_out + $40);
  fe25519_mul(p_out + $40, p_a.Y, p_out + $40)
}.

#[local] Existing Instances B.spec_of_fe25519_mul64 spec_of_fe25519_inv64.

Global Instance spec_of_to_affine64 : spec_of "to_affine" :=
  fnspec! "to_affine"
    (p_out p_a: word) /
    (a: B.projective_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (2 * felem_size);
      ensures t' m' :=
        t = t' /\
        exists x y : felem,
          m' =* FElem p_out x * FElem (p_out .+ felem_size) y * a p5@ p_a * R /\
          bounded_by tight_bounds x /\ bounded_by tight_bounds y /\
          (feval x, feval y) = to_affine_coords F.mul F.inv (B.feval_projective_coords a)
  }.

Lemma to_affine64_ok : program_logic_goal_for_function! to_affine.
Proof.
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub
      bin_carry_sub un_outbounds bin_outbounds].
  repeat straightline.
  destruct_points.
  pose proof BasicC64Semantics.wordok as Hwok.
  lazymatch goal with H : context [out $@ p_out] |- _ =>
    split_at out p_out 40%nat 40 H;
    B.convert_chunk_to_felem (p_out .+ 40) (ListDef.skipn 40 out) H
  end.
  repeat single_step.
  repeat straightline.
  lazymatch goal with
  | Hx : feval (felem_to_list ?x) = bin_model _ _, Hbx : bounded_by bin_outbounds (felem_to_list ?x),
    Hy : feval (felem_to_list ?y) = bin_model _ _, Hby : bounded_by bin_outbounds (felem_to_list ?y),
    Hi : feval _ = F.inv _ |- _ =>
      assert_fails (unify x y);
      exists x, y; ssplit;
      [ ecancel_assumption | exact Hbx | exact Hby
      | lazy [to_affine_coords B.feval_projective_coords proj1_sig bin_model bin_mul];
        rewrite Hx, Hy, Hi; reflexivity ]
  end.
Qed.

(** *** Against SigmaProtocol's points

    If the limbs at [p_a] represent the extended point [Q], the output
    limbs represent the coordinates of [Ed.to_affine Q]. *)
Definition spec_of_to_affine_sigma : spec_of "to_affine" :=
  fnspec! "to_affine"
    (p_out p_a: word) /
    (Q : SP.xpoint) (a: B.projective_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (2 * felem_size) /\
        B.feval_projective_coords a = phi5 (proj1_sig Q);
      ensures t' m' :=
        t = t' /\
        exists x y : felem,
          m' =* FElem p_out x * FElem (p_out .+ felem_size) y * a p5@ p_a * R /\
          bounded_by tight_bounds x /\ bounded_by tight_bounds y /\
          (feval x, feval y) = phi2 (proj1_sig (SP.to_affine Q))
  }.

Lemma to_affine_spec_sigma functions :
  spec_of_to_affine64 functions -> spec_of_to_affine_sigma functions.
Proof.
  intros H p_out p_a Q a out R t m (Hm & Hlen & Ha).
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (H p_out p_a a out R t m (conj Hm Hlen)) ].
  intros t' m' rets (Hrets & Ht & x & y & Hm' & Hx & Hy & Hxy).
  split; [exact Hrets |]. split; [exact Ht |].
  exists x, y; ssplit; [exact Hm' | exact Hx | exact Hy |].
  rewrite Hxy, Ha, SP_to_affine_coords, to_affine_coords_phi; reflexivity.
Qed.

(** [ed25519_exec_to_affine]: if the environment maps "to_affine" and
    "fe25519_inv" to the bedrock2 functions and [fe25519_copy],
    [fe25519_square] and [fe25519_mul] meet AUCurves' 64-bit
    specifications, a call of [to_affine] satisfies
    [spec_of_to_affine_sigma]. *)
Theorem ed25519_exec_to_affine functions :
  map.get functions "to_affine" = Some to_affine ->
  map.get functions "fe25519_inv" = Some fe25519_inv ->
  B.spec_of_fe25519_copy64 functions ->
  B.spec_of_fe25519_square64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  spec_of_to_affine_sigma functions.
Proof.
  intros Henv Hinv Hcopy Hsq Hmul.
  apply to_affine_spec_sigma.
  pose proof to_affine64_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; first [assumption | apply fe25519_inv_ok64; assumption].
Qed.

Print Assumptions from_affine64_ok.
Print Assumptions ed25519_exec_from_affine.
Print Assumptions fe25519_inv_ok64.
Print Assumptions to_affine64_ok.
Print Assumptions ed25519_exec_to_affine.
