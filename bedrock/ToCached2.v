(** Third bridge theorem: a halving-free cached-point preparation in
    bedrock2, so that the addition of two run-time extended points runs
    entirely in bedrock2 with AUCurves' verified [readd].

    AUCurves' [to_cached] computes [((Y-X)/2, (Y+X)/2, Z, d Ta Tb)] and
    calls a field halving for which no implementation exists. The function
    [to_cached2] below computes [(Y-X, Y+X, 2Z, 2d Ta Tb)] with the
    synthesised [fe25519_sub], [fe25519_add] and [fe25519_mul] only; these
    are the cached coordinates of the representative [(2X, 2Y, 2Z, 2Ta, Tb)]
    of the same projective point. The constant [2d] is an input buffer, as
    [d] is for [to_cached]. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Crypto.Algebra.Field.
Require Import coqutil.Tactics.syntactic_unify.
From Stdlib Require Import Zmod.
Require Import Bridge.FieldTransport Bridge.ExecReadd.
Import ProgramLogic.Coercions ListNotations.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.

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

(** ** The program

    The output layout is that of [to_cached] and of the cached operand of
    [readd]. The outputs of [fe25519_sub] and [fe25519_add] have loose
    bounds, that of [fe25519_mul] tight bounds; [readd] requires loose
    bounds on all four cached coordinates, so no carry is needed. *)
Definition to_cached2 := func! (p_out, p_a, p_d) {
  fe25519_sub(p_out.half_YmX, p_a.Y, p_a.X);
  fe25519_add(p_out.half_YpX, p_a.Y, p_a.X);
  fe25519_add(p_out.Z, p_a.Z, p_a.Z);
  fe25519_mul(p_out.Td, p_a.Ta, p_a.Tb);
  fe25519_mul(p_out.Td, p_out.Td, p_d)
}.

#[local] Existing Instances B.spec_of_fe25519_sub64 B.spec_of_fe25519_add64
  B.spec_of_fe25519_mul64.

(** ** The scaled representative over AUCurves' field *)

Local Notation Fa := Crypto.Spec.Curve25519.E.a.
Local Notation Fd := Crypto.Spec.Curve25519.E.d.
Local Notation point := (@Extended.point _ Logic.eq F.zero F.add F.mul Fa Fd).
Local Notation m1_prep :=
  (Readdition.m1_prep (a:=Fa) (d:=Fd)
     (nonzero_a:=Crypto.Spec.Curve25519.E.nonzero_a)
     (a_eq_minus1:=B.a_eq_minus1)
     (twice_d:=B.twice_d)
     (k_eq_2d:=B.k_eq_2d)
     (nonzero_d:=B.nonzero_d)).

(* Field facts for [scale2], with the curve constants as variables. *)
Add Ring Fp_ring : (Crypto.Arithmetic.ModularArithmeticTheorems.F.ring_theory Crypto.Spec.Curve25519.p).

Lemma double_mul (x : F Crypto.Spec.Curve25519.p) : F.add x x = F.mul (F.add F.one F.one) x.
Proof. ring. Qed.

Lemma scale2_curve (A D X Y Z : F Crypto.Spec.Curve25519.p) :
  F.add (F.mul (F.mul A (F.mul X X)) (F.mul Z Z)) (F.mul (F.mul Y Y) (F.mul Z Z)) =
  F.add (F.mul (F.mul Z Z) (F.mul Z Z)) (F.mul (F.mul D (F.mul X X)) (F.mul Y Y)) ->
  let X2 := F.add X X in let Y2 := F.add Y Y in let Z2 := F.add Z Z in
  F.add (F.mul (F.mul A (F.mul X2 X2)) (F.mul Z2 Z2)) (F.mul (F.mul Y2 Y2) (F.mul Z2 Z2)) =
  F.add (F.mul (F.mul Z2 Z2) (F.mul Z2 Z2)) (F.mul (F.mul D (F.mul X2 X2)) (F.mul Y2 Y2)).
Proof.
  intros h X2 Y2 Z2; subst X2 Y2 Z2.
  rewrite !(double_mul X), !(double_mul Y), !(double_mul Z).
  set (t := F.add F.one F.one).
  transitivity (F.mul (F.mul (F.mul t t) (F.mul t t))
    (F.add (F.mul (F.mul A (F.mul X X)) (F.mul Z Z)) (F.mul (F.mul Y Y) (F.mul Z Z))));
    [ring | rewrite h; ring].
Qed.

Lemma scale2_t (X Y Z Ta Tb : F Crypto.Spec.Curve25519.p) :
  F.mul X Y = F.mul (F.mul Z Ta) Tb ->
  F.mul (F.add X X) (F.add Y Y) = F.mul (F.mul (F.add Z Z) (F.add Ta Ta)) Tb.
Proof.
  intro h; rewrite !(double_mul X), !(double_mul Y), !(double_mul Z), !(double_mul Ta).
  set (t := F.add F.one F.one).
  transitivity (F.mul (F.mul t t) (F.mul X Y)); [ring | rewrite h; ring].
Qed.

Lemma scale2_z (Z : F Crypto.Spec.Curve25519.p) : Z <> F.zero -> F.add Z Z <> F.zero.
Proof. intro h; Crypto.Algebra.Field.fsatz. Qed.

Lemma half_of (u w : F Crypto.Spec.Curve25519.p) :
  u = F.add w w -> F.div u (F.add F.one F.one) = w.
Proof.
  intro h; subst u; unfold F.div.
  assert (h2 : F.add F.one F.one <> F.zero (m:=Crypto.Spec.Curve25519.p)) by Decidable.vm_decide.
  transitivity (F.mul w (F.mul (F.add F.one F.one) (F.inv (F.add F.one F.one)))); [ring |].
  rewrite (Crypto.Algebra.Field.right_multiplicative_inverse _ h2); ring.
Qed.

(** [(2X, 2Y, 2Z, 2Ta, Tb)] represents the same projective point as
    [(X, Y, Z, Ta, Tb)]. *)
Definition scale2 (P : point) : point.
Proof.
  refine (exist _ (let '(X, Y, Z, Ta, Tb) := proj1_sig P in
                   (F.add X X, F.add Y Y, F.add Z Z, F.add Ta Ta, Tb)) _).
  abstract (destruct P as [[[[[X Y] Z] Ta] Tb] (h1 & h2 & h3)]; cbn [proj1_sig];
            split; [| split]; [apply scale2_curve | apply scale2_t | apply scale2_z]; assumption).
Defined.

(** The cached coordinates of the scaled representative are those that
    [to_cached2] computes. *)
Lemma m1_prep_scale2 (P : point) :
  proj1_sig (m1_prep (scale2 P)) =
  (let '(X, Y, Z, Ta, Tb) := proj1_sig P in
   (F.sub Y X, F.add Y X, F.add Z Z, F.mul (F.mul Ta Tb) (F.add Fd Fd))).
Proof.
  destruct P as [[[[[X Y] Z] Ta] Tb] hP].
  cbv [Readdition.m1_prep scale2 proj1_sig]; clear hP.
  generalize Fd; intro D.
  apply (f_equal2 pair); [apply (f_equal2 pair); [apply (f_equal2 pair) |] |].
  - apply half_of; ring.
  - apply half_of; ring.
  - reflexivity.
  - ring.
Qed.

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

(** ** Specification and proof against AUCurves' coordinates

    As [spec_of_to_cached64], with [2d] in place of [d] at [p_d], and the
    output the cached coordinates of the scaled representative. *)
Global Instance spec_of_to_cached2_64 : spec_of "to_cached2" :=
  fnspec! "to_cached2"
    (p_out p_a p_d: word) /
    (a: B.projective_coords) (d2: felem) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * FElem p_d d2 * R /\
        Datatypes.length out = Z.to_nat (4 * felem_size) /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2;
      ensures t' m' :=
        t = t' /\
        exists a_cached: B.cached_coords,
          m' =* a_cached p4@ p_out * a p5@ p_a * FElem p_d d2 * R /\
          proj1_sig (m1_prep (scale2 (B.coords_to_point a))) = B.feval_cached_coords a_cached
  }.

Lemma to_cached2_64_ok : program_logic_goal_for_function! to_cached2.
Proof.
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_carry_add bin_sub
      bin_carry_sub un_outbounds bin_outbounds].
  repeat straightline.
  pose proof (B.cached_implies_coords_valid (m1_prep (scale2 (B.coords_to_point a)))) as HPost.
  destruct_points.
  B.split_output_stack out p_out 4.
  repeat straightline.
  match goal with H : context [ListDef.firstn 40 out] |- _ => B.convert_4_chunks p_out out H end.
  repeat single_step.
  repeat straightline.
  lazy delta [B.cached_coords].
  unshelve eexists.
  eexists (_, _, _, _).
  2: split; [solve_mem|].
  ssplit; try solve_bounds.
  apply HPost.
  (* Both remaining goals equate the cached coordinates of the scaled
     representative with the output limbs; [lazy] first removes the
     proof term inside the output sig before rewriting. *)
  all: lazymatch goal with |- context [m1_prep (scale2 ?P)] =>
         etransitivity; [exact (m1_prep_scale2 P) |] end;
       lazy [B.coords_to_point B.feval_projective_coords B.feval_cached_coords
             bin_model bin_mul bin_add bin_sub proj1_sig];
       match goal with H : F.add _ _ = feval _ |- _ => rewrite H end;
       repeat match goal with H : feval (felem_to_list _) = _ |- _ => rewrite H end;
       lazy [bin_model bin_mul bin_add bin_sub];
       reflexivity.
Qed.

(** ** The scaled representative of a SigmaProtocol point *)

Definition scale5 {T} (add : T -> T -> T) (c : T * T * T * T * T) : T * T * T * T * T :=
  let '(X, Y, Z, Ta, Tb) := c in (add X X, add Y Y, add Z Z, add Ta Ta, Tb).

Lemma psi_phi x : psi (phi x) = x.
Proof. apply phi_inj; rewrite phi_psi; reflexivity. Qed.

(** [xscale2 Q] has the coordinates [(2X, 2Y, 2Z, 2Ta, Tb)] of [Q]. *)
Definition xscale2 (Q : SP.xpoint) : SP.xpoint := psiX (scale2 (phiX Q)).

Lemma xscale2_coords (Q : SP.xpoint) :
  proj1_sig (xscale2 Q) = scale5 Zmod.add (proj1_sig Q).
Proof.
  destruct Q as [[[[[X Y] Z] Ta] Tb] hQ].
  cbv [xscale2 psiX phiX scale2 proj1_sig psi5 phi5 scale5].
  rewrite <-!phi_add, !psi_phi; reflexivity.
Qed.

Lemma xscale2_eq (Q : SP.xpoint) : SXeq (xscale2 Q) Q.
Proof.
  apply SXeq_of_AXeq.
  eapply AXeq_coords; [symmetry; apply phiX_psiX | reflexivity |].
  destruct Q as [[[[[X Y] Z] Ta] Tb] hQ].
  cbv [AX.eq scale2 phiX proj1_sig phi5].
  split; ring.
Qed.

(** The cached coordinates of [xscale2 Q], read through [phi], are the
    coordinates that [to_cached2] computes from those of [Q]. *)
Lemma xprep_xscale2 (Q : SP.xpoint) :
  phi4 (xprep (xscale2 Q)) = proj1_sig (m1_prep (scale2 (phiX Q))).
Proof.
  unfold xprep; rewrite prep_coords_phi.
  change (phi5 (proj1_sig (xscale2 Q))) with (proj1_sig (phiX (xscale2 Q))).
  unfold xscale2; rewrite phiX_psiX.
  generalize (scale2 (phiX Q)); intros [[[[[X Y] Z] Ta] Tb] h]; reflexivity.
Qed.

(** [m1_prep (scale2 _)] depends on the coordinates only. *)
Lemma m1_prep_scale2_coords (P1 P2 : point) :
  proj1_sig P1 = proj1_sig P2 ->
  proj1_sig (m1_prep (scale2 P1)) = proj1_sig (m1_prep (scale2 P2)).
Proof. intro h; rewrite !m1_prep_scale2, h; reflexivity. Qed.

(** ** Specification against SigmaProtocol's points

    If the limbs at [p_a] represent the extended point [Q], the output
    limbs hold [xprep Q'] for the representative [Q'] of [Q] with
    coordinates [(2X, 2Y, 2Z, 2Ta, Tb)]; this is the precondition on the
    cached operand of [spec_of_readd_sigma]. *)
Definition spec_of_to_cached2_sigma : spec_of "to_cached2" :=
  fnspec! "to_cached2"
    (p_out p_a p_d: word) /
    (Q : SP.xpoint) (a: B.projective_coords) (d2: felem) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * FElem p_d d2 * R /\
        Datatypes.length out = Z.to_nat (4 * felem_size) /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2 /\
        B.feval_projective_coords a = phi5 (proj1_sig Q);
      ensures t' m' :=
        t = t' /\
        exists c : B.cached_coords,
          m' =* c p4@ p_out * a p5@ p_a * FElem p_d d2 * R /\
          exists Q' : SP.xpoint,
            proj1_sig Q' = scale5 Zmod.add (proj1_sig Q) /\
            SXeq Q' Q /\
            B.feval_cached_coords c = phi4 (xprep Q')
  }.

Lemma to_cached2_spec_sigma functions :
  spec_of_to_cached2_64 functions -> spec_of_to_cached2_sigma functions.
Proof.
  intros H p_out p_a p_d Q a d2 out R t m (Hm & Hlen & Hd & Hb & Ha).
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (H p_out p_a p_d a d2 out R t m (conj Hm (conj Hlen (conj Hd Hb)))) ].
  intros t' m' rets (Hrets & Ht & c & Hm' & Hc).
  split; [exact Hrets |].
  split; [exact Ht |].
  exists c; split; [exact Hm' |].
  exists (xscale2 Q).
  split; [apply xscale2_coords |].
  split; [apply xscale2_eq |].
  rewrite <-Hc, xprep_xscale2.
  apply m1_prep_scale2_coords; exact Ha.
Qed.

(** [ed25519_exec_to_cached2]: if the environment maps "to_cached2" to
    the bedrock2 function and the field operations it calls meet
    AUCurves' 64-bit specifications, a call of [to_cached2] satisfies
    [spec_of_to_cached2_sigma]. *)
Theorem ed25519_exec_to_cached2 functions :
  map.get functions "to_cached2" = Some to_cached2 ->
  B.spec_of_fe25519_sub64 functions ->
  B.spec_of_fe25519_add64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  spec_of_to_cached2_sigma functions.
Proof.
  intros Henv Hsub Hadd Hmul.
  apply to_cached2_spec_sigma.
  pose proof to_cached2_64_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; assumption.
Qed.

(** ** Addition of two run-time points *)

Lemma cross_mul (x1 z1 x2 z2 : F Crypto.Spec.Curve25519.p) :
  z1 <> F.zero -> z2 <> F.zero ->
  F.mul x1 (F.inv z1) = F.mul x2 (F.inv z2) -> F.mul z2 x1 = F.mul z1 x2.
Proof.
  intros n1 n2 h.
  transitivity (F.mul (F.mul z1 z2) (F.mul x1 (F.inv z1))).
  - transitivity (F.mul (F.mul z2 x1) (F.mul z1 (F.inv z1)));
      [rewrite (Crypto.Algebra.Field.right_multiplicative_inverse _ n1); ring | ring].
  - rewrite h.
    transitivity (F.mul (F.mul z1 x2) (F.mul z2 (F.inv z2)));
      [ring | rewrite (Crypto.Algebra.Field.right_multiplicative_inverse _ n2); ring].
Qed.

(** Projective equality follows from equality of the affine images. *)
Lemma SXeq_of_to_affine (R S : SP.xpoint) :
  SP.to_affine R = SP.to_affine S -> SXeq R S.
Proof.
  destruct R as [[[[[X1 Y1] Z1] Ta1] Tb1] (h1 & h2 & h3)],
           S as [[[[[X2 Y2] Z2] Ta2] Tb2] (k1 & k2 & k3)].
  intro h; apply (f_equal (@proj1_sig _ _)) in h.
  cbv [SP.to_affine SX.to_affine SX.eq proj1_sig] in h |- *.
  pose proof (f_equal fst h) as hx; pose proof (f_equal snd h) as hy.
  cbn [fst snd] in hx, hy; clear h h1 h2 k1 k2.
  apply (f_equal phi) in hx, hy; rewrite !phi_mul, !phi_inv in hx, hy.
  split; apply phi_inj; rewrite !phi_mul; apply cross_mul;
    try (apply phi_nonzero; assumption); assumption.
Qed.

(** The point [S] that [readd] returns for the cached operand [xprep Q']
    of a representative [Q'] of [Q] is projectively equal to
    [Ed.xadd P Q]. *)
Lemma readd_representative (P Q Q' S : SP.xpoint) :
  SXeq Q' Q -> SXeq S (SP.xadd P Q') ->
  SXeq S (SP.xadd P Q) /\ SP.to_affine S = SP.padd (SP.to_affine P) (SP.to_affine Q).
Proof.
  intros hQ hS.
  assert (ha : SP.to_affine S = SP.padd (SP.to_affine P) (SP.to_affine Q)).
  { rewrite (readd_affine _ _ _ hS), (SXeq_to_affine _ _ hQ); reflexivity. }
  split; [| exact ha].
  apply SXeq_of_to_affine; rewrite ha, SP.to_affine_xadd; reflexivity.
Qed.

(** [ed25519_exec_add]: [to_cached2] on the limbs of [Q] (into the
    buffer at [p_c]) followed by [readd] on those of [P] and the cached
    result writes at [p_out] the image of a point [S] projectively equal
    to [Ed.xadd P Q], whose affine image is [padd] of those of [P] and
    [Q]. The hypotheses are the two specifications; [ed25519_exec_to_cached2]
    and [ed25519_exec_readd] discharge them from the bedrock2 code. *)
Theorem ed25519_exec_add functions :
  spec_of_to_cached2_sigma functions ->
  spec_of_readd_sigma functions ->
  forall (p_out p_a p_b p_c p_d : word) (P Q : SP.xpoint)
         (a b : B.projective_coords) (d2 : felem) (out cbuf : list byte)
         (R : _ -> Prop) t m,
    m =* out $@ p_out * cbuf $@ p_c * a p5@ p_a * b p5@ p_b * FElem p_d d2 * R ->
    Datatypes.length out = Z.to_nat (5 * felem_size) ->
    Datatypes.length cbuf = Z.to_nat (4 * felem_size) ->
    F.add Fd Fd = feval d2 -> bounded_by tight_bounds d2 ->
    B.feval_projective_coords a = phi5 (proj1_sig P) ->
    B.feval_projective_coords b = phi5 (proj1_sig Q) ->
    WeakestPrecondition.call functions "to_cached2" t m [p_c; p_b; p_d]
      (fun t1 m1 rets1 => rets1 = [] /\ t1 = t /\
         WeakestPrecondition.call functions "readd" t1 m1 [p_out; p_a; p_c]
           (fun t2 m2 rets2 => rets2 = [] /\ t2 = t /\
              exists (c : B.cached_coords) (s : B.projective_coords) (S : SP.xpoint),
                m2 =* s p5@ p_out * c p4@ p_c * a p5@ p_a * b p5@ p_b * FElem p_d d2 * R /\
                B.feval_projective_coords s = phi5 (proj1_sig S) /\
                SXeq S (SP.xadd P Q) /\
                SP.to_affine S = SP.padd (SP.to_affine P) (SP.to_affine Q))).
Proof.
  intros Hc Hr p_out p_a p_b p_c p_d P Q a b d2 out cbuf R t m Hm Hlo Hlc Hd Hb Ha HbQ.
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (Hc p_c p_b p_d Q b d2 cbuf (sep (sep (out $@ p_out) (a p5@ p_a)) R) t m);
        ssplit; [ecancel_assumption | assumption ..] ].
  intros t1 m1 rets1 (Hrets1 & Ht1 & c & Hm1 & Q' & _ & HQ' & Hcc).
  split; [exact Hrets1 |]. split; [symmetry; exact Ht1 |].
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (Hr p_out p_a p_c P Q' a c out
                 (sep (sep (b p5@ p_b) (FElem p_d d2)) R) t1 m1);
        ssplit; [ecancel_assumption | assumption ..] ].
  intros t2 m2 rets2 (Hrets2 & Ht2 & s & Hm2 & S & Hs & HS & _).
  split; [exact Hrets2 |]. split; [subst; reflexivity |].
  destruct (readd_representative P Q Q' S HQ' HS) as [HSeq Haff].
  exists c, s, S; ssplit; [ecancel_assumption | exact Hs | exact HSeq | exact Haff].
Qed.

(** ** A bedrock2 function for the addition of two run-time points

    [add] prepares the second operand with [to_cached2] in a stack buffer
    and calls [readd]. *)
Definition add := func! (p_out, p_a, p_b, p_d) {
  stackalloc 160 as p_c;
  to_cached2(p_c, p_b, p_d);
  readd(p_out, p_a, p_c)
}.

#[local] Existing Instances spec_of_to_cached2_sigma spec_of_readd_sigma.

Global Instance spec_of_add_sigma : spec_of "add" :=
  fnspec! "add"
    (p_out p_a p_b p_d: word) /
    (P Q : SP.xpoint) (a b: B.projective_coords) (d2: felem) (out : list byte)
    (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * b p5@ p_b * FElem p_d d2 * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
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

Lemma array_app40 (p q : word) (xs ys : list byte) :
  Datatypes.length xs = 40%nat -> q = word.add p (word.of_Z 40) ->
  Lift1Prop.iff1 (array ptsto (word.of_Z 1) p (xs ++ ys))
                 (sep (array ptsto (word.of_Z 1) p xs) (array ptsto (word.of_Z 1) q ys)).
Proof.
  intros hl hq; subst q.
  etransitivity; [apply Array.array_append |].
  rewrite hl.
  replace (word.add p (word.of_Z (word.unsigned (word.of_Z 1) * Z.of_nat 40)))
    with (word.add p (word.of_Z 40)) by ZnWords.
  reflexivity.
Qed.

Lemma add_40_40 (p : word) (n : Z) :
  word.add p (word.of_Z (n + 40)) = word.add (word.add p (word.of_Z n)) (word.of_Z 40).
Proof.
  rewrite coqutil.Word.Properties.word.ring_morph_add,
    coqutil.Word.Properties.word.add_assoc; reflexivity.
Qed.

Lemma array_app40_4 (p : word) (b1 b2 b3 b4 : list byte) :
  Datatypes.length b1 = 40%nat -> Datatypes.length b2 = 40%nat ->
  Datatypes.length b3 = 40%nat ->
  Lift1Prop.iff1 (array ptsto (word.of_Z 1) p (b1 ++ b2 ++ b3 ++ b4))
    (sep (sep (sep (array ptsto (word.of_Z 1) p b1)
                   (array ptsto (word.of_Z 1) (p .+ felem_size) b2))
              (array ptsto (word.of_Z 1) (p .+ (felem_size + felem_size)) b3))
         (array ptsto (word.of_Z 1) (p .+ (felem_size + felem_size + felem_size)) b4)).
Proof.
  intros h1 h2 h3.
  rewrite (array_app40 p (p .+ felem_size) b1 _ h1 eq_refl).
  rewrite (array_app40 (p .+ felem_size) (p .+ (felem_size + felem_size)) b2 _ h2
             (add_40_40 p 40)).
  rewrite (array_app40 (p .+ (felem_size + felem_size))
             (p .+ (felem_size + felem_size + felem_size)) b3 _ h3 (add_40_40 p (40 + 40))).
  cancel.
Qed.

(** The memory of a cached point is 160 bytes. *)
Lemma cached_to_anybytes (c : B.cached_coords) (p : word) m :
  (c p4@ p) m -> Memory.anybytes p 160 m.
Proof.
  destruct c as [[[[c1 c2] c3] c4] hc]; cbn [proj1_sig]; intro H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) p c1) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) (p .+ felem_size) c2) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) (p .+ (felem_size + felem_size)) c3) H.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519)
                   (p .+ (felem_size + felem_size + felem_size)) c4) H.
  pose proof (ws2bs_felem_length c1) as l1.
  pose proof (ws2bs_felem_length c2) as l2.
  pose proof (ws2bs_felem_length c3) as l3.
  pose proof (ws2bs_felem_length c4) as l4.
  change felem_size_in_bytes with 40 in l1, l2, l3, l4.
  lazymatch type of l1 with Datatypes.length ?b = _ => set (b1 := b) in * end.
  lazymatch type of l2 with Datatypes.length ?b = _ => set (b2 := b) in * end.
  lazymatch type of l3 with Datatypes.length ?b = _ => set (b3 := b) in * end.
  lazymatch type of l4 with Datatypes.length ?b = _ => set (b4 := b) in * end.
  assert (Harr : array ptsto (word.of_Z 1) p (b1 ++ b2 ++ b3 ++ b4) m).
  { apply (proj2 (array_app40_4 p b1 b2 b3 b4 l1 l2 l3 m)); ecancel_assumption. }
  pose proof (Array.array_1_to_anybytes _ _ _ Harr) as Hany.
  rewrite !length_app, l1, l2, l3, l4 in Hany; exact Hany.
Qed.

Lemma add_ok : program_logic_goal_for_function! add.
Proof.
  repeat straightline.
  straightline_call; ssplit; try solve_mem; try solve_length; try eassumption.
  repeat straightline.
  straightline_call; ssplit; try solve_mem; try solve_length; try eassumption.
  repeat straightline.
  (* Deallocation: the cached point in the stack buffer is 160 bytes. *)
  lazymatch goal with |- exists _ _, Memory.anybytes ?pc _ _ /\ map.split ?mf _ _ /\ _ =>
    lazymatch goal with H : sep ?S (sep ?A (sep ?C ?W)) mf |- _ =>
      assert (Hd : sep C (sep S (sep A W)) mf) by ecancel_assumption;
      destruct Hd as (mc & mr & Hs & Hc & Hr);
      exists mr, mc; ssplit;
        [ exact (cached_to_anybytes _ _ _ Hc) | apply Properties.map.split_comm; exact Hs | ]
    end
  end.
  repeat straightline.
  lazymatch goal with
  | HQ : SXeq ?Q' Q, HS : SXeq ?S (SP.xadd P ?Q'),
    Hs : ExecReadd.B.feval_projective_coords ?s = phi5 (proj1_sig ?S) |- _ =>
      destruct (readd_representative P Q Q' S HQ HS) as [HSeq Haff];
      exists s, S; ssplit; [ecancel_assumption | exact Hs | exact HSeq | exact Haff]
  end.
Qed.

(** [ed25519_exec_add_fn]: if the environment maps "add", "to_cached2"
    and "readd" to the bedrock2 functions and the field operations meet
    AUCurves' 64-bit specifications, a call of [add] satisfies
    [spec_of_add_sigma]. *)
Theorem ed25519_exec_add_fn functions :
  map.get functions "add" = Some add ->
  map.get functions "to_cached2" = Some to_cached2 ->
  map.get functions "readd" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.readd ->
  B.spec_of_fe25519_sub64 functions ->
  B.spec_of_fe25519_add64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  spec_of_add_sigma functions.
Proof.
  intros Hadd_fn Htc Hrd Hsub Hadd Hmul.
  pose proof add_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; [exact Hadd_fn | apply ed25519_exec_to_cached2 | apply ed25519_exec_readd];
    assumption.
Qed.

Print Assumptions to_cached2_64_ok.
Print Assumptions add_ok.
Print Assumptions ed25519_exec_to_cached2.
Print Assumptions ed25519_exec_add.
Print Assumptions ed25519_exec_add_fn.
