(** Ed25519 scalar multiplication on 32-byte encodings.

    [ed25519_smul_bytes] takes the coordinates [x], [y] of an affine point
    and a scalar [k] as 32-byte little-endian buffers and writes the two
    coordinates of the product as 32-byte little-endian buffers.  It
    converts the coordinates to field elements with [fe25519_from_bytes],
    builds the extended point with [from_affine], multiplies it by [k] with
    the constant-time [scalarmult_ct], converts back with [to_affine] and
    writes the coordinates with [fe25519_to_bytes]; all intermediate values
    live in stack buffers.  The constant [2d] that [scalarmult_ct] takes
    is computed by [ed25519_twice_d] from four 64-bit words with
    [fe25519_from_word], [fe25519_square], [fe25519_mul] and
    [fe25519_carry_add] (Horner's rule in base [2^64]).

    [ed25519_exec_smul_bytes] states that, for a group element [x] of
    SigmaProtocol and a scalar [s] of [Zl.F], a call on the canonical
    encodings of the coordinates of [x] and on [le_split 32 (unsigned s)]
    writes the canonical encodings of the coordinates of
    [Ed.gpow_fast x s]. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Crypto.Algebra.Field.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Word.LittleEndianList.
From Stdlib Require Import Zmod.
Require Crypto.Arithmetic.Partition Crypto.Util.ListUtil.FoldBool.
Require Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Require Import Bridge.FieldTransport Bridge.ExecReadd Bridge.ExecDouble Bridge.ToCached2.
Require Import Bridge.ScalarMult Bridge.ScalarMultCT Bridge.Affine.
Import ProgramLogic.Coercions ListNotations.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* The notations of [Affine] (module-local there), restated. *)
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
Local Notation Fd := Crypto.Spec.Curve25519.E.d.
Local Notation enc a := (le_split 32 (Zmod.unsigned a)).

Module ZL := Curve.Ed25519.Ed25519.Zl.

(* The tactics of [Affine] (module-local there), restated. *)
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
           apply Z.le_trans with (Z.pow 2 8);
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

(** ** Stack deallocation *)

Lemma array_app40' (p : word) (xs ys : list byte) :
  Datatypes.length xs = 40%nat ->
  Lift1Prop.iff1 (array ptsto (word.of_Z 1) p (xs ++ ys))
                 (sep (array ptsto (word.of_Z 1) p xs) (array ptsto (word.of_Z 1) (p .+ 40) ys)).
Proof. intro hl. exact (array_app40 p (p .+ 40) xs ys hl eq_refl). Qed.

(** A field element occupies 40 bytes. *)
Lemma felem_bytes (p : word) (x : felem) m :
  FElem p x m ->
  exists bs, Datatypes.length bs = 40%nat /\ array ptsto (word.of_Z 1) p bs m.
Proof.
  intro H.
  pose proof (proj1 (felem_to_bytearray (field_representation:=frep25519) p x m) H) as Hb.
  pose proof (ws2bs_felem_length x) as hl.
  change felem_size_in_bytes with 40 in hl.
  eexists; split; [| exact Hb]. rewrite hl; reflexivity.
Qed.

Lemma dealloc_felem (p : word) (x : felem) (R P : mem -> Prop) m :
  sep (FElem p x) R m -> (forall mR, R mR -> P mR) ->
  exists mR mS, Memory.anybytes p 40 mS /\ map.split m mR mS /\ P mR.
Proof.
  intros (mS & mR & Hs & Hx & HR) HP.
  destruct (felem_bytes _ _ _ Hx) as (bs & hl & Hb).
  exists mR, mS; ssplit; [| apply Properties.map.split_comm; exact Hs | exact (HP _ HR)].
  pose proof (Array.array_1_to_anybytes _ _ _ Hb) as Hany; rewrite hl in Hany; exact Hany.
Qed.

Lemma dealloc_felem2 (p : word) (x y : felem) (R P : mem -> Prop) m :
  sep (sep (FElem p x) (FElem (p .+ 40) y)) R m -> (forall mR, R mR -> P mR) ->
  exists mR mS, Memory.anybytes p 80 mS /\ map.split m mR mS /\ P mR.
Proof.
  intros (mS & mR & Hs & Hx & HR) HP.
  exists mR, mS; ssplit; [| apply Properties.map.split_comm; exact Hs | exact (HP _ HR)].
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) p x) Hx.
  seprewrite_in (felem_to_bytearray (field_representation:=frep25519) (p .+ 40) y) Hx.
  pose proof (ws2bs_felem_length x) as l1.
  pose proof (ws2bs_felem_length y) as l2.
  change felem_size_in_bytes with 40 in l1, l2.
  lazymatch type of l1 with Datatypes.length ?b = _ => set (b1 := b) in * end.
  lazymatch type of l2 with Datatypes.length ?b = _ => set (b2 := b) in * end.
  assert (Harr : array ptsto (word.of_Z 1) p (b1 ++ b2) mS)
    by (apply (proj2 (array_app40' p b1 b2 l1 mS)); ecancel_assumption).
  pose proof (Array.array_1_to_anybytes _ _ _ Harr) as Hany.
  rewrite length_app, l1, l2 in Hany; exact Hany.
Qed.

Lemma dealloc_p5 (p : word) (c : B.projective_coords) (R P : mem -> Prop) m :
  sep (c p5@ p) R m -> (forall mR, R mR -> P mR) ->
  exists mR mS, Memory.anybytes p 200 mS /\ map.split m mR mS /\ P mR.
Proof.
  intros H HP.
  destruct (p5_to_bytes c p R m H) as (bs & hl & Hm).
  apply map_to_arr in Hm; [| exact hl].
  destruct Hm as (mS & mR & Hs & HmS & HR).
  exists mR, mS; ssplit; [| apply Properties.map.split_comm; exact Hs | exact (HP _ HR)].
  pose proof (Array.array_1_to_anybytes _ _ _ HmS) as Hany; rewrite hl in Hany; exact Hany.
Qed.

Local Ltac dealloc :=
  lazymatch goal with
  | |- exists _ _, Memory.anybytes ?pc 40 _ /\ map.split _ _ _ /\ _ =>
      lazymatch goal with
      | H : context [FElem pc ?x] |- _ =>
          eapply (dealloc_felem pc x); [ecancel_assumption | intros ? ?]
      end
  | |- exists _ _, Memory.anybytes ?pc 80 _ /\ map.split _ _ _ /\ _ =>
      lazymatch goal with
      | H : context [FElem pc ?x] |- _ =>
          lazymatch goal with
          | H' : context [FElem (pc .+ 40) ?y] |- _ =>
              eapply (dealloc_felem2 pc x y); [ecancel_assumption | intros ? ?]
          end
      end
  | |- exists _ _, Memory.anybytes ?pc 200 _ /\ map.split _ _ _ /\ _ =>
      match goal with
      | c : B.projective_coords |- _ =>
          eapply (dealloc_p5 pc c); [ecancel_assumption | intros ? ?]
      end
  end.

(** ** The constant [2d] *)

(** [2d] is [w3 * 2^192 + w2 * 2^128 + w1 * 2^64 + w0] with the words
    [w3 = 2596001775599221991], [w2 = 1841551078520508720],
    [w1 = 63073048630374742], [w0 = 16993941304535871833]; [p_s] holds
    [2^64 = (2^32)^2]. *)
Definition ed25519_twice_d := func! (p_out) {
  stackalloc 40 as p_s;
  stackalloc 40 as p_t;
  fe25519_from_word(p_t, $4294967296);
  fe25519_square(p_s, p_t);
  fe25519_from_word(p_out, $2596001775599221991);
  fe25519_mul(p_out, p_out, p_s);
  fe25519_from_word(p_t, $1841551078520508720);
  fe25519_carry_add(p_out, p_out, p_t);
  fe25519_mul(p_out, p_out, p_s);
  fe25519_from_word(p_t, $63073048630374742);
  fe25519_carry_add(p_out, p_out, p_t);
  fe25519_mul(p_out, p_out, p_s);
  fe25519_from_word(p_t, $16993941304535871833);
  fe25519_carry_add(p_out, p_out, p_t)
}.

#[local] Existing Instances B.spec_of_fe25519_from_word64 B.spec_of_fe25519_square64
  B.spec_of_fe25519_mul64 B.spec_of_fe25519_carry_add64.

Global Instance spec_of_twice_d : spec_of "ed25519_twice_d" :=
  fnspec! "ed25519_twice_d" (p_out : word) / (out : list byte) (R : _ -> Prop), {
    requires t m :=
      m =* out $@ p_out * R /\ Datatypes.length out = Z.to_nat felem_size;
    ensures t' m' :=
      t = t' /\
      exists d2 : felem,
        m' =* FElem p_out d2 * R /\ bounded_by tight_bounds d2 /\ F.add Fd Fd = feval d2
  }.

Lemma twice_d_ok : program_logic_goal_for_function! ed25519_twice_d.
Proof.
  Strategy -1000 [un_xbounds bin_xbounds bin_ybounds un_square bin_mul bin_add bin_sub
      bin_carry_add bin_carry_sub un_outbounds bin_outbounds].
  repeat straightline.
  repeat single_step.
  repeat straightline.
  repeat (dealloc; repeat straightline).
  lazymatch goal with
  | H : feval (felem_to_list ?d) = bin_model _ _, Hb : bounded_by bin_outbounds (felem_to_list ?d),
    Hm : (FElem p_out ?d * _)%sep _ |- exists _, _ =>
      exists d; ssplit; [ecancel_assumption | exact Hb |]
  end.
  repeat match goal with
         | H : feval (felem_to_list ?x) = _ |- context [feval (felem_to_list ?x)] => rewrite H
         end.
  cbv [bin_model un_model bin_mul bin_carry_add un_square].
  apply Crypto.Arithmetic.ModularArithmeticTheorems.F.eq_to_Z_iff.
  vm_compute. reflexivity.
Qed.

(** ** Canonical encodings of coordinates *)

Lemma le_split_digits z :
  map byte.unsigned (le_split 32 z) =
  Crypto.Arithmetic.Partition.Partition.partition (Crypto.Arithmetic.ModOps.weight 8 1) 32 z.
Proof.
  rewrite <-(Crypto.Bedrock.Field.Synthesis.New.Signature.partition_le_split (width:=64) 32 z).
  rewrite Crypto.Bedrock.Field.Common.Arrays.ByteBounds.byte_map_unsigned_of_Z.
  apply (Crypto.Bedrock.Field.Common.Arrays.ByteBounds.map_byte_wrap_bounded 32),
    Crypto.Bedrock.Field.Common.Arrays.ByteBounds.partition_bounded_by.
Qed.

Lemma unsigned_lt_p (c : Zp) : 0 <= Zmod.unsigned c < 2^255 - 19.
Proof. apply Zmod.unsigned_pos_bound. cbv; reflexivity. Qed.

Lemma bytes_of_Zp (c : Zp) :
  bytes_in_bounds (FieldRepresentation:=frep25519) (enc c) /\
  feval_bytes (FieldRepresentation:=frep25519) (enc c) = phi c.
Proof.
  pose proof (unsigned_lt_p c) as hc.
  cbv [bytes_in_bounds feval_bytes frep25519
       Crypto.Bedrock.Field.Synthesis.New.UnsaturatedSolinas.field_representation
       Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation
       Crypto.Bedrock.Field.Interface.Representation.frep
       Crypto.Bedrock.Field.Interface.Representation.eval_bytes].
  assert (hn : UnsaturatedSolinas.n_bytes s = 32%nat) by (vm_compute; reflexivity).
  rewrite hn, le_split_digits.
  split.
  - cbv [UnsaturatedSolinas.prime_bytes_upperbound_list COperationSpecifications.list_Z_bounded_by].
    rewrite hn, Crypto.Util.ListUtil.FoldBool.fold_andb_map_map1.
    rewrite !(Crypto.Arithmetic.Partition.partition_step (Crypto.Arithmetic.ModOps.weight 8 1) 31).
    rewrite Crypto.Util.ListUtil.FoldBool.fold_andb_map_snoc.
    apply andb_true_intro; split.
    + replace (Crypto.Arithmetic.Partition.Partition.partition (Crypto.Arithmetic.ModOps.weight 8 1) 31 (s - 1))
        with (repeat 255 31) by (vm_compute; reflexivity).
      pose proof (Crypto.Bedrock.Field.Common.Arrays.ByteBounds.partition_bytes_range 31 (Zmod.unsigned c)) as Hr.
      apply Crypto.Util.ListUtil.FoldBool.fold_andb_map_iff; split.
      * rewrite repeat_length, Crypto.Arithmetic.Partition.length_partition; reflexivity.
      * intros [a b] Hin; cbn [fst snd ZRange.lower ZRange.upper].
        pose proof (in_combine_l _ _ _ _ Hin) as Ha.
        pose proof (in_combine_r _ _ _ _ Hin) as Hb.
        apply repeat_spec in Ha; subst a.
        rewrite Forall_forall in Hr; specialize (Hr b Hb).
        apply andb_true_intro; split; apply Z.leb_le; lia.
    + replace ((s - 1) mod Crypto.Arithmetic.ModOps.weight 8 1 32 / Crypto.Arithmetic.ModOps.weight 8 1 31)
        with 127 by (vm_compute; reflexivity).
      replace (Crypto.Arithmetic.ModOps.weight 8 1 32) with (2^256) by (vm_compute; reflexivity).
      replace (Crypto.Arithmetic.ModOps.weight 8 1 31) with (2^248) by (vm_compute; reflexivity).
      cbn [ZRange.lower ZRange.upper].
      rewrite Z.mod_small by lia.
      assert (0 <= Zmod.unsigned c / 2^248 < 128).
      { split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
      apply andb_true_intro; split; apply Z.leb_le; lia.
  - rewrite (@Crypto.Arithmetic.Partition.eval_partition _ (Crypto.Arithmetic.UniformWeight.uwprops 8 ltac:(lia))).
    replace (Crypto.Arithmetic.UniformWeight.uweight 8 32%nat) with (2^256) by (vm_compute; reflexivity).
    rewrite Z.mod_small by lia.
    reflexivity.
Qed.

Lemma to_Z_phi (c : Zp) : F.to_Z (phi c) = Zmod.unsigned c.
Proof.
  cbv [phi]. rewrite Crypto.Arithmetic.ModularArithmeticTheorems.F.to_Z_of_Z, p_eq.
  apply Z.mod_small, Zmod.unsigned_pos_bound. cbv; reflexivity.
Qed.

(** ** [scalarmult_ct] on a group element and a byte-encoded scalar

    [ed25519_exec_scalarmult_ct] restated as a specification, with the
    scalar given by its 32-byte encoding. *)

Lemma unsigned_range_l (a : ZL.F) :
  0 <= Zmod.unsigned a < 2^252 + 27742317777372353535851937790883648493.
Proof. apply Zmod.unsigned_pos_bound. lia. Qed.

Definition spec_of_scalarmult_ct_G : spec_of "scalarmult_ct" :=
  fnspec! "scalarmult_ct" (p_out p_P p_k p_d : word) /
    (x : SP.G) (s : ZL.F) (pP : B.projective_coords) (d2 : felem) (out : list byte)
    (R : _ -> Prop), {
    requires t m :=
      m =* out $@ p_out * pP p5@ p_P * array ptsto (word.of_Z 1) p_k (enc s) *
           FElem p_d d2 * R /\
      Datatypes.length out = Z.to_nat (5 * felem_size) /\
      F.add Fd Fd = feval d2 /\ bounded_by tight_bounds d2 /\
      B.feval_projective_coords pP = phi5 (proj1_sig (SP.from_affine (proj1_sig x)));
    ensures t' m' :=
      t = t' /\
      exists (a : B.projective_coords) (A : SP.xpoint),
        m' =* a p5@ p_out * pP p5@ p_P * array ptsto (word.of_Z 1) p_k (enc s) *
              FElem p_d d2 * R /\
        B.feval_projective_coords a = phi5 (proj1_sig A) /\
        SP.to_affine A = proj1_sig (SP.gpow_fast x s)
  }.

Lemma array_of_list_word (p : word) (bs : list byte) :
  Datatypes.length bs = 32%nat ->
  Lift1Prop.iff1 (array ptsto (word.of_Z 1) p bs) (bs $@ p).
Proof.
  intro hl.
  apply (Array.array1_iff_eq_of_list_word_at (map:=BasicC64Semantics.mem) p bs).
  rewrite hl; lia.
Qed.

Lemma scalarmult_ct_spec_G functions :
  map.get functions "scalarmult_ct" = Some scalarmult_ct ->
  map.get functions "step_ct" = Some step_ct ->
  map.get functions "cmov" = Some cmov ->
  map.get functions "set_identity" = Some set_identity ->
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
  B.spec_of_fe25519_from_word64 functions ->
  spec_of_scalarmult_ct_G functions.
Proof.
  intros H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
  pose proof (ed25519_exec_scalarmult_ct functions H1 H2 H3 H4 H5 H6 H7 H8
                H9 H10 H11 H12 H13 H14 H15) as Hsm.
  intros p_out p_P p_k p_d x s pP d2 out R t m (Hm & Hlo & Hd & Hb & HP).
  pose proof (length_le_split 32 (Zmod.unsigned s)) as hl.
  seprewrite_in (array_of_list_word p_k (enc s) hl) Hm.
  eapply WeakestPreconditionProperties.Proper_call;
    [| apply (Hsm p_out p_P p_k p_d x s pP d2 (enc s) out R t m);
       [ecancel_assumption | exact Hlo | exact hl | | exact Hd | exact Hb | exact HP] ].
  - intros t' m' rets (Hrets & Ht & a & A & Hm' & Ha & _ & HA).
    split; [exact Hrets |]. split; [symmetry; exact Ht |].
    exists a, A; ssplit; [| exact Ha | exact HA].
    seprewrite_in (iff1_sym (array_of_list_word p_k (enc s) hl)) Hm'. ecancel_assumption.
  - rewrite le_combine_split. apply Z.mod_small.
    pose proof (unsigned_range_l s). lia.
Qed.

(** ** [ed25519_smul_bytes] *)

Definition ed25519_smul_bytes := func! (p_ox, p_oy, p_x, p_y, p_k) {
  stackalloc 40 as p_d;
  stackalloc 40 as p_fx;
  stackalloc 40 as p_fy;
  stackalloc 200 as p_P;
  stackalloc 200 as p_R;
  stackalloc 80 as p_a;
  ed25519_twice_d(p_d);
  fe25519_from_bytes(p_fx, p_x);
  fe25519_from_bytes(p_fy, p_y);
  from_affine(p_P, p_fx, p_fy);
  scalarmult_ct(p_R, p_P, p_k, p_d);
  to_affine(p_a, p_R);
  fe25519_to_bytes(p_ox, p_a);
  fe25519_to_bytes(p_oy, p_a + $40)
}.

Local Notation xc x := (fst (proj1_sig (proj1_sig x))).
Local Notation yc x := (snd (proj1_sig (proj1_sig x))).

Global Instance spec_of_smul_bytes : spec_of "ed25519_smul_bytes" :=
  fnspec! "ed25519_smul_bytes" (p_ox p_oy p_x p_y p_k : word) /
    (x : SP.G) (s : ZL.F) (ox oy : list byte) (R : _ -> Prop), {
    requires t m :=
      m =* array ptsto (word.of_Z 1) p_x (enc (xc x)) *
           array ptsto (word.of_Z 1) p_y (enc (yc x)) *
           array ptsto (word.of_Z 1) p_k (enc s) *
           array ptsto (word.of_Z 1) p_ox ox * array ptsto (word.of_Z 1) p_oy oy * R /\
      Datatypes.length ox = 32%nat /\ Datatypes.length oy = 32%nat;
    ensures t' m' :=
      t = t' /\
      m' =* array ptsto (word.of_Z 1) p_x (enc (xc x)) *
            array ptsto (word.of_Z 1) p_y (enc (yc x)) *
            array ptsto (word.of_Z 1) p_k (enc s) *
            array ptsto (word.of_Z 1) p_ox (enc (xc (SP.gpow_fast x s))) *
            array ptsto (word.of_Z 1) p_oy (enc (yc (SP.gpow_fast x s))) * R
  }.

#[local] Instance spec_of_fe25519_from_bytes64 : spec_of "fe25519_from_bytes" :=
  spec_of_from_bytes (field_representation:=frep25519).
#[local] Instance spec_of_fe25519_to_bytes64 : spec_of "fe25519_to_bytes" :=
  spec_of_to_bytes (field_representation:=frep25519).
#[local] Existing Instance spec_of_from_affine_sigma | 0.
#[local] Existing Instance spec_of_scalarmult_ct_G | 0.
#[local] Existing Instance spec_of_to_affine_sigma | 0.

(* The side conditions of a call; the continuation is left alone.  The
   point [P] of [spec_of_from_affine_sigma] is instantiated with [x]. *)
Local Ltac side x :=
  lazymatch goal with
  | |- exists _, map.putmany_of_list_zip _ _ _ = _ /\ _ => idtac
  | |- phi2 (proj1_sig ?P) = (feval _, feval _) =>
      unify P (proj1_sig x);
      rewrite (surjective_pairing (proj1_sig (proj1_sig x)));
      cbv beta iota delta [phi2]; f_equal; congruence
  | |- Datatypes.length _ = encoded_felem_size_in_bytes =>
      change encoded_felem_size_in_bytes with 32%nat; assumption
  | _ => try solve_mem; try solve_bounds; try solve_length; try eassumption
  end.

Lemma smul_bytes_ok : program_logic_goal_for_function! ed25519_smul_bytes.
Proof.
  repeat straightline.
  destruct (bytes_of_Zp (xc x)) as [Hbx Hvx].
  destruct (bytes_of_Zp (yc x)) as [Hby Hvy].
  pose proof BasicC64Semantics.wordok as Hwok.
  (* the eight calls *)
  do 8 (repeat straightline; straightline_call; ssplit; side x).
  repeat straightline.
  (* The coordinates written are those of [gpow_fast x s]. *)
  repeat match goal with H : bytes_in_bounds (le_split _ _) |- _ => clear H end.
  lazymatch goal with
  | HA : SP.to_affine ?A = proj1_sig (SP.gpow_fast x s),
    Hc : (feval ?u, feval ?v) = phi2 (proj1_sig (SP.to_affine ?A)),
    Hm : context [le_split _ (F.to_Z (feval ?v))] |- _ =>
      rewrite HA, (surjective_pairing (proj1_sig (proj1_sig (SP.gpow_fast x s)))) in Hc;
      cbv beta iota delta [phi2] in Hc;
      pose proof (f_equal fst Hc) as Eu; pose proof (f_equal snd Hc) as Ev;
      cbn [fst snd] in Eu, Ev;
      rewrite Eu, Ev, !to_Z_phi in Hm;
      change encoded_felem_size_in_bytes with 32%nat in Hm
  end.
  repeat (dealloc; repeat straightline).
  ecancel_assumption.
Qed.

(** ** The theorem

    [ed25519_exec_smul_bytes]: if the environment maps the names of the
    bedrock2 functions to their code and the field operations meet the
    specifications of AUCurves' 64-bit field and fiat-crypto's byte
    conversions, a call of [ed25519_smul_bytes] on the canonical encodings
    of the coordinates of a group element [x] and the 32 little-endian
    bytes of a scalar [s] writes the canonical encodings of the coordinates
    of [Ed.gpow_fast x s]. *)
Theorem ed25519_exec_smul_bytes functions :
  map.get functions "ed25519_smul_bytes" = Some ed25519_smul_bytes ->
  map.get functions "ed25519_twice_d" = Some ed25519_twice_d ->
  map.get functions "from_affine" = Some from_affine ->
  map.get functions "to_affine" = Some to_affine ->
  map.get functions "fe25519_inv" = Some fe25519_inv ->
  map.get functions "scalarmult_ct" = Some scalarmult_ct ->
  map.get functions "step_ct" = Some step_ct ->
  map.get functions "cmov" = Some cmov ->
  map.get functions "set_identity" = Some set_identity ->
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
  spec_of_from_bytes (field_representation:=frep25519) functions ->
  spec_of_to_bytes (field_representation:=frep25519) functions ->
  spec_of_smul_bytes functions.
Proof.
  intros Hsb Htd Hfa Hta Hinv Hsm Hst Hcm Hid Hadd_fn Htc Hrd Hdbl
    Hsq Hcadd Hadd Hcsub Hsub Hmul Hcopy Hfw Hfb Htb.
  pose proof smul_bytes_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; clear H;
    [ exact Hsb
    | pose proof twice_d_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H;
      apply H; assumption
    | exact Hfb | exact Hfb
    | apply ed25519_exec_from_affine; assumption
    | apply scalarmult_ct_spec_G; assumption
    | apply ed25519_exec_to_affine; assumption
    | exact Htb | exact Htb ].
Qed.

Print Assumptions twice_d_ok.
Print Assumptions smul_bytes_ok.
Print Assumptions ed25519_exec_smul_bytes.
