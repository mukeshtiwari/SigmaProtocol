(** The operations of [Zl.F] on 32-byte little-endian encodings

    [zl_add_bytes], [zl_sub_bytes], [zl_opp_bytes] and [zl_mul_bytes] are
    bedrock2 functions that take the 32 little-endian bytes of the canonical
    representatives of their arguments and write those of the result: each
    converts its arguments to plain limb encodings with [fl_from_bytes] in
    stack buffers, calls the arithmetic of [FieldL.v] ([zl_mul_bytes]
    converts its second factor to Montgomery form with [fl_to_mont] first,
    so that [fl_mul] returns a plain encoding of the product), and converts
    the result back with [fl_to_bytes].  The theorems [zl_exec_*_bytes]
    state, from the specifications of [ExecFieldL.v], that a call computes
    [Zl.add], [Zl.sub], [Zl.opp] and [Zl.mul]. *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Curve Require Ed25519.
Require Import Crypto.Spec.ModularArithmetic.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte.
Require Import coqutil.Word.LittleEndianList coqutil.Map.OfListWord.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.syntactic_unify.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic bedrock2.WeakestPrecondition
        bedrock2.WeakestPreconditionProperties bedrock2.Syntax bedrock2.Array
        bedrock2.Scalars bedrock2.NotationsCustomEntry bedrock2.ZnWords
        bedrock2.bottom_up_simpl bedrock2.SepAutoArray.
Require bedrock2.Memory.
Require Import bedrock2.BasicC64Semantics coqutil.Word.Bitwidth64.
Require Import Bridge.FieldL Bridge.ExecFieldL.
Import ProgramLogic.Coercions ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

#[local] Existing Instances BasicC64Semantics.word BasicC64Semantics.wordok Bitwidth64.BW64
  BasicC64Semantics.mem BasicC64Semantics.mapok
  Defaults64.default_parameters Defaults64.default_parameters_ok
  FieldL.field_parametersL FieldL.frepL FieldL.frepL_ok.

Local Notation word := BasicC64Semantics.word.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation enc a := (le_split 32 (Zmod.unsigned a)).

(** ** The bedrock2 functions *)

Definition zl_add_bytes := func! (p_out, p_a, p_b) {
  stackalloc 32 as p_x;
  stackalloc 32 as p_y;
  stackalloc 32 as p_o;
  fl_from_bytes(p_x, p_a);
  fl_from_bytes(p_y, p_b);
  fl_add(p_o, p_x, p_y);
  fl_to_bytes(p_out, p_o)
}.

Definition zl_sub_bytes := func! (p_out, p_a, p_b) {
  stackalloc 32 as p_x;
  stackalloc 32 as p_y;
  stackalloc 32 as p_o;
  fl_from_bytes(p_x, p_a);
  fl_from_bytes(p_y, p_b);
  fl_sub(p_o, p_x, p_y);
  fl_to_bytes(p_out, p_o)
}.

Definition zl_mul_bytes := func! (p_out, p_a, p_b) {
  stackalloc 32 as p_x;
  stackalloc 32 as p_y;
  stackalloc 32 as p_ym;
  stackalloc 32 as p_o;
  fl_from_bytes(p_x, p_a);
  fl_from_bytes(p_y, p_b);
  fl_to_mont(p_ym, p_y);
  fl_mul(p_o, p_x, p_ym);
  fl_to_bytes(p_out, p_o)
}.

Definition zl_opp_bytes := func! (p_out, p_a) {
  stackalloc 32 as p_x;
  stackalloc 32 as p_o;
  fl_from_bytes(p_x, p_a);
  fl_opp(p_o, p_x);
  fl_to_bytes(p_out, p_o)
}.

(** ** Specifications *)

Definition zl_binop_bytes_spec name (op : Zl.F -> Zl.F -> Zl.F) : spec_of name :=
  fnspec! name (p_out p_a p_b : word) / (a b : Zl.F) (out : list byte) (R : mem -> Prop),
  { requires t m :=
      m =* array ptsto (word.of_Z 1) p_a (enc a) * array ptsto (word.of_Z 1) p_b (enc b) *
           array ptsto (word.of_Z 1) p_out out * R /\
      length out = 32%nat;
    ensures t' m' :=
      t = t' /\
      m' =* array ptsto (word.of_Z 1) p_a (enc a) * array ptsto (word.of_Z 1) p_b (enc b) *
            array ptsto (word.of_Z 1) p_out (enc (op a b)) * R }.

Definition zl_unop_bytes_spec name (op : Zl.F -> Zl.F) : spec_of name :=
  fnspec! name (p_out p_a : word) / (a : Zl.F) (out : list byte) (R : mem -> Prop),
  { requires t m :=
      m =* array ptsto (word.of_Z 1) p_a (enc a) * array ptsto (word.of_Z 1) p_out out * R /\
      length out = 32%nat;
    ensures t' m' :=
      t = t' /\
      m' =* array ptsto (word.of_Z 1) p_a (enc a) * array ptsto (word.of_Z 1) p_out (enc (op a)) * R }.

#[local] Instance spec_of_zl_add_bytes : spec_of "zl_add_bytes" := zl_binop_bytes_spec "zl_add_bytes" Zl.add.
#[local] Instance spec_of_zl_sub_bytes : spec_of "zl_sub_bytes" := zl_binop_bytes_spec "zl_sub_bytes" Zl.sub.
#[local] Instance spec_of_zl_mul_bytes : spec_of "zl_mul_bytes" := zl_binop_bytes_spec "zl_mul_bytes" Zl.mul.
#[local] Instance spec_of_zl_opp_bytes : spec_of "zl_opp_bytes" := zl_unop_bytes_spec "zl_opp_bytes" Zl.opp.

(** The callees, with the specifications of [ExecFieldL.v]. *)
#[local] Instance spec_of_fl_add : spec_of "fl_add" := zl_binop_spec "fl_add" enc_raw enc_raw enc_raw Zl.add.
#[local] Instance spec_of_fl_sub : spec_of "fl_sub" := zl_binop_spec "fl_sub" enc_raw enc_raw enc_raw Zl.sub.
#[local] Instance spec_of_fl_opp : spec_of "fl_opp" := zl_unop_spec "fl_opp" enc_raw enc_raw Zl.opp.
#[local] Instance spec_of_fl_mul : spec_of "fl_mul" := zl_binop_spec "fl_mul" enc_raw enc_mont enc_raw Zl.mul.
#[local] Instance spec_of_fl_to_mont : spec_of "fl_to_mont" :=
  zl_unop_spec "fl_to_mont" enc_raw enc_mont (fun a => a).
#[local] Existing Instances spec_of_fl_from_bytes_zl spec_of_fl_to_bytes_zl.

(** ** Proofs *)

Lemma felem_size_32 : felem_size_in_bytes = 32.
Proof. reflexivity. Qed.

(** A limb array occupies 32 bytes, which the stack deallocation needs. *)
Lemma felem_anybytes (p : word) (x : felem) m :
  FElem p x m -> Memory.anybytes p 32 m.
Proof.
  intro H. apply felem_to_bytes in H.
  eexists; split; [exact H |].
  split; [rewrite ws2bs_felem_length; reflexivity | apply ws2bs_felem_width].
Qed.

Lemma dealloc_felem (p : word) (x : felem) (R P : mem -> Prop) m :
  sep (FElem p x) R m -> (forall mR, R mR -> P mR) ->
  exists mR mS, Memory.anybytes p 32 mS /\ map.split m mR mS /\ P mR.
Proof.
  intros (mS & mR & Hs & Hx & HR) HP.
  exists mR, mS; ssplit; [exact (felem_anybytes _ _ _ Hx) | | exact (HP _ HR)].
  apply Properties.map.split_comm; exact Hs.
Qed.

Local Ltac solve_length :=
  try lia;
  try (match goal with
       | |- (Z.of_nat (Datatypes.length ?l) <= 2 ^ _)%Z =>
           apply Z.le_trans with (Z.pow 2 7);
             [ rewrite ?felem_size_32 in *;
               try (match goal with
                    | H : Datatypes.length l = _ |- _ => rewrite H
                    end);
               try listZnWords; try lia
             | apply Z.pow_le_mono_r; lia ]
       end);
  match goal with
    | |- Datatypes.length _ = _ =>
      solve [rewrite ?ws2bs_felem_length; try lia;
          rewrite ?felem_size_32 in *; try listZnWords; lia]
  end.

Local Ltac solve_mem :=
  repeat match goal with
    | |- exists _ : _ -> Prop, _%sep _ => eexists
    | H: ?P%sep ?m |- ?G%sep ?m => progress ecancel_assumption_preprocess_with solve_length
    | H : _ %sep ?m |- _ %sep ?m => bottom_up_simpl_in_goal
    | |- _%sep _ => ecancel_assumption
  end.

Local Ltac call :=
  repeat straightline; straightline_call;
  ssplit; try solve_mem; try solve_length; try eassumption.

Local Ltac dealloc :=
  lazymatch goal with
  | |- exists _ _, Memory.anybytes ?pc _ _ /\ map.split _ _ _ /\ _ =>
      lazymatch goal with
      | H : context [FElem pc ?x] |- _ =>
          eapply (dealloc_felem pc x); [ecancel_assumption | intros ? ?]
      end
  end.

(** [straightline]'s entry into a function, with the specification
    [zl_binop_bytes_spec] or [zl_unop_bytes_spec] unfolded. *)
Local Ltac start f :=
  enter f; cbv [zl_binop_bytes_spec zl_unop_bytes_spec]; intros;
  match goal with
  | H: map.get ?functions ?fname = Some _ |- _ =>
      eapply start_func; [exact H | clear H]
  end;
  cbv match beta delta [WeakestPrecondition.func];
  repeat straightline.

Lemma zl_add_bytes_ok : program_logic_goal_for_function! zl_add_bytes.
Proof.
  start zl_add_bytes.
  call. call. call. call.
  repeat straightline.
  repeat (dealloc; repeat straightline).
  ecancel_assumption.
Qed.

Lemma zl_sub_bytes_ok : program_logic_goal_for_function! zl_sub_bytes.
Proof.
  start zl_sub_bytes.
  call. call. call. call.
  repeat straightline.
  repeat (dealloc; repeat straightline).
  ecancel_assumption.
Qed.

Lemma zl_mul_bytes_ok : program_logic_goal_for_function! zl_mul_bytes.
Proof.
  start zl_mul_bytes.
  call. call. call. call. call.
  repeat straightline.
  repeat (dealloc; repeat straightline).
  ecancel_assumption.
Qed.

Lemma zl_opp_bytes_ok : program_logic_goal_for_function! zl_opp_bytes.
Proof.
  start zl_opp_bytes.
  call. call. call.
  repeat straightline.
  repeat (dealloc; repeat straightline).
  ecancel_assumption.
Qed.

(** ** The theorems *)

(** Under the environment hypotheses, a call of [zl_add_bytes],
    [zl_sub_bytes], [zl_mul_bytes] or [zl_opp_bytes] on the bytes of [a]
    (and [b]) writes the bytes of [Zl.add a b], [Zl.sub a b], [Zl.mul a b]
    or [Zl.opp a]. *)
Theorem zl_exec_add_bytes functions :
  map.get functions "zl_add_bytes" = Some zl_add_bytes ->
  map.get functions "fl_from_bytes" = Some (snd FieldL.fl_from_bytes) ->
  map.get functions "fl_add" = Some (snd FieldL.fl_add) ->
  map.get functions "fl_to_bytes" = Some (snd FieldL.fl_to_bytes) ->
  zl_binop_bytes_spec "zl_add_bytes" Zl.add functions.
Proof.
  intros H Hfb Hop Htb.
  pose proof zl_add_bytes_ok as Hok; cbv [ProgramLogic.program_logic_goal_for] in Hok.
  apply Hok; [exact H | apply fl_exec_from_bytes, Hfb | apply fl_exec_from_bytes, Hfb
             | apply fl_exec_add_raw, Hop | apply fl_exec_to_bytes, Htb].
Qed.

Theorem zl_exec_sub_bytes functions :
  map.get functions "zl_sub_bytes" = Some zl_sub_bytes ->
  map.get functions "fl_from_bytes" = Some (snd FieldL.fl_from_bytes) ->
  map.get functions "fl_sub" = Some (snd FieldL.fl_sub) ->
  map.get functions "fl_to_bytes" = Some (snd FieldL.fl_to_bytes) ->
  zl_binop_bytes_spec "zl_sub_bytes" Zl.sub functions.
Proof.
  intros H Hfb Hop Htb.
  pose proof zl_sub_bytes_ok as Hok; cbv [ProgramLogic.program_logic_goal_for] in Hok.
  apply Hok; [exact H | apply fl_exec_from_bytes, Hfb | apply fl_exec_from_bytes, Hfb
             | apply fl_exec_sub_raw, Hop | apply fl_exec_to_bytes, Htb].
Qed.

Theorem zl_exec_mul_bytes functions :
  map.get functions "zl_mul_bytes" = Some zl_mul_bytes ->
  map.get functions "fl_from_bytes" = Some (snd FieldL.fl_from_bytes) ->
  map.get functions "fl_to_mont" = Some (snd FieldL.fl_to_mont) ->
  map.get functions "fl_mul" = Some (snd FieldL.fl_mul) ->
  map.get functions "fl_to_bytes" = Some (snd FieldL.fl_to_bytes) ->
  zl_binop_bytes_spec "zl_mul_bytes" Zl.mul functions.
Proof.
  intros H Hfb Htm Hop Htb.
  pose proof zl_mul_bytes_ok as Hok; cbv [ProgramLogic.program_logic_goal_for] in Hok.
  apply Hok; [exact H | apply fl_exec_from_bytes, Hfb | apply fl_exec_from_bytes, Hfb
             | apply fl_exec_to_mont, Htm | apply fl_exec_mul_raw, Hop
             | apply fl_exec_to_bytes, Htb].
Qed.

Theorem zl_exec_opp_bytes functions :
  map.get functions "zl_opp_bytes" = Some zl_opp_bytes ->
  map.get functions "fl_from_bytes" = Some (snd FieldL.fl_from_bytes) ->
  map.get functions "fl_opp" = Some (snd FieldL.fl_opp) ->
  map.get functions "fl_to_bytes" = Some (snd FieldL.fl_to_bytes) ->
  zl_unop_bytes_spec "zl_opp_bytes" Zl.opp functions.
Proof.
  intros H Hfb Hop Htb.
  pose proof zl_opp_bytes_ok as Hok; cbv [ProgramLogic.program_logic_goal_for] in Hok.
  apply Hok; [exact H | apply fl_exec_from_bytes, Hfb
             | apply fl_exec_opp_raw, Hop | apply fl_exec_to_bytes, Htb].
Qed.

Print Assumptions zl_exec_add_bytes.
Print Assumptions zl_exec_sub_bytes.
Print Assumptions zl_exec_mul_bytes.
Print Assumptions zl_exec_opp_bytes.
