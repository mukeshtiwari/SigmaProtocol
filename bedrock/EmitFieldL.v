(** The C code of the arithmetic modulo [l]

    The byte-level operations of [ZlBytes.v] ([zl_add_bytes],
    [zl_sub_bytes], [zl_mul_bytes], [zl_opp_bytes]) and the bedrock2
    functions of [FieldL.v] that they call, printed as one C module by
    bedrock2's [ToCString].  The [Redirect] below writes the string to
    [fieldl_bedrock.out]; the C file ([bench/peregrine/fieldl_bedrock.c]) is
    that string with Rocq's quoting removed, as for [EmitC.v].  [ToCString]
    makes the first function external and the others [static]; the glue
    includes the C file.

    [fieldl_specs] checks that the four byte-level functions emitted here
    meet the specifications of [ZlBytes.v] over [Zl.F]. *)

From Stdlib Require Import String List.
Require Import bedrock2.ToCString.
Require Import coqutil.Map.Interface.
Require Import Bridge.FieldL Bridge.ExecFieldL.
Require Bridge.ZlBytes.
Import ListNotations.

Local Open Scope string_scope.

Definition funcs : list (string * Syntax.func) := [
  ("zl_mul_bytes", ZlBytes.zl_mul_bytes);
  ("zl_add_bytes", ZlBytes.zl_add_bytes);
  ("zl_sub_bytes", ZlBytes.zl_sub_bytes);
  ("zl_opp_bytes", ZlBytes.zl_opp_bytes);
  FieldL.fl_mul; FieldL.fl_add; FieldL.fl_sub; FieldL.fl_opp;
  FieldL.fl_to_mont; FieldL.fl_from_bytes; FieldL.fl_to_bytes].

(** The names of the functions of [FieldL.v] in [funcs]. *)
Lemma funcs_names :
  map fst funcs = ["zl_mul_bytes"; "zl_add_bytes"; "zl_sub_bytes"; "zl_opp_bytes";
                   "fl_mul"; "fl_add"; "fl_sub"; "fl_opp"; "fl_to_mont";
                   "fl_from_bytes"; "fl_to_bytes"].
Proof. reflexivity. Qed.

Local Ltac member := cbv [funcs]; repeat (first [left; reflexivity | right]).

(** An environment that contains [funcs] meets the specifications of
    [ZlBytes.v] for the four byte-level operations. *)
Lemma fieldl_specs fs :
  (forall name f, In (name, f) funcs -> map.get fs name = Some f) ->
  ZlBytes.zl_binop_bytes_spec "zl_add_bytes" Zl.add fs /\
  ZlBytes.zl_binop_bytes_spec "zl_sub_bytes" Zl.sub fs /\
  ZlBytes.zl_binop_bytes_spec "zl_mul_bytes" Zl.mul fs /\
  ZlBytes.zl_unop_bytes_spec "zl_opp_bytes" Zl.opp fs.
Proof.
  intro H.
  repeat split.
  - apply ZlBytes.zl_exec_add_bytes; apply H; member.
  - apply ZlBytes.zl_exec_sub_bytes; apply H; member.
  - apply ZlBytes.zl_exec_mul_bytes; apply H; member.
  - apply ZlBytes.zl_exec_opp_bytes; apply H; member.
Qed.

Definition fieldl_bedrock_c : string := c_module funcs.

Redirect "fieldl_bedrock" Eval vm_compute in fieldl_bedrock_c.

Print Assumptions fieldl_specs.
