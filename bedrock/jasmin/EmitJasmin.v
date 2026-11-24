(** The verified bedrock2 code of [EmitC.v] and [EmitFieldL.v] as Jasmin

    The function lists [EmitC.funcs] (the byte-level scalar multiplication
    [ed25519_smul_bytes] and its callees) and [EmitFieldL.funcs] (the
    byte-level arithmetic modulo l) are printed as two Jasmin modules by the
    reg-ptr printer of AUCurves ([RegPtrSized.pp_module_sized], after
    [Core.tr_func_sized] and the polishing passes of [Core], see [polish]),
    the printer of AUCurves' BLS12-381 Jasmin modules.  The [Redirect]s
    below write the strings to
    [ed25519_bedrock_jazz.out] and [fieldl_bedrock_jazz.out]; the files
    [bench/peregrine/ed25519_bedrock.jazz] and [fieldl_bedrock.jazz] are
    these strings with Rocq's quoting removed, as for [EmitC.v].

    Conventions of the printer: a pointer parameter is a [reg ptr u64[w]],
    its width [w] in words inferred from the accesses and calls of the body
    or given in [rpc_widths]; a parameter listed in [rpc_scalar] is a
    [reg u64]; a [stackalloc] is a [stack u64] array; a function returns the
    pointer parameters it writes.  Each module has local functions and one
    [export fn] per entry point ([rpc_exports]), with the C calling
    convention: the arguments are the addresses of the buffers, the written
    buffers first.

    The printer is not verified.  [Core.tr_cmd_correct] relates each bedrock2
    command to the command the printer reads, structurally; nothing relates
    the printed text to bedrock2's semantics.  [funcs_in_fragment] checks
    that the bedrock2 code uses only constructs the translation keeps: calls
    without return values, loads and stores of one byte or one word, the
    operators other than division, remainder and the signed ones, and
    shifts by a literal below 64 or by an amount masked below 64 (bedrock2's
    shift by 64 or more gives 0, x86's takes the amount modulo 64).  The
    translation drops [expr.ite], [expr.inlinetable], the return values of
    calls and the access sizes two and four; the checked code has none of
    them. *)

From Stdlib Require Import String List ZArith Bool.
Require Import bedrock2.Syntax.
Require Import Bridge.jasmin.Core Bridge.jasmin.RegPtrSized.
Require Bridge.jasmin.SpillLiveness.
Require Bridge.EmitC Bridge.EmitFieldL.
Import ListNotations.
Local Open Scope string_scope.
Local Open Scope Z_scope.

(** ** The fragment the translation keeps *)

Definition shift_amount_ok (e : expr) : bool :=
  match e with
  | expr.literal k => (0 <=? k) && (k <? 64)
  | expr.op bopname.and _ (expr.literal k) => (0 <=? k) && (k <? 64)
  | _ => false
  end.

Fixpoint expr_ok (e : expr) : bool :=
  match e with
  | expr.literal _ | expr.var _ => true
  | expr.load access_size.one a | expr.load access_size.word a => expr_ok a
  | expr.op1 _ a => expr_ok a
  | expr.op op a b =>
      match op with
      | bopname.add | bopname.sub | bopname.mul | bopname.mulhuu
      | bopname.and | bopname.or | bopname.xor | bopname.ltu | bopname.eq =>
          expr_ok a && expr_ok b
      | bopname.sru | bopname.slu => expr_ok a && expr_ok b && shift_amount_ok b
      | _ => false
      end
  | _ => false
  end.

Fixpoint cmd_ok (c : cmd) : bool :=
  match c with
  | cmd.skip | cmd.unset _ => true
  | cmd.set _ e => expr_ok e
  | cmd.store access_size.one a v | cmd.store access_size.word a v => expr_ok a && expr_ok v
  | cmd.stackalloc _ _ b => cmd_ok b
  | cmd.cond e c1 c2 => expr_ok e && cmd_ok c1 && cmd_ok c2
  | cmd.seq c1 c2 => cmd_ok c1 && cmd_ok c2
  | cmd.while e b => expr_ok e && cmd_ok b
  | cmd.call [] _ args => forallb expr_ok args
  | _ => false
  end.

Definition func_ok (f : string * Syntax.func) : bool :=
  let '(_, (_, rets, body)) := f in
  match rets with [] => cmd_ok body | _ => false end.

Lemma funcs_in_fragment :
  forallb func_ok EmitC.funcs = true /\ forallb func_ok EmitFieldL.funcs = true.
Proof. split; vm_compute; reflexivity. Qed.

(** ** Polishing

    [polish] is [Core.polish_func] without its first pass [carry_func]
    (AUCurves' [AdcChain.polish_func_adc] is [polish] after [carry_func] and
    [adc_func]); these two passes recognise fiat-crypto's carry and borrow
    chains and print them as [#ADD]/[#ADCX]/[#SUB]/[#SBB].  On the code here
    they are not faithful: on [fl_add] and [fl_to_mont] they remove the
    definitions of variables that are still read (jasmin rejects the
    module), on [fl_add] they replace the
    final comparison [x22 = x15 <u x15 - b] by the borrow [b] (equal only
    when the carry [x15] is 0), and on [fe25519_to_bytes] they leave a
    compound operand in [#ADD].  Without them each comparison is computed
    into a boolean and moved into a word by a conditional move
    ([lower_comparisons_func], [rpc_cmov]). *)
Definition polish (f : jasmin_func) : jasmin_func :=
  lift_lits_func (simplify_func (lower_func (normalize_func (simplify_func
    (lower_comparisons_func (lower_mulx_pairs_func f)))))).

(** ** The Ed25519 module *)

Definition ed25519_cfg : rp_config := {|
  rpc_n := 5;
  rpc_ffi := [];
  rpc_inline := [];
  (* the word argument of [fe25519_from_word], the bit of [cmov] and [step_ct] *)
  rpc_scalar := [("fe25519_from_word", [1%nat]); ("cmov", [3%nat]); ("step_ct", [5%nat])];
  rpc_skip := [];
  (* [cmov] walks a point (25 words) at offsets held in its parameters;
     [scalarmult_ct] reads the 32-byte scalar at offsets [i >> 3] *)
  rpc_widths := [("cmov", [25; 25; 25; 1]); ("scalarmult_ct", [25; 25; 4; 5])];
  rpc_export_all := false;
  (* [ed25519_smul_bytes] for the glue of the *_jasmin programs; the others
     for the constant-time glue (ed25519_ct_glue.c) of the *_ctj programs *)
  rpc_exports := [("ed25519_smul_bytes", "jasmin_ed25519_smul_bytes");
                  ("ed25519_twice_d", "jasmin_ed25519_twice_d");
                  ("from_affine", "jasmin_from_affine"); ("add", "jasmin_add");
                  ("to_affine", "jasmin_to_affine");
                  ("fe25519_from_bytes", "jasmin_fe25519_from_bytes");
                  ("fe25519_to_bytes", "jasmin_fe25519_to_bytes");
                  ("fe25519_from_word", "jasmin_fe25519_from_word");
                  ("fe25519_carry_sub", "jasmin_fe25519_carry_sub")];
  rpc_hints := true;
  (* 10 registers: with the default of 16, jasminc -auto-spill runs out of
     registers in fe25519_to_bytes and the fl_* functions *)
  rpc_budget := 10;
  rpc_cmov := true;
  rpc_direct := true |}.

Definition ed25519_jasmin : list jasmin_func :=
  List.map (fun f => polish (tr_func_sized 5 f)) EmitC.funcs.

Definition ed25519_jazz : string := pp_module_sized ed25519_cfg ed25519_jasmin.

(** ** The module of the arithmetic modulo l *)

Definition fieldl_cfg : rp_config := {|
  rpc_n := 4;
  rpc_ffi := [];
  rpc_inline := [];
  rpc_scalar := [];
  rpc_skip := [];
  rpc_widths := [];
  rpc_export_all := false;
  rpc_exports := [("zl_mul_bytes", "jasmin_zl_mul_bytes"); ("zl_add_bytes", "jasmin_zl_add_bytes");
                  ("zl_sub_bytes", "jasmin_zl_sub_bytes"); ("zl_opp_bytes", "jasmin_zl_opp_bytes")];
  rpc_hints := true;
  (* 10 registers: with the default of 16, jasminc -auto-spill runs out of
     registers in fe25519_to_bytes and the fl_* functions *)
  rpc_budget := 10;
  rpc_cmov := true;
  rpc_direct := true |}.

Definition fieldl_jasmin : list jasmin_func :=
  List.map (fun f => polish (tr_func_sized 4 f)) EmitFieldL.funcs.

Definition fieldl_jazz : string := pp_module_sized fieldl_cfg fieldl_jasmin.


Set Printing Depth 1000000.
Set Printing Width 1000000.
Redirect "ed25519_bedrock_jazz" Eval vm_compute in ed25519_jazz.
Redirect "fieldl_bedrock_jazz" Eval vm_compute in fieldl_jazz.
