(** The C code of the verified scalar multiplication

    The constant-time scalar multiplication of [ScalarMultCT.v]
    ([scalarmult_ct] and its callees, among them [set_identity] of
    [ScalarMult.v]),
    of [Affine.v] ([from_affine], [to_affine], [fe25519_inv]) and the
    64-bit field operations of AUCurves' [Field25519_64] that they call,
    together with the canonical byte conversions [fe25519_from_bytes] and
    [fe25519_to_bytes], printed as one C module by bedrock2's [ToCString].
    The [Redirect] below writes the string to [ed25519_bedrock.out]; the
    C file ([bench/peregrine/ed25519_bedrock.c]) is that string with Rocq's
    quoting removed: the text of the string literal, in which Rocq doubles
    every double quote, with each such pair replaced by one double quote.

    [ToCString] makes [scalarmult_ct], the first function, external and the
    others [static]; it does not rename functions, so the function [double]
    has the name of a C keyword, which the including file renames with the
    preprocessor.  The lemma [field_specs] checks that the field functions
    emitted here meet the specifications that [ed25519_exec_scalarmult_ct] and
    the theorems of [Affine.v] take as hypotheses. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Import bedrock2.ToCString.
Require Import Bridge.ToCached2 Bridge.Affine Bridge.ScalarMult Bridge.ScalarMultCT.
Import ListNotations.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.
Module FE := Bedrock.End2End.X25519_64.Field25519_64.
Module EX := Crypto.Bedrock.End2End.X25519.EdwardsXYZT.

Local Open Scope string_scope.

Definition funcs : list (string * Syntax.func) := [
  ("scalarmult_ct", ScalarMultCT.scalarmult_ct);
  ("step_ct", ScalarMultCT.step_ct);
  ("cmov", ScalarMultCT.cmov);
  ("set_identity", ScalarMult.set_identity);
  ("add", ToCached2.add);
  ("to_cached2", ToCached2.to_cached2);
  ("readd", EX.readd);
  ("double", EX.double);
  ("from_affine", Affine.from_affine);
  ("to_affine", Affine.to_affine);
  ("fe25519_inv", Affine.fe25519_inv);
  ("fe25519_from_bytes", FE.fe25519_from_bytes);
  ("fe25519_to_bytes", FE.fe25519_to_bytes);
  ("fe25519_copy", FE.fe25519_copy);
  ("fe25519_from_word", FE.fe25519_from_word);
  ("fe25519_mul", FE.fe25519_mul);
  ("fe25519_square", FE.fe25519_square);
  ("fe25519_add", FE.fe25519_add);
  ("fe25519_sub", FE.fe25519_sub);
  ("fe25519_carry_add", FE.fe25519_carry_add);
  ("fe25519_carry_sub", FE.fe25519_carry_sub)].

(** The field functions of [funcs] meet the 64-bit specifications that
    [ed25519_exec_scalarmult_ct] ([ScalarMultCT.v]) and [ed25519_exec_to_affine]
    ([Affine.v]) take as hypotheses, and the byte conversions meet
    fiat-crypto's specifications. *)
Lemma field_specs functions :
  (forall name f, In (name, f) funcs -> map.get functions name = Some f) ->
  B.spec_of_fe25519_square64 functions /\
  B.spec_of_fe25519_carry_add64 functions /\
  B.spec_of_fe25519_add64 functions /\
  B.spec_of_fe25519_carry_sub64 functions /\
  B.spec_of_fe25519_sub64 functions /\
  B.spec_of_fe25519_mul64 functions /\
  B.spec_of_fe25519_copy64 functions /\
  B.spec_of_fe25519_from_word64 functions /\
  spec_of_from_bytes (field_representation:=frep25519) functions /\
  spec_of_to_bytes (field_representation:=frep25519) functions.
Proof.
  intro H.
  repeat split.
  - apply FE.fe25519_square_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_carry_add_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_add_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_carry_sub_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_sub_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_mul_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_copy_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_from_word_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_from_bytes_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
  - apply FE.fe25519_to_bytes_correct, H; cbv [funcs]; repeat (first [left; reflexivity | right]).
Qed.

Definition ed25519_bedrock_c : string := c_module funcs.

Redirect "ed25519_bedrock" Eval vm_compute in ed25519_bedrock_c.
