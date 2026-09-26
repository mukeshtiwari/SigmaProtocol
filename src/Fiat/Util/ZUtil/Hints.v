(** * Hint Databases with lemmas about ℤ from the standard library *)
From Stdlib Require Import ZArith.
Require Export Fiat.Util.ZUtil.Hints.Core.
Require Export Fiat.Util.ZUtil.Hints.ZArith.
Require Export Fiat.Util.ZUtil.Hints.Ztestbit.
Require Export Fiat.Util.ZUtil.Hints.PullPush.
Require Export Fiat.Util.ZUtil.ZSimplify.Core.

Global Hint Resolve -> Z.log2_lt_pow2 Z.log2_le_pow2 : concl_log2.
Global Hint Resolve <- Z.log2_lt_pow2 Z.log2_le_pow2 : hyp_log2.

(** For the occasional lemma that can remove the use of [Z.div] *)
#[global]
Hint Rewrite Z.div_small_iff using zutil_arith : zstrip_div.
