(** Basic lemmas about [Z.div] for bootstrapping various tactics *)
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import Fiat.Util.ZUtil.Hints.Core.
Local Open Scope Z_scope.

Module Z.
  Lemma div_0_r_eq a b : b = 0 -> a / b = 0.
  Proof. intro; subst; auto with zarith. Qed.
#[global]
  Hint Resolve div_0_r_eq : zarith.
#[global]
  Hint Rewrite div_0_r_eq using assumption : zsimplify.
End Z.
