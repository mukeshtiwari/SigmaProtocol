(** * [Z], [positive] and [N] as GMP integers, for Peregrine's C backend

    The axioms below are the functions of z_gmp.c.  The attribute file written
    by splice_gmp_z.py maps each axiom to its C function and remaps the three
    inductives of [BinNums] to one representation, an integer: [Z0] and [N0] are
    0, [Zpos p] and [Npos p] are [p], [Zneg p] is [-p], [xH] is 1, [xO p] is
    [2p] and [xI p] is [2p + 1].  The bodies of the operations of Corelib's and
    Stdlib's [Z], [Pos] and [N] modules are replaced by the [*_impl] definitions
    below or by an axiom directly.

    Types are irrelevant after erasure, so the axioms are stated on [Z] and used
    for [positive] and [N] as well, and the case analyses are stated at [unit].
    Each C function implements the Rocq operation it replaces, including the
    cases of division by 0, truncating subtraction and negative exponents;
    extraction trusts this correspondence, and it is not proved here. *)

From Stdlib Require Import ZArith.
From Peregrine.Plugin Require Import Loader.

Axiom zg_Z0 zg_xH zg_N0 : Z.
Axioms zg_Zpos zg_Zneg zg_xO zg_xI zg_Npos : Z -> Z.
Axiom zg_z_case : Z -> (unit -> unit) -> (Z -> unit) -> (Z -> unit) -> unit.
Axiom zg_pos_case : Z -> (Z -> unit) -> (Z -> unit) -> (unit -> unit) -> unit.
Axiom zg_n_case : Z -> (unit -> unit) -> (Z -> unit) -> unit.

Axioms zg_add zg_sub zg_mul zg_fdiv zg_fmod zg_tdiv zg_tmod zg_pow
  zg_shiftl zg_shiftr zg_land zg_lor zg_lxor zg_pos_sub_trunc zg_n_sub_trunc : Z -> Z -> Z.
Axioms zg_opp zg_abs zg_pos_pred zg_n_pred zg_pos_size zg_to_pos zg_to_n : Z -> Z.
Axioms zg_testbit zg_eqb zg_leb zg_ltb : Z -> Z -> bool.
Axiom zg_compare : Z -> Z -> comparison.

Definition id_impl (x : Z) : Z := x.
Definition succ_impl (x : Z) : Z := zg_add x zg_xH.
Definition pred_impl (x : Z) : Z := zg_sub x zg_xH.
Definition double_impl (x : Z) : Z := zg_add x x.
Definition succ_double_impl (x : Z) : Z := zg_add (zg_add x x) zg_xH.
Definition pred_double_impl (x : Z) : Z := zg_sub (zg_add x x) zg_xH.
Definition div2_impl (x : Z) : Z := zg_shiftr x zg_xH.
Definition geb_impl (x y : Z) : bool := zg_leb y x.
Definition gtb_impl (x y : Z) : bool := zg_ltb y x.
Definition min_impl (x y : Z) : Z := if zg_leb x y then x else y.
Definition max_impl (x y : Z) : Z := if zg_leb x y then y else x.
Definition two : Z := zg_xO zg_xH.
Definition even_impl (x : Z) : bool := zg_eqb (zg_fmod x two) zg_Z0.
Definition odd_impl (x : Z) : bool := if zg_eqb (zg_fmod x two) zg_Z0 then false else true.
Definition sgn_impl (x : Z) : Z :=
  match zg_compare x zg_Z0 with Eq => zg_Z0 | Lt => zg_Zneg zg_xH | Gt => zg_xH end.
Definition div_eucl_impl (a b : Z) : Z * Z := (zg_fdiv a b, zg_fmod a b).
Definition compare_cont_impl (r : comparison) (x y : Z) : comparison :=
  match zg_compare x y with Eq => r | c => c end.

Definition gmp_z_impls :=
  (zg_Z0, zg_xH, zg_N0, zg_Zpos, zg_Zneg, zg_xO, zg_xI, zg_Npos,
   zg_z_case, zg_pos_case, zg_n_case,
   (zg_add, zg_sub, zg_mul, zg_fdiv, zg_fmod, zg_tdiv, zg_tmod, zg_pow,
    zg_shiftl, zg_shiftr, zg_land, zg_lor, zg_lxor, zg_pos_sub_trunc, zg_n_sub_trunc),
   (zg_opp, zg_abs, zg_pos_pred, zg_n_pred, zg_pos_size, zg_to_pos, zg_to_n,
    zg_testbit, zg_eqb, zg_leb, zg_ltb, zg_compare),
   (id_impl, succ_impl, pred_impl, double_impl, succ_double_impl, pred_double_impl,
    div2_impl, geb_impl, gtb_impl, min_impl, max_impl, even_impl, odd_impl, sgn_impl,
    div_eucl_impl, compare_cont_impl)).

Peregrine Extract "gmp_z.ast" gmp_z_impls.
