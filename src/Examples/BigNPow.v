(* Modular exponentiation over Bignums' BigN, mirroring Zpow_mod_pos, so
   that an equation Zpow_mod a m n = x on numbers of thousands of bits
   can be checked in the kernel by vm_compute in about a second (BigN uses
   the 63-bit machine integers of the kernel). Used by
   ElectionGuardIns.v for g^q = 1 mod p at the 4096-bit modulus. *)

From Stdlib Require Import ZArith Zpow_facts Lia.
From Bignums Require Import BigN.

(* ------------------------------------------------------------------ *)
(* Modular exponentiation over BigN, for the in-kernel order check      *)
(* ------------------------------------------------------------------ *)

Module BigNPow.

  Local Open Scope Z_scope.
  Local Notation "[ x ]" := (BigN.to_Z x).

  (* the recursion of Zpow_mod_pos, over BigN *)
  Fixpoint bpow_mod_pos (a : BigN.t) (m : positive) (n : BigN.t) : BigN.t :=
    match m with
    | xH => BigN.modulo a n
    | xO m' => let z := bpow_mod_pos a m' n in
        if BigN.eqb z BigN.zero then BigN.zero else BigN.modulo (BigN.mul z z) n
    | xI m' => let z := bpow_mod_pos a m' n in
        if BigN.eqb z BigN.zero then BigN.zero else BigN.modulo (BigN.mul (BigN.mul z z) a) n
    end.

  Lemma bpow_mod_pos_spec : forall m a n, [bpow_mod_pos a m n] = Zpow_mod_pos [a] m [n].
  Proof.
    induction m as [m ih | m ih |]; intros a n; cbn [bpow_mod_pos Zpow_mod_pos].
    + rewrite BigN.spec_eqb, BigN.spec_0, ih.
      destruct (Zpow_mod_pos [a] m [n]) eqn:e; cbn [Z.eqb].
      - apply BigN.spec_0.
      - rewrite !BigN.spec_modulo, !BigN.spec_mul, ih, e; reflexivity.
      - rewrite !BigN.spec_modulo, !BigN.spec_mul, ih, e; reflexivity.
    + rewrite BigN.spec_eqb, BigN.spec_0, ih.
      destruct (Zpow_mod_pos [a] m [n]) eqn:e; cbn [Z.eqb].
      - apply BigN.spec_0.
      - rewrite !BigN.spec_modulo, !BigN.spec_mul, ih, e; reflexivity.
      - rewrite !BigN.spec_modulo, !BigN.spec_mul, ih, e; reflexivity.
    + rewrite BigN.spec_modulo; reflexivity.
  Qed.

  Definition of_Z (z : Z) : BigN.t :=
    match z with Zpos p => BigN.of_pos p | _ => BigN.zero end.

  Lemma spec_of_Z : forall z, 0 <= z -> [of_Z z] = z.
  Proof.
    intros [| p | p] h; cbn [of_Z].
    + apply BigN.spec_0.
    + apply BigN.spec_of_pos.
    + exfalso; lia.
  Qed.

  Lemma bpow_mod_spec : forall a (m : positive) n, 0 <= a -> 0 <= n ->
    Zpow_mod a (Zpos m) n = [bpow_mod_pos (of_Z a) m (of_Z n)].
  Proof.
    intros; cbn [Zpow_mod]; rewrite bpow_mod_pos_spec, !spec_of_Z by assumption; reflexivity.
  Qed.

End BigNPow.

