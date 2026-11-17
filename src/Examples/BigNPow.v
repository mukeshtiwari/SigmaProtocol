From Stdlib Require Import ZArith Zpow_facts Lia.
From Bignums Require Import BigN.

(** * Modular exponentiation over BigN for in-kernel checks

    This file gives modular exponentiation on Bignums' [BigN] (arbitrary
    precision naturals built on the kernel's 63-bit machine integers). It
    follows the recursion of the standard library's [Zpow_mod_pos] and is
    proved equal to it ([bpow_mod_spec]). A goal [Zpow_mod a m n = x] on
    numbers of thousands of bits can therefore be rewritten into a [BigN]
    computation and closed by [vm_compute] in about a second, since the
    arithmetic runs on machine words instead of binary positive numbers.
    [Examples/ElectionGuardIns.v] uses it to check [g^q = 1 mod p] at the
    4096-bit ElectionGuard modulus. *)
Module BigNPow.

  Local Open Scope Z_scope.
  (** Local notation: a [BigN] number written between square brackets
      stands for its integer value [BigN.to_Z x]. *)
  Local Notation "[ x ]" := (BigN.to_Z x).

  (** [bpow_mod_pos a m n] computes [a^m mod n] for a positive exponent [m]
      by left-to-right square-and-multiply on the binary digits of [m],
      exactly as [Zpow_mod_pos]. This includes the short cut that returns
      [0] as soon as an intermediate result is [0]. *)
  Fixpoint bpow_mod_pos (a : BigN.t) (m : positive) (n : BigN.t) : BigN.t :=
    match m with
    | xH => BigN.modulo a n
    | xO m' => let z := bpow_mod_pos a m' n in
        if BigN.eqb z BigN.zero then BigN.zero else BigN.modulo (BigN.mul z z) n
    | xI m' => let z := bpow_mod_pos a m' n in
        if BigN.eqb z BigN.zero then BigN.zero else BigN.modulo (BigN.mul (BigN.mul z z) a) n
    end.

  (** [bpow_mod_pos] agrees with [Zpow_mod_pos] on the integer values. The
      proof is by induction on [m], using the specifications of the [BigN]
      operations. *)
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

  (** Conversion from [Z] to [BigN], sending non-positive integers to
      [0]. *)
  Definition of_Z (z : Z) : BigN.t :=
    match z with Zpos p => BigN.of_pos p | _ => BigN.zero end.

  (** [of_Z] is the identity on non-negative integers. *)
  Lemma spec_of_Z : forall z, 0 <= z -> [of_Z z] = z.
  Proof.
    intros [| p | p] h; cbn [of_Z].
    + apply BigN.spec_0.
    + apply BigN.spec_of_pos.
    + exfalso; lia.
  Qed.

  (** The rewriting lemma used by clients: for [a, n ≥ 0],
      [Zpow_mod a (Zpos m) n] equals the value of the [BigN] computation. *)
  Lemma bpow_mod_spec : forall a (m : positive) n, 0 <= a -> 0 <= n ->
    Zpow_mod a (Zpos m) n = [bpow_mod_pos (of_Z a) m (of_Z n)].
  Proof.
    intros; cbn [Zpow_mod]; rewrite bpow_mod_pos_spec, !spec_of_Z by assumption; reflexivity.
  Qed.

End BigNPow.
