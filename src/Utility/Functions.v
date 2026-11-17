(** * Modular exponentiation on binary naturals

    This file defines and verifies modular exponentiation [e ^ n mod w] on the
    binary natural numbers [N] of the Rocq standard library.  It is the
    executable exponentiation used by the multiplicative group [Z_p^*]
    development ([Zpstar.v]), by Fermat-based inverses ([Fermat.v]) and by the
    Schnorr-group order checks ([SchnorrOrder.v]); after extraction it becomes
    plain big-integer arithmetic.

    Three implementations are given and proved to agree:

    - [Npow_mod] (via [repeat_op_ntimes_rec]): left-to-right square-and-multiply
      that recurses over the bits of the positive exponent.  It performs one
      squaring per bit and one extra multiplication per set bit, so it uses
      Θ(log n) modular multiplications; the inductive relation
      [complexity_repeat_op_ntimes_rec] records this cost and
      [correct_complexity_repeat_op_ntimes_rec] proves that the recursion depth
      is exactly [N.log2 n].
    - [Npow_mod_constant_space] (via [repeat_op_ntimes_acc]): a tail-recursive,
      accumulator-based right-to-left variant that runs in constant stack space.
    - [Npow_mod_unary]: the obvious specification, multiplying [n] times; it is
      used only as a reference model in proofs.

    The bridge lemmas are [npow_mod_npow_constant_eqv] (fast = constant
    space), [npow_mod_exp_unary_binary_eqv] (unary = fast) and, most
    importantly for client files, [zmod_nmod], which identifies [Npow_mod] with
    the standard library's [Zpow_mod] on integers so that number-theoretic facts
    proved over [Z] (for example Fermat's little theorem) can be transported to
    the executable function.

    Many lemmas carry a hypothesis [prime (Z.of_N w)] although they only need
    [w ≠ 0] (or [w ≥ 2]); primality is simply the setting in which they are used. *)
From Stdlib Require Import
  NArith Nnat Znumtheory Lia
  Zdiv Znat Zpow_facts
  BinNat PeanoNat.

(** All definitions live in a single section [Fn] with no section variables. *)
Section Fn.

  (** [repeat_op_ntimes_rec e n w] computes [e ^ n mod w] for a positive exponent
      [n] by recursion on its binary representation: for [n = 2p] it squares the
      result for [p], for [n = 2p+1] it squares and multiplies by [e], and for
      [n = 1] it returns [e mod w].  Every intermediate value is reduced modulo [w],
      so operands stay below [w]. *)
  Fixpoint repeat_op_ntimes_rec (e : N) (n : positive) (w : N) : N :=
    match n with
    | xH => N.modulo e w
    | xO p => let ret := repeat_op_ntimes_rec e p w in
        N.modulo (ret * ret) w
    | xI p => let ret := repeat_op_ntimes_rec e p w in
        N.modulo (e * (ret * ret)) w
    end.

  (** [Npow_mod e n w] is [e ^ n mod w] for an arbitrary [n : N].  The case
      [n = 0] returns [1] without reducing it modulo [w] (so for [w = 1] the result
      is [1], not [0]); this is harmless because [w] is a prime in every use. *)
  Definition Npow_mod (e : N) (n w : N) :=
    match n with
    | N0 => Npos xH
    | Npos p => repeat_op_ntimes_rec e p w
    end.

  (** [complexity_repeat_op_ntimes_rec e t n r k] is a big-step cost semantics for
      [repeat_op_ntimes_rec]: it says that the recursion on exponent [n] modulo
      [t] returns [r] after [k] recursive (doubling) steps.  Each constructor
      mirrors one branch of the function and increments the step count by one. *)
  Inductive complexity_repeat_op_ntimes_rec
    (e t : N) : positive -> N -> N -> Prop :=
  | xH_case : complexity_repeat_op_ntimes_rec e t xH
      (N.modulo e t) N0
  | xO_case p ret w :
      complexity_repeat_op_ntimes_rec e t p ret w ->
      complexity_repeat_op_ntimes_rec e t (xO p)
      (N.modulo (ret * ret) t) (N.succ w)
  | xI_case p ret w :
      complexity_repeat_op_ntimes_rec e t p ret w ->
      complexity_repeat_op_ntimes_rec e t (xI p)
      (N.modulo (e * (ret * ret)) t) (N.succ w).

  (** Complexity bound: [repeat_op_ntimes_rec e n w] is related by
      [complexity_repeat_op_ntimes_rec] to its own result with step count
      [N.log2 n], so square-and-multiply uses ⌊log₂ n⌋ doubling steps (each with
      at most two modular multiplications).  The proof is by induction on [n],
      using [N.log2_succ_double] and [N.log2_double]. *)
  Lemma correct_complexity_repeat_op_ntimes_rec :
    forall n e w,
    complexity_repeat_op_ntimes_rec e w n
      (repeat_op_ntimes_rec e n w)  (N.log2 (N.pos n)).
  Proof.
    induction n;
    intros e w.
    + specialize (IHn e w).
      assert (Hwt : ((N.pos n~1) = (2 * (N.pos n) + 1))%N).
      cbn; nia.
      rewrite Hwt; clear Hwt.
      rewrite N.log2_succ_double.
      remember ((N.log2 (N.pos n))) as p.
      cbn.
      apply xI_case.
      exact IHn.
      nia.
    + specialize (IHn e w).
      assert (Hwt : ((N.pos n~0) = (2 * (N.pos n)))%N).
      cbn; nia.
      rewrite Hwt; clear Hwt.
      rewrite N.log2_double.
      remember ((N.log2 (N.pos n))) as p.
      cbn.
      apply xO_case.
      exact IHn.
      nia.
    + cbn; apply xH_case.
  Qed.

  (** [Npow_mod_unary e n w] is the naive specification of modular
      exponentiation with a unary exponent [n : nat]: it multiplies by [e] and
      reduces modulo [w] [n] times, starting from [1].  It is linear in [n] and is
      used only as a reference for correctness proofs. *)
  Fixpoint Npow_mod_unary (e : N) (n : nat) (w : N) : N :=
    match n with
    | 0%nat => Npos xH
    | S n' => N.modulo (e * Npow_mod_unary e n' w) w
    end.

  (** [repeat_op_ntimes_acc e n w acc] is the tail-recursive (right-to-left)
      variant of square-and-multiply.  It scans the bits of [n] from the least
      significant one, squaring the base [e] at each step and multiplying it into
      the accumulator [acc] whenever the current bit is set.  It computes
      [acc · e ^ n mod w] ([positive_mul_group_acc_rec_connection]). *)
  Fixpoint repeat_op_ntimes_acc
    (e : N) (n : positive) (w acc : N) : N :=
    match n with
    | xH => N.modulo (e * acc) w
    | xO p =>
      let ee := (N.modulo (e * e) w) in
      repeat_op_ntimes_acc ee p w acc
    | xI p =>
      let ee := (N.modulo (e * e) w) in
      let ea := (N.modulo (e * acc) w) in
      repeat_op_ntimes_acc ee p w ea
    end.

  (** Squaring the base squares the result:
      [repeat_op_ntimes_rec ((e·e) mod w) n w = (r · r) mod w] where
      [r = repeat_op_ntimes_rec e n w].  This is the key step relating the
      right-to-left and left-to-right algorithms. *)
  Lemma op_pushes_out :
    forall n e w, prime (Z.of_N w) ->
    repeat_op_ntimes_rec ((e * e) mod w) n w =
    N.modulo (
      (repeat_op_ntimes_rec e n w * repeat_op_ntimes_rec e n w)) w.
  Proof.
    induction n.
    - simpl; intros ? ? Hw.
      rewrite IHn.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      remember (repeat_op_ntimes_rec e n w * repeat_op_ntimes_rec e n w)%N as enw.
      rewrite <- N.Div0.mul_mod_idemp_r.
      repeat rewrite N.Div0.mul_mod_idemp_l.
      repeat rewrite N.Div0.mul_mod_idemp_r.
      assert (Ht : (e * enw * (e * enw) =
        e * e * (enw * enw))%N). lia.
      rewrite Ht; clear Ht.
      repeat rewrite N.mul_assoc.
      rewrite N.Div0.mul_mod_idemp_r.
      reflexivity.
      all:(try lia; try assumption).
    - simpl; intros ? ? Hw.
      rewrite IHn.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      reflexivity. exact Hw.
    - simpl; intros ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite N.Div0.mod_mod.
      rewrite N.Div0.mul_mod_idemp_l.
      rewrite N.Div0.mul_mod_idemp_r.
      reflexivity.
  Qed.

  (** The accumulator version computes [acc] times the recursive one:
      [repeat_op_ntimes_acc e n w acc = (acc · repeat_op_ntimes_rec e n w) mod w].
      Proof by induction on [n], generalising [e] and [acc], with
      [op_pushes_out] for the squaring steps. *)
  Lemma positive_mul_group_acc_rec_connection :
    forall n e w acc,
    prime (Z.of_N w) ->
    repeat_op_ntimes_acc e n w acc = N.modulo (acc * repeat_op_ntimes_rec e n w) w.
  Proof.
    induction n.
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      specialize (IHn (N.modulo (e * e) w) w (N.modulo (e * acc) w)).
      rewrite IHn.
      rewrite op_pushes_out.
      remember (repeat_op_ntimes_rec e n w * repeat_op_ntimes_rec e n w)%N as enw.
      rewrite N.Div0.mul_mod_idemp_l.
      repeat rewrite N.Div0.mul_mod_idemp_r.
      assert (Ht : ((acc * (e * enw) = e * acc * enw)%N)).
      lia.
      rewrite Ht; clear Ht.
      reflexivity.
      all:(try lia; try assumption).
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite IHn. rewrite op_pushes_out.
      reflexivity.
      all:assumption.
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite N.Div0.mul_mod_idemp_r.
      assert (Ht : (acc * e = e * acc)%N). lia.
      rewrite Ht; clear Ht.
      reflexivity.
  Qed.

  (** [Npow_mod_constant_space e n w] is [e ^ n mod w] computed by the
      constant-space [repeat_op_ntimes_acc] with initial accumulator [1]. *)
  Definition Npow_mod_constant_space (e : N) (n w : N) :=
    match n with
    | N0 => Npos xH
    | Npos p => repeat_op_ntimes_acc e p w 1
    end.

  (** The two binary algorithms agree: for a prime modulus [w],
      [Npow_mod e n w = Npow_mod_constant_space e n w]. *)
  Lemma npow_mod_npow_constant_eqv :
    forall n e w,
    prime (Z.of_N w) ->
    Npow_mod e n w = Npow_mod_constant_space e n w.
  Proof.
    destruct n; simpl; intros ? ? Hw.
    - reflexivity.
    - pose proof positive_mul_group_acc_rec_connection p e w 1 Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite H. rewrite N.mul_1_l.
      destruct p.
      all:simpl; rewrite N.Div0.mod_mod; lia.
  Qed.

  (** The unary power is a reduced residue: [Npow_mod_unary e n w < w] when
      [w] is prime (only [w ≥ 2] is needed, so that [1 < w]). *)
  Lemma Npow_mod_unary_bound :
    forall (n : nat) (e w : N),
    prime (Z.of_N w) ->
    (Npow_mod_unary e n w < w)%N.
  Proof.
    induction n.
    - simpl; intros ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      lia.
    - simpl; intros ? ? Hw.
      apply N.mod_lt.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      lia.
  Qed.

  (** If [N.of_nat n = 0] then [n = 0]. *)
  Lemma binnat_zero :
    forall (n : nat), 0%N = N.of_nat n -> n = 0%nat.
  Proof.
    induction n; try lia.
  Qed.

  (** Exponent addition law for the reference model:
      [e ^ (n+m) mod w = ((e ^ n mod w) · (e ^ m mod w)) mod w], stated for
      [Npow_mod_unary].  It is the main tool in
      [npow_mod_exp_unary_binary_eqv]. *)
  Theorem Npow_mod_add_mul :
    forall n m e w,
    prime (Z.of_N w) ->
    Npow_mod_unary e (n + m) w = N.modulo (Npow_mod_unary e n w *
    Npow_mod_unary e m w) w.
  Proof.
    induction n.
    - intros ? ? ? Hw.
      rewrite Nat.add_0_l.
      assert (Ht : Npow_mod_unary e 0 w = Npos xH).
      simpl. reflexivity.
      rewrite Ht.
      rewrite N.mul_1_l.
      induction m.
      + simpl. rewrite N.mod_1_l.
        reflexivity.
        pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
        lia.
      + simpl. rewrite N.Div0.mod_mod.
        reflexivity.
    - simpl; intros ? ? ? Hw.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
      rewrite IHn.
      rewrite N.Div0.mul_mod_idemp_r.
      rewrite N.Div0.mul_mod_idemp_l.
      rewrite N.mul_assoc. reflexivity.
      assumption.
  Qed.

  (** If the binary number [2p+1] (written [xI p]) equals [N.of_nat n], then
      [n = 2k+1] for some [k] with [N.pos p = N.of_nat k]. *)
  Lemma binnat_odd :
    forall (p : positive) (n : nat),
    N.pos (xI p) = N.of_nat n ->
    exists k,  n = (2 * k + 1)%nat /\  (N.pos p) = (N.of_nat k).
  Proof.
    intros p n Hp.
    destruct (Nat.Even_or_Odd  n) as [H | H].
    destruct H as [k Hk].
    rewrite Hk in Hp; lia.
    destruct H as [k Hk].
    rewrite Hk in Hp. exists k.
    split. exact Hk. lia.
  Qed.

  (** If the binary number [2p] (written [xO p]) equals [N.of_nat n], then
      [n = 2k] for some [k] with [N.pos p = N.of_nat k]. *)
  Lemma binnat_even : forall (p : positive) (n : nat),
    N.pos (xO p) = N.of_nat n :> N ->
    exists k, n = (Nat.mul 2 k) /\  (N.pos p) = (N.of_nat k).
  Proof.
    intros p n Hp.
    destruct (Nat.Even_or_Odd n) as [H | H].
    destruct H as [k Hk].
    rewrite Hk in Hp. exists k.
    split. exact Hk. lia.
    destruct H as [k Hk].
    rewrite Hk in Hp. lia.
  Qed.

  (** The fast algorithm meets its specification: for a prime modulus,
      [Npow_mod_unary e (N.to_nat n) w = Npow_mod e n w].  Proof by induction
      on the positive exponent: the odd case splits [2p+1] as [p + p + 1] and the
      even case [2p] as [p + p], each closed with [Npow_mod_add_mul]. *)
  Lemma npow_mod_exp_unary_binary_eqv :
    forall (n : N) e w, prime (Z.of_N w) ->
    Npow_mod_unary e (N.to_nat n) w = Npow_mod e n w.
  Proof.
    destruct n.
    - simpl; intros ? ? Hw.
      reflexivity.
    - simpl; revert p.
      induction p.
      + simpl; intros ? ? Hw.
        pose proof (prime_ge_2 (Z.of_N w) Hw) as Htt.
        rewrite <-IHp.
        rewrite ZL6.
        rewrite Npow_mod_add_mul.
        rewrite N.Div0.mul_mod_idemp_r.
        reflexivity.
        exact Hw.
        exact Hw.
      + simpl; intros ? ? Hw.
        rewrite <-IHp.
        rewrite Pos2Nat.inj_xO.
        assert (Ht : (2 * Pos.to_nat p =
          Pos.to_nat p + Pos.to_nat p)%nat).
        lia. rewrite Ht.
        rewrite Npow_mod_add_mul.
        reflexivity.
        exact Hw.
        exact Hw.
      + simpl; intros ? ? Hw.
        rewrite N.mul_1_r.
        reflexivity.
  Qed.

  (** The base may be reduced first:
      [repeat_op_ntimes_rec e n w = repeat_op_ntimes_rec (e mod w) n w]. *)
  Lemma mod_reduce_pow :
    forall n e w, prime (Z.of_N w) ->
    repeat_op_ntimes_rec e n w =
    repeat_op_ntimes_rec (N.modulo e w) n w.
  Proof.
    induction n.
    - simpl; intros ? ? Hp.
      rewrite IHn.
      remember (repeat_op_ntimes_rec (e mod w) n w *
      repeat_op_ntimes_rec (e mod w) n w)%N as t.
      rewrite N.Div0.mul_mod_idemp_l.
      reflexivity. exact Hp.
    - simpl; intros ? ? Hp.
      rewrite IHn.
      reflexivity.
      exact Hp.
    - simpl; intros ? ? Hp.
      rewrite N.Div0.mod_mod.
      reflexivity.
  Qed.

  (** The same statement for [Npow_mod]: [e ^ n mod w = (e mod w) ^ n mod w]. *)
  Lemma Nmod_reduce_pow : forall n e w, prime (Z.of_N w) ->
    Npow_mod e n w = Npow_mod (N.modulo e w) n w.
  Proof.
    destruct n.
    - simpl; intros ? ? Hp.
      reflexivity.
    - simpl; intros ? ? Hp.
      apply mod_reduce_pow.
      exact Hp.
  Qed.

  (** If [w ≡ 0 (mod p)] then [Npow_mod (w mod p) k p = 0] for any exponent
      [k ≥ 2] (in fact any [k ≥ 1] would do). *)
  Lemma wp_mod_zero :
    forall (w k p : N),
    prime (Z.of_N p) ->
    (2 <= k)%N -> (2 <= p)%N ->
    (w mod p = 0)%N ->  (Npow_mod (w mod p) k p = 0)%N.
  Proof.
    intros ? ? ? Hp Hk Hpt Hwp.
    rewrite Hwp.
    unfold Npow_mod.
    destruct k. lia.
    clear Hk.
    induction p0.
    simpl. rewrite N.Div0.mod_0_l.
    reflexivity.
    simpl. rewrite IHp0.
    rewrite N.Div0.mod_0_l.
    reflexivity.
    simpl. rewrite N.Div0.mod_0_l.
    reflexivity.
  Qed.

  (** If [w ≡ 1 (mod p)] then [Npow_mod (w mod p) k p = 1] for [k ≥ 2] and
      [p ≥ 2]. *)
  Lemma wp_mod_one :
    forall (w k p : N),
    prime (Z.of_N p) ->
    (2 <= k)%N -> (2 <= p)%N ->
    (w mod p = 1)%N ->  (Npow_mod (w mod p) k p = 1)%N.
  Proof.
    intros ? ? ? Hp Hk Hpt Hwp.
    rewrite Hwp.
    unfold Npow_mod.
    destruct k. lia.
    clear Hk.
    induction p0.
    simpl. rewrite IHp0.
    simpl. rewrite N.mod_1_l.
    reflexivity. lia.
    simpl. rewrite IHp0.
    rewrite N.mod_1_l.
    reflexivity. lia.
    simpl. rewrite N.mod_1_l.
    reflexivity. lia.
  Qed.

  (** Bridge to the integers: for a prime modulus [w],
      [Z.of_N (Npow_mod a b w) = Zpow_mod (Z.of_N a) (Z.of_N b) (Z.of_N w)].
      This is the lemma client files ([Zpstar.v], [SchnorrOrder.v]) use to move
      between the executable [N] exponentiation and [Z]-level number theory.
      The proof rewrites [Zpow_mod] with [Zpow_mod_correct] and proceeds by
      induction on the positive exponent, splitting [Z.pow_pos] with
      [Zpower_pos_is_exp] and pushing [mod] through products. *)
  Lemma zmod_nmod :
    forall (b a w : N),
    prime (Z.of_N w) ->
    Z.of_N (Npow_mod a b w) =
    Zpow_mod (Z.of_N a) (Z.of_N b) (Z.of_N w).
  Proof.
    intros ? ? ? Hw.
    rewrite Zpow_mod_correct.
    destruct b; simpl.
    - symmetry.
      rewrite Z.mod_1_l.
      reflexivity.
      pose proof (prime_ge_2 (Z.of_N w) Hw) as Ht.
      lia.
    (* Exponent zero is handled above; now induct on the positive exponent. *)
    - revert p.
      induction p.
      (* Odd case [2p+1]: split [a^(p+p+1)] and reduce each factor modulo [w]. *)
      + simpl.
        assert (Ht : (p~1 = p + p + 1)%positive).
        lia. rewrite Ht.
        rewrite Zpower_pos_is_exp.
        rewrite Zpower_pos_is_exp.
        rewrite Zpower_pos_1_r.
        rewrite N2Z.inj_mod.
        rewrite N2Z.inj_mul.
        rewrite N2Z.inj_mul.
        rewrite IHp.
        remember (Z.pow_pos (Z.of_N a) p) as zps.
        remember (Z.of_N a) as za.
        remember (Z.of_N w) as zw.
        assert (Hzp: zps * zps * za = za * (zps * zps)).
        lia. rewrite Hzp; clear Hzp; clear Ht.
        rewrite <-Zmult_mod_idemp_l.
        assert (Ht : (za * (zps * zps)) mod zw = (za mod zw * (zps * zps)) mod zw).
        rewrite <-Zmult_mod_idemp_l.
        reflexivity. rewrite Ht; clear Ht.
        assert (Ht : (za mod zw * (zps * zps)) mod zw =
        (za mod zw * ((zps * zps) mod zw)) mod zw).
        rewrite <-Zmult_mod_idemp_r. reflexivity.
        rewrite Ht; clear Ht.
        assert (Ht : (zps * zps) mod zw =
          (zps mod zw * (zps mod zw)) mod zw).
        rewrite <-Zmult_mod_idemp_l.
        rewrite <-Zmult_mod_idemp_r.
        reflexivity.
        rewrite Ht.
        rewrite Zmult_mod_idemp_r.
        reflexivity.
      (* Even case [2p]: [a^(p+p)] is the square of [a^p]. *)
      + simpl.
        assert (Ht : (p~0 = p + p)%positive).
        lia. rewrite Ht.
        rewrite Zpower_pos_is_exp.
        rewrite N2Z.inj_mod.
        rewrite N2Z.inj_mul.
        rewrite IHp.
        remember (Z.pow_pos (Z.of_N a) p) as zps.
        remember (Z.of_N a) as za.
        remember (Z.of_N w) as zw.
        rewrite Zmult_mod_idemp_l.
        rewrite Zmult_mod_idemp_r.
        reflexivity.
      (* Base case [p = 1]. *)
      + simpl. rewrite Zpower_pos_1_r.
        rewrite N2Z.inj_mod.
        reflexivity.
    - pose proof (prime_ge_2 (Z.of_N w) Hw) as Ht.
      lia.
  Qed.

  (** Bridge to [nat]: [Npow_mod_unary (N.of_nat a) n (N.of_nat p)] equals
      [N.of_nat ((a ^ n) mod p)] when [p] is prime. *)
  Lemma npow_mod_nat : forall (n a p : nat),
    prime (Z.of_nat p) ->
    Npow_mod_unary (N.of_nat a) n (N.of_nat p) =
    N.of_nat (Nat.modulo (Nat.pow a n) p).
  Proof.
    induction n.
    + intros * Hp.
      pose proof prime_ge_2 (Z.of_nat p) Hp as Hf.
      simpl. rewrite Nat.mod_1_l.
      lia. lia.
    + intros * Hp.
      simpl.
      pose proof (IHn a p Hp).
      rewrite H.
      rewrite <-Nat2N.inj_mul,
      <-Nat2N.inj_mod.
      f_equal.
      rewrite Nat.Div0.mul_mod_idemp_r.
      reflexivity.
  Qed.

  (** [(a ^ n) mod p] on [N] equals the same expression computed on [nat] and
      converted back with [N.of_nat].  (The primality hypothesis is unused.) *)
  Lemma N_to_nat_exp : forall (n a p : N),
    prime (Z.of_N p) ->
    N.modulo (N.pow a n) p =
    N.of_nat (Nat.modulo (Nat.pow (N.to_nat a)
      (N.to_nat n)) (N.to_nat p)).
  Proof.
    intros * Hp.
    rewrite <-N2Nat.inj_pow.
    rewrite <-N2Nat.inj_mod.
    lia.
  Qed.

End Fn.
