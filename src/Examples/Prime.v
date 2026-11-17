(** * Primality of small integers by trial division *)

(** The small textbook instances of the library ([SigmaIns.v],
[ElgamalIns.v], [ChaumPedersenIns.v] and the other examples over the toy
safe-prime group [p = 2·2963 + 1 = 5927]) need proofs that [p] and [q] are
prime. For numbers this small a Coqprime certificate is unnecessary: this
file provides a boolean trial-division test [is_prime_sqrt] and proves it
sound ([is_prime_sqrt_correct]), so that [prime n] follows from
[is_prime_sqrt n = true] by computation (proof by reflection).

The test checks that [n > 1] and that every [k] with [1 ≤ k ≤ ⌊√n⌋] is
coprime to [n]. Its cost is linear in [√n], so it is only usable for small
moduli; the cryptographic-size primes of the real-system instances are
handled by the certificates of [primeP.v], [primeQ.v], [primeQEG.v],
[primePEG.v] and [primeQSP.v]. *)

From Stdlib Require Import ZArith
Znumtheory Psatz Utf8.

(** [iterate_fn f n] is the conjunction [f n && f (n-1) && … && f 1] of a
    boolean predicate over the integers [1..n] (with [n] given as a natural
    number). It is the loop of the trial-division test. *)
Fixpoint iterate_fn (f : Z -> bool) (n : nat) : bool :=
  match n with
  | O => true
  | S m => f (Z.of_nat n) && iterate_fn f m
  end.

(** Soundness of [iterate_fn]: if [iterate_fn f n = true] then [f k = true]
    for every integer [k] with [1 ≤ k ≤ n]. Proved by induction on [n],
    splitting on whether [k] is the top value [n] or below it. *)
Lemma iterate_fn_spec_prime :
  ∀ (n : nat) (f : Z → bool), iterate_fn f n = true ->
  ∀ (k : Z), 1 <= k <= Z.of_nat n -> f k = true.
Proof.
  induction n as [|n ihn].
  +
    intros * ha * hb.
    nia.
  +
    intros * ha * hb.
    cbn in ha.
    eapply Bool.andb_true_iff in ha as [hal har].
    assert (hc : k = Z.of_nat (S n) ∨ 1 <= k <= Z.of_nat n) by nia.
    destruct hc as [hc | hc].
    ++
      subst. exact hal.
    ++
      eapply ihn; try assumption.
Qed.

(** [is_prime_sqrt p] decides [1 < p] and [gcd k p = 1] for every
    [1 ≤ k ≤ ⌊√p⌋]. Note that [k = 1] is always coprime, so the test is
    trial division by [2..⌊√p⌋]. *)
Definition is_prime_sqrt (p : Z) : bool :=
  (1 <? p) && iterate_fn (fun k => Z.gcd k p =? 1)
  (Z.to_nat (Z.sqrt p)).

(** A composite number has a small divisor: if [1 < n] and [n] is not
    prime, there is a [d] with [1 < d ≤ ⌊√n⌋] and [d | n]. Given any
    nontrivial factorisation [n = v·p], either [p] or the cofactor [n/p] is
    at most [⌊√n⌋]. *)
Lemma composite_has_divisor_sqrt :
  ∀ n, 1 < n -> ~prime n ->
  exists d, 1 < d <= Z.sqrt n /\ (d | n).
Proof.
  intros n Hn Hnp.
  destruct (not_prime_divide n Hn Hnp) as (p & hp & (v & hv)).
  destruct (Z.le_gt_cases p (Z.sqrt n)) as [ha | ha].
  +
    (* The divisor p from not_prime_divide is already at most the root. *)
    exists p; split; auto. split; [|assumption]. nia.
    eexists. exact hv.
    (* Otherwise p exceeds the root, and the cofactor n/p = v is below it:
       from s·s ≤ v·p < (s+1)·(s+1) with s = ⌊√(v·p)⌋ and s + 1 ≤ p. *)
  +
    exists (n/p); split.
    ++
      split.
      *
        rewrite hv in hp.
        assert (hb : n/p = v).
        rewrite hv.
        rewrite Z.div_mul.
        reflexivity. nia.
        rewrite hb. nia.
      *
        subst n.
        rewrite Z.div_mul;[|try nia].
        remember (Z.sqrt (v * p)) as s.
        assert (hb : s * s <= v * p < Z.succ s * Z.succ s).
        {
          split.
          +
            pose proof Z.sqrt_mul_below (v * p) (v * p) as hb.
            rewrite <-Heqs in hb. rewrite Z.sqrt_square in hb;[|try nia].
            exact hb.
          +

            assert (hb : v * p = Z.sqrt (v * p * (v * p))).
            rewrite Z.sqrt_square. reflexivity. nia.
            rewrite hb.
            pose proof Z.sqrt_mul_above (v * p) (v * p) (ltac:(nia))
            (ltac:(nia)) as hc. rewrite Heqs.
            exact hc.
        }
        assert (hc : Z.succ s <= p) by nia.
        assert(hd : v * p <= Z.succ s * p). nia.
        nia.
    ++
      exists p.
      rewrite !hv. rewrite Z.div_mul.
      nia. nia.
Qed.

(** Soundness of the test: [is_prime_sqrt n = true] implies [prime n].

    Proof idea: the test gives [1 < n] and [gcd k n = 1] for all
    [1 ≤ k ≤ ⌊√n⌋]. If [n] were not prime, [composite_has_divisor_sqrt]
    would give a divisor [d] in that range, and then [gcd d n = d > 1],
    a contradiction. The examples use it as
    [eapply is_prime_sqrt_correct; compute; reflexivity]. *)
Theorem is_prime_sqrt_correct :
  ∀ (n : Z), is_prime_sqrt n = true -> prime n.
Proof.
  intros * ha.
  unfold is_prime_sqrt in ha.
  apply Bool.andb_true_iff in ha;
  destruct ha as [halt haiter].
  rewrite Z.ltb_lt in halt.
  assert (hb : forall k, 1 <= k <= Z.sqrt n -> Z.gcd k n = 1).
  {
    intros k ha.
    eapply iterate_fn_spec_prime with (k := k), Z.eqb_eq  in haiter.
    exact haiter.
    rewrite Z2Nat.id.
    exact ha. nia.
  }
  (* By contradiction: a composite n has a divisor d ≤ √n with gcd d n = d. *)
  destruct (prime_dec n) as [hp | hnp]; [assumption|].
  destruct (composite_has_divisor_sqrt n halt hnp) as [d [hc hd]].
  assert (Hd_pos : 0 < d) by lia.
  assert (Hgcd : Z.gcd d n = d).
  {
    apply Z.gcd_unique; auto.
    - nia.
    - exists 1. nia.
  }
  assert (ha : 1 <= d <= Z.sqrt n). nia.
  specialize (hb _ ha).
  rewrite hb in Hgcd.
  nia.
Qed.
