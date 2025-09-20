From Stdlib Require Import ZArith 
Znumtheory Psatz Utf8.


(* A simple proof by reflection for primality testing. *)
Fixpoint iterate_fn (f : Z -> bool) (n : nat) : bool :=
  match n with
  | O => true 
  | S m => f (Z.of_nat n) && iterate_fn f m
  end.

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

(* A number n is prime if it is greater than 1 and 
and coprime to all numbers up sqrt n *)
Definition is_prime_sqrt (p : Z) : bool :=
  (1 <? p) && iterate_fn (fun k => Z.gcd k p =? 1)
  (Z.to_nat (Z.sqrt p)).


Lemma composite_has_divisor_sqrt :
  ∀ n, 1 < n -> ~prime n -> 
  exists d, 1 < d <= Z.sqrt n /\ (d | n).
Proof.
  intros n Hn Hnp.
  destruct (not_prime_divide n Hn Hnp) as (p & hp & (v & hv)).
  destruct (Z.le_gt_cases p (Z.sqrt n)) as [ha | ha]. 
  +
    exists p; split; auto. split; [|assumption]. nia.
    eexists. exact hv.
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
  (* Prove n is prime by contradiction *)
  destruct (prime_dec n) as [hp | hnp]; [assumption|].
  destruct (composite_has_divisor_sqrt n halt hnp) as [d [hc hd]].
  (* d satisfies gcd d n = d (since d divides n) *)
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

