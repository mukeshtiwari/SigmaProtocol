(* Every element other than 1 of the Schnorr group of Zpstar.v has order 
   exactly q: the group elements satisfy v^q = 1 mod p by construction, and 
   q is prime. Consequently exponentiation g ^ (.) : Zp -> Schnorr_group is 
   injective for g <> 1, and the field Zp has characteristic q, so the 
   map nat -> Zp (sums of 1) is injective below q. These discharge the two 
   hypotheses exp_injective / natF_injective of the Schulze soundness 
   theorems (Frontend/Schulze.v, Backend/SchulzeTally.v) for the Zpstar 
   instances. *)
From Stdlib Require Import Utf8 ZArith Znumtheory Zpow_facts Lia Psatz.
From Utility Require Import Zpstar Functions Util.
Import Zpfield Schnorr Vspace.

Local Open Scope Z_scope.

Section ZOrder.

  (* p does not divide any power of v, 0 < v < p *)
  Lemma pow_not_divisible : ∀ (p v e : Z), prime p -> 0 < v < p -> 0 <= e -> ~ (p | v ^ e).
  Proof.
    intros p v e hp hv he.
    pose proof (proj2 (prime_alt _) hp) as hp'.
    pattern e; apply natlike_ind; [| | exact he].
    + rewrite Z.pow_0_r; intro hd.
      pose proof (Z.divide_pos_le p 1 ltac:(lia) hd).
      pose proof (prime_ge_2 _ hp); lia.
    + intros x hx ih hd.
      rewrite Z.pow_succ_r in hd by exact hx.
      apply Z.divide_prime_mul in hd; [| exact hp'].
      destruct hd as [hd | hd]; [| exact (ih hd)].
      pose proof (Z.divide_pos_le p v ltac:(lia) hd); lia.
  Qed.

  (* equal powers give a power equal to 1 *)
  Lemma pow_mod_eq_one : ∀ (p v a b : Z), prime p -> 0 < v < p -> 0 <= b <= a ->
    v ^ a mod p = v ^ b mod p -> v ^ (a - b) mod p = 1.
  Proof.
    intros p v a b hp hv hab heq.
    pose proof (proj2 (prime_alt _) hp) as hp'.
    pose proof (prime_ge_2 _ hp) as hp2.
    assert (hd : (p | v ^ a - v ^ b)).
    { apply Z.mod_divide; [lia |].
      rewrite Zminus_mod, heq, Z.sub_diag; apply Zmod_0_l. }
    replace a with ((a - b) + b) in hd at 1 by lia.
    rewrite Z.pow_add_r in hd by lia.
    replace (v ^ (a - b) * v ^ b - v ^ b) with (v ^ b * (v ^ (a - b) - 1)) in hd by ring.
    apply Z.divide_prime_mul in hd; [| exact hp'].
    destruct hd as [hd | hd].
    + exfalso; exact (pow_not_divisible p v b hp hv ltac:(lia) hd).
    + apply Z.mod_divide in hd; [| lia].
      replace (v ^ (a - b)) with ((v ^ (a - b) - 1) + 1) by ring.
      rewrite Z.add_mod, hd, Z.add_0_l, Z.mod_mod by lia.
      apply Z.mod_small; lia.
  Qed.

  (* v^q = 1, q prime, v <> 1: no smaller positive power of v is 1 *)
  Lemma prime_order : ∀ (p q v : Z), prime p -> prime q -> 0 < v < p -> v <> 1 ->
    v ^ q mod p = 1 -> ∀ z, 0 < z < q -> v ^ z mod p <> 1.
  Proof.
    intros p q v hp hq hv hv1 hvq z hz hz1.
    pose proof (proj2 (prime_alt _) hq) as hq'.
    pose proof (prime_ge_2 _ hp) as hp2.
    pose proof (prime_ge_2 _ hq) as hq2.
    (* z is invertible modulo q *)
    assert (hcop : Z.coprime q z).
    { apply Z.coprime_prime_l; [exact hq' |].
      intro hd; pose proof (Z.divide_pos_le q z ltac:(lia) hd); lia. }
    destruct (Z.Bezout_coprime _ _ hcop) as (a & b & hab).
    (* u * z = 1 + q * t with u, t >= 0 *)
    set (u := b mod q).
    set (t := - a - (b / q) * z).
    assert (hu : 0 <= u) by (apply Z.mod_pos_bound; lia).
    assert (huz : u * z = 1 + q * t).
    { unfold u, t; pose proof (Z_div_mod_eq_full b q) as hb; nia. }
    assert (ht : 0 <= t) by nia.
    (* v^(u z) = (v^z)^u = 1 and v^(u z) = v * (v^q)^t = v modulo p *)
    assert (h1 : v ^ (u * z) mod p = 1).
    { rewrite Z.mul_comm, Z.pow_mul_r, Zpower_mod, hz1, Z.pow_1_l by lia.
      apply Z.mod_small; lia. }
    assert (h2 : v ^ (u * z) mod p = v).
    { rewrite huz, Z.pow_add_r, Z.pow_1_r, Z.pow_mul_r, Z.mul_mod, Zpower_mod, hvq, 
        Z.pow_1_l, (Z.mod_small 1 p), Z.mul_1_r, Z.mod_mod by lia.
      apply Z.mod_small; lia. }
    lia.
  Qed.

End ZOrder.

Section SchnorrOrder.

  Context {k p q : Z} {Hk : p = k * q + 1} {Hp : prime p} {Hq : prime q}.

  Local Notation Schnorr_group := (@Schnorr_group p q).
  Local Notation Zp := (@Zp q).
  Local Notation pow := (@pow k p q Hk Hp Hq).
  Local Notation one := (@Schnorr.one p q Hp Hq).

  (* the value of g ^ y *)
  Lemma pow_v : ∀ (g : Schnorr_group) (y : Zp), 
    Schnorr.v (pow g y) = (Schnorr.v g) ^ (Zpfield.v y) mod p.
  Proof.
    intros [gv ga gb] [yv hy]; cbn.
    pose proof (prime_ge_2 _ Hp).
    pose proof (prime_ge_2 _ Hq).
    pose proof (Z.mod_pos_bound yv q ltac:(lia)); rewrite hy in *.
    rewrite zmod_nmod, Zpow_mod_correct, !Z2N.id; try lia.
    rewrite Z2N.id; [exact Hp | lia].
  Qed.

  Lemma v_one : Schnorr.v one = 1.
  Proof. reflexivity. Qed.

  Lemma schnorr_eq_v : ∀ (a b : Schnorr_group), Schnorr.v a = Schnorr.v b -> a = b.
  Proof. intros [] [] h; cbn in h; apply construct_schnorr_group; exact h. Qed.

  Lemma zp_eq_v : ∀ (a b : Zp), Zpfield.v a = Zpfield.v b -> a = b.
  Proof. intros [] [] h; cbn in h; apply construct_zp; exact h. Qed.

  Lemma zp_bound : ∀ (a : Zp), 0 <= Zpfield.v a < q.
  Proof.
    intros [av ha]; cbn; pose proof (prime_ge_2 _ Hq).
    pose proof (Z.mod_pos_bound av q ltac:(lia)); lia.
  Qed.

  (* exponentiation with a non-identity base is injective *)
  Theorem pow_injective : ∀ (g : Schnorr_group) (a b : Zp), 
    g <> one -> pow g a = pow g b -> a = b.
  Proof.
    intros g a b hg hab.
    apply (f_equal Schnorr.v) in hab; rewrite !pow_v in hab.
    assert (hg1 : Schnorr.v g <> 1).
    { intro h; apply hg, schnorr_eq_v; cbn; exact h. }
    pose proof (Schnorr.Ha g) as ga.
    pose proof (Schnorr.Hb g) as gb.
    rewrite Zpow_mod_correct in gb by (pose proof (prime_ge_2 _ Hp); lia).
    set (gv := Schnorr.v g) in *.
    pose proof (zp_bound a) as hba; pose proof (zp_bound b) as hbb.
    apply zp_eq_v.
    destruct (Z_le_gt_dec (Zpfield.v b) (Zpfield.v a)) as [hle | hgt].
    + pose proof (pow_mod_eq_one p gv (Zpfield.v a) (Zpfield.v b) Hp ga ltac:(lia) hab) as h1.
      destruct (Z.eq_dec (Zpfield.v a) (Zpfield.v b)) as [heq | hne]; [exact heq |].
      exfalso; exact (prime_order p q gv Hp Hq ga hg1 gb (Zpfield.v a - Zpfield.v b) ltac:(lia) h1).
    + pose proof (pow_mod_eq_one p gv (Zpfield.v b) (Zpfield.v a) Hp ga ltac:(lia) (Logic.eq_sym hab)) as h1.
      exfalso; exact (prime_order p q gv Hp Hq ga hg1 gb (Zpfield.v b - Zpfield.v a) ltac:(lia) h1).
  Qed.

  (* the field Zp has characteristic q: nat_to_F counts modulo q *)
  Local Notation natF := (nat_to_F (@Zpfield.zero q Hq) (@Zpfield.one q Hq) (@zp_add q)).

  Lemma zp_add_v : ∀ (a b : Zp), Zpfield.v (zp_add a b) = (Zpfield.v a + Zpfield.v b) mod q.
  Proof. intros [] []; reflexivity. Qed.

  Lemma natF_v : ∀ (n : nat), Zpfield.v (natF n) = Z.of_nat n mod q.
  Proof.
    pose proof (prime_ge_2 _ Hq).
    induction n as [| n ih].
    + cbn; rewrite ?Z.mod_0_l by lia; reflexivity.
    + change (natF (S n)) with (zp_add (@Zpfield.one q Hq) (natF n)).
      rewrite zp_add_v, ih.
      change (Zpfield.v (@Zpfield.one q Hq)) with 1.
      rewrite Z.add_mod_idemp_r, Nat2Z.inj_succ by lia.
      f_equal; lia.
  Qed.

  Theorem natF_injective_below_q : ∀ (B : nat), Z.of_nat B < q -> 
    ∀ (a b : nat), (a <= B)%nat -> (b <= B)%nat -> natF a = natF b -> a = b.
  Proof.
    intros B hB a b ha hb hab.
    apply (f_equal Zpfield.v) in hab; rewrite !natF_v in hab.
    rewrite !Z.mod_small in hab by lia.
    lia.
  Qed.

End SchnorrOrder.
