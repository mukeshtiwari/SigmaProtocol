(** * Order facts for Schnorr groups *)

(** A Schnorr group is the order-[q] subgroup of [Z_p^*] for primes [p] and
    [q] with [p = k q + 1] (Schnorr 1991). In [Utility/Zpstar.v] its elements
    are represented by the record [Schnorr_group] (an integer [v] with
    [0 < v < p] and [v ^ q mod p = 1]) and exponents by [Zp] (integers modulo
    [q]); [pow g y] is modular exponentiation.

    This file proves that exponentiation with a non-identity base is
    injective on exponents ([pow_injective]), that is, every element other
    than [1] has order exactly [q], and that the embedding of natural
    numbers into [Z_q] is injective below [q] ([natF_injective_below_q]).
    Both facts are needed to decode tallies: a homomorphically aggregated
    ciphertext decrypts to [g ^ m], and [m] (a vote count smaller than [q])
    is recovered uniquely by search. They are instantiated in
    [Examples/SchulzeIns.v]. *)
From Stdlib Require Import Utf8 ZArith Znumtheory Zpow_facts Lia Psatz.
From Utility Require Import Zpstar Functions Util.
Import Zpfield Schnorr Vspace.

Local Open Scope Z_scope.

(** ** Integer lemmas *)
Section ZOrder.

  (** For a prime [p] and [0 < v < p], [p] does not divide [v ^ e] for any
      [e ≥ 0]. Induction on [e] using that a prime dividing a product
      divides a factor. *)
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

  (** Cancellation of powers modulo a prime: if [0 < v < p],
      [0 ≤ b ≤ a] and [v ^ a ≡ v ^ b (mod p)], then
      [v ^ (a - b) ≡ 1 (mod p)]. Proof: [p] divides
      [v ^ b · (v ^ (a - b) - 1)] and not [v ^ b]. *)
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

  (** _Prime order._ If [v ≠ 1], [0 < v < p] and [v ^ q ≡ 1 (mod p)] with
      [q] prime, then [v ^ z ≢ 1 (mod p)] for every [0 < z < q]. Proof: if
      [v ^ z ≡ 1], Bézout gives [u ≥ 0], [t ≥ 0] with [u z = 1 + q t], hence
      [1 ≡ v ^ (u z) ≡ v · (v ^ q) ^ t ≡ v], a contradiction. *)
  Lemma prime_order : ∀ (p q v : Z), prime p -> prime q -> 0 < v < p -> v <> 1 ->
    v ^ q mod p = 1 -> ∀ z, 0 < z < q -> v ^ z mod p <> 1.
  Proof.
    intros p q v hp hq hv hv1 hvq z hz hz1.
    pose proof (proj2 (prime_alt _) hq) as hq'.
    pose proof (prime_ge_2 _ hp) as hp2.
    pose proof (prime_ge_2 _ hq) as hq2.
    assert (hcop : Z.coprime q z).
    { apply Z.coprime_prime_l; [exact hq' |].
      intro hd; pose proof (Z.divide_pos_le q z ltac:(lia) hd); lia. }
    (* Bézout: from [a q + b z = 1] build [u = b mod q] and [t ≥ 0] with
       [u z = 1 + q t]. *)
    destruct (Z.Bezout_coprime _ _ hcop) as (a & b & hab).
    set (u := b mod q).
    set (t := - a - (b / q) * z).
    assert (hu : 0 <= u) by (apply Z.mod_pos_bound; lia).
    assert (huz : u * z = 1 + q * t).
    { unfold u, t; pose proof (Z_div_mod_eq_full b q) as hb; nia. }
    assert (ht : 0 <= t) by nia.
    (* Evaluate [v ^ (u z)] in two ways: as [(v ^ z) ^ u ≡ 1] and as
       [v · (v ^ q) ^ t ≡ v]. *)
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

(** ** Schnorr-group consequences *)
Section SchnorrOrder.

  (** Parameters: primes [p] and [q] with [p = k q + 1]. *)
  Context {k p q : Z} {Hk : p = k * q + 1} {Hp : prime p} {Hq : prime q}.

  Local Notation Schnorr_group := (@Schnorr_group p q).
  Local Notation Zp := (@Zp q).
  Local Notation pow := (@pow k p q Hk Hp Hq).
  Local Notation one := (@Schnorr.one p q Hp Hq).

  (** The underlying integer of [g ^ y] is [v(g) ^ v(y) mod p]. *)
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

  (** The identity of the Schnorr group is represented by [1]. *)
  Lemma v_one : Schnorr.v one = 1.
  Proof. reflexivity. Qed.

  (** Elements of the Schnorr group, respectively of [Zp], are equal when
      their underlying integers are (the proof components are irrelevant). *)
  Lemma schnorr_eq_v : ∀ (a b : Schnorr_group), Schnorr.v a = Schnorr.v b -> a = b.
  Proof. intros [] [] h; cbn in h; apply construct_schnorr_group; exact h. Qed.

  Lemma zp_eq_v : ∀ (a b : Zp), Zpfield.v a = Zpfield.v b -> a = b.
  Proof. intros [] [] h; cbn in h; apply construct_zp; exact h. Qed.

  (** The representative of an element of [Zp] satisfies [0 ≤ v < q]. *)
  Lemma zp_bound : ∀ (a : Zp), 0 <= Zpfield.v a < q.
  Proof.
    intros [av ha]; cbn; pose proof (prime_ge_2 _ Hq).
    pose proof (Z.mod_pos_bound av q ltac:(lia)); lia.
  Qed.

  (** _Injectivity of exponentiation._ For [g ≠ 1] in the Schnorr group,
      [g ^ a = g ^ b] implies [a = b] in [Z_q]. Proof: assume without loss
      of generality [b ≤ a] as integers; [pow_mod_eq_one] gives
      [g ^ (a - b) ≡ 1] with [0 ≤ a - b < q], and [prime_order] forces
      [a - b = 0]. *)
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

  (** [natF n] is [1 + 1 + ⋯ + 1] ([n] times) in [Z_q], via [nat_to_F]. *)
  Local Notation natF := (nat_to_F (@Zpfield.zero q Hq) (@Zpfield.one q Hq) (@zp_add q)).

  (** The representative of a sum in [Zp] is the sum of representatives
      reduced modulo [q]. *)
  Lemma zp_add_v : ∀ (a b : Zp), Zpfield.v (zp_add a b) = (Zpfield.v a + Zpfield.v b) mod q.
  Proof. intros [] []; reflexivity. Qed.

  (** The representative of [natF n] is [n mod q]. *)
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

  (** For a bound [B < q], the map [natF] is injective on [{0, …, B}]:
      distinct counts [a, b ≤ B] have distinct images in [Z_q]. *)
  Theorem natF_injective_below_q : ∀ (B : nat), Z.of_nat B < q ->
    ∀ (a b : nat), (a <= B)%nat -> (b <= B)%nat -> natF a = natF b -> a = b.
  Proof.
    intros B hB a b ha hb hab.
    apply (f_equal Zpfield.v) in hab; rewrite !natF_v in hab.
    rewrite !Z.mod_small in hab by lia.
    lia.
  Qed.

End SchnorrOrder.
