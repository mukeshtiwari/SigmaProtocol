From Stdlib Require Import Setoid setoid_ring.Field Psatz Vector Utf8 Fin Lia ZArith List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import Elgamal BayerGrothSound.
From Frontend Require Import Schulze SchulzeBatched.
From Backend Require Import SchulzeTally.
Import VectorNotations.

(* The end-to-end theorem of Backend/SchulzeTally.v for the batched ballot of
   Frontend/SchulzeBatched.v: accepted batched ballots (in the rewinding
   form of ballot2_sound) and an accepted certificate on the aggregate of
   their ciphertext matrices name a Schulze winner of the positions the
   ballots commit to, unless a commitment key is broken. *)

Section SchulzeBatchedTally.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Infix "^" := gpow.
  Local Infix "+" := add.
  Local Notation natF := (nat_to_F zero one add).
  Local Notation cmul := (Schulze.cmul (gop := gop)).
  Local Notation cid := (Schulze.cid (gid := gid)).
  Local Notation cdec := (Schulze.cdec (ginv := ginv) (gop := gop) (gpow := gpow)).
  Local Notation pow_add := (pow_add (Hvec := Hvec)).
  Local Notation pow_zero := (pow_zero (Hvec := Hvec)).
  Local Notation pow_gid := (pow_gid (Hvec := Hvec)).
  Local Notation gop_ginv_r := (gop_ginv_r (Hvec := Hvec)).
  Local Notation cdec_cmul := (cdec_cmul (Hvec := Hvec)).
  Local Notation natF_add := (natF_add (Hvec := Hvec)).
  Local Notation exp_injective := (Schulze.exp_injective (gpow := gpow)).
  Local Notation natF_injective := (Schulze.natF_injective (zero := zero) (one := one) (add := add)).
  Local Notation ballot2_rewound n := (@SchulzeBatched.ballot2_rewound F zero one add mul sub opp Fdec G gid gop gpow Gdec n).
  Local Notation ballot2_bits n := (@SchulzeBatched.ballot2_bits F G gid n).
  Local Notation verify_tally := (SchulzeTally.verify_tally (zero := zero) (one := one) (add := add) (Fdec := Fdec)
    (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation encrypts := (SchulzeTally.encrypts (zero := zero) (one := one) (add := add)
    (ginv := ginv) (gop := gop) (gpow := gpow)).
  Local Notation binding_break := (BayerGrothSound.binding_break (gid := gid) (gop := gop) (gpow := gpow)).

  (* the aggregate of ciphertext matrices, as aggregate_margins reads the
     matrices of the first ballot *)
  Definition aggregate_bits {m N : nat} (ms : Vector.t (Vector.t (Vector.t (G * G) m) m) N) :
    Vector.t (Vector.t (G * G) m) m :=
    Vector.fold_right (fun b acc => Vector.map2 (Vector.map2 cmul) b acc) ms (Vector.const (Vector.const cid m) m).

  Lemma cdec_aggregate_bits : ∀ {m N : nat} (x : F) (g : G) (ms : Vector.t (Vector.t (Vector.t (G * G) m) m) N)
    (ss : Vector.t (Vector.t nat m) N) (i j : Fin.t m),
    (∀ k, cdec x ms[@k][@i][@j] = g ^ (if Nat.ltb ss[@k][@i] ss[@k][@j] then one else zero)) ->
    cdec x (aggregate_bits ms)[@i][@j] = g ^ natF (margin_count ss i j).
  Proof.
    intros m N x g; induction N as [| N ih]; intros ms ss i j hb.
    + rewrite (vector_inv_0 ms), (vector_inv_0 ss).
      unfold aggregate_bits; cbn [Vector.fold_right].
      rewrite !Vector.const_nth; unfold Schulze.cid, Schulze.cdec; cbn.
      rewrite pow_gid, gop_ginv_r, pow_zero; reflexivity.
    + destruct (vector_inv_S ms) as (b & ms' & ->).
      destruct (vector_inv_S ss) as (s & ss' & ->).
      change (aggregate_bits (b :: ms')) with (Vector.map2 (Vector.map2 cmul) b (aggregate_bits ms')).
      rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl), (Vector.nth_map2 _ _ _ j j j eq_refl eq_refl).
      rewrite cdec_cmul, (ih ms' ss' i j (fun k => hb (Fin.FS k))).
      pose proof (hb Fin.F1) as h0; cbn [Vector.nth] in h0.
      rewrite h0; unfold margin_count; cbn [Vector.fold_right].
      rewrite natF_add, pow_add; f_equal; f_equal.
      destruct (Nat.ltb s[@i] s[@j]); cbn [nat_to_F]; field.
  Qed.

  (* finite choice with an escape clause *)
  Lemma fin_choice_or : ∀ (k : nat) (A : Type) (Q : Prop) (P : Fin.t k -> A -> Prop),
    (∀ i, Q ∨ ∃ a, P i a) -> Q ∨ ∃ f : Fin.t k -> A, ∀ i, P i (f i).
  Proof.
    induction k as [| k ih]; intros A Q P hP.
    + right; exists (fun i => Fin.case0 (fun _ => A) i); intro i; inversion i.
    + destruct (hP Fin.F1) as [hq | (a0 & h0)]; [left; exact hq |].
      destruct (ih A Q (fun i a => P (Fin.FS i) a) (fun i => hP (Fin.FS i))) as [hq | (f & hf)]; [left; exact hq |].
      right; exists (fun i => Fin.caseS' i (fun _ => A) a0 f).
      intro i; apply (Fin.caseS' i); [exact h0 | intro j; exact (hf j)].
  Qed.

  Theorem schulze_end_to_end2 : ∀ (n n' k L : nat) (x : F) (g h h1 : G) (gs1 gs2 : list G)
    (bts : Vector.t (@ballot2 F G) k) (w : Fin.t (S n)) (pf pf' : @tally_proof F G (S n) (S n')),
    h = g ^ x -> exp_injective g -> (1 <= L)%nat ->
    length gs1 = (S n * S n)%nat -> length gs2 = (L * (S n * S n))%nat ->
    natF_injective (3 * Nat.pow 2 L + 2 + (2 * S n' * S n' + 3 * S n'))%nat ->
    (* at most N ballots, the range of the certificate *)
    k <= S n' ->
    (* every ballot comes with the rewinding transcripts of ballot2_sound *)
    (∀ k', ballot2_rewound n L g h h1 gs1 gs2 bts[@k']) ->
    (* and so does the certificate, on the aggregate of the ballots *)
    same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
    verify_tally g h (aggregate_bits (Vector.map (ballot2_bits n) bts)) w pf = true ->
    verify_tally g h (aggregate_bits (Vector.map (ballot2_bits n) bts)) w pf' = true ->
    binding_break h1 gs1 ∨ binding_break h1 gs2 ∨
    ∃ (ss : Vector.t (Vector.t nat (S n)) k),
      (∀ k i, ss[@k][@i] <= 2 * Nat.pow 2 L) ∧
      let D := fun i j => Z.of_nat (margin_count ss i j) in
      ∃ (d p : Fin.t (S n) -> Fin.t (S n) -> Z)
        (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n))),
        (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w ∧
        (∀ p', is_closure d p' -> schulze_winner p' w).
  Proof.
    intros * hh hinj hL hg1 hg2 hchar hk hbal hsa hdc hv hv'.
    (* the positions of every ballot, unless a key is broken *)
    destruct (fin_choice_or k (Vector.t nat (S n)) (binding_break h1 gs1 ∨ binding_break h1 gs2) (fun k' s =>
      (∀ i, s[@i] <= 2 * Nat.pow 2 L) ∧
      (∀ i j, cdec x (ballot2_bits n bts[@k'])[@i][@j] =
        g ^ (if Nat.ltb s[@i] s[@j] then one else zero)))) as [hbb | (sf & hsf)].
    { intro k'.
      destruct (ballot2_sound_bits (Hvec := Hvec) L g h h1 gs1 gs2 x bts[@k'] hh hL hg1 hg2
        (natF_injective_mono (3 * Nat.pow 2 L + 2 + (2 * S n' * S n' + 3 * S n'))%nat
          (3 * Nat.pow 2 L + 2)%nat ltac:(lia) hchar) (hbal k')) as [hb | [hb | (pos & hpos & hdec)]].
      + left; left; exact hb.
      + left; right; exact hb.
      + right; exists pos; split; [exact hpos | intros i j; apply hdec]. }
    { destruct hbb as [hb | hb]; [left; exact hb | right; left; exact hb]. }
    right; right.
    exists (Vector.map sf (fin_enum k)).
    split; [intros k' i; rewrite (Vector.nth_map _ _ k' k' eq_refl), fin_enum_nth; apply hsf |].
    cbv zeta.
    set (D := fun i j => Z.of_nat (margin_count (Vector.map sf (fin_enum k)) i j)).
    assert (he : encrypts x g (aggregate_bits (Vector.map (ballot2_bits n) bts)) D).
    { intros i j; unfold D, encrypts, mget; rewrite Nat2Z.id.
      apply cdec_aggregate_bits; intro k'.
      rewrite (Vector.nth_map _ _ k' k' eq_refl), (Vector.nth_map _ _ k' k' eq_refl), fin_enum_nth; apply hsf. }
    assert (hb : ∀ i j, (0 <= D i j <= Z.of_nat (S n'))%Z).
    { intros i j; unfold D; pose proof (margin_count_le (Vector.map sf (fin_enum k)) i j); lia. }
    destruct (verify_tally_sound n n' x g h _ D w pf pf' hh hinj
      (natF_injective_mono (3 * Nat.pow 2 L + 2 + (2 * S n' * S n' + 3 * S n'))%nat
        (2 * S n' * S n' + 3 * S n')%nat ltac:(lia) hchar) he hb hsa hdc hv hv')
      as (d & p & paths & hd & hc & hw).
    exists d, p, paths; split; [exact hd | split; [exact hc | split; [exact hw |]]].
    intros p' hp'.
    apply (cert_winner d p paths w); [| exact hc | exact hw | exact hp'].
    intros i j; rewrite hd; pose proof (defeat_le D i j (proj1 (hb i j))); lia.
  Qed.

End SchulzeBatchedTally.
