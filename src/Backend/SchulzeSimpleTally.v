From Stdlib Require Import Setoid setoid_ring.Field Psatz Vector Utf8 Fin Lia ZArith List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import Elgamal BayerGrothSound.
From Frontend Require Import Schulze SchulzeBatched SchulzeSimple.
From Backend Require Import SchulzeTally SchulzeBatchedTally.
Import VectorNotations.

(* The end-to-end theorem of Backend/SchulzeTally.v for the simplified
   batched ballot of Frontend/SchulzeSimple.v: accepted simplified ballots
   (in the rewinding form of ballot3_sound) and an accepted certificate on
   the aggregate of their ciphertext matrices name a Schulze winner of the
   positions the ballots commit to, unless the commitment key is broken.
   Same proof as schulze_end_to_end2, with one key and one extractor. *)

Section SchulzeSimpleTally.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Local Infix "^" := gpow.
  Local Notation cdec := (Schulze.cdec (ginv := ginv) (gop := gop) (gpow := gpow)).
  Local Notation exp_injective := (Schulze.exp_injective (gpow := gpow)).
  Local Notation natF_injective := (Schulze.natF_injective (zero := zero) (one := one) (add := add)).
  Local Notation ballot3_rewound n := (@SchulzeSimple.ballot3_rewound F zero one add mul sub opp G gid gop gpow Gdec n).
  Local Notation ballot3_bits n := (@SchulzeSimple.ballot3_bits F G gid n).
  Local Notation verify_tally := (SchulzeTally.verify_tally (zero := zero) (one := one) (add := add) (Fdec := Fdec)
    (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation encrypts := (SchulzeTally.encrypts (zero := zero) (one := one) (add := add)
    (ginv := ginv) (gop := gop) (gpow := gpow)).
  Local Notation binding_break := (BayerGrothSound.binding_break (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation aggregate_bits := (SchulzeBatchedTally.aggregate_bits (gid := gid) (gop := gop)).

  Theorem schulze_end_to_end3 : ∀ (n n' k L : nat) (x : F) (g h h1 : G) (gs1 : list G)
    (bts : Vector.t (@ballot3 F G) k) (w : Fin.t (S n)) (pf pf' : @tally_proof F G (S n) (S n')),
    h = g ^ x -> exp_injective g -> (1 <= L)%nat ->
    length gs1 = (S n * S n)%nat ->
    natF_injective (3 * Nat.pow 2 L + 2 + (2 * S n' * S n' + 3 * S n'))%nat ->
    (* at most N ballots, the range of the certificate *)
    k <= S n' ->
    (* every ballot comes with the rewinding transcripts of ballot3_sound *)
    (∀ k', ballot3_rewound n L g h h1 gs1 bts[@k']) ->
    (* and so does the certificate, on the aggregate of the ballots *)
    same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
    verify_tally g h (aggregate_bits (Vector.map (ballot3_bits n) bts)) w pf = true ->
    verify_tally g h (aggregate_bits (Vector.map (ballot3_bits n) bts)) w pf' = true ->
    binding_break h1 gs1 ∨
    ∃ (ss : Vector.t (Vector.t nat (S n)) k),
      (∀ k i, ss[@k][@i] <= 2 * Nat.pow 2 L) ∧
      let D := fun i j => Z.of_nat (margin_count ss i j) in
      ∃ (d p : Fin.t (S n) -> Fin.t (S n) -> Z)
        (paths : Fin.t (S n) -> Fin.t (S n) -> list (Fin.t (S n))),
        (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w ∧
        (∀ p', is_closure d p' -> schulze_winner p' w).
  Proof.
    intros * hh hinj hL hg1 hchar hk hbal hsa hdc hv hv'.
    (* the positions of every ballot, unless the key is broken *)
    destruct (fin_choice_or k (Vector.t nat (S n)) (binding_break h1 gs1) (fun k' s =>
      (∀ i, s[@i] <= 2 * Nat.pow 2 L) ∧
      (∀ i j, cdec x (ballot3_bits n bts[@k'])[@i][@j] =
        g ^ (if Nat.ltb s[@i] s[@j] then one else zero)))) as [hbb | (sf & hsf)].
    { intro k'.
      destruct (ballot3_sound_bits (Hvec := Hvec) (Fdec := Fdec) L g h h1 gs1 x bts[@k'] hh hL hg1
        (natF_injective_mono (3 * Nat.pow 2 L + 2 + (2 * S n' * S n' + 3 * S n'))%nat
          (3 * Nat.pow 2 L + 2)%nat ltac:(lia) hchar) (hbal k')) as [hb | (pos & hpos & hdec)].
      + left; exact hb.
      + right; exists pos; split; [exact hpos | intros i j; apply hdec]. }
    { left; exact hbb. }
    right.
    exists (Vector.map sf (fin_enum k)).
    split; [intros k' i; rewrite (Vector.nth_map _ _ k' k' eq_refl), fin_enum_nth; apply hsf |].
    cbv zeta.
    set (D := fun i j => Z.of_nat (margin_count (Vector.map sf (fin_enum k)) i j)).
    assert (he : encrypts x g (aggregate_bits (Vector.map (ballot3_bits n) bts)) D).
    { intros i j; unfold D, encrypts, mget; rewrite Nat2Z.id.
      apply (cdec_aggregate_bits (Hvec := Hvec)); intro k'.
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

End SchulzeSimpleTally.
