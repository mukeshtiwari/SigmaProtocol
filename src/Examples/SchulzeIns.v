From Stdlib Require Import Utf8 ZArith Vector Psatz Fin Lia.
From Crypto Require Import Sigma EncProof.
From Frontend Require Import Approval Schulze.
From Backend Require Import SchulzeTally.
From Utility Require Import Zpstar Util SchnorrOrder.
From Algebra Require Import Hierarchy.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup
  VectorNotations.

(** * Schulze election example: three candidates, five ballots

    This file is a small, fully worked instance of the receipt-free Schulze
    election ([Frontend/Schulze.v] for ballots, [Backend/SchulzeTally.v] for
    the tally). It is extracted to OCaml by
    [src/Extraction/Schulzelib/Extraction.v] ([Separate Extraction SchulzeIns])
    and driven by [src/Executable/Schulzecode/main.ml].

    The group is the toy Schnorr group of [Examples/ApprovalIns.v]: the
    order-[q] subgroup of [Z_p^*] with [q = 2963] and [p = 2q + 1 = 5927]
    (a safe prime). The generator is [g = 4], the secret key is [x = 1234],
    and the public key is [h = 3210 = g^x] ([h_eq]). These parameters are
    far too small for security. They exist so that every computation is
    quick and inspectable.

    The election has [m = 3] candidates A, B, C (indices 0, 1, 2) and
    [N = 5] ballots. The file builds the following.

    - Ballots: honest encryptions of five rankings ([ballots]), their
      verification ([ballots_ok]), and two invalid ballots that must be
      rejected ([ballot_bad_pos], [ballot_bad_pair]). The Fiat–Shamir
      wrappers take the hash as a parameter, which the extracted program
      instantiates with SHAKE-256.
    - Tally: the aggregate [encD], its decryption, the trustees' defeats,
      closure and winner, the honest tally proof for the winner C and its
      verification, and two negative tests (a proof for A, and C's proof
      against the wrong winner).
    - The counting state machine [compute_final_count] on this instance.
    - Theorems: the group hypotheses of the soundness theorems are
      discharged for this group ([exp_injective_g] and [natF_injective_ins],
      from [Utility/SchnorrOrder.v]). Ballot soundness, end-to-end
      soundness, count soundness and tally completeness then hold with no
      assumptions beyond the transcripts.

    The boolean results ([ballots_ok], [tally_ok], and so on) are evaluated
    by the extracted program, not inside Rocq. The library's provers cast
    vectors along equations proved by [nia], which [vm_compute] cannot
    reduce. Only the plaintext certificate examples ([example_cert_ok] and
    the following lemmas) are checked by [vm_compute] here. *)
Section SchulzeIns.

  (** *** The group *)

  (** The prime order [q] of the subgroup. *)
  Definition q : Z := 2963.

  (** The safe prime [p = 2q + 1]. *)
  Definition p : Z := 2 * q + 1.

  (** Primality of [q] and [p], by trial division up to the square root
      ([is_prime_sqrt_correct]), and the safe-prime equation. *)
  Theorem prime_q : Znumtheory.prime q : Prop : Type.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  Theorem prime_p : Znumtheory.prime p : Prop : Type.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.

  (** [q ≠ 0], needed to build [Z_q] elements with [Z.mod_mod]. *)
  Lemma q_nz : q <> 0%Z.
  Proof. unfold q; lia. Qed.

  (** The generator [g = 4], a quadratic residue mod [p] and hence of order
      [q]. The membership proof [4^q mod p = 1] is checked by [vm_compute]
      with [vm_cast_no_check]. *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  (** The trustees' public key [h = 3210 = g^1234] (see [h_eq]). *)
  Definition h : @Schnorr_group p q.
  Proof.
    refine
    {| Schnorr.v := 3210;
    Ha := conj eq_refl eq_refl : (0 < 3210 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 3210 q p)).
  Defined.

  Local Notation F := (@Zp q).
  Local Notation G := (@Schnorr_group p q).

  (** The field [Z_q] and the group operations, named for passing as
      explicit arguments to the generic definitions. *)
  Definition Fzero : F := @Zpfield.zero q prime_q.
  Definition Fone : F := @Zpfield.one q prime_q.
  Definition Fadd : F -> F -> F := @zp_add q.
  Definition Fmul : F -> F -> F := @zp_mul q.
  Definition Fsub : F -> F -> F := @zp_sub q.
  Definition Fopp : F -> F := @zp_opp q prime_q.
  Definition Fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  Definition Gone : G := @Schnorr.one p q prime_p prime_q.
  Definition Ginv : G -> G := @inv_schnorr_group p q prime_p prime_q.
  Definition Gmul : G -> G -> G := @mul_schnorr_group p q prime_p prime_q.
  Definition Gpow : G -> F -> G := @pow 2 p q safe_prime prime_p prime_q.
  Definition Gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.

  (** Field elements from integers (reduced mod [q]), and the secret key
      [x = 1234]. *)
  Definition zp_of (k : Z) : F := @Zpfield.mk_zp q (k mod q)%Z (Z.mod_mod k q q_nz).
  Definition x : F := zp_of 1234.

  (** *** Ballots

      A ballot for three candidates, in the format of [Frontend/Schulze.v].
      This is unrelated to the simplified ballot [SchulzeSimple.ballot3]. *)
  Definition ballot3 : Type := @ballot F G 3.

  (** The interactive ballot verifier and the honest voter at this
      instance. The challenges are inside the ballot. *)
  Definition verify_ballot_ins (b : ballot3) : bool :=
    @verify_ballot F Fzero Fone Fadd Fdec G Ginv Gmul Gpow Gdec 3 g h b.

  Definition encrypt_ballot_ins (s : Vector.t nat 3) (rd : @ballot_rand F 2) : ballot3 :=
    @encrypt_ballot F Fzero Fone Fadd Fmul Fsub Fopp Fdec G Ginv Gmul Gpow 2 g h s rd.

  (** Deterministic randomness derived from a seed. It is used for the
      example only, and real voters must sample uniformly. [pos_rand_of],
      [pair_rand_of] and [ballot_rand_of] fill the randomness records of
      [Frontend/Schulze.v] from disjoint seed offsets. *)
  Definition rand_vec (seed : Z) (k : nat) : Vector.t F k :=
    Vector.map (fun i => zp_of (seed + 7 * Z.of_nat (fin_idx i))) (fin_enum k).

  Definition pos_rand_of (seed : Z) : @pos_rand F 2 :=
    mk_pos_rand (zp_of seed) (rand_vec (seed + 1) _) (zp_of (seed + 100)).

  Definition pair_rand_of (seed : Z) : @pair_rand F 2 :=
    mk_pair_rand (zp_of seed) (rand_vec (seed + 1) 3) (zp_of (seed + 30))
      (rand_vec (seed + 40) _) (zp_of (seed + 200)).

  Definition ballot_rand_of (seed : Z) : @ballot_rand F 2 :=
    mk_ballot_rand
      (Vector.map (fun i => pos_rand_of (seed + 1000 * Z.of_nat (fin_idx i))) (fin_enum 3))
      (Vector.map (fun i => Vector.map (fun j =>
        pair_rand_of (seed + 10000 * Z.of_nat (fin_idx i) + 1000 * Z.of_nat (fin_idx j) + 500))
        (fin_enum 3)) (fin_enum 3)).

  (** The five rankings as position vectors (lower is better, and [m = 3]
      means unranked):
      A > B = C; B > C > A; B > C > A; C > A > B; A > C > B. *)
  Definition positions : Vector.t (Vector.t nat 3) 5 :=
    [[0; 1; 1]; [2; 0; 1]; [2; 0; 1]; [1; 2; 0]; [0; 2; 1]].

  (** The five honest ballots, with seeds 1 to 5. *)
  Definition ballots : Vector.t ballot3 5 :=
    Vector.map2 (fun s k => encrypt_ballot_ins s (ballot_rand_of k)) positions
      [1%Z; 2%Z; 3%Z; 4%Z; 5%Z].

  (** Each honest ballot verifies (expected [true] five times). *)
  Definition ballots_ok : Vector.t bool 5 := Vector.map verify_ballot_ins ballots.

  (** A ballot with position [4 > m] for B. Its range proof cannot be made
      honestly, so it is rejected (expected [false]). *)
  Definition ballot_bad_pos : ballot3 := encrypt_ballot_ins [0; 4; 1] (ballot_rand_of 6).
  Definition ballot_bad_pos_ok : bool := verify_ballot_ins ballot_bad_pos.

  (** The first ballot with the cell (B, A) replaced by the cell (A, B). The
      membership proof of that cell was made for the pair (A, B), so the
      verifier, which combines it with the position ciphertexts of B and A,
      rejects it (expected [false]). *)
  Definition ballot_bad_pair : ballot3 :=
    let b := Vector.hd ballots in
    let cAB := Vector.nth (Vector.nth (snd b) Fin.F1) (Fin.FS Fin.F1) in
    (fst b, Vector.replace (snd b) (Fin.FS Fin.F1)
      (Vector.replace (Vector.nth (snd b) (Fin.FS Fin.F1)) Fin.F1 cAB)).
  Definition ballot_bad_pair_ok : bool := verify_ballot_ins ballot_bad_pair.

  (** Non-interactive ballots. The challenge is the hash [H] of the ballot's
      ciphertexts and announcements. [H] is a parameter, supplied by the
      extracted program. *)
  Definition nizk_encrypt_ballot_ins (H : list (G * G) -> F) (s : Vector.t nat 3)
    (rd : @ballot_rand F 2) : ballot3 :=
    nizk_encrypt_ballot (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := Fsub) (opp := Fopp) (Fdec := Fdec) (G := G) (ginv := Ginv) (gop := Gmul)
      (gpow := Gpow) (n := 2) g h H s rd.

  Definition nizk_verify_ballot_ins (H : list (G * G) -> F) (b : ballot3) : bool :=
    nizk_verify_ballot (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := 2) g h H b.

  Definition ballot_challenge_ins (H : list (G * G) -> F) (b : ballot3) : F :=
    ballot_challenge (G := G) (n := 2) H b.

  (** *** The aggregate and its plaintexts *)

  (** The aggregate [Enc(D)] of the five ballots. *)
  Definition encD : Vector.t (Vector.t (G * G) 3) 3 :=
    @aggregate_margins F G Gone Gmul 3 5 ballots.

  (** Discrete logarithm in base [g] for small exponents, by linear search
      (a test helper analogous to [SchulzeTally.dlog_le]). *)
  Fixpoint dlog_small (y : G) (k : nat) : option nat :=
    match k with
    | 0 => if Gdec y (Gpow g Fzero) then Some 0 else None
    | S k' =>
      match dlog_small y k' with
      | Some r => Some r
      | None => if Gdec y (Gpow g (zp_of (Z.of_nat k))) then Some k else None
      end
    end.

  (** The decrypted counts. Expected: [D_AB = 3], [D_BA = 2], [D_AC = 2],
      [D_CA = 3], [D_BC = 2], [D_CB = 2]. *)
  Definition D_plain : Vector.t (Vector.t (option nat) 3) 3 :=
    Vector.map (Vector.map (fun c =>
      dlog_small (@cdec F G Ginv Gmul Gpow x c) 5)) encD.

  (** *** The tally ([N = 5], so [n' = 4]) *)

  (** The trustees' randomness, deterministic for the example. *)
  Definition tally_rnd (k : nat) : F := zp_of (Z.of_nat k * 7919 + 13).

  (** The trustees' plaintext computation: decrypted counts [D_Z], defeats
      [d_Z], strongest paths [p_Z], and the announced winner [w_opt] (as an
      index in [w_idx]). With the counts above, the defeats are A→B (3),
      C→A (3) and no defeat between B and C. Hence [p_CA = 3] and
      [p_AC = 0], and C is the unique winner. *)
  Definition D_Z : Vector.t (Vector.t Z 3) 3 :=
    decrypt_margins (zero := Fzero) (one := Fone) (add := Fadd) (G := G) (ginv := Ginv)
      (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := 2) (n' := 4) x g encD.
  Definition d_Z : Vector.t (Vector.t Z 3) 3 :=
    mat_of (n := 2) (defeat (fun_of (n := 2) D_Z)).
  Definition p_Z : Vector.t (Vector.t Z 3) 3 :=
    mat_of (n := 2) (minmax_closure (defeat (fun_of (n := 2) D_Z))).
  Definition w_opt : option (Fin.t 3) :=
    tally_winner (zero := Fzero) (one := Fone) (add := Fadd) (G := G) (ginv := Ginv)
      (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := 2) (n' := 4) x g encD.
  Definition w_idx : option nat := option_map fin_idx w_opt.

  (** The announced winner, C (index 2). *)
  Definition wC : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

  (** The honest tally proof for C, with challenge [4242]. *)
  Definition tally_pf : @tally_proof F G 3 5 :=
    generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := 2) (n' := 4) x g h encD wC tally_rnd (zp_of 4242).

  (** The tally verifier at this instance, on an arbitrary aggregate
      ([verify_tally_ins_on]) or on [encD] ([verify_tally_ins]). *)
  Definition verify_tally_ins_on (encD : Vector.t (Vector.t (G * G) 3) 3)
    (w : Fin.t 3) (pf : @tally_proof F G 3 5) : bool :=
    verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (m := 3) (N := 5) g h encD w pf.

  Definition verify_tally_ins (w : Fin.t 3) (pf : @tally_proof F G 3 5) : bool :=
    verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) (G := G)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (m := 3) (N := 5) g h encD w pf.

  (** The honest proof for C verifies (expected [true]). [tally_checks_ins]
      lists the seven individual checks. *)
  Definition tally_ok : bool := verify_tally_ins wC tally_pf.
  Definition tally_checks_ins : list bool :=
    tally_checks (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) (G := G)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (m := 3) (N := 5) g h encD wC tally_pf.

  (** The trustees cannot certify A. The winner check for [j = C] needs
      [p_AC ≥ p_CA], but [p_AC = 0 < 3 = p_CA] (expected [false]). *)
  Definition tally_pf_A : @tally_proof F G 3 5 :=
    generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := 2) (n' := 4) x g h encD Fin.F1 tally_rnd (zp_of 4242).
  Definition tally_bad_ok : bool := verify_tally_ins Fin.F1 tally_pf_A.

  (** C's proof does not verify for a different winner (expected [false]). *)
  Definition tally_wrong_winner_ok : bool := verify_tally_ins Fin.F1 tally_pf.

  (** The Fiat–Shamir tally. One challenge, the hash [H] of the statement and
      all announcements, is supplied by the extracted program. *)
  Definition nizk_generate_tally_ins (H : list (@tr_item G) -> F) (w : Fin.t 3) :
    @tally_proof F G 3 5 :=
    nizk_generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := Fsub) (opp := Fopp) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := 2) (n' := 4) x g h H encD w tally_rnd.

  Definition nizk_verify_tally_ins (H : list (@tr_item G) -> F) (w : Fin.t 3)
    (pf : @tally_proof F G 3 5) : bool :=
    nizk_verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := 2) (n' := 4) g h H encD w pf.

  (** The challenge that [nizk_verify_tally] expects for a given proof. *)
  Definition tally_challenge_ins (H : list (@tr_item G) -> F) (w : Fin.t 3)
    (pf : @tally_proof F G 3 5) : F :=
    H (tally_transcript (n := 2) (n' := 4) encD w pf).

  (** The whole count as a state machine ([SchulzeTally.count]). Ballots are
      read one by one, the valid ones are aggregated, and the tally proof is
      checked against the aggregate. The result carries its own derivation. *)
  Definition compute_final_count_ins (Hb : list (G * G) -> F) (Ht : list (@tr_item G) -> F)
    (bs : list ballot3) (w : Fin.t 3) (pf : @tally_proof F G 3 5) :
    existsT (bfinal : bool) (vbs inbs : list ballot3),
      count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
        (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
        (n := 2) (n' := 4) g h Hb Ht (finished bs vbs inbs w pf bfinal) :=
    compute_final_count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := 2) (n' := 4) g h Hb Ht bs w pf.

  (** The verdict and the lists of valid and invalid ballots, for the
      extracted program. *)
  Definition final_count_ins (Hb : list (G * G) -> F) (Ht : list (@tr_item G) -> F)
    (bs : list ballot3) (w : Fin.t 3) (pf : @tally_proof F G 3 5) :
    bool * list ballot3 * list ballot3 :=
    let r := compute_final_count_ins Hb Ht bs w pf in
    (projT1 r, projT1 (projT2 r), projT1 (projT2 (projT2 r))).

  (** The trustees' computed certificate passes [cert_ok_b] (evaluated by
      the extracted program). *)
  Definition cert_ok_ins : bool :=
    cert_ok_b (fun_of (n := 2) d_Z) (fun_of (n := 2) p_Z)
      (witness_path (fun_of (n := 2) d_Z) (fun_of (n := 2) p_Z)).

  (** The same counts written down directly, so that the plaintext
      certificate can be checked inside Rocq by [vm_compute]. The closure and
      witness paths pass [cert_ok_b], C wins, and A does not. *)
  Definition D3 : Fin.t 3 -> Fin.t 3 -> Z :=
    fun_of (n := 2) [[0; 3; 2]; [2; 0; 2]; [3; 2; 0]]%Z.
  Definition d3 := defeat D3.
  Definition p3 := minmax_closure d3.
  Lemma example_cert_ok : cert_ok_b d3 p3 (witness_path d3 p3) = true.
  Proof. vm_compute; reflexivity. Qed.
  Lemma example_winner : schulze_winner_b p3 wC = true.
  Proof. vm_compute; reflexivity. Qed.
  Lemma example_not_winner_A : schulze_winner_b p3 Fin.F1 = false.
  Proof. vm_compute; reflexivity. Qed.

  (** *** Discharging the group hypotheses

      The soundness theorems assume [exp_injective g] and that [natF] is
      injective below a bound. Both hold here. [g ≠ 1] has prime order [q],
      and [Z_q] has characteristic [q > 79 = 4m + 2 + 2N² + 3N]. *)

  (** Division and inverse in [Z_q], needed for the vector-space
      structure. *)
  Definition Fdiv : F -> F -> F := @zp_div q.
  Definition Finv : F -> F := @zp_inv q.

  (** The Schnorr group is a vector space over [Z_q] ([pow_vspace]). *)
  Lemma sch_vspace : @vector_space F (@eq F) Fzero Fone Fadd Fmul Fsub Fdiv Fopp Finv
    G (@eq G) Gone Ginv Gmul Gpow.
  Proof. exact (@pow_vspace 2 p q safe_prime prime_p prime_q). Qed.

  (** [g ≠ 1]. *)
  Lemma g_not_one : g <> Gone.
  Proof. intro H; apply (f_equal Schnorr.v) in H; vm_compute in H; discriminate. Qed.

  (** [x ↦ g^x] is injective on [Z_q] ([pow_injective]). *)
  Lemma exp_injective_g : Schulze.exp_injective (gpow := Gpow) g.
  Proof.
    intros a b hab.
    exact (pow_injective (Hk := safe_prime) (Hp := prime_p) (Hq := prime_q) g a b g_not_one hab).
  Qed.

  (** The embedding [nat → Z_q] is injective below [q]. *)
  Lemma natF_injective_ins : ∀ B : nat, (Z.of_nat B < q)%Z ->
    Schulze.natF_injective (zero := Fzero) (one := Fone) (add := Fadd) B.
  Proof. intros B hB; exact (natF_injective_below_q (Hq := prime_q) B hB). Qed.

  (** The public key is [g^x], checked by [vm_compute]. *)
  Lemma h_eq : h = Gpow g x.
  Proof. apply schnorr_eq_v; vm_compute; reflexivity. Qed.

  (** The characteristic bound for [m = 3] and [N = 5]:
      [4·3 + 2 + 2·25 + 3·5 = 79 < q]. *)
  Lemma bound_79 : (Z.of_nat (4 * S 2 + 2 + (2 * S 4 * S 4 + 3 * S 4)) < q)%Z.
  Proof. unfold q; cbn; lia. Qed.

  (** *** Instantiated theorems *)

  (** Ballot special soundness: two accepting transcripts with the same
      announcements and different challenges determine a ranking
      [s ∈ {0..3}³] whose comparison bits the ballot encrypts. *)
  Theorem ballot_sound_ins : ∀ (b b' : ballot3),
    Schulze.same_announcements b b' -> Schulze.different_challenges b b' ->
    verify_ballot_ins b = true -> verify_ballot_ins b' = true ->
    ∃ s : Vector.t nat 3, (∀ i, Vector.nth s i <= 3) ∧
      (∀ i j, Schulze.plaintext_bit (ginv := Ginv) (gop := Gmul) (gpow := Gpow) x b i j =
        Gpow g (if Nat.ltb (Vector.nth s i) (Vector.nth s j) then Fone else Fzero)).
  Proof.
    intros b b' hsa hdc hv hv'.
    exact (Schulze.ballot_sound (Hvec := sch_vspace) 2 x g h b b' h_eq exp_injective_g
      (natF_injective_ins (4 * S 2 + 2) ltac:(unfold q; cbn; lia)) hsa hdc hv hv').
  Qed.

  (** End-to-end soundness for [k ≤ 5] ballots. Accepting ballot pairs and
      an accepting tally-proof pair on their aggregate make [w] a Schulze
      winner of every closure of the defeats of the extracted rankings. *)
  Theorem schulze_end_to_end_ins : ∀ (k : nat) (bs bs' : Vector.t ballot3 k) (w : Fin.t 3)
    (pf pf' : @tally_proof F G 3 5),
    k <= 5 ->
    (∀ k, Schulze.same_announcements bs[@k] bs'[@k] ∧ Schulze.different_challenges bs[@k] bs'[@k] ∧
      verify_ballot_ins bs[@k] = true ∧ verify_ballot_ins bs'[@k] = true) ->
    same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
    verify_tally_ins_on (@aggregate_margins F G Gone Gmul 3 k bs) w pf = true ->
    verify_tally_ins_on (@aggregate_margins F G Gone Gmul 3 k bs) w pf' = true ->
    ∃ (ss : Vector.t (Vector.t nat 3) k),
      (∀ k i, ss[@k][@i] <= 3) ∧
      let D := fun i j => Z.of_nat (Schulze.margin_count ss i j) in
      ∃ (d p : Fin.t 3 -> Fin.t 3 -> Z) (paths : Fin.t 3 -> Fin.t 3 -> list (Fin.t 3)),
        (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w ∧
        (∀ p', is_closure d p' -> schulze_winner p' w).
  Proof.
    intros k bs bs' w pf pf' hk hbal hsa hdc hv hv'.
    exact (schulze_end_to_end (Hvec := sch_vspace) 2 4 k x g h bs bs' w pf pf' h_eq
      exp_injective_g (natF_injective_ins _ bound_79) hk hbal hsa hdc hv hv').
  Qed.

  (** The same for a successful run of the counting state machine. *)
  Theorem count_sound_ins : ∀ (Hb : list (G * G) -> F) (Ht : list (@tr_item G) -> F)
    (us vbs inbs : list ballot3) (w : Fin.t 3) (pf pf' : @tally_proof F G 3 5),
    count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := 2) (n' := 4) g h Hb Ht (finished us vbs inbs w pf true) ->
    (∃ bs' : Vector.t ballot3 (List.length vbs), ∀ k,
      Schulze.same_announcements (Vector.of_list vbs)[@k] bs'[@k] ∧
      Schulze.different_challenges (Vector.of_list vbs)[@k] bs'[@k] ∧
      verify_ballot_ins bs'[@k] = true) ->
    same_tally_announcements pf pf' -> different_tally_challenges pf pf' ->
    verify_tally_ins_on (aggregate_list (gid := Gone) (gop := Gmul) (n := 2) vbs) w pf' = true ->
    ∃ (ss : Vector.t (Vector.t nat 3) (List.length vbs)),
      (∀ k i, ss[@k][@i] <= 3) ∧
      let D := fun i j => Z.of_nat (Schulze.margin_count ss i j) in
      ∃ (d p : Fin.t 3 -> Fin.t 3 -> Z) (paths : Fin.t 3 -> Fin.t 3 -> list (Fin.t 3)),
        (∀ i j, d i j = defeat D i j) ∧ cert_ok d p paths ∧ schulze_winner p w ∧
        (∀ p', is_closure d p' -> schulze_winner p' w).
  Proof.
    intros Hb Ht us vbs inbs w pf pf' hc hbs hsa hdc hv'.
    exact (count_sound (Hvec := sch_vspace) 2 4 x g h Hb Ht us vbs inbs w pf pf' h_eq
      exp_injective_g (natF_injective_ins _ bound_79) hc hbs hsa hdc hv').
  Qed.

  (** Completeness with the true counts. The honest trustees' proof
      verifies whenever the certificate they computed passes the boolean
      check. *)
  Theorem tally_complete_ins : ∀ (encD : Vector.t (Vector.t (G * G) 3) 3)
    (D : Fin.t 3 -> Fin.t 3 -> Z) (w : Fin.t 3) (rnd : nat -> F) (chal : F),
    encrypts (zero := Fzero) (one := Fone) (add := Fadd) (ginv := Ginv) (gop := Gmul) (gpow := Gpow)
      x g encD D ->
    (∀ i j, (0 <= D i j <= 5)%Z) ->
    let d := defeat D in
    let p := minmax_closure d in
    cert_ok_b d p (witness_path d p) = true -> schulze_winner_b p w = true ->
    verify_tally_ins_on encD w
      (generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
        (opp := Fopp) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
        (n := 2) (n' := 4) x g h encD w rnd chal) = true.
  Proof.
    intros encD D w rnd chal he hb d p hc hw.
    exact (verify_tally_complete_inj (Hvec := sch_vspace) 2 4 x g h encD D w rnd chal h_eq
      exp_injective_g (natF_injective_ins 5 ltac:(unfold q; cbn; lia)) he hb hc hw).
  Qed.

End SchulzeIns.
