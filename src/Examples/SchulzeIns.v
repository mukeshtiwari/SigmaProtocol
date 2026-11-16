From Stdlib Require Import Utf8 ZArith Vector Psatz Fin Lia.
From Crypto Require Import Sigma EncProof.
From Frontend Require Import Approval Schulze.
From Backend Require Import SchulzeTally.
From Utility Require Import Zpstar Util SchnorrOrder.
From Algebra Require Import Hierarchy.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield Zpgroup
  VectorNotations.

(* A three-candidate example over the toy group of 
   ApprovalIns.v (q = 2963, p = 2q + 1): five ballots, their verification, 
   the aggregated margins, and two invalid ballots that are rejected. *)

Section SchulzeIns.

  (* Prime q*)
  Definition q : Z := 2963.

  (* Prime p *)
  Definition p : Z := 2 * q + 1.
  
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

  Lemma q_nz : q <> 0%Z.
  Proof. unfold q; lia. Qed.

  (* group generator and public key h = g^x, x = 1234 (TallyIns.v) *)
  Definition g : @Schnorr_group p q.
  Proof.
    refine 
    {| Schnorr.v := 4;
    Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
    Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

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

  Definition Fzero : F := @Zpfield.zero q prime_q.
  Definition Fone : F := @Zpfield.one q prime_q.
  Definition Fadd : F -> F -> F := @zp_add q.
  Definition Fmul : F -> F -> F := @zp_mul q.
  Definition Fsub : F -> F -> F := @zp_sub q.
  Definition Fopp : F -> F := @zp_opp q prime_q.
  Definition Fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  Definition Gone : G := @Schnorr.one p q prime_p prime_q.
  Definition Ginv : G -> G := @inv_schnorr_group 2 p q safe_prime prime_p prime_q.
  Definition Gmul : G -> G -> G := @mul_schnorr_group p q prime_p prime_q.
  Definition Gpow : G -> F -> G := @pow 2 p q safe_prime prime_p prime_q.
  Definition Gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.

  (* field elements from integers *)
  Definition zp_of (k : Z) : F := @Zpfield.mk_zp q (k mod q)%Z (Z.mod_mod k q q_nz).
  Definition x : F := zp_of 1234.

  (* ---------------------------------------------------------------- *)
  (* m = 3 candidates A, B, C (indices 0, 1, 2); n = 2                   *)

  Definition ballot3 : Type := @ballot F G 3.

  Definition verify_ballot_ins (b : ballot3) : bool :=
    @verify_ballot F Fzero Fone Fadd Fdec G Ginv Gmul Gpow Gdec 3 g h b.

  Definition encrypt_ballot_ins (s : Vector.t nat 3) (rd : @ballot_rand F 2) : ballot3 :=
    @encrypt_ballot F Fzero Fone Fadd Fmul Fsub Fopp Fdec G Ginv Gmul Gpow 2 g h s rd.

  (* deterministic "randomness" from a seed, for the example only *)
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

  (* the five ballots as position vectors (0 = top, 3 = unranked):
     A > B = C, B > C > A, B > C > A, C > A > B, A > C > B *)
  Definition positions : Vector.t (Vector.t nat 3) 5 :=
    [[0; 1; 1]; [2; 0; 1]; [2; 0; 1]; [1; 2; 0]; [0; 2; 1]].

  Definition ballots : Vector.t ballot3 5 :=
    Vector.map2 (fun s k => encrypt_ballot_ins s (ballot_rand_of k)) positions 
      [1%Z; 2%Z; 3%Z; 4%Z; 5%Z].

  (* every honest ballot verifies: checked by the extracted OCaml program 
     (src/Executable/Schulzecode), since the library's prover 
     (generalised_construct_encryption_proof_elgamal_real, through 
     Util.vector_fin_app_pred) casts vectors along equations proved by nia, 
     which vm_compute cannot reduce *)
  Definition ballots_ok : Vector.t bool 5 := Vector.map verify_ballot_ins ballots.

  (* a ballot with a position out of range (4 > m) is rejected *)
  Definition ballot_bad_pos : ballot3 := encrypt_ballot_ins [0; 4; 1] (ballot_rand_of 6).
  Definition ballot_bad_pos_ok : bool := verify_ballot_ins ballot_bad_pos.

  (* ballot 1 with the cell (B, A) replaced by the cell (A, B): b_BA = 1, 
     whose membership proof was made for δ_AB; the verifier combines it with 
     Enc(s_A) / Enc(s_B) and rejects it *)
  Definition ballot_bad_pair : ballot3 :=
    let b := Vector.hd ballots in
    let cAB := Vector.nth (Vector.nth (snd b) Fin.F1) (Fin.FS Fin.F1) in
    (fst b, Vector.replace (snd b) (Fin.FS Fin.F1) 
      (Vector.replace (Vector.nth (snd b) (Fin.FS Fin.F1)) Fin.F1 cAB)).
  Definition ballot_bad_pair_ok : bool := verify_ballot_ins ballot_bad_pair.

  (* non-interactive ballots: the challenge is the hash H of the ballot's 
     ciphertexts and announcements, supplied by the caller (SHAKE-256 in 
     the extracted program) *)
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

  (* ---------------------------------------------------------------- *)
  (* aggregated margins Enc(D), and their plaintexts under x              *)

  Definition encD : Vector.t (Vector.t (G * G) 3) 3 := 
    @aggregate_margins F G Gone Gmul 3 5 ballots.

  (* discrete log of y in base g for small exponents, by search *)
  Fixpoint dlog_small (y : G) (k : nat) : option nat :=
    match k with
    | 0 => if Gdec y (Gpow g Fzero) then Some 0 else None
    | S k' => 
      match dlog_small y k' with
      | Some r => Some r
      | None => if Gdec y (Gpow g (zp_of (Z.of_nat k))) then Some k else None
      end
    end.

  Definition D_plain : Vector.t (Vector.t (option nat) 3) 3 :=
    Vector.map (Vector.map (fun c => 
      dlog_small (@cdec F G Ginv Gmul Gpow x c) 5)) encD.

  (* expected: D_AB = 3, D_BA = 2, D_AC = 2, D_CA = 3, D_BC = 2, D_CB = 2 *)

  (* ---------------------------------------------------------------- *)
  (* the tally: N = 5 ballots, n' = 4                                    *)

  (* the trustees' randomness and challenges, deterministic for the example *)
  Definition tally_rnd (k : nat) : F := zp_of (Z.of_nat k * 7919 + 13).

  (* the plaintext computation of the trustees: defeats, closure, winner *)
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

  (* the announced winner C = index 2 *)
  Definition wC : Fin.t 3 := Fin.FS (Fin.FS Fin.F1).

  Definition tally_pf : @tally_proof F G 3 5 :=
    generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub) 
      (opp := Fopp) (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (n := 2) (n' := 4) x g h encD wC tally_rnd (zp_of 4242).

  Definition verify_tally_ins_on (encD : Vector.t (Vector.t (G * G) 3) 3) 
    (w : Fin.t 3) (pf : @tally_proof F G 3 5) : bool :=
    verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) 
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (m := 3) (N := 5) g h encD w pf.

  Definition verify_tally_ins (w : Fin.t 3) (pf : @tally_proof F G 3 5) : bool :=
    verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) (G := G) 
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (m := 3) (N := 5) g h encD w pf.

  (* the honest certificate for C verifies *)
  Definition tally_ok : bool := verify_tally_ins wC tally_pf.
  Definition tally_checks_ins : list bool :=
    tally_checks (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) (G := G) 
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (m := 3) (N := 5) g h encD wC tally_pf.

  (* the trustees cannot certify A: p_AC = 0 < p_CA = 3, so the winner 
     inequality for j = C fails *)
  Definition tally_pf_A : @tally_proof F G 3 5 :=
    generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub) 
      (opp := Fopp) (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (n := 2) (n' := 4) x g h encD Fin.F1 tally_rnd (zp_of 4242).
  Definition tally_bad_ok : bool := verify_tally_ins Fin.F1 tally_pf_A.

  (* the certificate for C does not verify against a different winner *)
  Definition tally_wrong_winner_ok : bool := verify_tally_ins Fin.F1 tally_pf.

  (* the non-interactive tally: one SHAKE-256 challenge over the statement 
     and all announcements, supplied by the extracted program *)
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

  Definition tally_challenge_ins (H : list (@tr_item G) -> F) (w : Fin.t 3) 
    (pf : @tally_proof F G 3 5) : F :=
    H (tally_transcript (n := 2) (n' := 4) encD w pf).

  (* the whole count as a state machine (SchulzeTally.count): the ballots are 
     read one by one, the valid ones aggregated, the certificate checked 
     against the aggregate; the verdict carries its own evidence *)
  Definition compute_final_count_ins (Hb : list (G * G) -> F) (Ht : list (@tr_item G) -> F)
    (bs : list ballot3) (w : Fin.t 3) (pf : @tally_proof F G 3 5) :
    existsT (bfinal : bool) (vbs inbs : list ballot3),
      count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) 
        (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
        (n := 2) (n' := 4) g h Hb Ht (finished bs vbs inbs w pf bfinal) :=
    compute_final_count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) 
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (n := 2) (n' := 4) g h Hb Ht bs w pf.

  (* the verdict and the two lists of ballots, for the extracted program *)
  Definition final_count_ins (Hb : list (G * G) -> F) (Ht : list (@tr_item G) -> F)
    (bs : list ballot3) (w : Fin.t 3) (pf : @tally_proof F G 3 5) : 
    bool * list ballot3 * list ballot3 :=
    let r := compute_final_count_ins Hb Ht bs w pf in
    (projT1 r, projT1 (projT2 r), projT1 (projT2 (projT2 r))).

  (* the trustees' plaintext certificate passes the boolean check (computed 
     from the decrypted margins, in the extracted program) *)
  Definition cert_ok_ins : bool := 
    cert_ok_b (fun_of (n := 2) d_Z) (fun_of (n := 2) p_Z) 
      (witness_path (fun_of (n := 2) d_Z) (fun_of (n := 2) p_Z)).

  (* the same on the margins written down directly, checked in Rocq *)
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

  (* ---------------------------------------------------------------- *)
  (* the two group hypotheses of the soundness theorems hold for this 
     instance (Utility/SchnorrOrder.v): g <> 1 has prime order q, so 
     exponentiation is injective, and Z_q has characteristic q > 79 = 
     4m + 2 + 2N² + 3N. Nothing is assumed any more beyond the transcripts. *)

  Definition Fdiv : F -> F -> F := @zp_div q.
  Definition Finv : F -> F := @zp_inv q.

  Lemma sch_vspace : @vector_space F (@eq F) Fzero Fone Fadd Fmul Fsub Fdiv Fopp Finv 
    G (@eq G) Gone Ginv Gmul Gpow.
  Proof. exact (@pow_vspace 2 p q safe_prime prime_p prime_q). Qed.

  Lemma g_not_one : g <> Gone.
  Proof. intro H; apply (f_equal Schnorr.v) in H; vm_compute in H; discriminate. Qed.

  Lemma exp_injective_g : Schulze.exp_injective (gpow := Gpow) g.
  Proof. 
    intros a b hab. 
    exact (pow_injective (Hk := safe_prime) (Hp := prime_p) (Hq := prime_q) g a b g_not_one hab).
  Qed.

  Lemma natF_injective_ins : ∀ B : nat, (Z.of_nat B < q)%Z -> 
    Schulze.natF_injective (zero := Fzero) (one := Fone) (add := Fadd) B.
  Proof. intros B hB; exact (natF_injective_below_q (Hq := prime_q) B hB). Qed.

  (* the public key of the example is g^x *)
  Lemma h_eq : h = Gpow g x.
  Proof. apply schnorr_eq_v; vm_compute; reflexivity. Qed.

  Lemma bound_79 : (Z.of_nat (4 * S 2 + 2 + (2 * S 4 * S 4 + 3 * S 4)) < q)%Z.
  Proof. unfold q; cbn; lia. Qed.

  (* soundness of a ballot, no hypotheses beyond the two transcripts *)
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

  (* end to end: k <= 5 accepting ballot pairs and an accepting certificate 
     pair on their aggregate certify the Schulze winner of the plaintext 
     margins *)
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

  (* the same for a successful run of the certified count *)
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

  (* completeness with the true margins: the honest trustees' certificate 
     verifies whenever the plaintext certificate they computed passes the 
     boolean check *)
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
