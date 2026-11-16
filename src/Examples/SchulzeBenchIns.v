(* The receipt-free Schulze protocol at the real Helios parameters 
   (2048-bit p, 256-bit q, HeliosTallyIns.v), generic in the number of 
   candidates m = S n and the ballot bound N = S n', for benchmarking: the 
   extracted functions take n and n' at run time. *)
From Stdlib Require Import Utf8 ZArith Vector Psatz Fin Lia List.
From Crypto Require Import Sigma EncProof Elgamal.
From Frontend Require Import Approval Schulze SchulzeBatched SchulzeSimple.
From Backend Require Import SchulzeTally.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns.
Import Vspace Schnorr Zpfield Zpgroup VectorNotations.

Section SchulzeBench.

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
  Definition Ginv : G -> G := @inv_schnorr_group k p q safe_prime prime_p prime_q.
  Definition Gmul : G -> G -> G := @mul_schnorr_group p q prime_p prime_q.
  Definition Gpow : G -> F -> G := @pow k p q safe_prime prime_p prime_q.
  Definition Gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.

  Lemma q_nz : q <> 0%Z.
  Proof. unfold q; discriminate. Qed.

  Definition zp_of (z : Z) : F := @Zpfield.mk_zp q (z mod q)%Z (Z.mod_mod z q q_nz).

  (* a trustee key for the benchmark (the Helios key h2024 has no known 
     secret), h = g^x *)
  Definition x : F := zp_of 123456789.
  Definition h : G := Gpow g x.

  (* ---------------------------------------------------------------- *)
  (* ballots: m = S n candidates                                        *)

  (* the voter's randomness from an oracle (fresh randomness per call in 
     the extracted program) *)
  Definition pos_rand_of (n : nat) (rnd : nat -> F) : @pos_rand F n :=
    mk_pos_rand (rnd 0) (Vector.map (fun _ => rnd 1) (fin_enum _)) (rnd 2).

  Definition pair_rand_of (n : nat) (rnd : nat -> F) : @pair_rand F n :=
    mk_pair_rand (rnd 0) (Vector.map (fun _ => rnd 1) (fin_enum 3)) (rnd 2) 
      (Vector.map (fun _ => rnd 3) (fin_enum _)) (rnd 4).

  Definition ballot_rand_of (n : nat) (rnd : nat -> F) : @ballot_rand F n :=
    mk_ballot_rand 
      (Vector.map (fun _ => pos_rand_of n rnd) (fin_enum (S n)))
      (Vector.map (fun _ => Vector.map (fun _ => pair_rand_of n rnd) (fin_enum (S n))) 
        (fin_enum (S n))).

  Definition nizk_encrypt_ballot_bench (n : nat) (H : list (G * G) -> F) 
    (s : Vector.t nat (S n)) (rnd : nat -> F) : @ballot F G (S n) :=
    nizk_encrypt_ballot (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) 
      (sub := Fsub) (opp := Fopp) (Fdec := Fdec) (G := G) (ginv := Ginv) (gop := Gmul) 
      (gpow := Gpow) (n := n) g h H s (ballot_rand_of n rnd).

  Definition nizk_verify_ballot_bench (n : nat) (H : list (G * G) -> F) 
    (b : @ballot F G (S n)) : bool :=
    nizk_verify_ballot (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) 
      (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := n) g h H b.

  (* number of group elements on the bulletin board per ballot: the 
     transcript (ciphertexts and announcements) has one pair per entry, 
     the proofs carry challenges and responses in F *)
  Definition ballot_board_size (n : nat) (b : @ballot F G (S n)) : nat :=
    List.length (ballot_transcript (G := G) (n := n) b).

  (* ---------------------------------------------------------------- *)
  (* the tally: margins of a list of position vectors, encrypted directly 
     (the ballots' proofs are benchmarked separately)                    *)

  Definition margins_bench (n : nat) (ss : list (Vector.t nat (S n))) : 
    Vector.t (Vector.t Z (S n)) (S n) :=
    mat_of (n := n) (fun i j => Z.of_nat (Schulze.margin_count (Vector.of_list ss) i j)).

  Definition encrypt_margins_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) 
    (rnd : nat -> F) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    Vector.map (Vector.map (fun z => 
      @enc F G Gmul Gpow g h (nat_to_F Fzero Fone Fadd (Z.to_nat z)) (rnd 0))) D.

  Definition defeats_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) : 
    Vector.t (Vector.t Z (S n)) (S n) :=
    mat_of (n := n) (defeat (fun_of (n := n) D)).

  Definition closure_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) : 
    Vector.t (Vector.t Z (S n)) (S n) :=
    mat_of (n := n) (minmax_closure (defeat (fun_of (n := n) D))).

  Definition winner_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) : option (Fin.t (S n)) :=
    winner_of (minmax_closure (defeat (fun_of (n := n) D))).

  Definition nizk_generate_tally_bench (n n' : nat) (H : list (@tr_item G) -> F) 
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n)) (rnd : nat -> F) : 
    @tally_proof F G (S n) (S n') :=
    nizk_generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) 
      (sub := Fsub) (opp := Fopp) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (n := n) (n' := n') x g h H encD w rnd.

  Definition nizk_verify_tally_bench (n n' : nat) (H : list (@tr_item G) -> F) 
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n)) 
    (pf : @tally_proof F G (S n) (S n')) : bool :=
    nizk_verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) 
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (n := n) (n' := n') g h H encD w pf.

  Definition tally_checks_bench (n n' : nat) 
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n)) 
    (pf : @tally_proof F G (S n) (S n')) : list bool :=
    tally_checks (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec) 
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) 
      (m := S n) (N := S n') g h encD w pf.

  (* number of entries of the certificate transcript *)
  Definition tally_board_size (n n' : nat) (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) 
    (w : Fin.t (S n)) (pf : @tally_proof F G (S n) (S n')) : nat :=
    List.length (tally_transcript (n := n) (n' := n') encD w pf).

  (* ---------------------------------------------------------------- *)
  (* a real election: aggregate the accepted ballots, decrypt the margins *)

  Definition aggregate_bench (n : nat) (bs : list (@ballot F G (S n))) : 
    Vector.t (Vector.t (G * G) (S n)) (S n) :=
    aggregate_list (gid := Gone) (gop := Gmul) (n := n) bs.

  Definition decrypt_margins_bench (n n' : nat) 
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) : Vector.t (Vector.t Z (S n)) (S n) :=
    decrypt_margins (zero := Fzero) (one := Fone) (add := Fadd) (G := G) (ginv := Ginv) 
      (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := n) (n' := n') x g encD.

  (* ---------------------------------------------------------------- *)
  (* the batched ballot (Frontend/SchulzeBatched.v)                     *)

  Definition K2 (n : nat) : nat := @K n.
  Definition NX2 (n L : nat) : nat := @NX n L.
  Definition W2 (n L : nat) : nat := @W n L.

  Definition encrypt_ballot2_bench (n L : nat) (h1 : G) (gs1 gs2 : list G) (ch : @chal2 F)
    (sn : list nat) (rd : @rand2 F) : @ballot2 F G :=
    encrypt_ballot2 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) L g h h1 gs1 gs2 ch sn rd.

  Definition verify_ballot2_bench (n L : nat) (h1 : G) (gs1 gs2 : list G) (ch : @chal2 F)
    (bt : @ballot2 F G) : bool :=
    verify_ballot2 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (Fdec := Fdec) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 gs2 ch bt.

  Definition challenges2_bench (n : nat) (H : list (@b2_item F G) -> F) (bt : @ballot2 F G) : @chal2 F :=
    challenges_of (n := n) H bt.

  Definition nizk_verify_ballot2_bench (n L : nat) (h1 : G) (gs1 gs2 : list G)
    (H : list (@b2_item F G) -> F) (bt : @ballot2 F G) : bool :=
    nizk_verify_ballot2 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (Fdec := Fdec) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 gs2 H bt.

  Definition ballot2_bits_bench (n : nat) (bt : @ballot2 F G) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    ballot2_bits (gid := Gone) (n := n) bt.

  (* ---------------------------------------------------------------- *)
  (* the simplified batched ballot (Frontend/SchulzeSimple.v)           *)

  Definition W3_bench (n : nat) : nat := @W3 n.
  Definition R3_bench (L : nat) : nat := @R L.

  Definition gd_bench (n : nat) (gs1 : list G) : list G :=
    gd (zero := Fzero) (one := Fone) (sub := Fsub) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) gs1.

  Definition encrypt_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G) (ch : @chal3 F)
    (sn : list nat) (rd : @rand3 F) : @ballot3 F G :=
    encrypt_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) L g h h1 gs1 ch sn rd.

  Definition verify_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G) (ch : @chal3 F)
    (bt : @ballot3 F G) : bool :=
    verify_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 ch bt.

  Definition challenges3_bench (n : nat) (H : list (@b3_item F G) -> F) (bt : @ballot3 F G) : @chal3 F :=
    challenges_of3 (n := n) H bt.

  Definition nizk_verify_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G)
    (H : list (@b3_item F G) -> F) (bt : @ballot3 F G) : bool :=
    nizk_verify_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 H bt.

  Definition ballot3_bits_bench (n : nat) (bt : @ballot3 F G) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    ballot3_bits (gid := Gone) (n := n) bt.

  Definition nizk_encrypt_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G)
    (H : list (@b3_item F G) -> F) (sn : list nat) (rd : @rand3 F) : @ballot3 F G :=
    nizk_encrypt_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) L g h h1 gs1 H sn rd.

  (* the encrypted margins of a list of simplified ballots, as aggregate_list
     reads the first ballot *)
  Definition aggregate3_bench (n : nat) (bs : list (@ballot3 F G)) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    List.fold_right (fun b acc => Vector.map2 (Vector.map2 (Schulze.cmul (gop := Gmul))) (ballot3_bits_bench n b) acc)
      (Vector.const (Vector.const (Schulze.cid (gid := Gone)) (S n)) (S n)) bs.

End SchulzeBench.
