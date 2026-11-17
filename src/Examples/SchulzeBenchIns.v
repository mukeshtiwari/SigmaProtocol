From Stdlib Require Import Utf8 ZArith Vector Psatz Fin Lia List.
From Crypto Require Import Sigma EncProof Elgamal.
From Frontend Require Import Approval Schulze SchulzeBatched SchulzeSimple.
From Backend Require Import SchulzeTally.
From Utility Require Import Zpstar Util.
From Examples Require Import HeliosTallyIns.
Import Vspace Schnorr Zpfield Zpgroup VectorNotations.

(** * Schulze benchmarks at the Helios group parameters

    This file instantiates the receipt-free Schulze election at the real
    Helios parameters of [Examples/HeliosTallyIns.v]: a 2048-bit safe prime
    [p] with a 256-bit prime-order subgroup [q], and its generator [g]. It
    stays generic in the number of candidates [m = S n], the ballot bound
    [N = S n'] and the bit length [L]. The extracted functions take [n],
    [n'] and [L] at run time, so a single extracted library benchmarks
    every election size. Extraction is in
    [src/Extraction/SchulzeBenchlib/Extraction.v]
    ([Separate Extraction SchulzeBenchIns]), and the drivers are in
    [src/Executable/SchulzeBenchcode] ([main.ml], [batched.ml], [simple.ml])
    and [src/Executable/SchulzeGentoocode].

    It provides wrappers for three ballot front ends and for the tally:

    - the per-cell ballot of [Frontend/Schulze.v] (non-interactive
      encryption and verification, and bulletin-board size);
    - the tally of [Backend/SchulzeTally.v] (counts, encryption of the
      counts, defeats, closure, winner, non-interactive tally proof and
      verification, the individual checks, and board size);
    - the batched ballot of [Frontend/SchulzeBatched.v] ([ballot2]);
    - the simplified batched ballot of [Frontend/SchulzeSimple.v]
      ([ballot3]).

    Nothing is proved here. The wrappers only fix the group operations. The
    randomness is an oracle [rnd : nat -> F] supplied by the extracted
    program. Some wrappers reuse a single oracle value across several
    components (see [pos_rand_of] and [encrypt_margins_bench]). This is fine
    for timing but not for a real election. *)
Section SchulzeBench.

  Local Notation F := (@Zp q).
  Local Notation G := (@Schnorr_group p q).

  (** The field [Z_q] and the Schnorr group of [HeliosTallyIns] ([k = p / q]
      is the cofactor), named for passing to the generic definitions. *)
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

  (** [q ≠ 0], and field elements from integers. *)
  Lemma q_nz : q <> 0%Z.
  Proof. unfold q; discriminate. Qed.

  Definition zp_of (z : Z) : F := @Zpfield.mk_zp q (z mod q)%Z (Z.mod_mod z q q_nz).

  (** A trustee key for the benchmark, [h = g^x] with [x = 123456789]. The
      Helios election key has no known secret, so a fresh key is used. *)
  Definition x : F := zp_of 123456789.
  Definition h : G := Gpow g x.

  (** *** The per-cell ballot ([m = S n] candidates)

      The voter's randomness records, filled from the oracle [rnd].
      [pos_rand_of] and [pair_rand_of] read fixed oracle indices, and in the
      extracted program each call of [rnd] returns fresh randomness. *)
  Definition pos_rand_of (n : nat) (rnd : nat -> F) : @pos_rand F n :=
    mk_pos_rand (rnd 0) (Vector.map (fun _ => rnd 1) (fin_enum _)) (rnd 2).

  Definition pair_rand_of (n : nat) (rnd : nat -> F) : @pair_rand F n :=
    mk_pair_rand (rnd 0) (Vector.map (fun _ => rnd 1) (fin_enum 3)) (rnd 2)
      (Vector.map (fun _ => rnd 3) (fin_enum _)) (rnd 4).

  (** The randomness of a whole ballot, one record per position and per
      pair. *)
  Definition ballot_rand_of (n : nat) (rnd : nat -> F) : @ballot_rand F n :=
    mk_ballot_rand
      (Vector.map (fun _ => pos_rand_of n rnd) (fin_enum (S n)))
      (Vector.map (fun _ => Vector.map (fun _ => pair_rand_of n rnd) (fin_enum (S n)))
        (fin_enum (S n))).

  (** The non-interactive honest voter for ranking [s], with hash [H]. *)
  Definition nizk_encrypt_ballot_bench (n : nat) (H : list (G * G) -> F)
    (s : Vector.t nat (S n)) (rnd : nat -> F) : @ballot F G (S n) :=
    nizk_encrypt_ballot (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := Fsub) (opp := Fopp) (Fdec := Fdec) (G := G) (ginv := Ginv) (gop := Gmul)
      (gpow := Gpow) (n := n) g h H s (ballot_rand_of n rnd).

  (** The non-interactive ballot verifier. *)
  Definition nizk_verify_ballot_bench (n : nat) (H : list (G * G) -> F)
    (b : @ballot F G (S n)) : bool :=
    nizk_verify_ballot (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (G := G) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := n) g h H b.

  (** The number of group-element pairs a ballot puts on the bulletin board
      (the length of its hashed transcript of ciphertexts and
      announcements). Challenges and responses in [F] come on top. *)
  Definition ballot_board_size (n : nat) (b : @ballot F G (S n)) : nat :=
    List.length (ballot_transcript (G := G) (n := n) b).

  (** *** The tally

      The tally is benchmarked on counts computed from plaintext rankings
      and encrypted directly, independently of the ballot proofs. *)

  (** The pairwise counts [margin_count] of a list of rankings. *)
  Definition margins_bench (n : nat) (ss : list (Vector.t nat (S n))) :
    Vector.t (Vector.t Z (S n)) (S n) :=
    mat_of (n := n) (fun i j => Z.of_nat (Schulze.margin_count (Vector.of_list ss) i j)).

  (** Encrypts a count matrix entrywise under [(g, h)]. Every entry uses the
      same randomness [rnd 0]. *)
  Definition encrypt_margins_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n))
    (rnd : nat -> F) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    Vector.map (Vector.map (fun z =>
      @enc F G Gmul Gpow g h (nat_to_F Fzero Fone Fadd (Z.to_nat z)) (rnd 0))) D.

  (** The defeats, the strongest-path closure ([minmax_closure]) and the
      winner ([winner_of]) of a count matrix. These time the trustees'
      plaintext computation, in particular the tabulated closure. *)
  Definition defeats_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) :
    Vector.t (Vector.t Z (S n)) (S n) :=
    mat_of (n := n) (defeat (fun_of (n := n) D)).

  Definition closure_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) :
    Vector.t (Vector.t Z (S n)) (S n) :=
    mat_of (n := n) (minmax_closure (defeat (fun_of (n := n) D))).

  Definition winner_bench (n : nat) (D : Vector.t (Vector.t Z (S n)) (S n)) : option (Fin.t (S n)) :=
    winner_of (minmax_closure (defeat (fun_of (n := n) D))).

  (** The trustees' non-interactive tally proof (decryption, certificate,
      and Fiat–Shamir with hash [H]). *)
  Definition nizk_generate_tally_bench (n n' : nat) (H : list (@tr_item G) -> F)
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n)) (rnd : nat -> F) :
    @tally_proof F G (S n) (S n') :=
    nizk_generate_tally (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul)
      (sub := Fsub) (opp := Fopp) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) (n' := n') x g h H encD w rnd.

  (** The non-interactive tally verifier. *)
  Definition nizk_verify_tally_bench (n n' : nat) (H : list (@tr_item G) -> F)
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n))
    (pf : @tally_proof F G (S n) (S n')) : bool :=
    nizk_verify_tally (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) (n' := n') g h H encD w pf.

  (** The seven individual checks of the tally verifier, for diagnostics. *)
  Definition tally_checks_bench (n n' : nat)
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) (w : Fin.t (S n))
    (pf : @tally_proof F G (S n) (S n')) : list bool :=
    tally_checks (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (m := S n) (N := S n') g h encD w pf.

  (** The number of entries in the hashed tally transcript. *)
  Definition tally_board_size (n n' : nat) (encD : Vector.t (Vector.t (G * G) (S n)) (S n))
    (w : Fin.t (S n)) (pf : @tally_proof F G (S n) (S n')) : nat :=
    List.length (tally_transcript (n := n) (n' := n') encD w pf).

  (** *** A full election

      The valid ballots are aggregated and the counts decrypted. *)

  (** The homomorphic aggregate of a list of per-cell ballots. *)
  Definition aggregate_bench (n : nat) (bs : list (@ballot F G (S n))) :
    Vector.t (Vector.t (G * G) (S n)) (S n) :=
    aggregate_list (gid := Gone) (gop := Gmul) (n := n) bs.

  (** Decryption of the aggregate by the trustees ([decrypt_margins]). *)
  Definition decrypt_margins_bench (n n' : nat)
    (encD : Vector.t (Vector.t (G * G) (S n)) (S n)) : Vector.t (Vector.t Z (S n)) (S n) :=
    decrypt_margins (zero := Fzero) (one := Fone) (add := Fadd) (G := G) (ginv := Ginv)
      (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) (n := n) (n' := n') x g encD.

  (** *** The batched ballot ([Frontend/SchulzeBatched.v])

      The size parameters, exported for the driver: [K = m²] pairs,
      [NX = L · m²] bit columns, and [W], the length of the linear-relation
      witness. *)
  Definition K2 (n : nat) : nat := @K n.
  Definition NX2 (n L : nat) : nat := @NX n L.
  Definition W2 (n L : nat) : nat := @W n L.

  (** The interactive honest voter for the batched ballot, with commitment
      keys [(h1, gs1)] and [(h1, gs2)], challenges [ch], and ranking [sn]. *)
  Definition encrypt_ballot2_bench (n L : nat) (h1 : G) (gs1 gs2 : list G) (ch : @chal2 F)
    (sn : list nat) (rd : @rand2 F) : @ballot2 F G :=
    encrypt_ballot2 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) L g h h1 gs1 gs2 ch sn rd.

  (** The interactive batched-ballot verifier. *)
  Definition verify_ballot2_bench (n L : nat) (h1 : G) (gs1 gs2 : list G) (ch : @chal2 F)
    (bt : @ballot2 F G) : bool :=
    verify_ballot2 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (Fdec := Fdec) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 gs2 ch bt.

  (** The Fiat–Shamir challenges of a batched ballot under hash [H]. *)
  Definition challenges2_bench (n : nat) (H : list (@b2_item F G) -> F) (bt : @ballot2 F G) : @chal2 F :=
    challenges_of (n := n) H bt.

  (** The non-interactive batched-ballot verifier. *)
  Definition nizk_verify_ballot2_bench (n L : nat) (h1 : G) (gs1 gs2 : list G)
    (H : list (@b2_item F G) -> F) (bt : @ballot2 F G) : bool :=
    nizk_verify_ballot2 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (Fdec := Fdec) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 gs2 H bt.

  (** The pairwise-bit ciphertext matrix of a batched ballot, which is the
      input to the tally. *)
  Definition ballot2_bits_bench (n : nat) (bt : @ballot2 F G) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    ballot2_bits (gid := Gone) (n := n) bt.

  (** *** The simplified batched ballot ([Frontend/SchulzeSimple.v])

      The size parameters: [W3], the witness length, and [R = L + 3], the
      number of rows of the combined zero argument. *)
  Definition W3_bench (n : nat) : nat := @W3 n.
  Definition R3_bench (L : nat) : nat := @R L.

  (** The derived commitment key [g'_i = ∏_k g_k ^ M_ki] for the
      differences [δ = M s]. *)
  Definition gd_bench (n : nat) (gs1 : list G) : list G :=
    gd (zero := Fzero) (one := Fone) (sub := Fsub) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) gs1.

  (** The interactive honest voter for the simplified ballot. *)
  Definition encrypt_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G) (ch : @chal3 F)
    (sn : list nat) (rd : @rand3 F) : @ballot3 F G :=
    encrypt_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) L g h h1 gs1 ch sn rd.

  (** The interactive simplified-ballot verifier. *)
  Definition verify_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G) (ch : @chal3 F)
    (bt : @ballot3 F G) : bool :=
    verify_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 ch bt.

  (** The Fiat–Shamir challenges of a simplified ballot under hash [H]. *)
  Definition challenges3_bench (n : nat) (H : list (@b3_item F G) -> F) (bt : @ballot3 F G) : @chal3 F :=
    challenges_of3 (n := n) H bt.

  (** The non-interactive simplified-ballot verifier. *)
  Definition nizk_verify_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G)
    (H : list (@b3_item F G) -> F) (bt : @ballot3 F G) : bool :=
    nizk_verify_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      (n := n) L g h h1 gs1 H bt.

  (** The pairwise-bit ciphertext matrix of a simplified ballot. *)
  Definition ballot3_bits_bench (n : nat) (bt : @ballot3 F G) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    ballot3_bits (gid := Gone) (n := n) bt.

  (** The non-interactive honest voter for the simplified ballot. *)
  Definition nizk_encrypt_ballot3_bench (n L : nat) (h1 : G) (gs1 : list G)
    (H : list (@b3_item F G) -> F) (sn : list nat) (rd : @rand3 F) : @ballot3 F G :=
    nizk_encrypt_ballot3 (zero := Fzero) (one := Fone) (add := Fadd) (mul := Fmul) (sub := Fsub)
      (opp := Fopp) (gid := Gone) (gop := Gmul) (gpow := Gpow) (n := n) L g h h1 gs1 H sn rd.

  (** The aggregate of a list of simplified ballots. It is the list version of
      [SchulzeBatchedTally.aggregate_bits] applied to [ballot3_bits], the
      aggregate on which [Backend/SchulzeSimpleTally.v] states its
      theorem. *)
  Definition aggregate3_bench (n : nat) (bs : list (@ballot3 F G)) : Vector.t (Vector.t (G * G) (S n)) (S n) :=
    List.fold_right (fun b acc => Vector.map2 (Vector.map2 (Schulze.cmul (gop := Gmul))) (ballot3_bits_bench n b) acc)
      (Vector.const (Vector.const (Schulze.cid (gid := Gone)) (S n)) (S n)) bs.

End SchulzeBench.
