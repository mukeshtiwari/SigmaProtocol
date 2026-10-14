(* A certified verifier for ElectionGuard 2.0 election records
   (https://www.electionguard.vote, specification version 2.0.0), for the
   parts of the record that are proofs about ElGamal ciphertexts in the
   Schnorr group of the specification:

   - the guardians' proofs of knowledge of their polynomial coefficients
     (verification 2): Schnorr proofs of K_ij = g^a_ij, and the joint
     public key K = ∏_i K_i0 (verification 3);
   - the range proofs of the encrypted selections (verification 5) and
     the selection-limit proofs of the contests (verification 6): each
     is a disjunction over j = 0..R of "(α, β / K^j) = (g, K)^ξ", the
     Or composition of Chaum-Pedersen statements, which is a disjunction
     of Schnorr statements in the product group G × G with the common
     base (g, K);
   - the aggregation of the cast ballots into the encrypted tally
     (verification 8);
   - the decryption proofs of the tally (verification 9) and the
     decrypted values (verification 10): the Chaum-Pedersen statement
     (K, M) = (g, A)^s, a Schnorr statement in G × G, and T = K^t with
     M = B / T.

   ElectionGuard writes each proof as (challenge c, response v) and the
   verifier reconstructs the announcements (a, b) = (g^v · α^c, K^w · β^c)
   with w = v − j·c and checks that the hash of the announcements is the
   sum of the challenges. In the product group with base (g, K) and
   message (α, β / K^j), the reconstruction is exactly the Belenios one,
   (g, K)^v · (α, β / K^j)^c, so the Fiat-Shamir layer of
   Backend/BeleniosTally.v (fs_verify and its theorems
   fs_verify_schnorr_accepting and fs_verify_or_accepting) is reused
   unchanged. The hash functions are parameters, as everywhere in this
   development: the driver computes them (HMAC-SHA-256 over the
   specification's fixed-width encodings, keyed by the parameter base
   hash H_P or the extended base hash H_E) and passes them in. The
   checks that are only about hashes (manifest, base hashes, contest
   hashes, confirmation codes) and the hashed-ElGamal contest data are
   done by the driver. *)

From Stdlib Require Import Utf8 ZArith Vector List Lia Bool
  setoid_ring.Field Psatz.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space Product_space.
From Crypto Require Import Sigma OrSigmaGen.
From Backend Require Import BeleniosTally.
From Utility Require Import Util.
Import VectorNotations.

Section ElectionGuard.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  (* the product group G × G and the Fiat-Shamir layer of BeleniosTally *)
  Local Notation G2 := (G * G)%type.
  Local Notation gop2 := (BeleniosTally.gop2 (gop := gop)).
  Local Notation gpow2 := (BeleniosTally.gpow2 (gpow := gpow)).
  Local Notation gid2 := (BeleniosTally.gid2 (gid := gid)).
  Local Notation ginv2 := (BeleniosTally.ginv2 (ginv := ginv)).
  Local Notation Gdec2 := (BeleniosTally.Gdec2 (Gdec := Gdec)).
  Local Notation vspace2 := (BeleniosTally.vspace2 (Hvec := Hvec)).
  Local Notation proof := (@BeleniosTally.proof F).
  Local Notation ciphertext := (@BeleniosTally.ciphertext G).
  Local Notation nat_to_F := (BeleniosTally.nat_to_F (zero := zero) (one := one) (add := add)).
  Local Notation fs_verify1 :=
    (fs_verify (zero := zero) (add := add) (Fdec := Fdec) (vadd := gop) (smul := gpow)).
  Local Notation fs_verify2 :=
    (fs_verify (zero := zero) (add := add) (Fdec := Fdec) (vadd := gop2) (smul := gpow2)).

  (* ---------------------------------------------------------------- *)
  (* Election data                                                     *)
  (* ---------------------------------------------------------------- *)

  (* a contest of the manifest *)
  Record contest_spec : Type := mk_contest_spec {
    nselections : nat;      (* number of options *)
    option_limit : nat;     (* R: each option encrypts a value in 0..R *)
    selection_limit : nat   (* L: the options sum to a value in 0..L *)
  }.

  Record election : Type := mk_election {
    g : G;                          (* the generator of the specification *)
    K : G;                          (* the joint election public key *)
    nguardians : nat;               (* n *)
    quorum : nat;                   (* k *)
    contests : list contest_spec    (* in the order of the manifest *)
  }.

  (* an encrypted option, with its range proof (R + 1 pairs) *)
  Record selection : Type := mk_selection {
    encrypted_vote : ciphertext;
    range_proof : list proof
  }.

  (* an encrypted contest: the contest's position in the manifest, its
    options in the order of the manifest, and the selection-limit proof
    (L + 1 pairs) *)
  Record contest : Type := mk_contest {
    cindex : nat;
    selections : list selection;
    limit_proof : list proof
  }.

  Record ballot : Type := mk_ballot {
    bcontests : list contest;
    cast : bool                     (* cast, as opposed to challenged *)
  }.

  (* The hash functions of one ballot, as ElectionGuard computes them
    from the extended base hash, the public key, the ciphertext and the
    announcements. They are supplied by the driver. *)
  Record ballot_hashes : Type := mk_ballot_hashes {
    h_range : nat -> nat -> list G2 -> F;   (* contest i, option j: H(H_E; 0x21, K, α, β, a_0, b_0, …, a_R, b_R) *)
    h_limit : nat -> list G2 -> F           (* contest i: the same, over the aggregate of its options *)
  }.

  (* ---------------------------------------------------------------- *)
  (* Range proofs                                                      *)
  (* ---------------------------------------------------------------- *)

  (* the message of the j-th branch: (α, β / K^j) *)
  Definition message (E : election) (c : ciphertext) (j : nat) : G2 :=
    (fst c, gop (snd c) (ginv (gpow (K E) (nat_to_F j)))).

  (* the statements (α, β / K^j) = (g, K)^ξ, j = 0..R *)
  Definition range_statements (E : election) (c : ciphertext) (R : nat) : list (G2 * G2) :=
    List.map (fun j => ((g E, K E), message E c j)) (List.seq 0 (S R)).

  (* verification 5 / 6: the R + 1 proofs of a ciphertext, against the
    hash of the reconstructed announcements *)
  Definition verify_range (E : election) (H : list G2 -> F) (c : ciphertext) (R : nat)
    (pfs : list proof) : bool :=
    fs_verify2 H (range_statements E c R) pfs.

  Definition aggregate (cs : list ciphertext) : ciphertext :=
    sum_ciphertexts (gid := gid) (gop := gop) cs.

  Definition verify_contest (E : election) (hs : ballot_hashes) (spec : contest_spec)
    (ct : contest) : bool :=
    Nat.eqb (length ct.(selections)) spec.(nselections) &&
    forallb (fun '(j, s) =>
      verify_range E (hs.(h_range) ct.(cindex) j) s.(encrypted_vote) spec.(option_limit) s.(range_proof))
      (List.combine (List.seq 0 (length ct.(selections))) ct.(selections)) &&
    verify_range E (hs.(h_limit) ct.(cindex))
      (aggregate (List.map encrypted_vote ct.(selections))) spec.(selection_limit) ct.(limit_proof).

  Fixpoint strictly_increasing (l : list nat) : bool :=
    match l with
    | nil => true
    | List.cons a l' =>
        match l' with
        | nil => true
        | List.cons b _ => Nat.ltb a b && strictly_increasing l'
        end
    end.

  (* a ballot is valid when its contests are distinct contests of the
    manifest, in order, and each is valid *)
  Definition verify_ballot (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    strictly_increasing (List.map cindex b.(bcontests)) &&
    forallb (fun ct =>
      match List.nth_error E.(contests) ct.(cindex) with
      | Some spec => verify_contest E hs spec ct
      | None => false
      end) b.(bcontests).

  (* ---------------------------------------------------------------- *)
  (* Aggregation (verification 8)                                      *)
  (* ---------------------------------------------------------------- *)

  (* the ciphertexts of contest i of a ballot; a ballot without the
    contest contributes the neutral element *)
  Definition contest_ciphertexts (i n : nat) (b : ballot) : list ciphertext :=
    match List.find (fun ct => Nat.eqb ct.(cindex) i) b.(bcontests) with
    | Some ct => List.map encrypted_vote ct.(selections)
    | None => List.repeat (gid, gid) n
    end.

  Definition ballot_tally (E : election) (b : ballot) : list (list ciphertext) :=
    List.map (fun '(i, spec) => contest_ciphertexts i spec.(nselections) b)
      (List.combine (List.seq 0 (length E.(contests))) E.(contests)).

  Definition mul_tallies (t u : list (list ciphertext)) : list (list ciphertext) :=
    List.map (fun '(cs, ds) =>
      List.map (fun '(c, d) => mul_ciphertext (gop := gop) c d) (List.combine cs ds))
      (List.combine t u).

  Definition neutral_tally (E : election) : list (list ciphertext) :=
    List.map (fun spec => List.repeat (gid, gid) spec.(nselections)) E.(contests).

  (* the encrypted tally: the product, option by option, of the cast ballots *)
  Definition encrypted_tally (E : election) (bs : list ballot) : list (list ciphertext) :=
    List.fold_right (fun b acc => mul_tallies (ballot_tally E b) acc)
      (neutral_tally E) (List.filter cast bs).

  (* ---------------------------------------------------------------- *)
  (* Guardians (verifications 2 and 3)                                 *)
  (* ---------------------------------------------------------------- *)

  Record guardian : Type := mk_guardian {
    xcoord : nat;                       (* the guardian's index i, from 1 *)
    coefficients : list G;              (* K_i0, …, K_i(k-1) *)
    coefficient_proofs : list proof
  }.

  Record guardian_hashes : Type := mk_guardian_hashes {
    h_coef : nat -> nat -> list G -> F  (* guardian i, coefficient j: H(H_P; 0x10, i, j, K_ij, h_ij) *)
  }.

  (* each coefficient commitment K_ij comes with a Schnorr proof *)
  Definition verify_guardian (E : election) (gh : guardian_hashes) (gd : guardian) : bool :=
    Nat.eqb (length gd.(coefficients)) E.(quorum) &&
    Nat.eqb (length gd.(coefficients)) (length gd.(coefficient_proofs)) &&
    forallb (fun '(j, (Kij, pf)) =>
      fs_verify1 (gh.(h_coef) gd.(xcoord) j) (List.cons (g E, Kij) List.nil) (List.cons pf List.nil))
      (List.combine (List.seq 0 (length gd.(coefficients)))
        (List.combine gd.(coefficients) gd.(coefficient_proofs))).

  (* K = ∏_i K_i0 *)
  Definition joint_key (gs : list guardian) : G :=
    List.fold_right (fun gd acc =>
      match gd.(coefficients) with
      | List.cons k0 _ => gop k0 acc
      | nil => acc
      end) gid gs.

  Definition verify_guardians (E : election) (gh : guardian_hashes) (gs : list guardian) : bool :=
    Nat.eqb (length gs) E.(nguardians) &&
    (* the guardians are 1, …, n, in order *)
    forallb (fun '(i, gd) => Nat.eqb gd.(xcoord) i)
      (List.combine (List.seq 1 (length gs)) gs) &&
    forallb (verify_guardian E gh) gs &&
    (if Gdec (joint_key gs) E.(K) then true else false).

  (* ---------------------------------------------------------------- *)
  (* Decryption (verifications 9 and 10)                               *)
  (* ---------------------------------------------------------------- *)

  Record decryption : Type := mk_decryption {
    dT : G;                (* T = K^t, the "b_over_m" of the record *)
    dproof : proof;
    dvalue : F             (* t, the decrypted value *)
  }.

  Record decryption_hashes : Type := mk_decryption_hashes {
    h_dec : nat -> nat -> list G2 -> F   (* contest i, option j: H(H_E; 0x30, K, A, B, a, b, M) *)
  }.

  (* (K, M) = (g, A)^s with M = B / T, and T = K^t *)
  Definition verify_decryption (E : election) (H : list G2 -> F) (c : ciphertext)
    (d : decryption) : bool :=
    let M := gop (snd c) (ginv d.(dT)) in
    fs_verify2 H (List.cons ((g E, fst c), (K E, M)) List.nil) (List.cons d.(dproof) List.nil) &&
    (if Gdec d.(dT) (gpow (K E) d.(dvalue)) then true else false).

  (* the decryptions of a tally (or of a challenged ballot), option by option *)
  Definition verify_decryptions (E : election) (dh : decryption_hashes)
    (tally : list (list ciphertext)) (ds : list (list decryption)) : bool :=
    Nat.eqb (length tally) (length ds) &&
    forallb (fun '(i, (cs, dsi)) =>
      Nat.eqb (length cs) (length dsi) &&
      forallb (fun '(j, (c, d)) => verify_decryption E (dh.(h_dec) i j) c d)
        (List.combine (List.seq 0 (length cs)) (List.combine cs dsi)))
      (List.combine (List.seq 0 (length tally)) (List.combine tally ds)).

  (* a challenged ballot (verifications 12 and 13): its own ciphertexts,
    decrypted *)
  Definition verify_ballot_decryptions (E : election) (dh : decryption_hashes)
    (b : ballot) (ds : list (list decryption)) : bool :=
    verify_decryptions E dh (ballot_tally E b) ds.

  (* ---------------------------------------------------------------- *)
  (* The certificate                                                   *)
  (* ---------------------------------------------------------------- *)

  Inductive state : Type :=
  | partial : list ballot -> list ballot -> list ballot -> state
  | finished : list ballot -> list ballot -> list ballot -> bool -> state.

  Inductive count (E : election) (hs : ballot -> ballot_hashes) : state -> Type :=
  | ax : count E hs (partial nil nil nil)
  | cvalid (b : ballot) (us vbs inbs : list ballot) :
      count E hs (partial us vbs inbs) ->
      verify_ballot E (hs b) b = true ->
      count E hs (partial (List.cons b us) (List.cons b vbs) inbs)
  | cinvalid (b : ballot) (us vbs inbs : list ballot) :
      count E hs (partial us vbs inbs) ->
      verify_ballot E (hs b) b = false ->
      count E hs (partial (List.cons b us) vbs (List.cons b inbs))
  | cfinish (us vbs inbs : list ballot) (gh : guardian_hashes) (gs : list guardian)
      (dh : decryption_hashes) (tally published : list (list ciphertext))
      (ds : list (list decryption)) (bg bt bd : bool) :
      count E hs (partial us vbs inbs) ->
      (* the guardians' proofs and the joint public key *)
      verify_guardians E gh gs = bg ->
      (* the encrypted tally of the valid cast ballots is the published one *)
      tally = encrypted_tally E (List.rev vbs) ->
      tally_eqb (Gdec := Gdec) tally published = bt ->
      (* the decryption proofs and the decrypted values *)
      verify_decryptions E dh tally ds = bd ->
      count E hs (finished us vbs inbs (bg && bt && bd)).

  Definition compute_final_tally (E : election) (hs : ballot -> ballot_hashes) :
    forall (bs : list ballot),
    existsT (vbs inbs : list ballot), count E hs (partial bs vbs inbs).
  Proof.
    refine (fix fn bs :=
      match bs with
      | nil => existT _ nil (existT _ nil (ax E hs))
      | List.cons b bs' =>
          match fn bs' with
          | existT _ vbs (existT _ inbs c) =>
              match verify_ballot E (hs b) b as v return verify_ballot E (hs b) b = v -> _ with
              | true => fun hv => existT _ (List.cons b vbs) (existT _ inbs (cvalid E hs b bs' vbs inbs c hv))
              | false => fun hv => existT _ vbs (existT _ (List.cons b inbs) (cinvalid E hs b bs' vbs inbs c hv))
              end eq_refl
          end
      end).
  Defined.

  (* The certified verifier: the guardians, the ballots, the published
    encrypted tally and its decryptions; returns the certificate. *)
  Definition compute_final_count (E : election) (hs : ballot -> ballot_hashes)
    (gh : guardian_hashes) (gs : list guardian) (bs : list ballot)
    (published : list (list ciphertext)) (dh : decryption_hashes)
    (ds : list (list decryption)) :
    existsT (vbs inbs : list ballot) (bfinal : bool),
      count E hs (finished (List.rev bs) vbs inbs bfinal).
  Proof.
    destruct (compute_final_tally E hs (List.rev bs)) as (vbs & inbs & c).
    set (tally := encrypted_tally E (List.rev vbs)).
    exists vbs, inbs,
      (verify_guardians E gh gs &&
       tally_eqb (Gdec := Gdec) tally published &&
       verify_decryptions E dh tally ds).
    exact (cfinish E hs (List.rev bs) vbs inbs gh gs dh tally published ds _ _ _ c
      eq_refl eq_refl eq_refl eq_refl).
  Defined.

  (* ---------------------------------------------------------------- *)
  (* Link to the library                                               *)
  (* ---------------------------------------------------------------- *)

  (* A verified coefficient proof is an accepting transcript of the
    Schnorr protocol for K_ij = g^a_ij. *)
  Theorem coefficient_proof_schnorr_accepting : forall (E : election) (H : list G -> F)
    (Kij : G) (c s : F),
    fs_verify1 H (List.cons (g E, Kij) List.nil) (List.cons (c, s) List.nil) = true ->
    @accepting_conversation F G gop gpow Gdec (g E) Kij
      (mk_sigma _ _ _ [reconstruct (vadd := gop) (smul := gpow) (g E) Kij c s] [opp c] [s]) = true.
  Proof.
    intros * hv.
    exact (fs_verify_schnorr_accepting (Hvec := Hvec) (HV := Hvec) H (g E) Kij c s hv).
  Qed.

  (* every coefficient proof of a verified guardian *)
  Lemma forallb_seq_combine : forall {A B : Type} (f : nat -> A -> B -> bool)
    (xs : list A) (ys : list B) (k : nat),
    forallb (fun '(j, (x, y)) => f j x y) (List.combine (List.seq k (length xs)) (List.combine xs ys)) = true ->
    forall j x y, List.nth_error xs j = Some x -> List.nth_error ys j = Some y -> f (k + j) x y = true.
  Proof.
    intros A B f xs; induction xs as [| x xs ih]; intros ys k hf j x' y hx hy.
    + destruct j; cbn in hx; discriminate.
    + destruct ys as [| y' ys]; [destruct j; cbn in hy; discriminate |].
      cbn in hf; apply andb_true_iff in hf; destruct hf as [h1 h2].
      destruct j as [| j]; cbn in hx, hy.
      - inversion hx; inversion hy; subst; rewrite Nat.add_0_r; exact h1.
      - rewrite <-Nat.add_succ_comm; exact (ih ys (S k) h2 j x' y hx hy).
  Qed.

  Theorem verify_guardian_schnorr_accepting : forall (E : election) (gh : guardian_hashes)
    (gd : guardian) (j : nat) (Kij : G) (c s : F),
    verify_guardian E gh gd = true ->
    List.nth_error gd.(coefficients) j = Some Kij ->
    List.nth_error gd.(coefficient_proofs) j = Some (c, s) ->
    @accepting_conversation F G gop gpow Gdec (g E) Kij
      (mk_sigma _ _ _ [reconstruct (vadd := gop) (smul := gpow) (g E) Kij c s] [opp c] [s]) = true.
  Proof.
    intros * hv hK hp.
    unfold verify_guardian in hv.
    apply andb_true_iff in hv; destruct hv as [_ hf].
    apply (coefficient_proof_schnorr_accepting E (gh.(h_coef) gd.(xcoord) j)).
    exact (forallb_seq_combine
      (fun j (Kij : G) (pf : F * F) => fs_verify1 (gh.(h_coef) gd.(xcoord) j)
        (List.cons (g E, Kij) List.nil) (List.cons pf List.nil))
      gd.(coefficients) gd.(coefficient_proofs) 0 hf j Kij (c, s) hK hp).
  Qed.

  (* the messages of the branches, as a vector, for the statement about
    the library's Or composition *)
  Fixpoint messages_from (E : election) (c : ciphertext) (k n : nat) : Vector.t G2 n :=
    match n with
    | 0 => []
    | S n' => message E c k :: messages_from E c (S k) n'
    end.

  Lemma messages_from_to_list : forall (E : election) (c : ciphertext) (n k : nat),
    Vector.to_list (messages_from E c k n) = List.map (message E c) (List.seq k n).
  Proof.
    intros E c n; induction n as [| n ih]; intro k; [reflexivity |].
    cbn [messages_from List.seq List.map].
    change (Vector.to_list (message E c k :: messages_from E c (S k) n))
      with (List.cons (message E c k) (Vector.to_list (messages_from E c (S k) n))).
    rewrite ih; reflexivity.
  Qed.

  Lemma map2_pair_const_to_list : forall {A B : Type} (a : A) (n : nat) (v : Vector.t B n),
    Vector.to_list (Vector.map2 pair (Vector.const a n) v) = List.map (pair a) (Vector.to_list v).
  Proof.
    intros A B a n; induction n as [| n ih]; intro v.
    + rewrite (vector_inv_0 v); reflexivity.
    + destruct (vector_inv_S v) as (x & v' & ->).
      cbn; f_equal; apply ih.
  Qed.

  Lemma range_statements_vec : forall (E : election) (c : ciphertext) (n : nat),
    range_statements E c n =
    Vector.to_list (Vector.map2 pair (Vector.const (g E, K E) (S n)) (messages_from E c 0 (S n))).
  Proof.
    intros; unfold range_statements.
    rewrite map2_pair_const_to_list, messages_from_to_list, List.map_map; reflexivity.
  Qed.

  (* A verified range proof with R + 1 = 2 + n branches is an accepting
    transcript of the library's Or composition of the Schnorr statements
    (α, β / K^j) = (g, K)^ξ in G × G, with the reconstructed announcements
    and negated challenges. *)
  Theorem verify_range_or_accepting : forall (E : election) (H : list G2 -> F)
    (c : ciphertext) (n : nat) (cs ss : Vector.t F (2 + n)),
    verify_range E H c (S n) (Vector.to_list (Vector.map2 pair cs ss)) = true ->
    @generalised_or_accepting_conversations F zero add Fdec G2 gop2 gpow2 Gdec2 (2 + n)
      (Vector.const (g E, K E) (2 + n)) (messages_from E c 0 (2 + n))
      (mk_sigma _ _ _
        (announcements_vec (vadd := gop2) (smul := gpow2)
          (Vector.const (g E, K E) (2 + n)) (messages_from E c 0 (2 + n)) cs ss)
        (opp (Vector.fold_right add cs zero) :: Vector.map opp cs) ss) = true.
  Proof.
    intros * hv.
    unfold verify_range in hv.
    rewrite range_statements_vec in hv.
    exact (fs_verify_or_accepting (Hvec := Hvec) (HV := vspace2) n H
      (Vector.const (g E, K E) (2 + n)) (messages_from E c 0 (2 + n)) cs ss hv).
  Qed.

  (* A verified decryption proof is an accepting transcript of the Schnorr
    protocol in G × G for (K, M) = (g, A)^s, M = B / T. *)
  Theorem verify_decryption_schnorr_accepting : forall (E : election) (H : list G2 -> F)
    (c : ciphertext) (d : decryption),
    verify_decryption E H c d = true ->
    @accepting_conversation F G2 gop2 gpow2 Gdec2 (g E, fst c) (K E, gop (snd c) (ginv d.(dT)))
      (mk_sigma _ _ _
        [reconstruct (vadd := gop2) (smul := gpow2) (g E, fst c) (K E, gop (snd c) (ginv d.(dT)))
          (fst d.(dproof)) (snd d.(dproof))]
        [opp (fst d.(dproof))] [snd d.(dproof)]) = true.
  Proof.
    intros * hv.
    unfold verify_decryption in hv.
    apply andb_true_iff in hv; destruct hv as [hv _].
    destruct d as [T [c' s] t]; cbn [fst snd dproof dT] in *.
    exact (fs_verify_schnorr_accepting (Hvec := Hvec) (HV := vspace2) H
      (g E, fst c) (K E, gop (snd c) (ginv T)) c' s hv).
  Qed.

End ElectionGuard.
