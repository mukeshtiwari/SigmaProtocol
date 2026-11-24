(** * ElectionGuard tally verifier *)

(** A certified verifier for ElectionGuard 2.0 election records
    (specification version 2.0.0), covering the parts of the record that
    are proofs about ElGamal ciphertexts in the specification's Schnorr
    group.  ElectionGuard encrypts a value [m] as [(α, β) = (g^ξ, K^(m+ξ))]
    under the joint key [K], so plaintexts are encoded as powers of [K].
    The numbers below refer to the verification steps of the specification.

    - Guardian key ceremony (verifications 2 and 3): each guardian [i]
      commits to its polynomial coefficients [K_ij = g^(a_ij)] with Schnorr
      proofs, and [K = ∏_i K_i0] ([verify_guardians]).
    - Ballot validity (verifications 5 and 6): each selection has a range
      proof that it encrypts a value in [0..R], and each contest a
      selection-limit proof that the product of its selections encrypts a
      value in [0..L].  Each is a disjunction over [j] of the
      Chaum–Pedersen statement [(α, β / K^j) = (g, K)^ξ]
      ([verify_range], [verify_contest], [verify_ballot]).
    - Aggregation (verification 8): the encrypted tally is the product of
      the valid cast ballots ([encrypted_tally]).
    - Decryption (verifications 9 and 10): for each tally ciphertext
      [(A, B)] the record gives [T = K^t] and a proof that
      [(K, M) = (g, A)^s] with [M = B / T] ([verify_decryption]).

    ElectionGuard writes a proof as (challenge [c], response [v]) and the
    verifier reconstructs the announcements and checks that their hash is
    the sum of the challenges.  In the product group with base [(g, K)]
    this reconstruction coincides with the Belenios one, so the
    Fiat–Shamir layer ([fs_verify], [fs_verify_schnorr_accepting],
    [fs_verify_or_accepting]) and the [G × G] instance of
    [Backend/BeleniosTally.v] are reused unchanged.  The theorems at the
    end of the file ([verify_guardian_schnorr_accepting],
    [verify_range_or_accepting], [verify_decryption_schnorr_accepting])
    state that the reconstructed transcripts are accepting conversations
    of the library's Schnorr and OR protocols ([Crypto/Sigma.v],
    [Crypto/OrSigmaGen.v]), whose special soundness then applies.

    The verifier is an inductive certificate [count] built by
    [compute_final_tally] and [compute_final_count], extracted to OCaml in
    [src/Extraction/Electionguardlib] with the parameters of
    [Examples/ElectionGuardIns.v], and run on real records
    ([bench/electionguard-diff]).

    What is _not_ verified in this file: the hash functions are parameters
    computed by the OCaml driver (HMAC-SHA-256 over the specification's
    fixed-width encodings keyed by [H_P] or [H_E]); the hash-only checks
    (manifest, base hashes, contest hashes, confirmation codes) and the
    hashed-ElGamal contest data are done by the driver; group membership
    of the record's elements is not checked here; the decryptions of
    challenged ballots ([verify_ballot_decryptions], verifications 12 and
    13) are defined but are not part of the [count] certificate; and, as
    in Belenios, the soundness of Fiat–Shamir is not formalised (the
    [..._accepting] theorems do not depend on the hash check). *)
From Stdlib Require Import Utf8 ZArith Vector List Lia Bool
  setoid_ring.Field Psatz.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space Product_space.
From Sigma Require Import Sigma OrSigmaGen.
From Backend Require Import BeleniosTally.
From Utility Require Import Util.
Import VectorNotations.

(** ** Setting *)
Section ElectionGuard.

  (** Field [F], group [G] (a vector space over [F]) and decidable
      equalities. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  (** Local names for the product group [G × G], its vector-space instance,
      the Belenios proof type and ciphertexts, and the Fiat–Shamir verifier
      instantiated in [G] ([fs_verify1]) and in [G × G] ([fs_verify2]). *)
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

  (** ** Election data *)

  (** A contest of the manifest: number of options [nselections], the
      option limit [R] (each option encrypts a value in [0..R]) and the
      selection limit [L] (the options sum to a value in [0..L]). *)
  Record contest_spec : Type := mk_contest_spec {
    nselections : nat;
    option_limit : nat;
    selection_limit : nat
  }.

  (** The election: generator [g], joint public key [K], the number of
      guardians [n], the quorum [k], and the contests in manifest order. *)
  Record election : Type := mk_election {
    g : G;
    K : G;
    nguardians : nat;
    quorum : nat;
    contests : list contest_spec
  }.

  (** An encrypted option with its range proof ([R + 1] pairs). *)
  Record selection : Type := mk_selection {
    encrypted_vote : ciphertext;
    range_proof : list proof
  }.

  (** An encrypted contest: its position in the manifest, its options in
      manifest order, and its selection-limit proof ([L + 1] pairs). *)
  Record contest : Type := mk_contest {
    cindex : nat;
    selections : list selection;
    limit_proof : list proof
  }.

  (** A ballot: its contests and whether it was cast (as opposed to
      challenged). *)
  Record ballot : Type := mk_ballot {
    bcontests : list contest;
    cast : bool
  }.

  (** The hash functions for one ballot, supplied by the driver:
      [h_range i j] for option [j] of contest [i] and [h_limit i] for the
      selection-limit proof of contest [i]. *)
  Record ballot_hashes : Type := mk_ballot_hashes {
    h_range : nat -> nat -> list G2 -> F;
    h_limit : nat -> list G2 -> F
  }.

  (** ** Range proofs and ballot validity *)

  (** The target of branch [j]: [(α, β / K^j)]. *)
  Definition message (E : election) (c : ciphertext) (j : nat) : G2 :=
    (fst c, gop (snd c) (ginv (gpow (K E) (nat_to_F j)))).

  (** The [R + 1] statements [(α, β / K^j) = (g, K)^ξ] for [j = 0..R]. *)
  Definition range_statements (E : election) (c : ciphertext) (R : nat) : list (G2 * G2) :=
    List.map (fun j => ((g E, K E), message E c j)) (List.seq 0 (S R)).

  (** Range proof of a ciphertext (verifications 5 and 6): the [R + 1]
      proofs verify against the hash [H] of the reconstructed
      announcements. *)
  Definition verify_range (E : election) (H : list G2 -> F) (c : ciphertext) (R : nat)
    (pfs : list proof) : bool :=
    fs_verify2 H (range_statements E c R) pfs.

  (** Homomorphic product of a list of ciphertexts. *)
  Definition aggregate (cs : list ciphertext) : ciphertext :=
    sum_ciphertexts (gid := gid) (gop := gop) cs.

  (** A contest is valid when it has the expected number of options, every
      option's range proof for [0..R] verifies, and the selection-limit
      proof for [0..L] verifies on the product of its options. *)
  Definition verify_contest (E : election) (hs : ballot_hashes) (spec : contest_spec)
    (ct : contest) : bool :=
    Nat.eqb (length ct.(selections)) spec.(nselections) &&
    forallb (fun '(j, s) =>
      verify_range E (hs.(h_range) ct.(cindex) j) s.(encrypted_vote) spec.(option_limit) s.(range_proof))
      (List.combine (List.seq 0 (length ct.(selections))) ct.(selections)) &&
    verify_range E (hs.(h_limit) ct.(cindex))
      (aggregate (List.map encrypted_vote ct.(selections))) spec.(selection_limit) ct.(limit_proof).

  (** Whether a list of naturals is strictly increasing. *)
  Fixpoint strictly_increasing (l : list nat) : bool :=
    match l with
    | nil => true
    | List.cons a l' =>
        match l' with
        | nil => true
        | List.cons b _ => Nat.ltb a b && strictly_increasing l'
        end
    end.

  (** A ballot is valid when its contest indices are strictly increasing
      (distinct and in manifest order), each index names a manifest
      contest, and each contest is valid. *)
  Definition verify_ballot (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    strictly_increasing (List.map cindex b.(bcontests)) &&
    forallb (fun ct =>
      match List.nth_error E.(contests) ct.(cindex) with
      | Some spec => verify_contest E hs spec ct
      | None => false
      end) b.(bcontests).

  (** ** Aggregation *)

  (** The ciphertexts of contest [i] of a ballot; a ballot without that
      contest contributes [n] neutral ciphertexts. *)
  Definition contest_ciphertexts (i n : nat) (b : ballot) : list ciphertext :=
    match List.find (fun ct => Nat.eqb ct.(cindex) i) b.(bcontests) with
    | Some ct => List.map encrypted_vote ct.(selections)
    | None => List.repeat (gid, gid) n
    end.

  (** A ballot laid out as a full tally, contest by contest in manifest
      order. *)
  Definition ballot_tally (E : election) (b : ballot) : list (list ciphertext) :=
    List.map (fun '(i, spec) => contest_ciphertexts i spec.(nselections) b)
      (List.combine (List.seq 0 (length E.(contests))) E.(contests)).

  (** Component-wise product of two tallies. *)
  Definition mul_tallies (t u : list (list ciphertext)) : list (list ciphertext) :=
    List.map (fun '(cs, ds) =>
      List.map (fun '(c, d) => mul_ciphertext (gop := gop) c d) (List.combine cs ds))
      (List.combine t u).

  (** The empty tally: [(gid, gid)] for every option of every contest. *)
  Definition neutral_tally (E : election) : list (list ciphertext) :=
    List.map (fun spec => List.repeat (gid, gid) spec.(nselections)) E.(contests).

  (** The encrypted tally (verification 8): the product of the cast ballots
      among the given list; challenged ballots are filtered out. *)
  Definition encrypted_tally (E : election) (bs : list ballot) : list (list ciphertext) :=
    List.fold_right (fun b acc => mul_tallies (ballot_tally E b) acc)
      (neutral_tally E) (List.filter cast bs).

  (** ** Guardians *)

  (** A guardian: its index (from 1), the coefficient commitments
      [K_i0, …, K_i(k−1)] and their Schnorr proofs. *)
  Record guardian : Type := mk_guardian {
    xcoord : nat;
    coefficients : list G;
    coefficient_proofs : list proof
  }.

  (** Hash function for the proof of coefficient [j] of guardian [i],
      supplied by the driver. *)
  Record guardian_hashes : Type := mk_guardian_hashes {
    h_coef : nat -> nat -> list G -> F
  }.

  (** A guardian is valid when it has [quorum] coefficients, one proof per
      coefficient, and each Schnorr proof of [K_ij = g^(a_ij)] verifies. *)
  Definition verify_guardian (E : election) (gh : guardian_hashes) (gd : guardian) : bool :=
    Nat.eqb (length gd.(coefficients)) E.(quorum) &&
    Nat.eqb (length gd.(coefficients)) (length gd.(coefficient_proofs)) &&
    forallb (fun '(j, (Kij, pf)) =>
      fs_verify1 (gh.(h_coef) gd.(xcoord) j) (List.cons (g E, Kij) List.nil) (List.cons pf List.nil))
      (List.combine (List.seq 0 (length gd.(coefficients)))
        (List.combine gd.(coefficients) gd.(coefficient_proofs))).

  (** The joint key [∏_i K_i0] (guardians without coefficients
      contribute nothing). *)
  Definition joint_key (gs : list guardian) : G :=
    List.fold_right (fun gd acc =>
      match gd.(coefficients) with
      | List.cons k0 _ => gop k0 acc
      | nil => acc
      end) gid gs.

  (** Verifications 2 and 3: there are [nguardians] guardians indexed
      [1, …, n] in order, each guardian is valid, and the joint key equals
      [K]. *)
  Definition verify_guardians (E : election) (gh : guardian_hashes) (gs : list guardian) : bool :=
    Nat.eqb (length gs) E.(nguardians) &&
    forallb (fun '(i, gd) => Nat.eqb gd.(xcoord) i)
      (List.combine (List.seq 1 (length gs)) gs) &&
    forallb (verify_guardian E gh) gs &&
    (if Gdec (joint_key gs) E.(K) then true else false).

  (** ** Decryption *)

  (** A decryption of one tally ciphertext: [T = K^t], the proof, and the
      decrypted value [t]. *)
  Record decryption : Type := mk_decryption {
    dT : G;
    dproof : proof;
    dvalue : F
  }.

  (** Hash function for the decryption proof of option [j] of contest [i],
      supplied by the driver. *)
  Record decryption_hashes : Type := mk_decryption_hashes {
    h_dec : nat -> nat -> list G2 -> F
  }.

  (** Verifications 9 and 10 for one ciphertext [(A, B)]: with [M = B / T],
      the proof of [(K, M) = (g, A)^s] verifies (a Schnorr statement in
      [G × G]), and [T = K^t].  The discrete logarithm [t] is supplied by
      the record; only the equation is checked. *)
  Definition verify_decryption (E : election) (H : list G2 -> F) (c : ciphertext)
    (d : decryption) : bool :=
    let M := gop (snd c) (ginv d.(dT)) in
    fs_verify2 H (List.cons ((g E, fst c), (K E, M)) List.nil) (List.cons d.(dproof) List.nil) &&
    (if Gdec d.(dT) (gpow (K E) d.(dvalue)) then true else false).

  (** All decryptions of a tally, option by option, with matching
      shapes. *)
  Definition verify_decryptions (E : election) (dh : decryption_hashes)
    (tally : list (list ciphertext)) (ds : list (list decryption)) : bool :=
    Nat.eqb (length tally) (length ds) &&
    forallb (fun '(i, (cs, dsi)) =>
      Nat.eqb (length cs) (length dsi) &&
      forallb (fun '(j, (c, d)) => verify_decryption E (dh.(h_dec) i j) c d)
        (List.combine (List.seq 0 (length cs)) (List.combine cs dsi)))
      (List.combine (List.seq 0 (length tally)) (List.combine tally ds)).

  (** Decryption of a challenged ballot (verifications 12 and 13): its own
      ciphertexts, laid out as a tally, are checked as above.  Not used by
      [count]. *)
  Definition verify_ballot_decryptions (E : election) (dh : decryption_hashes)
    (b : ballot) (ds : list (list decryption)) : bool :=
    verify_decryptions E dh (ballot_tally E b) ds.

  (** ** The certificate *)

  (** [partial us vbs inbs] and [finished us vbs inbs b], as in
      [Backend/BeleniosTally.v]. *)
  Inductive state : Type :=
  | partial : list ballot -> list ballot -> list ballot -> state
  | finished : list ballot -> list ballot -> list ballot -> bool -> state.

  (** The ElectionGuard certificate.  [ax], [cvalid] and [cinvalid]
      classify the ballots with [verify_ballot]; [cfinish] checks the
      guardians ([bg]), that the encrypted tally of the valid cast ballots
      (in the original order) equals the published one ([bt]), and the
      decryptions ([bd]); the final flag is [bg && bt && bd]. *)
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
      verify_guardians E gh gs = bg ->
      tally = encrypted_tally E (List.rev vbs) ->
      tally_eqb (Gdec := Gdec) tally published = bt ->
      verify_decryptions E dh tally ds = bd ->
      count E hs (finished us vbs inbs (bg && bt && bd)).

  (** Classifies the ballots and builds [count E hs (partial bs vbs inbs)],
      processing the list from its end. *)
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

  (** The certified verifier: from the guardians, the ballots, the
      published encrypted tally and its decryptions, returns the final flag
      and a certificate [count E hs (finished (rev bs) vbs inbs bfinal)].
      This is the entry point of the extracted verifier. *)
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

  (** ** Link with the Sigma-protocol library *)

  (** A verified coefficient proof [(c, s)] for [K_ij] yields the accepting
      Schnorr conversation [(g^s · K_ij^c; −c; s)] of [Crypto/Sigma.v].
      An instance of [fs_verify_schnorr_accepting]. *)
  Theorem coefficient_proof_schnorr_accepting : forall (E : election) (H : list G -> F)
    (Kij : G) (c s : F),
    fs_verify1 H (List.cons (g E, Kij) List.nil) (List.cons (c, s) List.nil) = true ->
    @accepting_conversation F G gop gpow Gdec (g E) Kij
      (mk_sigma _ _ _ [reconstruct (vadd := gop) (smul := gpow) (g E) Kij c s] [opp c] [s]) = true.
  Proof.
    intros * hv.
    exact (fs_verify_schnorr_accepting (Hvec := Hvec) (HV := Hvec) H (g E) Kij c s hv).
  Qed.

  (** If [forallb] holds over [combine (seq k (length xs)) (combine xs ys)],
      then [f (k + j) x y] holds for every position [j] present in both
      lists. *)
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

  (** For a valid guardian, the proof of every coefficient [K_ij] yields an
      accepting Schnorr conversation for [K_ij = g^(a_ij)]. *)
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

  (** The vector of branch targets [message E c k, …, message E c (k+n−1)]. *)
  Fixpoint messages_from (E : election) (c : ciphertext) (k n : nat) : Vector.t G2 n :=
    match n with
    | 0 => []
    | S n' => message E c k :: messages_from E c (S k) n'
    end.

  (** [messages_from] agrees with the list of [message E c j] for
      [j ∈ seq k n]. *)
  Lemma messages_from_to_list : forall (E : election) (c : ciphertext) (n k : nat),
    Vector.to_list (messages_from E c k n) = List.map (message E c) (List.seq k n).
  Proof.
    intros E c n; induction n as [| n ih]; intro k; [reflexivity |].
    cbn [messages_from List.seq List.map].
    change (Vector.to_list (message E c k :: messages_from E c (S k) n))
      with (List.cons (message E c k) (Vector.to_list (messages_from E c (S k) n))).
    rewrite ih; reflexivity.
  Qed.

  (** Pairing a constant with a vector commutes with [Vector.to_list]. *)
  Lemma map2_pair_const_to_list : forall {A B : Type} (a : A) (n : nat) (v : Vector.t B n),
    Vector.to_list (Vector.map2 pair (Vector.const a n) v) = List.map (pair a) (Vector.to_list v).
  Proof.
    intros A B a n; induction n as [| n ih]; intro v.
    + rewrite (vector_inv_0 v); reflexivity.
    + destruct (vector_inv_S v) as (x & v' & ->).
      cbn; f_equal; apply ih.
  Qed.

  (** [range_statements] written as the list of a vector of statements with
      the constant base [(g, K)]. *)
  Lemma range_statements_vec : forall (E : election) (c : ciphertext) (n : nat),
    range_statements E c n =
    Vector.to_list (Vector.map2 pair (Vector.const (g E, K E) (S n)) (messages_from E c 0 (S n))).
  Proof.
    intros; unfold range_statements.
    rewrite map2_pair_const_to_list, messages_from_to_list, List.map_map; reflexivity.
  Qed.

  (** A verified range proof with [R = n + 1 ≥ 1] (so at least two
      branches) yields an accepting conversation of the generalised OR
      composition of [Crypto/OrSigmaGen.v] on the statements
      [(α, β / K^j) = (g, K)^ξ], [j = 0..R], with reconstructed
      announcements and challenge vector [(−Σ c_j) :: (−c_0, …, −c_R)].
      Obtained from [fs_verify_or_accepting] via [range_statements_vec]. *)
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

  (** A verified decryption yields an accepting conversation, in [G × G],
      for the Chaum–Pedersen statement [(K, B / T) = (g, A)^s]. *)
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
