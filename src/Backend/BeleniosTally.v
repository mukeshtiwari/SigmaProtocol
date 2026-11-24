(** * Belenios tally verifier *)

(** This file is a certified verifier for Belenios elections (Cortier,
    Gaudry, Glondu; specification version 1 as implemented by Belenios 3.x)
    restricted to homomorphic questions, with or without blank votes,
    weighted credentials and single (non-threshold) trustees.

    Belenios uses ElGamal [(α, β) = (g^r, g^m · y^r)] with exponential
    encoding of votes.  Every non-interactive proof is stored as a list of
    pairs [(c, s)] (challenge, response).  The verifier reconstructs each
    announcement [A = g^s · h^c] and checks that the hash of the
    announcements equals the sum of the challenges.  All Belenios proofs
    have one of two shapes:

    - a Schnorr proof of [h = g^x] (trustee proofs of knowledge, ballot
      signatures with the credential, and, in the product group [G × G],
      the decryption proofs [(X, f) = (g, α)^x]);
    - a disjunction of such statements in [G × G] with common base
      [(g, y)], each branch saying [(α, β / m) = (g, y)^r]; this covers the
      individual 0/1 proofs, the overall interval proof and the two proofs
      used for possibly-blank votes.

    Section [FiatShamir] defines this verification ([fs_verify]) over any
    vector space and relates it to the library's Sigma protocols:
    [fs_verify_schnorr_accepting] and [fs_verify_or_accepting] show that
    the reconstructed transcript, with negated challenges, is an accepting
    conversation of the Schnorr protocol of [Crypto/Sigma.v] or of the
    disjunctive composition of [Crypto/OrSigmaGen.v].  The negation is
    needed because the library writes the response as [u + c·x] whereas
    Belenios writes [w − x·c].  The special-soundness and zero-knowledge
    theorems of those files then apply to the transcripts.

    The rest of the file describes the election data, ballot validity
    ([verify_ballot]), the weighted homomorphic tally of the last valid
    ballot of each credential ([encrypted_tally], [last_per_credential]),
    the trustees' partial decryptions ([verify_trustee]) and the result
    ([verify_result]).  As in [Backend/HeliosTally.v], the whole
    verification is an inductive certificate [count], built by
    [compute_final_tally] and [compute_final_count]; these are extracted
    to OCaml ([src/Extraction/Belenioslib]) and run on real Belenios data
    over Ed25519 (see [Examples/BeleniosIns.v] and [bench/belenios-diff]).
    The Fiat–Shamir layer and the [G × G] instance are reused by
    [Backend/ElectionGuardTally.v].

    What is _not_ verified here: the hash functions are parameters
    ([ballot_hashes], [trustee_hashes]); the OCaml driver computes them
    (SHA-256 over the Belenios serialisation, including the election
    fingerprint and the credential) and passes them in, so the correct
    domain separation and serialisation are trusted.  Soundness of
    Fiat–Shamir in the random oracle model is not formalised; the
    [..._accepting] theorems in fact hold whatever the hash check returns
    (the hypothesis is not used), so they only fix the meaning of the
    reconstructed transcripts.  Membership of group elements in the prime
    order subgroup, the election fingerprint, the authenticity of the
    credential list, threshold decryption and non-homomorphic (mixnet)
    questions are outside this file, and no end-to-end theorem about the
    computed result is stated. *)
From Stdlib Require Import Utf8 ZArith Vector List Lia Bool
  setoid_ring.Field Psatz.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space Product_space.
From Sigma Require Import Sigma OrSigmaGen.
From Utility Require Import Util.
Import VectorNotations.

(** ** Setting

    [F] is the scalar field and [G] the group, a vector space over [F]
    (on Ed25519 in the extracted instance); the field tactic is
    registered for the algebraic lemmas. *)
Section Belenios.

  (** Field [F], group [G] with decidable equalities and the vector-space
      structure [Hvec]. *)
  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Infix "+" := add.

  (** ** Belenios-style Fiat–Shamir verification

      Everything in this section is generic in a vector space [V] over
      [F], so it applies both to [G] (Schnorr statements) and to [G × G]
      (Chaum–Pedersen and ElGamal statements). *)
  Section FiatShamir.

    (** The vector space [V] with addition [vadd], scalar multiplication
        [smul] and decidable equality [Vdec]. *)
    Context
      {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
      {Vdec : forall x y : V, {x = y} + {x <> y}}
      {HV : @vector_space F (@eq F) zero one add mul sub div opp inv
        V (@eq V) vid vopp vadd smul}.

    (** A Belenios proof component: a pair [(challenge, response)]. *)
    Definition proof : Type := (F * F)%type.

    (** The announcement reconstructed from a statement [h = g^x] and a
        proof [(c, s)]: [A = g^s · h^c] (written additively,
        [smul g s + smul h c]).  For an honest proof [s = w − x·c] this is
        the original commitment [g^w]. *)
    Definition reconstruct (g h : V) (c s : F) : V := vadd (smul g s) (smul h c).

    (** Sum of a list of challenges. *)
    Definition sumF (cs : list F) : F := List.fold_right add zero cs.

    (** The reconstructed announcements of a list of statements
        [(g_k, h_k)] with their proofs [(c_k, s_k)]. *)
    Definition announcements (stmts : list (V * V)) (pfs : list proof) : list V :=
      List.map (fun '((g, h), (c, s)) => reconstruct g h c s) (List.combine stmts pfs).

    (** Belenios verification of a proof list for the disjunction of the
        statements [stmts] (one statement is the non-disjunctive case):
        the number of proofs equals the number of statements and
        [Σ_k c_k = H (A_1, …, A_n)] where [A_k] are the reconstructed
        announcements.  The hash [H] is a parameter; it is expected to
        include all statement data, as Belenios does. *)
    Definition fs_verify (H : list V -> F) (stmts : list (V * V)) (pfs : list proof) : bool :=
      (Nat.eqb (length stmts) (length pfs)) &&
      (match Fdec (sumF (List.map fst pfs)) (H (announcements stmts pfs)) with
       | left _ => true | right _ => false end).

    (** For any statement and any [(c, s)], the transcript
        [(reconstruct g h c s; −c; s)] is an accepting Schnorr conversation
        in the library's convention [g^s = A · h^(−c)].  This is pure
        algebra and holds for every [c] and [s]. *)
    Lemma reconstruct_accepting : forall (g h : V) (c s : F),
      @accepting_conversation F V vadd smul Vdec g h
        (mk_sigma _ _ _ [reconstruct g h c s] [opp c] [s]) = true.
    Proof.
      intros *; unfold accepting_conversation; cbn [Vector.hd announcement challenge response].
      (* key identity: g^s = A · h^(−c), since h^c · h^(−c) = h^0 = identity *)
      assert (he : smul g s = vadd (reconstruct g h c s) (smul h (opp c))).
      { unfold reconstruct.
        pose proof (@vector_space_commutative_group F (@eq F) zero one add mul sub div
          opp inv V (@eq V) vid vopp vadd smul HV) as hcg.
        pose proof (@associative V (@eq V) vadd (@monoid_is_associative V (@eq V) vadd vid
          (@group_monoid V (@eq V) vadd vid vopp
            (@commutative_group_group V (@eq V) vadd vid vopp hcg)))) as hassoc.
        pose proof (@right_identity V (@eq V) vadd vid (@monoid_is_right_identity V (@eq V)
          vadd vid (@group_monoid V (@eq V) vadd vid vopp
            (@commutative_group_group V (@eq V) vadd vid vopp hcg)))) as hrid.
        rewrite <-hassoc.
        pose proof (@vector_space_smul_distributive_fadd F (@eq F) zero one add mul
          sub div opp inv V (@eq V) vid vopp vadd smul HV) as hd.
        rewrite <-(hd c (opp c) h).
        assert (ha : c + opp c = zero) by field.
        rewrite ha.
        pose proof (@vector_space_field_zero F (@eq F) zero one add mul
          sub div opp inv V (@eq V) vid vopp vadd smul HV) as hz.
        rewrite (hz h), hrid; reflexivity. }
      (* the accepting check reduces to comparing g^s with itself *)
      simpl. rewrite <-he.
      destruct (Vdec (smul g s) (smul g s)) as [_ | hne]; [reflexivity | contradiction].
    Qed.

    (** Vector version of [announcements], used to state the link with the
        disjunctive composition of [Crypto/OrSigmaGen.v]. *)
    Definition announcements_vec {n : nat} (gs hs : Vector.t V n)
      (cs ss : Vector.t F n) : Vector.t V n :=
      Vector.map2 (fun '(g, h) '(c, s) => reconstruct g h c s)
        (Vector.map2 pair gs hs) (Vector.map2 pair cs ss).

    (** [announcements_vec] agrees with [announcements] after conversion of
        the vectors to lists. *)
    Lemma announcements_vec_to_list : forall (n : nat) (gs hs : Vector.t V n)
      (cs ss : Vector.t F n),
      Vector.to_list (announcements_vec gs hs cs ss) =
      announcements (Vector.to_list (Vector.map2 pair gs hs))
        (Vector.to_list (Vector.map2 pair cs ss)).
    Proof.
      induction n as [| n ih]; intros.
      + rewrite (vector_inv_0 gs), (vector_inv_0 hs), (vector_inv_0 cs), (vector_inv_0 ss).
        reflexivity.
      + destruct (vector_inv_S gs) as (g & gs' & ->).
        destruct (vector_inv_S hs) as (h & hs' & ->).
        destruct (vector_inv_S cs) as (c & cs' & ->).
        destruct (vector_inv_S ss) as (s & ss' & ->).
        cbn; f_equal; apply ih.
    Qed.

    (** The sum of negated challenges is the negated sum. *)
    Lemma sum_opp : forall (n : nat) (cs : Vector.t F n),
      Vector.fold_right add (Vector.map opp cs) zero =
      opp (Vector.fold_right add cs zero).
    Proof.
      induction n as [| n ih]; intros cs.
      + rewrite (vector_inv_0 cs); cbn; field.
      + destruct (vector_inv_S cs) as (c & cs' & ->); cbn.
        rewrite ih; field.
    Qed.

    (** [sumF] on [Vector.to_list cs] is the vector fold of [cs]. *)
    Lemma sumF_to_list : forall (n : nat) (cs : Vector.t F n),
      sumF (Vector.to_list cs) = Vector.fold_right add cs zero.
    Proof.
      induction n as [| n ih]; intros cs.
      + rewrite (vector_inv_0 cs); reflexivity.
      + destruct (vector_inv_S cs) as (c & cs' & ->).
        change (to_list (c :: cs')) with (List.cons c (to_list cs')).
        unfold sumF in *; cbn [List.fold_right Vector.fold_right].
        rewrite ih; reflexivity.
    Qed.

    (** A Belenios disjunctive proof with at least two branches maps to an
        accepting transcript of the generalised OR composition
        ([generalised_or_accepting_conversations]) on the statements
        [(gs_k, hs_k)]: announcements [announcements_vec gs hs cs ss],
        challenge vector [(−Σ c_k) :: (−c_1, …, −c_n)] and responses [ss].
        The proof uses [generalised_or_accepting_conversations_correctness_backward]:
        the challenge-sum condition follows from [sum_opp] and each branch
        from [reconstruct_accepting].  The hypothesis that [fs_verify]
        returns [true] is not needed by the proof; the hash equation is
        what binds the challenges in the random-oracle argument, which is
        not formalised. *)
    Theorem fs_verify_or_accepting : forall (n : nat) (H : list V -> F)
      (gs hs : Vector.t V (2 + n)) (cs ss : Vector.t F (2 + n)),
      fs_verify H (Vector.to_list (Vector.map2 pair gs hs))
        (Vector.to_list (Vector.map2 pair cs ss)) = true ->
      @generalised_or_accepting_conversations F zero add Fdec V vadd smul Vdec (2 + n) gs hs
        (mk_sigma _ _ _ (announcements_vec gs hs cs ss)
          (opp (Vector.fold_right add cs zero) :: Vector.map opp cs) ss) = true.
    Proof.
      intros * hv.
      apply generalised_or_accepting_conversations_correctness_backward.
      split.
      + simpl. rewrite sum_opp; reflexivity.
      + intro f; simpl. unfold announcements_vec.
        erewrite !Vector.nth_map2; try reflexivity.
        erewrite Vector.nth_map; try reflexivity.
        apply reconstruct_accepting.
    Qed.

    (** The single-statement case: a Belenios Schnorr proof maps to an
        accepting conversation of the Schnorr protocol of
        [Crypto/Sigma.v].  As above, the [fs_verify] hypothesis is not
        used. *)
    Theorem fs_verify_schnorr_accepting : forall (H : list V -> F) (g h : V) (c s : F),
      fs_verify H (List.cons ((g, h)) List.nil) (List.cons ((c, s)) List.nil) = true ->
      @accepting_conversation F V vadd smul Vdec g h (mk_sigma _ _ _ [reconstruct g h c s] [opp c] [s]) = true.
    Proof. intros; apply reconstruct_accepting. Qed.

  End FiatShamir.

  (** ** The product group [G × G]

      ElGamal and Chaum–Pedersen statements live in [G × G] with the
      component-wise operations of [Algebra/Product_space.v]. *)

  (** The product group and its operations [gop2], [gpow2], [gid2],
      [ginv2], decidable equality [Gdec2], and the vector-space instance
      [vspace2]. *)
  Definition G2 : Type := (G * G)%type.
  Definition gop2 : G2 -> G2 -> G2 := padd (vadd1 := gop) (vadd2 := gop).
  Definition gpow2 : G2 -> F -> G2 := psmul (smul1 := gpow) (smul2 := gpow).
  Definition gid2 : G2 := pid (vid1 := gid) (vid2 := gid).
  Definition ginv2 : G2 -> G2 := popp (vopp1 := ginv) (vopp2 := ginv).
  Definition Gdec2 : forall x y : G2, {x = y} + {x <> y} := prod_dec Gdec Gdec.
  Instance vspace2 : @vector_space F (@eq F) zero one add mul sub div opp inv
    G2 (@eq G2) gid2 ginv2 gop2 gpow2 := prod_vspace (H1 := Hvec) (H2 := Hvec).

  (** ** Election data *)

  (** An ElGamal ciphertext [(α, β)]. *)
  Definition ciphertext : Type := (G * G)%type.

  (** A homomorphic question: number of answers [nanswers], the minimum
      [qmin] and maximum [qmax] number of selected answers, and whether a
      blank vote is allowed ([qblank]). *)
  Record question : Type := mk_question {
    nanswers : nat;
    qmin : nat;
    qmax : nat;
    qblank : bool
  }.

  (** The answer to one question: one ciphertext per choice (with an extra
      leading blank ciphertext when blank is allowed), one 0/1 proof per
      choice, the overall proof, and the blank proof when applicable. *)
  Record answer : Type := mk_answer {
    choices : list ciphertext;
    individual_proofs : list (list proof);
    overall_proof : list proof;
    blank_proof : option (list proof)
  }.

  (** A ballot: the public credential (verification key), the answers in
      question order and the signature, a Schnorr proof of knowledge of the
      credential's secret key whose hash binds the ballot content. *)
  Record ballot : Type := mk_ballot {
    credential : G;
    answers : list answer;
    signature : proof
  }.

  (** The hash functions used to verify one ballot, supplied by the driver
      as closures over the election fingerprint, the credential and the
      ciphertexts: [h_sig] for the signature, [h_indiv i j] for the 0/1
      proof of choice [j] of question [i], [h_overall i] for the overall
      (or second blank) proof and [h_blank i] for the first blank proof. *)
  Record ballot_hashes : Type := mk_ballot_hashes {
    h_sig : list G -> F;
    h_indiv : nat -> nat -> list G2 -> F;
    h_overall : nat -> list G2 -> F;
    h_blank : nat -> list G2 -> F
  }.

  (** The public election data: generator [g], election public key [y],
      the questions, and the public credentials with their weights. *)
  Record election : Type := mk_election {
    g : G;
    y : G;
    questions : list question;
    credentials : list (G * F)
  }.

  (** ** Ballot verification *)

  (** Embedding of natural numbers into [F] as iterated sums of [one]. *)
  Fixpoint nat_to_F (n : nat) : F :=
    match n with 0 => zero | S n' => one + nat_to_F n' end.

  (** The Chaum–Pedersen statement that [(α, β)] encrypts the group element
      [m]: [(α, β / m) = (g, y)^r], as a pair of bases and a pair of
      targets in [G × G]. *)
  Definition statement (E : election) (c : ciphertext) (m : G) : G2 * G2 :=
    ((g E, y E), (fst c, gop (snd c) (ginv m))).

  (** [g^k] for a natural number [k], the encoding of the vote value [k]. *)
  Definition gpow_nat (E : election) (k : nat) : G := gpow (g E) (nat_to_F k).

  (** Component-wise product of two ciphertexts (homomorphic addition of
      plaintexts). *)
  Definition mul_ciphertext (c d : ciphertext) : ciphertext :=
    (gop (fst c) (fst d), gop (snd c) (snd d)).

  (** Homomorphic sum of a list of ciphertexts, starting from
      [(gid, gid)]. *)
  Definition sum_ciphertexts (cs : list ciphertext) : ciphertext :=
    List.fold_right mul_ciphertext (gid, gid) cs.

  (** Individual proof for choice [j] of question [i]: a two-branch
      disjunction that the ciphertext encrypts [g^0] or [g^1]. *)
  Definition verify_individual (E : election) (hs : ballot_hashes) (i j : nat)
    (c : ciphertext) (pf : list proof) : bool :=
    fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_indiv) i j)
      (List.cons (statement E c gid) (List.cons (statement E c (g E)) List.nil)) pf.

  (** The [mx − mn + 1] branches of an interval proof: the ciphertext
      encrypts [g^(mn + k)] for some [k ∈ 0..(mx − mn)]. *)
  Definition interval_statements (E : election) (c : ciphertext) (mn mx : nat) : list (G2 * G2) :=
    List.map (fun k => statement E c (gpow_nat E (mn + k))) (List.seq 0 (S mx - mn)).

  (** Verification of the answer to question [i].  All individual 0/1
      proofs must verify.  Then:

      - without blank vote: there are exactly [nanswers] choices,
        [qmin ≤ qmax], and the overall proof shows that the sum of the
        choices lies in [qmin..qmax];
      - with blank vote: the choices are [c0 :: cs] with [nanswers + 1]
        entries; the blank proof shows [m0 = 0 ∨ Σ cs = 0] and the overall
        proof shows [m0 = 1 ∨ Σ cs ∈ [qmin, qmax]], so either the vote is
        blank or it is a regular vote;
      - any other combination is rejected. *)
  Definition verify_answer (E : election) (hs : ballot_hashes) (i : nat)
    (q : question) (a : answer) : bool :=
    let n := length a.(choices) in
    (Nat.eqb n (length a.(individual_proofs))) &&
    (forallb (fun x => x)
      (List.map (fun '(j, (c, pf)) => verify_individual E hs i j c pf)
        (List.combine (List.seq 0 n) (List.combine a.(choices) a.(individual_proofs))))) &&
    match q.(qblank), a.(choices), a.(blank_proof) with
    | false, cs, None =>
        (Nat.eqb n q.(nanswers)) &&
        (Nat.leb q.(qmin) q.(qmax)) &&
        fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_overall) i)
          (interval_statements E (sum_ciphertexts cs) q.(qmin) q.(qmax)) a.(overall_proof)
    | true, List.cons c0 cs, Some bpf =>
        let cS := sum_ciphertexts cs in
        (Nat.eqb n (S q.(nanswers))) &&
        (Nat.leb q.(qmin) q.(qmax)) &&
        fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_blank) i)
          (List.cons (statement E c0 gid) (List.cons (statement E cS gid) List.nil)) bpf &&
        fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_overall) i)
          (List.cons (statement E c0 (g E)) (interval_statements E cS q.(qmin) q.(qmax)))
          a.(overall_proof)
    | _, _, _ => false
    end.

  (** The weight associated with a credential in the election data, or
      [None] if the credential is not registered. *)
  Definition credential_weight (E : election) (cr : G) : option F :=
    match List.find (fun '(c, _) => if Gdec c cr then true else false) E.(credentials) with
    | Some (_, w) => Some w
    | None => None
    end.

  (** A ballot is valid when its credential is registered, its signature
      proof verifies, it has one answer per question, and every answer
      verifies.  Revoting and the credential's eligibility are handled at
      tally time by [last_per_credential]. *)
  Definition verify_ballot (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    (match credential_weight E b.(credential) with Some _ => true | None => false end) &&
    fs_verify (V := G) (vadd := gop) (smul := gpow) hs.(h_sig) (List.cons ((g E, b.(credential))) List.nil) (List.cons (b.(signature)) List.nil) &&
    (Nat.eqb (length b.(answers)) (length E.(questions))) &&
    forallb (fun x => x)
      (List.map (fun '(i, (q, a)) => verify_answer E hs i q a)
        (List.combine (List.seq 0 (length E.(questions)))
          (List.combine E.(questions) b.(answers)))).

  (** ** Tally *)

  (** Keeps, for each credential, only the last ballot of the list (in
      casting order): a ballot is dropped when a later ballot in the list
      has the same credential. *)
  Fixpoint last_per_credential (bs : list ballot) : list ballot :=
    match bs with
    | nil => nil
    | List.cons b bs' =>
        let rest := last_per_credential bs' in
        if existsb (fun b' => if Gdec b'.(credential) b.(credential) then true else false) bs'
        then rest else List.cons b rest
    end.

  (** Raises both components of a ciphertext to [w], multiplying the
      plaintext exponent by the weight [w]. *)
  Definition pow_ciphertext (c : ciphertext) (w : F) : ciphertext :=
    (gpow (fst c) w, gpow (snd c) w).

  (** The contribution of a ballot to the tally: every ciphertext raised
      to the ballot's credential weight (weight [zero] if the credential
      is unknown, which cannot happen for valid ballots). *)
  Definition ballot_weighted (E : election) (b : ballot) : list (list ciphertext) :=
    let w := match credential_weight E b.(credential) with Some w => w | None => zero end in
    List.map (fun a => List.map (fun c => pow_ciphertext c w) a.(choices)) b.(answers).

  (** Component-wise product of two tallies (lists of lists of
      ciphertexts, one list per question). *)
  Definition mul_tallies (t u : list (list ciphertext)) : list (list ciphertext) :=
    List.map (fun '(cs, ds) => List.map (fun '(c, d) => mul_ciphertext c d) (List.combine cs ds))
      (List.combine t u).

  (** The empty tally: [(gid, gid)] for every choice of every question
      (with an extra position for blank-enabled questions). *)
  Definition neutral_tally (E : election) : list (list ciphertext) :=
    List.map (fun q => List.repeat (gid, gid)
      (if q.(qblank) then S q.(nanswers) else q.(nanswers))) E.(questions).

  (** The encrypted tally: the product over the given ballots of their
      weighted ciphertexts. *)
  Definition encrypted_tally (E : election) (bs : list ballot) : list (list ciphertext) :=
    List.fold_right (fun b acc => mul_tallies (ballot_weighted E b) acc) (neutral_tally E) bs.

  (** Boolean equality of two tallies, including their shapes. *)
  Definition tally_eqb (t u : list (list ciphertext)) : bool :=
    (Nat.eqb (length t) (length u)) &&
    forallb (fun '(cs, ds) => (Nat.eqb (length cs) (length ds)) &&
      forallb (fun '(c, d) => if Gdec2 c d then true else false) (List.combine cs ds))
      (List.combine t u).

  (** ** Trustees, partial decryptions and result *)

  (** A (single) trustee: public key [X = g^x], proof of knowledge of [x],
      and, for each ciphertext of the tally, a decryption factor
      [f = α^x] with its proof. *)
  Record trustee : Type := mk_trustee {
    public_key : G;
    pok : proof;
    decryption_factors : list (list G);
    decryption_proofs : list (list proof)
  }.

  (** Hash functions for trustee [t]: [h_pok t] for the proof of
      knowledge and [h_dec t] for the decryption proofs.  Supplied by the
      driver. *)
  Record trustee_hashes : Type := mk_trustee_hashes {
    h_pok : nat -> list G -> F;
    h_dec : nat -> list G2 -> F
  }.

  (** Schnorr proof of knowledge of the secret key of trustee [t]. *)
  Definition verify_pok (E : election) (th : trustee_hashes) (t : nat) (tr : trustee) : bool :=
    fs_verify (V := G) (vadd := gop) (smul := gpow) (th.(h_pok) t) (List.cons ((g E, tr.(public_key))) List.nil) (List.cons (tr.(pok)) List.nil).

  (** Decryption-factor proof for ciphertext [(α, β)]: the Chaum–Pedersen
      statement [(X, f) = (g, α)^x], as a Schnorr statement in [G × G]. *)
  Definition verify_factor (E : election) (th : trustee_hashes) (t : nat) (tr : trustee)
    (c : ciphertext) (f : G) (pf : proof) : bool :=
    fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (th.(h_dec) t)
      (List.cons (((g E, fst c), (tr.(public_key), f))) List.nil) (List.cons (pf) List.nil).

  (** A trustee is valid when its proof of knowledge verifies and its
      factors and proofs have the shape of the tally and all decryption
      proofs verify. *)
  Definition verify_trustee (E : election) (th : trustee_hashes)
    (tally : list (list ciphertext)) (t : nat) (tr : trustee) : bool :=
    verify_pok E th t tr &&
    (Nat.eqb (length tally) (length tr.(decryption_factors))) &&
    (Nat.eqb (length tally) (length tr.(decryption_proofs))) &&
    forallb (fun '(cs, (fs, pfs)) =>
      (Nat.eqb (length cs) (length fs)) && (Nat.eqb (length cs) (length pfs)) &&
      forallb (fun '(c, (f, pf)) => verify_factor E th t tr c f pf)
        (List.combine cs (List.combine fs pfs)))
      (List.combine tally (List.combine tr.(decryption_factors) tr.(decryption_proofs))).

  (** The combined decryption factor of each ciphertext: the product of
      all trustees' factors (empty when there are no trustees). *)
  Definition combined_factors (trs : list trustee) : list (list G) :=
    match trs with
    | nil => nil
    | List.cons tr trs' =>
        List.fold_right (fun tr' acc =>
          List.map (fun '(fs, gs) => List.map (fun '(f, h) => gop f h) (List.combine fs gs))
            (List.combine tr'.(decryption_factors) acc))
          tr.(decryption_factors) trs'
    end.

  (** The published result [r] of each ciphertext [(α, β)] with combined
      factor [f] satisfies [g^r = β / f].  The discrete logarithm itself is
      found by the driver; only this equation is checked. *)
  Definition verify_result (E : election) (tally : list (list ciphertext))
    (factors : list (list G)) (result : list (list F)) : bool :=
    (Nat.eqb (length tally) (length factors)) && (Nat.eqb (length tally) (length result)) &&
    forallb (fun '(cs, (fs, rs)) =>
      (Nat.eqb (length cs) (length fs)) && (Nat.eqb (length cs) (length rs)) &&
      forallb (fun '(c, (f, r)) =>
        if Gdec (gpow (g E) r) (gop (snd c) (ginv f)) then true else false)
        (List.combine cs (List.combine fs rs)))
      (List.combine tally (List.combine factors result)).

  (** ** The certificate *)

  (** [partial us vbs inbs]: processed, valid and invalid ballots;
      [finished us vbs inbs b]: final state with the overall result [b]. *)
  Inductive state : Type :=
  | partial : list ballot -> list ballot -> list ballot -> state
  | finished : list ballot -> list ballot -> list ballot -> bool -> state.

  (** The Belenios certificate, parametrised by the election [E] and the
      per-ballot hashes [hs].

      - [ax]: no ballots processed;
      - [cvalid], [cinvalid]: process one ballot according to
        [verify_ballot];
      - [cfinish]: compute the encrypted tally of the last valid ballot of
        each credential (in casting order), compare it with the published
        tally ([bt]), check every trustee ([btr]) and the result against
        the combined factors ([bres]); the final flag is
        [bt && btr && bres].

      Unlike [Backend/HeliosTally.v], there is no explicit permutation
      invariant; the partition follows from the shape of the rules. *)
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
  | cfinish (us vbs inbs : list ballot) (th : trustee_hashes) (trs : list trustee)
      (tally published : list (list ciphertext)) (result : list (list F))
      (bt btr bres : bool) :
      count E hs (partial us vbs inbs) ->
      tally = encrypted_tally E (last_per_credential (List.rev vbs)) ->
      tally_eqb tally published = bt ->
      forallb (fun x => x) (List.map (fun '(t, tr) => verify_trustee E th tally t tr)
        (List.combine (List.seq 0 (length trs)) trs)) = btr ->
      verify_result E tally (combined_factors trs) result = bres ->
      count E hs (finished us vbs inbs (bt && btr && bres)).

  (** Processes the ballot list from its last element to its head and
      builds [count E hs (partial bs vbs inbs)], with [vbs] and [inbs] in
      the order of [bs]. *)
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

  (** The certified verifier: given the ballots in casting order, the
      published encrypted tally, the trustees and the published result,
      it returns the final flag and a certificate
      [count E hs (finished (rev bs) vbs inbs bfinal)].  The ballot list is
      reversed so that [List.rev vbs] is in casting order when the tally
      is computed.  This is the entry point of the extracted verifier. *)
  Definition compute_final_count (E : election) (hs : ballot -> ballot_hashes)
    (th : trustee_hashes) (bs : list ballot) (published : list (list ciphertext))
    (trs : list trustee) (result : list (list F)) :
    existsT (vbs inbs : list ballot) (bfinal : bool),
      count E hs (finished (List.rev bs) vbs inbs bfinal).
  Proof.
    destruct (compute_final_tally E hs (List.rev bs)) as (vbs & inbs & c).
    set (tally := encrypted_tally E (last_per_credential (List.rev vbs))).
    exists vbs, inbs,
      (tally_eqb tally published &&
       forallb (fun x => x) (List.map (fun '(t, tr) => verify_trustee E th tally t tr)
         (List.combine (List.seq 0 (length trs)) trs)) &&
       verify_result E tally (combined_factors trs) result).
    exact (cfinish E hs (List.rev bs) vbs inbs th trs tally published result _ _ _ c
      eq_refl eq_refl eq_refl eq_refl).
  Defined.

End Belenios.
