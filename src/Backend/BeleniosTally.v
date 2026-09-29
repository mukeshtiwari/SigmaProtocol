(* A certified verifier for Belenios elections (specification version 1,
   as implemented by Belenios 3.x), for homomorphic questions, with or
   without blank votes, weighted credentials, and "Single" trustees.

   Belenios stores each non-interactive proof as (challenge, response) and
   the verifier reconstructs the announcement A = g^response · h^challenge
   and checks that the hash of the announcements equals the challenge
   (or the sum of the challenges, for a disjunction). Every proof of
   Belenios is of one of two shapes:

   - a Schnorr proof of h = g^x, for the trustees' proofs of knowledge, the
     ballot signatures, and, in the product group G × G, the decryption
     proofs ((X, factor) = (g, α)^x);
   - a disjunction of such statements in G × G with the common base (g, y):
     each branch says (α, β / m) = (g, y)^r for a ciphertext (α, β) and a
     message m. This covers the individual 0/1 proofs, the overall
     interval proof, and the two proofs of possibly-blank votes, whose
     branches talk about different ciphertexts.

   The section [FiatShamir] below defines that verification over any
   vector space and proves that a verified proof is an accepting
   transcript of the library's Schnorr protocol (Crypto/Sigma.v) or Or
   composition (Crypto/OrSigmaGen.v): the announcement is the reconstructed
   one and the challenges are negated, because the library writes the
   response as u + c·x where Belenios writes w − x·c. The hash functions
   are parameters, as everywhere in this development: the driver computes
   them (SHA-256 over Belenios's serialisation) and passes them in. *)

From Stdlib Require Import Utf8 ZArith Vector List Lia Bool
  setoid_ring.Field Psatz.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space Product_space.
From Crypto Require Import Sigma OrSigmaGen.
From Utility Require Import Util.
Import VectorNotations.

Section Belenios.

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

  (* ---------------------------------------------------------------- *)
  (* Belenios-style Fiat-Shamir verification over a vector space V     *)
  (* ---------------------------------------------------------------- *)

  Section FiatShamir.

    Context
      {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
      {Vdec : forall x y : V, {x = y} + {x <> y}}
      {HV : @vector_space F (@eq F) zero one add mul sub div opp inv
        V (@eq V) vid vopp vadd smul}.

    (* a Belenios proof *)
    Definition proof : Type := (F * F)%type.   (* challenge, response *)

    (* the announcement that Belenios reconstructs for the statement
      h = g^x and the proof (c, s) *)
    Definition reconstruct (g h : V) (c s : F) : V := vadd (smul g s) (smul h c).

    Definition sumF (cs : list F) : F := List.fold_right add zero cs.

    (* announcements of a list of statements with their proofs *)
    Definition announcements (stmts : list (V * V)) (pfs : list proof) : list V :=
      List.map (fun '((g, h), (c, s)) => reconstruct g h c s) (List.combine stmts pfs).

    (* Verification of a Belenios proof list for a disjunction of statements:
      the sum of the challenges equals the hash of the reconstructed
      announcements. A single statement is the case of one proof. *)
    Definition fs_verify (H : list V -> F) (stmts : list (V * V)) (pfs : list proof) : bool :=
      (Nat.eqb (length stmts) (length pfs)) &&
      (match Fdec (sumF (List.map fst pfs)) (H (announcements stmts pfs)) with
       | left _ => true | right _ => false end).

    (* ---- link to the library ---- *)

    Lemma reconstruct_accepting : forall (g h : V) (c s : F),
      @accepting_conversation F V vadd smul Vdec g h 
        (mk_sigma _ _ _ [reconstruct g h c s] [opp c] [s]) = true.
    Proof.
      intros *; unfold accepting_conversation; cbn [Vector.hd announcement challenge response].
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
      simpl. rewrite <-he. 
      destruct (Vdec (smul g s) (smul g s)) as [_ | hne]; [reflexivity | contradiction].
    Qed.

    (* vector form of the announcements, for the statement about the
      library's Or composition *)
    Definition announcements_vec {n : nat} (gs hs : Vector.t V n)
      (cs ss : Vector.t F n) : Vector.t V n :=
      Vector.map2 (fun '(g, h) '(c, s) => reconstruct g h c s)
        (Vector.map2 pair gs hs) (Vector.map2 pair cs ss).

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

    Lemma sum_opp : forall (n : nat) (cs : Vector.t F n),
      Vector.fold_right add (Vector.map opp cs) zero =
      opp (Vector.fold_right add cs zero).
    Proof.
      induction n as [| n ih]; intros cs.
      + rewrite (vector_inv_0 cs); cbn; field.
      + destruct (vector_inv_S cs) as (c & cs' & ->); cbn.
        rewrite ih; field.
    Qed.

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

    (* A verified Belenios disjunction (at least two branches) is an
      accepting transcript of the library's Or composition, with the
      reconstructed announcements and negated challenges. *)
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

    (* A verified single Belenios proof is an accepting transcript of the
      library's Schnorr protocol. *)
    Theorem fs_verify_schnorr_accepting : forall (H : list V -> F) (g h : V) (c s : F),
      fs_verify H (List.cons ((g, h)) List.nil) (List.cons ((c, s)) List.nil) = true ->
      @accepting_conversation F V vadd smul Vdec g h (mk_sigma _ _ _ [reconstruct g h c s] [opp c] [s]) = true.
    Proof. intros; apply reconstruct_accepting. Qed.

  End FiatShamir.

  (* ---------------------------------------------------------------- *)
  (* The product group G × G                                          *)
  (* ---------------------------------------------------------------- *)

  Definition G2 : Type := (G * G)%type.
  Definition gop2 : G2 -> G2 -> G2 := padd (vadd1 := gop) (vadd2 := gop).
  Definition gpow2 : G2 -> F -> G2 := psmul (smul1 := gpow) (smul2 := gpow).
  Definition gid2 : G2 := pid (vid1 := gid) (vid2 := gid).
  Definition ginv2 : G2 -> G2 := popp (vopp1 := ginv) (vopp2 := ginv).
  Definition Gdec2 : forall x y : G2, {x = y} + {x <> y} := prod_dec Gdec Gdec.
  Instance vspace2 : @vector_space F (@eq F) zero one add mul sub div opp inv
    G2 (@eq G2) gid2 ginv2 gop2 gpow2 := prod_vspace (H1 := Hvec) (H2 := Hvec).

  (* ---------------------------------------------------------------- *)
  (* Election data                                                     *)
  (* ---------------------------------------------------------------- *)

  Definition ciphertext : Type := (G * G)%type.   (* alpha, beta *)

  Record question : Type := mk_question {
    nanswers : nat;
    qmin : nat;
    qmax : nat;
    qblank : bool
  }.

  Record answer : Type := mk_answer {
    choices : list ciphertext;
    individual_proofs : list (list proof);
    overall_proof : list proof;
    blank_proof : option (list proof)
  }.

  Record ballot : Type := mk_ballot {
    credential : G;
    answers : list answer;
    signature : proof
  }.

  (* The hash functions of one ballot, as Belenios computes them from the
    election fingerprint, the credential, the ciphertexts and the
    announcements. They are supplied by the driver. *)
  Record ballot_hashes : Type := mk_ballot_hashes {
    h_sig : list G -> F;                       (* H_signature(hash, A) *)
    h_indiv : nat -> nat -> list G2 -> F;      (* H_iprove(S0, α, β, A0, B0, A1, B1) for question i, choice j *)
    h_overall : nat -> list G2 -> F;           (* H_iprove(S, αΣ, βΣ, ...) or H_bproof1(S, ...) for question i *)
    h_blank : nat -> list G2 -> F              (* H_bproof0(S, A0, B0, AΣ, BΣ) for question i *)
  }.

  Record election : Type := mk_election {
    g : G;                                   (* group generator *)
    y : G;                                   (* election public key *)
    questions : list question;
    credentials : list (G * F)               (* public credentials with weights *)
  }.

  (* ---------------------------------------------------------------- *)
  (* Ballot verification                                               *)
  (* ---------------------------------------------------------------- *)

  Fixpoint nat_to_F (n : nat) : F :=
    match n with 0 => zero | S n' => one + nat_to_F n' end.

  (* the statement (α, β / m) = (g, y)^r, for a message m *)
  Definition statement (E : election) (c : ciphertext) (m : G) : G2 * G2 :=
    ((g E, y E), (fst c, gop (snd c) (ginv m))).

  Definition gpow_nat (E : election) (k : nat) : G := gpow (g E) (nat_to_F k).

  Definition mul_ciphertext (c d : ciphertext) : ciphertext :=
    (gop (fst c) (fst d), gop (snd c) (snd d)).

  Definition sum_ciphertexts (cs : list ciphertext) : ciphertext :=
    List.fold_right mul_ciphertext (gid, gid) cs.

  (* individual proof of choice j of question i: (α, β) encrypts 0 or 1 *)
  Definition verify_individual (E : election) (hs : ballot_hashes) (i j : nat)
    (c : ciphertext) (pf : list proof) : bool :=
    fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_indiv) i j)
      (List.cons (statement E c gid) (List.cons (statement E c (g E)) List.nil)) pf.

  (* the k = max - min + 1 branches of an interval proof on a ciphertext *)
  Definition interval_statements (E : election) (c : ciphertext) (mn mx : nat) : list (G2 * G2) :=
    List.map (fun k => statement E c (gpow_nat E (mn + k))) (List.seq 0 (S mx - mn)).

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
        (* blank_proof: m0 = 0 ∨ mΣ = 0 *)
        fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_blank) i)
          (List.cons (statement E c0 gid) (List.cons (statement E cS gid) List.nil)) bpf &&
        (* overall_proof: m0 = 1 ∨ mΣ ∈ [min, max] *)
        fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (hs.(h_overall) i)
          (List.cons (statement E c0 (g E)) (interval_statements E cS q.(qmin) q.(qmax)))
          a.(overall_proof)
    | _, _, _ => false
    end.

  Definition credential_weight (E : election) (cr : G) : option F :=
    match List.find (fun '(c, _) => if Gdec c cr then true else false) E.(credentials) with
    | Some (_, w) => Some w
    | None => None
    end.

  Definition verify_ballot (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    (match credential_weight E b.(credential) with Some _ => true | None => false end) &&
    fs_verify (V := G) (vadd := gop) (smul := gpow) hs.(h_sig) (List.cons ((g E, b.(credential))) List.nil) (List.cons (b.(signature)) List.nil) &&
    (Nat.eqb (length b.(answers)) (length E.(questions))) &&
    forallb (fun x => x)
      (List.map (fun '(i, (q, a)) => verify_answer E hs i q a)
        (List.combine (List.seq 0 (length E.(questions)))
          (List.combine E.(questions) b.(answers)))).

  (* ---------------------------------------------------------------- *)
  (* Tally                                                             *)
  (* ---------------------------------------------------------------- *)

  (* Belenios tallies the last ballot cast with each credential. *)
  Fixpoint last_per_credential (bs : list ballot) : list ballot :=
    match bs with
    | nil => nil
    | List.cons b bs' =>
        let rest := last_per_credential bs' in
        if existsb (fun b' => if Gdec b'.(credential) b.(credential) then true else false) bs'
        then rest else List.cons b rest
    end.

  Definition pow_ciphertext (c : ciphertext) (w : F) : ciphertext :=
    (gpow (fst c) w, gpow (snd c) w).

  (* the encrypted tally: per question, the product over the tallied
    ballots of the ciphertexts raised to the ballot's weight *)
  Definition ballot_weighted (E : election) (b : ballot) : list (list ciphertext) :=
    let w := match credential_weight E b.(credential) with Some w => w | None => zero end in
    List.map (fun a => List.map (fun c => pow_ciphertext c w) a.(choices)) b.(answers).

  Definition mul_tallies (t u : list (list ciphertext)) : list (list ciphertext) :=
    List.map (fun '(cs, ds) => List.map (fun '(c, d) => mul_ciphertext c d) (List.combine cs ds))
      (List.combine t u).

  Definition neutral_tally (E : election) : list (list ciphertext) :=
    List.map (fun q => List.repeat (gid, gid)
      (if q.(qblank) then S q.(nanswers) else q.(nanswers))) E.(questions).

  Definition encrypted_tally (E : election) (bs : list ballot) : list (list ciphertext) :=
    List.fold_right (fun b acc => mul_tallies (ballot_weighted E b) acc) (neutral_tally E) bs.

  Definition tally_eqb (t u : list (list ciphertext)) : bool :=
    (Nat.eqb (length t) (length u)) &&
    forallb (fun '(cs, ds) => (Nat.eqb (length cs) (length ds)) &&
      forallb (fun '(c, d) => if Gdec2 c d then true else false) (List.combine cs ds))
      (List.combine t u).

  (* ---------------------------------------------------------------- *)
  (* Trustees, decryption, result                                      *)
  (* ---------------------------------------------------------------- *)

  Record trustee : Type := mk_trustee {
    public_key : G;
    pok : proof;
    decryption_factors : list (list G);
    decryption_proofs : list (list proof)
  }.

  Record trustee_hashes : Type := mk_trustee_hashes {
    h_pok : nat -> list G -> F;              (* H_pok(X, A) for trustee t *)
    h_dec : nat -> list G2 -> F              (* H_decrypt(X, A, B) for trustee t *)
  }.

  Definition verify_pok (E : election) (th : trustee_hashes) (t : nat) (tr : trustee) : bool :=
    fs_verify (V := G) (vadd := gop) (smul := gpow) (th.(h_pok) t) (List.cons ((g E, tr.(public_key))) List.nil) (List.cons (tr.(pok)) List.nil).

  (* decryption factor f of ciphertext (α, _): (X, f) = (g, α)^x *)
  Definition verify_factor (E : election) (th : trustee_hashes) (t : nat) (tr : trustee)
    (c : ciphertext) (f : G) (pf : proof) : bool :=
    fs_verify (V := G2) (vadd := gop2) (smul := gpow2) (th.(h_dec) t)
      (List.cons (((g E, fst c), (tr.(public_key), f))) List.nil) (List.cons (pf) List.nil).

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

  (* the combined decryption factor of each ciphertext: the product of
    the trustees' factors *)
  Definition combined_factors (trs : list trustee) : list (list G) :=
    match trs with
    | nil => nil
    | List.cons tr trs' =>
        List.fold_right (fun tr' acc =>
          List.map (fun '(fs, gs) => List.map (fun '(f, h) => gop f h) (List.combine fs gs))
            (List.combine tr'.(decryption_factors) acc))
          tr.(decryption_factors) trs'
    end.

  (* result r of a ciphertext (α, β) with combined factor f: g^r = β / f *)
  Definition verify_result (E : election) (tally : list (list ciphertext))
    (factors : list (list G)) (result : list (list F)) : bool :=
    (Nat.eqb (length tally) (length factors)) && (Nat.eqb (length tally) (length result)) &&
    forallb (fun '(cs, (fs, rs)) =>
      (Nat.eqb (length cs) (length fs)) && (Nat.eqb (length cs) (length rs)) &&
      forallb (fun '(c, (f, r)) =>
        if Gdec (gpow (g E) r) (gop (snd c) (ginv f)) then true else false)
        (List.combine cs (List.combine fs rs)))
      (List.combine tally (List.combine factors result)).

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
  | cfinish (us vbs inbs : list ballot) (th : trustee_hashes) (trs : list trustee)
      (tally published : list (list ciphertext)) (result : list (list F))
      (bt btr bres : bool) :
      count E hs (partial us vbs inbs) ->
      (* the encrypted tally of the last ballot of each credential, in
        casting order, is the published one *)
      tally = encrypted_tally E (last_per_credential (List.rev vbs)) ->
      tally_eqb tally published = bt ->
      (* every trustee's proof of knowledge and decryption proofs *)
      forallb (fun x => x) (List.map (fun '(t, tr) => verify_trustee E th tally t tr)
        (List.combine (List.seq 0 (length trs)) trs)) = btr ->
      (* the result decrypts the tally with the combined factors *)
      verify_result E tally (combined_factors trs) result = bres ->
      count E hs (finished us vbs inbs (bt && btr && bres)).

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

  (* The certified verifier: the ballots in casting order, the published
    encrypted tally, the trustees with their partial decryptions, and
    the published result; returns the certificate. *)
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
