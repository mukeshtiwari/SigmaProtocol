(** * Certified tally for approval ballots (Helios-style homomorphic tally) *)

(** This file is the back end of the approval-voting pipeline whose front end
    (ballot encryption and per-ballot proofs) lives in [Frontend/Approval.v].
    It formalises the tallying authority of a homomorphic ElGamal election in
    the style of Helios: every ballot is a vector of exponential ElGamal
    ciphertexts [(g^r, g^m · h^r)], one per candidate, each carrying a
    disjunctive Chaum–Pedersen proof that it encrypts 0 or 1, plus an overall
    disjunctive proof on the homomorphic product of the ciphertexts that the
    total number of approvals lies in [0..k].

    The tally is described as a _certificate_: the inductive family [count]
    is indexed by a [state] and each constructor is one auditable step.

    - [ax] starts with the all-identity encrypted tally;
    - [cvalid] accepts a ballot whose proofs verify and multiplies its
      ciphertexts component-wise into the running encrypted tally;
    - [cinvalid] discards a ballot whose proofs do not verify;
    - [cfinish] publishes the plaintext tally [pt], the decrypted group
      elements [ds = g^pt], and one Chaum–Pedersen decryption proof per
      candidate, and records in a boolean whether [g^pt_i = ds_i] holds for
      every candidate.

    Every [count] derivation also carries the invariant that the processed
    ballots are a permutation of valid ++ invalid ballots, so no ballot is
    dropped or duplicated.

    Main results:

    - [compute_final_tally] walks a ballot list and builds the partial
      certificate (it is a [Defined] term and is extracted);
    - [compute_final_count] decrypts the final encrypted tally with the
      secret key [x], recovers each count with a caller-supplied discrete
      logarithm search, and produces honest decryption proofs; the existence
      of the [cfinish] step is justified by
      [decryption_proof_accepting_conversations_vector_completeness]
      from [Crypto/DecProof.v];
    - [finished_true_correct] unpacks a certificate whose final flag is
      [true]: the ballot partition is a permutation, each published count is
      the discrete logarithm of the corresponding decrypted element, and the
      decryption proofs are accepted.

    What is _not_ established here: the decryption proofs are interactive
    Sigma-protocol transcripts whose challenges [cs] are supplied by the
    caller (no Fiat–Shamir hashing in this file); soundness of those proofs
    and the correctness of the decrypted tally with respect to the ballot
    plaintexts are inherited from [Crypto/DecProof.v] and [Crypto/Elgamal.v]
    rather than restated as one end-to-end theorem; and the discrete
    logarithm search is an untrusted parameter whose output is only checked
    via the boolean flag.  The file is instantiated in [Examples/TallyIns.v]
    and extracted to OCaml through [src/Extraction/Tallylib]. *)
From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.
From Crypto Require Import
  Elgamal EncProof Sigma DecProof.
From Frontend Require Import
  Approval.

Import VectorNotations.

(** ** Generic setting

    The development is parametric in a field [F] of exponents (in practice
    [Z_q]) and a group [G] of prime order (in practice a subgroup of
    [Z_p^*]) forming a vector space over [F]; both carry decidable equality
    so that the checks are executable. *)
Section Tally.

  (** The exponent field [F] with its operations and decidable equality. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] written multiplicatively: identity [gid], inverse
      [ginv], operation [gop] and exponentiation [gpow], with decidable
      equality. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** Ballots, tally states and the certificate *)

  (** [n] is the number of candidates; [g] is the generator and [h = g^x]
      the election public key. *)
  Section Defs.

    Context {n : nat}
      (g h : G).

    (** A ballot: a vector of [n] triples (ciphertext, 0/1 encryption proof)
        together with the overall proof, a disjunctive Chaum–Pedersen proof
        with [S n] branches showing that the product of the ciphertexts
        encrypts one of [g^0, …, g^n] (see [verify_overall_proof] in
        [Frontend/Approval.v]). *)
    Definition ballot : Type :=
      (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n *
       @Sigma.sigma_proto F (G * G) (S n) (S (S n)) (S n))%type.

    (** Ballot validity: both the per-candidate 0/1 proofs and the overall
        proof must be accepting conversations; this is [verify_ballot] from
        [Frontend/Approval.v] specialised to the current parameters.  Only
        the Sigma-protocol verification equations are checked; whether the
        challenges were derived honestly is outside this check. *)
    Definition verify_ballot_full (b : ballot) : bool :=
      @verify_ballot F zero one add Fdec G gid ginv gop gpow Gdec n g h b.

    (** Tally states.  [partial us vbs inbs ms] records the ballots processed
        so far [us], the accepted ballots [vbs], the rejected ballots [inbs]
        and the running encrypted tally [ms] (one ciphertext per candidate).
        [finished us vbs inbs pt b] additionally records the published
        plaintext tally [pt] and the result [b] of checking it against the
        decrypted group elements. *)
    Inductive state : Type :=
    | partial : list (ballot) ->
      list (ballot) ->
      list (ballot) ->
      Vector.t (G * G) n -> state
    | finished : list (ballot) ->
      list (ballot) ->
      list (ballot) ->
      Vector.t F n -> bool -> state.

    (** The tally certificate.  A value of type [count s] is a derivation
        that state [s] is reachable by the rules below; the extracted proof
        term is the audit trail.

        - [ax]: start with an encrypted tally in which every component is
          the trivial ciphertext [(gid, gid)], an encryption of [0];
        - [cvalid]: if [u] verifies, prepend it to processed and accepted
          ballots and multiply its ciphertexts into the encrypted tally;
        - [cinvalid]: if [u] fails to verify, prepend it to processed and
          rejected ballots and leave the tally unchanged;
        - [cfinish]: given decrypted elements [ds], decryption proofs [pf]
          that each [ds_i] is the decryption of [ms_i] under [h], and a
          plaintext tally [pt], set [b] to whether [g^pt_i = ds_i] for all
          [i].

        Each step also requires [Permutation us (vbs ++ inbs)] for the
        predecessor state. *)
    Inductive count : state -> Type :=
    | ax  (ms : Vector.t (G * G) n) :
      (∀ (i : Fin.t n), Vector.nth ms i = (gid, gid)) ->
      count (partial (@List.nil (ballot))
        (@List.nil (ballot))
        (@List.nil (ballot)) ms)
    | cvalid
      (u : ballot)
      (us vbs inbs : list (ballot))
      (ms nms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) ->
      Permutation us (vbs ++ inbs) ->
      verify_ballot_full u = true ->
      nms = @mul_encrypted_ballots G gop _ ms (Vector.map fst (fst u)) ->
      count (partial (@List.cons _ u us) (@List.cons _ u vbs) inbs nms)
    | cinvalid
      (u : ballot)
      (us vbs inbs : list (ballot))
      (ms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) ->
      Permutation us (vbs ++ inbs) ->
      verify_ballot_full u = false ->
      count (partial (@List.cons _ u us) vbs (@List.cons _ u inbs) ms)
    | cfinish
      (us vbs inbs : list (ballot))
      (ms : Vector.t (G * G) n) (ds : Vector.t G n)
      (pf : Vector.t (@sigma_proto F G 2 1 1) n)
      (pt : Vector.t F n) (b : bool) :
      count (partial us vbs inbs ms) ->
      Permutation us (vbs ++ inbs) ->
      vector_forallb (fun u => u)
        (zip_with (fun u v => match Gdec (g ^ u) v with
          | left _ => true
          | right _ => false
          end) pt ds) = b ->
      @decryption_proof_accepting_conversations_vector F G ginv gop gpow
        Gdec _ g h ms ds pf = true ->
      count (finished us vbs inbs pt b).

    (** From here on [G] is assumed to be a vector space over [F], which
        supplies the group and field laws used in the proofs; the field
        tactic is registered for [F]. *)
    Context
      {Hvec: @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.

    Add Field field : (@field_theory_for_stdlib_tactic F
       eq zero one opp add mul sub inv div vector_space_field).

    (** Decryption identity, component-wise: if [g^x = h] then for every
        ciphertext [(c₁, c₂)] in [ms], [c₁^x = c₂ · (dec (c₁, c₂))⁻¹], where
        [dec (c₁, c₂) = c₂ · (c₁^x)⁻¹] is computed by [decrypted_ballot].  This
        is exactly the statement the Chaum–Pedersen decryption proof needs.
        The hypothesis [g^x = h] is not needed for the identity itself. *)
    Theorem  compute_final_tally_aux2 : ∀ (m : nat) (f : Fin.t m)
      (ms : Vector.t (G * G) m) (x : F), g^x = h ->
      fst ms[@f] ^ x = gop (snd ms[@f])
        (ginv (@decrypted_ballot F G ginv gop gpow x _ ms)[@f]).
    Proof.
      induction m as [|m ihm].
      +
        intros *. refine match f with end.
      +
        intros * ha.
        destruct (vector_inv_S ms) as ((c₁, c₂) & mst & hb).
        destruct (fin_inv_S _ f) as [f' | (f' & hc)].
        ++
          subst; cbn.
          (* head case: unfold dec and cancel c₂ using inverse laws *)
          remember (ginv (c₁ ^ x)) as ct.
          assert (ha : (ginv (gop c₂ ct)) =
            gop (ginv ct) (ginv c₂)).
          rewrite group_inv_flip. reflexivity.
          rewrite ha; clear ha.
          assert (ha : (gop (ginv ct) (ginv c₂)) = gop (ginv c₂) (ginv ct)).
          rewrite commutative. reflexivity.
          rewrite ha; clear ha.
          assert (Hwt : (gop c₂ (gop (ginv c₂) (ginv ct))) = (ginv ct)).
          {
            rewrite associative.
            rewrite group_is_right_inverse,
            monoid_is_left_idenity;
            reflexivity.
          }
          rewrite Hwt; clear Hwt. subst.
          rewrite group_inv_inv.
          reflexivity.
        ++
          subst; cbn.
          (* tail case: induction hypothesis *)
          eapply ihm.
          reflexivity.
    Qed.

    (** Builds the partial tally certificate for a list of ballots [bs].
        By structural recursion on [bs] it returns the accepted ballots
        [vbs], the rejected ballots [inbs], the encrypted tally [ms], a
        derivation of [count (partial bs vbs inbs ms)] and the permutation
        fact.  Ballots are processed from the end of the list towards the
        front, so the head ballot is the last one added.  The secret key [x]
        and the hypothesis [g^x = h] are in the signature but not used in
        this phase. *)
    Definition compute_final_tally (x : F) :
      g^x = h ->
      ∀ (bs : list (ballot)),
      existsT (vbs inbs :  list (ballot))
        (ms : Vector.t (G * G) n), (count (partial bs vbs inbs ms) *
        Permutation bs (vbs ++ inbs))%type.
    Proof.
      intro ha.
      refine(fix fn (bs : list (ballot)) {struct bs} :=
        match bs with
        | @List.nil _ => _
        | @List.cons _ bh bt => _
        end).
      (* empty list: start from the all-identity encrypted tally *)
      +
        set (ms := repeat_ntimes n (gid, gid)).
        exists (@List.nil (ballot)),
        (@List.nil (ballot)), ms.
        refine(pair (ax ms _) _).
        ++
          intros *.
          unfold ms.
          eapply repeat_ntimes_correct.
        ++
          reflexivity.
      +
        (* non-empty list: branch on the verification result of the head *)
        refine
          (match verify_ballot_full bh as v return
          verify_ballot_full bh = v -> _
          with
          | true => fun hv => _
          | false => fun hv => _
          end eq_refl).
        ++
          destruct (fn bt) as (vbs & inbs &  ms & hb & hc).
          exists (@List.cons _ bh vbs), inbs,
            (@mul_encrypted_ballots G gop _ ms (Vector.map fst (fst bh))).
          refine(pair _ _ ).
          *
            eapply cvalid. exact hb.
            exact hc.
            exact hv. reflexivity.
          *
            cbn.
            eapply Permutation_cons;
            [exact eq_refl | exact hc].
        ++
          destruct (fn bt) as (vbs & inbs &  ms & hb & hc).
          exists vbs, (@List.cons _ bh inbs), ms.
          refine(pair _ _).
          *
            eapply cinvalid; assumption.
          *
            cbn.
            eapply Permutation_trans with (l' := List.cons bh (vbs ++ inbs)).
            eapply Permutation_cons; [exact eq_refl | exact hc].
            eapply Permutation_middle.
    Defined.

    (** A discrete logarithm search [discrete_logarithm_search g y], supplied
        by the caller (for example a bounded linear search in the extracted
        code).  It is untrusted: its results are only accepted if
        [g^pt_i = ds_i], which is recorded in the final boolean flag. *)
    Variable (discrete_logarithm_search : G -> G -> F).

    (** End-to-end tally: from the secret key [x] with [g^x = h], commitment
        randomness [us] and challenges [cs] for the decryption proofs, and a
        ballot list [bs], produce a finished certificate
        [count (finished bs vbs inbs pt b)].  It computes the encrypted
        tally with [compute_final_tally], decrypts it, runs the discrete
        logarithm search, builds honest Chaum–Pedersen decryption proofs and
        sets the flag [b].  The obligation that the honest proofs are
        accepted is discharged by
        [decryption_proof_accepting_conversations_vector_completeness] with
        [compute_final_tally_aux2]. *)
    Definition compute_final_count (x : F) (us cs : Vector.t F n) :
      g^x = h ->
      ∀ (bs : list (ballot)),
      existsT (vbs inbs : list (ballot)) (pt : Vector.t F n) (b : bool),
        count (finished bs vbs inbs pt b).
    Proof.
      intros * ha *.
      destruct (compute_final_tally x ha bs) as (vbs & inbs & ms & hb & hc).
      set (ds := @decrypted_ballot F G ginv gop gpow x _ ms).
      set (pt := (map (fun hy => discrete_logarithm_search g hy) ds)).
      set (pf := @construct_decryption_proof_elgamal_real_vector F add mul G gpow
          _ x g ms us cs).
      set (b := vector_forallb (fun u => u)
        (zip_with (fun u v => match Gdec (g ^ u) v with
          | left _ => true
          | right _ => false
          end) pt ds)).
      exists vbs, inbs, pt, b.
      refine(cfinish bs vbs inbs ms ds pf pt b hb hc eq_refl _).
      eapply decryption_proof_accepting_conversations_vector_completeness;
      [exact ha | ].
      intro f.
      unfold ds.
      eapply compute_final_tally_aux2; exact ha.
    Defined.

    (** Correctness of a successful certificate: if
        [count (finished us vbs inbs pt true)] holds, then there exist an
        encrypted tally [ms], decrypted elements [ds] and decryption proofs
        [pf] such that [us] is a permutation of [vbs ++ inbs], [g^pt_i = ds_i]
        for every candidate [i], and the decryption proofs of [ds] against
        [ms] are accepted.  The proof inverts the [cfinish] step and
        unfolds the boolean flag with [vector_forallb_correct]. *)
    Theorem finished_true_correct :
      forall (us vbs inbs : list ballot) (pt : Vector.t F n),
      count (finished us vbs inbs pt true) ->
      ∃ (ms : Vector.t (G * G) n) (ds : Vector.t G n)
        (pf : Vector.t (@sigma_proto F G 2 1 1) n),
        Permutation us (vbs ++ inbs) ∧
        (∀ (i : Fin.t n), g ^ (Vector.nth pt i) = Vector.nth ds i) ∧
        @decryption_proof_accepting_conversations_vector F G ginv gop gpow
          Gdec _ g h ms ds pf = true.
    Proof.
      intros * hc.
      inversion hc as [| | | us' vbs' inbs' ms ds pf pt' b hcount hperm hb hdec];
      subst.
      exists ms, ds, pf.
      refine (conj hperm (conj _ hdec)).
      intro i.
      rewrite vector_forallb_correct in hb.
      specialize (hb i).
      rewrite nth_zip_with in hb.
      destruct (Gdec (g ^ pt[@i]) ds[@i]) as [he | he];
      [exact he | inversion hb].
    Qed.

  End Defs.

End Tally.
