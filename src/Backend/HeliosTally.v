(** * Helios tally verifier *)

(** This file formalises the verification of a published Helios election
    (Adida 2008), using its published JSON data, as a tally certificate.  Helios
    uses exponential ElGamal over a Schnorr subgroup of [Z_p^*] with a
    threshold-free distributed key: each trustee [i] holds [s_i] and
    publishes [y_i = g^(s_i)], and the election key is [h = ∏ y_i].  A
    ballot has one ciphertext [(α, β) = (g^r, g^v · h^r)] per answer, each
    with a disjunctive Chaum–Pedersen proof that [v ∈ {0, 1}].  The
    encrypted tally is the component-wise product of the ciphertexts of the
    valid ballots; each trustee publishes partial decryption factors
    [d_i = α^(s_i)] with Chaum–Pedersen proofs, and the plaintext tally
    [pt] is checked against [β · (∏ d_i)⁻¹ = g^pt].

    The verifier is phrased as an inductive certificate [count] over tally
    [state]s, in the same style as [Backend/Tally.v]:

    - [ax], [cvalid], [cinvalid] process ballots one at a time, keeping the
      invariant that all processed ballots are a permutation of the valid
      and the invalid ones;
    - [finish] checks the trustees' work and the published tally and
      records the conjunction of all checks as a boolean.

    [compute_final_tally] and [compute_final_count] build such a certificate
    for real data; they are [Defined] and extracted to OCaml through
    [src/Extraction/HeliosTallylib], with concrete parameters (the 2048-bit
    Helios group with a 256-bit [q]) from [Examples/HeliosTallyIns.v].

    What is checked: each per-answer 0/1 proof (the Sigma verification
    equations and that the overall challenge equals the sum of the branch
    challenges), the trustees' decryption proofs (that [log_g y_i = log_α d_i]
    for every candidate), the trustees' Schnorr proofs of knowledge of [s_i],
    that [h] is the product of the trustee keys, and [g^pt = decrypted tally].
    The soundness of these checks rests on special soundness of the
    disjunctive and Chaum–Pedersen protocols proved in [Crypto/EncProof.v],
    [Crypto/ChaumPedersen.v] and [Crypto/DistElgamal.v]
    ([decrypt_ballot_value] and its correctness lemmas).

    What is _not_ checked: Helios computes all challenges by Fiat–Shamir
    (a hash of the commitments); here challenges are read from the
    published data and not recomputed, so only the algebraic verification
    equations are checked.  The Helios overall (max/min) proof on a ballot
    is not part of the ballot type and is not checked.  The string fields
    (timestamps, hashes, UUIDs) are carried but not checked, the group
    parameters [(g, p, q)] stored with each trustee key are ignored, and
    group membership of ciphertext components is not tested.  No theorem
    relating a [true] flag to the plaintext tally is proved in this file. *)
From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin Permutation
  String.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import Util.
From Crypto Require Import
  Elgamal EncProof Sigma
  DistElgamal ChaumPedersen.
From Frontend Require Import Approval.
Import VectorNotations.

(** ** Generic setting

    The field [F] of exponents and the prime-order group [G] are abstract;
    both have decidable equality so the checks compute. *)
Section HeliosTally.
  (** The exponent field [F] with decidable equality [Fdec]. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G], written multiplicatively, with exponentiation [gpow]
      and decidable equality [Gdec]. *)
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

  (** ** Helios data: ballots and trustees *)

  (** [n] is the number of answers (candidates) in the question, [1 + m]
      is the number of trustees, [g] is the generator and [h] the joint
      election public key. *)
  Section Defs.

    Context {n m : nat}
     (g h : G).

    (** A Helios cast ballot, flattened into a tuple so that it extracts to
        a plain OCaml tuple.  The fields are, in order: the cast-at
        timestamp, the [n] ciphertexts, the [n] disjunctive 0/1 proofs
        (two branches each, as Sigma transcripts over pairs), the election
        hash, the election UUID, the vote hash, the voter hash and the voter
        UUID.  Only the ciphertexts and the proofs are used by the
        verifier. *)
    Definition ballot : Type := (string * Vector.t (G * G) n *
      Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n *
      string * string * string * string * string)%type.

    (** Projection of the ciphertext vector of a ballot. *)
    Definition get_ballot_ciphertext (b : ballot) : Vector.t (G * G) n :=
      match b with
      | (_, c, _, _, _, _, _, _) => c
      end.

    (** Projection of the vector of per-answer 0/1 proofs of a ballot. *)
    Definition get_ballot_encryption_proof (b : ballot) :
      Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n :=
      match b with
      | (_, _, c, _, _, _, _, _) => c
      end.

    (** A Helios trustee record, flattened into a tuple: the decryption
        factors [d_j = α_j^(s_i)] for each answer [j], the corresponding
        Chaum–Pedersen decryption proofs, the trustee e-mail, a Schnorr
        proof of knowledge of [s_i], the public key [(g, p, q, y_i)], the
        public-key hash and the trustee UUID. *)
    Definition tallier : Type := (Vector.t G n *
      Vector.t (@Sigma.sigma_proto F G 2 1 1) n *
      string * (@Sigma.sigma_proto F G 1 1 1) *
      (G * F * F * G) * string * string)%type.

    (** Projection of the decryption factors of a trustee. *)
    Definition get_tallier_decryption_factor (t : tallier) : Vector.t G n :=
      match t with
      | (d, _, _, _, _, _, _) => d
      end.

    (** Projection of the decryption proofs of a trustee. *)
    Definition get_tallier_decryption_proof (t : tallier) :
      Vector.t (@Sigma.sigma_proto F G 2 1 1) n :=
      match t with
      | (_, p, _, _, _, _, _) => p
      end.

    (** Projection of the Schnorr proof of knowledge of the trustee's secret
        key. *)
    Definition get_tallier_pok (t : tallier) :
      @Sigma.sigma_proto F G 1 1 1 :=
      match t with
      | (_, _, _, p, _, _, _) => p
      end.

    (** Projection of the trustee public key [(g, p, q, y)]; only [y] is
        used. *)
    Definition get_tallier_public_key (t : tallier) :
      (G * F * F * G) :=
      match t with
      | (_, _, _, _, pk, _, _) => pk
      end.

    (** ** Tally states and certificate *)

    (** [partial us vbs inbs ms]: processed, valid and invalid ballots and
        the running encrypted tally [ms].  [finished us vbs inbs ts pt b]:
        the final state with the trustee records [ts], the published
        plaintext tally [pt] and the overall verification result [b]. *)
    Inductive state : Type :=
    | partial : list ballot ->  list ballot -> list ballot ->
      Vector.t (G * G) n -> state
    | finished : list ballot ->  list ballot -> list ballot ->
      Vector.t tallier (1 + m) -> Vector.t F n -> bool -> state.

    (** The Helios tally certificate.  [count s] is a derivation that the
        state [s] was reached by the following steps.

        - [ax]: the encrypted tally starts as [(gid, gid)] in every
          position (an encryption of zero) with no ballots;
        - [cvalid]: a ballot whose 0/1 proofs all verify (via
          [verify_encryption_ballot_proof] from [Frontend/Approval.v]) is
          recorded as valid and its ciphertexts are multiplied into the
          tally;
        - [cinvalid]: a ballot whose proofs fail is recorded as invalid and
          the tally is unchanged;
        - [finish]: from the final encrypted tally [ms] and trustee records
          [ts], compute [ds = decrypt_ballot_value ms (factors of ts)], that
          is [β_j · (∏_i d_(i,j))⁻¹], and the four flags [bptds]
          ([g^pt_j = ds_j] for all [j]), [bdec] (every trustee's
          Chaum–Pedersen proof that [log_g y_i = log_(α_j) d_(i,j)] is an
          accepting conversation), [bpok] (every trustee's Schnorr proof of
          knowledge of [log_g y_i] is accepting) and [bhmul]
          ([h = ∏_i y_i]); the final flag [b] is their conjunction.

        All rules other than [ax] require the permutation invariant
        [Permutation us (vbs ++ inbs)] on the predecessor state.  The flag
        [b] is recorded rather than required to be [true], so a failed
        verification still yields a certificate explaining the outcome. *)
    Inductive count : state -> Type :=
    | ax  (ms : Vector.t (G * G) n) :
      (∀ (i : Fin.t n), Vector.nth ms i = (gid, gid)) ->
      count (partial (@List.nil ballot) (@List.nil ballot) (@List.nil ballot) ms)
    | cvalid (upf : ballot) (us vbs inbs : list ballot)
      (ms nms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) ->
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h (zip_with pair (get_ballot_ciphertext upf)
        (get_ballot_encryption_proof upf)) = true ->
      nms = @mul_encrypted_ballots G gop _ ms (get_ballot_ciphertext upf) ->
      count (partial (@List.cons _ upf us) (@List.cons _ upf vbs) inbs nms)
    | cinvalid (upf : ballot) (us vbs inbs : list ballot)
      (ms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) ->
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h (zip_with pair (get_ballot_ciphertext upf)
        (get_ballot_encryption_proof upf)) = false  ->
      count (partial (@List.cons _ upf us) vbs (@List.cons _ upf inbs) ms)
    | finish (us vbs inbs : list ballot) (ms : Vector.t (G * G) n)
      (ts : Vector.t tallier (1 + m))  (pt : Vector.t F n) (ds : Vector.t G n)
      (bptds bdec bpok bhmul b : bool) :
      count (partial us vbs inbs ms) -> Permutation us (vbs ++ inbs) ->
      ds = @decrypt_ballot_value G ginv gop _ _ ms
        (Vector.map  get_tallier_decryption_factor ts) ->
      (vector_forallb (fun u => u)
        (zip_with (fun u v => match Gdec (g ^ u) v with
        | left _ => true
        | _ => false
        end) pt ds)) = bptds ->
      (vector_forallb (fun u => vector_forallb (fun '(mx, (ux, sx)) =>
        @generalised_cp_accepting_conversations F G gop gpow Gdec g mx
        (match get_tallier_public_key u with
          | (_, _, _, pk_y) => pk_y
        end) ux sx)
        (zip_with pair (Vector.map fst ms) (zip_with pair
        (get_tallier_decryption_factor u)
        (get_tallier_decryption_proof u)))) ts = bdec) ->
      (vector_forallb (fun u =>
      match get_tallier_public_key u with
      | (_, _, _, pk_y) =>
        @accepting_conversation F G gop gpow Gdec g pk_y
        (get_tallier_pok u)
      end) ts = bpok) ->
      (match Gdec h (Vector.fold_right gop
      (Vector.map (fun u => match get_tallier_public_key u with
        | (_, _, _, pk_y) => pk_y
        end) ts) gid)
      with
      | left _ => true
      | _ => false
      end) = bhmul ->
      b = andb bptds (andb bdec (andb bpok bhmul)) ->
      count (finished us vbs inbs ts pt b).

    (** ** Building the certificate *)

    (** Walks the ballot list [bs] by structural recursion and returns the
        valid ballots, the invalid ballots, the encrypted tally and a
        derivation of [count (partial bs vbs inbs ms)] together with the
        permutation fact.  For each ballot it evaluates
        [verify_encryption_ballot_proof] once and uses the result (with its
        equation) to choose between [cvalid] and [cinvalid]. *)
    Definition compute_final_tally :
      ∀ (bs : list ballot),
      existsT (vbs inbs :  list ballot)
        (ms : Vector.t (G * G) n), (count (partial bs vbs inbs ms) *
        Permutation bs (vbs ++ inbs))%type.
    Proof.
      refine(fix fn (bs : list ballot) {struct bs} :=
        match bs with
        | @List.nil _ => _
        | @List.cons _ bh bt => _
        end).
      (* empty list: initial all-identity tally *)
      +
        set (ms := repeat_ntimes n (gid, gid)).
        exists (@List.nil ballot), (@List.nil ballot), ms.
        refine(pair (ax ms _) _).
         ++
          intros *.
          unfold ms.
          eapply repeat_ntimes_correct.
        ++
          reflexivity.
      +
        (* non-empty list: dependent match on the ballot verification result *)
        refine
        (match @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h (zip_with pair (get_ballot_ciphertext bh)
        (get_ballot_encryption_proof bh)) as v
        return @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
          _ g h (zip_with pair (get_ballot_ciphertext bh)
          (get_ballot_encryption_proof bh)) = v -> existsT (vbs inbs :  list ballot)
          (ms : Vector.t (G * G) n), (count (partial (bh :: bt) vbs inbs ms) *
          Permutation (bh :: bt) (vbs ++ inbs))%type
        with
        | true => fun ha => _
        | false => fun ha => _
        end eq_refl).
        ++
          destruct (fn bt) as [vbs [inbs [ms [Hcount Hperm]]]].
          exists (@List.cons _ bh vbs), inbs.
          set (nms := @mul_encrypted_ballots G gop _ ms (get_ballot_ciphertext bh)).
          exists nms.
          refine(pair _ _).
          *
            eapply cvalid. exact Hcount.
            exact Hperm.
            exact ha.
            unfold nms.
            exact eq_refl.
          *
            cbn.
            eapply Permutation_cons;
            [reflexivity | exact Hperm].
        ++
          destruct (fn bt) as [vbs [inbs [ms [Hcount Hperm]]]].
          exists vbs, (@List.cons _ bh inbs).
          exists ms.
          refine(pair _ _).
          *
            eapply cinvalid. exact Hcount.
            exact Hperm.
            exact ha.
          *
            cbn.
            eapply Permutation_trans with (l' := List.cons bh (vbs ++ inbs)).
            eapply Permutation_cons;[
              reflexivity | exact Hperm].
            eapply Permutation_middle.
    Defined.

    (** Full Helios verification: given the ballots [bs], the trustee records
        [ts] and the published plaintext tally [pt], returns the final flag
        and a derivation of [count (finished bs vbs inbs ts pt bfinal)].  It
        runs [compute_final_tally], combines the trustees' decryption
        factors, and evaluates the four checks of [finish]; each premise of
        [finish] holds by [eq_refl] because the flags are defined as exactly
        those computations.  This is the function called by the extracted
        OCaml verifier. *)
    Definition compute_final_count :
      ∀ (bs : list ballot) (ts : Vector.t tallier (1 + m)) (pt : Vector.t F n),
      existsT (bfinal : bool) (vbs inbs : list ballot),
        count (finished bs vbs inbs ts pt bfinal).
    Proof.
      intros *.
      destruct (compute_final_tally bs) as [vbs [inbs [ms [Hcount Hperm]]]].
      set (ds := @decrypt_ballot_value G ginv gop _ _ ms
        (Vector.map get_tallier_decryption_factor ts)).
      set (bptds := (vector_forallb (fun u => u)
        (zip_with (fun u v => match Gdec (g ^ u) v with
        | left _ => true
        | _ => false
        end) pt ds))).
      set (bdec := (vector_forallb (fun u => vector_forallb (fun '(mx, (ux, sx)) =>
        @generalised_cp_accepting_conversations F G gop gpow Gdec g mx
        (match get_tallier_public_key u with
          | (_, _, _, pk_y) => pk_y
        end) ux sx)
        (zip_with pair (Vector.map fst ms) (zip_with pair
        (get_tallier_decryption_factor u)
        (get_tallier_decryption_proof u)))) ts)).
      set (bpok := (vector_forallb (fun u =>
      match get_tallier_public_key u with
      | (_, _, _, pk_y) =>
        @accepting_conversation F G gop gpow Gdec g pk_y
        (get_tallier_pok u)
      end) ts)).
      set (bhmul := (match Gdec h (Vector.fold_right gop
      (Vector.map (fun u => match get_tallier_public_key u with
        | (_, _, _, pk_y) => pk_y
        end) ts) gid)
      with
      | left _ => true
      | _ => false
      end)).
      set (bfinal := andb bptds (andb bdec (andb bpok bhmul))).
      exists bfinal, vbs, inbs.
      eapply finish with (ms := ms) (ds := ds);
      try assumption.
      +
        unfold ds.
        exact eq_refl.
      +
        unfold bptds.
        exact eq_refl.
      +
        unfold bdec.
        exact eq_refl.
      +
        unfold bpok.
        exact eq_refl.
      +
        unfold bhmul.
        exact eq_refl.
      +
        unfold bfinal.
        exact eq_refl.
    Defined.

  End Defs.
End HeliosTally.
