(** * Inequality of discrete logarithms (NEQ)

    This file formalises a Σ-protocol for [k = 2 + n] discrete-logarithm statements
    [hs[i] = gs[i] ^ xs[i]] whose witnesses are pairwise distinct. The prover shows
    that it knows [xs] such that

    [[
      ∀ i, hs[i] = gs[i] ^ xs[i]     and     ∀ i ≠ j, xs[i] ≠ xs[j]
    ]]

    The protocol combines two existing proofs and uses one verifier challenge [c]
    for all of them:

    - an AND-composition of [k] Schnorr proofs, one for each
      [hs[i] = gs[i] ^ xs[i]], taken from [AndSigmaGen];
    - for every unordered pair [(i, j)] (there are [k (k - 1) / 2] of them, listed
      by [generate_pairs_of_vector]), an Okamoto proof from [Okamoto] of a
      representation of [gs[j]] in the two bases [gs[i] · gs[j]] and
      [hs[i] · hs[j]]:

    [[
      gⱼ = (gᵢ · gⱼ) ^ a · (hᵢ · hⱼ) ^ b,   a = xᵢ / (xᵢ - xⱼ),   b = 1 / (xⱼ - xᵢ)
    ]]

    When [hᵢ = gᵢ ^ xᵢ] and [hⱼ = gⱼ ^ xⱼ], the right-hand side is
    [gᵢ ^ (a + b xᵢ) · gⱼ ^ (a + b xⱼ)]. The first exponent is [0] and the second is
    [1], so the equation holds; the witness [(a, b)] exists only when [xᵢ ≠ xⱼ].
    Conversely, if [xᵢ = xⱼ = y] then [hᵢ · hⱼ = (gᵢ · gⱼ) ^ y], and any
    representation gives [gⱼ = (gᵢ · gⱼ) ^ γ] with [γ = a + b y]. That is a
    non-trivial discrete-logarithm relation between [gᵢ] and [gⱼ], or one of them is
    the identity.

    Sizes: a transcript has [k + k (k - 1) / 2] commitments, a challenge vector of
    length 1 and [k + k (k - 1)] responses, written [(2 + n) + (2 + n) (1 + n)] in
    the types. The prover consumes as many random scalars as there are responses.
    The proof therefore grows quadratically in [k].

    Main results:

    - completeness [generalised_neq_real_transcript_accepting_conversations]: if
      [gs[i] ^ xs[i] = hs[i]] for all [i] and the [xs] are pairwise distinct, the
      honest transcript is accepted for all randomness and challenges;
    - simulator correctness
      [generalised_neq_simulator_transcript_accepting_conversations]: the
      simulator's transcripts are always accepted;
    - special soundness [generalised_neq_accepting_conversations_soundness]: from
      two accepting transcripts with the same commitments and different challenges
      one obtains [xs] with [hs[i] = gs[i] ^ xs[i]], and either the [xs] are
      pairwise distinct, or for some [i ≠ j] the generator [gs[j]] is a power of
      [gs[i]], or [gs[i]] or [gs[j]] is the identity. The theorem does not assume
      independent generators; it states this dichotomy instead. See the remark on
      that theorem for how weak the second alternative is in a cyclic group;
    - special honest-verifier zero knowledge: the weak form
      [generalised_neq_special_honest_verifier_zkp] compares the two distributions
      after mapping each transcript to its verification bit. The strong form
      [generalised_neq_special_honest_verifier_zkp_perm] shows that the real and
      simulated distributions are permutations of each other when the sampling list
      enumerates the field without duplicates.

    The file depends on [Sigma] for transcripts, on [AndSigmaGen] for the
    AND-composition and its soundness ([generalise_and_sigma_soundness_neq]), on
    [Okamoto] for the two-base representation proof and its special soundness, and
    on [Utility.Util] for [generate_pairs_of_vector], [pair_zip], [pair_unzip] and
    [nat_div_2] (the identity [k (k - 1) / 2 + k (k - 1) / 2 = k (k - 1)]). It is
    instantiated in [Examples.NeqSigmaIns] and extracted through
    [Extraction/NeqSigmalib]. The Okamoto protocol is from T. Okamoto, Provably
    Secure and Practical Identification Schemes and Corresponding Signature Schemes,
    CRYPTO 1992. *)

From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos Arith Eqdep_dec Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import Util.
From ExtLib Require Import Monad.
From Sigma Require Import Sigma
  AndSigmaGen Okamoto.

Import MonadNotation
  VectorNotations
  EqNotations.

#[local] Open Scope monad_scope.

(** ** Parameters

    Everything is parametric in a field [F] of scalars and a group [G] with
    exponentiation [gpow]. The definitions only use the operations and decidable
    equality; the proofs assume in addition that [G] is a vector space over [F]
    (context [Hvec]). *)
Section DL.
  (** The scalar field [F] with its operations and decidable equality [Fdec]. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G]: identity [gid], inverse [ginv], operation [gop], exponentiation
      [gpow] by scalars and decidable equality [Gdec]. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Local notations: [^] is [gpow], and [*], [/], [+], [-] are the field
      operations. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** [(a; c; r)] builds a transcript [mk_sigma] with commitments [a], challenges
      [c] and responses [r]. *)
  #[local] Notation "( a ; c ; r )" :=
    (mk_sigma _ _ _ a c r).

  (** ** The NEQ protocol *)
  Section Neq.

    (** *** Definitions

        Every definition splits its randomness or response vector at [2 + n]: the
        first part belongs to the AND-composition of Schnorr proofs, the second part
        to the pairwise Okamoto proofs. The second part has length
        [(2 + n) (1 + n)]. It is cast to [P + P] with [P = (2 + n) (1 + n) / 2]
        (using [nat_div_2]) and grouped by [pair_zip] into [P] two-element vectors,
        one per pair. *)
    Section Def.

        (** Prover commitment. From [us = usl ++ usr] it computes the AND
            commitments [gs[i] ^ usl[i]], one per statement, followed by one Okamoto
            commitment [(gᵢ · gⱼ) ^ u₁ · (hᵢ · hⱼ) ^ u₂] per pair [(i, j)], where
            [(u₁, u₂)] is that pair's slice of [usr]. The commitment does not depend
            on the witness. *)
        Definition generalised_construct_neq_commitment {n : nat} :
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) ->
          Vector.t G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2).
        Proof.
          intros gs hs us.
          destruct (splitat (2 + n) us) as (usl & usr).
          set (and_commit := @construct_and_conversations_schnorr_commitment
            F G gpow _ gs usl).
          set (gs_pairs := Vector.map (fun '(g₁, g₂) => gop g₁ g₂)
            (generate_pairs_of_vector gs)).
          set (hs_pairs := Vector.map (fun '(h₁, h₂) => gop h₁ h₂)
            (generate_pairs_of_vector hs)).
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) +
           (Nat.div ((2 + n) * (1 + n)) 2) =
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in usr; clear ha.
          set (oka_commitment := zip_with (fun '(gg, hh) us =>
            @okamoto_commitment F G gid gop gpow
            [gg; hh] us) (zip_with pair gs_pairs hs_pairs)
            (pair_zip usr)).
          refine(and_commit ++ oka_commitment).
        Defined.

        (** Prover response for challenge [c]. The AND part responds
            [usl[i] + c · xs[i]]; the Okamoto part of pair [(i, j)] responds to the
            witness [(xᵢ · (xᵢ - xⱼ)⁻¹, (xⱼ - xᵢ)⁻¹)] with its two random values.
            Here [inv] is the field inverse. It is total, so the definition makes
            sense even when two [xs] coincide, but the transcript is then not
            accepting in general. The pair responses are flattened back with
            [pair_unzip]. *)
        Definition generalised_construct_neq_response {n : nat} :
          Vector.t F (2 + n) -> Vector.t F ((2 + n) + ((2 + n) * (1 + n))) ->
          F -> Vector.t F ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          intros xs us c.
          set (xs_pair := generate_pairs_of_vector xs).
          destruct (splitat (2 + n) us) as (usl & usr).
          set (and_response := @construct_and_conversations_schnorr_response
            F add mul _ xs usl c).
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) +
           (Nat.div ((2 + n) * (1 + n)) 2) =
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in usr; clear ha.
          set (oka_response := pair_unzip (zip_with (fun '(x₁, x₂) us =>
              @okamoto_response F add mul [x₁ * inv (x₁ - x₂); inv (x₂ - x₁)]
              us c) xs_pair (pair_zip usr))).
          rewrite nat_div_2 in oka_response.
          exact (and_response ++ oka_response).
        Defined.

        (** Honest transcript [(commitment; [c]; response)] for witnesses [xs],
            statement [gs], [hs], randomness [us] and challenge [c]. *)
        Definition generalised_construct_neq_conversations_real_transcript {n : nat} :
          Vector.t F (2 + n) -> Vector.t G (2 + n) ->
          Vector.t G (2 + n) ->
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          intros xs gs hs us c.
          exact (generalised_construct_neq_commitment gs hs us; [c];
          generalised_construct_neq_response xs us c).
        Defined.

        (** Special honest-verifier simulator. It uses the randomness [us] directly
            as the response vector and computes the commitments that make every
            check pass: the AND simulator commitment
            [gs[i] ^ usl[i] · hs[i] ^ (opp c)], and for each pair the Okamoto
            simulator commitment for bases [gᵢ · gⱼ] and [hᵢ · hⱼ] and target [gⱼ].
            The simulator does not use any witness. *)
        Definition generalised_construct_neq_conversations_simulator_transcript
          {n : nat} : Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          intros gs hs us c.
          destruct (splitat (2 + n) us) as (usl & usr).
          set (and_sim_comm :=
            @construct_and_conversations_simulator_commitment
            F opp G gop gpow _ gs hs usl c).
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) +
           (Nat.div ((2 + n) * (1 + n)) 2) =
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in usr; clear ha.
          set (oka_sim_comm := zip_with (fun '((g₁, g₂), (h₁, h₂)) vs =>
            @okamoto_simulator_protocol_commitment F opp G gid gop gpow
              [gop g₁ g₂; gop h₁ h₂] g₂ vs c)
              (zip_with pair
                (generate_pairs_of_vector gs)
                (generate_pairs_of_vector hs))
              (pair_zip usr)).
          refine (and_sim_comm ++ oka_sim_comm; [c]; us).
        Defined.

        (** Verifier. It splits commitments and responses at [2 + n] and first runs
            the AND verifier [generalised_and_accepting_conversations] on the
            Schnorr part. If that succeeds it checks, for every pair [(i, j)], the
            Okamoto equation [(gᵢ · gⱼ) ^ r₁ · (hᵢ · hⱼ) ^ r₂ = aᵢⱼ · gⱼ ^ c] with
            the pair's commitment [aᵢⱼ] and responses [r₁] and [r₂]. It accepts iff
            all these checks pass. *)
        Definition generalised_neq_accepting_conversations {n : nat} :
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)) -> bool.
        Proof.
          intros gs hs pf.
          refine
            match pf with
            |(a; c; r) => _
            end.
          destruct (splitat (2 + n) a) as (al & ar).
          destruct (splitat (2 + n) r) as (rl & rr).
          refine
            match
              @generalised_and_accepting_conversations F G gop gpow Gdec _
              gs hs (al; c; rl)
            with
            | true => _
            | _ => false
            end.
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) +
           (Nat.div ((2 + n) * (1 + n)) 2) =
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in rr; clear ha.
          set (oka_veri :=
            (zip_with (fun '((g₁, g₂), (h₁, h₂)) '(a, rs) =>
            @okamoto_accepting_conversation F G gid gop gpow Gdec
              [gop g₁ g₂; gop h₁ h₂] g₂ ([a]; c; rs))
              (zip_with pair
                (generate_pairs_of_vector gs)
                (generate_pairs_of_vector hs))
              (zip_with pair ar (pair_zip rr)))).
            exact (vector_forallb (fun x => x) oka_veri).
        Defined.

        (** Real transcript distribution for a fixed challenge [c]: draw
            [(2 + n) + (2 + n) (1 + n)] scalars independently and uniformly from the
            non-empty list [lf] and run the honest prover. *)
        Definition generalised_neq_schnorr_distribution
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
          (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F) :
          dist (@sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          us <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_real_transcript xs gs hs us c).

        (** Simulated transcript distribution: draw the same amount of randomness
            and run the simulator. *)
        Definition generalised_neq_simulator_distribution
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
          (gs hs : Vector.t G (2 + n)) (c : F) :
          dist (@sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          us <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_simulator_transcript gs hs us c).

    End Def.

    (** *** Proofs *)
    Section Proofs.

        (** From here on [G] is a vector space over [F], which models a prime-order
            group, and the [field] tactic is available for [F]. *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub
            div opp inv G (@eq G) gid ginv gop gpow}.

        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

      (** Inversion lemma for the commitment: if the commitment on randomness
          [usl ++ (usrl ++ usr)] (after the length cast) equals [al ++ ar], then
          [al] is the AND commitment on [usl] and [ar] is the vector of Okamoto
          commitments on the pairs. *)
      Theorem generalised_construct_neq_commitment_proof :
        ∀ (n : nat) (gs hs al : Vector.t G (2 + n))
        (ar : Vector.t G ((2 + n) * (1 + n) / 2))
        (usl : Vector.t F (2 + n))
        (usrl usrr : Vector.t F (Nat.div ((2 + n) * (1 + n)) 2)),
        generalised_construct_neq_commitment gs hs
          (usl ++ @eq_rect _ _ (Vector.t F)
          (usrl ++ usrr) _ (nat_div_2 n)) = al ++ ar ->
        @construct_and_conversations_schnorr_commitment F G gpow _
        gs usl = al ∧
        zip_with (λ '(gg, hh) us,
          @okamoto_commitment F G gid gop gpow [gg; hh] us)
          (zip_with pair
          (map (λ '(g₁, g₂), gop g₁ g₂) (generate_pairs_of_vector gs))
          (map (λ '(h₁, h₂), gop h₁ h₂) (generate_pairs_of_vector hs)))
          (pair_zip (usrl ++ usrr)) = ar.
      Proof.
        intros * ha.
        unfold generalised_construct_neq_commitment in ha.
        rewrite !VectorSpec.splitat_append in ha.
        rewrite rew_opp_l in ha.
        eapply VectorSpec.append_inj in ha.
        exact ha.
      Qed.

      (** Completeness. If [gs[i] ^ xs[i] = hs[i]] for every [i] and the [xs] are
          pairwise distinct, then for all randomness [us] and challenges [c] the
          honest transcript is accepted.

          Proof idea: the AND part is completeness of [AndSigmaGen]. For every pair,
          [generate_pairs_distinct_triple] gives indices [j ≠ k] with
          [(g₁, g₂) = (gs[j], gs[k])] and corresponding [h]s and [x]s. Okamoto
          completeness then reduces to the identity
          [(g₁ g₂) ^ (x₁ / (x₁ - x₂)) · (h₁ h₂) ^ (1 / (x₂ - x₁)) = g₂], an exercise
          in field arithmetic that needs [x₁ ≠ x₂]. *)
      Theorem generalised_neq_real_transcript_accepting_conversations :
        ∀ (n : nat) (gs hs : Vector.t G (2 + n)) (xs : Vector.t F (2 + n))
        (us : Vector.t F (2 + n + (2 + n) * (1 + n))) (c : F),
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        generalised_neq_accepting_conversations gs hs
          (generalised_construct_neq_conversations_real_transcript xs gs hs us c) = true.
      Proof.
        intros * ha hb.
        unfold generalised_neq_accepting_conversations,
        generalised_construct_neq_conversations_real_transcript.
        destruct (splitat (2 + n) (generalised_construct_neq_commitment gs hs us)) as
        [al ar] eqn:hc.
        destruct (splitat (2 + n) (generalised_construct_neq_response xs us c)) as
        [rl rr] eqn:hd.
        destruct (splitat (2 + n) us) as (usl & usr) eqn:he.
        eapply append_splitat in hc, hd, he.
        subst.
        unfold generalised_construct_neq_commitment in hc.
        rewrite !VectorSpec.splitat_append in hc.
        unfold generalised_construct_neq_response in hd.
        rewrite splitat_append in hd.
        eapply VectorSpec.append_inj in hc, hd.
        destruct hc as (hcl & hcd).
        destruct hd as (hdl & hdr).
        subst.
        (* AND part: completeness of the AND composition. *)
        pose proof (@construct_and_conversations_schnorr_completeness F zero one
          add mul sub div opp inv G gid ginv gop gpow Gdec Hvec
          _ xs gs hs ha usl c) as hf.
        unfold construct_and_conversations_schnorr in hf.
        rewrite hf; clear hf.
        rewrite !rew_opp_l.
        (* Okamoto part: check every pair separately. *)
        rewrite vector_forallb_correct.
        intro i.
        rewrite !nth_zip_with.
        destruct ((generate_pairs_of_vector gs)[@i]) as (g₁ & g₂) eqn:hc.
        destruct ((generate_pairs_of_vector hs)[@i]) as (h₁ & h₂) eqn:hd.
        destruct ((generate_pairs_of_vector xs)[@i]) as (x₁ & x₂) eqn:hf.
        unfold okamoto_accepting_conversation, okamoto_commitment,
        okamoto_response.
        rewrite !map_fin.
        rewrite !hc, !hd, !pair_zip_unzip_id.
        rewrite !nth_zip_with.
        rewrite hf.
        pose proof @generalised_okamoto_real_accepting_conversation F zero one
          add mul sub div opp inv G gid ginv gop gpow Gdec Hvec _
          ([x₁ * inv (x₁ - x₂); inv (x₂ - x₁)])
          ([gop g₁ g₂; gop h₁ h₂])
          g₂ ((pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr))[@i]) as hg.
        unfold generalised_okamoto_real_protocol in hg.
        eapply hg; clear hg.
        cbn.
        (* The pair comes from two distinct indices j and k; replace h₁ and h₂ by
           g₁^x₁ and g₂^x₂. *)
        destruct (@generate_pairs_distinct_triple G F _
        gs hs xs i g₁ g₂ h₁ h₂ x₁ x₂ hc hd hf) as (j & k & hg & hi &
        hj & hk & hl & hm & hn).
        clear hc hd hf.
        pose proof (ha j) as hc.
        rewrite <- hi, <-hk, <-hm in hc.
        rewrite <-hc.
        clear hc.
        pose proof (ha k) as hc.
        rewrite <- hj, <-hl, <-hn in hc.
        rewrite <-hc.
        rewrite right_identity, !smul_distributive_vadd,
        <-!smul_associative_fmul.
        rewrite gop_simp.
        rewrite <-!smul_distributive_fadd.
        (* The exponent of g₁ is x₁/(x₁ - x₂) + x₁/(x₂ - x₁) = 0. The side
           conditions x₁ - x₂ ≠ 0 and x₂ - x₁ ≠ 0 come from the distinctness
           hypothesis. *)
        assert (hd : (x₁ * inv (x₁ - x₂) + x₁ * inv (x₂ - x₁)) = zero). field.
        pose proof (hb j k hg) as hd.
        rewrite <-hm, <-hn in hd.
        split. intro hw.
        eapply hd.
        eapply eq_sym, ring_sub_zero_iff.
        exact hw.
        intro hw. eapply hd.
        eapply ring_sub_zero_iff.
        exact hw.
        rewrite !hd; clear hd.
        rewrite field_zero, left_identity.
        (* The exponent of g₂ is x₁/(x₁ - x₂) + x₂/(x₂ - x₁) = 1. *)
        assert (hd : (x₁ * inv (x₁ - x₂) + x₂ * inv (x₂ - x₁)) =
          (x₂ - x₁) * inv (x₂ - x₁)). field.
        pose proof (hb j k hg) as hd.
        rewrite <-hm, <-hn in hd.
        split. intro hw.
        eapply hd.
        eapply eq_sym, ring_sub_zero_iff.
        exact hw.
        intro hw. eapply hd.
        eapply ring_sub_zero_iff.
        exact hw.
        rewrite !hd; clear hd.
        assert (hd : ((x₂ - x₁) * inv (x₂ - x₁)) = one).
        field.
        pose proof (hb j k hg) as hd.
        rewrite <-hm, <-hn in hd.
        intro hw.
        eapply hd.
        eapply eq_sym, ring_sub_zero_iff.
        exact hw.
        rewrite hd, field_one.
        reflexivity.
      Qed.

      (** The simulator's transcripts are always accepted, for every randomness and
          challenge, by simulator correctness of the AND composition and of the
          Okamoto protocol. *)
      Theorem generalised_neq_simulator_transcript_accepting_conversations :
        ∀ (n : nat) (gs hs : Vector.t G (2 + n))
        (us : Vector.t F (2 + n + (2 + n) * (1 + n))) (c : F),
        generalised_neq_accepting_conversations gs hs
          (generalised_construct_neq_conversations_simulator_transcript gs hs us c) = true.
      Proof.
        intros *.
        unfold generalised_neq_accepting_conversations,
        generalised_construct_neq_conversations_simulator_transcript.
        destruct (splitat (2 + n) us) as (usl & usr) eqn:ha.
        rewrite ha, splitat_append.
        setoid_rewrite construct_and_conversations_simulator_completeness.
        rewrite vector_forallb_correct.
        intro i.
        rewrite !nth_zip_with.
        destruct ((generate_pairs_of_vector gs)[@i]) as (g₁ & g₂) eqn:hc.
        destruct ((generate_pairs_of_vector hs)[@i]) as (h₁ & h₂) eqn:hd.
        pose proof @generalised_okamoto_simulator_accepting_conversation F
        zero one add mul sub div opp inv G gid ginv gop gpow Gdec Hvec
        _ [gop g₁ g₂; gop h₁ h₂] g₂
        ((pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr))[@i]) c as he.
        eapply he.
        exact Fdec.
      Qed.

      (** Given a decision procedure for every proposition (hypothesis [ha], a
          strong form of excluded middle), [P -> Q] is equivalent to [~P ∨ Q].
          Nothing in this file or elsewhere in the development uses this lemma. *)
      Theorem dec_prop_equiv (ha : ∀ (A : Prop), A + ~A) : ∀ (P Q : Prop),
        (P -> Q) <-> ~P ∨ Q.
      Proof.
        intros *; split.
        +
          intro f.
          destruct (ha P) as [hb | hb];
          [(right; eapply f; exact hb) |
          (left; exact hb)].
        +
          intros hb p.
          destruct hb as [hb | hb];
          [congruence | exact hb].
      Qed.

      (** Special soundness. Suppose two transcripts [(a; [c₁]; rs₁)] and
          [(a; [c₂]; rs₂)] share their commitments, have [c₁ ≠ c₂], and are both
          accepted. Then there are [xs] with [hs[i] = gs[i] ^ xs[i]] for every [i],
          and either

          - the [xs] are pairwise distinct, or
          - there are [i ≠ j] such that [gs[j] = gs[i] ^ α] for some [α], or [gs[i]]
            or [gs[j]] is the identity [gid].

          Remark: the existential [∃ α, gs[j] = gs[i] ^ α] is a proposition. In a
          cyclic group it holds for every [gs[i] ≠ gid], so the second alternative
          has no logical content there. The useful reading is computational: the
          proof builds [α] explicitly from the extracted Okamoto witness, as
          [γ / (1 - γ)] or its inverse. So a prover that convinces the verifier with
          two equal witnesses yields a discrete-logarithm relation between two
          generators. The formal statement does not include the assumption that such
          relations are hard to find.

          Proof idea: AND special soundness ([generalise_and_sigma_soundness_neq])
          extracts [ys]. If [ys] has two equal entries [ii ≠ jj], take the Okamoto
          pair built from them ([generate_pairs_contains_triple]) and extract a
          representation [g₂ = (g₁ g₂) ^ a · (h₁ h₂) ^ b] with Okamoto special
          soundness. With [h₁ = g₁ ^ y] and [h₂ = g₂ ^ y] this gives
          [g₂ = (g₁ g₂) ^ γ] for [γ = a + b y]. Then [γ = 0] gives [g₂ = gid],
          [γ = 1] gives [g₁ = gid], and otherwise [g₂ = g₁ ^ (γ / (1 - γ))]. Both
          orders of the pair are handled. *)
      Theorem generalised_neq_accepting_conversations_soundness :
        ∀ (n : nat) (a : Vector.t G (2 + n + (2 + n) * (1 + n) / 2))
        (c₁ c₂ : F) (rs₁ rs₂ : Vector.t F (2 + n + (2 + n) * (1 + n)))
        (gs hs : Vector.t G (2 + n)), [c₁] <> [c₂] ->
        generalised_neq_accepting_conversations gs hs (a; [c₁]; rs₁) = true ->
        generalised_neq_accepting_conversations gs hs (a; [c₂]; rs₂) = true ->
        ∃ (xs : Vector.t F (2 + n)),
        (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) ∧
        ((∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ∨
        (∃ (i j : Fin.t (2 + n)), i ≠ j ∧ ((∃ (α : F), gs[@j] = gs[@i] ^ α) ∨
        gs[@i] = gid ∨ gs[@j] = gid))).
      Proof.
        intros * hn ha hb.
        unfold generalised_neq_accepting_conversations in ha, hb.
        destruct (splitat (2 + n) a) as (al & ar) eqn:hc.
        destruct (splitat (2 + n) rs₁) as (rl₁ & rr₁) eqn:hd.
        destruct (splitat (2 + n) rs₂) as (rl₂ & rr₂) eqn:he.
        eapply append_splitat in hc, hd, he.
        destruct (generalised_and_accepting_conversations gs hs (al; [c₁]; rl₁))
        eqn:hf; try congruence.
        destruct (generalised_and_accepting_conversations gs hs (al; [c₂]; rl₂))
        eqn:hg; try congruence.
        (* AND special soundness extracts ys with hs = gs ^ ys componentwise. *)
        destruct (@generalise_and_sigma_soundness_neq F zero one add mul sub div
        opp inv Fdec G gid ginv gop gpow Gdec Hvec _ gs hs al [c₁] rl₁
        [c₂] rl₂ hf hg hn) as (ys & hi & hir). cbn in hir.
        exists ys. split. exact (fun f => eq_sym (hi f)).
        rewrite vector_forallb_correct in ha, hb.
        clear hf hg.
        (* Either ys is pairwise distinct (first disjunct) or two entries ii ≠ jj
           are equal. *)
        destruct (@vector_unique_decidable _ Fdec _ ys) as [hj |
          (ii & jj & hj & hk)].
        ++
          left. exact hj.
        ++
          right.
          (* Locate the Okamoto pair kk built from ii and jj. *)
          destruct (@generate_pairs_contains_triple _ _ _ gs hs ys
            ii jj hj) as (kk & hl).
          specialize (ha kk).
          specialize (hb kk).
          rewrite !nth_zip_with in ha, hb.
          destruct (generate_pairs_of_vector gs)[@kk] as (g₁, g₂).
          destruct (generate_pairs_of_vector hs)[@kk] as (h₁, h₂).
          destruct (generate_pairs_of_vector ys)[@kk] as (y₁, y₂).
          cbn in hl.
          assert (hw : c₁ ≠ c₂).
          intro hw. eapply hn.
          subst. reflexivity.
          (* Okamoto special soundness for pair kk: g₂ = (g₁ g₂)^a · (h₁ h₂)^b. *)
          destruct (@generalised_okamoto_real_special_soundness F zero
          one add mul sub div opp inv G gid ginv gop gpow Gdec Hvec _
          [gop g₁ g₂; gop h₁ h₂]  g₂ ar[@kk] c₁ c₂
          (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₁))[@kk]
          (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₂))[@kk]
          hw ha hb) as (xs & hm & ho). clear hw.
          (* The pair lists (ii, jj) either in this order or swapped. *)
          destruct hl as [hl | hl].
          -
            destruct hl as (hl₁ & hl₂ & hl₃ & hl₄ & hl₅ & hl₆).
            exists ii, jj. split. exact hj.
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₁))[@kk]
            as rrs₁; clear Heqrrs₁.
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₂))[@kk]
            as rrs₂; clear Heqrrs₂.
            setoid_rewrite <-hl₂.
            setoid_rewrite <-hl₁.
            pose proof (hi ii) as hii.
            pose proof (hi jj) as hjj.
            setoid_rewrite <-hl₁ in hii.
            setoid_rewrite <-hl₃ in hii.
            setoid_rewrite <-hl₅ in hii.
            setoid_rewrite <-hl₂ in hjj.
            setoid_rewrite <-hl₄ in hjj.
            setoid_rewrite <-hl₆ in hjj.
            setoid_rewrite <-hl₅ in hk.
            setoid_rewrite <-hl₆ in hk.
            destruct (vector_inv_S xs) as (xsh & xst & hx).
            destruct (vector_inv_S xst) as (xsth & xstt & hxx).
            pose proof (vector_inv_0 xstt) as hxxx.
            revert ho.
            subst xs. subst xst.
            subst xstt. cbn in hm.
            rewrite <-hii, <-hjj, <-hk in hm.
            rewrite !smul_distributive_vadd,
            <-!smul_associative_fmul,
            gop_simp, right_identity,
            associative in hm.
            pose proof (@vector_space_smul_distributive_fadd F (@eq F)
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow Hvec) as hp.
            unfold  is_smul_distributive_fadd in hp.
            rewrite <-hp, <-associative,
            <-hp in hm.
            assert (ht : (y₁ * xsth + xsh) = xsh + y₁ * xsth).
            field. rewrite ht in hm. clear ht.
            (* Collect exponents: g₂ = g₁^γ · g₂^γ with γ = a + b y. *)
            remember ((xsh + y₁ * xsth)) as gamma.
            (* γ = 0: g₂ = gid. γ = 1: g₁ = gid. Otherwise g₂ = g₁^(γ / (1 - γ)). *)
            destruct (Fdec gamma zero) as [hf | hf].
            *
              rewrite hf, field_zero, left_identity,
              field_zero in hm. intro ho.
              right. right. exact hm.
            *
              destruct (Fdec gamma one) as [hfo | hfo].
              **
                rewrite hfo, !field_one in hm.
                eapply f_equal with (f := fun x => gop x (ginv g₂)) in hm.
                rewrite right_inverse, <-associative,
                right_inverse, right_identity in hm.
                intro ho.
                right. left. now rewrite hm.
              **
                eapply f_equal with (f := fun x => gop x (ginv (g₂ ^ gamma)))
                in hm.
                rewrite !connection_between_vopp_and_fopp in hm.
                assert (ht : gop g₂ (g₂ ^ opp gamma) =
                  gop (g₂ ^ one) (g₂ ^ opp gamma)).
                f_equal. now rewrite field_one.
                rewrite ht in hm. clear ht.
                rewrite <-hp, <-associative in hm.
                rewrite <-hp in hm.
                assert (ht : (gamma + opp gamma) = zero).
                field. rewrite ht in hm.
                clear ht. rewrite field_zero, right_identity in hm.
                eapply f_equal with (f := fun x => x ^ inv (one + opp gamma)) in hm.
                rewrite <-!smul_associative_fmul in hm.
                assert (ht : ((one + opp gamma) * inv (one + opp gamma)) = one).
                field. intro hg. eapply hfo.
                eapply f_equal with (f := fun x => x + gamma) in hg.
                rewrite <-associative in hg.
                assert (hgg : opp gamma + gamma = zero). field.
                rewrite hgg in hg. clear hgg.
                rewrite right_identity, left_identity in hg.
                now rewrite hg.
                rewrite ht, field_one in hm.
                intro ho.
                left.
                exists ((gamma * inv (one + opp gamma))).
                exact hm.
          -
            destruct hl as (hl₁ & hl₂ & hl₃ & hl₄ & hl₅ & hl₆).
            exists ii, jj. split. exact hj.
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₁))[@kk]
            as rrs₁; clear Heqrrs₁.
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₂))[@kk]
            as rrs₂; clear Heqrrs₂.
            setoid_rewrite <-hl₂.
            setoid_rewrite <-hl₁.
            pose proof (hi ii) as hii.
            pose proof (hi jj) as hjj.
            setoid_rewrite <-hl₂ in hii.
            setoid_rewrite <-hl₄ in hii.
            setoid_rewrite <-hl₆ in hii.
            setoid_rewrite <-hl₁ in hjj.
            setoid_rewrite <-hl₃ in hjj.
            setoid_rewrite <-hl₅ in hjj.
            setoid_rewrite <-hl₅ in hk.
            setoid_rewrite <-hl₆ in hk.
            destruct (vector_inv_S xs) as (xsh & xst & hx).
            destruct (vector_inv_S xst) as (xsth & xstt & hxx).
            pose proof (vector_inv_0 xstt) as hxxx.
            revert ho.
            subst xs. subst xst.
            subst xstt. cbn in hm.
            rewrite <-hii, <-hjj, <-hk in hm.
            rewrite !smul_distributive_vadd,
            <-!smul_associative_fmul,
            gop_simp, right_identity,
            associative in hm.
            pose proof (@vector_space_smul_distributive_fadd F (@eq F)
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow Hvec) as hp.
            unfold  is_smul_distributive_fadd in hp.
            rewrite <-hp, <-associative,
            <-hp in hm.
            assert (ht : (y₂ * xsth + xsh) = xsh + y₂ * xsth).
            field. rewrite ht in hm. clear ht.
            (* Swapped order: the same computation with the roles of ii and jj
               exchanged. *)
            remember ((xsh + y₂ * xsth)) as gamma.
            (* γ = 0: gs[ii] = gid. γ = 1: gs[jj] = gid. Otherwise invert the
               exponent to express gs[jj] as a power of gs[ii]. *)
            destruct (Fdec gamma zero) as [hf | hf].
            *
              rewrite hf, field_zero, left_identity,
              field_zero in hm.
              intro ho.
              right. left. exact hm.
            *
              destruct (Fdec gamma one) as [hfo | hfo].
              **
                rewrite hfo, !field_one in hm.
                eapply f_equal with (f := fun x => gop x (ginv g₂)) in hm.
                rewrite right_inverse, <-associative,
                right_inverse, right_identity in hm.
                intro ho.
                right. right. now rewrite hm.
              **
                eapply f_equal with (f := fun x => gop x (ginv (g₂ ^ gamma)))
                in hm.
                rewrite !connection_between_vopp_and_fopp in hm.
                assert (ht : gop g₂ (g₂ ^ opp gamma) =
                  gop (g₂ ^ one) (g₂ ^ opp gamma)).
                f_equal. now rewrite field_one.
                rewrite ht in hm. clear ht.
                rewrite <-hp, <-associative in hm.
                rewrite <-hp in hm.
                assert (ht : (gamma + opp gamma) = zero).
                field. rewrite ht in hm.
                clear ht. rewrite field_zero, right_identity in hm.
                eapply f_equal with (f := fun x => x ^ inv (one + opp gamma)) in hm.
                rewrite <-!smul_associative_fmul in hm.
                assert (ht : ((one + opp gamma) * inv (one + opp gamma)) = one).
                field. intro hg. eapply hfo.
                eapply f_equal with (f := fun x => x + gamma) in hg.
                rewrite <-associative in hg.
                assert (hgg : opp gamma + gamma = zero). field.
                rewrite hgg in hg. clear hgg.
                rewrite right_identity, left_identity in hg.
                now rewrite hg.
                rewrite ht, field_one in hm.
                eapply f_equal with (f := fun x =>
                  x ^ inv (gamma * inv (one + opp gamma))) in hm.
                rewrite <-!smul_associative_fmul in hm.
                assert (hgam : (gamma * inv (one + opp gamma) * inv (gamma * inv (one + opp gamma))) = one). field.
                split; [| exact hf].
                intro hg. eapply hfo.
                eapply f_equal with (f := fun x => x + gamma) in hg.
                assert (hgg : opp gamma + gamma = zero). field.
                rewrite <-associative in hg.
                rewrite hgg in hg. clear hgg.
                rewrite right_identity, left_identity in hg.
                now rewrite hg.
                rewrite hgam, field_one in hm.
                intro ho.
                left.
                exists (inv (gamma * inv (one + opp gamma))).

                exact (eq_sym hm).
      Qed.

      (** ** Special honest-verifier zero knowledge

          [p / q] is the probability [p/q] built by [mk_prob]. *)
      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      (** Under the witness hypotheses, every transcript in the support of the
          honest prover pushed over any distribution [l] of randomness is accepting. *)
      Lemma generalised_neq_real_distribution_transcript_accepting_generic {n : nat} :
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) (xs : Vector.t F (2 + n))
        (gs hs : Vector.t G (2 + n))
        (trans : sigma_proto) (pr : prob) (c : F),
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] =  hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)),
            Ret (generalised_construct_neq_conversations_real_transcript xs gs hs us c))) →
        generalised_neq_accepting_conversations gs hs trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Hrel Hr Ha.
          cbn in Ha;
          inversion Ha.
        +
          destruct l as [|(la, lp) l].
          ++
            intros * Hrel Hr Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply generalised_neq_real_transcript_accepting_conversations;
            assumption.
          ++
            intros * Hrel Hr Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply generalised_neq_real_transcript_accepting_conversations;
              assumption.
            +++
              eapply IHl; try assumption.
              exact Hrel. exact Hr.
              exact Ha.
      Qed.

      (** If every entry of [l] has weight [1 / m], then so does every transcript
          obtained by running the honest prover on [l]. *)
      Lemma generalised_neq_real_distribution_transcript_probability_generic {n : nat} :
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) (xs : Vector.t F (2 + n))
        (gs hs : Vector.t G (2 + n))
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n + (2 + n) * (1 + n))) (prx : prob),
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)),
          Ret (generalised_construct_neq_conversations_real_transcript xs gs hs us c))) →
        pr = 1 / m.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst;
          clear Hwa.
          unfold mul_prob,
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.

      (** Every element [(a, b)] of the real distribution is accepting and has
          probability [1 / |lf| ^ ((2 + n) + (2 + n) (1 + n))]. *)
      Lemma generalised_neq_real_distribution_transcript_generic {n : nat} :
        forall (lf : list F) (Hlf : lf <> List.nil)
        (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n))
        (a : sigma_proto) (b : prob) (c : F),
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.In (a, b) (generalised_neq_schnorr_distribution lf Hlf xs gs hs c) ->
        generalised_neq_accepting_conversations gs hs a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n + (2 + n) * (1 + n)))).
      Proof.
        intros * Hrel Hr Ha.
        refine(conj _ _).
        +
          eapply generalised_neq_real_distribution_transcript_accepting_generic.
          exact Hrel. exact Hr. exact Ha.
        +
          eapply generalised_neq_real_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.

       (** Every transcript in the support of the simulator pushed over any
           distribution is accepting. *)
       Lemma generalised_neq_simulator_distribution_transcript_accepting_generic {n : nat} :
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n))))
        (gs hs : Vector.t G (2 + n)) (trans : sigma_proto) (pr : prob) (c : F),
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)),
            Ret (generalised_construct_neq_conversations_simulator_transcript gs hs us c))) →
        generalised_neq_accepting_conversations gs hs trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Ha.
          cbn in Ha;
          inversion Ha.
        +
          destruct l as [|(la, lp) l].
          ++
            intros * Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply generalised_neq_simulator_transcript_accepting_conversations.
          ++
            intros * Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply generalised_neq_simulator_transcript_accepting_conversations.
            +++
              eapply IHl; exact Ha.
      Qed.

      (** Simulator analogue of
          [generalised_neq_real_distribution_transcript_probability_generic]. *)
      Lemma generalised_neq_simulator_distribution_transcript_probability_generic {n : nat} :
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n))))
        (gs hs : Vector.t G (2 + n))
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n + (2 + n) * (1 + n))) (prx : prob),
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)),
          Ret (generalised_construct_neq_conversations_simulator_transcript gs hs us c))) →
        pr = 1 / m.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst;
          clear Hwa.
          unfold mul_prob,
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.

       (** Every element [(a, b)] of the simulated distribution is accepting and has
           probability [1 / |lf| ^ ((2 + n) + (2 + n) (1 + n))]. *)
       Lemma generalised_neq_simulator_distribution_transcript_generic {n : nat} :
        forall (lf : list F) (Hlf : lf <> List.nil)
        (gs hs : Vector.t G (2 + n))
        (a : sigma_proto) (b : prob) (c : F),
        List.In (a, b) (generalised_neq_simulator_distribution lf Hlf gs hs c) ->
        generalised_neq_accepting_conversations gs hs a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n + (2 + n) * (1 + n)))).
      Proof.
        intros * Ha.
        refine(conj _ _).
        +
          eapply generalised_neq_simulator_distribution_transcript_accepting_generic.
          exact Ha.
        +
          eapply generalised_neq_simulator_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.

      (** Weak form of special honest-verifier zero knowledge. Under the witness
          hypotheses, the real and simulated distributions coincide once each
          transcript is replaced by its verification bit: both are lists of the same
          length whose entries are all
          [(true, 1 / |lf| ^ ((2 + n) + (2 + n) (1 + n)))]. This does not compare
          the transcripts themselves; see
          [generalised_neq_special_honest_verifier_zkp_perm]. *)
      Lemma generalised_neq_special_honest_verifier_zkp {n : nat} :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F),
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.map (fun '(a, p) =>
          (generalised_neq_accepting_conversations gs hs a, p))
          (@generalised_neq_schnorr_distribution n lf Hlfn xs gs hs c) =
        List.map (fun '(a, p) =>
          (generalised_neq_accepting_conversations gs hs a, p))
          (@generalised_neq_simulator_distribution n lf Hlfn gs hs c).
      Proof.
        intros * Hrel Hr.
        eapply map_ext_eq.
        +
          unfold generalised_neq_schnorr_distribution,
          generalised_neq_simulator_distribution; cbn.
          repeat rewrite distribution_length.
          reflexivity.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_neq_real_distribution_transcript_generic.
          exact Hrel. exact Hr. exact Ha.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_neq_simulator_distribution_transcript_generic.
          exact Ha.
      Qed.

      (** *** Equality of the real and simulated distributions

          The bijection on randomness is the prover's own response map
          [us ↦ generalised_construct_neq_response xs us c]. It adds [c] times the
          witness to every coordinate: [xs[i]] in the AND part and the derived
          Okamoto witness for every pair. Its inverse is the same map with challenge
          [opp c].

          [pair_unzip_zip_id]: [pair_unzip] is a left inverse of [pair_zip]. *)
      Lemma pair_unzip_zip_id : forall (m : nat) (vs : Vector.t F (m + m)),
        pair_unzip (pair_zip vs) = vs.
      Proof.
        induction m as [| m ih]; intros vs.
        + rewrite (vector_inv_0 vs); reflexivity.
        + cbn.
          generalize (eq_trans eq_refl (f_equal S (eq_ind_r
            (λ n : nat, S (m + m) = n) eq_refl (add_succ_r m m)))) as e.
          intros e.
          set (vs' := rew <- [λ n : nat, t F n] e in vs).
          assert (hvs : vs = rew [λ n : nat, t F n] e in vs') by
            (unfold vs'; symmetry; apply rew_opp_r).
          clearbody vs'.
          rewrite hvs; clear hvs.
          destruct (vector_inv_S vs') as (a & vs'' & hv).
          destruct (vector_inv_S vs'') as (b & w & hw).
          subst; cbn.
          rewrite rew_opp_l; cbn.
          rewrite ih.
          match goal with
          | |- eq_rect _ _ _ _ ?p = eq_rect _ _ _ _ ?q =>
            rewrite (Peano_dec.UIP_nat _ _ p q); reflexivity
          end.
      Qed.

      (** The algebraic core of completeness, stated on its own: under the witness
          hypotheses, for every pair [i] with bases [(g₁, g₂)], targets [(h₁, h₂)]
          and witnesses [(x₁, x₂)], the element [g₂] equals the Okamoto product
          [(g₁ g₂) ^ (x₁ / (x₁ - x₂)) · (h₁ h₂) ^ (1 / (x₂ - x₁))]. *)
      Lemma neq_pair_relation {n : nat} (gs hs : Vector.t G (2 + n))
        (xs : Vector.t F (2 + n))
        (ha : ∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i])
        (hb : ∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) :
        forall (i : Fin.t ((2 + n) * (1 + n) / 2)) (g₁ g₂ h₁ h₂ : G) (x₁ x₂ : F),
        (generate_pairs_of_vector gs)[@i] = (g₁, g₂) ->
        (generate_pairs_of_vector hs)[@i] = (h₁, h₂) ->
        (generate_pairs_of_vector xs)[@i] = (x₁, x₂) ->
        g₂ = fold_right (λ '(g, x) acc, gop (g ^ x) acc)
          (zip_with pair [gop g₁ g₂; gop h₁ h₂]
            [x₁ * inv (x₁ - x₂); inv (x₂ - x₁)]) gid.
      Proof.
        intros * hc hd hf.
        cbn.
        destruct (@generate_pairs_distinct_triple G F _
          gs hs xs i g₁ g₂ h₁ h₂ x₁ x₂ hc hd hf) as
          (j & k & hg & hi & hj & hk & hl & hm & hn).
        clear hc hd hf.
        pose proof (ha j) as hc.
        rewrite <- hi, <-hk, <-hm in hc.
        rewrite <-hc.
        clear hc.
        pose proof (ha k) as hc.
        rewrite <- hj, <-hl, <-hn in hc.
        rewrite <-hc.
        rewrite right_identity, !smul_distributive_vadd,
        <-!smul_associative_fmul.
        rewrite gop_simp.
        rewrite <-!smul_distributive_fadd.
        (* The exponent of g₁ vanishes; distinctness gives the non-zero
           denominators. *)
        assert (hd : (x₁ * inv (x₁ - x₂) + x₁ * inv (x₂ - x₁)) = zero).
        {
          field.
          pose proof (hb j k hg) as hd.
          rewrite <-hm, <-hn in hd.
          split; intro hw; eapply hd;
          [eapply eq_sym, ring_sub_zero_iff | eapply ring_sub_zero_iff]; exact hw.
        }
        rewrite !hd; clear hd.
        rewrite field_zero, left_identity.
        (* The exponent of g₂ is (x₂ - x₁)/(x₂ - x₁) = 1. *)
        assert (hd : (x₁ * inv (x₁ - x₂) + x₂ * inv (x₂ - x₁)) =
          (x₂ - x₁) * inv (x₂ - x₁)).
        {
          field.
          pose proof (hb j k hg) as hd.
          rewrite <-hm, <-hn in hd.
          split; intro hw; eapply hd;
          [eapply eq_sym, ring_sub_zero_iff | eapply ring_sub_zero_iff]; exact hw.
        }
        rewrite !hd; clear hd.
        assert (hd : ((x₂ - x₁) * inv (x₂ - x₁)) = one).
        {
          field.
          pose proof (hb j k hg) as hd.
          rewrite <-hm, <-hn in hd.
          intro hw; eapply hd; eapply eq_sym, ring_sub_zero_iff; exact hw.
        }
        rewrite hd, field_one.
        reflexivity.
      Qed.

      (** Under the witness hypotheses, the honest transcript on randomness [us]
          equals the simulated transcript on randomness
          [generalised_construct_neq_response xs us c]. For the AND part this is
          [construct_and_commitment_shift]. For each pair it is
          [okamoto_commitment_shift] together with [neq_pair_relation], which
          identifies the Okamoto target with [gⱼ]. *)
      Lemma construct_neq_shift {n : nat} (xs : Vector.t F (2 + n))
        (gs hs : Vector.t G (2 + n)) (c : F)
        (ha : ∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i])
        (hb : ∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) :
        forall (us : Vector.t F ((2 + n) + ((2 + n) * (1 + n)))),
        generalised_construct_neq_conversations_real_transcript xs gs hs us c =
        generalised_construct_neq_conversations_simulator_transcript gs hs
          (generalised_construct_neq_response xs us c) c.
      Proof.
        intros us.
        destruct (splitat (2 + n) us) as (usl & usr) eqn:he.
        apply append_splitat in he; subst us.
        unfold generalised_construct_neq_conversations_real_transcript,
          generalised_construct_neq_conversations_simulator_transcript,
          generalised_construct_neq_commitment, generalised_construct_neq_response.
        rewrite !VectorSpec.splitat_append.
        rewrite rew_opp_l, pair_zip_unzip_id.
        f_equal; f_equal.
        (* AND commitments: the Schnorr commitment shift for each statement. *)
        + apply construct_and_commitment_shift; exact ha.
        (* Okamoto commitments, pair by pair: the Okamoto shift, then
           neq_pair_relation to rewrite the target. *)
        + apply VectorSpec.eq_nth_iff; intros i ? <-.
          rewrite !nth_zip_with, !map_fin.
          destruct ((generate_pairs_of_vector gs)[@i]) as (g₁ & g₂) eqn:hc.
          destruct ((generate_pairs_of_vector hs)[@i]) as (h₁ & h₂) eqn:hd.
          destruct ((generate_pairs_of_vector xs)[@i]) as (x₁ & x₂) eqn:hf.
          unfold okamoto_commitment, okamoto_simulator_protocol_commitment,
            okamoto_response, generalised_okamoto_simulator_protocol_commitment,
            generalised_okamoto_commitment, generalised_okamoto_response.
          etransitivity;
          [apply (okamoto_commitment_shift c 2 [gop g₁ g₂; gop h₁ h₂]
            [x₁ * inv (x₁ - x₂); inv (x₂ - x₁)]) |].
          f_equal; f_equal.
          symmetry; apply (neq_pair_relation gs hs xs ha hb i g₁ g₂ h₁ h₂ x₁ x₂ hc hd hf).
      Qed.

      (** Applying the AND response map with challenge [c] and then with [c'] is the
          response map with [c + c']. *)
      Lemma and_response_compose :
        forall (m : nat) (xs us : Vector.t F m) (c c' : F),
        @construct_and_conversations_schnorr_response F add mul m xs
          (@construct_and_conversations_schnorr_response F add mul m xs us c) c' =
        @construct_and_conversations_schnorr_response F add mul m xs us (c + c').
      Proof.
        induction m as [| m ih]; intros xs us c c'.
        + rewrite (vector_inv_0 xs), (vector_inv_0 us); reflexivity.
        + destruct (vector_inv_S xs) as (x & xs' & hx).
          destruct (vector_inv_S us) as (u & us' & hu).
          subst; specialize (ih xs' us' c c').
          unfold construct_and_conversations_schnorr_response in *; cbn in *.
          f_equal; [field | exact ih].
      Qed.

      (** The AND response map with challenge [zero] is the identity. *)
      Lemma and_response_zero :
        forall (m : nat) (xs us : Vector.t F m),
        @construct_and_conversations_schnorr_response F add mul m xs us zero = us.
      Proof.
        induction m as [| m ih]; intros xs us.
        + rewrite (vector_inv_0 us); reflexivity.
        + destruct (vector_inv_S xs) as (x & xs' & hx).
          destruct (vector_inv_S us) as (u & us' & hu).
          subst; specialize (ih xs' us').
          unfold construct_and_conversations_schnorr_response in *; cbn in *.
          f_equal; [field | exact ih].
      Qed.

      (** The NEQ response map composes additively in the challenge, as in
          [and_response_compose], on both the AND part and the Okamoto part. *)
      Lemma neq_response_compose {n : nat} (xs : Vector.t F (2 + n)) :
        forall (us : Vector.t F ((2 + n) + ((2 + n) * (1 + n)))) (c c' : F),
        generalised_construct_neq_response xs
          (generalised_construct_neq_response xs us c) c' =
        generalised_construct_neq_response xs us (c + c').
      Proof.
        intros us c c'.
        destruct (splitat (2 + n) us) as (usl & usr) eqn:he.
        apply append_splitat in he; subst us.
        unfold generalised_construct_neq_response.
        rewrite !VectorSpec.splitat_append, rew_opp_l, pair_zip_unzip_id.
        f_equal; [apply and_response_compose |].
        f_equal; f_equal.
        apply VectorSpec.eq_nth_iff; intros i ? <-.
        rewrite !nth_zip_with.
        destruct ((generate_pairs_of_vector xs)[@i]) as (x₁ & x₂).
        unfold okamoto_response, generalised_okamoto_response.
        destruct (vector_inv_S
          ((pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr))[@i]))
          as (a & v' & hv).
        destruct (vector_inv_S v') as (b & v'' & hv').
        rewrite (vector_inv_0 v'') in hv'; rewrite hv' in hv; rewrite hv; cbn.
        f_equal; [ring | f_equal; ring].
      Qed.

      (** The NEQ response map with challenge [zero] is the identity. *)
      Lemma neq_response_zero {n : nat} (xs : Vector.t F (2 + n)) :
        forall (us : Vector.t F ((2 + n) + ((2 + n) * (1 + n)))),
        generalised_construct_neq_response xs us zero = us.
      Proof.
        intros us.
        destruct (splitat (2 + n) us) as (usl & usr) eqn:he.
        apply append_splitat in he; subst us.
        unfold generalised_construct_neq_response.
        rewrite !VectorSpec.splitat_append.
        f_equal; [apply and_response_zero |].
        (* On the Okamoto part each pair's response with challenge zero is its
           randomness; then pair_unzip undoes pair_zip and the length cast cancels. *)
        assert (hz : zip_with (λ '(x₁, x₂) (us : t F 2),
            @okamoto_response F add mul [x₁ * inv (x₁ - x₂); inv (x₂ - x₁)] us zero)
           (generate_pairs_of_vector xs)
           (pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr)) =
           pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr)).
        {
          apply VectorSpec.eq_nth_iff; intros i ? <-.
          rewrite !nth_zip_with.
          destruct ((generate_pairs_of_vector xs)[@i]) as (x₁ & x₂).
          unfold okamoto_response, generalised_okamoto_response.
          destruct (vector_inv_S
            ((pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr))[@i]))
            as (a & v' & hv).
          destruct (vector_inv_S v') as (b & v'' & hv').
          rewrite (vector_inv_0 v'') in hv'; rewrite hv' in hv; rewrite hv; cbn.
          f_equal; [ring | f_equal; ring].
        }
        rewrite hz, pair_unzip_zip_id, rew_opp_r.
        reflexivity.
      Qed.

      (** Special honest-verifier zero knowledge as equality of distributions.
          Assume the witness hypotheses ([gs[i] ^ xs[i] = hs[i]] and pairwise
          distinct [xs]), and that [lf] has no duplicates and contains every field
          element. Then, for every challenge [c], the real transcript distribution
          is a permutation of the simulated one, so both give every transcript the
          same probability.

          Proof idea: [construct_neq_shift] writes the prover as the simulator
          composed with the response map [phi]. [phi] is a bijection with inverse
          the response map for [opp c] ([neq_response_compose],
          [neq_response_zero]), so it permutes the uniform product distribution
          ([repeat_uniform_bijection_perm]), and [bind_ret_perm] concludes. *)
      Theorem generalised_neq_special_honest_verifier_zkp_perm {n : nat} :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F),
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.NoDup lf -> (forall x : F, List.In x lf) ->
        Permutation
          (@generalised_neq_schnorr_distribution n lf Hlfn xs gs hs c)
          (@generalised_neq_simulator_distribution n lf Hlfn gs hs c).
      Proof.
        intros * ha hb hnd hall.
        change (Permutation
          (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
              ((2 + n) + ((2 + n) * (1 + n))))
            (fun us => Ret (generalised_construct_neq_conversations_real_transcript
              xs gs hs us c)))
          (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
              ((2 + n) + ((2 + n) * (1 + n))))
            (fun us => Ret (generalised_construct_neq_conversations_simulator_transcript
              gs hs us c)))).
        (* The bijection is the response map for c; its inverse is the response map
           for opp c. *)
        eapply bind_ret_perm with
          (phi := fun us => generalised_construct_neq_response xs us c).
        + apply (repeat_uniform_bijection_perm lf Hlfn _ _
            (fun us => generalised_construct_neq_response xs us (opp c)) hnd hall).
          * intros us.
            rewrite neq_response_compose.
            assert (hc : c + opp c = zero) by field.
            rewrite hc; apply neq_response_zero.
          * intros us.
            rewrite neq_response_compose.
            assert (hc : opp c + c = zero) by field.
            rewrite hc; apply neq_response_zero.
        + intros us p _. apply construct_neq_shift; assumption.
      Qed.

    End Proofs.
  End Neq.
End DL.
