(** * Proof of Correct ElGamal Decryption *)

(** This file builds a non-interactive-ready Sigma protocol showing that a
    claimed plaintext is the correct decryption of an ElGamal ciphertext. It
    is the standard Chaum–Pedersen decryption proof used by Helios, Belenios
    and ElectionGuard to publish a verifiable tally.

    Setting: generator [g], public key [h = g ^ x], ciphertext
    [(c₁, c₂) = (g ^ r, m₀ · h ^ r)] (see [Elgamal]) and a claimed decryption
    [m : G] (a group element, e.g. [g ^ tally]). The decryptor proves
    knowledge of [x] such that

    [[
      g ^ x = h   ∧   c₁ ^ x = c₂ · m⁻¹
    ]]

    The second equation says exactly that [m = c₂ · (c₁ ^ x)⁻¹], i.e. that
    [m] is the decryption of [(c₁, c₂)] under the secret key matching [h].
    This is the Chaum–Pedersen statement of [ChaumPedersen] for the tuple
    [(g, h, c₁, c₂ · m⁻¹)], and every definition here is a wrapper around
    the corresponding [ChaumPedersen] definition with that tuple; note the
    argument order [g c₁ h (c₂ · m⁻¹)] in the wrappers, which pairs the bases
    [g], [c₁] with the values [h], [c₂ · m⁻¹].

    Results: an explicit two-equation characterisation of the verifier
    ([decryption_proof_accepting_conversations_accept] and the reject
    variants), completeness ([construct_decryption_proof_elgamal_real_completeness]),
    special soundness ([special_soundness_construct_decryption_proof_elgamal],
    which extracts [y] satisfying both equations), and special honest-verifier
    zero-knowledge (weak verdict-level form and the strong permutation form).
    A vector version proves the decryption of a whole vector of ciphertexts
    with one proof per ciphertext, as needed for a per-candidate tally. *)
From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import Util.
From ExtLib Require Import Monad.
From Sigma Require Import Sigma ChaumPedersen.

Import MonadNotation
  VectorNotations EqNotations.

#[local] Open Scope monad_scope.

(** ** Parameters *)
Section DL.
  (** The scalar field [F] with decidable equality. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] with decidable equality. *)
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

  (** [(a; c; r)] builds a transcript from announcement, challenge and
      response vectors. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** Decryption proof *)
  Section DecProof.
    (** *** Definitions *)
    Section Def.

      (** Honest prover for secret key [x], ciphertext [cp = (c₁, c₂)],
          randomness [u] and challenge [c]: the Chaum–Pedersen transcript
          [([g ^ u; c₁ ^ u]; [c]; [u + c · x])]. Only [c₁] is needed to
          compute it. *)
      Definition construct_decryption_proof_elgamal_real
        (x : F) (g : G) (cp : G * G) (u c : F) :  @sigma_proto F G 2 1 1 :=
        @construct_cp_conversations_schnorr F add mul G gpow x
        g (fst cp) u c.

      (** Simulator for the statement [(g, h, (c₁, c₂), m)]: the
          Chaum–Pedersen simulator on [(g, c₁, h, c₂ · m⁻¹)] with response [u]
          and challenge [c]. *)
      Definition construct_decryption_proof_elgamal_simulator
        (g h : G) (c₁ c₂ : G) (m : G) (u c : F) :  @sigma_proto F G 2 1 1 :=
        @construct_cp_conversations_simulator F opp G gop gpow
        g c₁ h (gop c₂ (ginv m)) u c.

      (** Verifier: accepts [([a₁; a₂]; [c]; [r])] iff
          [g ^ r = a₁ · h ^ c] and [c₁ ^ r = a₂ · (c₂ · m⁻¹) ^ c]. *)
      Definition decryption_proof_accepting_conversations
        (g h : G) (c₁ c₂ : G) (m : G)
        (s : @sigma_proto F G 2 1 1) : bool :=
        @generalised_cp_accepting_conversations F G gop gpow
          Gdec g c₁ h (gop c₂ (ginv m)) s.

      (** Distribution of honest transcripts, with [u] uniform over [lf].
          It depends only on [x], [g] and [c₁]. *)
      Definition construct_decryption_proof_elgamal_real_distribution
        (lf : list F) (Hlfn : lf <> List.nil) (x : F)
        (g c₁ : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_cp_schnorr_distribution F add mul G gpow
          lf Hlfn x g c₁ c.

      (** Distribution of simulated transcripts, with the response uniform
          over [lf]. (The name drops the final ‘l’ of ‘elgamal’.) *)
      Definition construct_decryption_proof_elgama_simulator_distribution
        (lf : list F) (Hlfn : lf <> List.nil) (g h : G)
        (c₁ c₂ : G) (m : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_cp_simulator_distribution  F opp G gop
        gpow lf Hlfn g c₁ h (gop c₂ (ginv m)) c.

      (** Honest proofs for a vector of [n] ciphertexts, using the same
          secret key [x], with the [i]-th proof built from the [i]-th
          randomness and the [i]-th challenge. *)
      Fixpoint construct_decryption_proof_elgamal_real_vector {n : nat}
        (x : F) (g : G) (cps : Vector.t (G * G) n) (us cs : Vector.t F n) :
        Vector.t (@sigma_proto F G 2 1 1) n.
      Proof.
        destruct n as [|n].
        +
          exact [].
        +
          destruct (vector_inv_S cps) as (cph & cpt & _).
          destruct (vector_inv_S us) as (ush & ust & _).
          destruct (vector_inv_S cs) as (csh & cst & _).
          exact ((construct_decryption_proof_elgamal_real x g cph ush csh) ::
            (construct_decryption_proof_elgamal_real_vector _ x g cpt ust cst)).
      Defined.

      (** Verifier for a vector of decryption proofs: accepts iff the [i]-th
          proof is accepting for the [i]-th ciphertext and claimed plaintext,
          for every [i] (the empty vector is accepted). *)
      Fixpoint decryption_proof_accepting_conversations_vector {n : nat} (g h : G)
        (cps : Vector.t (G * G) n) (ms : Vector.t G n)
        (pf : Vector.t (@sigma_proto F G 2 1 1) n ) : bool.
      Proof.
        destruct n as [|n].
        +
          exact true.
        +
          destruct (vector_inv_S cps) as ((c₁, c₂) & cpst & _).
          destruct (vector_inv_S ms) as (msh & mst & _).
          destruct (vector_inv_S pf) as (pfh & pft & _).
          exact ((decryption_proof_accepting_conversations g h c₁ c₂ msh pfh) &&
          (decryption_proof_accepting_conversations_vector n g h cpst mst pft)).
      Defined.

    End Def.

    (** *** Proofs *)

    (** The first six theorems characterise the boolean verifier by its two
        group equations. *)
    Section Proofs.

      (** Acceptance implies [g ^ r = a₁ · h ^ c] and
          [c₁ ^ r = a₂ · (c₂ · m⁻¹) ^ c]. *)
      Theorem decryption_proof_accepting_conversations_accept_forward :
        ∀ (g h : G) (c₁ c₂ : G) (m : G)  (a₁ a₂ : G) (c r : F),
        decryption_proof_accepting_conversations g h c₁ c₂ m
        ([a₁; a₂]; [c]; [r]) = true ->
        g ^ r = gop a₁ (h ^ c) ∧ c₁ ^ r = gop a₂ (gop c₂ (ginv m) ^ c).
      Proof.
        intros * ha.
        cbn in ha.
        eapply andb_true_iff in ha.
        rewrite !dec_true in ha.
        exact ha.
      Qed.

      (** The two verification equations imply acceptance. *)
      Theorem decryption_proof_accepting_conversations_accept_backward :
        ∀ (g h : G) (c₁ c₂ : G) (m : G)  (a₁ a₂ : G) (c r : F),
        g ^ r = gop a₁ (h ^ c) ->  c₁ ^ r = gop a₂ (gop c₂ (ginv m) ^ c) ->
        decryption_proof_accepting_conversations g h c₁ c₂ m
        ([a₁; a₂]; [c]; [r]) = true.
      Proof.
        intros * ha hb.
        cbn. eapply andb_true_iff.
        rewrite !dec_true.
        split; assumption.
      Qed.

      (** Acceptance is equivalent to the two verification equations. *)
      Theorem decryption_proof_accepting_conversations_accept :
        ∀ (g h : G) (c₁ c₂ : G) (m : G)  (a₁ a₂ : G) (c r : F),
        decryption_proof_accepting_conversations g h c₁ c₂ m
        ([a₁; a₂]; [c]; [r]) = true <->
        g ^ r = gop a₁ (h ^ c) ∧ c₁ ^ r = gop a₂ (gop c₂ (ginv m) ^ c).
      Proof.
        intros *; split; intro ha.
        eapply decryption_proof_accepting_conversations_accept_forward;
        assumption.
        eapply decryption_proof_accepting_conversations_accept_backward;
        destruct ha as (hal & har); assumption.
      Qed.

      (** Rejection implies that one of the two verification equations
          fails. *)
      Theorem decryption_proof_accepting_conversations_reject_forward :
        ∀ (g h : G) (c₁ c₂ : G) (m : G)  (a₁ a₂ : G) (c r : F),
        decryption_proof_accepting_conversations g h c₁ c₂ m
        ([a₁; a₂]; [c]; [r]) = false ->
        g ^ r ≠ gop a₁ (h ^ c) ∨ c₁ ^ r ≠ gop a₂ (gop c₂ (ginv m) ^ c).
      Proof.
        intros * ha.
        cbn in ha.
        eapply andb_false_iff in ha.
        rewrite !dec_false in ha.
        exact ha.
      Qed.

      (** Failure of either verification equation implies rejection. *)
      Theorem decryption_proof_accepting_conversations_reject_backward :
        ∀ (g h : G) (c₁ c₂ : G) (m : G)  (a₁ a₂ : G) (c r : F),
        (g ^ r ≠ gop a₁ (h ^ c) ∨ c₁ ^ r ≠ gop a₂ (gop c₂ (ginv m) ^ c)) ->
        decryption_proof_accepting_conversations g h c₁ c₂ m
        ([a₁; a₂]; [c]; [r]) = false.
      Proof.
        intros * [ha | ha]; cbn;
        eapply andb_false_iff;
        rewrite !dec_false;
        [left | right]; assumption.
      Qed.

      (** Rejection is equivalent to the failure of one of the two
          verification equations. *)
      Theorem decryption_proof_accepting_conversations_reject :
        ∀ (g h : G) (c₁ c₂ : G) (m : G)  (a₁ a₂ : G) (c r : F),
        (g ^ r ≠ gop a₁ (h ^ c) ∨ c₁ ^ r ≠ gop a₂ (gop c₂ (ginv m) ^ c)) <->
        decryption_proof_accepting_conversations g h c₁ c₂ m
        ([a₁; a₂]; [c]; [r]) = false.
      Proof.
        intros *; split; intro ha.
        eapply decryption_proof_accepting_conversations_reject_backward;
        assumption.
        eapply decryption_proof_accepting_conversations_reject_forward;
        assumption.
      Qed.

      (** From here on [G] is an [F]-vector space, and the [field] tactic is
          registered for [F]. *)
      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.

      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** Completeness: if [g ^ x = h] and [c₁ ^ x = c₂ · m⁻¹] (i.e. [m] is
          the correct decryption), then the honest transcript is accepted for
          every [u] and [c]. The first equation is Schnorr completeness;
          the second is [c₁ ^ (u + c · x) = c₁ ^ u · (c₁ ^ x) ^ c]. *)
      Lemma construct_decryption_proof_elgamal_real_completeness
        (x : F)
        (g h m c₁ c₂ : G)
        (R : g^x = h ∧ c₁^x = gop c₂ (ginv m)) :
        forall (u c : F),
        decryption_proof_accepting_conversations g h c₁ c₂ m
          (construct_decryption_proof_elgamal_real x g (c₁, c₂) u c) = true.
      Proof.
        intros *. cbn.
        eapply andb_true_iff; split;
        rewrite dec_true.
        +
          destruct R as [ra rb].
          pose proof (@schnorr_completeness F zero one add mul sub div opp inv
            G gid ginv gop gpow Gdec Hvec g h x (eq_sym ra) u c) as ha.
          cbn in ha. rewrite dec_true in ha.
          exact ha.
        +
          destruct R as [ra rb].
          rewrite <-rb.
          assert (Hg : (c₁ ^ x) ^ c = (c₁ ^ (x * c))).
          rewrite smul_pow_up.
          reflexivity.
          rewrite Hg; clear Hg.
          assert (Hxc : x * c = c * x) by field.
          rewrite Hxc; clear Hxc.
          rewrite <- (@vector_space_smul_distributive_fadd F (@eq F)
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow);
          subst; [exact eq_refl
          | assumption].
      Qed.

      (** Simulator completeness: simulated transcripts are accepted for
          every statement, including false decryption claims. Each equation
          reduces to [g ^ u · h ^ (-c) · h ^ c = g ^ u]. *)
      Lemma construct_decryption_proof_elgamal_simulator_completeness
        (g h m c₁ c₂ : G) :
        forall (u c : F),
        decryption_proof_accepting_conversations g h c₁ c₂ m
          (construct_decryption_proof_elgamal_simulator g h c₁ c₂ m u c) = true.
      Proof.
        intros *. cbn.
        eapply andb_true_iff; split;
        rewrite dec_true.
        +
          rewrite <-associative.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto.
        +
          remember (gop c₂ (ginv m)) as ct.
          rewrite <-associative.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto.
      Qed.

      (** Special soundness: from two accepting transcripts with the same
          announcement and distinct challenges [c₁ ≠ c₂] one extracts
          [y = (r₁ - r₂) · (c₁ - c₂)⁻¹] with [g ^ y = h] and
          [cp₁ ^ y = cp₂ · m⁻¹]. Consequently an accepting proof shows (in
          the knowledge-soundness sense) that [m] is the correct decryption
          of [(cp₁, cp₂)] under the key matching [h]. The proof repeats the
          algebra of [generalise_eq_sigma_soundness] for each equation. *)
      Lemma special_soundness_construct_decryption_proof_elgamal (g h m cp₁ cp₂ : G) :
        forall (a : Vector.t G 2) (c₁ r₁ c₂ r₂ : F),
        c₁ <> c₂ ->
        decryption_proof_accepting_conversations g h cp₁ cp₂ m
          (a; [c₁]; [r₁]) = true ->
        decryption_proof_accepting_conversations g h cp₁ cp₂ m
          (a; [c₂]; [r₂]) = true ->
        ∃ y : F, g^y = h ∧ cp₁^y = gop cp₂  (ginv m).
      Proof.
        intros * ha hb hc.
        cbn in hb, hc.
        destruct (vector_inv_S a) as (ah & atl & hd).
        destruct (vector_inv_S atl) as (ahh & atll & he).
        subst.
        eapply andb_true_iff in hb, hc.
        rewrite !dec_true in hb, hc.
        destruct hc as (hcl & hcr).
        destruct hb as (hbl & hbr).
        (* Both equations use the same extracted witness. *)
        exists ((r₁ - r₂) * inv (c₁ - c₂)).
        split.
        +
          (* First equation [g ^ y = h]: divide the two Schnorr equations to
             cancel the announcement [ah], then raise to
             [(c₁ - c₂)⁻¹]. *)
          eapply f_equal with (f := ginv) in hcl.
          rewrite connection_between_vopp_and_fopp in hcl.
          rewrite group_inv_flip  in hcl.
          rewrite commutative in hcl.
          pose proof (@rewrite_gop G gop _ _ _ _ hbl hcl) as Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          assert (Hwt : (gop ah (h ^ c₁))= (gop (h ^ c₁) ah)).
          rewrite commutative; reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
          in Hcom.
          assert (Hwt : (gop ah (gop (ginv ah) (ginv (h ^ c₂)))) =
           (ginv (h ^ c₂))).
          rewrite associative.
          rewrite group_is_right_inverse,
          monoid_is_left_idenity;
          reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          rewrite connection_between_vopp_and_fopp in Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          apply f_equal with (f := fun x => x^(inv (c₁ + opp c₂)))
          in Hcom.
          rewrite !smul_pow_up in Hcom.
          assert (Hw : (c₁ + opp c₂) * inv (c₁ + opp c₂) =
          (inv (c₁ + opp c₂) * (c₁ + opp c₂))).
          rewrite commutative; reflexivity.
          rewrite Hw in Hcom; clear Hw.
          rewrite field_is_left_multiplicative_inverse in Hcom.
          pose proof vector_space_field_one as Hone.
          unfold is_field_one in Hone.
          specialize (Hone h).
          rewrite Hone in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          exact Hcom.
          intros Hf.
          pose proof ring_neq_sub_neq_zero c₁ c₂ ha as Hw.
          apply Hw.
          rewrite ring_sub_definition.
          exact Hf.
          all:typeclasses eauto.
        +
          (* Second equation [cp₁ ^ y = ct] with [ct = cp₂ · m⁻¹]: the same
             computation with base [cp₁]. *)
          cbn in * |- .
          remember (gop cp₂ (ginv m)) as ct.
          eapply f_equal with (f := ginv) in hcr.
          rewrite connection_between_vopp_and_fopp in hcr.
          rewrite group_inv_flip  in hcr.
          rewrite commutative in hcr.
          pose proof (@rewrite_gop G gop _ _ _ _ hbr hcr) as Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          assert (Hwt : (gop ahh (ct ^ c₁)) = (gop (ct ^ c₁) ahh)).
          rewrite commutative; reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
          in Hcom.
          assert (Hwt : (gop ahh (gop (ginv ahh) (ginv (ct ^ c₂)))) =
           (ginv (ct ^ c₂))).
          rewrite associative.
          rewrite group_is_right_inverse,
          monoid_is_left_idenity;
          reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          rewrite connection_between_vopp_and_fopp in Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          apply f_equal with (f := fun x => x^(inv (c₁ + opp c₂)))
          in Hcom.
          rewrite !smul_pow_up in Hcom.
          assert (Hw : (c₁ + opp c₂) * inv (c₁ + opp c₂) =
          (inv (c₁ + opp c₂) * (c₁ + opp c₂))).
          rewrite commutative; reflexivity.
          rewrite Hw in Hcom; clear Hw.
          rewrite field_is_left_multiplicative_inverse in Hcom.
          pose proof vector_space_field_one as Hone.
          unfold is_field_one in Hone.
          specialize (Hone ct).
          rewrite Hone in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          exact Hcom.
          intros Hf.
          pose proof ring_neq_sub_neq_zero c₁ c₂ ha as Hw.
          apply Hw.
          rewrite ring_sub_definition.
          exact Hf.
          all:typeclasses eauto.
      Qed.

      (** Special honest-verifier zero-knowledge, weak form: under the
          relation, honest and simulated distributions agree after mapping
          each transcript to the verifier’s verdict. *)
      Lemma construct_decryption_proof_elgamal_special_honest_verifier_zkp
        (x : F)
        (g h m c₁ c₂ : G)
        (R : g^x = h ∧ c₁^x = gop c₂ (ginv m)) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.map (fun '(a, p) =>
          (decryption_proof_accepting_conversations g h c₁ c₂ m a, p))
          (construct_decryption_proof_elgamal_real_distribution lf Hlfn x g c₁ c) =
        List.map (fun '(a, p) =>
          (decryption_proof_accepting_conversations g h c₁ c₂ m a, p))
          (construct_decryption_proof_elgama_simulator_distribution lf Hlfn g h c₁ c₂ m c).
      Proof.
        intros *.
        eapply generalised_cp_special_honest_verifier_zkp.
        exact R.
      Qed.

    (** Completeness for vectors: if [g ^ x = h] and, for every [i], the
        [i]-th claimed plaintext [msᵢ] satisfies
        [fst cpsᵢ ^ x = snd cpsᵢ · msᵢ⁻¹], then the vector of honest proofs
        is accepted by [decryption_proof_accepting_conversations_vector], for
        all randomness [us] and challenges [cs]. By induction on [n]. *)
    Theorem decryption_proof_accepting_conversations_vector_completeness :
      ∀ (n : nat) (x : F) (g h : G)
      (cps : Vector.t (G * G) n) (ms : Vector.t G n) (us cs : Vector.t F n),
      (g^x = h) -> (∀ (i : Fin.t n), (fst (Vector.nth cps i))^x =
      gop (snd (Vector.nth cps i)) (ginv ((Vector.nth ms i)))) ->
      decryption_proof_accepting_conversations_vector g h
        cps ms (construct_decryption_proof_elgamal_real_vector x g cps us cs) = true.
    Proof.
      induction n as [|n ihn].
      +
        intros * ha hb.
        reflexivity.
      +
        intros * ha hb.
        destruct (vector_inv_S cps) as ((c₁, c₂) & cpst & hc).
        destruct (vector_inv_S ms) as (msh & mst & hd).
        destruct (vector_inv_S us) as (ush & ust & he).
        destruct (vector_inv_S cs) as (csh & cst & hf).
        subst. cbn.
        eapply Bool.andb_true_iff. split.
        eapply construct_decryption_proof_elgamal_real_completeness.
        ++
          specialize (hb Fin.F1).
          cbn in hb.
          exact (conj eq_refl hb).
        ++
          eapply ihn;
          [exact eq_refl | ].
          intro f. exact (hb (Fin.FS f)).
    Qed.

      (** Special honest-verifier zero-knowledge, strong form: if
          [u ↦ u + c · x] permutes [lf], the honest and simulated transcript
          distributions are permutations of each other. *)
      Theorem construct_decryption_proof_elgamal_special_honest_verifier_zkp_perm
        (x : F) (g h m c₁ c₂ : G) (R : g^x = h ∧ c₁^x = gop c₂ (ginv m)) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        Permutation (List.map (fun u => u + c * x) lf) lf ->
        Permutation
          (construct_decryption_proof_elgamal_real_distribution lf Hlfn x g c₁ c)
          (construct_decryption_proof_elgama_simulator_distribution lf Hlfn g h c₁ c₂ m c).
      Proof.
        intros * hp.
        eapply generalised_cp_special_honest_verifier_zkp_perm; [exact R | exact hp].
      Qed.

      (** Special honest-verifier zero-knowledge when [lf] enumerates the
          field without duplicates. *)
      Theorem construct_decryption_proof_elgamal_special_honest_verifier_zkp_enum
        (x : F) (g h m c₁ c₂ : G) (R : g^x = h ∧ c₁^x = gop c₂ (ginv m)) :
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.NoDup lf -> (forall y : F, List.In y lf) ->
        Permutation
          (construct_decryption_proof_elgamal_real_distribution lf Hlfn x g c₁ c)
          (construct_decryption_proof_elgama_simulator_distribution lf Hlfn g h c₁ c₂ m c).
      Proof.
        intros * hnd hall.
        eapply construct_decryption_proof_elgamal_special_honest_verifier_zkp_perm; [exact R |].
        eapply enumerates_perm_map with (psi := fun u => u - c * x);
        [exact hnd | exact hall | intros u; field | intros u; field].
      Qed.

    End Proofs.
  End DecProof.
End DL.
