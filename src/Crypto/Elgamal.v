(** * ElGamal Encryption in the Exponent *)

(** This file formalises (lifted, or ‘exponential’) ElGamal encryption over
    an abstract prime-order group and proves its basic correctness and
    homomorphic properties.

    The setting is a vector space [G] over a field [F] (in practice a cyclic
    group of prime order [q] written multiplicatively, with scalars in
    [Z/qZ]); [gop] is the group operation, [ginv] the inverse and
    [g ^ a] (i.e. [gpow g a]) scalar multiplication / exponentiation. The
    key pair is a secret key [x : F] and a public key [h = g ^ x]. A message
    [m : F] is encrypted in the exponent with randomness [r : F]:

    [[
      enc m r   = (g ^ r, g ^ m · h ^ r)
      dec (c₁, c₂) = c₂ · (c₁ ^ x)⁻¹
    ]]

    Decryption therefore recovers the group element [g ^ m], not [m]
    itself; recovering [m] requires a discrete-logarithm search over the
    (small) message space, which is done elsewhere (for example in the tally
    back-ends). The scheme is additively homomorphic: the component-wise
    product of two ciphertexts encrypts the sum of the messages, and
    multiplying by an encryption of zero ([re_enc]) re-randomises a
    ciphertext without changing its plaintext.

    Main results:

    - [dec_is_left_inv_of_enc]: decryption inverts encryption (up to the
      exponent lifting);
    - [dec_re_enc_left_inv]: re-encryption preserves the plaintext;
    - [additive_homomorphic_property]: [mul_cipher] is homomorphic for
      addition of plaintexts;
    - [ballot_encryption_decryption_raise_message] and
      [ballot_re_encryption_decryption_raise_message]: the same facts lifted
      point-wise to vectors of ciphertexts (‘ballots’).

    Only functional correctness is proved here; no semantic-security (IND-CPA)
    statement is made. These definitions are used by the proofs of correct
    encryption ([EncProof]), correct decryption ([DecProof]), the distributed
    variant ([DistElgamal]), the shuffle proofs and the e-voting tallies. *)
From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.

(** ** Parameters

    The section is parameterised by an abstract field [F] and a vector space
    [G] over it, followed by the key pair. *)
Section Elgamal.

  (** The scalar field [F] with its operations. Equality is Leibniz
      equality. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.

  (** The group [G], viewed as an [F]-vector space: [gid] is the identity,
      [ginv] the inverse, [gop] the group operation and [gpow] the scalar
      action (exponentiation). *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Hvec: @vector_space F (@eq F) zero one add mul sub
      div opp inv G (@eq G) gid ginv gop gpow}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.

  (** The key material: secret key [x], generator [g] and public key [h],
      together with the hypothesis [Hk] that [h = g ^ x]. Every lemma below
      depends on [Hk]. *)
  Context
    (x : F)
    (g h : G)
    (Hk : h = g^x).

  (** ** Encryption, decryption and ciphertext operations *)
  Section EncDecDef.

    (** [enc m r] is the ElGamal encryption of [g ^ m] under public key [h]
        with randomness [r]: the pair [(g ^ r, g ^ m · h ^ r)]. *)
    Definition enc (m : F) (r : F) : G * G :=
      (g^r, gop (g^m) (h^r)).

    (** [dec (c₁, c₂)] computes [c₂ · (c₁ ^ x)⁻¹] using the secret key [x].
        On an honest ciphertext it yields [g ^ m], the message lifted into
        the group. *)
    Definition dec (c : G * G) :=
      match c with
      |(c₁, c₂) => gop c₂ (ginv (c₁^x))
      end.

    (** [re_enc (c₁, c₂) r] re-randomises a ciphertext by multiplying it
        component-wise with [(g ^ r, h ^ r)], an encryption of the neutral
        message [0]. This is the operation applied by a mix server in a
        re-encryption shuffle. *)
    Definition re_enc (c : G * G) (r : F) : G * G :=
      match c with
      |(c₁, c₂) => (gop c₁ (g^r), gop c₂ (h^r))
      end.

    (** [mul_cipher] is the component-wise product of two ciphertexts, the
        homomorphic operation corresponding to addition of plaintexts. *)
    Definition mul_cipher (c₁ c₂ : G * G) : G * G :=
      match c₁, c₂ with
      |(c₁, d₁), (c₂, d₂) => (gop c₁ c₂, gop d₁ d₂)
      end.

  End EncDecDef.

  (** ** Ballots: vectors of ciphertexts

      A ballot is a length-[n] vector of ciphertexts (one per candidate or
      option). The operations below lift [enc], [dec], [re_enc] and
      [mul_cipher] point-wise to such vectors. *)
  Section BallotDef.

      (** [encrypted_ballot ms rs] encrypts the [i]-th message with the
          [i]-th randomness. *)
      Definition encrypted_ballot {n : nat}
        (ms rs : Vector.t F n) : Vector.t (G * G) n :=
        zip_with (fun m r => enc m r) ms rs.

      (** [decrypted_ballot cs] decrypts every component, yielding a vector
          of group elements [g ^ mᵢ]. *)
      Definition decrypted_ballot {n : nat}
        (cs : Vector.t (G * G) n) : Vector.t G n :=
        map (fun c => dec c) cs.

      (** [re_encryption_ballot cs rs] re-randomises every component of a
          ballot with fresh randomness. *)
      Definition re_encryption_ballot {n : nat}
        (cs : Vector.t (G * G) n) (rs : Vector.t F n) :
        Vector.t (G * G) n :=
        zip_with (fun c r => re_enc c r) cs rs.

      (** [mul_encrypted_ballots us vs] is the component-wise homomorphic
          product of two ballots; used to accumulate ballots into an
          encrypted tally. *)
      Definition mul_encrypted_ballots {n : nat}
        (us vs : Vector.t (G * G) n) : Vector.t (G * G) n :=
        zip_with (fun c₁ c₂ => mul_cipher c₁ c₂) us vs.

      (** [raise_message_gen ms] lifts each message into the group,
          [map (fun m => g ^ m) ms]; it is the expected result of decrypting
          [encrypted_ballot ms rs]. *)
      Definition raise_message_gen {n : nat}
        (ms : Vector.t F n) : Vector.t G n :=
        map (fun m => g^m) ms.

  End BallotDef.

  (** ** Correctness proofs *)
  Section Proofs.

    (** *** Single ciphertexts *)
    Section EncDecProof.

      (** Correctness of decryption: if [(c, d) = enc m r] then
          [dec (c, d) = g ^ m]. Proof: [d · (c ^ x)⁻¹ = g ^ m · g ^ (x r) ·
          (g ^ (r x))⁻¹], and commutativity of [F] cancels the last two
          factors. *)
      Lemma dec_is_left_inv_of_enc :
        forall (c d : G) (r m : F),
        (c, d) = enc m r -> g^m = dec (c, d).
      Proof.
        unfold enc, dec;
        intros ? ? ? ? H;
        inversion H; clear H.
        rewrite Hk.
        rewrite <- !(@vector_space_smul_associative_fmul F (@eq F)
          zero one add mul sub div
          opp inv G (@eq G) gid ginv gop gpow Hvec).
        setoid_rewrite <- (@monoid_is_associative G (@eq G) gop gid).
        rewrite <- commutative.
        rewrite (@commutative_ring_is_commutative F (@eq F)
          zero one opp add sub mul).
        rewrite (@group_is_right_inverse G (@eq G) gop gid ginv).
        rewrite left_identity.
        exact eq_refl.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
      Qed.

      (** Re-encryption preserves the plaintext: if [(c, d) = enc m r₁] and
          [(e, f) = re_enc (c, d) r₂] then [dec (e, f) = g ^ m]. The proof
          collects the randomness into [g ^ (x (r₁ + r₂))] and cancels it. *)
      Lemma dec_re_enc_left_inv :
        forall c d e f r₁ r₂ m,
        (c, d) = enc m r₁ ->
        (e, f) = re_enc (c, d) r₂ ->
        g^m = dec (e, f).
      Proof.
        unfold re_enc, enc, dec.
        intros ? ? ? ? ? ? ? H₁ H₂.
        inversion H₁; clear H₁.
        inversion H₂; clear H₂.
        rewrite Hk in * |- *.
        subst.
        remember (gop (g ^ r₁) (g ^ r₂) ^ x) as t.
        rewrite <- smul_distributive_fadd in Heqt.
        rewrite <- (@vector_space_smul_associative_fmul
          F (@eq F) zero one add mul sub div
          opp inv G (@eq G) gid ginv gop gpow) in Heqt.
        rewrite (@commutative_ring_is_commutative
          F (@eq F) zero one opp add sub mul) in Heqt.
        rewrite (@ring_is_left_distributive
          F (@eq F) zero one opp add sub mul) in Heqt.
        repeat rewrite smul_pow_up.
        assert (Ht : (gop (gop (g ^ m) (g ^ (x * r₁))) (g ^ (x * r₂)) =
              (gop (g ^ m) (gop (g ^ (x * r₁)) (g ^ (x * r₂)))))).
        rewrite <- (@monoid_is_associative G (@eq G) gop gid).
        reflexivity.
        typeclasses eauto.
        rewrite Ht; clear Ht.
        rewrite <- smul_distributive_fadd.
        rewrite <- (@monoid_is_associative G (@eq G) gop gid).
        rewrite Heqt.
        rewrite (@group_is_right_inverse G (@eq G) gop gid ginv).
        rewrite monoid_is_right_identity.
        reflexivity.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
      Qed.

      (** Additive homomorphism: if [(c, d) = enc m₁ r₁] and
          [(e, f) = enc m₂ r₂], then decrypting
          [mul_cipher (c, d) (e, f)] yields [g ^ (m₁ + m₂)]. The proof works
          entirely in the exponent: the product is [g ^ (m₁ + m₂ + x r₁ +
          x r₂)] times the inverse of [g ^ (x (r₁ + r₂))], and the field
          identities cancel the randomness terms. *)
      Lemma additive_homomorphic_property :
        forall c d e f r₁ r₂ m₁ m₂,
        (c, d) = enc m₁ r₁ ->
        (e, f) = enc m₂ r₂ ->
        g^(m₁ + m₂) = dec (mul_cipher (c, d) (e, f)).
      Proof.
        unfold re_enc, enc, dec, mul_cipher.
        intros ? ? ? ? ? ? ? ? H1 H2.
        inversion H1; clear H1;
        inversion H2; clear H2.
        rewrite Hk in * |- *.
        subst.
        remember (gop (g ^ r₁) (g ^ r₂) ^ x) as t.
        rewrite <- smul_distributive_fadd in Heqt.
        rewrite <- (@vector_space_smul_associative_fmul
          F (@eq F) zero one add mul sub div
          opp inv G (@eq G) gid ginv gop gpow) in Heqt.
        rewrite (@commutative_ring_is_commutative
          F (@eq F) zero one opp add sub mul) in Heqt.
        rewrite (@ring_is_left_distributive
          F (@eq F) zero one opp add sub mul) in Heqt.
        (* Turn the inverse of a power into a power with negated exponent
           and merge every factor into a single exponent. *)
        rewrite Heqt.
        rewrite connection_between_vopp_and_fopp.
        repeat rewrite smul_pow_up.
        repeat rewrite <- smul_distributive_fadd.
        assert (Htt: x * r₁ + m₂ = m₂ + x * r₁).
          rewrite commutative; reflexivity.
        rewrite associative.
        assert (Htv: m₁ + x * r₁ + m₂ = m₁ + (x * r₁ + m₂)).
          rewrite associative; reflexivity.
        rewrite Htv, Htt, associative.
        clear Htt; clear Htv; clear Heqt.
        (* The exponent is [m₁ + m₂ + (t + opp t)] with [t = x r₁ + x r₂],
           which simplifies to [m₁ + m₂]. *)
        assert(Htt: m₁ + m₂ + x * r₁ + x * r₂ + opp (x * r₁ + x * r₂) =
          m₁ + m₂ + (x * r₁ + x * r₂ + opp (x * r₁ + x * r₂))).
          repeat rewrite associative; reflexivity.
        rewrite Htt, field_zero_iff_right, right_identity;
        reflexivity.
        typeclasses eauto.
        typeclasses eauto.
        typeclasses eauto.
      Qed.

    End EncDecProof.

    (** *** Ballots *)
    Section BallotProof.
      (** Ballot-level correctness: if [cs = encrypted_ballot ms rs] then
          [decrypted_ballot cs = raise_message_gen ms]. By induction on the
          length [n], using [dec_is_left_inv_of_enc]-style reasoning on the
          head component. *)
      Lemma ballot_encryption_decryption_raise_message:
        forall (n : nat) (ms rs : Vector.t F n) (cs :  Vector.t (G * G) n),
        cs = encrypted_ballot ms rs ->
        raise_message_gen ms = decrypted_ballot cs.
      Proof.
        induction n.
        + intros ? ? cs ->.
          refine (match ms, rs with
            | nil _, nil _ => _
            end).
          reflexivity.
        + intros ? ? cs ->.
          pose proof (vector_inv_S ms) as (hms & tms & Hms).
          pose proof (vector_inv_S rs) as (hrs & trs & Hrs).
          rewrite Hms, Hrs; simpl.
          f_equal.
          rewrite Hk.
          repeat rewrite smul_pow_up,
          smul_pow_mul, <-associative, right_inverse,
          right_identity; reflexivity.
          apply IHn with  (rs := tl rs).
          unfold encrypted_ballot.
          rewrite Hrs; simpl.
          reflexivity.
      Qed.

      (** Ballot-level re-encryption correctness: encrypting [ms] with
          [rs₁] and then re-encrypting with [rs₂] still decrypts to
          [raise_message_gen ms]. By induction on [n]; the head case
          repeats the algebra of [dec_re_enc_left_inv]. *)
      Lemma ballot_re_encryption_decryption_raise_message :
        forall (n : nat) (ms rs₁ rs₂: Vector.t F n) cs₁ cs₂,
        cs₁ = encrypted_ballot ms rs₁ ->
        cs₂ = re_encryption_ballot cs₁ rs₂ ->
        raise_message_gen ms = decrypted_ballot cs₂.
      Proof.
        induction n.
        + intros ? ? ? ? ? Hcs₁ ->.
          rewrite Hcs₁; clear Hcs₁;
          clear cs₁.
          refine (match ms, rs₁, rs₂ with
            | nil _, nil _, nil _ => _
            end).
          reflexivity.
          (* Inductive step: split all three vectors into head and tail;
             the head goal is the single-ciphertext identity, the tail goal
             is the induction hypothesis. *)
        + intros ? ? ? ? ? Hcs₁ ->.
          rewrite Hcs₁; clear Hcs₁; clear cs₁.
          pose proof (vector_inv_S ms) as (hms & tms & Hms).
          pose proof (vector_inv_S rs₁) as (hrs₁ & trs₁ & Hrs₁).
          pose proof (vector_inv_S rs₂) as (hrs₂ & trs₂ & Hrs₂).
          rewrite Hms, Hrs₁, Hrs₂; simpl.
          f_equal.
          rewrite Hk.
          repeat rewrite smul_pow_up,
          smul_pow_mul.
          assert (Ht :
            (gop (gop (g ^ hms) (g ^ (x * hrs₁)))
                (g ^ (x * hrs₂))) =
            (gop (g ^ hms)
                (gop (g ^ (x * hrs₁))
                      (g ^ (x * hrs₂))))).
          rewrite <- (@monoid_is_associative G (@eq G) gop gid).
          reflexivity.
          typeclasses eauto.
          assert (Htv : hrs₂ * x = x * hrs₂).
          rewrite commutative;
          reflexivity.
          rewrite <-Htv in Ht.
          rewrite Ht.
          clear Ht.
          rewrite <- smul_distributive_fadd.
          rewrite <- (@monoid_is_associative G (@eq G) gop gid).
          (* Key identity: [(g ^ r₁ · g ^ r₂) ^ x = g ^ (r₁ x) · g ^ (r₂ x)],
             i.e. the mask removed by decryption equals the mask added by
             encryption plus re-encryption. *)
          assert (Htt: gop (g ^ hrs₁) (g ^ hrs₂) ^ x =
            gop (g ^ (hrs₁ * x)) (g ^ (hrs₂ * x))).
          rewrite <- smul_distributive_fadd.
          rewrite <- (@vector_space_smul_associative_fmul
              F (@eq F) zero one add mul sub div
              opp inv G (@eq G) gid ginv gop gpow).
          rewrite (@commutative_ring_is_commutative F (@eq F) zero one opp add sub mul).
          rewrite (@ring_is_left_distributive F (@eq F) zero one opp add sub mul).
          rewrite (@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          assert (Hwt₁: x * hrs₁ = hrs₁ * x).
          rewrite commutative; reflexivity.
          rewrite Hwt₁.
          assert (Hwt₂: x * hrs₂ = hrs₂ * x).
          rewrite commutative; reflexivity.
          rewrite Hwt₂.
          reflexivity.
          typeclasses eauto.
          typeclasses eauto.
          typeclasses eauto.
          typeclasses eauto.
          rewrite Htt.
          rewrite <- (@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          assert (Hwt₁: x * hrs₁ = hrs₁ * x).
          rewrite commutative; reflexivity.
          rewrite <-Hwt₁.
          assert (Hwt₂: x * hrs₂ = hrs₂ * x).
          rewrite commutative; reflexivity.
          rewrite <-Hwt₂.
          rewrite right_inverse, right_identity;
          reflexivity.
          typeclasses eauto.
          typeclasses eauto.
          (* Tail: the induction hypothesis on the tails. *)
          exact (IHn tms trs₁ trs₂
            (encrypted_ballot tms trs₁)
            (re_encryption_ballot
              (encrypted_ballot tms trs₁) trs₂)
            eq_refl eq_refl).
      Qed.

    End BallotProof.

  End Proofs.

End Elgamal.
