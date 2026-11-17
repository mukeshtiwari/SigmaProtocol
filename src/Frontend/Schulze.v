(** * Receipt-free Schulze ballots, version 1: pairwise bits with position consistency

    This file formalises the voter side of a receipt-free encrypted
    preferential ballot for the Schulze method (Schulze 2011). The tally
    side, in which trustees certify the Schulze winner on the encrypted
    pairwise margins without decrypting them, is in [Backend/SchulzeTally.v].
    Because individual ballots and the margins are never decrypted, a voter
    cannot be identified through a pattern of preferences (the so-called
    Italian attack), which is what _receipt-free_ refers to here.

    _Ballot encoding._ For [m] candidates the voter chooses a position
    [s_i ∈ {0, …, m}] for every candidate [i]; smaller positions are
    preferred, equal positions are ties (a weak ranking), and position [m]
    can be used for unranked candidates. The ballot contains:

    - for every candidate [i], the ciphertext [Enc(s_i)] and a membership
      proof that [s_i ∈ {0, …, m}];
    - for every ordered pair [(i, j)] (including [i = j]), the ciphertext
      [Enc(b_ij)] of the preference bit [b_ij = 1] iff [s_i < s_j], a bit
      proof [b_ij ∈ {0, 1}], and a membership proof for the homomorphic
      combination
[[
        Enc(b_ij) ^ K · Enc(δ_ij) = Enc(K · b_ij + δ_ij),   K = 2m + 1,
]]
      in the set [{-m, …, 0} ∪ {K+1, …, K+m}], where
      [Enc(δ_ij) = Enc(s_j) · Enc(s_i)⁻¹] is computed by the verifier from
      the position ciphertexts (it is not part of the ballot; the voter
      knows its randomness [r_j - r_i]).

    Here [Enc] is exponential ElGamal, [Enc(v; r) = (g ^ r, g ^ v · h ^ r)].

    _Why the shift by K._ The statement to prove for a pair is the
    disjunction of conjunctions
[[
      (b_ij = 1 ∧ δ_ij ∈ {1, …, m}) ∨ (b_ij = 0 ∧ δ_ij ∈ {-m, …, 0}).
]]
    The generic OR/AND combinators of [Crypto/OrSigmaGen.v] and
    [Crypto/AndSigmaGen.v] only compose Schnorr statements over a single
    group, so this cannot be built from them directly. Instead, given
    [b_ij ∈ {0, 1}] (bit proof) and [δ_ij ∈ [-m, m] ] (both positions are in
    [0, m]), the value [K · b_ij + δ_ij] lies in [{-m, …, 0}] exactly when
    the second disjunct holds and in [{K+1, …, K+m}] exactly when the first
    holds, because [K = 2m + 1] separates the two ranges. The disjunction
    is therefore one set-membership proof, and every proof of the ballot is
    an instance of the CDS-style disjunctive encryption proof of
    [Crypto/EncProof.v] (the bit proof is literally the approval-vote proof
    of [Frontend/Approval.v]).

    _Results._

    - Completeness: [ballot_valid] (interactive) and [nizk_ballot_valid]
      (Fiat–Shamir with one hashed challenge per ballot).
    - Special soundness: [ballot_sound] extracts, from two accepting
      ballots with equal ciphertexts and announcements and different
      challenges in every proof, positions [s ∈ [0, m]^m] such that every
      pairwise ciphertext decrypts to [g ^ [s_i < s_j] ]. Hypotheses:
      exponentiation in base [g] is injective ([exp_injective]) and the
      field has characteristic above [4m + 2] ([natF_injective]); both hold
      for a prime-order group with [q > 4m + 2].
    - Aggregation: [aggregate_margins_enc] and [cdec_aggregate] show that
      the product of the bit ciphertexts of all ballots encrypts the
      pairwise margin matrix [D_ij = number of ballots with s_i < s_j].
    - Special honest-verifier zero knowledge: [ballot_zk] shows that the
      proofs of an honest ballot are distributed (as a list-based
      distribution, up to permutation) exactly as the output of a simulator
      that sees only the ciphertexts and the challenges.

    The batched variant [Frontend/SchulzeBatched.v] (version 2) and the
    simplified variant [Frontend/SchulzeSimple.v] (version 3) replace the
    [m²] membership proofs by Pedersen-committed linear and zero arguments
    and are much smaller; they reuse the ciphertext algebra and some
    lemmas of this file. *)
From Stdlib Require Import Setoid
  setoid_ring.Field Psatz Vector Utf8 Fin Lia Arith Bool.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import
  Util.
From Crypto Require Import
  Elgamal EncProof Sigma.
From Frontend Require Import Approval.
From Probability Require Import Prob Distr.
From Stdlib Require Import Permutation.
Import VectorNotations EqNotations.

(** ** Parameters

    A field [F] of exponents and a group [G], with decidable equalities.
    [natF] maps a natural number [k] to the field element [1 + … + 1]. *)
Section Schulze.

  (** The exponent field. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group of ciphertext components. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.

  (** [(a; c; r)] is a Sigma transcript (announcement, challenges, responses). *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).
  (** [natF k] is [k] as a field element. *)
  Local Notation natF := (nat_to_F zero one add).

  (** ** Definitions *)

  (** *** Ciphertext algebra

      ElGamal ciphertexts are pairs in [G × G]; the group operations are
      lifted componentwise. *)
  Section Definitions.

    (** [cmul a b] is the componentwise product (homomorphic addition of
        plaintexts). *)
    Definition cmul (a b : G * G) : G * G :=
      (gop (fst a) (fst b), gop (snd a) (snd b)).
    (** [cinv a] is the componentwise inverse (negation of the plaintext). *)
    Definition cinv (a : G * G) : G * G := (ginv (fst a), ginv (snd a)).
    (** [cpow a k] raises both components to [k] (scales the plaintext by [k]). *)
    Definition cpow (a : G * G) (k : F) : G * G := (fst a ^ k, snd a ^ k).
    (** [cid] is the trivial ciphertext [(1, 1)], the encryption of [0] with
        randomness [0]. *)
    Definition cid : G * G := (gid, gid).
    (** [ceqb a b] decides equality of ciphertexts. *)
    Definition ceqb (a b : G * G) : bool :=
      match Gdec (fst a) (fst b), Gdec (snd a) (snd b) with
      | left _, left _ => true
      | _, _ => false
      end.
    (** [cdec x a] decrypts [a = (a₁, a₂)] with secret key [x]: it returns
        [a₂ · (a₁ ^ x)⁻¹], which is [g ^ v] for an encryption of [v]
        ([cdec_enc]). *)
    Definition cdec (x : F) (a : G * G) : G := gop (snd a) (ginv (fst a ^ x)).

    (** *** Set membership of an ElGamal plaintext

        The disjunctive encryption proof of [Crypto/EncProof.v] over a list
        [ms] of [n] group elements: [cp] encrypts one of [ms], that is,
        [∃ r k, cp = (g ^ r, ms_k · h ^ r)]. *)

    (** A membership proof over [n] messages is a Sigma transcript with [n]
        announcements, [1 + n] challenges (the main challenge followed by the
        branch challenges) and [n] responses. *)
    Definition membership_proof (n : nat) : Type :=
      @sigma_proto F (G * G) n (S n) n.

    (** Verifier of the membership proof: all [n] Chaum–Pedersen branches
        accept and the branch challenges add up to the main challenge. *)
    Definition verify_membership {n : nat} (g h : G) (ms : Vector.t G n)
      (cp : G * G) (pf : membership_proof n) : bool :=
      @generalised_accepting_encryption_proof_elgamal F zero add Fdec
        G ginv gop gpow Gdec n ms g h cp pf.

    (** Honest prover: [cp] encrypts [ms[rindex] ] with randomness [r]. The
        prover randomness [uscs] holds [2 + n] commitment exponents and
        [1 + n] simulated challenges. *)
    Definition prove_membership {n : nat} (g h : G) (ms : Vector.t G (2 + n))
      (rindex : Fin.t (2 + n)) (r : F) (uscs : Vector.t F ((2 + n) + (1 + n)))
      (cp : G * G) (c : F) : membership_proof (2 + n) :=
      @generalised_construct_encryption_proof_elgamal_real F zero add mul sub
        opp G ginv gop gpow n rindex r uscs ms g h cp c.

    (** The announcement of the honest membership proof, computed before
        the challenge is known (with dummy witness and challenge [zero],
        which do not affect it: [prove_membership_announcement]). *)
    Definition membership_commitment {n : nat} (g h : G) (ms : Vector.t G (2 + n))
      (rindex : Fin.t (2 + n)) (uscs : Vector.t F ((2 + n) + (1 + n)))
      (cp : G * G) : Vector.t (G * G) (2 + n) :=
      Sigma.announcement (prove_membership g h ms rindex zero uscs cp zero).

    (** *** Ballots for [m] candidates

        The data layout of a ballot and its verifier. Everything here is
        parametric in the number of candidates [m], the generator [g] and
        the election public key [h]. *)
    Section Ballot.
      Context {m : nat} (g h : G).

      (** The admissible position messages [ [g ^ 0; g ^ 1; …; g ^ m] ]. *)
      Definition msgs_pos : Vector.t G (S m) :=
        Vector.map (fun k => g ^ natF (fin_idx k)) (fin_enum (S m)).

      (** The separating shift [K = 2m + 1]. *)
      Definition pair_shift : nat := S (m + m).

      (** The admissible messages of the combined pair value
          [K · b + δ]:
[[
          g ^ 0, g ^ -1, …, g ^ -m,   g ^ (K+1), …, g ^ (K+m)
]]
          The first [m + 1] entries are the case [b = 0] ([δ ∈ {-m, …, 0}],
          at index [-δ]), the last [m] entries the case [b = 1]
          ([δ ∈ {1, …, m}], at index [m + δ]). *)
      Definition msgs_pair : Vector.t G (S m + m) :=
        Vector.map (fun k => ginv (g ^ natF (fin_idx k))) (fin_enum (S m)) ++
        Vector.map (fun k => g ^ natF (pair_shift + S (fin_idx k))) (fin_enum m).

      (** A position cell: [Enc(s_i)] and the proof [s_i ∈ {0, …, m}]. *)
      Definition pos_cell : Type := G * G * membership_proof (S m).

      (** A pair cell: [Enc(b_ij)], the bit proof [b_ij ∈ {0, 1}], and the
          membership proof [K · b_ij + δ_ij ∈ {-m, …, 0} ∪ {K+1, …, K+m}]. *)
      Definition pair_cell : Type :=
        (G * G) * @sigma_proto F (G * G) 2 3 2 * membership_proof (S m + m).

      (** A ballot: [m] position cells and an [m × m] matrix of pair cells. *)
      Definition ballot : Type :=
        Vector.t pos_cell m * Vector.t (Vector.t pair_cell m) m.

      (** Projections out of position and pair cells. *)
      Definition pos_cipher (pc : pos_cell) : G * G := fst pc.
      Definition pair_bit (pc : pair_cell) : G * G := fst (fst pc).
      Definition pair_bit_proof (pc : pair_cell) : @sigma_proto F (G * G) 2 3 2 :=
        snd (fst pc).
      Definition pair_mem_proof (pc : pair_cell) : membership_proof (S m + m) :=
        snd pc.

      (** [pair_combined cd pc] is [Enc(b_ij) ^ K · cd], the ciphertext on
          which the pair membership proof is checked; [cd] is [Enc(δ_ij)]
          as computed by the verifier. *)
      Definition pair_combined (cd : G * G) (pc : pair_cell) : G * G :=
        cmul (cpow (pair_bit pc) (natF pair_shift)) cd.

      (** A position cell is valid iff its membership proof over
          [msgs_pos] accepts. *)
      Definition verify_pos_cell (pc : pos_cell) : bool :=
        verify_membership g h msgs_pos (pos_cipher pc) (snd pc).

      (** A pair cell is valid with respect to [cd = Enc(δ_ij)] iff its bit
          proof (the approval-vote verifier) and its combined membership
          proof over [msgs_pair] accept. *)
      Definition verify_pair_cell (cd : G * G) (pc : pair_cell) : bool :=
        (@verify_encryption_vote_proof F zero one add Fdec G ginv gop gpow Gdec
          g h (pair_bit pc, pair_bit_proof pc) &&
         verify_membership g h msgs_pair (pair_combined cd pc) (pair_mem_proof pc))%bool.

      (** All position cells are valid. *)
      Definition verify_positions (b : ballot) : bool :=
        forall_fin m (fun i => verify_pos_cell (Vector.nth (fst b) i)).

      (** All pair cells are valid, with [Enc(δ_ij)] computed as
          [Enc(s_j) · Enc(s_i)⁻¹] from the position ciphertexts. *)
      Definition verify_pairs (b : ballot) : bool :=
        forall_fin m (fun i => forall_fin m (fun j =>
          verify_pair_cell
            (cmul (pos_cipher (Vector.nth (fst b) j)) (cinv (pos_cipher (Vector.nth (fst b) i))))
            (Vector.nth (Vector.nth (snd b) i) j))).

      (** The interactive ballot verifier. *)
      Definition verify_ballot (b : ballot) : bool :=
        (verify_positions b && verify_pairs b)%bool.

      (** The [m × m] matrix of encrypted preference bits of a ballot. *)
      Definition ballot_bits (b : ballot) : Vector.t (Vector.t (G * G) m) m :=
        Vector.map (Vector.map pair_bit) (snd b).

      (** [aggregate_margins bs] multiplies the bit matrices of all ballots
          entrywise, giving [Enc(D_ij)] with [D_ij = Σ_ballots b_ij]
          ([aggregate_margins_enc]). *)
      Definition aggregate_margins {N : nat} (bs : Vector.t ballot N) :
        Vector.t (Vector.t (G * G) m) m :=
        Vector.fold_right (fun b acc => Vector.map2 (Vector.map2 cmul) (ballot_bits b) acc)
          bs (Vector.const (Vector.const cid m) m).

      (** The decrypted bit [b_ij] of a ballot under the secret key [x], as a
          group element; for a valid ballot it is [g ^ 0] or [g ^ 1]. *)
      Definition plaintext_bit (x : F) (b : ballot) (i j : Fin.t m) : G :=
        cdec x (pair_bit (Vector.nth (Vector.nth (snd b) i) j)).

    End Ballot.

    (** *** The honest voter

        The voter for [m = n + 1] candidates (at least one, so that the
        EncProof index types [2 + k] are inhabited). All randomness,
        including the challenges in the interactive form, is supplied
        explicitly in records. *)
    Section Prover.
      Context {n : nat} (g h : G).
      Local Notation m := (S n).

      (** Randomness for one position cell: encryption randomness [ps_r],
          membership-proof randomness [ps_uscs] and challenge [ps_c]. *)
      Record pos_rand : Type := mk_pos_rand {
        ps_r : F;
        ps_uscs : Vector.t F ((2 + n) + (1 + n));
        ps_c : F
      }.

      (** Randomness for one pair cell: encryption randomness [pr_rb] of the
          bit, bit-proof randomness [pr_uscs_b] and challenge [pr_c_b],
          membership-proof randomness [pr_uscs_m] and challenge [pr_c_m]. *)
      Record pair_rand : Type := mk_pair_rand {
        pr_rb : F;
        pr_uscs_b : Vector.t F 3;
        pr_c_b : F;
        pr_uscs_m : Vector.t F ((2 + (n + S n)) + (1 + (n + S n)));
        pr_c_m : F
      }.

      (** Randomness for a whole ballot. *)
      Record ballot_rand : Type := mk_ballot_rand {
        br_pos : Vector.t pos_rand m;
        br_pair : Vector.t (Vector.t pair_rand m) m
      }.

      (** [encrypt_pos s rd] encrypts the position [s] and proves membership
          at index [s] of [msgs_pos]. *)
      Definition encrypt_pos (s : nat) (rd : pos_rand) : @pos_cell m :=
        let cp := @enc F G gop gpow g h (natF s) (ps_r rd) in
        (cp, prove_membership g h (msgs_pos (m := m) g) (fin_of_nat_default s m)
          (ps_r rd) (ps_uscs rd) cp (ps_c rd)).

      (** [pair_index si sj] is the index of [g ^ (K b + δ)] in [msgs_pair]:
          [m + (sj - si)] if [si < sj] ([b = 1]), and [si - sj] otherwise
          ([b = 0]). *)
      Definition pair_index (si sj : nat) : Fin.t (S m + m) :=
        if Nat.ltb si sj
        then fin_of_nat_default (m + (sj - si)) (m + m)
        else fin_of_nat_default (si - sj) (m + m).

      (** [encrypt_pair si sj ri rj rd] builds the pair cell for positions
          [si], [sj] whose ciphertexts used randomness [ri], [rj]: it
          encrypts [b = [si < sj] ], proves [b ∈ {0, 1}] with
          [generate_enc_proof] of [Frontend/Approval.v], and proves that the
          combination [Enc(b) ^ K · Enc(δ)] (randomness [K · rb + (rj - ri)])
          encrypts the message at [pair_index si sj]. The local [cd] is
          exactly the verifier's [Enc(s_j) · Enc(s_i)⁻¹] because
          [rdelta = rj - ri]. *)
      Definition encrypt_pair (si sj : nat) (ri rj : F) (rd : pair_rand) :
        @pair_cell m :=
        let b : F := if Nat.ltb si sj then one else zero in
        let cb := @enc F G gop gpow g h b (pr_rb rd) in
        let pfb := @generate_enc_proof F zero one add mul sub opp Fdec G ginv gop gpow
          g h (pr_rb rd) b (pr_uscs_b rd) cb (pr_c_b rd) in
        let rdelta := sub rj ri in
        let cd := @enc F G gop gpow g h (sub (natF sj) (natF si)) rdelta in
        let rc := (natF (@pair_shift m) * pr_rb rd) + rdelta in
        let cc := cmul (cpow cb (natF (@pair_shift m))) cd in
        (cb, pfb, prove_membership g h (msgs_pair (m := m) g) (pair_index si sj)
          rc (pr_uscs_m rd) cc (pr_c_m rd)).

      (** [encrypt_ballot s rd] builds the full ballot for the position
          vector [s]. *)
      Definition encrypt_ballot (s : Vector.t nat m) (rd : ballot_rand) : @ballot m :=
        (Vector.map (fun i => encrypt_pos (Vector.nth s i) (Vector.nth (br_pos rd) i))
          (fin_enum m),
         Vector.map (fun i => Vector.map (fun j =>
            encrypt_pair (Vector.nth s i) (Vector.nth s j)
              (ps_r (Vector.nth (br_pos rd) i)) (ps_r (Vector.nth (br_pos rd) j))
              (Vector.nth (Vector.nth (br_pair rd) i) j)) (fin_enum m)) (fin_enum m)).

    End Prover.

    (** *** Non-interactive ballots (Fiat–Shamir)

        All proofs of a ballot share one challenge, [H] applied to the
        ballot transcript: the position ciphertexts with their
        announcements, then for every pair the bit ciphertext with the
        announcements of the bit proof and of the membership proof. [H] is
        an abstract function; random-oracle soundness of the transformation
        is not formalised. The public key [(g, h)] is not hashed. *)
    Section NIZK.
      Context {n : nat} (g h : G) (H : list (G * G) -> F).
      Local Notation m := (S n).

      (** The list of group-element pairs fed to the hash. *)
      Definition ballot_transcript (b : @ballot m) : list (G * G) :=
        (List.concat (Vector.to_list (Vector.map (fun i =>
          pos_cipher (fst b)[@i] :: Vector.to_list (Sigma.announcement (snd (fst b)[@i])))
          (fin_enum m))) ++
         List.concat (Vector.to_list (Vector.map (fun i =>
          List.concat (Vector.to_list (Vector.map (fun j =>
            let pc := (snd b)[@i][@j] in
            pair_bit pc ::
            (Vector.to_list (Sigma.announcement (pair_bit_proof pc)) ++
             Vector.to_list (Sigma.announcement (pair_mem_proof pc)))) (fin_enum m))))
          (fin_enum m))))%list.

      (** The Fiat–Shamir challenge of a ballot. *)
      Definition ballot_challenge (b : @ballot m) : F := H (ballot_transcript b).

      (** [is_chal c pf] tests whether the main challenge of [pf] is [c]. *)
      Definition is_chal (c : F) {k l r : nat} (pf : @sigma_proto F (G * G) k (S l) r) : bool :=
        if Fdec (Vector.hd (Sigma.challenge pf)) c then true else false.

      (** [challenges_are c b] holds iff every proof of [b] uses main
          challenge [c]. *)
      Definition challenges_are (c : F) (b : @ballot m) : bool :=
        (forall_fin m (fun i => is_chal c (snd (fst b)[@i])) &&
         forall_fin m (fun i => forall_fin m (fun j =>
           (is_chal c (pair_bit_proof (snd b)[@i][@j]) &&
            is_chal c (pair_mem_proof (snd b)[@i][@j]))%bool)))%bool.

      (** The non-interactive verifier: all main challenges equal the hash
          of the transcript and the interactive verifier accepts. *)
      Definition nizk_verify_ballot (b : @ballot m) : bool :=
        (challenges_are (ballot_challenge b) b && verify_ballot g h b)%bool.

      (** [set_challenges rd c] replaces every challenge field of [rd] by
          [c]. *)
      Definition set_challenges (rd : ballot_rand (n := n)) (c : F) : ballot_rand (n := n) :=
        mk_ballot_rand
          (Vector.map (fun r => mk_pos_rand (ps_r r) (ps_uscs r) c) (br_pos rd))
          (Vector.map (Vector.map (fun r =>
            mk_pair_rand (pr_rb r) (pr_uscs_b r) c (pr_uscs_m r) c)) (br_pair rd)).

      (** The non-interactive honest voter in two passes: compute the ballot
          once with arbitrary challenges, hash its transcript (which does not
          depend on the challenges: [ballot_transcript_set_challenges]) and
          recompute it with the hashed challenge. *)
      Definition nizk_encrypt_ballot (s : Vector.t nat m) (rd : ballot_rand (n := n)) :
        @ballot m :=
        encrypt_ballot g h s (set_challenges rd (ballot_challenge (encrypt_ballot g h s rd))).
    End NIZK.
  End Definitions.

  (** ** Proofs

      From here on [G] is a vector space over [F] ([Hvec]). *)
  Section Proofs.

    Context
      {Hvec: @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.

    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (** *** Group and vector-space algebra

        The group laws are restated by name. Files that import
        [Algebra/Product_space.v] have global instances that make typeclass
        search for these laws diverge, so they use these lemmas (with
        [Hvec] given explicitly) instead of the generic ones. *)

    (** [g ^ (a + b) = g ^ a · g ^ b]. *)
    Lemma pow_add : ∀ (g : G) (a b : F), g ^ (a + b) = gop (g ^ a) (g ^ b).
    Proof.
      intros; rewrite (@vector_space_smul_distributive_fadd F (@eq F)
        zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow);
      [reflexivity | typeclasses eauto].
    Qed.

    (** [g ^ (a · b) = (g ^ a) ^ b]. *)
    Lemma pow_mul : ∀ (g : G) (a b : F), g ^ (a * b) = (g ^ a) ^ b.
    Proof.
      intros; rewrite (@vector_space_smul_associative_fmul F (@eq F)
        zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow);
      [reflexivity | typeclasses eauto].
    Qed.

    (** [g ^ (-a) = (g ^ a)⁻¹]. *)
    Lemma pow_opp : ∀ (g : G) (a : F), g ^ (opp a) = ginv (g ^ a).
    Proof.
      intros; rewrite <- (@connection_between_vopp_and_fopp F (@eq F)
        zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow Hvec);
      reflexivity.
    Qed.

    (** [(a · b) ^ r = a ^ r · b ^ r]. *)
    Lemma gop_pow : ∀ (a b : G) (r : F), (gop a b) ^ r = gop (a ^ r) (b ^ r).
    Proof.
      intros; rewrite (@vector_space_smul_distributive_vadd F (@eq F)
        zero one add mul sub div opp inv G (@eq G) gid ginv gop gpow);
      [reflexivity | typeclasses eauto].
    Qed.

    (** Associativity, commutativity, identity and inverse laws of [G], and
        [a ^ 1 = a], under fixed names. *)
    Lemma gop_assoc : ∀ (a b c : G), gop a (gop b c) = gop (gop a b) c.
    Proof. intros; apply associative. Qed.
    Lemma gop_comm : ∀ (a b : G), gop a b = gop b a.
    Proof. intros; apply commutative. Qed.
    Lemma gop_gid_l : ∀ (a : G), gop gid a = a.
    Proof. intros; apply left_identity. Qed.
    Lemma gop_gid_r : ∀ (a : G), gop a gid = a.
    Proof. intros; apply right_identity. Qed.
    Lemma gop_ginv_l : ∀ (a : G), gop (ginv a) a = gid.
    Proof. intros; apply group_is_left_inverse. Qed.
    Lemma gop_ginv_r : ∀ (a : G), gop a (ginv a) = gid.
    Proof. intros; apply group_is_right_inverse. Qed.
    Lemma ginv_gid : ginv gid = gid.
    Proof. apply group_inv_id. Qed.
    Lemma pow_one : ∀ (a : G), a ^ one = a.
    Proof. intros; apply field_one. Qed.

    (** [a ^ 0 = 1]. *)
    Lemma pow_zero : ∀ (a : G), a ^ zero = gid.
    Proof. intros; apply field_zero. Qed.

    (** [(a⁻¹) ^ x = (a ^ x)⁻¹]. *)
    Lemma ginv_pow : ∀ (a : G) (x : F), (ginv a) ^ x = ginv (a ^ x).
    Proof.
      intros a x.
      assert (h2 : ginv a = a ^ (opp one)) by (rewrite pow_opp, pow_one; reflexivity).
      rewrite h2, <- pow_mul, <- pow_opp.
      f_equal; field.
    Qed.

    (** [(a · b) · (c · d) = (a · c) · (b · d)]. *)
    Lemma gop_rearrange : ∀ (a b c d : G),
      gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
    Proof.
      intros a b c d.
      rewrite <- associative, (associative b c d), (commutative b c),
        <- (associative c b d), associative.
      reflexivity.
    Qed.

    (** [(a · b)⁻¹ = a⁻¹ · b⁻¹] (the group is commutative). *)
    Lemma ginv_gop : ∀ (a b : G), ginv (gop a b) = gop (ginv a) (ginv b).
    Proof.
      intros a b.
      eapply group_cancel_left with (z := gop a b).
      rewrite group_is_right_inverse, gop_rearrange, !group_is_right_inverse,
        left_identity; reflexivity.
    Qed.

    (** [(a · b) · a⁻¹ = b]. *)
    Lemma gop_cancel : ∀ (a b : G), gop (gop a b) (ginv a) = b.
    Proof.
      intros a b.
      rewrite commutative, associative, group_is_left_inverse, left_identity;
      reflexivity.
    Qed.

    (** *** Homomorphic properties of exponential ElGamal *)

    (** [enc g h m r] below is [(g ^ r, g ^ m · h ^ r)]. *)
    Local Notation enc := (@enc F G gop gpow).

    (** [Enc(m₁; r₁) · Enc(m₂; r₂) = Enc(m₁ + m₂; r₁ + r₂)]. *)
    Lemma enc_mul : ∀ (g h : G) (m1 r1 m2 r2 : F),
      cmul (enc g h m1 r1) (enc g h m2 r2) = enc g h (m1 + m2) (r1 + r2).
    Proof.
      intros; unfold cmul, enc; cbn.
      rewrite !pow_add, gop_rearrange; reflexivity.
    Qed.

    (** [Enc(m; r)⁻¹ = Enc(-m; -r)]. *)
    Lemma enc_inv : ∀ (g h : G) (m r : F),
      cinv (enc g h m r) = enc g h (opp m) (opp r).
    Proof.
      intros; unfold cinv, enc; cbn.
      rewrite !pow_opp, ginv_gop; reflexivity.
    Qed.

    (** [Enc(m; r) ^ k = Enc(m k; r k)]. *)
    Lemma enc_pow : ∀ (g h : G) (m r k : F),
      cpow (enc g h m r) k = enc g h (m * k) (r * k).
    Proof.
      intros; unfold cpow, enc; cbn.
      rewrite !pow_mul, gop_pow; reflexivity.
    Qed.

    (** [Enc(m₁; r₁) · Enc(m₂; r₂)⁻¹ = Enc(m₁ - m₂; r₁ - r₂)]. *)
    Lemma enc_div : ∀ (g h : G) (m1 r1 m2 r2 : F),
      cmul (enc g h m1 r1) (cinv (enc g h m2 r2)) = enc g h (sub m1 m2) (sub r1 r2).
    Proof.
      intros; rewrite enc_inv, enc_mul.
      f_equal; field.
    Qed.

    (** Congruence of [enc] in the plaintext and randomness. *)
    Lemma enc_ext : ∀ (g h : G) (m r m' r' : F),
      m = m' -> r = r' -> enc g h m r = enc g h m' r'.
    Proof. intros; subst; reflexivity. Qed.

    (** [ceqb] is reflexive. *)
    Lemma ceqb_refl : ∀ (c : G * G), ceqb c c = true.
    Proof.
      intros [a b]; unfold ceqb; cbn.
      destruct (Gdec a a) as [_ | hn]; [| contradiction].
      destruct (Gdec b b) as [_ | hn]; [reflexivity | contradiction].
    Qed.

    (** *** Vectors indexed by [fin_enum] *)

    (** [fin_idx (FS j) = fin_idx j + 1]. *)
    Lemma fin_idx_FS : ∀ (n : nat) (j : Fin.t n), fin_idx (Fin.FS j) = S (fin_idx j).
    Proof.
      intros; unfold fin_idx; cbn; destruct (Fin.to_nat j); reflexivity.
    Qed.

    (** The [i]-th entry of [map (f ∘ fin_idx) (fin_enum n)] is
        [f (fin_idx i)]. *)
    Lemma nth_enum : ∀ (A : Type) (n : nat) (f : nat -> A) (i : Fin.t n),
      (Vector.map (fun k => f (fin_idx k)) (fin_enum n))[@i] = f (fin_idx i).
    Proof.
      intros; rewrite (Vector.nth_map _ _ i i eq_refl), fin_enum_nth; reflexivity.
    Qed.

    (** Lookup in the concatenation of two such tabulated vectors: the
        left part for indices below [a], the right part (shifted by [a])
        otherwise. Used to read [msgs_pair]. *)
    Lemma nth_enum_append : ∀ (A : Type) (a b : nat) (f g : nat -> A) (i : Fin.t (a + b)),
      (Vector.map (fun k => f (fin_idx k)) (fin_enum a) ++
       Vector.map (fun k => g (fin_idx k)) (fin_enum b))[@i] =
      if Nat.ltb (fin_idx i) a then f (fin_idx i) else g (fin_idx i - a).
    Proof.
      intros A a b f g i.
      destruct (fin_append_inv a b i) as [(p & hp) | (p & hp)]; subst i.
      + rewrite VectorSpec.nth_append_L, nth_enum.
        unfold fin_idx; rewrite Fin.L_sanity.
        destruct (Fin.to_nat p) as [k hk]; cbn [proj1_sig].
        rewrite (proj2 (Nat.ltb_lt _ _) hk); reflexivity.
      + rewrite VectorSpec.nth_append_R, nth_enum.
        unfold fin_idx; rewrite Fin.R_sanity.
        destruct (Fin.to_nat p) as [k hk]; cbn [proj1_sig].
        rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
        f_equal; lia.
    Qed.

    (** Lookup in a tabulated [n × n] matrix. *)
    Lemma nth_mat : ∀ (A : Type) (n : nat) (f : Fin.t n -> Fin.t n -> A) (i j : Fin.t n),
      (Vector.map (fun i => Vector.map (fun j => f i j) (fin_enum n)) (fin_enum n))[@i][@j] = f i j.
    Proof.
      intros; rewrite (Vector.nth_map _ _ i i eq_refl), fin_enum_nth,
        (Vector.nth_map _ _ j j eq_refl), fin_enum_nth; reflexivity.
    Qed.

    (** [fin_idx_default] rewrites [fin_idx (fin_of_nat_default i n)] to
        [i], whatever form the index of [fin_idx] takes (plain [rewrite]
        fails when it is [S n + n] instead of [S (n + n)]). *)
    Ltac fin_idx_default :=
      match goal with
      | [ |- context [ @fin_idx ?N (fin_of_nat_default ?i ?n) ] ] =>
          let e := fresh "hidx" in
          assert (e : @fin_idx N (fin_of_nat_default i n) = i)
            by (apply fin_of_nat_default_idx; lia);
          rewrite e; clear e
      end.

    (** *** The embedding [natF] *)

    (** [natF] is additive. *)
    Lemma natF_add : ∀ (a b : nat), natF (a + b) = natF a + natF b.
    Proof.
      induction a as [| a ih]; intro b; cbn.
      + field.
      + rewrite ih; field.
    Qed.

    (** [natF (a - b) = natF a - natF b] for [b ≤ a]. *)
    Lemma natF_sub : ∀ (a b : nat), b <= a -> natF (a - b) = sub (natF a) (natF b).
    Proof.
      intros a b hb.
      assert (h : natF a = natF (a - b) + natF b) by (rewrite <- natF_add; f_equal; lia).
      rewrite h; field.
    Qed.

    (** *** Completeness *)

    (** The honest membership proof is accepted when [cp] encrypts [m] with
        randomness [r] and the message at the real index is [g ^ m]. *)
    Lemma prove_membership_valid : ∀ (n : nat) (g h : G) (ms : Vector.t G (2 + n))
      (idx : Fin.t (2 + n)) (m r : F) (uscs : Vector.t F ((2 + n) + (1 + n)))
      (cp : G * G) (c : F),
      cp = enc g h m r -> ms[@idx] = g ^ m ->
      verify_membership g h ms cp (prove_membership g h ms idx r uscs cp c) = true.
    Proof.
      intros * hc hm; subst.
      unfold verify_membership, prove_membership, enc.
      apply generalised_construct_encryption_proof_elgamal_real_completeness.
      split; [reflexivity |].
      rewrite hm, gop_cancel; reflexivity.
    Qed.

    (** An honest position cell with [s ≤ m] is valid. *)
    Lemma encrypt_pos_valid : ∀ (n : nat) (g h : G) (s : nat) (rd : pos_rand (n := n)),
      s <= S n -> verify_pos_cell g h (encrypt_pos g h s rd) = true.
    Proof.
      intros * hs.
      unfold verify_pos_cell, encrypt_pos, pos_cipher; cbn [fst snd].
      eapply prove_membership_valid; [reflexivity |].
      unfold msgs_pos.
      rewrite (nth_enum _ _ (fun k => g ^ natF k)).
      fin_idx_default; reflexivity.
    Qed.

    (** An honest pair cell with positions [si, sj ≤ m] is valid against the
        verifier's [Enc(δ) = Enc(sj; rj) · Enc(si; ri)⁻¹]. In the case
        [si < sj] the combined plaintext is [K + (sj - si)], found at index
        [m + (sj - si)] of [msgs_pair]; otherwise it is [-(si - sj)], found
        at index [si - sj]. *)
    Lemma encrypt_pair_valid : ∀ (n : nat) (g h : G) (si sj : nat) (ri rj : F)
      (rd : pair_rand (n := n)),
      si <= S n -> sj <= S n ->
      verify_pair_cell g h (cmul (enc g h (natF sj) rj) (cinv (enc g h (natF si) ri)))
        (encrypt_pair g h si sj ri rj rd) = true.
    Proof.
      intros * hi hj.
      unfold verify_pair_cell, encrypt_pair, pair_bit, pair_bit_proof, pair_mem_proof,
        pair_combined; cbn [fst snd].
      apply andb_true_iff; split.
      (* The bit proof is the approval-vote proof for b ∈ {0, 1}. *)
      + apply vote_proof_valid.
        destruct (Nat.ltb si sj); [right | left]; reflexivity.
      + cbn [pair_bit fst snd].
        (* The combined ciphertext encrypts K b + (sj - si) with
           randomness K rb + (rj - ri). *)
        rewrite enc_div, enc_pow, enc_mul.
        unfold msgs_pair, pair_index.
        (* Case si < sj: index m + (sj - si) in the right half of
           msgs_pair; otherwise index si - sj in the left half. *)
        destruct (Nat.ltb si sj) eqn:hlt.
        - apply Nat.ltb_lt in hlt.
          eapply prove_membership_valid.
          * apply enc_ext; [reflexivity | field].
          * etransitivity; [exact (nth_enum_append _ (S (S n)) (S n)
              (fun k => ginv (g ^ natF k)) (fun k => g ^ natF (pair_shift + S k))
              (fin_of_nat_default (S n + (sj - si)) (S n + S n))) |].
            fin_idx_default.
            rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
            f_equal.
            replace (S (S n + (sj - si) - S (S n)))%nat with (sj - si)%nat by lia.
            rewrite natF_add, (natF_sub sj si); [field | lia].
        - apply Nat.ltb_ge in hlt.
          eapply prove_membership_valid.
          * apply enc_ext; [reflexivity | field].
          * etransitivity; [exact (nth_enum_append _ (S (S n)) (S n)
              (fun k => ginv (g ^ natF k)) (fun k => g ^ natF (pair_shift + S k))
              (fin_of_nat_default (si - sj) (S n + S n))) |].
            fin_idx_default.
            rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
            rewrite <- pow_opp; f_equal.
            rewrite (natF_sub si sj); [field | lia].
    Qed.

    (** Completeness of the interactive ballot: for any positions
        [s_i ≤ m] and any randomness, [verify_ballot] accepts
        [encrypt_ballot s rd]. *)
    Theorem ballot_valid : ∀ (n : nat) (g h : G) (s : Vector.t nat (S n))
      (rd : ballot_rand (n := n)),
      (∀ i, Vector.nth s i <= S n) ->
      verify_ballot g h (encrypt_ballot g h s rd) = true.
    Proof.
      intros * hs.
      unfold verify_ballot, verify_positions, verify_pairs, encrypt_ballot; cbn [fst snd].
      apply andb_true_iff; split.
      + apply forall_fin_true; intro i.
        rewrite (Vector.nth_map _ _ i i eq_refl), fin_enum_nth.
        apply encrypt_pos_valid, hs.
      + apply forall_fin_true; intro i; apply forall_fin_true; intro j.
        rewrite nth_mat, !(Vector.nth_map _ _ _ _ eq_refl), !fin_enum_nth.
        unfold encrypt_pos, pos_cipher; cbn [fst snd].
        apply encrypt_pair_valid; apply hs.
    Qed.

    (** *** Special soundness

        Extraction from two accepting ballots, and the decoding of the
        extracted plaintexts back to a ranking. *)

    (** Exponentiation in base [g] is injective; true when [g] generates a
        group of prime order [q] and [F] is the field of integers mod [q]. *)
    Definition exp_injective (g : G) : Prop := ∀ a b : F, g ^ a = g ^ b -> a = b.

    (** The characteristic of [F] exceeds [B]: [natF] is injective on
        [ [0, B] ]. *)
    Definition natF_injective (B : nat) : Prop :=
      ∀ a b : nat, a <= B -> b <= B -> natF a = natF b -> a = b.

    (** [(a · b) · b⁻¹ = a]. *)
    Lemma gop_cancel_r : ∀ (a b : G), gop (gop a b) (ginv b) = a.
    Proof. intros; rewrite (gop_comm a b); apply gop_cancel. Qed.

    (** [ceqb] reflects equality. *)
    Lemma ceqb_true : ∀ (a b : G * G), ceqb a b = true -> a = b.
    Proof.
      intros [a1 a2] [b1 b2] h; unfold ceqb in h; cbn in h.
      destruct (Gdec a1 b1); [| discriminate].
      destruct (Gdec a2 b2); [| discriminate].
      subst; reflexivity.
    Qed.

    (** Decryption correctness: if [h = g ^ x] then [cdec x (Enc(m; r)) = g ^ m]. *)
    Lemma cdec_enc : ∀ (x : F) (g h : G) (m r : F),
      h = g ^ x -> cdec x (enc g h m r) = g ^ m.
    Proof.
      intros * ->; unfold cdec, enc; cbn.
      rewrite <- !pow_mul.
      replace (r * x) with (x * r) by field.
      apply gop_cancel_r.
    Qed.

    (** [natF] is multiplicative. *)
    Lemma natF_mul : ∀ (a b : nat), natF (a * b) = natF a * natF b.
    Proof.
      induction a as [| a ih]; intro b; cbn [Nat.mul nat_to_F].
      + field.
      + rewrite natF_add, ih; field.
    Qed.

    (** With injective exponentiation, equal ciphertexts have equal
        randomness and equal message group elements. *)
    Lemma enc_eq : ∀ (g h : G) (m r m' r' : F), exp_injective g ->
      enc g h m r = enc g h m' r' -> r = r' ∧ g ^ m = g ^ m'.
    Proof.
      intros * hinj he; unfold enc in he; injection he as h1 h2.
      apply hinj in h1; subst r'; split; [reflexivity |].
      apply (f_equal (fun z => gop z (ginv (h ^ r)))) in h2.
      rewrite !gop_cancel_r in h2; exact h2.
    Qed.

    (** Finite choice over [Fin.t n]: a pointwise existence statement gives
        a choice function (provable without axioms by induction on [n]). *)
    Lemma fin_choice : ∀ (n : nat) (A : Type) (P : Fin.t n -> A -> Prop),
      (∀ i, ∃ a, P i a) -> ∃ f : Fin.t n -> A, ∀ i, P i (f i).
    Proof.
      induction n as [| n ih]; intros A P hP.
      + exists (fun i => Fin.case0 (fun _ => A) i); intro i; inversion i.
      + destruct (hP Fin.F1) as (a0 & h0).
        destruct (ih A (fun i a => P (Fin.FS i) a) (fun i => hP (Fin.FS i))) as (f & hf).
        exists (fun i => Fin.caseS' i (fun _ => A) a0 f).
        intro i; apply (Fin.caseS' i); [exact h0 | intro j; exact (hf j)].
    Qed.

    (** Special soundness of the membership proof: two accepting proofs
        with the same announcement and different main challenges show that
        [cp = (g ^ y, ms_f · h ^ y)] for some index [f] and randomness [y].
        Instance of [generalised_accepting_elgamal_soundness_main]. *)
    Lemma membership_sound : ∀ (n : nat) (g h : G) (ms : Vector.t G (2 + n))
      (cp : G * G) (pf pf' : membership_proof (2 + n)),
      Sigma.announcement pf = Sigma.announcement pf' ->
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      verify_membership g h ms cp pf = true -> verify_membership g h ms cp pf' = true ->
      ∃ (f : Fin.t (2 + n)) (y : F), cp = (g ^ y, gop (ms[@f]) (h ^ y)).
    Proof.
      intros * ha hc h1 h2.
      destruct pf as [a c r]; destruct pf' as [a' c' r']; cbn in ha, hc; subst a'.
      destruct (vector_inv_S c) as (c0 & cs & ->).
      destruct (vector_inv_S c') as (c0' & cs' & ->); cbn in hc.
      destruct cp as (c1 & c2).
      unfold verify_membership in h1, h2.
      destruct (generalised_accepting_elgamal_soundness_main g h ms c1 c2 a c0 cs r
        c0' cs' r' h1 h2 hc) as (y & hy & f & hf).
      exists f, y; rewrite <- hy; f_equal.
      rewrite hf, (gop_comm c2), gop_assoc, gop_ginv_r, gop_gid_l; reflexivity.
    Qed.

    (** Special soundness of the bit proof: the ciphertext encrypts [0] or
        [1] (via [vote_proof_sound] of [Frontend/Approval.v]). *)
    Lemma bit_sound : ∀ (g h : G) (cp : G * G) (pf pf' : @sigma_proto F (G * G) 2 3 2),
      Sigma.announcement pf = Sigma.announcement pf' ->
      Vector.hd (Sigma.challenge pf) <> Vector.hd (Sigma.challenge pf') ->
      @verify_encryption_vote_proof F zero one add Fdec G ginv gop gpow Gdec g h (cp, pf) = true ->
      @verify_encryption_vote_proof F zero one add Fdec G ginv gop gpow Gdec g h (cp, pf') = true ->
      ∃ r : F, cp = enc g h zero r ∨ cp = enc g h one r.
    Proof.
      intros * ha hc h1 h2.
      destruct pf as [a c r]; destruct pf' as [a' c' r']; cbn in ha, hc; subst a'.
      destruct (vector_inv_S c) as (c0 & cs & ->).
      destruct (vector_inv_S c') as (c0' & cs' & ->); cbn in hc.
      exact (vote_proof_sound g h cp a c0 c0' cs cs' r r' h1 h2 hc).
    Qed.

    (** Decoding the combined value. With [b ≤ 1], positions in [ [0, m] ]
        and characteristic above [4m + 2]: if [K b + (sj - si) = -k] with
        [k ≤ m] then [b = 0] and [si ≥ sj]; if [K b + (sj - si) = K + 1 + k]
        with [k < m] then [b = 1] and [si < sj]. In both cases
        [b = [si < sj] ]. Both equations are moved into [natF] of natural
        numbers bounded by [4m + 2] and decided by [lia]. *)
    Lemma pair_decode : ∀ (m : nat), natF_injective (4 * m + 2) ->
      ∀ (si sj k b : nat), si <= m -> sj <= m -> b <= 1 ->
      ((k <= m ∧ natF b * natF (S (m + m)) + sub (natF sj) (natF si) = opp (natF k)) ∨
       (k < m ∧ natF b * natF (S (m + m)) + sub (natF sj) (natF si) = natF (S (m + m) + S k))) ->
      b = (if Nat.ltb si sj then 1 else 0).
    Proof.
      intros m hinj si sj k b hi hj hb [(hk & he) | (hk & he)].
      + assert (h1 : natF (b * S (m + m) + sj + k) = natF si).
        { rewrite !natF_add, natF_mul.
          transitivity ((natF b * natF (S (m + m)) + sub (natF sj) (natF si)) + natF si + natF k);
          [field | rewrite he; field]. }
        apply hinj in h1; [| nia | lia].
        destruct (Nat.ltb si sj) eqn:hlt; [apply Nat.ltb_lt in hlt | apply Nat.ltb_ge in hlt];
        destruct b as [| [| b]]; cbn in h1; lia.
      + assert (h1 : natF (b * S (m + m) + sj) = natF (S (m + m) + S k + si)).
        { rewrite !natF_add, natF_mul.
          transitivity ((natF b * natF (S (m + m)) + sub (natF sj) (natF si)) + natF si);
          [field | rewrite he; rewrite !natF_add; field]. }
        apply hinj in h1; [| nia | lia].
        destruct (Nat.ltb si sj) eqn:hlt; [apply Nat.ltb_lt in hlt | apply Nat.ltb_ge in hlt];
        destruct b as [| [| b]]; cbn in h1; lia.
    Qed.

    (** Two ballots have the same ciphertexts and the same announcements
        in every proof (the rewinding hypothesis). *)
    Definition same_announcements {m : nat} (b b' : @ballot m) : Prop :=
      (∀ i, pos_cipher (Vector.nth (fst b) i) = pos_cipher (Vector.nth (fst b') i) ∧
        Sigma.announcement (snd (Vector.nth (fst b) i)) =
        Sigma.announcement (snd (Vector.nth (fst b') i))) ∧
      (∀ i j,
        let pc := Vector.nth (Vector.nth (snd b) i) j in
        let pc' := Vector.nth (Vector.nth (snd b') i) j in
        pair_bit pc = pair_bit pc' ∧
        Sigma.announcement (pair_bit_proof pc) = Sigma.announcement (pair_bit_proof pc') ∧
        Sigma.announcement (pair_mem_proof pc) = Sigma.announcement (pair_mem_proof pc')).

    (** Two ballots have different main challenges in every proof. *)
    Definition different_challenges {m : nat} (b b' : @ballot m) : Prop :=
      (∀ i, Vector.hd (Sigma.challenge (snd (Vector.nth (fst b) i))) <>
        Vector.hd (Sigma.challenge (snd (Vector.nth (fst b') i)))) ∧
      (∀ i j,
        let pc := Vector.nth (Vector.nth (snd b) i) j in
        let pc' := Vector.nth (Vector.nth (snd b') i) j in
        Vector.hd (Sigma.challenge (pair_bit_proof pc)) <>
        Vector.hd (Sigma.challenge (pair_bit_proof pc')) ∧
        Vector.hd (Sigma.challenge (pair_mem_proof pc)) <>
        Vector.hd (Sigma.challenge (pair_mem_proof pc'))).

    (** If [Enc(M; r) = (g ^ y, msg · h ^ y)] then [g ^ M = msg]. *)
    Lemma enc_eq_msg : ∀ (g h : G) (M r y : F) (msg : G), exp_injective g ->
      enc g h M r = (g ^ y, gop msg (h ^ y)) -> g ^ M = msg.
    Proof.
      intros * hinj he; unfold enc in he; injection he as h1 h2.
      apply hinj in h1; subst y.
      apply (f_equal (fun z => gop z (ginv (h ^ r)))) in h2.
      rewrite !gop_cancel_r in h2; exact h2.
    Qed.

    (** Decryption is a homomorphism: [cdec] maps [cmul], [cinv] and
        [cpow] to the product, inverse and power of plaintext group
        elements. *)
    Lemma cdec_cmul : ∀ (x : F) (a b : G * G), cdec x (cmul a b) = gop (cdec x a) (cdec x b).
    Proof.
      intros x [a1 a2] [b1 b2]; unfold cdec, cmul; cbn.
      rewrite gop_pow, ginv_gop, gop_rearrange; reflexivity.
    Qed.

    (** Decryption of an inverse. *)
    Lemma cdec_cinv : ∀ (x : F) (a : G * G), cdec x (cinv a) = ginv (cdec x a).
    Proof.
      intros x [a1 a2]; unfold cdec, cinv; cbn.
      rewrite ginv_pow, ginv_gop; reflexivity.
    Qed.

    (** Decryption of a power. *)
    Lemma cdec_cpow : ∀ (x : F) (a : G * G) (k : F), cdec x (cpow a k) = (cdec x a) ^ k.
    Proof.
      intros x [a1 a2] k; unfold cdec, cpow; cbn.
      rewrite gop_pow, ginv_pow, <- !pow_mul.
      f_equal; f_equal; f_equal; field.
    Qed.

    (** Decryption of a ciphertext presented as [(g ^ y, msg · h ^ y)]
        gives [msg]. *)
    Lemma cdec_msg : ∀ (x : F) (g h : G) (cp : G * G) (msg : G) (y : F),
      h = g ^ x -> cp = (g ^ y, gop msg (h ^ y)) -> cdec x cp = msg.
    Proof.
      intros * -> ->; unfold cdec; cbn.
      rewrite <- !pow_mul; replace (y * x) with (x * y) by field.
      apply gop_cancel_r.
    Qed.

    (** [fin_idx f < n]. *)
    Lemma fin_idx_lt : ∀ (n : nat) (f : Fin.t n), fin_idx f < n.
    Proof. intros; unfold fin_idx; destruct (Fin.to_nat f); cbn; assumption. Qed.

    (** Special soundness of the ballot. If [h = g ^ x], exponentiation in
        base [g] is injective and the characteristic of [F] is above
        [4m + 2] (with [m = n + 1]), then from two accepting ballots [b],
        [b'] with the same ciphertexts and announcements and different
        challenges in every proof one obtains positions [s_i ≤ m] such that
        every pair ciphertext of [b] decrypts to [g ^ [s_i < s_j] ].

        Proof idea: [membership_sound] on each position cell gives
        [Enc(s_i)] for some [s_i ≤ m] (made into a vector by [fin_choice]);
        [bit_sound] gives [b_ij ∈ {0, 1}]; [membership_sound] on the pair
        cell gives an admissible message for
        [Enc(b_ij) ^ K · Enc(s_j) · Enc(s_i)⁻¹], whose plaintext is
        [K b_ij + s_j - s_i]; [pair_decode] then forces
        [b_ij = [s_i < s_j] ]. *)
    Theorem ballot_sound : ∀ (n : nat) (x : F) (g h : G) (b b' : @ballot (S n)),
      h = g ^ x -> exp_injective g -> natF_injective (4 * S n + 2) ->
      same_announcements b b' -> different_challenges b b' ->
      verify_ballot g h b = true -> verify_ballot g h b' = true ->
      ∃ s : Vector.t nat (S n),
        (∀ i, Vector.nth s i <= S n) ∧
        (∀ i j, plaintext_bit x b i j =
          g ^ (if Nat.ltb (Vector.nth s i) (Vector.nth s j) then one else zero)).
    Proof.
      intros * hh hinj hchar (hsa_pos & hsa_pair) (hdc_pos & hdc_pair) hv hv'.
      unfold verify_ballot in hv, hv'.
      apply andb_prop in hv; destruct hv as (hpos & hpair).
      apply andb_prop in hv'; destruct hv' as (hpos' & hpair').
      unfold verify_positions in hpos, hpos'; rewrite forall_fin_true in hpos, hpos'.
      unfold verify_pairs in hpair, hpair'; rewrite forall_fin_true in hpair, hpair'.
      (* Extract a position s_i ≤ m for every candidate from the two
         position proofs. *)
      assert (hP : ∀ i, ∃ k : nat, k <= S n ∧
        ∃ y, pos_cipher (fst b)[@i] = enc g h (natF k) y).
      { intro i.
        specialize (hpos i); specialize (hpos' i).
        unfold verify_pos_cell in hpos, hpos'.
        destruct (hsa_pos i) as (hcp & han).
        rewrite <- hcp in hpos'.
        destruct (membership_sound n g h (msgs_pos (m := S n) g) _ _ _ han (hdc_pos i) hpos hpos')
          as (f & y & hf).
        exists (fin_idx f); split; [pose proof (fin_idx_lt _ f); lia |].
        exists y; rewrite hf; unfold msgs_pos.
        rewrite (nth_enum _ _ (fun k => g ^ natF k)); reflexivity. }
      (* Turn the pointwise extraction into a position vector. *)
      destruct (fin_choice _ _ _ hP) as (sf & hsf).
      exists (Vector.map sf (fin_enum (S n))).
      split.
      + intro i; rewrite (Vector.nth_map _ _ i i eq_refl), fin_enum_nth; exact (proj1 (hsf i)).
      + intros i j; rewrite !(Vector.nth_map _ _ _ _ eq_refl), !fin_enum_nth.
        destruct (hsf i) as (hi & yi & hci); destruct (hsf j) as (hj & yj & hcj).
        specialize (hpair i); rewrite forall_fin_true in hpair; specialize (hpair j).
        specialize (hpair' i); rewrite forall_fin_true in hpair'; specialize (hpair' j).
        unfold verify_pair_cell in hpair, hpair'.
        apply andb_prop in hpair; destruct hpair as (hbit & hmem).
        apply andb_prop in hpair'; destruct hpair' as (hbit' & hmem').
        destruct (hsa_pair i j) as (hb_eq & han_bit & han_mem).
        destruct (hdc_pair i j) as (hdc_bit & hdc_mem).
        rewrite <- hb_eq in hbit'.
      (* The bit ciphertext encrypts 0 or 1. *)
        destruct (bit_sound g h _ _ _ han_bit hdc_bit hbit hbit') as (rb & hrb).
        destruct (hsa_pos i) as (hcpi & _); destruct (hsa_pos j) as (hcpj & _).
        unfold pair_combined in hmem, hmem'; rewrite <- hb_eq, <- hcpi, <- hcpj in hmem'.
        (* The combined ciphertext encrypts an admissible message of
           msgs_pair. *)
        destruct (membership_sound (n + S n) g h (msgs_pair (m := S n) g) _ _ _ han_mem hdc_mem hmem hmem')
          as (f & y & hf).
        unfold pos_cipher in hci, hcj, hf; rewrite hci, hcj, enc_div in hf.
        assert (hb2 : ∃ bv : nat, bv <= 1 ∧ pair_bit (snd b)[@i][@j] = enc g h (natF bv) rb).
        { destruct hrb as [hrb | hrb]; [exists 0 | exists 1]; (split; [lia |]);
          (rewrite hrb; apply enc_ext; [cbn; field | reflexivity]). }
        destruct hb2 as (bv & hbv & hbe).
        (* Its plaintext is K b + (s_j - s_i); compare with the extracted
           message by injectivity of exponentiation. *)
        rewrite hbe, enc_pow, enc_mul in hf.
        apply enc_eq_msg in hf; [| exact hinj].
        pose proof (eq_trans hf (nth_enum_append _ (S (S n)) (S n)
          (fun k => ginv (g ^ natF k)) (fun k => g ^ natF (pair_shift + S k)) f)) as hmsg.
        pose proof (fin_idx_lt (S (S n) + S n)%nat f) as hfl.
        set (fi := @fin_idx (S (S n) + S n)%nat f) in *.
        (* Decode: left half of msgs_pair gives b = 0, right half b = 1. *)
        assert (hbv' : bv = (if Nat.ltb (sf i) (sf j) then 1 else 0)).
        { case_eq (Nat.ltb fi (S (S n))); intro hlt; rewrite hlt in hmsg;
          unfold pair_shift in hmsg; cbv beta in hmsg.
          + apply Nat.ltb_lt in hlt.
            apply (pair_decode (S n) hchar (sf i) (sf j) fi bv hi hj hbv).
            left; split; [lia |].
            rewrite <- pow_opp in hmsg; apply hinj in hmsg; exact hmsg.
          + apply Nat.ltb_ge in hlt.
            apply (pair_decode (S n) hchar (sf i) (sf j) (fi - S (S n)) bv hi hj hbv).
            right; split; [lia |].
            apply hinj in hmsg; exact hmsg. }
        (* Decrypt the bit ciphertext. *)
        unfold plaintext_bit; rewrite hbe, cdec_enc; [| exact hh].
        rewrite hbv'; destruct (Nat.ltb (sf i) (sf j)); cbn [nat_to_F]; f_equal; field.
    Qed.

    (** *** Aggregation *)

    (** If ballot [k] encrypts the bit [bits_k(i, j)] with randomness
        [rs_k(i, j)], then the aggregate entry [(i, j)] encrypts
        [Σ_k bits_k(i, j)] with randomness [Σ_k rs_k(i, j)]. *)
    Theorem aggregate_margins_enc : ∀ (m N : nat) (g h : G)
      (bs : Vector.t (@ballot m) N) (bits rs : Vector.t (Vector.t (Vector.t F m) m) N),
      (∀ k i j, pair_bit (Vector.nth (Vector.nth (snd (Vector.nth bs k)) i) j) =
        enc g h (Vector.nth (Vector.nth (Vector.nth bits k) i) j)
          (Vector.nth (Vector.nth (Vector.nth rs k) i) j)) ->
      ∀ i j, Vector.nth (Vector.nth (aggregate_margins bs) i) j =
        enc g h
          (Vector.fold_right add (Vector.map (fun v => Vector.nth (Vector.nth v i) j) bits) zero)
          (Vector.fold_right add (Vector.map (fun v => Vector.nth (Vector.nth v i) j) rs) zero).
    Proof.
      intros m N g h bs bits rs hb i j.
      induction N as [| N ih].
      + rewrite (vector_inv_0 bs), (vector_inv_0 bits), (vector_inv_0 rs).
        unfold aggregate_margins; cbn [Vector.fold_right Vector.map].
        rewrite !Vector.const_nth; unfold cid, enc; cbn [Vector.fold_right].
        rewrite !pow_zero, gop_gid_l; reflexivity.
      + destruct (vector_inv_S bs) as (b & bs' & hbs).
        destruct (vector_inv_S bits) as (bt & bits' & hbt).
        destruct (vector_inv_S rs) as (r & rs' & hr).
        subst.
        change (aggregate_margins (b :: bs')) with
          (Vector.map2 (Vector.map2 cmul) (ballot_bits b) (aggregate_margins bs')).
        rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl),
          (Vector.nth_map2 _ _ _ j j j eq_refl eq_refl).
        rewrite (ih bs' bits' rs' (fun k => hb (Fin.FS k))).
        unfold ballot_bits; rewrite !(Vector.nth_map _ _ _ _ eq_refl).
        rewrite (hb Fin.F1); cbn [Vector.nth Vector.map Vector.fold_right].
        rewrite enc_mul; reflexivity.
    Qed.

    (** *** Fiat–Shamir

        The announcements of the honest proofs do not depend on the
        witness or the challenge, and the first challenge entry is the
        main challenge. Together these give completeness of the
        non-interactive ballot. The notations abbreviate the EncProof
        prover functions with the implicit arguments fixed. *)
    Local Notation construct_real := (construct_encryption_proof_elgamal_real (F := F)
      (zero := zero) (add := add) (mul := mul) (sub := sub) (opp := opp) (G := G)
      (ginv := ginv) (gop := gop) (gpow := gpow)).
    Local Notation construct_commitment := (construct_encryption_proof_elgamal_commitment
      (F := F) (opp := opp) (G := G) (ginv := ginv) (gop := gop) (gpow := gpow)).
    Local Notation generalised_real := (generalised_construct_encryption_proof_elgamal_real
      (F := F) (zero := zero) (add := add) (mul := mul) (sub := sub) (opp := opp) (G := G)
      (ginv := ginv) (gop := gop) (gpow := gpow)).

    (** The announcement of the inner real/simulated construction is the
        commitment function [construct_encryption_proof_elgamal_commitment]. *)
    Lemma construct_real_announcement : ∀ (k l : nat) (x : F)
      (uscs : Vector.t F ((k + (1 + l)) + (k + l))) (ms : Vector.t G (k + (1 + l)))
      (g h : G) (cp : G * G) (c : F),
      Sigma.announcement (@construct_encryption_proof_elgamal_real F zero add mul sub opp
        G ginv gop gpow k l x uscs ms g h cp c) =
      @construct_encryption_proof_elgamal_commitment F opp G ginv gop gpow k l uscs ms g h cp.
    Proof.
      intros; unfold construct_encryption_proof_elgamal_real.
      destruct (splitat (k + (1 + l)) uscs) as (us & cs).
      destruct (splitat k us) as (usl & usrh).
      destruct (vector_inv_S usrh) as (u & usr & _).
      destruct (splitat k cs) as (csl & csr).
      reflexivity.
    Qed.

    (** The head of the challenge vector of the inner construction is the
        main challenge [c]. *)
    Lemma construct_real_challenge : ∀ (k l : nat) (x : F)
      (uscs : Vector.t F ((k + (1 + l)) + (k + l))) (ms : Vector.t G (k + (1 + l)))
      (g h : G) (cp : G * G) (c : F),
      Vector.hd (Sigma.challenge (@construct_encryption_proof_elgamal_real F zero add mul sub opp
        G ginv gop gpow k l x uscs ms g h cp c)) = c.
    Proof.
      intros; unfold construct_encryption_proof_elgamal_real.
      destruct (splitat (k + (1 + l)) uscs) as (us & cs).
      destruct (splitat k us) as (usl & usrh).
      destruct (vector_inv_S usrh) as (u & usr & _).
      destruct (splitat k cs) as (csl & csr).
      reflexivity.
    Qed.

    (** Transport of announcements and challenge heads along a length
        equality [e] (used to remove the casts introduced by the
        index-splitting in the generalised prover). *)
    Lemma rew_announcement : ∀ (A B : nat) (e : A = B) (P : @sigma_proto F (G * G) B (S B) B),
      Sigma.announcement (rew <- [fun k => @sigma_proto F (G * G) k (S k) k] e in P) =
      rew <- [fun k => Vector.t (G * G) k] e in Sigma.announcement P.
    Proof. intros A B e P; destruct e; reflexivity. Qed.

    (** See [rew_announcement]. *)
    Lemma rew_challenge_hd : ∀ (A B : nat) (e : A = B) (P : @sigma_proto F (G * G) B (S B) B),
      Vector.hd (Sigma.challenge (rew <- [fun k => @sigma_proto F (G * G) k (S k) k] e in P)) =
      Vector.hd (Sigma.challenge P).
    Proof. intros A B e P; destruct e; reflexivity. Qed.

    (** The announcement of the generalised honest prover depends neither on
        the witness [x] nor on the challenge [c]. *)
    Lemma enc_real_announcement : ∀ (k : nat) (rindex : Fin.t (2 + k)) (x x' : F)
      (uscs : Vector.t F ((2 + k) + (1 + k))) (ms : Vector.t G (2 + k))
      (g h : G) (cp : G * G) (c c' : F),
      Sigma.announcement (generalised_real rindex x uscs ms g h cp c) =
      Sigma.announcement (generalised_real rindex x' uscs ms g h cp c').
    Proof.
      intros; rewrite !enc_prover_alt_eq; unfold enc_prover_alt.
      destruct (splitat (2 + k) uscs) as (us & cs).
      destruct (vector_fin_app_pred (1 + k) rindex us cs) as
        (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & _).
      destruct pfaa as [pfa]; destruct pfbb as [pfb].
      rewrite !rew_announcement; f_equal.
      etransitivity; [apply construct_real_announcement |].
      symmetry; apply construct_real_announcement.
    Qed.

    (** The head of the challenge vector of the generalised honest prover
        is [c]. *)
    Lemma enc_real_challenge : ∀ (k : nat) (rindex : Fin.t (2 + k)) (x : F)
      (uscs : Vector.t F ((2 + k) + (1 + k))) (ms : Vector.t G (2 + k))
      (g h : G) (cp : G * G) (c : F),
      Vector.hd (Sigma.challenge (generalised_real rindex x uscs ms g h cp c)) = c.
    Proof.
      intros; rewrite enc_prover_alt_eq; unfold enc_prover_alt.
      destruct (splitat (2 + k) uscs) as (us & cs).
      destruct (vector_fin_app_pred (1 + k) rindex us cs) as
        (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & _).
      destruct pfaa as [pfa]; destruct pfbb as [pfb].
      rewrite rew_challenge_hd; apply construct_real_challenge.
    Qed.

    (** [prove_membership] specialisations of the two previous lemmas. *)
    Lemma prove_membership_announcement : ∀ (k : nat) (g h : G) (ms : Vector.t G (2 + k))
      (rindex : Fin.t (2 + k)) (r r' : F) (uscs : Vector.t F ((2 + k) + (1 + k)))
      (cp : G * G) (c c' : F),
      Sigma.announcement (prove_membership g h ms rindex r uscs cp c) =
      Sigma.announcement (prove_membership g h ms rindex r' uscs cp c').
    Proof. intros; apply enc_real_announcement. Qed.

    (** See [prove_membership_announcement]. *)
    Lemma prove_membership_challenge : ∀ (k : nat) (g h : G) (ms : Vector.t G (2 + k))
      (rindex : Fin.t (2 + k)) (r : F) (uscs : Vector.t F ((2 + k) + (1 + k)))
      (cp : G * G) (c : F),
      Vector.hd (Sigma.challenge (prove_membership g h ms rindex r uscs cp c)) = c.
    Proof. intros; apply enc_real_challenge. Qed.

    (** The main challenge of the bit proof [generate_enc_proof] is [c]. *)
    Lemma generate_enc_proof_challenge : ∀ (g h : G) (r b : F) (uscs : Vector.t F 3)
      (cp : G * G) (c : F),
      Vector.hd (Sigma.challenge (@generate_enc_proof F zero one add mul sub opp Fdec G ginv gop gpow
        g h r b uscs cp c)) = c.
    Proof.
      intros; unfold generate_enc_proof; destruct (Fdec b zero); apply enc_real_challenge.
    Qed.

    (** The transcript of the honest ballot does not depend on the
        challenge fields of the randomness. *)
    Lemma ballot_transcript_set_challenges : ∀ (n : nat) (g h : G) (s : Vector.t nat (S n))
      (rd : ballot_rand (n := n)) (c : F),
      ballot_transcript (encrypt_ballot g h s (set_challenges rd c)) =
      ballot_transcript (encrypt_ballot g h s rd).
    Proof.
      intros; unfold ballot_transcript, encrypt_ballot, set_challenges; cbn [fst snd br_pos br_pair].
      f_equal.
      + f_equal; f_equal; apply VectorSpec.map_ext; intro i.
        rewrite !(Vector.nth_map _ _ i i eq_refl), !fin_enum_nth.
        unfold encrypt_pos, pos_cipher; cbn [fst snd ps_r ps_uscs ps_c].
        rewrite (Vector.nth_map _ _ i i eq_refl); cbn [ps_r ps_uscs ps_c].
        f_equal; f_equal; apply prove_membership_announcement.
      + f_equal; f_equal; apply VectorSpec.map_ext; intro i;
        f_equal; f_equal; apply VectorSpec.map_ext; intro j.
        rewrite !nth_mat.
        rewrite (Vector.nth_map _ _ i i eq_refl); rewrite (Vector.nth_map _ _ i i eq_refl);
        rewrite (Vector.nth_map _ _ j j eq_refl); rewrite (Vector.nth_map _ _ j j eq_refl).
        unfold encrypt_pair, pair_bit, pair_bit_proof, pair_mem_proof;
        cbn [fst snd ps_r pr_rb pr_uscs_b pr_c_b pr_uscs_m pr_c_m].
        f_equal; f_equal.
        * rewrite !generate_enc_proof_commitment_announcement; reflexivity.
        * f_equal; apply prove_membership_announcement.
    Qed.

    (** Completeness of the non-interactive ballot: for positions
        [s_i ≤ m] and any hash function [H], [nizk_verify_ballot] accepts
        [nizk_encrypt_ballot s rd]. *)
    Theorem nizk_ballot_valid : ∀ (n : nat) (g h : G) (H : list (G * G) -> F)
      (s : Vector.t nat (S n)) (rd : ballot_rand (n := n)),
      (∀ i, s[@i] <= S n) ->
      nizk_verify_ballot g h H (nizk_encrypt_ballot g h H s rd) = true.
    Proof.
      intros * hs; unfold nizk_verify_ballot, nizk_encrypt_ballot, ballot_challenge.
      (* The hash input of the recomputed ballot equals that of the first
         pass, so the challenge c is consistent. *)
      rewrite ballot_transcript_set_challenges.
      apply andb_true_iff; split; [| apply ballot_valid; exact hs].
      set (c := H (ballot_transcript (encrypt_ballot g h s rd))).
      unfold challenges_are; apply andb_true_iff; split.
      + apply forall_fin_true; intro i; unfold is_chal.
        unfold encrypt_ballot, set_challenges; cbn [fst snd br_pos].
        rewrite !(Vector.nth_map _ _ i i eq_refl), !fin_enum_nth.
        rewrite (Vector.nth_map _ _ i i eq_refl).
        unfold encrypt_pos; cbn [snd ps_c].
        rewrite (prove_membership_challenge n).
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
      + apply forall_fin_true; intro i; apply forall_fin_true; intro j; unfold is_chal.
        unfold encrypt_ballot, set_challenges; cbn [fst snd br_pos br_pair].
        rewrite !nth_mat.
        rewrite (Vector.nth_map _ _ i i eq_refl); rewrite (Vector.nth_map _ _ i i eq_refl);
        rewrite (Vector.nth_map _ _ j j eq_refl); rewrite (Vector.nth_map _ _ j j eq_refl).
        unfold encrypt_pair, pair_bit_proof, pair_mem_proof; cbn [fst snd pr_c_b pr_c_m].
        rewrite generate_enc_proof_challenge, (prove_membership_challenge (n + S n)).
        destruct (Fdec c c) as [_ | hne]; [reflexivity | contradiction].
    Qed.

    (** *** Decrypted aggregate *)

    (** [1 ^ r = 1]. *)
    Lemma pow_gid : ∀ (r : F), gid ^ r = gid.
    Proof.
      intros r; exact (@vid_identity F (@eq F) zero one add mul sub div opp inv
        G (@eq G) gid ginv gop gpow Hvec r).
    Qed.

    (** [margin_count ss i j] is the number of position vectors in [ss]
        with [s_i < s_j]: the pairwise margin [D_ij] of the election. *)
    Definition margin_count {m N : nat} (ss : Vector.t (Vector.t nat m) N) (i j : Fin.t m) : nat :=
      Vector.fold_right (fun s acc => (if Nat.ltb s[@i] s[@j] then 1 else 0) + acc)%nat ss 0.

    (** [D_ij ≤ N]. *)
    Lemma margin_count_le : ∀ {m N : nat} (ss : Vector.t (Vector.t nat m) N) (i j : Fin.t m),
      margin_count ss i j <= N.
    Proof.
      intros m N; induction N as [| N ih]; intros ss i j.
      + rewrite (vector_inv_0 ss); reflexivity.
      + destruct (vector_inv_S ss) as (s & ss' & ->); unfold margin_count in *; cbn [Vector.fold_right].
        specialize (ih ss' i j); destruct (Nat.ltb s[@i] s[@j]); lia.
    Qed.

    (** If every ballot's pair bit [(i, j)] decrypts to [g ^ [s_i < s_j] ]
        for the positions [ss_k] (as [ballot_sound] guarantees), then the
        aggregate entry [(i, j)] decrypts to [g ^ D_ij]. *)
    Lemma cdec_aggregate : ∀ {m N : nat} (x : F) (g : G) (bs : Vector.t (@ballot m) N)
      (ss : Vector.t (Vector.t nat m) N) (i j : Fin.t m),
      (∀ k, plaintext_bit x bs[@k] i j =
        g ^ (if Nat.ltb ss[@k][@i] ss[@k][@j] then one else zero)) ->
      cdec x (aggregate_margins bs)[@i][@j] = g ^ natF (margin_count ss i j).
    Proof.
      intros m N x g; induction N as [| N ih]; intros bs ss i j hb.
      + rewrite (vector_inv_0 bs), (vector_inv_0 ss).
        unfold aggregate_margins; cbn [Vector.fold_right].
        rewrite !Vector.const_nth; unfold cid, cdec; cbn.
        rewrite pow_gid, gop_ginv_r, pow_zero; reflexivity.
      + destruct (vector_inv_S bs) as (b & bs' & ->).
        destruct (vector_inv_S ss) as (s & ss' & ->).
        change (aggregate_margins (b :: bs')) with
          (Vector.map2 (Vector.map2 cmul) (ballot_bits b) (aggregate_margins bs')).
        rewrite (Vector.nth_map2 _ _ _ i i i eq_refl eq_refl),
          (Vector.nth_map2 _ _ _ j j j eq_refl eq_refl).
        rewrite cdec_cmul, (ih bs' ss' i j (fun k => hb (Fin.FS k))).
        unfold ballot_bits; rewrite !(Vector.nth_map _ _ _ _ eq_refl).
        pose proof (hb Fin.F1) as h0; unfold plaintext_bit in h0; cbn [Vector.nth] in h0.
        rewrite h0; unfold margin_count; cbn [Vector.fold_right].
        rewrite natF_add, pow_add; f_equal; f_equal.
        destruct (Nat.ltb s[@i] s[@j]); cbn [nat_to_F]; field.
    Qed.

    (** *** Special honest-verifier zero knowledge

        Distributions are the list-based ones of [Probability/Distr.v];
        two distributions are equal when they are permutations of each
        other. *)

    (** Independent product of two distributions. *)
    Definition dist_pair {A B : Type} (da : dist A) (db : dist B) : dist (A * B) :=
      Bind da (fun a => Bind db (fun b => Ret (a, b))).

    (** Independent product of a vector of distributions. *)
    Fixpoint dist_vec {A : Type} {k : nat} (ds : Vector.t (dist A) k) : dist (Vector.t A k) :=
      match ds with
      | Vector.nil _ => Ret (Vector.nil A)
      | Vector.cons _ d k' ds' =>
        Bind d (fun a => Bind (dist_vec ds') (fun v => Ret (Vector.cons A a k' v)))
      end.

    (** [dist_pair] respects permutation in both arguments. *)
    Lemma dist_pair_perm : ∀ {A B : Type} (da da' : dist A) (db db' : dist B),
      Permutation da da' -> Permutation db db' ->
      Permutation (dist_pair da db) (dist_pair da' db').
    Proof.
      intros * ha hb; unfold dist_pair.
      eapply Permutation_trans; [apply bind_perm_left; exact ha |].
      apply bind_perm_right; intros a p _.
      apply bind_perm_left; exact hb.
    Qed.

    (** [dist_vec] respects pointwise permutation. *)
    Lemma dist_vec_perm : ∀ {A : Type} {k : nat} (ds ds' : Vector.t (dist A) k),
      (∀ i, Permutation ds[@i] ds'[@i]) -> Permutation (dist_vec ds) (dist_vec ds').
    Proof.
      intros A k; induction k as [| k ih]; intros ds ds' hp.
      + rewrite (vector_inv_0 ds), (vector_inv_0 ds'); apply Permutation_refl.
      + destruct (vector_inv_S ds) as (d & dt & ->).
        destruct (vector_inv_S ds') as (d' & dt' & ->).
        cbn [dist_vec].
        eapply Permutation_trans; [apply bind_perm_left; exact (hp Fin.F1) |].
        apply bind_perm_right; intros a p _.
        apply bind_perm_left; apply ih; intro i; exact (hp (Fin.FS i)).
    Qed.

    (** [dist_vec] over a mapped vector respects pointwise permutation of
        the function. *)
    Lemma dist_vec_map_perm : ∀ {A B : Type} {k : nat} (f f' : B -> dist A) (v : Vector.t B k),
      (∀ b, Permutation (f b) (f' b)) ->
      Permutation (dist_vec (Vector.map f v)) (dist_vec (Vector.map f' v)).
    Proof.
      intros; apply dist_vec_perm; intro i.
      rewrite !(Vector.nth_map _ _ i i eq_refl); auto.
    Qed.

    (** The prover randomness and the simulator randomness are drawn
        uniformly from the list [lf], which enumerates [F] without
        duplicates. *)
    Section ZK.
      Context (lf : list F) (Hlfn : lf <> List.nil)
        (hnd : List.NoDup lf) (hall : ∀ y : F, List.In y lf).
      Context {n : nat} (g h : G).
      Local Notation m := (S n).

      (** The real distribution of one membership proof (over uniform
          prover randomness), for witness [r] at index [rindex]. *)
      Definition mem_real_dist {k : nat} (ms : Vector.t G (2 + k)) (rindex : Fin.t (2 + k))
        (r : F) (cp : G * G) (c : F) : dist (membership_proof (2 + k)) :=
        generalised_encryption_proof_elgamal_real_distribution (F := F) (zero := zero)
          (add := add) (mul := mul) (sub := sub) (opp := opp) (G := G) (ginv := ginv)
          (gop := gop) (gpow := gpow) lf Hlfn rindex r cp g h ms c.
      (** The simulated distribution of one membership proof, from the
          statement [cp] and the challenge [c] only. *)
      Definition mem_sim_dist {k : nat} (ms : Vector.t G (2 + k)) (cp : G * G) (c : F) :
        dist (membership_proof (2 + k)) :=
        generalised_encryption_proof_elgamal_simulator_distribution (F := F) (zero := zero)
          (add := add) (sub := sub) (opp := opp) (G := G) (ginv := ginv)
          (gop := gop) (gpow := gpow) lf Hlfn g h cp ms c.

      (** SHVZK of one membership proof: if [cp = Enc(mv; r)] and
          [ms[rindex] = g ^ mv], the real and simulated distributions are
          permutations of each other. Instance of
          [generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm]. *)
      Lemma mem_zk : ∀ {k : nat} (ms : Vector.t G (2 + k)) (rindex : Fin.t (2 + k))
        (r mv : F) (cp : G * G) (c : F),
        cp = enc g h mv r -> ms[@rindex] = g ^ mv ->
        Permutation (mem_real_dist ms rindex r cp c) (mem_sim_dist ms cp c).
      Proof.
        intros * hc hm; subst cp; unfold mem_real_dist, mem_sim_dist, enc.
        apply generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm;
        [| exact hnd | exact hall].
        split; [reflexivity | rewrite hm, gop_cancel; reflexivity].
      Qed.

      (** Real and simulated distributions of a position proof. *)
      Definition pos_real_dist (s : nat) (r c : F) : dist (membership_proof (S m)) :=
        mem_real_dist (msgs_pos (m := m) g) (fin_of_nat_default s m) r (enc g h (natF s) r) c.
      Definition pos_sim_dist (cp : G * G) (c : F) : dist (membership_proof (S m)) :=
        mem_sim_dist (msgs_pos (m := m) g) cp c.

      (** SHVZK of a position proof for [s ≤ m]. *)
      Lemma pos_zk : ∀ (s : nat) (r c : F), s <= m ->
        Permutation (pos_real_dist s r c) (pos_sim_dist (enc g h (natF s) r) c).
      Proof.
        intros * hs; unfold pos_real_dist, pos_sim_dist.
        apply (mem_zk _ _ _ (natF s)); [reflexivity |].
        unfold msgs_pos; rewrite (nth_enum _ _ (fun k => g ^ natF k)).
        fin_idx_default; reflexivity.
      Qed.

      (** The branch of the bit proof: [F1] for [b = 0], [FS F1] otherwise. *)
      Definition bit_index (b : F) : Fin.t 2 :=
        if Fdec b zero then Fin.F1 else Fin.FS Fin.F1.
      (** Real and simulated distributions of the bit proof, the approval
          prover over [ [g ^ 0; g ^ 1] ]. *)
      Definition bit_real_dist (b rb c : F) : dist (@sigma_proto F (G * G) 2 3 2) :=
        mem_real_dist [g ^ zero; g ^ one] (bit_index b) rb (enc g h b rb) c.
      Definition bit_sim_dist (cb : G * G) (c : F) : dist (@sigma_proto F (G * G) 2 3 2) :=
        mem_sim_dist [g ^ zero; g ^ one] cb c.

      (** SHVZK of a bit proof for [b ∈ {0, 1}]. *)
      Lemma bit_zk : ∀ (b rb c : F), (b = zero ∨ b = one) ->
        Permutation (bit_real_dist b rb c) (bit_sim_dist (enc g h b rb) c).
      Proof.
        intros * hb; unfold bit_real_dist, bit_sim_dist.
        apply (mem_zk _ _ _ b); [reflexivity |].
        unfold bit_index; destruct (Fdec b zero) as [-> | hne]; [reflexivity |].
        destruct hb as [hb | hb]; [contradiction | rewrite hb; reflexivity].
      Qed.

      (** Real distribution of the combined pair proof. Only the arguments
          [ri], [rj], [rb], [c], [sin], [sjn] are used; the first two field
          arguments [si], [sj] are ignored (callers pass [ri], [rj] there). *)
      Definition pair_real_dist (si sj ri rj rb c : F) (sin sjn : nat) :
        dist (membership_proof (S m + m)) :=
        let b : F := if Nat.ltb sin sjn then one else zero in
        mem_real_dist (msgs_pair (m := m) g) (pair_index (n := n) sin sjn)
          (natF (@pair_shift m) * rb + sub rj ri)
          (cmul (cpow (enc g h b rb) (natF (@pair_shift m)))
            (enc g h (sub (natF sjn) (natF sin)) (sub rj ri))) c.
      (** Simulated distribution of the combined pair proof, from the bit
          ciphertext [cb], the derived [cd = Enc(δ)] and the challenge. *)
      Definition pair_sim_dist (cb cd : G * G) (c : F) : dist (membership_proof (S m + m)) :=
        mem_sim_dist (msgs_pair (m := m) g) (cmul (cpow cb (natF (@pair_shift m))) cd) c.

      (** SHVZK of the combined pair proof for positions [sin, sjn ≤ m];
          the index computation is the same as in [encrypt_pair_valid]. *)
      Lemma pair_zk : ∀ (ri rj rb c : F) (sin sjn : nat), sin <= m -> sjn <= m ->
        Permutation (pair_real_dist ri rj ri rj rb c sin sjn)
          (pair_sim_dist (enc g h (if Nat.ltb sin sjn then one else zero) rb)
            (enc g h (sub (natF sjn) (natF sin)) (sub rj ri)) c).
      Proof.
        intros * hi hj; unfold pair_real_dist, pair_sim_dist; cbv zeta.
        rewrite enc_pow, enc_mul.
        unfold msgs_pair, pair_index.
        (* Same index computation as in encrypt_pair_valid. *)
        destruct (Nat.ltb sin sjn) eqn:hlt.
        + apply Nat.ltb_lt in hlt.
          eapply mem_zk.
          * apply enc_ext; [reflexivity | field].
          * etransitivity; [exact (nth_enum_append _ (S (S n)) (S n)
              (fun k => ginv (g ^ natF k)) (fun k => g ^ natF (pair_shift + S k))
              (fin_of_nat_default (S n + (sjn - sin)) (S n + S n))) |].
            fin_idx_default.
            rewrite (proj2 (Nat.ltb_ge _ _)); [| lia].
            f_equal.
            replace (S (S n + (sjn - sin) - S (S n)))%nat with (sjn - sin)%nat by lia.
            rewrite natF_add, (natF_sub sjn sin); [field | lia].
        + apply Nat.ltb_ge in hlt.
          eapply mem_zk.
          * apply enc_ext; [reflexivity | field].
          * etransitivity; [exact (nth_enum_append _ (S (S n)) (S n)
              (fun k => ginv (g ^ natF k)) (fun k => g ^ natF (pair_shift + S k))
              (fin_of_nat_default (sin - sjn) (S n + S n))) |].
            fin_idx_default.
            rewrite (proj2 (Nat.ltb_lt _ _)); [| lia].
            rewrite <- pow_opp; f_equal.
            rewrite (natF_sub sin sjn); [field | lia].
      Qed.

      (** The proofs of a whole ballot: position proofs, then for every
          pair the bit proof and the combined membership proof. *)
      Definition ballot_proofs : Type :=
        Vector.t (membership_proof (S m)) m *
        Vector.t (Vector.t (@sigma_proto F (G * G) 2 3 2 * membership_proof (S m + m)) m) m.

      (** The honest voter's proofs as a distribution, for positions [s],
          position randomness [rs], bit randomness [rb] and challenges
          [cs], [cb], [cm]. *)
      Definition ballot_real_dist (s : Vector.t nat m) (rs cs : Vector.t F m)
        (rb cb cm : Vector.t (Vector.t F m) m) : dist ballot_proofs :=
        dist_pair
          (dist_vec (Vector.map (fun i => pos_real_dist s[@i] rs[@i] cs[@i]) (fin_enum m)))
          (dist_vec (Vector.map (fun i => dist_vec (Vector.map (fun j =>
            dist_pair
              (bit_real_dist (if Nat.ltb s[@i] s[@j] then one else zero) rb[@i][@j] cb[@i][@j])
              (pair_real_dist rs[@i] rs[@j] rs[@i] rs[@j] rb[@i][@j] cm[@i][@j] s[@i] s[@j]))
            (fin_enum m))) (fin_enum m))).

      (** The simulator: from the position ciphertexts [cps], the bit
          ciphertexts [cbs] and the challenges only; the [Enc(δ)]
          ciphertexts are computed from the positions, as the verifier
          does. *)
      Definition ballot_sim_dist (cps : Vector.t (G * G) m)
        (cbs : Vector.t (Vector.t (G * G) m) m) (cs : Vector.t F m)
        (cb cm : Vector.t (Vector.t F m) m) : dist ballot_proofs :=
        dist_pair
          (dist_vec (Vector.map (fun i => pos_sim_dist cps[@i] cs[@i]) (fin_enum m)))
          (dist_vec (Vector.map (fun i => dist_vec (Vector.map (fun j =>
            dist_pair (bit_sim_dist cbs[@i][@j] cb[@i][@j])
              (pair_sim_dist cbs[@i][@j] (cmul cps[@j] (cinv cps[@i])) cm[@i][@j]))
            (fin_enum m))) (fin_enum m))).

      (** The position and bit ciphertexts of the honest ballot. *)
      Definition honest_pos (s : Vector.t nat m) (rs : Vector.t F m) : Vector.t (G * G) m :=
        Vector.map (fun i => enc g h (natF s[@i]) rs[@i]) (fin_enum m).
      Definition honest_bits (s : Vector.t nat m) (rb : Vector.t (Vector.t F m) m) :
        Vector.t (Vector.t (G * G) m) m :=
        Vector.map (fun i => Vector.map (fun j =>
          enc g h (if Nat.ltb s[@i] s[@j] then one else zero) rb[@i][@j]) (fin_enum m)) (fin_enum m).

      (** SHVZK of the ballot: for valid positions, the honest proofs are
          distributed exactly as the simulated ones, which depend only on
          the ciphertexts and challenges. Hence the proofs reveal nothing
          beyond the ciphertexts. Proof: the distributions are independent
          products, so the result follows cell by cell from [pos_zk],
          [bit_zk] and [pair_zk]. *)
      Theorem ballot_zk : ∀ (s : Vector.t nat m) (rs cs : Vector.t F m)
        (rb cb cm : Vector.t (Vector.t F m) m),
        (∀ i, s[@i] <= m) ->
        Permutation (ballot_real_dist s rs cs rb cb cm)
          (ballot_sim_dist (honest_pos s rs) (honest_bits s rb) cs cb cm).
      Proof.
        intros * hs; unfold ballot_real_dist, ballot_sim_dist.
        apply dist_pair_perm.
        + apply dist_vec_perm; intro i.
          rewrite (Vector.nth_map _ _ i i eq_refl).
          rewrite (Vector.nth_map _ _ i i eq_refl); rewrite !fin_enum_nth.
          unfold honest_pos; rewrite (Vector.nth_map _ _ i i eq_refl); rewrite !fin_enum_nth.
          apply pos_zk, hs.
        + apply dist_vec_perm; intro i.
          rewrite (Vector.nth_map _ _ i i eq_refl); rewrite (Vector.nth_map _ _ i i eq_refl);
          rewrite !fin_enum_nth.
          apply dist_vec_perm; intro j.
          rewrite (Vector.nth_map _ _ j j eq_refl); rewrite (Vector.nth_map _ _ j j eq_refl);
          rewrite !fin_enum_nth.
          unfold honest_bits, honest_pos.
          rewrite (Vector.nth_map _ _ i i eq_refl); rewrite (Vector.nth_map _ _ i i eq_refl);
          rewrite !fin_enum_nth.
          rewrite (Vector.nth_map _ _ j j eq_refl); rewrite (Vector.nth_map _ _ j j eq_refl);
          rewrite !fin_enum_nth.
          apply dist_pair_perm.
          * apply bit_zk; destruct (Nat.ltb s[@i] s[@j]); [right | left]; reflexivity.
          * rewrite enc_div; apply pair_zk; apply hs.
      Qed.
    End ZK.

  End Proofs.
End Schulze.
