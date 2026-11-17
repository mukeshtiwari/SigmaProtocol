(** * Proof of Correct Encryption: Disjunctive Chaum–Pedersen *)

(** This file formalises the disjunctive (OR) zero-knowledge proof that an
    ElGamal ciphertext encrypts one value from a public list, as used in
    Helios-style ballots to show that each encrypted vote is, say, [g ^ 0]
    or [g ^ 1] without revealing which. The construction is the
    Cramer–Damgård–Schoenmakers OR-composition (Crypto 1994) of
    Chaum–Pedersen proofs; the code structure follows the Helios
    implementation of disjunctive proofs ([helios/crypto/elgamal.py]).

    Statement: generator [g], public key [h], ciphertext [(c₁, c₂)] and a
    list of candidate plaintexts [ms = [m₀; …; m₍ₖ₋₁₎]] (group elements,
    [k = 2 + n ≥ 2]). The prover knows the encryption randomness [x] and an
    index [rindex] such that

    [[
      g ^ x = c₁   ∧   h ^ x = c₂ · m_rindex⁻¹
    ]]

    i.e. [(c₁, c₂) = (g ^ x, m_rindex · h ^ x)]. Each branch [i] is a
    Chaum–Pedersen statement about [(g, h, c₁, c₂ · mᵢ⁻¹)].

    Protocol (with main challenge [c]):

    - for every false branch [i ≠ rindex] the prover picks a response [uᵢ]
      and a sub-challenge [cᵢ] and simulates announcements
      [(g ^ uᵢ · c₁ ^ (-cᵢ), h ^ uᵢ · (c₂ · mᵢ⁻¹) ^ (-cᵢ))];
    - for the true branch it picks [u] and announces [(g ^ u, h ^ u)];
    - after receiving [c] it sets the true sub-challenge to
      [c_rindex = c - Σ_{i ≠ rindex} cᵢ] and the response to
      [u + c_rindex · x];
    - the transcript carries the challenge vector [c :: [c₀; …; c₍ₖ₋₁₎]].

    The verifier [generalised_accepting_encryption_proof_elgamal] checks that
    the head challenge equals the sum of the sub-challenges and that every
    branch is an accepting Chaum–Pedersen transcript for its sub-challenge.
    Randomness is a single vector [uscs] of [k + (k - 1)] field elements: [k]
    responses/randomness values followed by [k - 1] free sub-challenges.

    Main results:

    - verifier characterisation:
      [generalised_accepting_elgamal_conversations_correctness] (and the
      reject and [_gen] variants);
    - completeness:
      [generalised_construct_encryption_proof_elgamal_real_completeness];
    - special soundness: [generalised_accepting_elgamal_soundness_main]:
      two accepting transcripts with the same announcements and distinct
      main challenges yield [y] and an index [f] with [g ^ y = c₁] and
      [h ^ y = c₂ · m_f⁻¹], i.e. the ciphertext encrypts some [m_f];
    - simulator completeness:
      [generalised_construct_encryption_proof_elgamal_simulator_completeness];
    - special honest-verifier zero-knowledge, weak form
      ([generalised_encryption_proof_elgamal_special_honest_verifier_zkp]:
      equal distributions of verdicts and probabilities) and strong form
      ([generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm]:
      real and simulated transcript distributions are permutations of each
      other when the randomness list [lf] enumerates the field).

    The strong zero-knowledge proof uses an explicit bijection [or_shift] on
    the randomness vector that maps the real prover’s coins to the
    simulator’s coins producing the same transcript. The file relies on the
    Schnorr verifier [accepting_conversation] from [Sigma] and on vector
    utilities from [Utility.Util] and [Utility.Insert]. *)
From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos Permutation Arith.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import Util Insert.
From ExtLib Require Import Monad.
From Crypto Require Import Sigma.

Import MonadNotation
  VectorNotations EqNotations.

#[local] Open Scope monad_scope.

(** ** Parameters *)
Section DL.
  (** The scalar field [F] with decidable equality [Fdec] (needed by the
      verifier to compare challenges). *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G] with decidable equality [Gdec]. *)
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
      response vectors. Announcements here are pairs [(G * G)], one per
      branch. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** The disjunctive encryption proof *)
  Section EncProof.
    (** *** Prover, simulator, verifier and distributions *)
    Section Def.

      (** Announcements of the real prover, with the true branch at
          position [m] in a list of [m + (1 + n)] candidates. The randomness
          vector [uscs] is split into responses/randomness [us] (length
          [m + (1 + n)]) and free sub-challenges [cs] (length [m + n]). For
          every false branch the announcement is simulated as
          [(g ^ uᵢ · c₁ ^ (-cᵢ), h ^ uᵢ · (c₂ · mᵢ⁻¹) ^ (-cᵢ))]; the true
          branch gets the honest Chaum–Pedersen announcement [(g ^ u, h ^ u)]. *)
      Definition construct_encryption_proof_elgamal_commitment {m n : nat}
        (uscs : Vector.t F ((m + (1 + n)) + (m + n)))
        (ms : Vector.t G (m + (1 + n))) (g h : G) (cp : G * G) :
        Vector.t (G * G) (m + (1 + n)).
      Proof.
        destruct (splitat (m + (1 + n)) uscs) as (us & cs).
        destruct (splitat m us) as (usl & usrh).
        destruct (vector_inv_S usrh) as (u & usr & _).
        destruct (splitat m cs) as (csl & csr).
        destruct cp as (c₁, c₂).
        destruct (splitat m ms) as (msl & mslt).
        destruct (vector_inv_S mslt) as (_ & msr & _).
        set (comml := zip_with (fun ui ci => (ui, ci)) usl csl).
        set (commitl := zip_with (fun mi '(ui, ci) =>
          (gop (g^ui) (c₁^(opp ci)),
          gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) msl comml).
        set (com := (g^u, h^u)).
        set (commr := zip_with (fun ui ci => (ui, ci)) usr csr).
        set (commitr := zip_with (fun mi '(ui, ci) =>
          (gop (g^ui) (c₁^(opp ci)),
          gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) msr commr).
        exact (commitl ++ [com] ++ commitr).
      Defined.

      (** Real prover with the true branch at position [m]: announcements
          from [construct_encryption_proof_elgamal_commitment], challenge
          vector [c :: csl ++ [cb] ++ csr] with
          [cb = c - Σ (csl ++ csr)], and responses [usl ++ [u + cb · x] ++ usr].
          [x] is the encryption randomness. *)
      Definition construct_encryption_proof_elgamal_real {m n : nat} (x : F)
        (uscs : Vector.t F ((m + (1 + n)) + (m + n)))
        (ms : Vector.t G (m + (1 + n))) (g h : G) (cp : G * G) (c : F) :
         @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
      Proof.
        set (comm := @construct_encryption_proof_elgamal_commitment m n
          uscs ms g h cp).
        destruct (splitat (m + (1 + n)) uscs) as (us & cs).
        destruct (splitat m us) as (usl & usrh).
        destruct (vector_inv_S usrh) as (u & usr & _).
        destruct (splitat m cs) as (csl & csr).
        (* The true-branch sub-challenge is whatever is left of [c]. *)
        remember (c - (Vector.fold_right add (csl ++ csr) zero)) as cb.
        remember (u + cb * x) as res.
        refine (comm;
          c :: csl ++ [cb] ++ csr ; usl ++ [res] ++ usr).
      Defined.

      (** Real prover for [2 + n] candidates with the true branch at the
          index [rindex : Fin.t (2 + n)]. It uses [vector_fin_app_pred] to
          rewrite [2 + n] as [m₁ + (1 + m₂)] with [m₁ = rindex], and then calls
          [construct_encryption_proof_elgamal_real] at that split. *)
      Definition generalised_construct_encryption_proof_elgamal_real {n : nat}
          (rindex : Fin.t (2 + n)) (x : F) (uscs : Vector.t F ((2 + n) + (1 + n)))
          (ms : Vector.t G (2 + n))
          (g h : G) (cp : G * G) (c : F) :
          @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n).
      Proof.
        destruct (splitat (2 + n) uscs) as (us & cs).
        destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as
        (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
        destruct pfaa as [pfa].
        destruct pfbb as [pfb].
        destruct haa as [ha].
        destruct ha as (ha & hb & hc & hd).
        generalize dependent ms. generalize dependent us.
        generalize dependent cs. generalize dependent rindex.
        cbn in * |- *. rewrite !pfa, !pfb. cbn.
        intros rindex ha cs hb us hc hd ms.
        pose proof (@construct_encryption_proof_elgamal_real m₁ m₂
         x (us ++ cs) ms g h cp c) as he. exact he.
      Defined.

      (** Simulator: from randomness [uscs = us ++ cs] and challenge [c],
          it sets the sub-challenges to [cm = (c - Σ cs) :: cs] and simulates
          every branch with response [usᵢ] and sub-challenge [cmᵢ]. It uses no
          witness, and its output is accepting for every statement. *)
      Definition generalised_construct_encryption_proof_elgamal_simulator {n : nat}
        (uscs : Vector.t F ((2 + n) + (1 + n)))
        (ms : Vector.t G ((2 + n))) (g h : G) (cp : G * G)
        (c : F) :  @sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n)).
      Proof.
        destruct (splitat ((2 + n)) uscs) as (us & cs).
        destruct cp as (c₁, c₂).
        set (cm := (c - (Vector.fold_right add cs zero) :: cs)).
        set (comm := zip_with (fun ui ci => (ui, ci)) us cm).
        set (commit := zip_with (fun mi '(ui, ci) =>
          (gop (g^ui) (c₁^(opp ci)),
          gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) ms comm).
        refine(commit; c :: cm; us).
      Defined.

      (** Branch-wise verifier (local helper): for transcripts
          [(a; c; r)] with one announcement pair, sub-challenge and response
          per candidate, returns [true] iff for every [i]
          [g ^ rᵢ = aᵢ.1 · c₁ ^ cᵢ] and [h ^ rᵢ = aᵢ.2 · (c₂ · mᵢ⁻¹) ^ cᵢ]. *)
      #[local]
      Definition generalised_accepting_encryption_proof_elgamal_supplement {n : nat}
        (g h : G) (ms : Vector.t G n) (cp : G * G)
        (pf : @sigma_proto F (G * G) n n n) : bool.
      Proof.
        revert n g h ms cp pf.
        refine
          (fix Fn n :=
          match n with
          | 0 => fun g h ms cp pf => true
          | S n' => fun g h ms cp pf =>
            match pf with
            | (a; c; r) => _
            end
          end).
        destruct (vector_inv_S a) as ((ah₁, ah₂) & asr & _).
        destruct (vector_inv_S c) as (ch & csr & _).
        destruct (vector_inv_S r) as (rh & rsr & _).
        destruct (vector_inv_S ms) as (m & msr & _).
        destruct cp as (c₁, c₂).
        exact ((@accepting_conversation F G gop gpow Gdec g c₁ ([ah₁]; [ch]; [rh])) &&
          (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv m)) ([ah₂]; [ch]; [rh])) &&
          (Fn _ g h msr (c₁, c₂) (asr; csr; rsr))).
      Defined.

      (** Verifier of the disjunctive proof: a transcript
          [(a; c :: cs; r)] is accepted iff [c = Σ cs] and every branch
          passes the Chaum–Pedersen check of
          [generalised_accepting_encryption_proof_elgamal_supplement]. *)
      Definition generalised_accepting_encryption_proof_elgamal  {n : nat}
        (ms : Vector.t G n)  (g h : G) (cp : G * G)
        (pf : @sigma_proto F (G * G) n (1 + n) n) : bool.
      Proof.
        refine
          match pf with
          |(a; css; r) => _
          end.
        destruct (vector_inv_S css) as (c & cs & _).
        refine
          match Fdec c (Vector.fold_right add cs zero) with
          | left _ =>
              generalised_accepting_encryption_proof_elgamal_supplement g h ms cp (a; cs; r)
          | right _ => false
          end.
      Defined.

      (** Distribution of real transcripts: draw all [(2 + n) + (1 + n)]
          coins independently and uniformly from [lf] and run the real
          prover. *)
      Definition generalised_encryption_proof_elgamal_real_distribution
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil) (rindex : Fin.t (2 + n))
        (x : F) (cp : G * G) (g h : G) (ms : Vector.t G ((2 + n))) (c : F) :
        dist (@sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))) :=
        uscs <- repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) (((2 + n)) + (1 + n)) ;;
        Ret (generalised_construct_encryption_proof_elgamal_real
          rindex x uscs ms g h cp c).

      (** Distribution of simulated transcripts: draw the same number of
          coins uniformly from [lf] and run the simulator. *)
      Definition generalised_encryption_proof_elgamal_simulator_distribution
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
        (g h : G) (cp : G * G) (ms : Vector.t G ((2 + n))) (c : F) :
        dist (@sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))) :=
        uscs <- repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) (((2 + n)) + (1 + n)) ;;
        Ret (generalised_construct_encryption_proof_elgamal_simulator
          uscs ms g h cp c).

    End Def.

    (** *** Characterisation of the verifier

        The lemmas below unfold the boolean verifiers into explicit
        per-branch Schnorr checks, in the accepting and rejecting
        directions. *)
    Section Proofs.

        (** If the branch-wise verifier accepts, then for every branch [f]
            both Schnorr checks (base [g] with value [c₁], and base [h] with
            value [c₂ · m_f⁻¹]) accept. By induction on [n]. *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_forward :
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = true ->
          (match s with
          | (a; c; r) =>
            ∀ f : Fin.t n,
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c f]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c f]; [nth r f])) = true
          end).
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (a₁; c₁; r₁) => fun Hb => _
              end eq_refl).
            intros f;
            inversion f.
          +
            intros * Ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (au; cu; ru) => fun Hb => _
              end eq_refl); intro f.
            destruct (vector_inv_S au) as ((ah₁, ah₂) & aut & He).
            destruct (vector_inv_S cu) as (cuh & cut & Hf).
            destruct (vector_inv_S ru) as (ruh & rut & Hg).
            destruct (vector_inv_S ms) as (msh & mst & Hi).
            destruct (fin_inv_S _ f) as [Hj | (fs & Hj)];
            subst; simpl.
            ++
              cbn in Ha.
              eapply andb_true_iff in Ha.
              destruct Ha as (Hal  &  Har).
              split. eapply andb_true_iff in Hal.
              destruct Hal as [Hall Halr]. exact Hall.
              eapply andb_true_iff in Hal.
              destruct Hal as [Hall Halr]. exact Halr.
            ++
              simpl in Ha;
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              eapply andb_true_iff in Hal.
              destruct Hal as [Hall Halr].
              specialize (IHn g h mst c₁ c₂ (aut; cut; rut) Har).
              cbn in IHn.
              eapply IHn.
        Qed.

        (** If the branch-wise verifier rejects, some branch has a failing
            Schnorr check. *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_reject_forward :
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = false ->
          (match s with
          | (a; c; r) =>
            ∃ f : Fin.t n,
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c f]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c f]; [nth r f])) = false
          end).
        Proof.
          induction n as [|n ihn].
          +
            intros * ha.
            cbn in ha.
            congruence.
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (au; cu; ru) => fun hb => _
              end eq_refl).
            rewrite hb in ha.
            destruct (vector_inv_S au) as ((ah₁, ah₂) & aut & He).
            destruct (vector_inv_S cu) as (cuh & cut & Hf).
            destruct (vector_inv_S ru) as (ruh & rut & Hg).
            destruct (vector_inv_S ms) as (msh & mst & Hi).
            subst. simpl in ha.
            eapply andb_false_iff in ha.
            destruct ha as [ha | ha].
            ++
              exists Fin.F1.
              cbn.
              eapply andb_false_iff in ha.
              exact ha.
            ++
              destruct (ihn g h mst c₁ c₂ (aut; cut; rut) ha) as (f & [ihnn | ihnn]).
              +++
                exists (Fin.FS f).
                left. exact ihnn.
              +++
                exists (Fin.FS f).
                right. exact ihnn.
        Qed.

        (** Converse of
            [generalised_accepting_encryption_proof_elgamal_supplement_forward]. *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_backward :
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          (match s with
          | (a; c; r) =>
            ∀ f : Fin.t n,
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c f]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c f]; [nth r f])) = true
          end) -> generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 ms);
            cbn; reflexivity.
          +
            intros * Ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (au; cu; ru) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S ms) as (msh & mstl & Hd).
            destruct (vector_inv_S au) as ((auh₁, auh₂) & autl & He).
            destruct (vector_inv_S cu) as (cuh & cutl & Hf).
            destruct (vector_inv_S ru) as (ruh & rutl & Hg).
            subst. simpl.
            eapply andb_true_iff.
            split.
            ++
              pose proof (Ha Fin.F1) as Hi.
              cbn in Hi.
              eapply andb_true_iff.
              exact Hi.
            ++
              eapply IHn.
              intro f.
              specialize (Ha (Fin.FS f)).
              cbn in Ha.
              exact Ha.
        Qed.

        (** Converse of
            [generalised_accepting_encryption_proof_elgamal_supplement_reject_forward]. *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_reject_backward :
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          (match s with
          | (a; c; r) =>
            ∃ f : Fin.t n,
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c f]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c f]; [nth r f])) = false
          end) ->
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = false.
        Proof.
          induction n as [|n ihn].
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (au; cu; ru) => fun Hb => _
              end eq_refl).
            rewrite Hb in ha.
            destruct ha as (f & ha).
            refine match f with end.
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (au; cu; ru) => fun Hb => _
              end eq_refl).
            rewrite Hb in ha.
            destruct (vector_inv_S ms) as (msh & mstl & Hd).
            destruct (vector_inv_S au) as ((auh₁, auh₂) & autl & He).
            destruct (vector_inv_S cu) as (cuh & cutl & Hf).
            destruct (vector_inv_S ru) as (ruh & rutl & Hg).
            destruct ha as (f & [ha | ha]);
            destruct (fin_inv_S _ f) as [Hj | (fs & Hj)];
            subst.
            ++
              simpl. cbn in ha.
              rewrite ha.
              reflexivity.
            ++
              simpl. cbn in ha.
              eapply andb_false_iff.
              right. eapply ihn.
              exists fs. left.
              exact ha.
            ++
              simpl. cbn in ha.
              rewrite ha.
              eapply andb_false_iff.
              left. eapply andb_false_iff.
              right. reflexivity.
            ++
              simpl. cbn in ha.
              eapply andb_false_iff.
              right. eapply ihn.
              exists fs.
              cbn. rewrite ha.
              right. reflexivity.
        Qed.

        (** The branch-wise verifier accepts iff every branch passes both
            Schnorr checks. *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_correctness :
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = true <->
          (match s with
          | (a; c; r) =>
            ∀ f : Fin.t n,
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c f]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c f]; [nth r f])) = true
          end).
        Proof.
          intros *; split; intro ha;
          [eapply generalised_accepting_encryption_proof_elgamal_supplement_forward |
          eapply generalised_accepting_encryption_proof_elgamal_supplement_backward]; assumption.
        Qed.

        (** The branch-wise verifier rejects iff some branch fails a Schnorr
            check. *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_reject_correctness :
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = false <->
          (match s with
          | (a; c; r) =>
            ∃ f : Fin.t n,
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c f]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c f]; [nth r f])) = false
          end).
        Proof.
          intros *; split; intro ha;
          [eapply generalised_accepting_encryption_proof_elgamal_supplement_reject_forward |
          eapply generalised_accepting_encryption_proof_elgamal_supplement_reject_backward];
          assumption.
        Qed.

        (** The branch-wise verifier distributes over concatenation of the
            candidate list and the transcript vectors: it is the conjunction
            of the verifier on the left part and on the right part. *)
        Lemma generalised_accepting_elgamal_accepting_conversations_supplement_app :
          forall (n m : nat) (g h : G) (cp : G * G)
          (msl : Vector.t G n) (msr : Vector.t G m)
          (al : Vector.t (G * G) n) (ar : Vector.t (G * G) m)
          (cl rl : Vector.t F n) (cr rr : Vector.t F m) ,
          generalised_accepting_encryption_proof_elgamal_supplement g h (msl ++ msr)
          cp  ((al ++ ar); (cl ++ cr); (rl ++ rr)) =
          generalised_accepting_encryption_proof_elgamal_supplement g h msl cp (al; cl; rl) &&
          generalised_accepting_encryption_proof_elgamal_supplement g h msr cp (ar; cr; rr).
        Proof.
           induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 msl).
            rewrite (vector_inv_0 al).
            rewrite (vector_inv_0 cl).
            rewrite (vector_inv_0 rl).
            simpl; reflexivity.
          +
            intros *.
            destruct (vector_inv_S msl) as (mslh & msltl & Hb).
            destruct (vector_inv_S al) as ((alhl, alhr) & altl & Hc).
            destruct (vector_inv_S cl) as (clh & cltl & Hd).
            destruct (vector_inv_S rl) as (rlh & rltl & He).
            destruct cp as (c₁, c₂).
            subst; simpl.
            destruct (Gdec (g ^ rlh) (gop alhl (c₁ ^ clh)));
            destruct (Gdec (h ^ rlh) (gop alhr (gop c₂ (ginv mslh) ^ clh)));
            simpl; try reflexivity.
            ++
              simpl. eapply IHn.
        Qed.

        (** If the full verifier accepts a transcript [(a; c; r)] with
            [m + (1 + n)] branches, then [hd c = Σ (tl c)] and every branch
            [f] passes both Schnorr checks with sub-challenge [c (FS f)]. *)
        Lemma generalised_accepting_elgamal_conversations_correctness_forward :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true ->
          match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end.
        Proof.
          intros * Ha.
          unfold generalised_accepting_encryption_proof_elgamal in Ha.
          refine
            (match s as s' return s = s' -> _
            with
            | (au; cu; ru) => fun Hb => _
            end eq_refl).
          rewrite Hb in Ha.
          destruct (vector_inv_S cu) as (cuh & cut & hc).
          subst. split.
          +
            destruct (Fdec cuh (fold_right add cut zero)); try congruence.
            exact e.
          +
          intro f.
          pose proof (@generalised_accepting_encryption_proof_elgamal_supplement_forward
          _ g h ms c₁ c₂ (au; cut; ru)) as hb.
          destruct (Fdec cuh (fold_right add cut zero)); try congruence.
          specialize (hb Ha).
          cbn in hb |- *.
          exact (hb f).
        Qed.

        (** If the full verifier rejects, then either the challenge sum
            check fails or some branch fails a Schnorr check. *)
        Lemma generalised_accepting_elgamal_conversations_correctness_reject_forward :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = false ->
          match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false)
          end.
        Proof.
          intros * ha.
          unfold generalised_accepting_encryption_proof_elgamal in ha.
          refine
            (match s as s' return s = s' -> _
            with
            | (au; cu; ru) => fun Hb => _
            end eq_refl).
          rewrite Hb in ha.
          destruct (vector_inv_S cu) as (cuh & cut & hc).
          subst. simpl.
          destruct (Fdec cuh (fold_right add cut zero)) as [hc | hc].
          +
            eapply generalised_accepting_encryption_proof_elgamal_supplement_reject_correctness in ha.
            destruct ha as (f & [ha | ha]).
            ++
              right.
              exists f. cbn in ha.
              rewrite ha. left; reflexivity.
            ++
              right.
              exists f. cbn in ha.
              rewrite ha. right.
              reflexivity.
          +
            left. exact hc.
        Qed.

        (** Converse of
            [generalised_accepting_elgamal_conversations_correctness_forward]. *)
        Lemma generalised_accepting_elgamal_conversations_correctness_backward :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end ->  generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true.
        Proof.
          intros * Ha.
          unfold generalised_accepting_encryption_proof_elgamal.
          refine
            (match s as s' return s = s' -> _
            with
            | (au; cu; ru) => fun Hb => _
            end eq_refl).
          destruct (vector_inv_S cu) as (cuh & cutl & Hc).
          assert (Hd : cuh = (fold_right add cutl zero)).
          {
            rewrite Hb in Ha.
            destruct Ha as [hal har].
            rewrite Hc in hal; cbn in hal.
            exact hal.
          }
          rewrite <-Hd.
          destruct (Fdec cuh cuh) as [e | e]; try congruence.
          rewrite Hb in Ha. destruct Ha as (hal & har).
          eapply generalised_accepting_encryption_proof_elgamal_supplement_backward.
          intro f. specialize (har f).
          rewrite Hc in har.
          cbn in har. cbn. exact har.
        Qed.

        (** Converse of
            [generalised_accepting_elgamal_conversations_correctness_reject_forward]. *)
        Lemma generalised_accepting_elgamal_conversations_correctness_reject_backward :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false)
          end ->
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = false.
        Proof.
          intros * Ha.
          unfold generalised_accepting_encryption_proof_elgamal.
          refine
            (match s as s' return s = s' -> _
            with
            | (au; cu; ru) => fun Hb => _
            end eq_refl).
          destruct (vector_inv_S cu) as (cuh & cutl & Hc).
          rewrite Hb in Ha.
          subst. cbn in Ha.
          destruct Ha as [Ha | (f & [Ha | Ha])].
          +
            destruct (Fdec cuh (fold_right add cutl zero)) as [hb | hb];
            try contradiction.
            reflexivity.
          +
            destruct (Fdec cuh (fold_right add cutl zero)) as [hc | hc];
            try reflexivity.
            eapply generalised_accepting_encryption_proof_elgamal_supplement_reject_correctness.
            exists f. cbn. rewrite Ha.
            left; reflexivity.
          +
            destruct (Fdec cuh (fold_right add cutl zero)) as [hc | hc];
            try reflexivity.
            eapply generalised_accepting_encryption_proof_elgamal_supplement_reject_correctness.
            exists f. cbn.
            rewrite Ha. right; reflexivity.
        Qed.

        (** Full verifier characterisation (accepting side), for candidate
            lists of length [m + (1 + n)]. *)
        Lemma generalised_accepting_elgamal_conversations_correctness:
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true <->
          match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end.
        Proof.
          intros *; split; intro ha;
          [eapply generalised_accepting_elgamal_conversations_correctness_forward |
          eapply generalised_accepting_elgamal_conversations_correctness_backward]; assumption.
        Qed.

        (** Full verifier characterisation (rejecting side), for candidate
            lists of length [m + (1 + n)]. *)
        Lemma generalised_accepting_elgamal_conversations_reject_correctness:
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = false <->
          match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false)
          end.
        Proof.
          intros *; split; intro ha;
          [eapply generalised_accepting_elgamal_conversations_correctness_reject_forward |
          eapply generalised_accepting_elgamal_conversations_correctness_reject_backward];
          assumption.
        Qed.

        (** [generalised_accepting_elgamal_conversations_correctness]
            restated for lengths of the form [2 + n], by writing [2 + n] as
            [1 + (1 + n)]. *)
        Lemma generalised_accepting_elgamal_conversations_correctness_gen :
          forall {n : nat} (g h : G) (ms : Vector.t G ((2 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true <->
          match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t ((2 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end.
        Proof.
          intros n.
          assert (ha : (∃ (m₁ m₂ : nat), (2 + n) = (m₁ + (1 + m₂)))%nat).
          exists 1, n. reflexivity.
          destruct ha as (m₁ & m₂ & ha).
          rewrite !ha.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness.
        Qed.

        (** [generalised_accepting_elgamal_conversations_reject_correctness]
            restated for lengths of the form [2 + n]. *)
         Lemma generalised_accepting_elgamal_conversations_reject_correctness_gen :
          forall {n : nat} (g h : G) (ms : Vector.t G ((2 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = false <->
          match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t ((2 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false ∨
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f)))
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = false)
          end.
        Proof.
          intros n.
          assert (ha : (∃ (m₁ m₂ : nat), (2 + n) = (m₁ + (1 + m₂)))%nat).
          exists 1, n. reflexivity.
          destruct ha as (m₁ & m₂ & ha).
          rewrite !ha.
          intros *.
          eapply generalised_accepting_elgamal_conversations_reject_correctness.
        Qed.

        (** *** Soundness, completeness and zero-knowledge

            From here on [G] is an [F]-vector space, and the [field] tactic
            is registered for [F]. *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub
            div opp inv G (@eq G) gid ginv gop gpow}.

        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        (** Special soundness for [m + (1 + n)] candidates: given two
            accepting transcripts with the same announcements [a] and
            distinct main challenges [cu₁ ≠ cu₂], there is [y] with
            [g ^ y = c₁] and an index [f] with [h ^ y = c₂ · m_f⁻¹].

            Proof idea: since [cu₁ = Σ cut₁] and [cu₂ = Σ cut₂] differ, the
            sub-challenge vectors differ at some index [f]; at that index
            the two Chaum–Pedersen transcripts share the announcement and
            have distinct challenges, so the usual extractor
            [y = (r₁ - r₂) · (c₁ - c₂)⁻¹] gives a witness for branch [f]. *)
        Lemma generalised_accepting_elgamal_soundness :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (a : t (G * G) (m + (1 + n))) (cu₁ : F) (cut₁ ru₁ : t F (m + (1 + n)))
          (cu₂ : F) (cut₂ ru₂ : t F (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h
            (c₁, c₂) (a; cu₁ :: cut₁; ru₁) = true ->
          generalised_accepting_encryption_proof_elgamal ms g h
            (c₁, c₂) (a; cu₂ :: cut₂; ru₂) = true ->
          cu₁ ≠ cu₂ -> ∃ (y : F), g^y = c₁ ∧
          ∃ (f : Fin.t (m + (1 + n))), h^y = gop c₂ (ginv (nth ms f)).
        Proof.
          intros * ha hb hc.
          (* Unfold both acceptances into the sum check and the per-branch
             Schnorr equations. *)
          eapply generalised_accepting_elgamal_conversations_correctness in ha, hb.
          cbn in ha, hb.
          generalize dependent n.
          generalize dependent cu₂.
          revert cu₁.
          (* Induction on the number [m] of branches before the split
             point. *)
          induction m as [|m ihm].
          +
            intros * hc * [ha hb] [hd he].
            destruct (vector_inv_S ms) as (msh & mstl & He).
            destruct (vector_inv_S a) as ((ahl, ahr) & alt & Hf).
            destruct (vector_inv_S ru₁) as (ruh₁ & rutl₁ & Hh).
            destruct (vector_inv_S ru₂) as (ruh₂ & rult₂ & Hi).
            destruct (vector_inv_S cut₁) as (cuth₁ & cutl₁ & Hj).
            destruct (vector_inv_S cut₂) as (cuth₂ & cutl₂ & Hk).
            subst. cbn in hc.
            remember (fold_right add cutl₁ zero) as hcl.
            remember (fold_right add cutl₂ zero) as hcr.
            (* Either the head sub-challenges differ, or they agree and the
               sums of the tails must differ. *)
            assert (hcase : cuth₁ <> cuth₂ ∨
              (cuth₁ = cuth₂ ∧ (hcl <> hcr))).
            {
              case_eq (Fdec cuth₁ cuth₂);
              intros huu hv.
              right.
              refine (conj huu _).
              intro hf. eapply hc.
              subst. rewrite hf.
              reflexivity.
              left. exact huu.
            }

            destruct hcase as [hcase | hcase].
              (* Head sub-challenges differ: extract the witness at branch
                 [F1] by the Chaum–Pedersen extractor. *)
            ++
              specialize (he Fin.F1).
              specialize (hb Fin.F1).
              rewrite dec_true in he, hb.
              cbn in he, hb.
              destruct he as [hel her].
              destruct hb as [hbl hbr].
              rewrite dec_true in her, hbr.
              exists ((ruh₁ - ruh₂) * inv (cuth₁ - cuth₂)).
              split.
              +++
                eapply f_equal with (f := ginv) in hel.
                rewrite connection_between_vopp_and_fopp in hel.
                rewrite group_inv_flip  in hel.
                rewrite commutative in hel.
                pose proof (@rewrite_gop G gop _ _ _ _ hbl hel) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahl (c₁ ^ cuth₁) = gop (c₁ ^ cuth₁) ahl).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
                in Hcom.
                assert (Hwt : (gop ahl (gop (ginv ahl) (ginv (c₁ ^ cuth₂)))) =
                (ginv (c₁ ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) =
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone c₁).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              +++
                exists Fin.F1. cbn.
                remember (gop c₂ (ginv msh)) as ct.
                eapply f_equal with (f := ginv) in her.
                rewrite connection_between_vopp_and_fopp in her.
                rewrite group_inv_flip  in her.
                rewrite commutative in her.
                pose proof (@rewrite_gop G gop _ _ _ _ hbr her) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahr (ct ^ cuth₁) = gop (ct ^ cuth₁) ahr).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
                in Hcom.
                assert (Hwt : (gop ahr (gop (ginv ahr) (ginv (ct ^ cuth₂)))) =
                (ginv (ct ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) =
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
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
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              (* Heads agree, so the tails differ at some index [f]
                 ([vector_not_equal_implies_disjoint_someelem]); extract at
                 [FS f]. *)
            ++
              destruct hcase as (hcasel & hcaser).
              assert (ht : cutl₁ <> cutl₂).
              {
                subst. intro ha. eapply hcaser.
                subst. reflexivity.
              }
              destruct (@vector_not_equal_implies_disjoint_someelem F Fdec _
                cutl₁ cutl₂ ht) as (f & ha).
              destruct (hb (Fin.FS f)) as (hbl & hbr); clear hb.
              destruct (he (Fin.FS f)) as (hel & her); clear he.
              rewrite dec_true in hbl, hbr, hel, her.
              cbn in * |- .
              remember (rutl₁[@f]) as rf₁.
              remember (cutl₁[@f]) as cf₁.
              remember (rult₂[@f]) as rf₂.
              remember (cutl₂[@f]) as cf₂.
              remember (fst alt[@f]) as a.
              exists ((rf₁ - rf₂) * inv (cf₁ - cf₂)).
              split.
              +++
                eapply f_equal with (f := ginv) in hel.
                rewrite connection_between_vopp_and_fopp in hel.
                rewrite group_inv_flip  in hel.
                rewrite commutative in hel.
                pose proof (@rewrite_gop G gop _ _ _ _ hbl hel) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop a (c₁ ^ cf₁) = gop (c₁ ^ cf₁) a).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
                in Hcom.
                assert (Hwt : (gop a (gop (ginv a) (ginv (c₁ ^ cf₂)))) =
                (ginv (c₁ ^ cf₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cf₁ + opp cf₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cf₁ + opp cf₂) * inv (cf₁ + opp cf₂) =
                (inv (cf₁ + opp cf₂) * (cf₁ + opp cf₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone c₁).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cf₁ cf₂ ha as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              +++
                exists (Fin.FS f).
                cbn.
                remember (snd alt[@f]) as sa.
                remember (gop c₂ (ginv mstl[@f])) as ct.
                eapply f_equal with (f := ginv) in her.
                rewrite connection_between_vopp_and_fopp in her.
                rewrite group_inv_flip  in her.
                rewrite commutative in her.
                pose proof (@rewrite_gop G gop _ _ _ _ hbr her) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop sa (ct ^ cf₁) = gop (ct ^ cf₁) sa).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
                in Hcom.
                assert (Hwt : (gop sa (gop (ginv sa) (ginv (ct ^ cf₂)))) =
                (ginv (ct ^ cf₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cf₁ + opp cf₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cf₁ + opp cf₂) * inv (cf₁ + opp cf₂) =
                (inv (cf₁ + opp cf₂) * (cf₁ + opp cf₂))).
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
                pose proof ring_neq_sub_neq_zero cf₁ cf₂ ha as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
          (* Inductive step [m = S m']: the same case split on the head
             sub-challenges. *)
          +
            intros * hc * [ha hb] [hd he].
            destruct (vector_inv_S ms) as (msh & mstl & He).
            destruct (vector_inv_S a) as ((ahl, ahr) & alt & Hf).
            destruct (vector_inv_S ru₁) as (ruh₁ & rutl₁ & Hh).
            destruct (vector_inv_S ru₂) as (ruh₂ & rutl₂ & Hi).
            destruct (vector_inv_S cut₁) as (cuth₁ & cutl₁ & Hj).
            destruct (vector_inv_S cut₂) as (cuth₂ & cutl₂ & Hk).
            cbn in hc.
            remember (fold_right add cutl₁ zero) as hcl.
            remember (fold_right add cutl₂ zero) as hcr.
            assert (hcase : cuth₁ <> cuth₂ ∨
              (cuth₁ = cuth₂ ∧ (hcl <> hcr))).
            {
              case_eq (Fdec cuth₁ cuth₂);
              intros hu hv.
              right.
              refine (conj hu _).
              intro hf. eapply hc.
              subst. cbn. f_equal.
              exact hf.
              left. exact hu.
            }
            destruct hcase as [hcase | hcase].
            ++
              specialize (he Fin.F1).
              specialize (hb Fin.F1).
              rewrite dec_true in he, hb.
              cbn in he, hb.
              destruct he as [hel her].
              destruct hb as [hbl hbr].
              rewrite dec_true in her, hbr.
              exists ((ruh₁ - ruh₂) * inv (cuth₁ - cuth₂)).
              split.
              +++
                subst; cbn in * |-.
                eapply f_equal with (f := ginv) in hel.
                rewrite connection_between_vopp_and_fopp in hel.
                rewrite group_inv_flip  in hel.
                rewrite commutative in hel.
                pose proof (@rewrite_gop G gop _ _ _ _ hbl hel) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahl (c₁ ^ cuth₁) = gop (c₁ ^ cuth₁) ahl).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
                in Hcom.
                assert (Hwt : (gop ahl (gop (ginv ahl) (ginv (c₁ ^ cuth₂)))) =
                (ginv (c₁ ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) =
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone c₁).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              +++
                exists Fin.F1. subst; cbn in *|- *.
                remember (gop c₂ (ginv msh)) as ct.
                eapply f_equal with (f := ginv) in her.
                rewrite connection_between_vopp_and_fopp in her.
                rewrite group_inv_flip  in her.
                rewrite commutative in her.
                pose proof (@rewrite_gop G gop _ _ _ _ hbr her) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahr (ct ^ cuth₁) = gop (ct ^ cuth₁) ahr).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid)
                in Hcom.
                assert (Hwt : (gop ahr (gop (ginv ahr) (ginv (ct ^ cuth₂)))) =
                (ginv (ct ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd
                  F (@eq F) zero one add mul sub div
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) =
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
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
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              (* Heads agree: the tails form two accepting transcripts for
                 the shorter list (with main challenges their sums), so the
                 induction hypothesis gives a witness for some branch
                 [f'], which is branch [FS f'] of the full list. *)
            ++
              specialize (ihm (fold_right add cutl₁ zero) (fold_right add cutl₂ zero)).
              destruct hcase as (hcasel & hcaser).
              rewrite Heqhcl, Heqhcr in hcaser.
              specialize (ihm hcaser n mstl alt cutl₁ rutl₁ cutl₂ rutl₂).
              assert (hua : fold_right add cutl₁ zero = fold_right add cutl₁ zero
                ∧ (∀ f : Fin.t (m + S n),
                (if Gdec (g ^ rutl₁[@f]) (gop (fst alt[@f])
                (c₁ ^ cutl₁[@f]))
                then true
                else false) = true
                ∧ (if
                Gdec (h ^ rutl₁[@f])
                (gop (snd alt[@f]) (gop c₂ (ginv mstl[@f])
                ^ cutl₁[@f]))
                then true
                else false) = true)).
              {
                refine(conj eq_refl _).
                intro f.
                specialize (hb (Fin.FS f)).
                subst; simpl in * |- *.
                exact hb.
              }
            assert (hub : fold_right add cutl₂ zero = fold_right add cutl₂ zero
              ∧ (∀ f : Fin.t (m + S n),
              (if Gdec (g ^ rutl₂[@f])
              (gop (fst alt[@f]) (c₁ ^ cutl₂[@f]))
              then true
              else false) = true
              ∧ (if
              Gdec (h ^ rutl₂[@f])
              (gop (snd alt[@f])
              (gop c₂ (ginv mstl[@f]) ^ cutl₂[@f]))
              then true
              else false) = true)).
              {
                refine(conj eq_refl _).
                intro f.
                specialize (he (Fin.FS f)).
                subst; simpl in * |- *.
                exact he.
              }
            destruct (ihm hua hub) as (y & hg & f' & hff).
            exists y. split. exact hg.
            exists (Fin.FS f'). subst; cbn. exact hff.
        Qed.

        (** Special soundness for [2 + n] candidates: two accepting
            transcripts with the same announcements and distinct main
            challenges yield the encryption randomness [y] and an index
            [f] such that [(c₁, c₂) = (g ^ y, m_f · h ^ y)]. Instance of
            [generalised_accepting_elgamal_soundness] with [2 + n = 1 + (1 + n)]. *)
        Lemma generalised_accepting_elgamal_soundness_main :
          forall {n : nat} (g h : G) (ms : Vector.t G (2 + n)) (c₁ c₂ : G)
          (a : Vector.t (G * G) ((2 + n))) (cu₁ : F) (cut₁ ru₁ : Vector.t F ((2 + n)))
          (cu₂ : F) (cut₂ ru₂ : Vector.t F ((2 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h
            (c₁, c₂) (a; cu₁ :: cut₁; ru₁) = true ->
          generalised_accepting_encryption_proof_elgamal ms g h
            (c₁, c₂) (a; cu₂ :: cut₂; ru₂) = true ->
          cu₁ ≠ cu₂ -> ∃ (y : F), g^y = c₁ ∧
          ∃ (f : Fin.t ((2 + n))), h^y = gop c₂ (ginv (nth ms f)).
        Proof.
          intro n.
          assert (hu : ∃ (m₁ m₂ : nat), (2 + n = m₁ + (1 + m₂))%nat).
          exists 1, n. reflexivity.
          destruct hu as (m₁ & m₂ & hu).
          rewrite !hu.
          intros * ha hb hc.
          eapply generalised_accepting_elgamal_soundness.
          exact ha. exact hb. exact hc.
        Qed.

        (** Sum over a concatenation:
            [Σ (ul ++ ur) = Σ ul + Σ ur]. *)
        Lemma fold_right_app :
          forall (n m : nat) (ul : Vector.t F n)
          (ur : Vector.t F m),
          fold_right add (ul ++ ur) zero =
          (fold_right add ul zero) + (fold_right add ur zero).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 ul);
            cbn. field.
          +
            intros *.
            destruct (vector_inv_S ul) as (ulh & ultl & Ha).
            subst; cbn.
            rewrite IHn; cbn.
            field.
        Qed.

        (** Completeness helper (first equation, false branches to the
            right of the true one): the simulated announcement for branch
            [f] satisfies [g ^ uᶠ = a_f.1 · (g ^ x) ^ cᶠ]. *)
        Lemma construct_encryption_proof_elgamal_real_completeness_generic_first_base :
          forall (n : nat) (f : Fin.t n) (x : F) (g h c₂ : G)
          (msr : Vector.t G n) (usr csr : Vector.t F n),
          g ^ usr[@f] = gop (fst (zip_with (λ (mi : G) '(ui, ci),
          (gop (g ^ ui) ((g ^ x) ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
          (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f]) ((g ^ x) ^ csr[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S csr) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihn.
        Qed.

        (** Completeness helper (second equation, false branches): the
            simulated announcement satisfies
            [h ^ uᶠ = a_f.2 · (c₂ · m_f⁻¹) ^ cᶠ]. *)
        Lemma construct_encryption_proof_elgamal_real_completeness_generic_second_base :
          forall (n : nat) (f : Fin.t n) (g h c₁ c₂ : G)
          (msr : Vector.t G n) (usr csr : Vector.t F n),
          h ^ usr[@f] = gop (snd (zip_with (λ (mi : G) '(ui, ci),
          (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
            (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f])
          (gop c₂ (ginv msr[@f]) ^ csr[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S csr) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihn.
        Qed.

         (** Completeness, first equation, for every branch of the real
             prover’s transcript: assuming [c₁ = g ^ x], branch [f] satisfies
             [g ^ r_f = a_f.1 · c₁ ^ c_f]. False branches hold by
             construction; the true branch holds since
             [g ^ (u + cb · x) = g ^ u · (g ^ x) ^ cb]. By induction on [m]. *)
         Lemma construct_encryption_proof_elgamal_real_completeness_generic_first :
          forall (m n : nat) (f : Fin.t (m + S n)) (x : F) (g h c₁ c₂ : G)
          (msl : Vector.t G m)
          (msr : Vector.t G n) (c : F) (usl csl : Vector.t F m)
          (u : F) (usr csr : Vector.t F n), c₁ = g^x ->
          g ^ (usl ++ u + (c - fold_right add (csl ++ csr) zero) * x :: usr)[@f] =
          gop (fst (zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msl
              (zip_with (λ ui ci : F, (ui, ci)) usl csl) ++ (g ^ u, h ^ u)
              :: zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
                gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
                (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f])
          (c₁ ^ (csl ++ c - fold_right add (csl ++ csr) zero :: csr)[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros * hr.
            rewrite (vector_inv_0 usl), (vector_inv_0 csl),
            (vector_inv_0 msl).
            assert (ha : (zip_with (λ (mi : G) '(ui, ci),
              (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) []
              (zip_with (λ ui ci : F, (ui, ci)) [] [])) = []). reflexivity.
              rewrite ha. clear ha.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              remember ((c - fold_right add csr zero)) as ct.
              assert (Hg : (g ^ x) ^ ct = (g ^ (x * ct))).
              rewrite smul_pow_up.
              reflexivity.
              rewrite Hg; clear Hg.
              assert (Hxc : x * ct = ct * x) by field.
              rewrite Hxc; clear Hxc.
              rewrite <- (@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow);
              subst; [exact eq_refl
              | assumption].
            ++
              subst; cbn.
              eapply construct_encryption_proof_elgamal_real_completeness_generic_first_base.
          +
            intros * hr.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            destruct (vector_inv_S csl) as (cslh & cslt & hb).
            destruct (vector_inv_S msl) as (mslh & mslt & hc).
            rewrite ha, hb, hc.
            destruct (fin_inv_S _ f) as [f' | (f' & hd)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              rewrite hd. cbn.
              specialize (ihm n f' x g h c₁ c₂ mslt msr (c - cslh) uslt cslt u usr csr
                hr).
              remember (fold_right add (cslt ++ csr) zero) as ct.
              assert (he : c - (cslh + ct) = c - cslh - ct). field.
              rewrite he.
              eapply ihm.
        Qed.

        (** Completeness, second equation, for every branch of the real
            prover’s transcript: assuming [h ^ x = c₂ · mc⁻¹] for the true
            candidate [mc], branch [f] satisfies
            [h ^ r_f = a_f.2 · (c₂ · m_f⁻¹) ^ c_f]. By induction on [m]. *)
        Lemma construct_encryption_proof_elgamal_real_completeness_generic_second :
          forall (m n : nat) (f : Fin.t (m + S n)) (x : F) (g h c₁ c₂ : G)
          (msl : Vector.t G m) (mc : G)
          (msr : Vector.t G n) (c : F) (usl csl : Vector.t F m)
          (u : F) (usr csr : Vector.t F n), h ^ x = gop c₂ (ginv mc) ->
          h ^ (usl ++ u + (c - fold_right add (csl ++ csr) zero) * x :: usr)[@f] =
          gop (snd (zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msl
            (zip_with (λ ui ci : F, (ui, ci)) usl csl) ++ (g ^ u, h ^ u):: zip_with
            (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
            (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f])
            (gop c₂ (ginv (msl ++ mc :: msr)[@f])
            ^ (csl ++ c - fold_right add (csl ++ csr) zero :: csr)[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros * hr.
            rewrite (vector_inv_0 usl), (vector_inv_0 csl),
            (vector_inv_0 msl).
            assert (ha : (zip_with (λ (mi : G) '(ui, ci),
              (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) []
              (zip_with (λ ui ci : F, (ui, ci)) [] [])) = []). reflexivity.
              rewrite ha. clear ha.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              remember ((c - fold_right add csr zero)) as ct.
              rewrite <- hr.
              assert (Hg : (h ^ x) ^ ct = (h ^ (x * ct))).
              rewrite smul_pow_up.
              reflexivity.
              rewrite Hg; clear Hg.
              assert (Hxc : x * ct = ct * x) by field.
              rewrite Hxc; clear Hxc.
              rewrite <- (@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow);
              subst; [exact eq_refl
              | assumption].
            ++
              subst; cbn.
              eapply construct_encryption_proof_elgamal_real_completeness_generic_second_base.
          +
            intros * hr.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            destruct (vector_inv_S csl) as (cslh & cslt & hb).
            destruct (vector_inv_S msl) as (mslh & mslt & hc).
            rewrite ha, hb, hc.
            destruct (fin_inv_S _ f) as [f' | (f' & hd)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              rewrite hd. cbn.
              specialize (ihm n f' x g h c₁ c₂ mslt mc msr (c - cslh) uslt cslt u usr csr
                hr).
              remember (fold_right add (cslt ++ csr) zero) as ct.
              assert (he : c - (cslh + ct) = c - cslh - ct). field.
              rewrite he.
              eapply ihm.
        Qed.

        (** Simulator helper (first equation) for the branches of a plain
            simulated list. *)
        Lemma construct_encryption_proof_elgamal_simulator_completeness_generic_first_base :
          forall (n : nat) (f : Fin.t n) (g h c₁ c₂ : G)
          (msr : Vector.t G n) (usr cstt : Vector.t F n),
          g ^ usr[@f] = gop (fst (zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
            (zip_with (λ ui ci : F, (ui, ci)) usr cstt))[@f]) (c₁ ^ cstt[@f]).
        Proof.
           induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S cstt) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihn.
        Qed.

        (** Simulator completeness, first equation, for every branch:
            [g ^ u_f = a_f.1 · c₁ ^ c_f] holds for any statement. By
            induction on [m]. *)
        Lemma construct_encryption_proof_elgamal_simulator_completeness_generic_first :
          forall (m n : nat) (f : Fin.t (m + S n)) (msl : Vector.t G m)
            (mc g h c₁ c₂ : G) (msr : Vector.t G n) (usl : Vector.t F m) cst
            (usr : Vector.t F n) (u : F),
            g ^ (usl ++ u :: usr)[@f] = gop (fst (zip_with (λ (mi : G) '(ui, ci),
            (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci)))
            (msl ++ mc :: msr) (zip_with (λ ui ci : F, (ui, ci)) (usl ++ u :: usr) cst))[@f])
            (c₁ ^ cst[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros *.
            rewrite (vector_inv_0 usl), (vector_inv_0 msl).
            destruct (vector_inv_S cst) as (csth & cstt & ha).
            destruct (fin_inv_S _ f) as [f' | (f' & hb)].
            ++
              subst. cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_first_base.
        +
          intros *.
          destruct (vector_inv_S usl) as (uslh & uslt & ha).
          cbn in cst.
          destruct (vector_inv_S cst) as (csth & cstt & hb).
          destruct (vector_inv_S msl) as (mslh & mslt & hc).
          subst.
          destruct (fin_inv_S _ f) as [f' | (f' & hf)].
          ++
            subst; cbn.
            rewrite <-associative.
            rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
              zero one add mul sub div
              opp inv G (@eq G) gid ginv gop gpow).
            rewrite field_zero_iff_left,
            vector_space_field_zero,
            monoid_is_right_identity.
            reflexivity.
            typeclasses eauto.
          ++
            subst; cbn.
            eapply ihm.
        Qed.

        (** Summing a vector is invariant under transport along an equality
            of lengths. *)
        Theorem fold_right_rew_gen :
          forall (m n : nat) (cs : Vector.t F m) (pf : m = n),
          fold_right add (rew [t F] pf in cs) zero =
          fold_right add cs zero.
        Proof.
          intros m n cs.
          refine(match cs as cs' in Vector.t _ m'
            return ∀ (pf : m' = n), fold_right add (rew [t F] pf in cs') zero =
              fold_right add cs' zero
            with
            | [] => _
            | csh :: cst => _
            end); intro pf; subst; reflexivity.
        Qed.

        (** Simulator helper (second equation) for the branches of a plain
            simulated list. *)
        Theorem construct_encryption_proof_elgamal_simulator_completeness_generic_second_base :
          forall (n : nat) (f : Fin.t n) (g h c₁ c₂ : G)
          (msr : Vector.t G n) (usr cstt : Vector.t F n),
          h ^ usr[@f] = gop (snd (zip_with (λ (mi : G) '(ui, ci),
          (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
          (zip_with (λ ui ci : F, (ui, ci)) usr cstt))[@f])
          (gop c₂ (ginv msr[@f]) ^ cstt[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S cstt) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihn.
        Qed.

        (** Simulator completeness, second equation, for every branch:
            [h ^ u_f = a_f.2 · (c₂ · m_f⁻¹) ^ c_f] holds for any statement. *)
        Theorem construct_encryption_proof_elgamal_simulator_completeness_generic_second :
          forall (m n : nat) (f : Fin.t (m + S n)) (g h c₁ c₂ : G)
          (msl : Vector.t G m) (mc : G)
          (msr : Vector.t G n)  (usl : Vector.t F m) cst
          (u : F) (usr : Vector.t F n),
          h ^ (usl ++ u :: usr)[@f] = gop (snd (zip_with (λ (mi : G) '(ui, ci),
            (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci)))
            (msl ++ mc :: msr) (zip_with (λ ui ci : F, (ui, ci)) (usl ++ u :: usr) cst))[@f])
          (gop c₂ (ginv (msl ++ mc :: msr)[@f]) ^ cst[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros *.
            rewrite (vector_inv_0 usl), (vector_inv_0 msl).
            destruct (vector_inv_S cst) as (csth & cstt & ha).
            destruct (fin_inv_S _ f) as [f' | (f' & hb)].
            ++
              subst. cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_second_base.
        +
          intros *.
          destruct (vector_inv_S usl) as (uslh & uslt & ha).
          cbn in cst.
          destruct (vector_inv_S cst) as (csth & cstt & hb).
          destruct (vector_inv_S msl) as (mslh & mslt & hc).
          subst.
          destruct (fin_inv_S _ f) as [f' | (f' & hf)].
          ++
            subst; cbn.
            rewrite <-associative.
            rewrite <-(@vector_space_smul_distributive_fadd F (@eq F)
              zero one add mul sub div
              opp inv G (@eq G) gid ginv gop gpow).
            rewrite field_zero_iff_left,
            vector_space_field_zero,
            monoid_is_right_identity.
            reflexivity.
            typeclasses eauto.
          ++
            subst; cbn.
            eapply ihm.
        Qed.

        (** Completeness with the true branch at position [m]: if
            [g ^ x = c₁] and [h ^ x = c₂ · mc⁻¹], the real transcript for
            candidates [msl ++ [mc] ++ msr] is accepted for every challenge
            [c] and every randomness vector [uscs]. The sum check holds
            because [cb = c - Σ (csl ++ csr)]; the branch checks are the
            two [_generic] lemmas above. *)
        Lemma construct_encryption_proof_elgamal_real_completeness
          {m n : nat}
          (x : F)
          (g h c₁ c₂ : G)
          (msl : Vector.t G m)
          (mc : G)
          (msr : Vector.t G n)
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv mc)) :
          forall (c : F) (uscs : Vector.t F ((m + (1 + n)) + (m + n))),
          generalised_accepting_encryption_proof_elgamal
          (msl ++ [mc] ++ msr)  g h (c₁, c₂)
            (construct_encryption_proof_elgamal_real (x : F)
            uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c) = true.
        Proof.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness.
          unfold construct_encryption_proof_elgamal_real,
          construct_encryption_proof_elgamal_commitment.
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usl & usrh).
          destruct (vector_inv_S usrh) as (u & usr & _).
          destruct (splitat m cs) as (csl & csr).
          rewrite VectorSpec.splitat_append.
          cbn; split.
          +
            rewrite !fold_right_app. cbn.
            field.
          +
            intro f.
            rewrite !dec_true.
            split.
            ++
              eapply construct_encryption_proof_elgamal_real_completeness_generic_first.
              destruct R as [Ra Rb].
              rewrite Ra; reflexivity.
            ++
              eapply construct_encryption_proof_elgamal_real_completeness_generic_second.
              destruct R as [Ra Rb].
              rewrite Rb; reflexivity.
        Qed.

        (** Index bookkeeping: if [rindex] points at position [m] of
            [msl ++ ms :: msr], then the relation stated at [rindex] is the
            relation for [ms]. *)
        Theorem generalised_construct_encryption_proof_elgamal_real_completeness_fin :
          forall (m n : nat) (rindex : Fin.t (m + S n))
          (msl : Vector.t G m) (h ms : G) (msr : Vector.t G n) (x : F)
          (c₂ : G),
          m = proj1_sig (Fin.to_nat rindex) ->
          h ^ x = gop c₂ (ginv (msl ++ ms :: msr)[@rindex]) ->
          h ^ x = gop c₂ (ginv ms).
        Proof.
          intros * ha hb.
          assert (hc : rindex = Fin.R m (Fin.F1 : Fin.t (1 + n))).
          eapply fin_to_nat. exact ha.
          subst. rewrite VectorSpec.nth_append_R in hb.
          cbn in hb.
          exact hb.
        Qed.

        (** Completeness of the disjunctive proof: if [g ^ x = c₁] and
            [h ^ x = c₂ · ms_rindex⁻¹] (the ciphertext encrypts the
            [rindex]-th candidate with randomness [x]), the real prover’s
            transcript is accepted for every challenge [c] and every
            randomness vector [uscs]. *)
        Lemma generalised_construct_encryption_proof_elgamal_real_completeness
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F)
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) :
          forall (c : F) (uscs : Vector.t F (((2 + n)) + (1 + n))),
          generalised_accepting_encryption_proof_elgamal
          ms g h (c₁, c₂)
            (generalised_construct_encryption_proof_elgamal_real rindex (x : F)
            uscs ms g h (c₁, c₂) c) = true.
        Proof.
          intros *.
          unfold generalised_construct_encryption_proof_elgamal_real.
          destruct (splitat (2 + n) uscs) as (us & cs).
          destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa].
          destruct pfbb as [pfb].
          destruct haa as [ha].
          destruct ha as (ha & hb & hc & hd).
          generalize dependent ms. generalize dependent us.
          generalize dependent cs. generalize dependent rindex.
          cbn in * |- *. rewrite !pfa, !pfb. cbn.
          intros rindex ha cs hb us hc hd ms he.
          destruct (splitat m₁ ms) as (msl & msrr) eqn:hm.
          eapply append_splitat in hm.
          destruct (vector_inv_S msrr) as (m & msr & hmm).
          subst.
          eapply construct_encryption_proof_elgamal_real_completeness.
          destruct he as (hel & her).
          split. exact hel.
          eapply generalised_construct_encryption_proof_elgamal_real_completeness_fin.
          exact ha. exact her.
        Qed.

        (** Simulator completeness: for every statement (including
            ciphertexts that encrypt none of the candidates), every
            challenge and every randomness vector, the simulated transcript
            is accepted. *)
        Lemma generalised_construct_encryption_proof_elgamal_simulator_completeness
          {n : nat}
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n)) :
          forall (c : F) (uscs : Vector.t F (((2 + n)) + (1 + n))),
          generalised_accepting_encryption_proof_elgamal
          ms g h (c₁, c₂)
            (generalised_construct_encryption_proof_elgamal_simulator uscs
             ms g h (c₁, c₂) c) = true.
        Proof.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness_gen.
          unfold generalised_construct_encryption_proof_elgamal_simulator.
          destruct (splitat ((2 + n)) uscs) as (us & cs).
          (* The sum check holds by construction of [cm]; for the branch
             checks, split [2 + n] as [1 + (1 + n)] and use the two
             simulator [_generic] lemmas. *)
          split.
          + cbn; field.
          +
            intros *.
            remember (c - fold_right add cs zero :: cs) as cst. cbn.
            rewrite !dec_true.
            split.
            ++
              clear uscs Heqcst.
              assert (ha : (∃ (m₁ m₂ : nat), 2 + n = m₁ + (1 + m₂))%nat).
              exists 1, n. reflexivity.
              destruct ha as (m₁ & m₂ & ha).
              revert us cst f ms. cbn in * |- *.
              rewrite !ha. intros *.
              destruct (splitat m₁ us) as (usl & usrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S usrr) as (u & usr & hc).
              subst.
              destruct (splitat m₁ ms) as (msl & msrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S msrr) as (mc & msr & hc).
              subst.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_first.
            ++
              clear uscs Heqcst.
              assert (ha : (∃ (m₁ m₂ : nat), 2 + n = m₁ + (1 + m₂))%nat).
              exists 1, n. reflexivity.
              destruct ha as (m₁ & m₂ & ha).
              revert us cst f ms. cbn in * |- *.
              rewrite !ha. intros *.
              destruct (splitat m₁ us) as (usl & usrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S usrr) as (u & usr & hc).
              subst.
              destruct (splitat m₁ ms) as (msl & msrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S msrr) as (mc & msr & hc).
              subst.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_second.
        Qed.

        (** [p / q] denotes the rational probability [p / q] with a natural
            denominator (local notation). *)
        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (** If every coin vector in [l] has probability [1 / q], so does every
            transcript in the image of [l] under the real prover with the
            true branch at position [m]. *)
        Lemma construct_encryption_proof_elgamal_distribution_probability_generic
          {m n : nat}
          (x : F)
          (g h c₁ c₂ : G)
          (msl : Vector.t G m)
          (mc : G)
          (msr : Vector.t G n) :
          forall (l : dist (t F (m + (1 + n) + (m + n))))
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob),
            List.In (trx, prx) l → prx = 1 / q) ->
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_encryption_proof_elgamal_real x
              uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c))) → pr = 1 / q.
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

        (** The same probability transfer for the real prover indexed by
            [rindex]. *)
        Lemma generalised_construct_encryption_proof_elgamal_distribution_probability_generic
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F)
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n)) :
          forall (l : dist (t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob),
            List.In (trx, prx) l → prx = 1 / q) ->
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_real rindex x
              uscs ms g h (c₁, c₂) c))) → pr = 1 / q.
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

        (** Under the relation, every transcript in the support of
            [Bind l (real prover at position m)] is accepting. *)
        Lemma construct_encryption_proof_elgamal_distribution_transcript_generic
          {m n : nat}
          (x : F)
          (g h c₁ c₂ : G)
          (msl : Vector.t G m)
          (mc : G)
          (msr : Vector.t G n)
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv mc)) :
          forall (l : dist (t F (m + (1 + n) + (m + n))))
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_encryption_proof_elgamal_real x
              uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c))) →
          generalised_accepting_encryption_proof_elgamal (msl ++ [mc] ++ msr)
            g h (c₁, c₂) trans = true.
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
              now eapply construct_encryption_proof_elgamal_real_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply construct_encryption_proof_elgamal_real_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (** Under the relation, every transcript in the support of
            [Bind l (real prover at rindex)] is accepting. *)
        Lemma generalised_construct_encryption_proof_elgamal_distribution_transcript_generic
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F)
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n) )
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) :
          forall (l : dist (t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_real rindex x
              uscs ms g h (c₁, c₂) c))) →
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) trans = true.
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
              now eapply generalised_construct_encryption_proof_elgamal_real_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply generalised_construct_encryption_proof_elgamal_real_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (** Every entry [(a, b)] of the real transcript distribution is
            accepting and has probability [1 / |lf| ^ ((2 + n) + (1 + n))]. *)
        Lemma generalised_encryption_proof_elgamal_special_honest_verifier_dist
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F)
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) :
          forall (lf : list F) (Hlfn : lf <> List.nil)
          (c : F) a b,
          List.In (a, b)
            (generalised_encryption_proof_elgamal_real_distribution lf Hlfn
            rindex x (c₁, c₂) g h ms c) ->
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) a = true ∧
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          +
            eapply generalised_construct_encryption_proof_elgamal_distribution_transcript_generic.
            exact R.
            exact Ha.
          +
            eapply generalised_construct_encryption_proof_elgamal_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.

         (** Probability transfer for the simulator: every transcript in the
             image of a uniform distribution of weight [1 / q] has weight
             [1 / q]. *)
         Lemma generalised_construct_encryption_proof_elgamal_simulator_distribution_probability_generic
          {n : nat}
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n)) :
          forall (l : dist (t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob),
            List.In (trx, prx) l → prx = 1 / q) ->
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_simulator uscs
             ms g h (c₁, c₂) c))) → pr = 1 / q.
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

        (** Every transcript in the support of the simulated distribution is
            accepting (no relation needed). *)
        Lemma generalised_construct_encryption_proof_elgamal_simulator_distribution_transcript_generic
          {n : nat}
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n)) :
          forall (l : dist (t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_simulator uscs
              ms g h (c₁, c₂) c))) →
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) trans = true.
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
              eapply generalised_construct_encryption_proof_elgamal_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply generalised_construct_encryption_proof_elgamal_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

         (** Every entry [(a, b)] of the simulated distribution is accepting
             and has probability [1 / |lf| ^ ((2 + n) + (1 + n))]. *)
         Lemma generalised_construct_encryption_proof_elgamal_simulator_special_honest_verifier_dist
          {n : nat}
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n)) :
          forall (lf : list F) (Hlfn : lf <> List.nil)
          (c : F) a b,
          List.In (a, b)
            (generalised_encryption_proof_elgamal_simulator_distribution lf Hlfn
              g h (c₁, c₂) ms c) ->
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) a = true ∧
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          +
            eapply generalised_construct_encryption_proof_elgamal_simulator_distribution_transcript_generic.
            exact Ha.
          +
            eapply generalised_construct_encryption_proof_elgamal_simulator_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.

         (** Special honest-verifier zero-knowledge, weak form: under the
             relation, the real and simulated distributions coincide after
             mapping each transcript to the verifier’s verdict (all entries
             are [(true, 1 / |lf| ^ ((2 + n) + (1 + n)))]). This compares only
             verdicts and probabilities; the strong form is
             [generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm]. *)
         Lemma generalised_encryption_proof_elgamal_special_honest_verifier_zkp
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F)
          (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) =>
            (generalised_accepting_encryption_proof_elgamal ms
              g h (c₁, c₂) a, p))
            (generalised_encryption_proof_elgamal_real_distribution lf Hlfn
              rindex x (c₁, c₂) g h ms c) =
          List.map (fun '(a, p) =>
            (generalised_accepting_encryption_proof_elgamal ms
              g h (c₁, c₂) a, p))
            (generalised_encryption_proof_elgamal_simulator_distribution lf Hlfn
              g h (c₁, c₂) ms c).
        Proof.
          intros ? ? ?.
          eapply map_ext_eq.
          +
            unfold generalised_encryption_proof_elgamal_real_distribution,
            generalised_encryption_proof_elgamal_simulator_distribution; cbn.
            repeat rewrite distribution_length.
            reflexivity.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_encryption_proof_elgamal_special_honest_verifier_dist.
            exact R.
            exact Ha.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_construct_encryption_proof_elgamal_simulator_special_honest_verifier_dist.
            exact Ha.
        Qed.

        (** *** Strong zero-knowledge: equality of transcript distributions

            The real prover and the simulator consume coin vectors of the
            same shape. The map [or_shift] turns the real prover’s coins
            into simulator coins that produce exactly the same transcript
            ([construct_enc_shift]); since [or_shift] is a bijection (with
            inverse [or_unshift]), the two transcript distributions are
            permutations of each other. *)

        (** Rewriting along [eq_refl] with [eq_rew_r_dep] is the identity
            (uses uniqueness of identity proofs on [nat]). *)
        Lemma eq_rew_r_dep_refl_nat : forall (x : nat) (P : forall y, y = x -> Type)
          (HC : P x eq_refl), eq_rew_r_dep P HC eq_refl = HC.
        Proof.
          intros x P HC.
          unfold eq_rew_r_dep.
          generalize (eq_sym_involutive (@eq_refl nat x)) as q; intros q.
          assert (hq : q = eq_refl).
          { apply Eqdep_dec.UIP_dec; intros a b; left; apply UIP_nat. }
          rewrite hq; reflexivity.
        Qed.

        (** A presentation of
            [generalised_construct_encryption_proof_elgamal_real] by explicit
            transport ([rew]) along the length equalities produced by
            [vector_fin_app_pred], instead of the tactic-built term; easier
            to reason about. *)
        Definition enc_prover_alt {n : nat} (rindex : Fin.t (2 + n)) (x : F)
          (uscs : Vector.t F ((2 + n) + (1 + n))) (ms : Vector.t G (2 + n))
          (g h : G) (cp : G * G) (c : F) :
          @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n).
        Proof.
          destruct (splitat (2 + n) uscs) as (us & cs).
          destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & _).
          destruct pfaa as [pfa]; destruct pfbb as [pfb].
          exact (rew <- [fun k => @sigma_proto F (G * G) k (S k) k] pfa in
            construct_encryption_proof_elgamal_real x
              ((rew [Vector.t F] pfa in us) ++ (rew [Vector.t F] pfb in cs))
              (rew [Vector.t G] pfa in ms) g h cp c).
        Defined.

        (** [enc_prover_alt] agrees with
            [generalised_construct_encryption_proof_elgamal_real]. *)
        Lemma enc_prover_alt_eq {n : nat} (rindex : Fin.t (2 + n)) (x : F)
          (uscs : Vector.t F ((2 + n) + (1 + n))) (ms : Vector.t G (2 + n))
          (g h : G) (cp : G * G) (c : F) :
          generalised_construct_encryption_proof_elgamal_real rindex x uscs ms g h cp c =
          enc_prover_alt rindex x uscs ms g h cp c.
        Proof.
          unfold generalised_construct_encryption_proof_elgamal_real, enc_prover_alt.
          destruct (splitat (2 + n) uscs) as (us & cs).
          destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa]; destruct pfbb as [pfb]; destruct haa as [ha].
          destruct ha as (ha & hb & hc & hd).
          (* Eliminate the length equalities with UIP on [nat] so that both
             sides reduce to the same term. *)
          subst us cs.
          cbn [p] in *.
          change ((2 + n)%nat) with ((1 + (1 + n))%nat) in *.
          generalize dependent pfa; generalize dependent ms; generalize dependent rindex.
          set (N := (1 + n)%nat) in *.
          change (S n) with N.
          clearbody N.
          assert (pfb' : (m₁ + m₂)%nat = N) by (symmetry; exact pfb).
          destruct pfb'.
          rewrite (UIP_nat _ _ pfb eq_refl).
          intros rindex hd ms pfa hb.
          cbn [eq_rect_r eq_rect eq_sym].
          rewrite eq_rew_r_dep_refl_nat.
          set (Y := (1 + (m₁ + m₂))%nat) in *.
          change (S (m₁ + m₂)) with Y.
          clearbody Y.
          assert (pfa' : (m₁ + (1 + m₂))%nat = Y) by (symmetry; exact pfa).
          generalize dependent pfa; generalize dependent ms; generalize dependent rindex.
          destruct pfa'.
          intros rindex hd ms pfa hb.
          assert (hpfa : pfa = eq_refl) by apply UIP_nat.
          subst pfa.
          rewrite eq_rew_r_dep_refl_nat.
          cbn.
          reflexivity.
        Qed.

        (** The simulator written as a plain [let] term for a list of
            length [S N]. *)
        Definition enc_simulator_base {N : nat} (uscs : Vector.t F (S N + N))
          (ms : Vector.t G (S N)) (g h : G) (cp : G * G) (c : F) :
          @sigma_proto F (G * G) (S N) (S (S N)) (S N) :=
          let (us, cs) := splitat (S N) uscs in
          let (c₁, c₂) := cp in
          let cm := (c - Vector.fold_right add cs zero) :: cs in
          let comm := zip_with (fun ui ci => (ui, ci)) us cm in
          let commit := zip_with (fun mi '(ui, ci) =>
            (gop (g^ui) (c₁^(opp ci)), gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) ms comm in
          (commit; c :: cm; us).

        (** [enc_simulator_base] agrees definitionally with
            [generalised_construct_encryption_proof_elgamal_simulator]. *)
        Lemma enc_simulator_base_eq {n : nat} (uscs : Vector.t F ((2 + n) + (1 + n)))
          (ms : Vector.t G (2 + n)) (g h : G) (cp : G * G) (c : F) :
          generalised_construct_encryption_proof_elgamal_simulator uscs ms g h cp c =
          @enc_simulator_base (1 + n) uscs ms g h cp c.
        Proof. reflexivity. Qed.

        (** The coin shift from real to simulator coins: replace the
            [rindex]-th randomness [u] by the response [u + cb · x], where
            [cb = c - Σ cs], and replace the free sub-challenges [cs] by the
            tail of the full sub-challenge vector obtained by inserting [cb]
            at position [rindex]. *)
        Definition or_shift {n : nat} (rindex : Fin.t (2 + n)) (x c : F)
          (uscs : Vector.t F ((2 + n) + (1 + n))) : Vector.t F ((2 + n) + (1 + n)) :=
          let (us, cs) := splitat (2 + n) uscs in
          let cb := c - Vector.fold_right add cs zero in
          Vector.append (replace us rindex (us[@rindex] + cb * x))
            (tl (insert_at (1 + n) cs rindex cb)).

        (** Inverse of [or_shift]: recompute the full sub-challenge vector
            [cm = (c - Σ cs) :: cs], read [cb] at [rindex], subtract
            [cb · x] from the [rindex]-th response and remove [cb] from
            [cm]. *)
        Definition or_unshift {n : nat} (rindex : Fin.t (2 + n)) (x c : F)
          (uscs : Vector.t F ((2 + n) + (1 + n))) : Vector.t F ((2 + n) + (1 + n)) :=
          let (us, cs) := splitat (2 + n) uscs in
          let cm := (c - Vector.fold_right add cs zero) :: cs in
          let cb := cm[@rindex] in
          Vector.append (replace us rindex (us[@rindex] - cb * x))
            (remove_at (1 + n) cm rindex).

        (** Summing after inserting [a]: [Σ (insert_at v i a) = a + Σ v]. *)
        Lemma fold_insert_at : forall k (v : Vector.t F k) (i : Fin.t (S k)) (a : F),
          Vector.fold_right add (insert_at k v i a) zero =
          a + Vector.fold_right add v zero.
        Proof.
          induction k as [| k ih]; intros v i a.
          + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst;
            [rewrite (vector_inv_0 v); reflexivity | inversion j].
          + destruct (fin_inv_S _ i) as [hi | (j & hi)]; subst; cbn; [reflexivity |].
            destruct (vector_inv_S v) as (b & v' & hv); subst; cbn.
            rewrite ih; field.
        Qed.

        (** Summing a vector by removing one entry:
            [Σ v = v_i + Σ (remove_at v i)]. *)
        Lemma fold_remove_at : forall k (v : Vector.t F (S k)) (i : Fin.t (S k)),
          Vector.fold_right add v zero =
          v[@i] + Vector.fold_right add (remove_at k v i) zero.
        Proof.
          intros k v i.
          set (w := remove_at k v i); set (a := v[@i]).
          assert (hv : v = insert_at k w i a) by
            (unfold w, a; symmetry; apply insert_remove).
          clearbody w a.
          rewrite hv, fold_insert_at; reflexivity.
        Qed.

        (** If [cm] is [cs] with [c - Σ cs] inserted somewhere, then [cm]
            equals [(c - Σ (tl cm)) :: tl cm], i.e. its head is determined by
            the rest and the total [c]. *)
        Lemma insert_at_eta : forall k (cs : Vector.t F k) (i : Fin.t (S k)) (c : F),
          (c - Vector.fold_right add
            (tl (insert_at k cs i (c - Vector.fold_right add cs zero))) zero) ::
          tl (insert_at k cs i (c - Vector.fold_right add cs zero)) =
          insert_at k cs i (c - Vector.fold_right add cs zero).
        Proof.
          intros k cs i c.
          set (cb := c - Vector.fold_right add cs zero).
          set (cm := insert_at k cs i cb).
          assert (hsum : Vector.fold_right add cm zero = c).
          { unfold cm; rewrite fold_insert_at; unfold cb; field. }
          rewrite (VectorSpec.eta cm) at 3.
          f_equal.
          rewrite (VectorSpec.eta cm) in hsum at 1.
          cbn [fold_right] in hsum.
          rewrite <- hsum; field.
        Qed.

        (** [or_unshift] is a left inverse of [or_shift]. *)
        Lemma or_unshift_shift {n : nat} (rindex : Fin.t (2 + n)) (x c : F) :
          forall (uscs : Vector.t F ((2 + n) + (1 + n))),
          or_unshift rindex x c (or_shift rindex x c uscs) = uscs.
        Proof.
          intros uscs.
          destruct (splitat (2 + n) uscs) as (us & cs) eqn:he.
          apply append_splitat in he; subst uscs.
          unfold or_shift, or_unshift.
          rewrite !VectorSpec.splitat_append.
          rewrite insert_at_eta.
          rewrite VectorSpec.nth_replace_eq, VectorSpec.replace_replace_eq.
          rewrite nth_insert_at, remove_insert.
          f_equal.
          assert (hu : us[@rindex] + (c - Vector.fold_right add cs zero) * x -
            (c - Vector.fold_right add cs zero) * x = us[@rindex]) by field.
          rewrite hu; apply VectorSpec.replace_id.
        Qed.

        (** [or_unshift] is a right inverse of [or_shift]. *)
        Lemma or_shift_unshift {n : nat} (rindex : Fin.t (2 + n)) (x c : F) :
          forall (uscs : Vector.t F ((2 + n) + (1 + n))),
          or_shift rindex x c (or_unshift rindex x c uscs) = uscs.
        Proof.
          intros uscs.
          destruct (splitat (2 + n) uscs) as (us & cs) eqn:he.
          apply append_splitat in he; subst uscs.
          unfold or_shift, or_unshift.
          rewrite !VectorSpec.splitat_append.
          set (cm := (c - Vector.fold_right add cs zero) :: cs).
          set (cb := cm[@rindex]).
          assert (hsum : Vector.fold_right add cm zero = c) by (unfold cm; cbn; field).
          assert (hcb : c - Vector.fold_right add (remove_at (1 + n) cm rindex) zero = cb).
          {
            rewrite (fold_remove_at (1 + n) cm rindex) in hsum.
            unfold cb; rewrite <- hsum; field.
          }
          rewrite hcb, VectorSpec.nth_replace_eq, VectorSpec.replace_replace_eq.
          unfold cb; rewrite insert_remove.
          unfold cm; cbn [tl].
          f_equal.
          assert (hu : us[@rindex] - ((c - Vector.fold_right add cs zero) :: cs)[@rindex] * x
            + ((c - Vector.fold_right add cs zero) :: cs)[@rindex] * x = us[@rindex]) by field.
          rewrite hu; apply VectorSpec.replace_id.
        Qed.

        (** Transport of a transcript triple along a length equality is
            component-wise transport. *)
        Lemma rew_sigma_proto_pair : forall (N M : nat) (e : N = M)
          (a : Vector.t (G * G) N) (cm : Vector.t F (S N)) (r : Vector.t F N),
          rew [fun k => @sigma_proto F (G * G) k (S k) k] e in (a; cm; r) =
          (rew [Vector.t (G * G)] e in a; rew [fun k => Vector.t F (S k)] e in cm;
           rew [Vector.t F] e in r).
        Proof. intros N M e a cm r; destruct e; reflexivity. Qed.

        (** Transport commutes with [cons]. *)
        Lemma rew_cons_S {A : Type} :
          forall (N M : nat) (e : N = M) (a : A) (v : Vector.t A N),
          rew [fun k => Vector.t A (S k)] e in (a :: v) = a :: rew [Vector.t A] e in v.
        Proof. intros N M e a v; destruct e; reflexivity. Qed.

        (** Transcript shift: under the relation, the real prover with coins
            [uscs] produces exactly the simulator’s transcript with coins
            [or_shift rindex x c uscs]. False branches coincide literally;
            for the true branch, the honest announcement [(g ^ u, h ^ u)]
            equals the simulated one with response [u + cb · x] by
            [schnorr_commitment_shift]. *)
        Lemma construct_enc_shift {n : nat} (rindex : Fin.t (2 + n)) (x : F)
          (g h c₁ c₂ : G) (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) :
          forall (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F),
          generalised_construct_encryption_proof_elgamal_real rindex x uscs ms g h (c₁, c₂) c =
          generalised_construct_encryption_proof_elgamal_simulator
            (or_shift rindex x c uscs) ms g h (c₁, c₂) c.
        Proof.
          intros uscs c.
          (* Replace both sides by their explicit forms and split [uscs]. *)
          rewrite enc_prover_alt_eq, enc_simulator_base_eq.
          destruct (splitat (2 + n) uscs) as (us & cs) eqn:hv.
          apply append_splitat in hv; subst uscs.
          unfold enc_prover_alt, or_shift.
          rewrite !VectorSpec.splitat_append.
          destruct (vector_fin_app_pred (1 + n) rindex us cs) as
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa]; destruct pfbb as [pfb]; destruct haa as [ha].
          destruct ha as (ha & hb & hc & hd).
          subst us cs.
          cbn [p] in hb |- *.
          change ((2 + n)%nat) with ((1 + (1 + n))%nat) in *.
          generalize dependent pfa; generalize dependent ms; generalize dependent rindex.
          set (N := (1 + n)%nat) in *.
          clearbody N.
          assert (pfb' : (m₁ + m₂)%nat = N) by (symmetry; exact pfb).
          destruct pfb'.
          rewrite (UIP_nat _ _ pfb eq_refl); cbn [eq_rect_r eq_rect eq_sym].
          intros rindex hd ms R pfa hb.
          rewrite !rew_opp_r.
          (* Split the candidate list at the true branch and identify
             [rindex] with position [m₁]. *)
          destruct (splitat m₁ (rew [t G] pfa in ms)) as (msl & msrr) eqn:hma.
          apply append_splitat in hma.
          destruct (vector_inv_S msrr) as (m & msr & hm); subst msrr.
          pose proof (f_equal (fun v => rew <- [t G] pfa in v) hma) as hms.
          cbn beta in hms.
          rewrite rew_opp_l in hms.
          rewrite hma.
          subst ms.
          assert (hri : rindex = rew <- [Fin.t] pfa in Fin.R m₁ (Fin.F1 : Fin.t (S m₂))).
          {
            apply fin_eq_of_to_nat; rewrite <- hd.
            unfold eq_rect_r; rewrite rew_to_nat, Fin.R_sanity; cbn; lia.
          }
          subst rindex.
          cbn [append] in *.
          unfold eq_rect_r in *.
          set (i := rew [Fin.t] eq_sym pfa in Fin.R m₁ Fin.F1) in *.
          rewrite !rew_app_cons in R.
          rewrite !rew_app_cons.
          rewrite nth_insert_at in R.
          rewrite nth_insert_at.
          (* Unfold the simulator; the inserted sub-challenge is exactly
             [cb], and the vectors line up with the prover’s split. *)
          unfold enc_simulator_base; rewrite VectorSpec.splitat_append; cbv beta iota zeta.
          rewrite replace_insert_at, insert_at_eta, !zip_with_insert_at.
          unfold construct_encryption_proof_elgamal_real,
            construct_encryption_proof_elgamal_commitment.
          rewrite !VectorSpec.splitat_append; cbn.
          change (rew [λ y : nat, Fin.t y] eq_sym pfa in Fin.R m₁ Fin.F1) with i in *.
          rewrite rew_sigma_proto_pair, rew_cons_S, !rew_app_cons.
          change (rew [Fin.t] eq_sym pfa in Fin.R m₁ Fin.F1) with i.
          rewrite !zip_with_app.
          f_equal; f_equal.
          (* Only the true branch remains: Schnorr commitment shift for
             [g] and for [h]. *)
          destruct R as (R1 & R2).
          f_equal; apply schnorr_commitment_shift; symmetry; assumption.
        Qed.

        (** Special honest-verifier zero-knowledge, strong form: under the
            relation, if [lf] lists every field element exactly once, the real
            and simulated transcript distributions are permutations of each
            other (identical as distributions). Proof: [bind_ret_perm] with the
            bijection [or_shift] (inverse [or_unshift]) on uniformly drawn coin
            vectors ([repeat_uniform_bijection_perm]), together with
            [construct_enc_shift]. *)
        Theorem generalised_encryption_proof_elgamal_special_honest_verifier_zkp_perm
          {n : nat} (rindex : Fin.t (2 + n)) (x : F) (g h c₁ c₂ : G)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.NoDup lf -> (forall y : F, List.In y lf) ->
          Permutation
            (generalised_encryption_proof_elgamal_real_distribution
              lf Hlfn rindex x (c₁, c₂) g h ms c)
            (generalised_encryption_proof_elgamal_simulator_distribution
              lf Hlfn g h (c₁, c₂) ms c).
        Proof.
          intros * hnd hall.
          change (Permutation
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
                ((2 + n) + (1 + n)))
              (fun uscs => Ret (generalised_construct_encryption_proof_elgamal_real
                rindex x uscs ms g h (c₁, c₂) c)))
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
                ((2 + n) + (1 + n)))
              (fun uscs => Ret (generalised_construct_encryption_proof_elgamal_simulator
                uscs ms g h (c₁, c₂) c)))).
          eapply bind_ret_perm with (phi := or_shift rindex x c).
          + apply (repeat_uniform_bijection_perm lf Hlfn _ _
              (or_unshift rindex x c) hnd hall);
            [apply or_unshift_shift | apply or_shift_unshift].
          + intros uscs p _. apply construct_enc_shift; exact R.
        Qed.

    End Proofs.
  End EncProof.
End DL.
