(** * OR-composition of Schnorr protocols over a common generator

    This file formalises the Cramer–Damgård–Schoenmakers (CDS) disjunctive
    composition of Schnorr's Σ-protocol for [k = 2 + n] discrete-logarithm
    statements that share one generator [g]. The public statement is a vector [hs]
    of group elements [h₀, …, h₍ₖ₋₁₎] and the prover shows that it knows the
    discrete logarithm of one of them, without revealing which:

    [[
      R_OR(g, hs)  =  { (i, x) | hs[i] = g ^ x }
    ]]

    The protocol lets the prover answer all [k] branches, but only one of them
    honestly. The verifier sends a single challenge [c] and the prover may split it
    into branch challenges [c₀, …, c₍ₖ₋₁₎] subject to the linear constraint
    [c = c₀ + … + c₍ₖ₋₁₎]. This one degree of freedom is enough to run the Schnorr
    simulator on every branch whose witness is unknown. For a prover that knows [x]
    with [hs[i] = g ^ x] the protocol is:

    - Commitment. For every [j ≠ i] pick [uⱼ] and [cⱼ] at random and set
      [aⱼ = g ^ uⱼ · hⱼ ^ (opp cⱼ)], which is a simulated Schnorr commitment. For
      the real branch pick [u] and set [aᵢ = g ^ u].
    - Challenge. The verifier sends [c].
    - Response. Set [cᵢ = c - Σ_{j≠i} cⱼ] and [rᵢ = u + cᵢ · x], with [rⱼ = uⱼ] for
      [j ≠ i]. Send all [cⱼ] and all [rⱼ].
    - Verification. Accept iff [c = Σⱼ cⱼ] and [g ^ rⱼ = aⱼ · hⱼ ^ cⱼ] for every
      branch [j].

    A transcript has type [sigma_proto F G k (1 + k) k]: [k] commitments, a
    challenge vector of length [1 + k] whose head is the verifier's challenge [c]
    and whose tail is the split [c₀ … c₍ₖ₋₁₎], and [k] responses. The prover's
    randomness is one vector [uscs] of length [k + (k - 1)], written
    [(2 + n) + (1 + n)]: the first [k] entries are the per-branch values [uⱼ] and
    the last [k - 1] entries are the simulated challenges of the fake branches.

    The main results, all for an arbitrary number [2 + n] of branches, are:

    - completeness [generalised_construct_or_conversations_schnorr_completeness]: if
      [hs[rindex] = g ^ x] then the transcript built by the prover is accepted for
      every choice of randomness and challenge;
    - special soundness [generalised_or_sigma_soundness_main]: two accepting
      transcripts with the same commitment and different top-level challenges yield
      an index [f] and an exponent [y] with [g ^ y = hs[f]];
    - special honest-verifier zero knowledge: the simulator
      [generalised_construct_or_conversations_simulator] produces accepting
      transcripts without the witness
      ([generalised_construct_or_conversations_simulator_completeness]); the real
      and simulated distributions give every transcript the same weight and the same
      verification result ([generalised_or_special_honest_verifier_zkp]); and, when
      the sampling list enumerates the field without duplicates, the two
      distributions are permutations of each other, so they are equal
      ([generalised_or_special_honest_verifier_zkp_perm]).

    The protocol only proves knowledge of one witness out of [k]. The k-out-of-n
    threshold variant of Cramer, Damgård and Schoenmakers, built from secret
    sharing, is not formalised.

    The file depends on [Sigma] (the record [sigma_proto], the Schnorr verifier
    [accepting_conversation], Schnorr special soundness [special_soundness_berry]
    and the commitment identity [schnorr_commitment_shift]) and on the distribution
    monad of [Probability.Distr]. The file [OrSigmaGen] is the same construction
    with a separate generator per branch; the tally verifiers use that version. This
    file is instantiated in [Examples.OrSigmaIns] and extracted to OCaml through
    [Extraction/OrSigmalib].

    Reference: R. Cramer, I. Damgård, B. Schoenmakers, Proofs of Partial Knowledge
    and Simplified Design of Witness Hiding Protocols, CRYPTO 1994
    (https://www.win.tue.nl/~berry/papers/crypto94.pdf). *)

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

(** ** Parameters

    Everything is parametric in a field [F] of scalars (exponents and challenges)
    and a group [G] written multiplicatively, with exponentiation [gpow] by scalars.
    The definitions only need the operations and decidable equality. The proofs
    further assume that [G] is a vector space over [F] (the [Hvec] context below),
    which is how a prime-order group is modelled in this development. *)
Section DL.
  (** The scalar field [F]: constants [zero] and [one], the field operations, and
      decidable equality [Fdec], which the verifier uses to compare challenges. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group [G]: identity [gid], inverse [ginv], group operation [gop],
      exponentiation [gpow] by scalars, and decidable equality [Gdec], which the
      verifier uses to compare group elements. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  (** Local notations: [^] is exponentiation [gpow], and [*], [/], [+], [-] are the
      field operations. *)
  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** [(a; c; r)] builds a transcript [mk_sigma] with commitments [a], challenges
      [c] and responses [r]. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** The OR protocol

      The section [Defs] contains the prover, the simulator, the verifier and the
      two transcript distributions. The section [Proofs] proves the verifier
      characterisation, completeness, special soundness and special honest-verifier
      zero knowledge. *)
  Section Or.
    (** *** Definitions *)
    Section Defs.

        (** Commitment vector of the prover, for the case where the real branch sits
            at position [m] of a statement of length [m + (1 + n)].

            The randomness [uscs] is split as [us ++ cs], with
            [us = usl ++ [u] ++ usr] (one value per branch) and [cs = csl ++ csr]
            (one simulated challenge per fake branch, so [m + n] in total). The
            result is [commitl ++ [g ^ u] ++ commitr] where each fake branch [j]
            gets the simulated commitment [g ^ uⱼ · hⱼ ^ (opp cⱼ)]. The entry of
            [hs] at position [m] is not used: the real commitment does not depend on
            the statement. *)
        Definition construct_or_conversations_schnorr_commitment {m n : nat}
         (g : G) (hs : Vector.t G (m + (1 + n)))
         (uscs : Vector.t F ((m + (1 + n)) + (m + n))) :
         Vector.t G ((m + (1 + n))).
        Proof.
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usl & usrh).
          destruct (vector_inv_S usrh) as (u & usr & _).
          destruct (splitat m cs) as (csl & csr).
          destruct (splitat m hs) as (hsl & hsrh).
          destruct (vector_inv_S hsrh) as (_ & hsr & _).
          set (coml := zip_with (fun ui ci => (ui, ci)) usl csl).
          set (commitl := zip_with (fun hi '(ui, ci) => gop (g^ui) (hi^(opp ci))) hsl coml).
          set (com := g^u).
          set (comr := zip_with (fun ui ci => (ui, ci)) usr csr).
          set (commitr := zip_with (fun hi '(ui, ci) => gop (g^ui) (hi^(opp ci))) hsr comr).
          exact ((commitl ++ [com] ++ commitr)).
        Defined.

        (** Full prover transcript when the witness [x] is for branch [m], that is
            [hs[m] = g ^ x].

            The commitment comes from
            [construct_or_conversations_schnorr_commitment]. The real branch
            challenge is [cb = c - Σ (csl ++ csr)], so that all branch challenges
            add up to [c], and its response is [u + cb · x]. The challenge vector is
            [c :: csl ++ [cb] ++ csr] and the response vector is
            [usl ++ [u + cb · x] ++ usr]: fake branches reuse their sampled [uⱼ] as
            responses. This version fixes the real index through the type
            [m + (1 + n)]; [generalised_construct_or_conversations_schnorr] takes
            the index as a [Fin.t] instead. *)
        #[local]
        Definition construct_or_conversations_schnorr {m n : nat}
          (x : F) (g : G) (hs : Vector.t G (m + (1 + n)))
          (uscs : Vector.t F ((m + (1 + n)) + (m + n))) (c : F) :
          @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          set (comm := @construct_or_conversations_schnorr_commitment m n g hs
            uscs).
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usl & usrh).
          destruct (vector_inv_S usrh) as (u & usr & _).
          destruct (splitat m cs) as (csl & csr).
          remember (c - (Vector.fold_right add (csl ++ csr) zero)) as cb.
          remember (u + cb * x) as res.
          refine(comm; c :: csl ++ [cb] ++ csr ; usl ++ [res] ++ usr).
        Defined.

        (** Prover for [2 + n] branches with the real branch given by
            [rindex : Fin.t (2 + n)].

            [vector_fin_app_pred] computes [m₁] and [m₂] with
            [2 + n = m₁ + (1 + m₂)], where [m₁] is the numeric value of [rindex],
            together with matching splits of the randomness. The statement and the
            randomness are transported along these equalities and
            [construct_or_conversations_schnorr] is called with [m = m₁]. The result
            is transported back to length [2 + n]. Arguments: [rindex] is the branch
            whose witness is known, [x] is the witness, [g] [hs] is the statement,
            [uscs] is the randomness of length [(2 + n) + (1 + n)] and [c] is the
            verifier's challenge. *)
        Definition generalised_construct_or_conversations_schnorr {n : nat}
          (rindex : Fin.t (2 + n)) (x : F) (g : G) (hs : Vector.t G (2 + n))
          (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) :
          @sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n).
        Proof.
          destruct (splitat (2 + n) uscs) as (us & cs).
          destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & _).
          inversion pfaa as [pfa].
          inversion pfbb as [pfb].
          pose proof (@construct_or_conversations_schnorr m₁ m₂ x g
          (rew pfa in hs) ((rew pfa in us) ++ (rew pfb in cs)) c) as hd.
          rewrite <-pfa in hd.
          exact hd.
        Defined.

        (** Special honest-verifier simulator. It needs no witness and no index.

            It splits [uscs] into [us] (length [2 + n]) and [cs] (length [1 + n]),
            sets the branch challenges to [cm = (c - Σ cs) :: cs], so they add up to
            [c], and runs the Schnorr simulator on every branch: commitment
            [aⱼ = g ^ usⱼ · hsⱼ ^ (opp cmⱼ)] and response [usⱼ]. The transcript is
            [(a; c :: cm; us)]. Here the first branch takes the dependent challenge,
            whereas the prover gives it to branch [rindex]. [or_shift] bridges this
            difference in the zero-knowledge proof. *)
        Definition generalised_construct_or_conversations_simulator {n : nat}
          (g : G) (hs : Vector.t G (2 + n)) (uscs : Vector.t F ((2 + n) + (1 + n)))
          (c : F) :  @sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n).
        Proof.
          destruct (splitat (2 + n) uscs) as (us & cs).
          set (cm := (c - (Vector.fold_right add cs zero) :: cs)).
          set (comm := zip_with (fun ui ci => (ui, ci)) us cm).
          set(commitment := zip_with (fun hi '(ui, ci) =>
            gop (g^ui) (hi^(opp ci))) hs comm).
          refine(commitment; c :: cm; us).
        Defined.

        (** Branch-wise verifier, defined by recursion on the number of branches: it
            checks the Schnorr equation [g ^ rⱼ = aⱼ · hⱼ ^ cⱼ] for each branch with
            the single-branch verifier [accepting_conversation] from [Sigma], and
            returns the conjunction. Here the challenge vector has one entry per
            branch and no leading top-level challenge. *)
        #[local]
        Definition or_accepting_conversations_supplement :
          forall {n : nat}, G -> Vector.t G n -> @sigma_proto F G n n n -> bool.
        Proof.
          refine
            (fix Fn n :=
            match n with
            | 0 => fun g hs Ha => true
            | S n' => fun g hs Ha =>
              match Ha with
              | (a₁; c₁; r₁) => _
              end
            end).
          destruct (vector_inv_S hs) as (h & hsr & _).
          destruct (vector_inv_S a₁) as (a & asr & _).
          destruct (vector_inv_S c₁) as (c & csr & _).
          destruct (vector_inv_S r₁) as (r & rsr & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([a]; [c]; [r])) &&
            (Fn _ g hsr (asr; csr; rsr))).
        Defined.

        (** Verifier of the OR protocol. For a transcript [(a; c :: cs; r)] it
            accepts iff [c = Σ cs] (tested with [Fdec]) and every branch passes its
            Schnorr check, as computed by [or_accepting_conversations_supplement] on
            [(a; cs; r)]. The statement is [g] [hs]; the number of branches [n] is
            arbitrary here, including [0] and [1]. *)
        Definition generalised_or_accepting_conversations {n : nat}
          (g : G) (hs : Vector.t G n)
          (pf : @sigma_proto F G n (1 + n) n) : bool.
        Proof.
          refine
            match pf with
            |(a; css; r) => _
            end.
          destruct (vector_inv_S css) as (c & cs & _).
          refine
            match Fdec c (Vector.fold_right add cs zero) with
            | left _ =>
                or_accepting_conversations_supplement g hs (a; cs; r)
            | right _ => false
            end.
        Defined.

        (** Distribution of real transcripts for a fixed challenge [c]: draw [uscs]
            uniformly (with replacement) from the non-empty list [lf], independently
            in each of the [(2 + n) + (1 + n)] coordinates, and run the prover
            [generalised_construct_or_conversations_schnorr]. When [lf] lists the
            whole field this is the honest prover's distribution. *)
        Definition generalised_or_schnorr_distribution
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
          (rindex : Fin.t (2 + n)) (x : F) (g : G) (hs : Vector.t G (2 + n)) (c : F) :
          dist (@sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n)) :=
          uscs <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) ((2 + n) + (1 + n)) ;;
          Ret (generalised_construct_or_conversations_schnorr rindex x g hs uscs c).

        (** Distribution of simulated transcripts for a fixed challenge [c]: draw
            the same amount of randomness as the prover and run
            [generalised_construct_or_conversations_simulator]. *)
        Definition generalised_or_simulator_distribution
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
          (g : G) (hs : Vector.t G (2 + n)) (c : F) :
          dist (@sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n)) :=
          usrs <- repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) ((2 + n) + (1 + n)) ;;
          Ret (generalised_construct_or_conversations_simulator g hs usrs c).

    End Defs.

    (** *** Proofs

        The first group of lemmas characterises the boolean verifiers by
        propositional statements over all branches. Then come completeness for the
        prover and the simulator, special soundness, and special honest-verifier
        zero knowledge. *)
    Section Proofs.

        (** If the branch-wise verifier accepts [(a; c; r)], then for every branch
            [f] the single Schnorr conversation formed by the [f]-th components of [a], [c] and [r] is
            accepting for the statement [(g, hs[f])]. *)
        Lemma or_accepting_conversations_correctness_supplement_forward :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          or_accepting_conversations_supplement g hs s = true ->
          (match s with
          | (a; c; r) =>
            ∀ f : Fin.t n,
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
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
              | (a₁; c₁; r₁) => fun Hb => _
              end eq_refl); intro f.
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            (* The index f is either the head, which is checked by the left
               conjunct, or FS fs, in which case the tail recursion and the
               induction hypothesis apply. *)
            destruct (fin_inv_S _ f) as [Hi | (fs & Hi)];
            subst; simpl.
            ++
              cbn in Ha.
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              exact Hal.
            ++
              simpl in Ha;
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              exact (IHn _ _ _ Har fs).
        Qed.

        (** If the branch-wise verifier rejects, some branch [f] has a rejecting
            single-branch Schnorr conversation. *)
        Lemma or_accepting_conversations_correctness_supplement_forward_reject :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          or_accepting_conversations_supplement g hs s = false ->
          (match s with
          | (a; c; r) =>
            ∃ f : Fin.t n,
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c f]; [(nth r f)]) = false
          end).
        Proof.
          induction n as [|n ihn].
          +
            intros * ha.
            cbn in ha; congruence.
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (a₁; c₁; r₁) => fun hb => _
              end eq_refl).
            rewrite hb in ha.
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            subst. cbn in ha.
            (* If the head check succeeds the failure lies in the tail (induction
               hypothesis, shifted by FS); otherwise the head F1 is the failing
               branch. *)
            destruct (Gdec (g ^ rh₁) (gop ah₁ (hsh ^ ch₁))) as [hb | hb].
            ++
              destruct (ihn g hstl (atl₁; ctl₁; rtl₁) ha) as (f & hc).
              exists (Fin.FS f); cbn. exact hc.
            ++
              exists Fin.F1; cbn.
              eapply dec_false.
              exact hb.
        Qed.

        (** Converse of [or_accepting_conversations_correctness_supplement_forward]:
            if every branch has an accepting Schnorr conversation, the branch-wise
            verifier accepts. *)
        Lemma or_accepting_conversations_correctness_supplement_backward :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          (match s with
          | (a; c; r) =>
            ∀ f : Fin.t n,
            @accepting_conversation  F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end) -> or_accepting_conversations_supplement g hs s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 hs);
            cbn; reflexivity.
          +
            intros * Ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (a₁; c₁; r₁) => fun Hb => _
              end eq_refl).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            subst; cbn.
            (* Head branch from the hypothesis at F1; the tail from the induction
               hypothesis, fed with the hypothesis at FS f. *)
            eapply andb_true_iff.
            split.
            ++
              pose proof (Ha Fin.F1) as Hi.
              cbn in Hi.
              exact Hi.
            ++
              specialize (IHn g hstl (atl₁; ctl₁; rtl₁)).
              assert (Hb : (∀ f : Fin.t n,
              match (atl₁; ctl₁; rtl₁) with
              | (a; c; r) =>
                  @accepting_conversation  F G gop gpow Gdec g hstl[@f]
                    ([a[@f]]; [c[@f]]; [r[@f]]) = true
              end)).
              intros *; exact (Ha (Fin.FS f)).
              exact (IHn Hb).
        Qed.

        (** Converse of
            [or_accepting_conversations_correctness_supplement_forward_reject]: a
            single rejecting branch makes the branch-wise verifier reject. *)
        Lemma or_accepting_conversations_correctness_supplement_backward_reject :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          (match s with
          | (a; c; r) =>
            ∃ f : Fin.t n,
            @accepting_conversation  F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c f]; [(nth r f)]) = false
          end) -> or_accepting_conversations_supplement g hs s = false.
        Proof.
          induction n as [|n ihn].
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (a₁; c₁; r₁) => fun hb => _
              end eq_refl).
            rewrite hb in ha.
            destruct ha as (f & ha).
            refine match f with end.
          +
            intros * ha.
            refine
              (match s as s' return s = s' -> _
              with
              | (a₁; c₁; r₁) => fun hb => _
              end eq_refl).
            rewrite hb in ha.
            destruct ha as (f & ha).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            (* The failing branch is either the head, which falsifies the left
               conjunct, or lies in the tail, which falsifies the right conjunct by
               induction. *)
            destruct (fin_inv_S _ f) as [Hi | (fs & Hi)];
            subst.
            ++
              cbn in ha |- *.
              rewrite dec_false in ha.
              eapply andb_false_iff; left.
              rewrite dec_false. exact ha.
            ++
              cbn in ha |- *.
              eapply andb_false_iff; right.
              eapply ihn.
              exists fs.
              exact ha.
        Qed.

        (** The branch-wise verifier accepts iff every branch has an accepting
            Schnorr conversation. *)
        Lemma or_accepting_conversations_correctness_supplement :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          or_accepting_conversations_supplement g hs s = true <->
          match s with
          | (a; c; r) =>
            ∀ f : Fin.t n,
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end.
        Proof.
          intros *.
          split; intros Ha.
          +
            eapply or_accepting_conversations_correctness_supplement_forward;
            exact Ha.
          +
            eapply or_accepting_conversations_correctness_supplement_backward;
            exact Ha.
        Qed.

        (** The branch-wise verifier rejects iff some branch has a rejecting Schnorr
            conversation. *)
        Lemma or_accepting_conversations_correctness_supplement_reject :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          or_accepting_conversations_supplement g hs s = false <->
          match s with
          | (a; c; r) =>
            ∃ f : Fin.t n,
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c f]; [(nth r f)]) = false
          end.
        Proof.
          intros *; split; intro ha;
          [eapply or_accepting_conversations_correctness_supplement_forward_reject |
          eapply or_accepting_conversations_correctness_supplement_backward_reject];
          assumption.
        Qed.

        (** The branch-wise verifier distributes over vector concatenation: checking
            [hsl ++ hsr] with concatenated commitments, challenges and responses is
            the conjunction of the checks on the two halves. *)
        Lemma or_accepting_conversations_supplement_app :
          forall (n m : nat) (g : G)
          (hsl al : Vector.t G n) (hsr ar : Vector.t G m)
          (cl rl : Vector.t F n) (cr rr : Vector.t F m),
          or_accepting_conversations_supplement
            g (hsl ++ hsr)
            ((al ++ ar); (cl ++ cr); (rl ++ rr)) =
          or_accepting_conversations_supplement g hsl (al; cl; rl)  &&
          or_accepting_conversations_supplement g hsr (ar; cr; rr).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 hsl).
            rewrite (vector_inv_0 al).
            rewrite (vector_inv_0 cl).
            rewrite (vector_inv_0 rl).
            cbn; reflexivity.
          +
            intros *.
            destruct (vector_inv_S hsl) as (hslh & hsltl & Hb).
            destruct (vector_inv_S al) as (alh & altl & Hc).
            destruct (vector_inv_S cl) as (clh & cltl & Hd).
            destruct (vector_inv_S rl) as (rlh & rltl & He).
            subst; cbn.
            (* The head check either succeeds (then recurse) or fails (then both
               sides are false). *)
            destruct (Gdec (g ^ rlh) (gop alh (hslh ^ clh))).
            ++
              cbn; eapply IHn.
            ++
              cbn; reflexivity.
        Qed.

        (** If the OR verifier accepts [(a; c; r)], then the head of [c] is the sum
            of its tail, and for every branch [f] the conversation
            formed by the [f]-th components of [a] and [r] and the [FS f]-th component of [c] is an accepting Schnorr conversation. *)
        Lemma generalised_or_accepting_conversations_correctness_forward :
          forall {n : nat} (g : G) (hs : Vector.t G n )
          (s :  @sigma_proto F G n (1 + n) n),
          generalised_or_accepting_conversations g hs s = true ->
          match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end.
        Proof.
          intros * Ha.
          unfold generalised_or_accepting_conversations in Ha.
          refine
            (match s as s' return s = s' -> _
            with
            | (a₁; c₁; r₁) => fun Hb => _
            end eq_refl).
          rewrite Hb in Ha.
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          destruct (Fdec ch₁ (fold_right add ctl₁ zero)) eqn:Hd;
          [|inversion Ha].
          split.
          +
            rewrite Hc; cbn;
            exact e.
          +
            rewrite Hc; cbn.
            eapply or_accepting_conversations_correctness_supplement_forward in
            Ha; exact Ha.
        Qed.

         (** If the OR verifier rejects, either the challenge sum is wrong or some
             branch has a rejecting Schnorr conversation. *)
         Lemma generalised_or_accepting_conversations_correctness_forward_reject :
          forall {n : nat} (g : G) (hs : Vector.t G n )
          (s :  @sigma_proto F G n (1 + n) n),
          generalised_or_accepting_conversations g hs s = false ->
          match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = false)
          end.
        Proof.
          intros * ha.
          refine
            (match s as s' return s = s' -> _
            with
            | (a₁; c₁; r₁) => fun hb => _
            end eq_refl).
          rewrite hb in ha.
          unfold generalised_or_accepting_conversations in ha.
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          destruct (Fdec ch₁ (fold_right add ctl₁ zero)) eqn:hc;
          [|inversion ha].
          +
            right. rewrite Hc.
            cbn.
            eapply or_accepting_conversations_correctness_supplement_forward_reject in ha.
            exact ha.
          +
            left. subst. cbn.
            assumption.
        Qed.

        (** Converse of
            [generalised_or_accepting_conversations_correctness_forward]: a correct
            challenge sum together with accepting branch conversations makes the OR
            verifier accept. *)
        Lemma generalised_or_accepting_conversations_correctness_backward :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n (1 + n) n),
          (match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) ->
          generalised_or_accepting_conversations g hs s = true.
        Proof.
          intros * Ha.
          unfold generalised_or_accepting_conversations.
          refine
            (match s as s' return s = s' -> _
            with
            | (a₁; c₁; r₁) => fun Hb => _
            end eq_refl).
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          (* The sum condition makes the Fdec test succeed; the per-branch
             hypotheses then give the branch-wise check. *)
          assert (Hd : ch₁ = (fold_right add ctl₁ zero)).
          rewrite Hb in Ha.
          +
            destruct Ha as [Hal Har].
            rewrite Hc in Hal; cbn
            in Hal. exact Hal.
          +
            rewrite <-Hd.
            destruct (Fdec ch₁ ch₁) eqn:He.
            eapply or_accepting_conversations_correctness_supplement;
            intros f.
            rewrite Hb in Ha.
            destruct Ha as [Hal Har].
            rewrite Hc in Har.
            specialize (Har f).
            cbn in Har; cbn.
            exact Har.
            congruence.
        Qed.

        (** Converse of
            [generalised_or_accepting_conversations_correctness_forward_reject]. *)
        Lemma generalised_or_accepting_conversations_correctness_backward_reject :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n (1 + n) n),
          (match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = false)
          end) ->
          generalised_or_accepting_conversations g hs s = false.
        Proof.
          intros * ha.
          refine
            (match s as s' return s = s' -> _
            with
            | (a₁; c₁; r₁) => fun hb => _
            end eq_refl).
          rewrite hb in ha.
          destruct ha as [ha | ha].
          +
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
            subst; cbn in ha |- *.
            destruct (Fdec ch₁ (fold_right add ctl₁ zero)) as [hb | hb];
            [congruence | exact eq_refl].
          +
            destruct ha as (f & ha).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
            subst; cbn in ha |- *.
            destruct (Fdec ch₁ (fold_right add ctl₁ zero)) as [hb | hb].
            eapply or_accepting_conversations_correctness_supplement_backward_reject.
            exists f. cbn. exact ha.
            reflexivity.
        Qed.

        (** Characterisation of the OR verifier:
            [generalised_or_accepting_conversations] accepts [(a; c; r)] iff
            [hd c = Σ (tl c)] and [g ^ rⱼ = aⱼ · hⱼ ^ cⱼ] holds for every branch
            [j], with [cⱼ = c[FS j]]. Completeness and soundness proofs go through
            this lemma. *)
        Lemma generalised_or_accepting_conversations_correctness:
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n (1 + n) n),
          (match s with
          | (a; c; r) =>
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) <->
          generalised_or_accepting_conversations g hs s = true.
        Proof.
          intros *;
          split; intro Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_backward;
            try assumption.
          +
            eapply generalised_or_accepting_conversations_correctness_forward;
            try assumption.
        Qed.

        (** Characterisation of rejection: the OR verifier rejects iff the challenge
            sum is wrong or some branch's Schnorr check fails. *)
        Lemma generalised_or_accepting_conversations_correctness_reject :
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n (1 + n) n),
          (match s with
          | (a; c; r) =>
            Vector.hd c ≠ Vector.fold_right add (Vector.tl c) zero ∨
            (∃ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f)
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = false)
          end) <->
          generalised_or_accepting_conversations g hs s = false.
        Proof.
          intros *;
          split; intro Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_backward_reject;
            try assumption.
          +
            eapply generalised_or_accepting_conversations_correctness_forward_reject;
            try assumption.
        Qed.

        (** From here on [G] is assumed to be a vector space over [F], which models
            a group of prime order whose exponents live in [F], and the [field]
            tactic is enabled for [F]. *)
        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub
            div opp inv G (@eq G) gid ginv gop gpow}.

        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        (** The sum of a concatenation is the sum of the two sums,
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

        (** Completeness of the simulated branches, for a block of [n] fake branches
            with responses [usr] and challenges [csr]. For every position [f], the
            response [usr[f]] satisfies the Schnorr equation against the simulated
            commitment [g ^ usr[f] · hsr[f] ^ (opp csr[f])], because
            [(b ^ u · h ^ (opp c)) · h ^ c = b ^ u]. *)
        Theorem construct_or_conversations_schnorr_completeness_base :
          forall (n : nat) (f : Fin.t n) (usr csr : Vector.t F n)
          (hsr : Vector.t G n) (g : G),
          g ^ usr[@f] = gop
          (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsr
          (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f]
          (hsr[@f] ^ csr[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *.
            refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S csr) as (csrh & csrt & hb).
            destruct (vector_inv_S hsr) as (hsrh & hsrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              (* Head position: reassociate and merge the powers of h, using opp c +
                 c = 0. *)
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

        (** Completeness of every branch of [construct_or_conversations_schnorr].
            With the real branch at position [m] and [g ^ x = h], every position [f]
            of the response vector [usl ++ [u + cb · x] ++ usr] satisfies the
            Schnorr equation against the commitment vector and the challenge vector
            [csl ++ [cb] ++ csr], where [cb = c - Σ (csl ++ csr)]. *)
        Theorem construct_or_conversations_schnorr_completeness_generic :
          forall (m n : nat) (f : Fin.t (m + S n)) (g : G) (usl : Vector.t F m)
          (c : F) (csl : Vector.t F m) (csr : Vector.t F n) (x : F) (u : F)
          (usr : Vector.t F n) (hsl : Vector.t G m) (h : G) (hsr : Vector.t G n),
          g^x = h ->
          g ^ (usl ++ u + (c - fold_right add (csl ++ csr) zero) * x :: usr)[@f] =
          gop (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsl
          (zip_with (λ ui ci : F, (ui, ci)) usl csl) ++ g ^ u
          :: zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsr
            (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f]
          ((hsl ++ h :: hsr)[@f] ^ (csl ++ c - fold_right add (csl ++ csr) zero :: csr)[@f]).
        Proof.
          (* Induction on the number m of fake branches before the real one. *)
          induction m as [|m ihm].
          +
            cbn; intros * hr.
            rewrite (vector_inv_0 csl), (vector_inv_0 usl),
            (vector_inv_0 hsl).
            assert (ha : (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) []
            (zip_with (λ ui ci : F, (ui, ci)) [] []) = [])). reflexivity.
            rewrite ha; clear ha.
            destruct (fin_inv_S _ f) as [f' | (f' & hf)].
            ++
              subst; cbn.
              (* Real branch: g^(u + ct x) = g^u · (g^x)^ct, using h = g^x. *)
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
              (* Branches after the real one are simulated. *)
              eapply construct_or_conversations_schnorr_completeness_base.
          +
            intros *.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            destruct (vector_inv_S csl) as (cslh & cslt & hb).
            destruct (vector_inv_S hsl) as (hslh & hslt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & hd)].
            ++
              subst; cbn.
              (* Step case, head position: a simulated branch, closed by the same
                 identity as in the base lemma. *)
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
              specialize (ihm _ f' g uslt (c - cslh) cslt csr x u usr hslt h hsr).
              (* Step case, later position: since c - (cₕ + ct) = (c - cₕ) - ct, the
                 induction hypothesis applies with the challenge c - cₕ. *)
              remember (fold_right add (cslt ++ csr) zero) as ct.
              assert (ha : c - (cslh + ct) = c - cslh - ct). field.
              rewrite ha; clear ha.
              exact ihm.
        Qed.

        (** Summing a vector is invariant under transport along a length equality
            [m = n]. *)
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

        (** Simulator analogue of
            [construct_or_conversations_schnorr_completeness_base]: each simulated
            branch in a block satisfies its Schnorr equation, whatever its
            challenge. *)
        Theorem construct_or_conversations_simulator_completeness_base :
          ∀ (n : nat) (f : Fin.t n) (usr : Vector.t F n) (g : G)
          (hsr : Vector.t G n) (cstt : Vector.t F n),
          g ^ usr[@f] =
          gop
          (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsr
          (zip_with (λ ui ci : F, (ui, ci)) usr cstt))[@f]
          (hsr[@f] ^ cstt[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *.
            refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S cstt) as (cstth & csttt & hb).
            destruct (vector_inv_S hsr) as (hsrh & hsrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              (* Head position: (b^u · h^(opp c)) · h^c = b^u. *)
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

      (** Every branch of a fully simulated transcript satisfies its Schnorr
          equation, for an arbitrary challenge vector [cst]. The statement is
          phrased over [m + S n] branches with a distinguished middle element, so
          that it can be reused after rewriting [2 + n] as [m₁ + (1 + m₂)]. *)
      Theorem construct_or_conversations_simulator_completeness_generic :
          ∀ (m n : nat) (f : Fin.t (m + S n))
          (usl : Vector.t F m) (u : F) (usr : Vector.t F n)
          (hsl : t G m) (g h : G) (hsr : t G n)
          (cst : t F (m + S n)),
          g ^ (usl ++ u :: usr)[@f] =
          gop
          (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci))
          (hsl ++ h :: hsr)
          (zip_with (λ ui ci : F, (ui, ci)) (usl ++ u :: usr) cst))[@f]
          ((hsl ++ h :: hsr)[@f] ^ cst[@f]).
        Proof.
          (* Induction on the length m of the left block; the middle and right parts
             are handled by the base lemma. *)
          induction m as [|m ihm].
          +
            cbn; intros *.
            rewrite (vector_inv_0 usl), (vector_inv_0 hsl).
            destruct (vector_inv_S cst) as (csth & cstt & ha).
            destruct (fin_inv_S _ f) as [f' | (f' & hf)].
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
              eapply construct_or_conversations_simulator_completeness_base.
          +
            intros *.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            cbn in cst.
            destruct (vector_inv_S cst) as (csth & cstt & hb).
            destruct (vector_inv_S hsl) as (hslh & hslt & hc).
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

        (** Completeness for a real branch at a fixed position [m]: if [h = g ^ x],
            then the transcript produced by [construct_or_conversations_schnorr] on
            the statement [g], [hsl ++ [h] ++ hsr] is accepted, for all randomness
            and challenges. *)
        Lemma construct_or_conversations_schnorr_completeness {m n : nat}
          (x : F) (g : G)
          (hsl : Vector.t G m) (h : G) (hsr : Vector.t G n) (R : h = g ^ x) :
          ∀ (uscs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          generalised_or_accepting_conversations g (hsl ++ [h] ++ hsr)
          (construct_or_conversations_schnorr x g (hsl ++ [h] ++ hsr) uscs c) = true.
        Proof.
          intros *. cbn.
          eapply generalised_or_accepting_conversations_correctness.
          unfold construct_or_conversations_schnorr,
          construct_or_conversations_schnorr_commitment.
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usl & usrh).
          destruct (vector_inv_S usrh) as (u & usr & _).
          destruct (splitat m cs) as (csl & csr).
          rewrite VectorSpec.splitat_append.
          cbn; split.
          +
            (* Challenge sum: Σ csl + (c - Σ (csl ++ csr)) + Σ csr = c. *)
            rewrite !fold_right_app.
            remember (fold_right add csl zero) as ca.
            remember (fold_right add csr zero) as cb.
            cbn. rewrite <-Heqcb. field.
          +
            (* Branch checks: the generic completeness lemma. *)
            intros f.
            rewrite dec_true.
            eapply construct_or_conversations_schnorr_completeness_generic.
            rewrite R; reflexivity.
        Qed.

        (** Bridge from a [Fin.t] index to the split form: if [rindex] has numeric
            value [m], the element of [hsl ++ h :: hsr] at [rindex] is the middle
            element, so the hypothesis at [rindex] becomes [h = g ^ x]. *)
        Theorem generalised_construct_or_conversations_schnorr_completeness_fin :
          forall (m n : nat) (rindex : Fin.t (m + S n))
          (hsl : Vector.t G m) (h g : G) (hsr : Vector.t G n) (x : F),
          m = proj1_sig (Fin.to_nat rindex) ->
          (hsl ++ h :: hsr)[@rindex] = g ^ x -> h = g ^ x.
        Proof.
          intros * ha hb.
          assert (hc : rindex = Fin.R m (Fin.F1 : Fin.t (1 + n))).
          eapply fin_to_nat. exact ha.
          subst. rewrite VectorSpec.nth_append_R in hb.
          cbn in hb.
          exact hb.
        Qed.

        (** Completeness of the OR prover. If [hs[rindex] = g ^ x], then for every
            randomness [uscs] and every challenge [c] the transcript
            [generalised_construct_or_conversations_schnorr rindex x g hs uscs c] is
            accepted by [generalised_or_accepting_conversations].

            Proof idea: unfold the index split performed by the prover, transport
            along [2 + n = m₁ + (1 + m₂)], and apply
            [construct_or_conversations_schnorr_completeness]. *)
        Lemma generalised_construct_or_conversations_schnorr_completeness {n : nat}
          (rindex : Fin.t (2 + n)) (x : F) (g : G) (hs : Vector.t G (2 + n))
          (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) :
          Vector.nth hs rindex = g^x ->
          generalised_or_accepting_conversations g hs
          (generalised_construct_or_conversations_schnorr rindex x g hs uscs c) = true.
        Proof.
          intros * hu.
          unfold generalised_construct_or_conversations_schnorr.
          destruct (splitat (2 + n) uscs) as (us & cs) eqn:hv.
          eapply append_splitat in hv.
          (* Replay the decomposition of the randomness around rindex performed
             inside the prover. *)
          destruct (vector_fin_app_pred (1 + n) rindex us cs) as
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa].
          destruct pfbb as [pfb].
          destruct haa as [ha].
          destruct ha as (ha & hb & hc & hd).
          revert hd.
          subst; cbn. intro hf. rewrite !rew_opp_r.
          destruct (splitat m₁ ((rew [t G] pfa in hs))) as (hsl & hsrr) eqn:ha.
          eapply append_splitat in ha.
          destruct (vector_inv_S hsrr) as (h & hsr & hc).
          rewrite hc in ha. revert hf.
          subst; cbn. intro hf.
          remember ((rew <- [λ n0 : nat, @sigma_proto F G n0 (S n0) n0] pfa in
          @construct_or_conversations_schnorr m₁ m₂ x g (rew [t G] pfa in hs)
          ((v₁ ++ vm :: v₂) ++ v₃ ++ v₄) c))  as sa.  cbn in sa.
          setoid_rewrite <-Heqsa.
          generalize dependent sa. revert hu. generalize dependent hs.
          generalize dependent  rindex.
          cbn in * |- *. rewrite pfa.
          intros * ha * hb hc * hd he * hf.
          cbn in * |- *; subst.
          (* After eliminating the transport the goal is completeness in split form;
             the _fin lemma turns the hypothesis at rindex into one about the middle
             element. *)
          eapply construct_or_conversations_schnorr_completeness.
          eapply generalised_construct_or_conversations_schnorr_completeness_fin.
          exact hb. exact he.
        Qed.

        (** The simulator always produces accepting transcripts, for every
            randomness and every challenge, without any witness. The challenge sum
            holds by construction of [cm], and every branch is a simulated Schnorr
            conversation. *)
        Lemma generalised_construct_or_conversations_simulator_completeness {n : nat}
          (g : G) (hs : Vector.t G (2 + n)) :
          ∀ (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F),
          generalised_or_accepting_conversations g hs
          (generalised_construct_or_conversations_simulator g hs uscs c) = true.
        Proof.
          intros *.
          eapply generalised_or_accepting_conversations_correctness.
          unfold generalised_construct_or_conversations_simulator.
          destruct (splitat (2 + n) uscs) as (us & cs).
          (* First conjunct: (c - Σ cs) + Σ cs = c. Second: view 2 + n as 1 + (1 +
             n) and use the generic simulator lemma. *)
          split.
          + cbn; field.
          +

            intros *.
            assert (ha : ∃ (m₁ m₂ : nat), (2 + n = m₁ + (1 + m₂))%nat).
            exists 1, n. nia.
            destruct ha as (m₁ & m₂ & ha).
            revert us. revert f. revert hs.
            remember ((c - fold_right add cs zero :: cs)) as cst.
            clear Heqcst. revert cst.
            cbn in * |- *. rewrite !ha.
            intros *. rewrite dec_true.
            destruct (splitat m₁ us) as (usl & usrr) eqn:hb.
            eapply append_splitat in hb.
            destruct (vector_inv_S usrr) as (u & usr & hc).
            subst.
            destruct (splitat m₁ hs) as (hsl & hsrr) eqn:hb.
            eapply append_splitat in hb.
            destruct (vector_inv_S hsrr) as (h & hsr & hc).
            subst.
            eapply construct_or_conversations_simulator_completeness_generic.
        Qed.

        (** Special soundness, base case of the induction on the left block: for
            [1 + n] branches, two accepting transcripts [(a; c₁ :: cs₁; r₁)] and
            [(a; c₂ :: cs₂; r₂)] with the same commitments and [c₁ ≠ c₂] yield a
            branch [f] and [y] with [g ^ y = hs[f]].

            Proof idea: since [cᵢ = Σ csᵢ], different top-level challenges force the
            branch challenges to differ somewhere. Either the first branch
            challenges differ, and Schnorr special soundness
            ([special_soundness_berry]) applies to that branch, or the sums of the
            remaining branch challenges differ, and the induction hypothesis applies
            to the tail with those sums as top-level challenges. *)
        Lemma generalised_or_sigma_soundness_base_case :
          forall (n : nat) g hs
          (a : Vector.t G (1 + n)) (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (1 + n))
          (r₁ r₂ : Vector.t F (1 + n)),
          generalised_or_accepting_conversations
            g hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations
            g hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ ->
          ∃ (f : Fin.t (1 + n)) (y : F),
          g^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward
            g hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward
            g hs (a; c₂ :: cs₂; r₂) Hb as He.
          clear Ha; clear Hb.
          generalize dependent n.
          intros n hs a. revert c₂; revert c₁.
          generalize dependent n.
          (* Induction on the number of branches after the first. *)
          induction n as [|n IHn].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            (* Single branch: its challenge equals the top-level challenge, so the
               two branch challenges differ and Schnorr extraction applies. *)
            exists Fin.F1.
            destruct (vector_inv_S hs) as (hsh & hstl & Hg).
            rewrite (vector_inv_0 hstl) in Hg.
            rewrite Hg; cbn.
            specialize (Har Fin.F1).
            specialize (Hbr Fin.F1).
            cbn in * |- *.
            rewrite dec_true, Hg in Har, Hbr.
            destruct (vector_inv_S a) as (ah & atl & Hh).
            rewrite (vector_inv_0 atl) in Hh.
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hi).
            rewrite (vector_inv_0 rtl₁) in Hi.
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hj).
            rewrite (vector_inv_0 cstl₁) in Hj.
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hk).
            rewrite (vector_inv_0 rtl₂) in Hk.
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hl).
            rewrite (vector_inv_0 cstl₂) in Hl.
            subst.
            assert (Hm : csh₁ <> csh₂).
            intros Hm; eapply Hc;
            rewrite Hm; reflexivity.
            eapply special_soundness_berry; cbn;
            try (rewrite dec_true);
            [exact Hm | exact Har | exact Hbr].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            cbn in Hal, Har, Hbl, Hbr.
            destruct (vector_inv_S hs) as (hsh & hstl & He).
            destruct (vector_inv_S a) as (ah & atl & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hh).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hj).
            subst; cbn in Hc.
            remember (fold_right add cstl₁ zero) as hcl.
            remember (fold_right add cstl₂ zero) as hcr.
            (* Key case split: c₁ ≠ c₂ with cᵢ = headᵢ + Σ tailᵢ means that either
               the head challenges differ or the tail sums differ. *)
            assert (Hd : csh₁ <> csh₂ ∨
              (csh₁ = csh₂ ∧ (hcl <> hcr))).
            case_eq (Fdec csh₁ csh₂);
            intros Hd He.
            right.
            refine (conj Hd _).
            intros Hf; eapply Hc;
            rewrite Hd, Hf;
            exact eq_refl.
            left; exact Hd.
            destruct Hd as [Hd | Hd].
            ++
              (* Head challenges differ: extract the witness of branch F1. *)
              pose proof (Hbr Fin.F1) as Hk.
              pose proof (Har Fin.F1) as Hj.
              exists (Fin.F1).
              cbn in Hj, Hk |- *.
              rewrite dec_true in Hk, Hj.
              eapply special_soundness_berry; cbn;
              try (rewrite dec_true);
              [exact Hd | exact Hj | exact Hk].
            ++
              (* Tail sums differ: the tails form two accepting OR transcripts with
                 distinct top-level challenges, so the induction hypothesis applies. *)
              cbn in IHn.
              destruct Hd as (Hdl & Hdr).
              assert (He : (∀ f : Fin.t (S n),
              (if
                Gdec (g^rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf :
              (∀ f : Fin.t (S n),
                (if
                  Gdec (g ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f;
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHn hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
              Unshelve.
              eapply Gdec.
              eapply Gdec.
        Qed.

        (** Special soundness for [m + (1 + n)] branches, by induction on [m]: the
            base case is [generalised_or_sigma_soundness_base_case], and the step
            case makes the same case split on the first branch as in the base lemma. *)
        Lemma generalised_or_sigma_soundness_generic :
          forall (m n : nat)
          (g : G) (hs : Vector.t G (m + (1 + n)))
          (a : Vector.t G (m + (1 + n)))
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (m + (1 + n)))
          (r₁ r₂ : Vector.t F (m + (1 + n))),
          generalised_or_accepting_conversations
            g hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations
            g hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ ->
          ∃ (f : Fin.t (m + (1 + n))) (y : F),
          g^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward
            g hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward
            g hs (a; c₂ :: cs₂; r₂) Hb as He.
          cbn in Hd, He.
          clear Ha; clear Hb.
          generalize dependent n;
          intros n hs a;
          revert c₂; revert c₁;
          generalize dependent n.
          (* Induction on the length m of the left block. *)
          induction m as [|m' IHm].
          +
            intros * Ha Hb Hc.
            eapply generalised_or_sigma_soundness_base_case;
            try assumption.
            eapply generalised_or_accepting_conversations_correctness_backward;
            exact Ha.
            eapply generalised_or_accepting_conversations_correctness_backward;
            exact Hb.
            exact Hc.
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            cbn in * |- .
            destruct (vector_inv_S hs) as (hsh & hstl & He).
            destruct (vector_inv_S a) as (ah & atl & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hh).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hj).
            subst; cbn in Hc.
            remember (fold_right add cstl₁ zero) as hcl.
            remember (fold_right add cstl₂ zero) as hcr.
            (* Either the head challenges differ (extract there) or the tail sums
               differ (recurse). *)
            assert (Hd : csh₁ <> csh₂ ∨
              (csh₁ = csh₂ ∧ (hcl <> hcr))).
            case_eq (Fdec csh₁ csh₂);
            intros Hd He.
            right.
            refine (conj Hd _).
            intros Hf; eapply Hc;
            rewrite Hd, Hf;
            exact eq_refl.
            left; exact Hd.
            destruct Hd as [Hd | Hd].
            ++
              pose proof (Hbr Fin.F1) as Hk.
              pose proof (Har Fin.F1) as Hj.
              exists (Fin.F1).
              cbn in Hj, Hk |- *.
              rewrite dec_true in Hk, Hj.
              eapply special_soundness_berry; cbn;
              try (rewrite dec_true);
              [exact Hd | exact Hj | exact Hk].
            ++
              (* Tail sums differ: apply the induction hypothesis to the tail
                 transcripts. *)
              cbn in IHm.
              destruct Hd as (Hdl & Hdr).
              assert (He : (∀ f : Fin.t (m' + S n),
              (if
                Gdec (g ^ rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf :
              (∀ f : Fin.t (m' + S n),
                (if
                  Gdec (g ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f;
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHm _  hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
              Unshelve.
              eapply Gdec.
        Qed.

        (** Special soundness with the statement written as [hsl ++ [h] ++ hsr]; a
            direct instance of [generalised_or_sigma_soundness_generic]. *)
        Lemma generalised_or_sigma_soundness
          {m n : nat}
          (g : G)
          (hsl : Vector.t G m)
          (h : G)
          (hsr : Vector.t G n) :
          forall (a : Vector.t G (m + (1 + n)))
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (m + (1 + n)))
          (r₁ r₂ : Vector.t F (m + (1 + n))),
          generalised_or_accepting_conversations
            g (hsl ++ [h] ++ hsr) (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations
            g (hsl ++ [h] ++ hsr) (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ ->
          ∃ (f : Fin.t (m + (1 + n))) (y : F),
          g^y = (nth (hsl ++ [h] ++ hsr) f).
        Proof.
          intros * Ha Hb Hc.
          eapply generalised_or_sigma_soundness_generic;
          [exact Ha | exact Hb | exact Hc].
        Qed.

        (** Special soundness of the OR protocol. For [2 + n] branches, two
            accepting transcripts that share the commitment vector [a] and have
            different top-level challenges [c₁ ≠ c₂] (the branch challenges [cs₁],
            [cs₂] and responses may differ arbitrarily) yield some branch [f] and a
            witness [y] with [g ^ y = hs[f]]. This is a witness for the OR relation.
            The theorem is existential: it states that a witness exists, and the
            extractor is not given as a separate function in this file.

            Proof idea: rewrite [2 + n] as [1 + (1 + n)], split the statement, and
            apply [generalised_or_sigma_soundness]. *)
        Lemma generalised_or_sigma_soundness_main
          {n : nat}
          (g : G)
          (hs : Vector.t G (2 + n)):
          forall (a : Vector.t G (2 + n))
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (2 + n))
          (r₁ r₂ : Vector.t F (2 + n)),
          generalised_or_accepting_conversations
            g hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations
            g hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ ->
          ∃ (f : Fin.t (2 + n)) (y : F),
          g^y = (nth hs f).
        Proof.
          intros *.
          (* Rewrite 2 + n as 1 + (1 + n) and split hs around position 1 to match
             the split-form lemma. *)
          assert (ha : ∃ (m₁ m₂ : nat), (2 + n = m₁ + (1 + m₂))%nat).
          exists 1, n. nia.
          destruct ha as (m₁ & m₂ & ha).
          revert hs a cs₁ cs₂ r₁ r₂.
          rewrite ha; clear ha.
          intros * ha hb hc.
          destruct (splitat m₁ hs) as (hsl & hsrr) eqn:hd.
          eapply append_splitat in hd.
          destruct (vector_inv_S hsrr) as (h & hsr & he).
          subst.
          eapply generalised_or_sigma_soundness.
          exact ha. exact hb. exact hc.
        Qed.

        (** ** Special honest-verifier zero knowledge

            [p / q] is the probability [p/q] built by [mk_prob]; here it is always
            [1 / |lf| ^ ((2 + n) + (1 + n))], the weight of one sample of
            randomness. *)
        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (** If every entry of a distribution [l] over randomness vectors has weight
            [1 / q], then so does every entry of [l] pushed through the
            fixed-position prover [construct_or_conversations_schnorr]. Bind
            followed by Ret does not change the weights. *)
        Lemma or_schnorr_distribution_probability_generic
          {m n : nat}
          (x : F)
          (g : G)
          (hsl : Vector.t G m)
          (h : G)
          (hsr : Vector.t G n) :
          forall (l : dist (t F (m + (1 + n) + (m + n))))
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob),
            List.In (trx, prx) l → prx = 1 / q) ->
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_schnorr x
              g (hsl ++ [h] ++ hsr) uscs c))) → pr = 1 / q.
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

        (** Same as [or_schnorr_distribution_probability_generic], for the
            [Fin.t]-indexed prover [generalised_construct_or_conversations_schnorr]. *)
        Lemma generalised_or_schnorr_distribution_probability_generic
          {n : nat}
          (x : F)
          (g : G)
          (hs : Vector.t G (2 + n)):
          forall (rindex : Fin.t (2 + n)) (l : dist (t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob),
            List.In (trx, prx) l → prx = 1 / q) ->
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_schnorr rindex x
              g hs uscs c))) → pr = 1 / q.
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

         (** Every transcript in the support of the prover pushed over any
             distribution [l] is accepting, provided [hs[rindex] = g ^ x]. This
             follows from completeness by induction on [l]. *)
         Lemma generalised_or_schnorr_distribution_transcript_generic
          {n : nat}
          (x : F)
          (g : G)
          (hs : Vector.t G (2 + n))
          (rindex : Fin.t (2 + n))
          (R : Vector.nth hs rindex = g ^ x) :
          forall (l : dist (Vector.t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_schnorr rindex x
              g hs uscs c))) →
          generalised_or_accepting_conversations g hs trans = true.
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
              now eapply generalised_construct_or_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply generalised_construct_or_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (** Each element [(a, b)] of the real transcript distribution is accepting
            and has probability [b = 1 / |lf| ^ ((2 + n) + (1 + n))]. *)
        Lemma generalised_or_special_honest_verifier_schnorr_dist
          {n : nat}
          (x : F)
          (g : G)
          (hs : Vector.t G (2 + n))
          (rindex : Fin.t (2 + n))
          (R : Vector.nth hs rindex = g ^ x) :
          forall (lf : list F) (Hlfn : lf <> List.nil)
          (c : F) a b,
          List.In (a, b)
            (generalised_or_schnorr_distribution lf Hlfn rindex x g hs c) ->
          generalised_or_accepting_conversations g hs a = true ∧
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          +
            eapply generalised_or_schnorr_distribution_transcript_generic.
            exact R.
            exact Ha.
          +
            eapply generalised_or_schnorr_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.

         (** Simulator analogue of
             [generalised_or_schnorr_distribution_probability_generic]. *)
         Lemma generalised_or_simulator_distribution_probability_generic
          {n : nat}
          (g : G)
          (hs : Vector.t G (2 + n)) :
          forall (l : dist (t F ((2 + n) + (1+ n))))
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob),
            List.In (trx, prx) l → prx = 1 / q) ->
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_simulator
              g hs uscs c))) → pr = 1 / q.
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

        (** Every transcript in the support of the simulator pushed over any
            distribution is accepting, by
            [generalised_construct_or_conversations_simulator_completeness]. *)
        Lemma generalised_or_simulator_distribution_transcript_generic
          {n : nat}
          (g : G)
          (hs : Vector.t G (2 + n)) :
          forall (l : dist (Vector.t F ((2 + n) + (1 + n))))
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_simulator
                g hs uscs c))) →
          generalised_or_accepting_conversations g hs trans = true.
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
              eapply generalised_construct_or_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply generalised_construct_or_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (** Each element [(a, b)] of the simulated distribution is accepting and has
            probability [b = 1 / |lf| ^ ((2 + n) + (1 + n))]. *)
        Lemma generalised_or_special_honest_verifier_simulator_dist
          {n : nat}
          (g : G)
          (hs : Vector.t G (2 + n)) :
          forall (lf : list F) (Hlfn : lf <> List.nil)
          (c : F) a b,
          List.In (a, b)
            (generalised_or_simulator_distribution lf Hlfn g hs c) ->
          generalised_or_accepting_conversations g hs a = true ∧
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          +
            eapply generalised_or_simulator_distribution_transcript_generic;
            exact Ha.
          +
            eapply generalised_or_simulator_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.

        (** Weak form of special honest-verifier zero knowledge. After mapping each
            transcript to its verification bit, the real distribution and the
            simulated distribution are the same list: both have the same length, and
            every entry is [(true, 1 / |lf| ^ ((2 + n) + (1 + n)))].

            This shows that the two distributions are indistinguishable to anyone
            who sees only the verifier's output. It does not compare the transcripts
            themselves; [generalised_or_special_honest_verifier_zkp_perm] below
            does. *)
        Lemma generalised_or_special_honest_verifier_zkp
          {n : nat}
          (x : F)
          (g : G)
          (hs : Vector.t G (2 + n))
          (rindex : Fin.t (2 + n))
          (R : Vector.nth hs rindex = g ^ x) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) =>
            (generalised_or_accepting_conversations g hs a, p))
            (generalised_or_schnorr_distribution lf Hlfn rindex x g hs c) =
          List.map (fun '(a, p) =>
            (generalised_or_accepting_conversations g hs a, p))
            (generalised_or_simulator_distribution lf Hlfn g hs c).
        Proof.
          intros ? ? ?.
          eapply map_ext_eq.
          +
            unfold generalised_or_schnorr_distribution,
            generalised_or_simulator_distribution; cbn.
            repeat rewrite distribution_length.
            reflexivity.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_or_special_honest_verifier_schnorr_dist.
            exact R.
            exact Ha.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_or_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed.

        (** *** Equality of the real and simulated distributions

            The simulator gives the dependent challenge to branch 0, while the
            prover gives it to branch [rindex] and adds [cb · x] to that branch's
            response. [or_shift rindex x c] maps prover randomness to the simulator
            randomness that yields the same transcript. With [uscs = us ++ cs] and
            [cb = c - Σ cs], it replaces [us[rindex]] by [us[rindex] + cb · x] and
            inserts [cb] into [cs] at position [rindex]. The head of the result is
            dropped, because the simulator recomputes it from the sum. The map is a
            bijection, with inverse [or_unshift], so it preserves the uniform
            distribution. *)
        Definition or_shift {n : nat} (rindex : Fin.t (2 + n)) (x c : F)
          (uscs : Vector.t F ((2 + n) + (1 + n))) : Vector.t F ((2 + n) + (1 + n)) :=
          let (us, cs) := splitat (2 + n) uscs in
          let cb := c - Vector.fold_right add cs zero in
          Vector.append (replace us rindex (us[@rindex] + cb * x))
            (tl (insert_at (1 + n) cs rindex cb)).

        (** Inverse of [or_shift]. It rebuilds the full challenge vector
            [cm = (c - Σ cs) :: cs], subtracts [cm[rindex] · x] from [us[rindex]],
            and removes position [rindex] from [cm]. *)
        Definition or_unshift {n : nat} (rindex : Fin.t (2 + n)) (x c : F)
          (uscs : Vector.t F ((2 + n) + (1 + n))) : Vector.t F ((2 + n) + (1 + n)) :=
          let (us, cs) := splitat (2 + n) uscs in
          let cm := (c - Vector.fold_right add cs zero) :: cs in
          let cb := cm[@rindex] in
          Vector.append (replace us rindex (us[@rindex] - cb * x))
            (remove_at (1 + n) cm rindex).

        (** Inserting [a] anywhere in a vector adds [a] to its sum. *)
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

        (** The sum of a vector is its [i]-th entry plus the sum of the vector with
            that entry removed. *)
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

        (** After inserting [cb = c - Σ cs] into [cs], the head of the result equals
            [c] minus the sum of its tail. So the simulator, which recomputes the
            head from the tail, rebuilds exactly the vector that [or_shift]
            produced. *)
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
          (* The challenge that or_shift recomputes from remove_at cm rindex is
             exactly cm[rindex], since cm sums to c. *)
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

        (** The simulator written for [S N] branches with a plain [let] instead of a
            proof script. [or_simulator_base_eq] shows that it agrees with
            [generalised_construct_or_conversations_simulator] at [N = 1 + n]; the
            rewriting in [construct_or_shift] works with this form. *)
        Definition or_simulator_base {N : nat} (g : G) (hs : Vector.t G (S N))
          (uscs : Vector.t F (S N + N)) (c : F) : @sigma_proto F G (S N) (S (S N)) (S N) :=
          let (us, cs) := splitat (S N) uscs in
          let cm := (c - Vector.fold_right add cs zero) :: cs in
          let comm := zip_with (fun ui ci => (ui, ci)) us cm in
          let commitment := zip_with (fun hi '(ui, ci) => gop (g^ui) (hi^(opp ci))) hs comm in
          (commitment; c :: cm; us).

        (** The simulator and [or_simulator_base] agree definitionally. *)
        Lemma or_simulator_base_eq {n : nat} (g : G) (hs : Vector.t G (2 + n))
          (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) :
          generalised_construct_or_conversations_simulator g hs uscs c =
          @or_simulator_base (1 + n) g hs uscs c.
        Proof. reflexivity. Qed.

        (** Transporting a transcript along [N = M] transports each of its three
            components. *)
        Lemma rew_sigma_proto : forall (N M : nat) (e : N = M) (a : Vector.t G N)
          (cm : Vector.t F (S N)) (r : Vector.t F N),
          rew [fun k => @sigma_proto F G k (S k) k] e in (a; cm; r) =
          (rew [Vector.t G] e in a; rew [fun k => Vector.t F (S k)] e in cm;
           rew [Vector.t F] e in r).
        Proof. intros N M e a cm r; destruct e; reflexivity. Qed.

        (** Transport along [N = M] commutes with [cons]. *)
        Lemma rew_cons_S {A : Type} :
          forall (N M : nat) (e : N = M) (a : A) (v : Vector.t A N),
          rew [fun k => Vector.t A (S k)] e in (a :: v) = a :: rew [Vector.t A] e in v.
        Proof. intros N M e a v; destruct e; reflexivity. Qed.

        (** The key identity for zero knowledge: if [hs[rindex] = g ^ x], then the
            prover on randomness [uscs] produces exactly the same transcript as the
            simulator on randomness [or_shift rindex x c uscs].

            Proof idea: decompose the index as in the prover, transport everything
            to the split form [m₁ + (1 + m₂)], identify [rindex] with [Fin.R m₁ F1],
            and push [insert_at] and [replace] through [zip_with]. The only
            non-syntactic step is the real branch, where [schnorr_commitment_shift]
            gives [b ^ u = b ^ (u + cb · x) · h ^ (opp cb)]. *)
        Lemma construct_or_shift {n : nat} (rindex : Fin.t (2 + n)) (x : F)
          (g : G) (hs : Vector.t G (2 + n)) (R : hs[@rindex] = g ^ x) :
          forall (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F),
          generalised_construct_or_conversations_schnorr rindex x g hs uscs c =
          generalised_construct_or_conversations_simulator g hs
            (or_shift rindex x c uscs) c.
        Proof.
          intros uscs c.
          rewrite or_simulator_base_eq.
          destruct (splitat (2 + n) uscs) as (us & cs) eqn:hv.
          apply append_splitat in hv; subst uscs.
          unfold generalised_construct_or_conversations_schnorr, or_shift.
          rewrite !VectorSpec.splitat_append.
          (* Decompose the randomness around rindex, as the prover does. *)
          destruct (vector_fin_app_pred (1 + n) rindex us cs) as
            (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa]; destruct pfbb as [pfb]; destruct haa as [ha].
          destruct ha as (ha & hb & hc & hd).
          subst us cs.
          cbn [p] in hb |- *.
          change ((2 + n)%nat) with ((1 + (1 + n))%nat) in *.
          generalize dependent pfa; generalize dependent hs; generalize dependent rindex.
          set (N := (1 + n)%nat) in *.
          clearbody N.
          assert (pfb' : (m₁ + m₂)%nat = N) by (symmetry; exact pfb).
          destruct pfb'.
          (* Eliminate the length equation for the challenge part using UIP on nat. *)
          rewrite (UIP_nat _ _ pfb eq_refl); cbn [eq_rect_r eq_rect eq_sym].
          intros rindex hd hs R pfa hb.
          rewrite !rew_opp_r.
          destruct (splitat m₁ (rew [t G] pfa in hs)) as (hsl & hsrr) eqn:hha.
          apply append_splitat in hha.
          destruct (vector_inv_S hsrr) as (h & hsr & hh); subst hsrr.
          pose proof (f_equal (fun v => rew <- [t G] pfa in v) hha) as hhs.
          cbn beta in hhs.
          rewrite rew_opp_l in hhs.
          rewrite hha.
          subst hs.
          (* rindex is the middle position m₁ of the split statement. *)
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
          unfold or_simulator_base; rewrite VectorSpec.splitat_append; cbv beta iota zeta.
          (* Push the shift through the simulator: insert_at commutes with zip_with,
             and the recomputed head challenge is the original one. *)
          rewrite replace_insert_at, insert_at_eta, !zip_with_insert_at.
          unfold construct_or_conversations_schnorr,
            construct_or_conversations_schnorr_commitment.
          rewrite !VectorSpec.splitat_append; cbn.
          change (rew [λ y : nat, Fin.t y] eq_sym pfa in Fin.R m₁ Fin.F1) with i in *.
          rewrite rew_sigma_proto, rew_cons_S, !rew_app_cons.
          change (rew [Fin.t] eq_sym pfa in Fin.R m₁ Fin.F1) with i.
          rewrite !zip_with_app.
          f_equal; f_equal.
          (* Real branch: the honest commitment equals the simulated commitment
             built from the shifted response. *)
          apply schnorr_commitment_shift; exact R.
        Qed.

        (** Special honest-verifier zero knowledge as equality of distributions.
            Assume [hs[rindex] = g ^ x], and that the sampling list [lf] has no
            duplicates and contains every field element, so that it is the uniform
            distribution on [F]. Then for every challenge [c] the real transcript
            distribution is a permutation of the simulated one: they give every
            transcript the same probability. The simulator does not use [x] or
            [rindex].

            Proof idea: by [construct_or_shift] the prover equals the simulator
            composed with [or_shift]. Since [or_shift] is a bijection on randomness
            vectors ([or_unshift_shift], [or_shift_unshift]), it permutes the
            uniform product distribution ([repeat_uniform_bijection_perm]);
            [bind_ret_perm] combines the two facts. *)
        Theorem generalised_or_special_honest_verifier_zkp_perm {n : nat} (x : F)
          (g : G) (hs : Vector.t G (2 + n)) (rindex : Fin.t (2 + n))
          (R : hs[@rindex] = g ^ x) :
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.NoDup lf -> (forall y : F, List.In y lf) ->
          Permutation
            (generalised_or_schnorr_distribution lf Hlfn rindex x g hs c)
            (generalised_or_simulator_distribution lf Hlfn g hs c).
        Proof.
          intros * hnd hall.
          change (Permutation
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
                ((2 + n) + (1 + n)))
              (fun uscs => Ret (generalised_construct_or_conversations_schnorr
                rindex x g hs uscs c)))
            (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
                ((2 + n) + (1 + n)))
              (fun uscs => Ret (generalised_construct_or_conversations_simulator
                g hs uscs c)))).
          eapply bind_ret_perm with (phi := or_shift rindex x c).
          + apply (repeat_uniform_bijection_perm lf Hlfn _ _
              (or_unshift rindex x c) hnd hall);
            [apply or_unshift_shift | apply or_shift_unshift].
          + intros uscs p _. apply construct_or_shift; exact R.
        Qed.

    End Proofs.
  End Or.
End DL.
