From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool String List.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import
  Util.
From ExtLib.Structures Require Import
  Monad.
From Crypto Require Import
  Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl.
From Utility Require Import Util.

Import VectorNotations.

(*
  Fiat-Shamir transformation of the composed protocol.

  The challenge is derived by hashing the transcript's announcement
  part.  The hash is an abstract parameter (hash : comp_ann_t r -> F);
  an instantiation should follow the *strong* Fiat-Shamir transform
  (Bernhard-Pereira-Warinschi, ePrint 2016/771): the hash input must
  bind the full instance (the statement / matrices / public points),
  which the caller achieves by baking the instance into the hash
  function it passes.

  What is proven here is exactly what is provable without a random
  oracle:
  - the announcement part of an honest transcript does not depend on
    the challenge (prove_ann_independent), which makes the
    transformation well-defined; and
  - NIZK completeness: the honestly generated non-interactive proof
    verifies, for every hash function.

  Soundness and zero-knowledge of the non-interactive protocol hold
  in the random-oracle model by the standard argument on top of
  comp_special_soundness / comp_special_honest_verifier_zkp; the ROM
  step is deliberately not axiomatized here so that the development
  stays free of axioms — it is the single explicitly-stated
  assumption of the final system.
*)
Section Nizk.

  (* Underlying Field of Vector Space *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (* Vector Element *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Notation comp_witnessC :=
    (@comp_witness F G).
  #[local] Notation comp_randC :=
    (@comp_rand F G).
  #[local] Notation comp_transcriptC :=
    (@comp_transcript F G).
  #[local] Notation comp_rel_holdsC :=
    (@comp_rel_holds F G gid gop gpow).
  #[local] Notation comp_proveC :=
    (@comp_prove F add mul sub opp G gid gop gpow).
  #[local] Notation comp_verifyC :=
    (@comp_verify F sub G gid gop gpow Gdec).
  #[local] Notation stmt_denoteC :=
    (@stmt_denote F add mul opp G gid gop gpow).
  #[local] Notation compileC :=
    (@compile F add mul opp G gid ginv gop gpow).
  #[local] Notation compile_stmt_soundC :=
    (@compile_stmt_sound F zero one add mul sub div opp inv
      G gid ginv gop gpow).
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow).
  #[local] Notation verify_fwd :=
    (@verify_linear_relation_forward F G gid gop gpow Gdec).

  Section Def.

    (* The announcement part of a transcript, computed from the
       statement tree.  This is the hash input of the Fiat-Shamir
       transform (the challenges stored at OR nodes and the
       responses are third-move data and are not hashed). *)
    Fixpoint comp_ann_t (r : @comp_rel G) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t G m
      | CAnd rl rr => (comp_ann_t rl * comp_ann_t rr)%type
      | COr rl rr => (comp_ann_t rl * comp_ann_t rr)%type
      end.

    Fixpoint transcript_ann (r : @comp_rel G) :
      comp_transcriptC r -> comp_ann_t r :=
      match r with
      | Leaf _ _ _ _ => fun t => fst t
      | CAnd rl rr => fun t =>
          (transcript_ann rl (fst t), transcript_ann rr (snd t))
      | COr rl rr => fun t =>
          (transcript_ann rl (fst (fst t)),
           transcript_ann rr (snd (fst t)))
      end.

    (* Non-interactive prover: derive the challenge from the
       announcements (which do not depend on it — see
       prove_ann_independent). *)
    Definition nizk_prove (r : @comp_rel G)
      (hash : comp_ann_t r -> F)
      (w : comp_witnessC r) (rnd : comp_randC r) :
      comp_transcriptC r :=
      comp_proveC r w rnd
        (hash (transcript_ann r (comp_proveC r w rnd zero))).

    (* Non-interactive verifier: recompute the challenge from the
       transcript's announcements. *)
    Definition nizk_verify (r : @comp_rel G)
      (hash : comp_ann_t r -> F)
      (t : comp_transcriptC r) : bool :=
      comp_verifyC r (hash (transcript_ann r t)) t.

  End Def.

  Section Proofs.

    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.

    (* The announcement part of an honest transcript does not
       depend on the challenge: real leaf announcements are
       commitments to fresh randomness, and simulated branches use
       the pre-committed challenge from the randomness. *)
    Lemma prove_ann_independent :
      ∀ (r : @comp_rel G) (w : comp_witnessC r)
        (rnd : comp_randC r) (c c' : F),
      transcript_ann r (comp_proveC r w rnd c) =
      transcript_ann r (comp_proveC r w rnd c').
    Proof.
      induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
      +
        intros *; cbn.
        reflexivity.
      +
        intros *; cbn.
        f_equal.
        eapply ihl.
        eapply ihr.
      +
        intros *; cbn.
        destruct w as [wl | wr]; cbn.
        ++
          f_equal.
          eapply ihl.
        ++
          f_equal.
          eapply ihr.
    Qed.

    (* NIZK completeness — unconditional: it holds for every hash
       function, not just a random oracle. *)
    Theorem nizk_completeness :
      ∀ (r : @comp_rel G) (hash : comp_ann_t r -> F)
        (w : comp_witnessC r) (rnd : comp_randC r),
      comp_rel_holdsC r w ->
      nizk_verify r hash (nizk_prove r hash w rnd) = true.
    Proof.
      intros * ha.
      unfold nizk_verify, nizk_prove.
      rewrite (prove_ann_independent r w rnd _ zero).
      eapply comp_completeness.
      exact ha.
    Qed.

    (* End to end: for every well-formed DSL statement the prover
       can witness, the compiled non-interactive protocol produces
       an accepting proof, for every hash function. *)
    Corollary compile_nizk_completeness :
      ∀ {n : nat} (privs : Vector.t string n)
        (genv : string -> G) (penv : string -> F)
        (s : @stmt F) (wenv : string -> F),
      wf_stmt privs s = true ->
      nodupb (Vector.to_list privs) = true ->
      stmt_denoteC genv penv wenv s ->
      ∃ (w : comp_witnessC (compileC privs genv penv s)),
        ∀ (hash : comp_ann_t (compileC privs genv penv s) -> F)
          (rnd : comp_randC (compileC privs genv penv s)),
        nizk_verify _ hash (nizk_prove _ hash w rnd) = true.
    Proof.
      intros * ha hb hc.
      destruct (compile_stmt_soundC privs genv penv s wenv ha hb hc)
        as (w & hw).
      exists w.
      intros *.
      eapply nizk_completeness.
      exact hw.
    Qed.

  End Proofs.

  (* ---------- Compact wire format (Milestone H2) ----------

     The compact encoding stores only responses (and the OR
     sub-challenges), dropping announcements; the verifier
     recomputes each leaf announcement from its challenge and
     response via the simulator formula
       a_i = row_eval mat_i res · pub_i^(-c).
     comp_compact_recover proves this recomputation recovers the
     original announcements of any accepting transcript, so the
     compact form carries the same information as the batchable one
     (the sigma-proofs prove_compact / verify_compact pair). *)
  Section Compact.

    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    Fixpoint compact_t (r : @comp_rel G) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (compact_t rl * compact_t rr)%type
      | COr rl rr => (compact_t rl * compact_t rr * F)%type
      end.

    (* drop announcements *)
    Fixpoint compact_proj (r : @comp_rel G) :
      comp_transcriptC r -> compact_t r :=
      match r with
      | Leaf _ _ _ _ => fun t => snd t
      | CAnd rl rr => fun t =>
          (compact_proj rl (fst t), compact_proj rr (snd t))
      | COr rl rr => fun t =>
          (compact_proj rl (fst (fst t)),
           compact_proj rr (snd (fst t)), snd t)
      end.

    (* recompute announcements from challenge + compact data *)
    Fixpoint compact_fill (r : @comp_rel G) :
      F -> compact_t r -> comp_transcriptC r :=
      match r with
      | Leaf m n mat pub => fun c res =>
          (zip_with (fun row p =>
            gop (row_evalC row res) (gpow p (opp c))) mat pub, res)
      | CAnd rl rr => fun c t =>
          (compact_fill rl c (fst t), compact_fill rr c (snd t))
      | COr rl rr => fun c t =>
          (compact_fill rl (snd t) (fst (fst t)),
           compact_fill rr (sub c (snd t)) (snd (fst t)), snd t)
      end.

    Theorem comp_compact_recover :
      ∀ (r : @comp_rel G) (c : F) (t : comp_transcriptC r),
      comp_verifyC r c t = true ->
      compact_fill r c (compact_proj r t) = t.
    Proof.
      induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
      +
        intros * hv.
        destruct t as (comm & res); cbn.
        f_equal.
        eapply Vector.eq_nth_iff.
        intros i j hij; subst.
        rewrite nth_zip_with.
        pose proof (verify_fwd m n mat pub comm c res hv j) as hf.
        rewrite hf.
        rewrite <-associative.
        rewrite <-(@vector_space_smul_distributive_fadd
          F (@eq F) zero one add mul sub div opp inv
          G (@eq G) gid ginv gop gpow Hvec).
        assert (ha : add c (opp c) = zero). field.
        rewrite ha.
        rewrite (@vector_space_field_zero
          F (@eq F) zero one add mul sub div opp inv
          G (@eq G) gid ginv gop gpow Hvec).
        rewrite right_identity.
        reflexivity.
      +
        intros * hv; cbn in hv |- *.
        eapply andb_true_iff in hv.
        destruct hv as (hvl & hvr).
        rewrite (ihl _ _ hvl), (ihr _ _ hvr).
        destruct t as (tl & tr); reflexivity.
      +
        intros * hv; cbn in hv |- *.
        eapply andb_true_iff in hv.
        destruct hv as (hvl & hvr).
        rewrite (ihl _ _ hvl), (ihr _ _ hvr).
        destruct t as ((tl & tr) & c1); reflexivity.
    Qed.

  End Compact.

End Nizk.
