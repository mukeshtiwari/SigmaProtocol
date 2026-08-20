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
    (@compile F add mul opp G gid gop gpow).
  #[local] Notation compile_stmt_soundC :=
    (@compile_stmt_sound F zero one add mul sub div opp inv
      G gid ginv gop gpow).

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

End Nizk.
