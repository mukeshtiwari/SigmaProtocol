From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos.
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
  LinearRelation.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(*
  Composition of linear-relation sigma protocols by structural
  induction on a statement tree:

      comp_rel ::= Leaf (mat, pub) | CAnd comp_rel comp_rel
                 | COr comp_rel comp_rel

  - Leaf: the generic Maurer protocol of LinearRelation.v.
  - CAnd: both children share the challenge.
  - COr (CDS composition): the transcript stores the left child's
    challenge c₁; the right child's challenge is c - c₁, so the two
    sub-challenges always sum to the top-level challenge.  The prover
    simulates the branch it has no witness for using a
    pre-committed challenge and answers the other branch honestly.

  Witness, transcript, and randomness *types* are computed by
  recursion on the tree (nested products) — no heterogeneous vector
  machinery, and every function and proof proceeds by the same
  structural induction.
*)

(* Generic distribution lemmas, independent of the tree. *)
Section DistrLemmas.

  #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

  Lemma bind_ret_in_generic {A B : Type} :
    ∀ (l : dist A) (f : A -> B) (y : B) (p : prob),
    List.In (y, p) (Bind l (fun x => Ret (f x))) ->
    ∃ (x : A) (q : prob), List.In (x, q) l ∧ y = f x.
  Proof.
    induction l as [|(a, q) l ihl].
    +
      intros * ha; cbn in ha; inversion ha.
    +
      intros * ha; cbn in ha.
      destruct ha as [ha | ha].
      ++
        inversion ha; subst.
        exists a, q.
        split. left; reflexivity. reflexivity.
      ++
        destruct (ihl _ _ _ ha) as (x & qx & hb & hc).
        exists x, qx.
        split. right; exact hb. exact hc.
  Qed.

  Lemma bind_ret_prob_generic {A B : Type} :
    ∀ (l : dist A) (f : A -> B) (y : B) (p : prob) (w : nat),
    (∀ x q, List.In (x, q) l -> q = 1 / w) ->
    List.In (y, p) (Bind l (fun x => Ret (f x))) ->
    p = 1 / w.
  Proof.
    induction l as [|(a, q) l ihl].
    +
      intros * ha hb; cbn in hb; inversion hb.
    +
      intros * ha hb; cbn in hb.
      pose proof (ha a q (or_introl eq_refl)) as hc.
      destruct hb as [hb | hb].
      ++
        inversion hb; subst.
        unfold mul_prob, Prob.one; cbn.
        f_equal. nia.
      ++
        eapply ihl.
        intros x qx hd.
        eapply (ha x qx (or_intror hd)).
        exact hb.
  Qed.

  Lemma bind_in_inv {A B : Type} :
    ∀ (l : dist A) (f : A -> dist B) (y : B) (p : prob),
    List.In (y, p) (Bind l f) ->
    ∃ (x : A) (px py : prob),
      List.In (x, px) l ∧ List.In (y, py) (f x) ∧ p = mul_prob px py.
  Proof.
    induction l as [|(a, q) l ihl].
    +
      intros * ha; cbn in ha; inversion ha.
    +
      intros * ha; cbn in ha.
      eapply List.in_app_or in ha.
      destruct ha as [ha | ha].
      ++
        eapply List.in_map_iff in ha.
        destruct ha as ((b & pb) & hb & hc).
        inversion hb; subst.
        exists a, q, pb.
        repeat split.
        left; reflexivity.
        exact hc.
      ++
        destruct (ihl _ _ _ ha) as (x & px & py & hb & hc & hd).
        exists x, px, py.
        repeat split.
        right; exact hb.
        exact hc.
        exact hd.
  Qed.

  Lemma prob_mul_split : ∀ (w₁ w₂ : nat),
    w₁ <> 0 -> w₂ <> 0 ->
    mul_prob (1 / w₁) (1 / w₂) = 1 / (w₁ * w₂)%nat.
  Proof.
    intros * ha hb.
    unfold mul_prob; cbn.
    rewrite Nat2Pos.inj_mul; try assumption.
    reflexivity.
  Qed.

End DistrLemmas.

Section Composition.

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

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (* The section-closed constants of LinearRelation.v, applied to
     this section's group structure. *)
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow _).
  #[local] Notation mat_evalC :=
    (@mat_eval F G gid gop gpow _ _).
  #[local] Notation verifyC :=
    (@verify_linear_relation_proof F G gid gop gpow Gdec _ _).

  Section Def.

    (* The statement tree *)
    Inductive comp_rel : Type :=
    | Leaf (m n : nat)
        (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) : comp_rel
    | CAnd (rl rr : comp_rel) : comp_rel
    | COr (rl rr : comp_rel) : comp_rel.

    (* Witness type, computed from the tree: an OR witness is a
       witness for one branch. *)
    Fixpoint comp_witness (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (comp_witness rl * comp_witness rr)%type
      | COr rl rr => (comp_witness rl + comp_witness rr)%type
      end.

    (* The relation the composed protocol proves *)
    Fixpoint comp_rel_holds (r : comp_rel) :
      comp_witness r -> Prop :=
      match r with
      | Leaf m n mat pub => fun xs => mat_evalC mat xs = pub
      | CAnd rl rr => fun w =>
          comp_rel_holds rl (fst w) ∧ comp_rel_holds rr (snd w)
      | COr rl rr => fun w =>
          match w with
          | inl wl => comp_rel_holds rl wl
          | inr wr => comp_rel_holds rr wr
          end
      end.

    (* Transcript shape, computed from the tree.  A leaf transcript
       is (announcement, response); its challenge is supplied
       externally.  An OR transcript additionally stores the left
       child's challenge c₁ (the right child's is the difference). *)
    Fixpoint comp_transcript (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => (Vector.t G m * Vector.t F n)%type
      | CAnd rl rr => (comp_transcript rl * comp_transcript rr)%type
      | COr rl rr =>
          (comp_transcript rl * comp_transcript rr * F)%type
      end.

    (* Prover randomness: leaf commitment randomness, plus — at each
       OR node — the challenge used for the simulated branch. *)
    Fixpoint comp_rand (r : comp_rel) : Type :=
      match r with
      | Leaf m n _ _ => Vector.t F n
      | CAnd rl rr => (comp_rand rl * comp_rand rr)%type
      | COr rl rr => (comp_rand rl * comp_rand rr * F)%type
      end.

    (* Number of field elements drawn by the prover / simulator *)
    Fixpoint comp_size (r : comp_rel) : nat :=
      match r with
      | Leaf m n _ _ => n
      | CAnd rl rr => (comp_size rl + comp_size rr)%nat
      | COr rl rr => S (comp_size rl + comp_size rr)
      end.

    (* Simulator: builds an accepting transcript for challenge c
       without any witness. *)
    Fixpoint comp_simulate (r : comp_rel) :
      comp_rand r -> F -> comp_transcript r :=
      match r with
      | Leaf m n mat pub => fun zs c =>
          (zip_with (fun row p => gop (row_evalC row zs) (p ^ (opp c)))
            mat pub, zs)
      | CAnd rl rr => fun s c =>
          (comp_simulate rl (fst s) c, comp_simulate rr (snd s) c)
      | COr rl rr => fun s c =>
          (comp_simulate rl (fst (fst s)) (snd s),
           comp_simulate rr (snd (fst s)) (c - snd s),
           snd s)
      end.

    (* Prover: honest on the branches it has witnesses for,
       simulated (with the pre-committed challenge from the
       randomness) on the others. *)
    Fixpoint comp_prove (r : comp_rel) :
      comp_witness r -> comp_rand r -> F -> comp_transcript r :=
      match r with
      | Leaf m n mat pub => fun xs us c =>
          (mat_evalC mat us,
           zip_with (fun u x => u + c * x) us xs)
      | CAnd rl rr => fun w s c =>
          (comp_prove rl (fst w) (fst s) c,
           comp_prove rr (snd w) (snd s) c)
      | COr rl rr => fun w s c =>
          match w with
          | inl wl =>
              (comp_prove rl wl (fst (fst s)) (c - snd s),
               comp_simulate rr (snd (fst s)) (snd s),
               c - snd s)
          | inr wr =>
              (comp_simulate rl (fst (fst s)) (snd s),
               comp_prove rr wr (snd (fst s)) (c - snd s),
               snd s)
          end
      end.

    (* Verifier: leaf checks are the linear-relation checks; an AND
       passes the same challenge down; an OR verifies the left child
       at the stored challenge c₁ and the right child at c - c₁. *)
    Fixpoint comp_verify (r : comp_rel) :
      F -> comp_transcript r -> bool :=
      match r with
      | Leaf m n mat pub => fun c t =>
          verifyC mat pub (fst t; [c]; snd t)
      | CAnd rl rr => fun c t =>
          comp_verify rl c (fst t) && comp_verify rr c (snd t)
      | COr rl rr => fun c t =>
          comp_verify rl (snd t) (fst (fst t)) &&
          comp_verify rr (c - snd t) (snd (fst t))
      end.

    (* Two transcripts with the same announcements everywhere
       (challenges and responses may differ) — the hypothesis of
       special soundness. *)
    Fixpoint comp_same_announcement (r : comp_rel) :
      comp_transcript r -> comp_transcript r -> Prop :=
      match r with
      | Leaf m n _ _ => fun t t' => fst t = fst t'
      | CAnd rl rr => fun t t' =>
          comp_same_announcement rl (fst t) (fst t') ∧
          comp_same_announcement rr (snd t) (snd t')
      | COr rl rr => fun t t' =>
          comp_same_announcement rl (fst (fst t)) (fst (fst t')) ∧
          comp_same_announcement rr (snd (fst t)) (snd (fst t'))
      end.

    (* Uniform distribution over the prover randomness *)
    Fixpoint comp_rand_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel) :
      dist (comp_rand r) :=
      match r with
      | Leaf m n _ _ =>
          repeat_dist_ntimes_vector
            (uniform_with_replacement lf Hlfn) n
      | CAnd rl rr =>
          sl <- comp_rand_distribution lf Hlfn rl ;;
          sr <- comp_rand_distribution lf Hlfn rr ;;
          Ret (sl, sr)
      | COr rl rr =>
          sl <- comp_rand_distribution lf Hlfn rl ;;
          sr <- comp_rand_distribution lf Hlfn rr ;;
          c₁ <- uniform_with_replacement lf Hlfn ;;
          Ret (sl, sr, c₁)
      end.

    Definition comp_real_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel)
      (w : comp_witness r) (c : F) : dist (comp_transcript r) :=
      s <- comp_rand_distribution lf Hlfn r ;;
      Ret (comp_prove r w s c).

    Definition comp_simulator_distribution
      (lf : list F) (Hlfn : lf <> List.nil) (r : comp_rel)
      (c : F) : dist (comp_transcript r) :=
      s <- comp_rand_distribution lf Hlfn r ;;
      Ret (comp_simulate r s c).

  End Def.

  Section Proofs.

    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (* ------------------ Simulator correctness ------------------ *)

    Theorem comp_simulate_completeness :
      ∀ (r : comp_rel) (s : comp_rand r) (c : F),
      comp_verify r c (comp_simulate r s c) = true.
    Proof.
      induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
      +
        intros *; cbn.
        eapply linear_relation_simulator_completeness.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply ihl. eapply ihr.
      +
        intros *; cbn.
        eapply andb_true_iff; split.
        eapply ihl. eapply ihr.
    Qed.

    (* ------------------ Completeness ------------------ *)

    Theorem comp_completeness :
      ∀ (r : comp_rel) (w : comp_witness r) (s : comp_rand r) (c : F),
      comp_rel_holds r w ->
      comp_verify r c (comp_prove r w s c) = true.
    Proof.
      induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
      +
        intros * ha; cbn.
        eapply linear_relation_completeness.
        rewrite ha; reflexivity.
      +
        intros * ha; cbn in ha |- *.
        destruct ha as (hal & har).
        eapply andb_true_iff; split.
        eapply ihl; exact hal.
        eapply ihr; exact har.
      +
        intros * ha; cbn in ha |- *.
        destruct w as [wl | wr]; cbn.
        ++
          eapply andb_true_iff; split.
          eapply ihl; exact ha.
          assert (hb : c - (c - snd s) = snd s). field.
          rewrite hb.
          eapply comp_simulate_completeness.
        ++
          eapply andb_true_iff; split.
          eapply comp_simulate_completeness.
          eapply ihr; exact ha.
    Qed.

    (* ------------------ Special soundness ------------------ *)

    Theorem comp_special_soundness :
      ∀ (r : comp_rel) (c c' : F)
        (t t' : comp_transcript r),
      c <> c' ->
      comp_same_announcement r t t' ->
      comp_verify r c t = true ->
      comp_verify r c' t' = true ->
      ∃ (w : comp_witness r), comp_rel_holds r w.
    Proof.
      induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
      +
        intros * ha hb hc hd.
        destruct t as (comm & res).
        destruct t' as (comm' & res').
        cbn in hb, hc, hd; subst.
        eapply linear_relation_special_soundness.
        exact ha. exact hc. exact hd.
      +
        intros * ha hb hc hd.
        destruct t as (tl & tr).
        destruct t' as (tl' & tr').
        cbn in hb, hc, hd.
        destruct hb as (hbl & hbr).
        eapply andb_true_iff in hc, hd.
        destruct hc as (hcl & hcr).
        destruct hd as (hdl & hdr).
        destruct (ihl _ _ _ _ ha hbl hcl hdl) as (wl & hwl).
        destruct (ihr _ _ _ _ ha hbr hcr hdr) as (wr & hwr).
        exists (wl, wr); cbn.
        exact (conj hwl hwr).
      +
        intros * ha hb hc hd.
        destruct t as ((tl & tr) & e).
        destruct t' as ((tl' & tr') & e').
        cbn in hb, hc, hd.
        destruct hb as (hbl & hbr).
        eapply andb_true_iff in hc, hd.
        destruct hc as (hcl & hcr).
        destruct hd as (hdl & hdr).
        destruct (Fdec e e') as [he | he].
        ++
          (* left challenges equal, so right challenges differ *)
          subst e'.
          assert (hf : c - e <> c' - e).
          intro hf. eapply ha.
          eapply f_equal with (f := fun x => x + e) in hf.
          assert (hg : ∀ a : F, a - e + e = a). intros; field.
          rewrite !hg in hf. exact hf.
          destruct (ihr _ _ _ _ hf hbr hcr hdr) as (wr & hwr).
          exists (inr wr); cbn.
          exact hwr.
        ++
          (* left challenges differ *)
          destruct (ihl _ _ _ _ he hbl hcl hdl) as (wl & hwl).
          exists (inl wl); cbn.
          exact hwl.
    Qed.

    (* ------------------ SHVZK ------------------ *)

    #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

    Lemma comp_rand_distribution_prob :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (s : comp_rand r) (q : prob),
      List.In (s, q) (comp_rand_distribution lf Hlfn r) ->
      q = 1 / (Nat.pow (List.length lf) (comp_size r)).
    Proof.
      induction r as [m n mat pub | rl ihl rr ihr | rl ihl rr ihr].
      +
        intros * ha; cbn in ha |- *.
        eapply uniform_probability_multidraw_prob.
        exact ha.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (sl & px & py & hb & hc & hd).
        eapply bind_ret_prob_generic in hc.
        2: { intros x qx he. eapply ihr. exact he. }
        specialize (ihl lf Hlfn sl px hb).
        subst.
        rewrite PeanoNat.Nat.pow_add_r.
        eapply prob_mul_split;
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
      +
        intros * ha; cbn in ha |- *.
        assert (hL : List.length lf <> 0%nat).
        destruct lf; [congruence | cbn; lia].
        eapply bind_in_inv in ha.
        destruct ha as (sl & px & py & hb & hc & hd).
        eapply bind_in_inv in hc.
        destruct hc as (sr & px2 & py2 & he & hf & hg).
        eapply bind_ret_prob_generic in hf.
        2: { intros x qx hh. eapply uniform_probability. exact hh. }
        specialize (ihl lf Hlfn sl px hb).
        specialize (ihr lf Hlfn sr px2 he).
        subst.
        assert (h₁ : Nat.pow (List.length lf) (comp_size rl) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
        assert (h₂ : Nat.pow (List.length lf) (comp_size rr) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; exact hL.
        assert (hmul :
          (Nat.pow (List.length lf) (comp_size rr) *
           List.length lf)%nat <> 0%nat). nia.
        rewrite (prob_mul_split _ _ h₂ hL).
        rewrite (prob_mul_split _ _ h₁ hmul).
        f_equal.
        f_equal.
        rewrite PeanoNat.Nat.pow_add_r.
        nia.
    Qed.

    Lemma comp_real_distribution_transcript_generic :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F) (t : comp_transcript r)
        (p : prob),
      comp_rel_holds r w ->
      List.In (t, p) (comp_real_distribution lf Hlfn r w c) ->
      comp_verify r c t = true ∧
      p = 1 / (Nat.pow (List.length lf) (comp_size r)).
    Proof.
      intros * ha hb.
      refine (conj _ _).
      +
        unfold comp_real_distribution in hb.
        eapply bind_ret_in_generic in hb.
        destruct hb as (s & q & hc & hd).
        subst.
        eapply comp_completeness.
        exact ha.
      +
        unfold comp_real_distribution in hb.
        eapply bind_ret_prob_generic in hb.
        exact hb.
        intros s q hc.
        eapply comp_rand_distribution_prob.
        exact hc.
    Qed.

    Lemma comp_simulator_distribution_transcript_generic :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (c : F) (t : comp_transcript r) (p : prob),
      List.In (t, p) (comp_simulator_distribution lf Hlfn r c) ->
      comp_verify r c t = true ∧
      p = 1 / (Nat.pow (List.length lf) (comp_size r)).
    Proof.
      intros * ha.
      refine (conj _ _).
      +
        unfold comp_simulator_distribution in ha.
        eapply bind_ret_in_generic in ha.
        destruct ha as (s & q & hb & hc).
        subst.
        eapply comp_simulate_completeness.
      +
        unfold comp_simulator_distribution in ha.
        eapply bind_ret_prob_generic in ha.
        exact ha.
        intros s q hb.
        eapply comp_rand_distribution_prob.
        exact hb.
    Qed.

    (* Special honest-verifier zero-knowledge for the whole tree:
       real and simulated transcript distributions are identical. *)
    Theorem comp_special_honest_verifier_zkp :
      ∀ (r : comp_rel) (lf : list F) (Hlfn : lf <> List.nil)
        (w : comp_witness r) (c : F),
      comp_rel_holds r w ->
      List.map (fun '(t, p) => (comp_verify r c t, p))
        (comp_real_distribution lf Hlfn r w c) =
      List.map (fun '(t, p) => (comp_verify r c t, p))
        (comp_simulator_distribution lf Hlfn r c).
    Proof.
      intros * ha.
      eapply map_ext_eq.
      +
        unfold comp_real_distribution,
          comp_simulator_distribution.
        repeat rewrite distribution_length.
        reflexivity.
      +
        intros t p hb.
        eapply comp_real_distribution_transcript_generic.
        exact ha. exact hb.
      +
        intros t p hb.
        eapply comp_simulator_distribution_transcript_generic.
        exact hb.
    Qed.

  End Proofs.
End Composition.
