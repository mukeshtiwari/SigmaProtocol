From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos String List.
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
  LinearRelation Composition.

Import VectorNotations.

(*
  The statement DSL and its verified compiler.

  A specification declares an ordered vector of private scalar
  names (privs); public scalars and points are total environments
  (penv : string -> F, genv : string -> G) — the "instance".  A
  statement is a tree of AND/OR over leaves, where a leaf is a list
  of linear equations

      lhs = Π_j  base_j ^ (coeff_j · x_j)

  with lhs and base_j point names, coeff_j a *public* scalar
  expression, and x_j a *private* scalar name.  Note the AST makes
  the linearity discipline structurally unrepresentable: a
  coefficient is a pexpr, which has no private variables, so no
  private·private product can be written.

  The compiler maps a well-formed statement to a comp_rel
  (Composition.v):
  - a leaf becomes one Leaf matrix: column x of the row for an
    equation collects Π base_j^coeff_j over the terms with
    variable x — public scalars fold into the bases;
  - consecutive ANDs of pure leaves are merged into a single Leaf,
    so that shared private variables are bound by a shared witness
    vector (the same merging sigma-compiler performs);
  - OR nodes become COr.

  Main results:
  - compile_leaf_correct: for a leaf, the compiled relation holds
    of the witness vector iff the denotation holds (an iff).
  - compile_stmt_sound: for any well-formed statement, a
    denotation proof yields a witness for the compiled relation.
  - compile_protocol_completeness / compile_protocol_zkp:
    end-to-end corollaries with Composition.v's protocol.
*)

Section Dsl.

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
  #[local] Infix "+" := add.

  (* Section-closed constants from LinearRelation.v/Composition.v,
     applied to this section's structure. *)
  #[local] Notation row_evalC :=
    (@row_eval F G gid gop gpow _).
  #[local] Notation comp_rel_holdsC :=
    (@comp_rel_holds F G gid gop gpow).
  #[local] Notation comp_witnessC :=
    (@comp_witness F G).
  #[local] Notation comp_randC :=
    (@comp_rand F G).
  #[local] Notation comp_proveC :=
    (@comp_prove F add mul sub opp G gid gop gpow).
  #[local] Notation comp_verifyC :=
    (@comp_verify F sub G gid gop gpow Gdec).
  #[local] Notation comp_real_distributionC :=
    (@comp_real_distribution F add mul sub opp G gid gop gpow).
  #[local] Notation comp_simulator_distributionC :=
    (@comp_simulator_distribution F sub opp G gid gop gpow).

  (* ---------------- Syntax ---------------- *)

  (* Public scalar expressions *)
  Inductive pexpr : Type :=
  | PConst (c : F)
  | PVar (x : string)
  | PAdd (a b : pexpr)
  | PMul (a b : pexpr)
  | POpp (a : pexpr).

  (* One term  base ^ (coeff · var)  of a linear equation *)
  Record term : Type := mkterm
    { t_coeff : pexpr;
      t_var : string;
      t_base : string }.

  (* One equation  lhs = Π terms *)
  Record equation : Type := mkeq
    { eq_lhs : string;
      eq_rhs : list term }.

  (* Statement tree *)
  Inductive stmt : Type :=
  | SLeaf (eqs : list equation)
  | SAnd (a b : stmt)
  | SOr (a b : stmt).

  Fixpoint peval (penv : string -> F) (e : pexpr) : F :=
    match e with
    | PConst c => c
    | PVar x => penv x
    | PAdd a b => peval penv a + peval penv b
    | PMul a b => peval penv a * peval penv b
    | POpp a => opp (peval penv a)
    end.

  (* Duplicate check for the private-variable declaration list *)
  Fixpoint nodupb (l : list string) : bool :=
    match l with
    | List.nil => true
    | List.cons x r =>
        negb (List.existsb (String.eqb x) r) && nodupb r
    end.

  Section Spec.

    Context {n : nat}.
    Variable privs : Vector.t string n.  (* private scalar names *)
    Variable genv : string -> G.         (* point environment *)
    Variable penv : string -> F.         (* public scalar environment *)

    (* ---------------- Semantics ---------------- *)

    Definition term_denote (wenv : string -> F) (t : term) : G :=
      (genv (t_base t)) ^ (peval penv (t_coeff t) * wenv (t_var t)).

    Definition eq_denote (wenv : string -> F) (e : equation) : Prop :=
      genv (eq_lhs e) =
      List.fold_right (fun t acc => gop (term_denote wenv t) acc)
        gid (eq_rhs e).

    Fixpoint stmt_denote (wenv : string -> F) (s : stmt) : Prop :=
      match s with
      | SLeaf eqs => List.Forall (eq_denote wenv) eqs
      | SAnd a b => stmt_denote wenv a ∧ stmt_denote wenv b
      | SOr a b => stmt_denote wenv a ∨ stmt_denote wenv b
      end.

    (* ---------------- Well-formedness (typechecker) ---------------- *)

    Definition wf_term (t : term) : bool :=
      List.existsb (String.eqb (t_var t)) (Vector.to_list privs).

    Definition wf_eq (e : equation) : bool :=
      List.forallb wf_term (eq_rhs e).

    Fixpoint wf_stmt (s : stmt) : bool :=
      match s with
      | SLeaf eqs => List.forallb wf_eq eqs
      | SAnd a b => wf_stmt a && wf_stmt b
      | SOr a b => wf_stmt a && wf_stmt b
      end.

    (* ---------------- Compilation ---------------- *)

    (* Column entry of a term at declared variable x: the public
       coefficient folds into the base. *)
    Definition term_col (t : term) (x : string) : G :=
      if String.eqb (t_var t) x
      then (genv (t_base t)) ^ (peval penv (t_coeff t))
      else gid.

    (* The matrix row of a term list: column x collects the product
       of the folded bases of all terms with variable x. *)
    Definition row_of_terms (ts : list term) : Vector.t G n :=
      Vector.map (fun x =>
        List.fold_right (fun t acc => gop (term_col t x) acc) gid ts)
        privs.

    Definition compile_eq_row (e : equation) : Vector.t G n :=
      row_of_terms (eq_rhs e).

    Definition compile_leaf (eqs : list equation) : @comp_rel G :=
      Leaf (List.length eqs) n
        (Vector.map compile_eq_row (Vector.of_list eqs))
        (Vector.map (fun e => genv (eq_lhs e)) (Vector.of_list eqs)).

    (* A statement is "pure" when it is an AND-tree of leaves; those
       merge into a single Leaf so that shared private variables are
       bound by one shared witness vector. *)
    Fixpoint leaves_only (s : stmt) : option (list equation) :=
      match s with
      | SLeaf eqs => Some eqs
      | SAnd a b =>
          match leaves_only a, leaves_only b with
          | Some la, Some lb => Some (List.app la lb)
          | _, _ => None
          end
      | SOr _ _ => None
      end.

    Fixpoint compile (s : stmt) : @comp_rel G :=
      match s with
      | SLeaf eqs => compile_leaf eqs
      | SAnd a b =>
          match leaves_only a, leaves_only b with
          | Some la, Some lb => compile_leaf (List.app la lb)
          | _, _ => CAnd (compile a) (compile b)
          end
      | SOr a b => COr (compile a) (compile b)
      end.

    (* The compiled witness vector of a DSL witness environment *)
    Definition compile_witness (wenv : string -> F) : Vector.t F n :=
      Vector.map wenv privs.

    (* ---------------- Proofs ---------------- *)

    Section Proofs.

      Context
        {Hvec : @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (* row_eval of an all-identity row *)
      Lemma row_eval_map_gid :
        ∀ (m : nat) (sv : Vector.t string m) (ws : Vector.t F m),
        row_evalC (Vector.map (fun _ => gid) sv) ws = gid.
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S sv) as (svh & svt & ha).
          destruct (vector_inv_S ws) as (wsh & wst & hb).
          subst.
          specialize (ihm svt wst).
          unfold row_eval in ihm |- *; cbn.
          rewrite vid_identity, left_identity.
          exact ihm.
      Qed.

      (* row_eval is homomorphic in pointwise products of rows *)
      Lemma row_eval_zip_gop :
        ∀ (m : nat) (r₁ r₂ : Vector.t G m) (ws : Vector.t F m),
        row_evalC (zip_with gop r₁ r₂) ws =
        gop (row_evalC r₁ ws) (row_evalC r₂ ws).
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 r₁), (vector_inv_0 r₂),
            (vector_inv_0 ws).
          unfold row_eval; cbn.
          rewrite left_identity.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S r₁) as (rh₁ & rt₁ & ha).
          destruct (vector_inv_S r₂) as (rh₂ & rt₂ & hb).
          destruct (vector_inv_S ws) as (wh & wt & hc).
          subst.
          specialize (ihm rt₁ rt₂ wt).
          unfold row_eval in ihm |- *; cbn.
          rewrite ihm, smul_distributive_vadd, gop_simp.
          reflexivity.
      Qed.

      (* pointwise gop under map splits into zip_with *)
      Lemma map_pointwise_zip :
        ∀ (A : Type) (m : nat) (v : Vector.t A m) (f g : A -> G),
        Vector.map (fun x => gop (f x) (g x)) v =
        zip_with gop (Vector.map f v) (Vector.map g v).
      Proof.
        induction m as [|m ihm].
        +
          intros *.
          rewrite (vector_inv_0 v).
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S v) as (vh & vt & ha); subst.
          cbn.
          rewrite ihm.
          reflexivity.
      Qed.

      (* A term whose variable does not occur in sv contributes an
         all-identity row. *)
      Lemma term_col_absent :
        ∀ (m : nat) (sv : Vector.t string m) (ws : Vector.t F m)
          (t : term),
        List.existsb (String.eqb (t_var t)) (Vector.to_list sv)
          = false ->
        row_evalC (Vector.map (term_col t) sv) ws = gid.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb).
          destruct (vector_inv_S ws) as (wsh & wst & hc).
          subst; cbn in ha.
          eapply orb_false_iff in ha.
          destruct ha as (hal & har).
          specialize (ihm svt wst t har).
          unfold term_col in ihm |- *.
          unfold row_eval in ihm |- *; cbn.
          rewrite hal.
          rewrite vid_identity, left_identity.
          exact ihm.
      Qed.

      (* One-hot row: a term with a declared variable evaluates to
         its denotation. *)
      Lemma term_col_one_hot :
        ∀ (m : nat) (sv : Vector.t string m) (wenv : string -> F)
          (t : term),
        List.existsb (String.eqb (t_var t)) (Vector.to_list sv)
          = true ->
        nodupb (Vector.to_list sv) = true ->
        row_evalC (Vector.map (term_col t) sv) (Vector.map wenv sv) =
        (genv (t_base t)) ^ (peval penv (t_coeff t) * wenv (t_var t)).
      Proof.
        induction m as [|m ihm].
        +
          intros * ha hb.
          rewrite (vector_inv_0 sv) in ha.
          cbn in ha; congruence.
        +
          intros * ha hb.
          destruct (vector_inv_S sv) as (svh & svt & hc); subst.
          cbn in ha, hb.
          eapply andb_true_iff in hb.
          destruct hb as (hbl & hbr).
          destruct (String.eqb (t_var t) svh) eqn:hd.
          ++
            (* head is the variable *)
            eapply String.eqb_eq in hd.
            assert (he :
              List.existsb (String.eqb (t_var t))
                (Vector.to_list svt) = false).
            rewrite hd.
            eapply negb_true_iff in hbl.
            exact hbl.
            unfold row_eval; cbn.
            unfold term_col at 1.
            rewrite hd, String.eqb_refl.
            pose proof (term_col_absent m svt
              (Vector.map wenv svt) t he) as hf.
            unfold row_eval in hf; cbn in hf.
            rewrite hf, right_identity.
            rewrite smul_associative_fmul.
            reflexivity.
          ++
            (* head is a different variable; the destruct has
               already substituted false into ha *)
            cbn in ha.
            specialize (ihm svt wenv t ha hbr).
            unfold row_eval in ihm |- *; cbn.
            unfold term_col at 1.
            rewrite hd.
            rewrite vid_identity, left_identity.
            exact ihm.
      Qed.

      (* The main per-equation lemma: evaluating the compiled row at
         the compiled witness is the product of term denotations. *)
      Lemma row_of_terms_correct :
        ∀ (ts : list term) (wenv : string -> F),
        List.forallb wf_term ts = true ->
        nodupb (Vector.to_list privs) = true ->
        row_evalC (row_of_terms ts) (compile_witness wenv) =
        List.fold_right (fun t acc => gop (term_denote wenv t) acc)
          gid ts.
      Proof.
        induction ts as [|t ts iht].
        +
          intros * ha hb.
          unfold row_of_terms; cbn.
          eapply row_eval_map_gid.
        +
          intros * ha hb.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          unfold row_of_terms; cbn.
          rewrite map_pointwise_zip.
          rewrite row_eval_zip_gop.
          unfold compile_witness.
          rewrite term_col_one_hot;
          [| exact hal | exact hb].
          unfold row_of_terms in iht.
          unfold compile_witness in iht.
          rewrite iht.
          unfold term_denote.
          reflexivity.
          exact har.
          exact hb.
      Qed.

      (* Leaf-level equivalence: the compiled relation holds of the
         compiled witness iff the denotation holds. *)
      Lemma compile_leaf_correct :
        ∀ (eqs : list equation) (wenv : string -> F),
        List.forallb wf_eq eqs = true ->
        nodupb (Vector.to_list privs) = true ->
        (comp_rel_holdsC (compile_leaf eqs) (compile_witness wenv) <->
         List.Forall (eq_denote wenv) eqs).
      Proof.
        induction eqs as [|e eqs ihe].
        +
          intros * ha hb.
          split; intro hc.
          constructor.
          reflexivity.
        +
          intros * ha hb.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hae & har).
          specialize (ihe wenv har hb).
          split; intro hc.
          ++
            cbn in hc.
            pose proof (f_equal (@Vector.hd G _) hc) as hh;
            cbn in hh.
            pose proof (f_equal (@Vector.tl G _) hc) as ht;
            cbn in ht.
            constructor.
            +++
              unfold eq_denote.
              rewrite <-hh.
              unfold compile_eq_row.
              eapply row_of_terms_correct.
              exact hae. exact hb.
            +++
              eapply ihe.
              exact ht.
          ++
            inversion hc as [| ? ? hde hrest]; subst.
            cbn.
            f_equal.
            +++
              unfold compile_eq_row.
              rewrite row_of_terms_correct;
              [| exact hae | exact hb].
              symmetry.
              exact hde.
            +++
              eapply ihe.
              exact hrest.
      Qed.

      (* Pure AND-subtrees denote the conjunction of their collected
         equations. *)
      Lemma leaves_only_denote :
        ∀ (s : stmt) (eqs : list equation) (wenv : string -> F),
        leaves_only s = Some eqs ->
        (stmt_denote wenv s <-> List.Forall (eq_denote wenv) eqs).
      Proof.
        induction s as [leqs | a iha b ihb | a iha b ihb].
        +
          intros * ha; cbn in ha.
          injection ha as ha; subst.
          cbn; reflexivity.
        +
          intros * ha; cbn in ha.
          destruct (leaves_only a) as [la|] eqn:hb;
          [| congruence].
          destruct (leaves_only b) as [lb|] eqn:hc;
          [| congruence].
          injection ha as ha; subst.
          cbn.
          rewrite (iha la wenv eq_refl), (ihb lb wenv eq_refl).
          rewrite List.Forall_app.
          reflexivity.
        +
          intros * ha; cbn in ha; congruence.
      Qed.

      Lemma leaves_only_wf :
        ∀ (s : stmt) (eqs : list equation),
        leaves_only s = Some eqs ->
        wf_stmt s = true ->
        List.forallb wf_eq eqs = true.
      Proof.
        induction s as [leqs | a iha b ihb | a iha b ihb].
        +
          intros * ha hb; cbn in ha, hb.
          injection ha as ha; subst.
          exact hb.
        +
          intros * ha hb; cbn in ha, hb.
          eapply andb_true_iff in hb.
          destruct hb as (hbl & hbr).
          destruct (leaves_only a) as [la|] eqn:hc;
          [| congruence].
          destruct (leaves_only b) as [lb|] eqn:hd;
          [| congruence].
          injection ha as ha; subst.
          rewrite List.forallb_app.
          eapply andb_true_iff; split.
          eapply iha; [reflexivity | exact hbl].
          eapply ihb; [reflexivity | exact hbr].
        +
          intros * ha; cbn in ha; congruence.
      Qed.

      (* Main theorem (completeness direction): a denotation proof
         yields a witness for the compiled relation. *)
      Theorem compile_stmt_sound :
        ∀ (s : stmt) (wenv : string -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC (compile s)),
          comp_rel_holdsC (compile s) w.
      Proof.
        induction s as [leqs | a iha b ihb | a iha b ihb].
        +
          intros * ha hb hc; cbn in *.
          exists (compile_witness wenv).
          eapply compile_leaf_correct.
          exact ha. exact hb. exact hc.
        +
          intros * ha hb hc.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          destruct hc as (hcl & hcr).
          cbn.
          destruct (leaves_only a) as [la|] eqn:hd;
          destruct (leaves_only b) as [lb|] eqn:he.
          ++
            (* both pure: merged leaf *)
            exists (compile_witness wenv).
            eapply compile_leaf_correct.
            rewrite List.forallb_app.
            eapply andb_true_iff; split.
            eapply leaves_only_wf; [exact hd | exact hal].
            eapply leaves_only_wf; [exact he | exact har].
            exact hb.
            eapply List.Forall_app; split.
            eapply (leaves_only_denote a la wenv hd); exact hcl.
            eapply (leaves_only_denote b lb wenv he); exact hcr.
          ++
            destruct (iha wenv hal hb hcl) as (wa & hwa).
            destruct (ihb wenv har hb hcr) as (wb & hwb).
            exists (wa, wb); cbn.
            exact (conj hwa hwb).
          ++
            destruct (iha wenv hal hb hcl) as (wa & hwa).
            destruct (ihb wenv har hb hcr) as (wb & hwb).
            exists (wa, wb); cbn.
            exact (conj hwa hwb).
          ++
            destruct (iha wenv hal hb hcl) as (wa & hwa).
            destruct (ihb wenv har hb hcr) as (wb & hwb).
            exists (wa, wb); cbn.
            exact (conj hwa hwb).
        +
          intros * ha hb hc.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          cbn in hc |- *.
          destruct hc as [hc | hc].
          ++
            destruct (iha wenv hal hb hc) as (wa & hwa).
            exists (inl wa); cbn.
            exact hwa.
          ++
            destruct (ihb wenv har hb hc) as (wb & hwb).
            exists (inr wb); cbn.
            exact hwb.
      Qed.

      (* ---------------- End-to-end corollaries ---------------- *)

      (* For every well-formed statement whose denotation the prover
         can witness, the compiled protocol produces accepting
         transcripts for every challenge. *)
      Corollary compile_protocol_completeness :
        ∀ (s : stmt) (wenv : string -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC (compile s)),
          ∀ (rnd : comp_randC (compile s)) (c : F),
          comp_verifyC (compile s) c
            (comp_proveC (compile s) w rnd c) = true.
      Proof.
        intros * ha hb hc.
        destruct (compile_stmt_sound s wenv ha hb hc) as (w & hw).
        exists w.
        intros *.
        eapply comp_completeness.
        exact hw.
      Qed.

      (* The compiled protocol is zero-knowledge: real and simulated
         transcript distributions coincide. *)
      Corollary compile_protocol_zkp :
        ∀ (s : stmt) (wenv : string -> F) (lf : list F)
          (Hlfn : lf <> List.nil) (c : F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        stmt_denote wenv s ->
        ∃ (w : comp_witnessC (compile s)),
          List.map (fun '(t, p) => (comp_verifyC (compile s) c t, p))
            (comp_real_distributionC lf Hlfn (compile s) w c) =
          List.map (fun '(t, p) => (comp_verifyC (compile s) c t, p))
            (comp_simulator_distributionC lf Hlfn (compile s) c).
      Proof.
        intros * ha hb hc.
        destruct (compile_stmt_sound s wenv ha hb hc) as (w & hw).
        exists w.
        eapply comp_special_honest_verifier_zkp.
        exact hw.
      Qed.

    End Proofs.

  End Spec.

  (* ---------------- Example: Schnorr ---------------- *)

  Section SchnorrExample.

    #[local] Open Scope string_scope.

    (* One private scalar x; the statement  H = G^x  *)
    Definition schnorr_privs : Vector.t string 1 := ["x"].

    Definition schnorr_stmt : stmt :=
      SLeaf (List.cons
        (mkeq "H" (List.cons (mkterm (PConst one) "x" "G") List.nil))
        List.nil).

    (* The typechecker runs by computation. *)
    Example schnorr_wf :
      wf_stmt schnorr_privs schnorr_stmt = true := eq_refl.

    Example schnorr_nodup :
      nodupb (Vector.to_list schnorr_privs) = true := eq_refl.

    (* The denotation is the Schnorr relation (up to the unit
       coefficient and the trailing identity of the fold). *)
    Example schnorr_denote :
      ∀ (genv : string -> G) (penv : string -> F)
        (wenv : string -> F),
      stmt_denote genv penv wenv schnorr_stmt <->
      genv "H" = gop ((genv "G") ^ (one * wenv "x")) gid.
    Proof.
      intros *; cbn; split.
      +
        intro ha.
        inversion ha as [| ? ? hb hc]; subst.
        exact hb.
      +
        intro ha.
        constructor.
        exact ha.
        constructor.
    Qed.

  End SchnorrExample.

End Dsl.
