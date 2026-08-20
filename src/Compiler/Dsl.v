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

(* Generic k-combinations of a list, used for the THRESH
   construction: THRESH(t, l) is the OR over all t-element
   subsequences of l of the AND of the subsequence. *)
Section Combinations.

  Context {A : Type}.

  Fixpoint combs (k : nat) (l : list A) : list (list A) :=
    match k with
    | 0 => List.cons List.nil List.nil
    | S k' =>
        match l with
        | List.nil => List.nil
        | List.cons x xs =>
            List.app (List.map (List.cons x) (combs k' xs))
              (combs (S k') xs)
        end
    end.

  Inductive subseq : list A -> list A -> Prop :=
  | sub_nil : ∀ l, subseq List.nil l
  | sub_take : ∀ x l₁ l₂,
      subseq l₁ l₂ -> subseq (List.cons x l₁) (List.cons x l₂)
  | sub_skip : ∀ x l₁ l₂,
      subseq l₁ l₂ -> subseq l₁ (List.cons x l₂).

  Lemma combs_sound :
    ∀ (l : list A) (k : nat) (c : list A),
    List.In c (combs k l) ->
    subseq c l ∧ List.length c = k.
  Proof.
    induction l as [|x xs ihl].
    +
      intros [|k'] c ha; cbn in ha.
      ++
        destruct ha as [ha | ha]; [| destruct ha].
        subst; split; [constructor | reflexivity].
      ++
        destruct ha.
    +
      intros [|k'] c ha; cbn in ha.
      ++
        destruct ha as [ha | ha]; [| destruct ha].
        subst; split; [constructor | reflexivity].
      ++
        eapply List.in_app_or in ha.
        destruct ha as [ha | ha].
        +++
          eapply List.in_map_iff in ha.
          destruct ha as (c' & hb & hc); subst.
          destruct (ihl k' c' hc) as (hd & he).
          split.
          eapply sub_take; exact hd.
          cbn; rewrite he; reflexivity.
        +++
          destruct (ihl (S k') c ha) as (hb & hc).
          split.
          eapply sub_skip; exact hb.
          exact hc.
  Qed.

  Lemma combs_complete :
    ∀ (c l : list A),
    subseq c l ->
    List.In c (combs (List.length c) l).
  Proof.
    intros * ha.
    induction ha as [l | x l₁ l₂ hsub ih | x l₁ l₂ hsub ih].
    +
      destruct l as [|x xs]; cbn; left; reflexivity.
    +
      cbn.
      eapply List.in_or_app; left.
      eapply List.in_map; exact ih.
    +
      destruct l₁ as [|y l₁'].
      ++
        cbn; left; reflexivity.
      ++
        cbn.
        eapply List.in_or_app; right.
        exact ih.
  Qed.

  Lemma combs_nonempty :
    ∀ (l : list A) (k : nat),
    (k <= List.length l)%nat ->
    combs k l <> List.nil.
  Proof.
    induction l as [|x xs ihl].
    +
      intros [|k'] ha; cbn.
      ++
        discriminate.
      ++
        cbn in ha; lia.
    +
      intros [|k'] ha; cbn.
      ++
        discriminate.
      ++
        intro hb.
        eapply List.app_eq_nil in hb.
        destruct hb as (hbl & hbr).
        eapply List.map_eq_nil in hbl.
        revert hbl.
        eapply (ihl k').
        cbn in ha; lia.
  Qed.

End Combinations.

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
  #[local] Notation comp_transcriptC :=
    (@comp_transcript F G).
  #[local] Notation comp_same_announcementC :=
    (@comp_same_announcement F G).

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

  (* ---------------- Renaming (for the Pedersen repair) ------------ *)

  Definition override (w : string -> F) (x : string) (v : F) :
    string -> F :=
    fun y => if String.eqb x y then v else w y.

  Definition rename_term (x x' : string) (t : term) : term :=
    mkterm (t_coeff t)
      (if String.eqb (t_var t) x then x' else t_var t)
      (t_base t).

  Definition rename_eq (x x' : string) (e : equation) : equation :=
    mkeq (eq_lhs e) (List.map (rename_term x x') (eq_rhs e)).

  Fixpoint rename_stmt (x x' : string) (s : stmt) : stmt :=
    match s with
    | SLeaf eqs => SLeaf (List.map (rename_eq x x') eqs)
    | SAnd a b => SAnd (rename_stmt x x' a) (rename_stmt x x' b)
    | SOr a b => SOr (rename_stmt x x' a) (rename_stmt x x' b)
    end.

  (* The Pedersen commitment equation  C = A^v · B^w  *)
  Definition commit_eq (Cn An Bn v w : string) : equation :=
    mkeq Cn (List.cons (mkterm (PConst one) v An)
      (List.cons (mkterm (PConst one) w Bn) List.nil)).

  (* The repaired form of  AND(C = A^x·B^r, OR(sa, sb))  when the
     private x is shared between the OR branches: rename x per
     branch and bind each copy to the same commitment C. *)
  Definition repair_or (sa sb : stmt)
    (Cn An Bn x r x₁ r₁ x₂ r₂ : string) : stmt :=
    SAnd (SLeaf (List.cons (commit_eq Cn An Bn x r) List.nil))
      (SOr
        (SAnd (rename_stmt x x₁ sa)
          (SLeaf (List.cons (commit_eq Cn An Bn x₁ r₁) List.nil)))
        (SAnd (rename_stmt x x₂ sb)
          (SLeaf (List.cons (commit_eq Cn An Bn x₂ r₂) List.nil)))).

  (* ---------------- THRESH by monotone expansion ------------------ *)

  Definition big_and (l : list stmt) : stmt :=
    List.fold_right SAnd (SLeaf List.nil) l.

  Definition big_or (s : stmt) (l : list stmt) : stmt :=
    List.fold_right SOr s l.

  (* THRESH(t, l): at least t of the statements in l hold.  Encoded
     as the OR over all t-element subsequences of l of their AND.
     Proof size is C(|l|, t); the Shamir-based challenge-sharing
     encoding is the future optimization (see Lagrange.v). *)
  Definition thresh_stmt (t : nat) (l : list stmt) : stmt :=
    match List.map big_and (combs t l) with
    | List.nil => SLeaf List.nil
    | List.cons s₀ rest => big_or s₀ rest
    end.

  (* All private-variable occurrences of a statement *)
  Fixpoint stmt_vars (s : stmt) : list string :=
    match s with
    | SLeaf eqs =>
        List.flat_map (fun e => List.map t_var (eq_rhs e)) eqs
    | SAnd a b => List.app (stmt_vars a) (stmt_vars b)
    | SOr a b => List.app (stmt_vars a) (stmt_vars b)
    end.

  (* ---------------- Automated Pedersen repair ---------------- *)

  (* Generated names: the commitment point, the root commitment
     randomness, and the per-branch copy / randomness for each
     repaired variable.  The '#' marker keeps generated names out of
     the user's namespace; freshness is *validated* by the boolean
     checkers below rather than proven about the generator
     (validated-compilation style). *)
  Definition c_name (x : string) : string := String.append x "#C".
  Definition r_name (x : string) : string := String.append x "#r".
  Definition l_name (x : string) : string := String.append x "#1".
  Definition lr_name (x : string) : string := String.append x "#1r".
  Definition rn_name (x : string) : string := String.append x "#2".
  Definition rr_name (x : string) : string := String.append x "#2r".

  Fixpoint dedup (l : list string) : list string :=
    match l with
    | List.nil => List.nil
    | List.cons x r =>
        if List.existsb (String.eqb x) r then dedup r
        else List.cons x (dedup r)
    end.

  (* The disjunction-invariant violations of SAnd sc (SOr sa sb):
     root variables that also occur in a disjunction branch. *)
  Definition shared_vars (sc sa sb : stmt) : list string :=
    dedup (List.filter
      (fun x => List.existsb (String.eqb x)
        (List.app (stmt_vars sa) (stmt_vars sb)))
      (stmt_vars sc)).

  Definition rename_list (ps : list (string * string)) (s : stmt) :
    stmt :=
    List.fold_right (fun p acc => rename_stmt (fst p) (snd p) acc)
      s ps.

  (* Each original differs from all later originals and copies —
     what the sequential-renaming semantics needs. *)
  Fixpoint pairs_ok (ps : list (string * string)) : bool :=
    match ps with
    | List.nil => true
    | List.cons (x, _) ps' =>
        List.forallb (fun p =>
          negb (String.eqb x (fst p)) &&
          negb (String.eqb x (snd p))) ps'
        && pairs_ok ps'
    end.

  Definition left_pairs (xs : list string) :
    list (string * string) :=
    List.map (fun x => (x, l_name x)) xs.
  Definition right_pairs (xs : list string) :
    list (string * string) :=
    List.map (fun x => (x, rn_name x)) xs.

  Definition root_commits (An Bn : string) (xs : list string) :
    list equation :=
    List.map (fun x => commit_eq (c_name x) An Bn x (r_name x)) xs.
  Definition left_binds (An Bn : string) (xs : list string) :
    list equation :=
    List.map (fun x =>
      commit_eq (c_name x) An Bn (l_name x) (lr_name x)) xs.
  Definition right_binds (An Bn : string) (xs : list string) :
    list equation :=
    List.map (fun x =>
      commit_eq (c_name x) An Bn (rn_name x) (rr_name x)) xs.

  (* The repaired form: the root keeps sc and gains one Pedersen
     commitment per shared variable (in the same, mergeable,
     AND-branch, so the compiled root witness binds them to sc's
     variables); each OR branch has the shared variables renamed to
     fresh copies, each bound to the same commitment. *)
  Definition repair_with (An Bn : string) (xs : list string)
    (sc sa sb : stmt) : stmt :=
    match xs with
    | List.nil => SAnd sc (SOr sa sb)
    | _ =>
      SAnd (SAnd sc (SLeaf (root_commits An Bn xs)))
        (SOr
          (SAnd (rename_list (left_pairs xs) sa)
            (SLeaf (left_binds An Bn xs)))
          (SAnd (rename_list (right_pairs xs) sb)
            (SLeaf (right_binds An Bn xs))))
    end.

  (* The automated pass. *)
  Definition auto_repair (An Bn : string) (sc sa sb : stmt) : stmt :=
    repair_with An Bn (shared_vars sc sa sb) sc sa sb.

  (* First variable whose renamed copy carries a different value —
     the constructive pivot of the soundness dichotomy. *)
  Fixpoint find_unequal (wenv : string -> F) (f : string -> string)
    (xs : list string) : option string :=
    match xs with
    | List.nil => None
    | List.cons x r =>
        match Fdec (wenv x) (wenv (f x)) with
        | left _ => find_unequal wenv f r
        | right _ => Some x
        end
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

    (* ---------------- Disjunction invariant ---------------- *)

    Definition disjointb (l₁ l₂ : list string) : bool :=
      List.forallb
        (fun x => negb (List.existsb (String.eqb x) l₂)) l₁.

    (* Is the statement a pure AND-tree of leaves (compiled to a
       single merged Leaf)? *)
    Definition pureb (s : stmt) : bool :=
      match leaves_only s with
      | Some _ => true
      | None => false
      end.

    (*
      The disjunction-invariant checker.  A private variable shared
      between two subtrees is only bound to a single value when both
      subtrees compile into the same merged Leaf (one shared witness
      vector).  Whenever compilation keeps a CAnd node — i.e. at
      least one side contains an OR — the two sides have independent
      witnesses, so the checker requires their variable sets to be
      disjoint.  (sigma-compiler instead *repairs* violations with
      Pedersen commitments; that transformation is future work, and
      this checker is the precise acceptance condition it must
      re-establish.)
    *)
    Fixpoint disj_inv (s : stmt) : bool :=
      match s with
      | SLeaf _ => true
      | SAnd a b =>
          (pureb a && pureb b) ||
          (disjointb (stmt_vars a) (stmt_vars b) &&
           disj_inv a && disj_inv b)
      | SOr a b => disj_inv a && disj_inv b
      end.

    (* First-match lookup: reconstruct a witness environment from a
       compiled witness vector. *)
    Fixpoint lookup (names : list string) (vals : list F)
      (x : string) : F :=
      match names, vals with
      | List.cons nm names', List.cons v vals' =>
          if String.eqb nm x then v else lookup names' vals' x
      | _, _ => zero
      end.

    (* Merge two branch environments: variables of the left branch
       read from w₁, all others from w₂. *)
    Definition combine_env (va : list string)
      (w₁ w₂ : string -> F) : string -> F :=
      fun x =>
        if List.existsb (String.eqb x) va then w₁ x else w₂ x.

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

      (* ---------------- Phase 4: soundness reflection ------------ *)

      Lemma in_vars_existsb :
        ∀ (l : list string) (x : string),
        List.In x l ->
        List.existsb (String.eqb x) l = true.
      Proof.
        intros * ha.
        eapply List.existsb_exists.
        exists x.
        split. exact ha. eapply String.eqb_refl.
      Qed.

      Lemma disjointb_existsb :
        ∀ (l₁ l₂ : list string) (x : string),
        disjointb l₁ l₂ = true ->
        List.In x l₂ ->
        List.existsb (String.eqb x) l₁ = false.
      Proof.
        intros * ha hb.
        destruct (List.existsb (String.eqb x) l₁) eqn:hc;
        [| reflexivity].
        eapply List.existsb_exists in hc.
        destruct hc as (y & hy & hxy).
        eapply String.eqb_eq in hxy; subst.
        unfold disjointb in ha.
        pose proof (proj1 (List.forallb_forall _ _) ha y hy) as hd.
        eapply negb_true_iff in hd.
        pose proof (in_vars_existsb _ _ hb) as he.
        congruence.
      Qed.

      Lemma lookup_skip :
        ∀ (m : nat) (sv : Vector.t string m) (names : list string)
          (vals : list F) (nm : string) (v : F),
        List.existsb (String.eqb nm) (Vector.to_list sv) = false ->
        Vector.map
          (fun x => if String.eqb nm x then v else lookup names vals x)
          sv =
        Vector.map (lookup names vals) sv.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb); subst.
          cbn in ha.
          eapply orb_false_iff in ha.
          destruct ha as (hal & har).
          cbn.
          rewrite hal.
          f_equal.
          eapply ihm.
          exact har.
      Qed.

      (* Round trip: mapping the reconstructed environment over the
         declarations recovers the witness vector. *)
      Lemma map_lookup_gen :
        ∀ (m : nat) (sv : Vector.t string m) (ws : Vector.t F m),
        nodupb (Vector.to_list sv) = true ->
        Vector.map (lookup (Vector.to_list sv) (Vector.to_list ws)) sv
          = ws.
      Proof.
        induction m as [|m ihm].
        +
          intros * ha.
          rewrite (vector_inv_0 sv), (vector_inv_0 ws).
          reflexivity.
        +
          intros * ha.
          destruct (vector_inv_S sv) as (svh & svt & hb).
          destruct (vector_inv_S ws) as (wh & wt & hc).
          subst.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          eapply negb_true_iff in hal.
          cbn.
          rewrite String.eqb_refl.
          f_equal.
          rewrite lookup_skip.
          eapply ihm.
          exact har.
          exact hal.
      Qed.

      (* Frame lemmas: denotations depend only on the values of the
         variables occurring in the statement. *)
      Lemma term_fold_ext :
        ∀ (ts : list term) (w₁ w₂ : string -> F),
        (∀ x, List.In x (List.map t_var ts) -> w₁ x = w₂ x) ->
        List.fold_right (fun t acc => gop (term_denote w₁ t) acc)
          gid ts =
        List.fold_right (fun t acc => gop (term_denote w₂ t) acc)
          gid ts.
      Proof.
        induction ts as [|t ts iht].
        +
          intros; reflexivity.
        +
          intros * ha.
          cbn.
          f_equal.
          ++
            unfold term_denote.
            rewrite (ha (t_var t) (or_introl eq_refl)).
            reflexivity.
          ++
            eapply iht.
            intros x hx.
            eapply ha.
            right; exact hx.
      Qed.

      Lemma eq_denote_ext :
        ∀ (e : equation) (w₁ w₂ : string -> F),
        (∀ x, List.In x (List.map t_var (eq_rhs e)) -> w₁ x = w₂ x) ->
        eq_denote w₁ e -> eq_denote w₂ e.
      Proof.
        intros * ha hb.
        unfold eq_denote in hb |- *.
        rewrite <-(term_fold_ext (eq_rhs e) w₁ w₂ ha).
        exact hb.
      Qed.

      Lemma eqs_denote_ext :
        ∀ (eqs : list equation) (w₁ w₂ : string -> F),
        (∀ x, List.In x (List.flat_map
          (fun e => List.map t_var (eq_rhs e)) eqs) -> w₁ x = w₂ x) ->
        List.Forall (eq_denote w₁) eqs ->
        List.Forall (eq_denote w₂) eqs.
      Proof.
        induction eqs as [|e eqs ihe].
        +
          intros; constructor.
        +
          intros * ha hb.
          inversion hb as [| ? ? hbe hbr]; subst.
          constructor.
          ++
            eapply eq_denote_ext; [| exact hbe].
            intros x hx.
            eapply ha; cbn.
            eapply List.in_or_app.
            left; exact hx.
          ++
            eapply ihe; [| exact hbr].
            intros x hx.
            eapply ha; cbn.
            eapply List.in_or_app.
            right; exact hx.
      Qed.

      Lemma stmt_denote_ext :
        ∀ (s : stmt) (w₁ w₂ : string -> F),
        (∀ x, List.In x (stmt_vars s) -> w₁ x = w₂ x) ->
        stmt_denote w₁ s -> stmt_denote w₂ s.
      Proof.
        induction s as [eqs | a iha b ihb | a iha b ihb].
        +
          intros * ha hb; cbn in *.
          eapply eqs_denote_ext; [exact ha | exact hb].
        +
          intros * ha hb; cbn in *.
          destruct hb as (hbl & hbr).
          split.
          ++
            eapply iha; [| exact hbl].
            intros x hx.
            eapply ha, List.in_or_app.
            left; exact hx.
          ++
            eapply ihb; [| exact hbr].
            intros x hx.
            eapply ha, List.in_or_app.
            right; exact hx.
        +
          intros * ha hb; cbn in *.
          destruct hb as [hb | hb].
          ++
            left.
            eapply iha; [| exact hb].
            intros x hx.
            eapply ha, List.in_or_app.
            left; exact hx.
          ++
            right.
            eapply ihb; [| exact hb].
            intros x hx.
            eapply ha, List.in_or_app.
            right; exact hx.
      Qed.

      (* Main theorem (soundness reflection): under the disjunction
         invariant, a witness for the compiled relation yields a DSL
         witness environment satisfying the denotation. *)
      Theorem compile_stmt_reflect :
        ∀ (s : stmt),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        ∀ (w : comp_witnessC (compile s)),
        comp_rel_holdsC (compile s) w ->
        ∃ (wenv : string -> F), stmt_denote wenv s.
      Proof.
        induction s as [eqs | a iha b ihb | a iha b ihb].
        +
          (* SLeaf *)
          intros ha hb hinv w hw.
          cbn in w, hw.
          exists (lookup (Vector.to_list privs) (Vector.to_list w)).
          cbn.
          eapply compile_leaf_correct.
          exact ha.
          exact hb.
          unfold compile_witness.
          rewrite map_lookup_gen.
          exact hw.
          exact hb.
        +
          (* SAnd *)
          intros ha hb hinv.
          cbn in ha.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          cbn.
          destruct (leaves_only a) as [la|] eqn:hd;
          destruct (leaves_only b) as [lb|] eqn:he.
          ++
            (* both pure: one merged Leaf, shared witness vector *)
            intros w hw.
            assert (hwf : List.forallb wf_eq (List.app la lb) = true).
            rewrite List.forallb_app.
            eapply andb_true_iff; split.
            eapply leaves_only_wf; [exact hd | exact hal].
            eapply leaves_only_wf; [exact he | exact har].
            exists (lookup (Vector.to_list privs) (Vector.to_list w)).
            assert (hf : List.Forall
              (eq_denote (lookup (Vector.to_list privs)
                (Vector.to_list w))) (List.app la lb)).
            eapply compile_leaf_correct.
            exact hwf.
            exact hb.
            unfold compile_witness.
            rewrite map_lookup_gen.
            exact hw.
            exact hb.
            eapply List.Forall_app in hf.
            destruct hf as (hfl & hfr).
            cbn; split.
            eapply (leaves_only_denote a la _ hd); exact hfl.
            eapply (leaves_only_denote b lb _ he); exact hfr.
          ++
            (* unmerged: independent witnesses, disjointness *)
            cbn in hinv.
            unfold pureb in hinv.
            rewrite hd, he in hinv.
            cbn in hinv.
            eapply andb_true_iff in hinv.
            destruct hinv as (hinvl & hinvb).
            eapply andb_true_iff in hinvl.
            destruct hinvl as (hdisj & hinva).
            intros w hw.
            destruct w as (wa & wb).
            cbn in hw.
            destruct hw as (hwa & hwb).
            destruct (iha hal hb hinva wa hwa) as (wea & hwea).
            destruct (ihb har hb hinvb wb hwb) as (web & hweb).
            exists (combine_env (stmt_vars a) wea web).
            cbn; split.
            eapply stmt_denote_ext; [| exact hwea].
            intros x hx.
            unfold combine_env.
            rewrite (in_vars_existsb _ _ hx).
            reflexivity.
            eapply stmt_denote_ext; [| exact hweb].
            intros x hx.
            unfold combine_env.
            rewrite (disjointb_existsb _ _ _ hdisj hx).
            reflexivity.
          ++
            cbn in hinv.
            unfold pureb in hinv.
            rewrite hd, he in hinv.
            cbn in hinv.
            eapply andb_true_iff in hinv.
            destruct hinv as (hinvl & hinvb).
            eapply andb_true_iff in hinvl.
            destruct hinvl as (hdisj & hinva).
            intros w hw.
            destruct w as (wa & wb).
            cbn in hw.
            destruct hw as (hwa & hwb).
            destruct (iha hal hb hinva wa hwa) as (wea & hwea).
            destruct (ihb har hb hinvb wb hwb) as (web & hweb).
            exists (combine_env (stmt_vars a) wea web).
            cbn; split.
            eapply stmt_denote_ext; [| exact hwea].
            intros x hx.
            unfold combine_env.
            rewrite (in_vars_existsb _ _ hx).
            reflexivity.
            eapply stmt_denote_ext; [| exact hweb].
            intros x hx.
            unfold combine_env.
            rewrite (disjointb_existsb _ _ _ hdisj hx).
            reflexivity.
          ++
            cbn in hinv.
            unfold pureb in hinv.
            rewrite hd, he in hinv.
            cbn in hinv.
            eapply andb_true_iff in hinv.
            destruct hinv as (hinvl & hinvb).
            eapply andb_true_iff in hinvl.
            destruct hinvl as (hdisj & hinva).
            intros w hw.
            destruct w as (wa & wb).
            cbn in hw.
            destruct hw as (hwa & hwb).
            destruct (iha hal hb hinva wa hwa) as (wea & hwea).
            destruct (ihb har hb hinvb wb hwb) as (web & hweb).
            exists (combine_env (stmt_vars a) wea web).
            cbn; split.
            eapply stmt_denote_ext; [| exact hwea].
            intros x hx.
            unfold combine_env.
            rewrite (in_vars_existsb _ _ hx).
            reflexivity.
            eapply stmt_denote_ext; [| exact hweb].
            intros x hx.
            unfold combine_env.
            rewrite (disjointb_existsb _ _ _ hdisj hx).
            reflexivity.
        +
          (* SOr *)
          intros ha hb hinv.
          cbn in ha, hinv.
          eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          eapply andb_true_iff in hinv.
          destruct hinv as (hinva & hinvb).
          cbn.
          intros w hw.
          destruct w as [wa | wb].
          ++
            destruct (iha hal hb hinva wa hw) as (wea & hwea).
            exists wea.
            left; exact hwea.
          ++
            destruct (ihb har hb hinvb wb hw) as (web & hweb).
            exists web.
            right; exact hweb.
      Qed.

      (* DSL-level special soundness: two accepting transcripts with
         the same announcements and different challenges imply the
         *statement itself* has a witness environment. *)
      Corollary compile_protocol_soundness :
        ∀ (s : stmt) (c c' : F)
          (t t' : comp_transcriptC (compile s)),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        c <> c' ->
        comp_same_announcementC (compile s) t t' ->
        comp_verifyC (compile s) c t = true ->
        comp_verifyC (compile s) c' t' = true ->
        ∃ (wenv : string -> F), stmt_denote wenv s.
      Proof.
        intros * ha hb hc hd he hf hg.
        destruct (@comp_special_soundness F zero one add mul sub div
          opp inv Fdec G gid ginv gop gpow Gdec Hvec
          (compile s) c c' t t' hd he hf hg) as (w & hw).
        eapply compile_stmt_reflect.
        exact ha. exact hb. exact hc. exact hw.
      Qed.

      (* ------------- Phase 4b: the Pedersen repair ------------- *)

      Lemma existsb_false_in :
        ∀ (l : list string) (z y : string),
        List.existsb (String.eqb z) l = false ->
        List.In y l ->
        String.eqb z y = false.
      Proof.
        intros * ha hb.
        destruct (String.eqb z y) eqn:hc; [| reflexivity].
        eapply String.eqb_eq in hc; subst.
        rewrite (in_vars_existsb _ _ hb) in ha.
        congruence.
      Qed.

      Lemma rename_term_denote :
        ∀ (x x' : string) (wenv : string -> F) (t : term),
        term_denote wenv (rename_term x x' t) =
        term_denote (override wenv x (wenv x')) t.
      Proof.
        intros *.
        unfold term_denote, rename_term, override; cbn.
        destruct (String.eqb (t_var t) x) eqn:ha.
        +
          eapply String.eqb_eq in ha; subst.
          rewrite String.eqb_refl.
          reflexivity.
        +
          rewrite String.eqb_sym in ha.
          rewrite ha.
          reflexivity.
      Qed.

      Lemma rename_eq_denote :
        ∀ (x x' : string) (wenv : string -> F) (e : equation),
        eq_denote wenv (rename_eq x x' e) <->
        eq_denote (override wenv x (wenv x')) e.
      Proof.
        intros *.
        unfold eq_denote, rename_eq; cbn.
        enough (hf :
          List.fold_right
            (fun t acc => gop (term_denote wenv t) acc) gid
            (List.map (rename_term x x') (eq_rhs e)) =
          List.fold_right
            (fun t acc =>
              gop (term_denote (override wenv x (wenv x')) t) acc)
            gid (eq_rhs e)).
        rewrite hf; reflexivity.
        induction (eq_rhs e) as [|t ts iht]; cbn.
        reflexivity.
        rewrite rename_term_denote, iht; reflexivity.
      Qed.

      Lemma rename_stmt_denote :
        ∀ (s : stmt) (x x' : string) (wenv : string -> F),
        stmt_denote wenv (rename_stmt x x' s) <->
        stmt_denote (override wenv x (wenv x')) s.
      Proof.
        induction s as [eqs | a iha b ihb | a iha b ihb].
        +
          intros *; cbn.
          induction eqs as [|e eqs ihe]; cbn.
          ++
            split; intro; constructor.
          ++
            split; intro ha;
            inversion ha as [|? ? hb hc]; subst; constructor.
            eapply rename_eq_denote; exact hb.
            eapply ihe; exact hc.
            eapply rename_eq_denote; exact hb.
            eapply ihe; exact hc.
        +
          intros *; cbn.
          rewrite (iha x x' wenv), (ihb x x' wenv).
          reflexivity.
        +
          intros *; cbn.
          rewrite (iha x x' wenv), (ihb x x' wenv).
          reflexivity.
      Qed.

      (* The computational core: two openings of the same Pedersen
         commitment either agree on the committed value or exhibit a
         discrete-log relation between the two bases. *)
      Lemma pedersen_binding_dichotomy :
        ∀ (A B : G) (a b a' b' : F),
        gop (A ^ a) (B ^ b) = gop (A ^ a') (B ^ b') ->
        a = a' ∨ (∃ d : F, A = B ^ d).
      Proof.
        intros * ha.
        destruct (Fdec a a') as [heq | hneq].
        +
          left; exact heq.
        +
          right.
          exists ((b' + opp b) * inv (a + opp a')).
          eapply f_equal with
            (f := fun z => gop z (gop (ginv (A ^ a')) (ginv (B ^ b))))
            in ha.
          rewrite gop_simp in ha.
          rewrite right_inverse, right_identity in ha.
          rewrite gop_simp in ha.
          rewrite right_inverse, left_identity in ha.
          rewrite !connection_between_vopp_and_fopp in ha.
          rewrite <-!smul_distributive_fadd in ha.
          eapply f_equal with
            (f := fun z => z ^ (inv (a + opp a'))) in ha.
          rewrite <-!smul_associative_fmul in ha.
          assert (hb : (a + opp a') * inv (a + opp a') = one).
          field.
          intro hb; eapply hneq.
          eapply f_equal with (f := fun z => z + a') in hb.
          rewrite left_identity in hb.
          rewrite <-hb; field.
          rewrite hb, field_one in ha.
          exact ha.
      Qed.

      Lemma commit_eq_denote :
        ∀ (Cn An Bn v w : string) (wenv : string -> F),
        eq_denote wenv (commit_eq Cn An Bn v w) <->
        genv Cn = gop ((genv An) ^ (wenv v)) ((genv Bn) ^ (wenv w)).
      Proof.
        intros *.
        unfold eq_denote, commit_eq, term_denote; cbn.
        assert (ha : one * wenv v = wenv v). field.
        assert (hb : one * wenv w = wenv w). field.
        rewrite ha, hb, right_identity.
        reflexivity.
      Qed.

      (* Repair soundness: a witness environment for the repaired
         statement yields either one for the original statement (the
         shared variable is bound to the committed value), or an
         explicit discrete-log relation between the commitment bases
         — the extractor dichotomy. *)
      Theorem repair_soundness :
        ∀ (sa sb : stmt) (Cn An Bn x r x₁ r₁ x₂ r₂ : string)
          (wenv : string -> F),
        String.eqb x r = false ->
        stmt_denote wenv (repair_or sa sb Cn An Bn x r x₁ r₁ x₂ r₂) ->
        (∃ wenv' : string -> F,
          stmt_denote wenv'
            (SAnd (SLeaf (List.cons (commit_eq Cn An Bn x r) List.nil))
              (SOr sa sb))) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * hxr hd.
        cbn in hd.
        destruct hd as (hroot & hbranch).
        inversion hroot as [| ? ? hce hnil]; subst.
        eapply commit_eq_denote in hce.
        destruct hbranch as [hbr | hbr].
        +
          destruct hbr as (hren & hcom).
          inversion hcom as [| ? ? hce₁ hnil₁]; subst.
          eapply commit_eq_denote in hce₁.
          rewrite hce in hce₁.
          destruct (pedersen_binding_dichotomy _ _ _ _ _ _ hce₁)
            as [heq | hdlog].
          ++
            left.
            exists (override wenv x (wenv x₁)).
            cbn; split.
            +++
              constructor; [| constructor].
              eapply commit_eq_denote.
              unfold override.
              rewrite String.eqb_refl, hxr.
              rewrite <-heq.
              exact hce.
            +++
              left.
              eapply rename_stmt_denote.
              exact hren.
          ++
            right; exact hdlog.
        +
          destruct hbr as (hren & hcom).
          inversion hcom as [| ? ? hce₂ hnil₂]; subst.
          eapply commit_eq_denote in hce₂.
          rewrite hce in hce₂.
          destruct (pedersen_binding_dichotomy _ _ _ _ _ _ hce₂)
            as [heq | hdlog].
          ++
            left.
            exists (override wenv x (wenv x₂)).
            cbn; split.
            +++
              constructor; [| constructor].
              eapply commit_eq_denote.
              unfold override.
              rewrite String.eqb_refl, hxr.
              rewrite <-heq.
              exact hce.
            +++
              right.
              eapply rename_stmt_denote.
              exact hren.
          ++
            right; exact hdlog.
      Qed.

      (* Repair completeness: an honest prover for the original
         statement can prove the repaired one, by opening the
         commitment for the renamed copy of the branch it holds. *)
      Theorem repair_completeness :
        ∀ (sa sb : stmt) (Cn An Bn x r x₁ r₁ x₂ r₂ : string)
          (wenv : string -> F),
        String.eqb x₁ x = false -> String.eqb r₁ x = false ->
        String.eqb x₁ r = false -> String.eqb r₁ r = false ->
        String.eqb r₁ x₁ = false ->
        List.existsb (String.eqb x₁) (stmt_vars sa) = false ->
        List.existsb (String.eqb r₁) (stmt_vars sa) = false ->
        String.eqb x₂ x = false -> String.eqb r₂ x = false ->
        String.eqb x₂ r = false -> String.eqb r₂ r = false ->
        String.eqb r₂ x₂ = false ->
        List.existsb (String.eqb x₂) (stmt_vars sb) = false ->
        List.existsb (String.eqb r₂) (stmt_vars sb) = false ->
        stmt_denote wenv
          (SAnd (SLeaf (List.cons (commit_eq Cn An Bn x r) List.nil))
            (SOr sa sb)) ->
        ∃ (wenv' : string -> F),
          stmt_denote wenv'
            (repair_or sa sb Cn An Bn x r x₁ r₁ x₂ r₂).
      Proof.
        intros * hx₁x hr₁x hx₁r hr₁r hr₁x₁ hx₁sa hr₁sa
          hx₂x hr₂x hx₂r hr₂r hr₂x₂ hx₂sb hr₂sb hd.
        cbn in hd.
        destruct hd as (hroot & hbranch).
        inversion hroot as [| ? ? hce hnil]; subst.
        eapply commit_eq_denote in hce.
        destruct hbranch as [hbr | hbr].
        +
          (* left branch holds *)
          exists (override (override wenv x₁ (wenv x)) r₁ (wenv r)).
          cbn; split.
          ++
            constructor; [| constructor].
            eapply commit_eq_denote.
            unfold override.
            rewrite hr₁x, hx₁x, hr₁r, hx₁r.
            exact hce.
          ++
            left; split.
            +++
              eapply rename_stmt_denote.
              eapply stmt_denote_ext; [| exact hbr].
              intros y hy.
              unfold override.
              rewrite hr₁x₁, String.eqb_refl.
              destruct (String.eqb x y) eqn:hxy.
              ++++
                eapply String.eqb_eq in hxy; subst.
                reflexivity.
              ++++
                rewrite (existsb_false_in _ _ _ hr₁sa hy).
                rewrite (existsb_false_in _ _ _ hx₁sa hy).
                reflexivity.
            +++
              constructor; [| constructor].
              eapply commit_eq_denote.
              unfold override.
              rewrite hr₁x₁, !String.eqb_refl.
              exact hce.
        +
          (* right branch holds *)
          exists (override (override wenv x₂ (wenv x)) r₂ (wenv r)).
          cbn; split.
          ++
            constructor; [| constructor].
            eapply commit_eq_denote.
            unfold override.
            rewrite hr₂x, hx₂x, hr₂r, hx₂r.
            exact hce.
          ++
            right; split.
            +++
              eapply rename_stmt_denote.
              eapply stmt_denote_ext; [| exact hbr].
              intros y hy.
              unfold override.
              rewrite hr₂x₂, String.eqb_refl.
              destruct (String.eqb x y) eqn:hxy.
              ++++
                eapply String.eqb_eq in hxy; subst.
                reflexivity.
              ++++
                rewrite (existsb_false_in _ _ _ hr₂sb hy).
                rewrite (existsb_false_in _ _ _ hx₂sb hy).
                reflexivity.
            +++
              constructor; [| constructor].
              eapply commit_eq_denote.
              unfold override.
              rewrite hr₂x₂, !String.eqb_refl.
              exact hce.
      Qed.

      (* ------------- Phase 5: THRESH semantics ------------- *)

      Lemma big_and_denote :
        ∀ (l : list stmt) (wenv : string -> F),
        stmt_denote wenv (big_and l) <->
        List.Forall (stmt_denote wenv) l.
      Proof.
        induction l as [|s l ihl].
        +
          intros *; cbn.
          split; intro ha; constructor.
        +
          intros *; cbn.
          split.
          ++
            intros (hs & hl).
            constructor; [exact hs | eapply ihl; exact hl].
          ++
            intro ha.
            inversion ha; subst.
            split; [assumption | eapply ihl; assumption].
      Qed.

      Lemma big_or_denote :
        ∀ (l : list stmt) (s : stmt) (wenv : string -> F),
        stmt_denote wenv (big_or s l) <->
        (stmt_denote wenv s ∨ List.Exists (stmt_denote wenv) l).
      Proof.
        induction l as [|a l ihl].
        +
          intros *; cbn.
          split.
          intro ha; left; exact ha.
          intros [ha | ha]; [exact ha | inversion ha].
        +
          intros *; cbn.
          split.
          ++
            intros [ha | ha].
            +++
              right; eapply List.Exists_cons_hd; exact ha.
            +++
              eapply ihl in ha.
              destruct ha as [ha | ha].
              left; exact ha.
              right; eapply List.Exists_cons_tl; exact ha.
          ++
            intros [ha | ha].
            +++
              right; eapply ihl; left; exact ha.
            +++
              inversion ha as [? ? hb | ? ? hb]; subst.
              left; exact hb.
              right; eapply ihl; right; exact hb.
      Qed.

      (* THRESH(t, l) denotes: some t-element subsequence of l holds
         entirely — i.e. at least t of the statements hold. *)
      Theorem thresh_stmt_denote :
        ∀ (t : nat) (l : list stmt) (wenv : string -> F),
        (t <= List.length l)%nat ->
        (stmt_denote wenv (thresh_stmt t l) <->
         (∃ c : list stmt, subseq c l ∧ List.length c = t ∧
            List.Forall (stmt_denote wenv) c)).
      Proof.
        intros * ht.
        unfold thresh_stmt.
        destruct (List.map big_and (combs t l)) as [|s₀ rest] eqn:hm.
        +
          exfalso.
          eapply List.map_eq_nil in hm.
          eapply combs_nonempty; [exact ht | exact hm].
        +
          rewrite big_or_denote.
          assert (hiff :
            (stmt_denote wenv s₀ ∨ List.Exists (stmt_denote wenv) rest)
            <-> List.Exists (stmt_denote wenv)
                  (List.map big_and (combs t l))).
          rewrite hm.
          split.
          intros [ha | ha].
          eapply List.Exists_cons_hd; exact ha.
          eapply List.Exists_cons_tl; exact ha.
          intro ha.
          inversion ha as [? ? hb | ? ? hb]; subst.
          left; exact hb.
          right; exact hb.
          rewrite hiff.
          rewrite List.Exists_exists.
          split.
          ++
            intros (y & hy & hdy).
            eapply List.in_map_iff in hy.
            destruct hy as (c & hc & hcin); subst.
            destruct (combs_sound _ _ _ hcin) as (hsub & hlen).
            exists c.
            split; [exact hsub | split; [exact hlen |]].
            eapply big_and_denote; exact hdy.
          ++
            intros (c & hsub & hlen & hall).
            exists (big_and c).
            split.
            eapply List.in_map.
            rewrite <-hlen.
            eapply combs_complete; exact hsub.
            eapply big_and_denote; exact hall.
      Qed.

      (* ------------- The automated repair pass ------------- *)

      Lemma find_unequal_none :
        ∀ (xs : list string) (wenv : string -> F)
          (f : string -> string),
        find_unequal wenv f xs = None ->
        ∀ x, List.In x xs -> wenv x = wenv (f x).
      Proof.
        induction xs as [|a xs ih]; intros * ha x hb.
        +
          destruct hb.
        +
          cbn in ha.
          destruct (Fdec (wenv a) (wenv (f a))) as [he | hne];
          [| congruence].
          destruct hb as [hb | hb].
          ++
            subst; exact he.
          ++
            eapply ih; [exact ha | exact hb].
      Qed.

      Lemma find_unequal_some :
        ∀ (xs : list string) (wenv : string -> F)
          (f : string -> string) (x : string),
        find_unequal wenv f xs = Some x ->
        List.In x xs ∧ wenv x <> wenv (f x).
      Proof.
        induction xs as [|a xs ih]; intros * ha.
        +
          cbn in ha; congruence.
        +
          cbn in ha.
          destruct (Fdec (wenv a) (wenv (f a))) as [he | hne].
          ++
            destruct (ih _ _ _ ha) as (hi & hn).
            split; [right; exact hi | exact hn].
          ++
            injection ha as ha; subst.
            split; [left; reflexivity | exact hne].
      Qed.

      Lemma forall_map_in :
        ∀ (A B : Type) (P : B -> Prop) (f : A -> B)
          (l : list A) (x : A),
        List.Forall P (List.map f l) ->
        List.In x l ->
        P (f x).
      Proof.
        intros * ha hb.
        rewrite List.Forall_forall in ha.
        eapply ha, List.in_map, hb.
      Qed.

      (* Sequential renaming collapses when every copy carries the
         same value as its original. *)
      Lemma rename_list_transfer :
        ∀ (ps : list (string * string)) (s : stmt)
          (wenv : string -> F),
        pairs_ok ps = true ->
        (∀ x x', List.In (x, x') ps -> wenv x = wenv x') ->
        stmt_denote wenv (rename_list ps s) ->
        stmt_denote wenv s.
      Proof.
        induction ps as [|(x, x') ps ih]; intros * hok heq hd.
        +
          exact hd.
        +
          cbn in hd, hok.
          eapply andb_true_iff in hok.
          destruct hok as (hall & hok).
          eapply rename_stmt_denote in hd.
          assert (hd₂ : stmt_denote (override wenv x (wenv x')) s).
          eapply ih.
          exact hok.
          intros y y' hin.
          pose proof (proj1 (List.forallb_forall _ _) hall
            (y, y') hin) as hp.
          cbn in hp.
          eapply andb_true_iff in hp.
          destruct hp as (hp₁ & hp₂).
          eapply negb_true_iff in hp₁, hp₂.
          unfold override.
          rewrite hp₁, hp₂.
          eapply heq.
          right; exact hin.
          exact hd.
          eapply stmt_denote_ext; [| exact hd₂].
          intros y hy.
          unfold override.
          destruct (String.eqb x y) eqn:hxy.
          ++
            eapply String.eqb_eq in hxy; subst.
            symmetry.
            eapply heq.
            left; reflexivity.
          ++
            reflexivity.
      Qed.

      (* Soundness of the automated pass: a witness environment for
         the repaired statement satisfies the *original* statement —
         with the same environment — or exhibits a discrete-log
         relation between the commitment bases.  The two pairs_ok
         hypotheses are decidable and hold by computation for
         '#'-generated names. *)
      Theorem auto_repair_sound :
        ∀ (An Bn : string) (sc sa sb : stmt) (wenv : string -> F),
        pairs_ok (left_pairs (shared_vars sc sa sb)) = true ->
        pairs_ok (right_pairs (shared_vars sc sa sb)) = true ->
        stmt_denote wenv (auto_repair An Bn sc sa sb) ->
        stmt_denote wenv (SAnd sc (SOr sa sb)) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * hokl hokr hd.
        unfold auto_repair in hd.
        revert hokl hokr hd.
        generalize (shared_vars sc sa sb) as xs;
        intros xs hokl hokr hd.
        destruct xs as [|x₀ xs₀]; [left; exact hd |].
        unfold repair_with in hd.
        destruct hd as ((hsc & hroot) & hbranch).
        change (List.Forall (eq_denote wenv)
          (List.map (fun x => commit_eq (c_name x) An Bn x (r_name x))
            (List.cons x₀ xs₀))) in hroot.
        destruct hbranch as [hbranch | hbranch].
        +
          destruct hbranch as (hren & hbinds).
          change (List.Forall (eq_denote wenv)
            (List.map (fun x =>
              commit_eq (c_name x) An Bn (l_name x) (lr_name x))
              (List.cons x₀ xs₀))) in hbinds.
          destruct (find_unequal wenv l_name (List.cons x₀ xs₀))
            eqn:hfu.
          ++
            destruct (find_unequal_some _ _ _ _ hfu) as (hin & hne).
            pose proof (forall_map_in _ _ _ _ _ _ hroot hin) as hce.
            pose proof (forall_map_in _ _ _ _ _ _ hbinds hin) as hce₁.
            eapply commit_eq_denote in hce, hce₁.
            rewrite hce in hce₁.
            destruct (pedersen_binding_dichotomy _ _ _ _ _ _ hce₁)
              as [heq | hdlog].
            +++
              exfalso; eapply hne; exact heq.
            +++
              right; exact hdlog.
          ++
            left.
            cbn; split.
            exact hsc.
            left.
            eapply rename_list_transfer.
            exact hokl.
            intros x x' hin.
            unfold left_pairs in hin.
            eapply List.in_map_iff in hin.
            destruct hin as (y & hy & hyin).
            injection hy as h₁ h₂; subst.
            eapply find_unequal_none.
            exact hfu. exact hyin.
            exact hren.
        +
          destruct hbranch as (hren & hbinds).
          change (List.Forall (eq_denote wenv)
            (List.map (fun x =>
              commit_eq (c_name x) An Bn (rn_name x) (rr_name x))
              (List.cons x₀ xs₀))) in hbinds.
          destruct (find_unequal wenv rn_name (List.cons x₀ xs₀))
            eqn:hfu.
          ++
            destruct (find_unequal_some _ _ _ _ hfu) as (hin & hne).
            pose proof (forall_map_in _ _ _ _ _ _ hroot hin) as hce.
            pose proof (forall_map_in _ _ _ _ _ _ hbinds hin) as hce₂.
            eapply commit_eq_denote in hce, hce₂.
            rewrite hce in hce₂.
            destruct (pedersen_binding_dichotomy _ _ _ _ _ _ hce₂)
              as [heq | hdlog].
            +++
              exfalso; eapply hne; exact heq.
            +++
              right; exact hdlog.
          ++
            left.
            cbn; split.
            exact hsc.
            right.
            eapply rename_list_transfer.
            exact hokr.
            intros x x' hin.
            unfold right_pairs in hin.
            eapply List.in_map_iff in hin.
            destruct hin as (y & hy & hyin).
            injection hy as h₁ h₂; subst.
            eapply find_unequal_none.
            exact hfu. exact hyin.
            exact hren.
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

    (* The disjunction-invariant checker runs by computation. *)
    Example schnorr_disj : disj_inv schnorr_stmt = true := eq_refl.

    (* An OR over disjoint variables — knowledge of the discrete log
       of H1 or of H2 — passes the checker. *)
    Definition or_stmt : stmt :=
      SOr
        (SLeaf (List.cons
          (mkeq "H1" (List.cons (mkterm (PConst one) "x" "G")
            List.nil)) List.nil))
        (SLeaf (List.cons
          (mkeq "H2" (List.cons (mkterm (PConst one) "y" "G")
            List.nil)) List.nil)).

    Example or_disj : disj_inv or_stmt = true := eq_refl.

    (* Sharing a private variable between an OR branch and a
       statement outside the OR is rejected: the compiled witnesses
       would be independent, so the shared x would not be bound.
       (sigma-compiler repairs this with Pedersen commitments; here
       it is the checker's acceptance condition.) *)
    Definition bad_stmt : stmt :=
      SAnd
        (SLeaf (List.cons
          (mkeq "C" (List.cons (mkterm (PConst one) "x" "G")
            List.nil)) List.nil))
        (SOr
          (SLeaf (List.cons
            (mkeq "H1" (List.cons (mkterm (PConst one) "x" "G")
              List.nil)) List.nil))
          (SLeaf (List.cons
            (mkeq "H2" (List.cons (mkterm (PConst one) "y" "G")
              List.nil)) List.nil))).

    Example bad_disj : disj_inv bad_stmt = false := eq_refl.

    (* The automated repair pass turns the rejected pattern into an
       accepted one; the checker, the pass, and its side conditions
       all run by computation. *)
    Definition bad_sc : stmt :=
      SLeaf (List.cons
        (mkeq "C" (List.cons (mkterm (PConst one) "x" "G")
          List.nil)) List.nil).
    Definition bad_sa : stmt :=
      SLeaf (List.cons
        (mkeq "H1" (List.cons (mkterm (PConst one) "x" "G")
          List.nil)) List.nil).
    Definition bad_sb : stmt :=
      SLeaf (List.cons
        (mkeq "H2" (List.cons (mkterm (PConst one) "y" "G")
          List.nil)) List.nil).

    Example bad_pattern_rejected :
      disj_inv (SAnd bad_sc (SOr bad_sa bad_sb)) = false := eq_refl.

    Example repaired_accepted :
      disj_inv (auto_repair "A" "B" bad_sc bad_sa bad_sb) = true
      := eq_refl.

    Example repaired_pairs_left :
      pairs_ok (left_pairs (shared_vars bad_sc bad_sa bad_sb)) = true
      := eq_refl.

    Example repaired_pairs_right :
      pairs_ok (right_pairs (shared_vars bad_sc bad_sa bad_sb)) = true
      := eq_refl.

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
