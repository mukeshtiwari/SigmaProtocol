From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos String List DecimalString
  DecimalNat.
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

  (* One equation, in homogeneous form:
       Π base_i ^ (coeff_i · x_i)  ·  Π base_j ^ coeff_j  =  1.
     eq_rhs are the private terms; eq_off the *public offsets*
     (Milestone B) — terms with no private variable, e.g. constants
     and public-scalar multiples of points, and the (negated)
     left-hand side.  simple_eq recovers the readable
     P = Π terms  form. *)
  Record equation : Type := mkeq
    { eq_rhs : list term;
      eq_off : list (pexpr * string) }.

  Definition simple_eq (Pn : string) (ts : list term) : equation :=
    mkeq ts (List.cons (POpp (PConst one), Pn) List.nil).

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
    mkeq (List.map (rename_term x x') (eq_rhs e)) (eq_off e).

  Fixpoint rename_stmt (x x' : string) (s : stmt) : stmt :=
    match s with
    | SLeaf eqs => SLeaf (List.map (rename_eq x x') eqs)
    | SAnd a b => SAnd (rename_stmt x x' a) (rename_stmt x x' b)
    | SOr a b => SOr (rename_stmt x x' a) (rename_stmt x x' b)
    end.

  (* The Pedersen commitment equation  C = A^v · B^w  *)
  Definition commit_eq (Cn An Bn v w : string) : equation :=
    simple_eq Cn (List.cons (mkterm (PConst one) v An)
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

  (* ---------------- Not-equals lowering (Milestone D) ------------ *)

  Definition neq_j (x : string) : string := String.append x "#j".
  Definition neq_s (x : string) : string := String.append x "#s".

  (* C = A^(coeff·x + off) · B^r, in homogeneous form *)
  Definition neq_commit (Cn An Bn x r : string)
    (coeff off : pexpr) : equation :=
    mkeq (List.cons (mkterm coeff x An)
      (List.cons (mkterm (PConst one) r Bn) List.nil))
      (List.cons (off, An)
        (List.cons (POpp (PConst one), Cn) List.nil)).

  (*
    The lowering of  coeff·x + off ≠ 0  (sigma-compiler's notequals
    pass): commit to L(x) = coeff·x + off as C = A^L(x)·B^r, and
    prove knowledge of j, s with  A = C^j · B^s  (honest prover:
    j = L(x)⁻¹, s = −r·j).  Everything is linear, so the result
    composes under the existing pipeline.
  *)
  Definition neq_stmt (Cn An Bn x j s r : string)
    (coeff off : pexpr) : stmt :=
    SLeaf (List.cons (neq_commit Cn An Bn x r coeff off)
      (List.cons (simple_eq An
        (List.cons (mkterm (PConst one) j Cn)
          (List.cons (mkterm (PConst one) s Bn) List.nil)))
        List.nil)).

  (* automated wrapper with generated names *)
  Definition neq_auto (An Bn x : string) (coeff off : pexpr) : stmt :=
    neq_stmt (c_name x) An Bn x (neq_j x) (neq_s x) (r_name x)
      coeff off.

  (* ============ Surface expression language (Milestone C) ========

     The sigma_compiler!-style front end: arbitrary arithmetic over
     public scalars, private scalars, and points, normalized into
     the homogeneous equation form.  Normalization returns None on
     the ill-typed cases (private·private products, point·point
     products are unrepresentable by the syntax split). *)

  Inductive sexpr : Type :=
  | SConst (c : F)
  | SPubV (x : string)
  | SPrivV (x : string)
  | SAddE (a b : sexpr)
  | SMulE (a b : sexpr)
  | SOppE (a : sexpr).

  Inductive gexpr : Type :=
  | GIdE
  | GPointV (P : string)
  | GAddE (a b : gexpr)
  | GInvE (a : gexpr)
  | GSmulE (sc : sexpr) (a : gexpr).

  (* normal form of a scalar expression: private linear part
     (coefficient · variable) plus a public part *)
  Definition lin : Type :=
    (list (pexpr * string) * pexpr)%type.

  Fixpoint snorm (e : sexpr) : option lin :=
    match e with
    | SConst c => Some (List.nil, PConst c)
    | SPubV x => Some (List.nil, PVar x)
    | SPrivV x =>
        Some (List.cons (PConst one, x) List.nil, PConst zero)
    | SAddE a b =>
        match snorm a, snorm b with
        | Some (la, pa), Some (lb, pb) =>
            Some (List.app la lb, PAdd pa pb)
        | _, _ => None
        end
    | SOppE a =>
        match snorm a with
        | Some (la, pa) =>
            Some (List.map (fun cx => (POpp (fst cx), snd cx)) la,
              POpp pa)
        | None => None
        end
    | SMulE a b =>
        match snorm a, snorm b with
        | Some (la, pa), Some (lb, pb) =>
            match la, lb with
            | List.nil, _ =>
                Some (List.map
                  (fun cx => (PMul pa (fst cx), snd cx)) lb,
                  PMul pa pb)
            | _, List.nil =>
                Some (List.map
                  (fun cx => (PMul pb (fst cx), snd cx)) la,
                  PMul pa pb)
            | _, _ => None
            end
        | _, _ => None
        end
    end.

  (* normal form of a point expression: private terms + offsets —
     the two components of a homogeneous equation *)
  Fixpoint gnorm (e : gexpr) :
    option (list term * list (pexpr * string)) :=
    match e with
    | GIdE => Some (List.nil, List.nil)
    | GPointV P =>
        Some (List.nil, List.cons (PConst one, P) List.nil)
    | GAddE a b =>
        match gnorm a, gnorm b with
        | Some (ta, oa), Some (tb, ob) =>
            Some (List.app ta tb, List.app oa ob)
        | _, _ => None
        end
    | GInvE a =>
        match gnorm a with
        | Some (ta, oa) =>
            Some (List.map (fun t =>
                mkterm (POpp (t_coeff t)) (t_var t) (t_base t)) ta,
              List.map (fun o => (POpp (fst o), snd o)) oa)
        | None => None
        end
    | GSmulE sc a =>
        match snorm sc, gnorm a with
        | Some (ls, ps), Some (ta, oa) =>
            match ta, ls with
            | List.nil, List.nil =>
                Some (List.nil,
                  List.map (fun o => (PMul ps (fst o), snd o)) oa)
            | List.nil, _ =>
                Some (List.flat_map (fun o =>
                    List.map (fun cx =>
                      mkterm (PMul (fst cx) (fst o))
                        (snd cx) (snd o)) ls) oa,
                  List.map (fun o => (PMul ps (fst o), snd o)) oa)
            | _, List.nil =>
                Some (List.map (fun t =>
                    mkterm (PMul ps (t_coeff t))
                      (t_var t) (t_base t)) ta,
                  List.map (fun o => (PMul ps (fst o), snd o)) oa)
            | _, _ => None
            end
        | _, _ => None
        end
    end.

  (* surface statements *)
  Inductive sstmt : Type :=
  | SSEq (lhs rhs : gexpr)
  | SSNeq (a b : sexpr)
  | SSAndS (a b : sstmt)
  | SSOrS (a b : sstmt).

  (* elaborate a point equation:  lhs = rhs  becomes the
     homogeneous  rhs · lhs⁻¹ = 1 *)
  Definition elab_eq (lhs rhs : gexpr) : option equation :=
    match gnorm (GAddE rhs (GInvE lhs)) with
    | Some (ts, os) => Some (mkeq ts os)
    | None => None
    end.

  (* elaborate a surface statement; An Bn are the two cind base
     names used by the not-equals lowering *)
  Fixpoint elab (An Bn : string) (s : sstmt) : option stmt :=
    match s with
    | SSEq l r =>
        match elab_eq l r with
        | Some e => Some (SLeaf (List.cons e List.nil))
        | None => None
        end
    | SSNeq a b =>
        match snorm (SAddE a (SOppE b)) with
        | Some (List.cons (c, x) List.nil, off) =>
            Some (neq_auto An Bn x c off)
        | _ => None
        end
    | SSAndS a b =>
        match elab An Bn a, elab An Bn b with
        | Some a', Some b' => Some (SAnd a' b')
        | _, _ => None
        end
    | SSOrS a b =>
        match elab An Bn a, elab An Bn b with
        | Some a', Some b' => Some (SOr a' b')
        | _, _ => None
        end
    end.

  (* ---------------- Substitution (Milestone A1) ---------------- *)

  Fixpoint sexpr_subst (x : string) (v : sexpr) (e : sexpr) :
    sexpr :=
    match e with
    | SConst c => SConst c
    | SPubV y => SPubV y
    | SPrivV y => if String.eqb y x then v else SPrivV y
    | SAddE a b => SAddE (sexpr_subst x v a) (sexpr_subst x v b)
    | SMulE a b => SMulE (sexpr_subst x v a) (sexpr_subst x v b)
    | SOppE a => SOppE (sexpr_subst x v a)
    end.

  Fixpoint gexpr_subst (x : string) (v : sexpr) (e : gexpr) :
    gexpr :=
    match e with
    | GIdE => GIdE
    | GPointV P => GPointV P
    | GAddE a b => GAddE (gexpr_subst x v a) (gexpr_subst x v b)
    | GInvE a => GInvE (gexpr_subst x v a)
    | GSmulE sc a => GSmulE (sexpr_subst x v sc) (gexpr_subst x v a)
    end.

  Fixpoint sstmt_subst (x : string) (v : sexpr) (s : sstmt) :
    sstmt :=
    match s with
    | SSEq l r => SSEq (gexpr_subst x v l) (gexpr_subst x v r)
    | SSNeq a b => SSNeq (sexpr_subst x v a) (sexpr_subst x v b)
    | SSAndS a b => SSAndS (sstmt_subst x v a) (sstmt_subst x v b)
    | SSOrS a b => SSOrS (sstmt_subst x v a) (sstmt_subst x v b)
    end.

  Fixpoint neq_free (s : sstmt) : bool :=
    match s with
    | SSEq _ _ => true
    | SSNeq _ _ => false
    | SSAndS a b => neq_free a && neq_free b
    | SSOrS a b => neq_free a && neq_free b
    end.

  (* ---------------- Vectors and SIMD (Milestone F) ---------------
     Vector variables are families of indexed scalar/point names;
     vec statements expand at a runtime length.  sum(x*A)-style dot
     products are single equations with one term per index. *)

  Definition nat_name (k : nat) : string :=
    NilEmpty.string_of_uint (Nat.to_uint k).

  Definition vname (x : string) (i : nat) : string :=
    String.append x (String.append "@" (nat_name i)).

  Definition vec_names (x : string) (nv : nat) : list string :=
    List.map (vname x) (List.seq 0 nv).

  (* AND of a family of statements (SIMD componentwise statements) *)
  Definition big_sand (s : sstmt) (l : list sstmt) : sstmt :=
    List.fold_right SSAndS s l.

  (* product of a family of point expressions *)
  Definition big_gop (e : gexpr) (l : list gexpr) : gexpr :=
    List.fold_right GAddE e l.

  (* Σᵢ x@i · A@i  — the sum(x*A) dot product *)
  Definition dot_terms (x A : string) (nv : nat) : list gexpr :=
    List.map (fun i => GSmulE (SPrivV (vname x i))
      (GPointV (vname A i))) (List.seq 0 nv).

  Definition dot_product_stmt (C x A : string) (nv : nat) : sstmt :=
    SSEq (GPointV C) (big_gop GIdE (dot_terms x A nv)).

  (* ---------------- Range lowering (Milestone E) -----------------

     (a..b).contains(L) reduces (after normalization) to
     0 <= x < u.  The lowering follows sigma-compiler: commit to
     selection bits b_i, prove each is a bit with the *linear*
     b = b² trick (C = A^b·B^r ∧ C = C^b·B^s), and add one linear
     equation linking x to the weighted bit sum, with weights
     [1, 2, ..., 2^(m-1), u - 2^m] (m = log2 u) whose subset sums
     are exactly [0, u).

     "0 <= x < u" is an *integer* statement about a field element;
     its semantics uses the canonical embedding fnat : nat -> F
     (1 + ... + 1).  Injectivity of fnat below u — a characteristic
     hypothesis, true in Z_q for u < q — is where the field meets
     the integers; the soundness theorem produces the witness
     k < u with  x = fnat k  directly, so no injectivity hypothesis
     is needed for soundness. *)

  Fixpoint fnat (k : nat) : F :=
    match k with
    | 0 => zero
    | S k' => one + fnat k'
    end.

  (* the field-to-bit projection used by the extractor *)
  Definition bitof (v : F) : nat :=
    match Fdec v zero with
    | left _ => 0
    | right _ => 1
    end.

  Definition bit_b (x : string) (i : nat) : string :=
    vname (String.append x "#b") i.
  Definition bit_r (x : string) (i : nat) : string :=
    vname (String.append x "#br") i.
  Definition bit_s (x : string) (i : nat) : string :=
    vname (String.append x "#bs") i.
  Definition bit_C (x : string) (i : nat) : string :=
    vname (String.append x "#bC") i.

  Definition range_weights (u : nat) : list nat :=
    List.app
      (List.map (fun i => Nat.pow 2 i) (List.seq 0 (Nat.log2 u)))
      (List.cons (u - Nat.pow 2 (Nat.log2 u))%nat List.nil).

  Definition indexed_weights (u : nat) : list (nat * nat) :=
    List.combine
      (List.seq 0 (List.length (range_weights u)))
      (range_weights u).

  (* bit equations for index i:
       Cb_i = A^{b_i} · B^{r_i}   and   Cb_i = Cb_i^{b_i} · B^{s_i} *)
  Definition bit_eqs (An Bn x : string) (i : nat) : list equation :=
    List.cons (commit_eq (bit_C x i) An Bn (bit_b x i) (bit_r x i))
    (List.cons (simple_eq (bit_C x i)
      (List.cons (mkterm (PConst one) (bit_b x i) (bit_C x i))
        (List.cons (mkterm (PConst one) (bit_s x i) Bn) List.nil)))
      List.nil).

  (* linking equation:  A^x · Π A^{-w_i·b_i} = 1 *)
  Definition range_link (An x : string) (iws : list (nat * nat)) :
    equation :=
    mkeq (List.cons (mkterm (PConst one) x An)
      (List.map (fun iw =>
        mkterm (PConst (opp (fnat (snd iw))))
          (bit_b x (fst iw)) An) iws))
      List.nil.

  Definition range_stmt (An Bn x : string) (u : nat) : stmt :=
    SLeaf (List.cons (range_link An x (indexed_weights u))
      (List.flat_map (fun iw => bit_eqs An Bn x (fst iw))
        (indexed_weights u))).

  (* first index whose committed value is not a bit — the pivot of
     the soundness dichotomy *)
  Fixpoint find_nonbit (wenv : string -> F) (x : string)
    (l : list (nat * nat)) : option (nat * nat) :=
    match l with
    | List.nil => None
    | List.cons iw l' =>
        match Fdec (wenv (bit_b x (fst iw))) zero with
        | left _ => find_nonbit wenv x l'
        | right _ =>
            match Fdec (wenv (bit_b x (fst iw))) one with
            | left _ => find_nonbit wenv x l'
            | right _ => Some iw
            end
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

    Definition terms_fold (wenv : string -> F) (ts : list term) : G :=
      List.fold_right (fun t acc => gop (term_denote wenv t) acc)
        gid ts.

    Definition off_denote (o : pexpr * string) : G :=
      (genv (snd o)) ^ (peval penv (fst o)).

    Definition off_fold (os : list (pexpr * string)) : G :=
      List.fold_right (fun o acc => gop (off_denote o) acc) gid os.

    Definition eq_denote (wenv : string -> F) (e : equation) : Prop :=
      gop (terms_fold wenv (eq_rhs e)) (off_fold (eq_off e)) = gid.

    Fixpoint stmt_denote (wenv : string -> F) (s : stmt) : Prop :=
      match s with
      | SLeaf eqs => List.Forall (eq_denote wenv) eqs
      | SAnd a b => stmt_denote wenv a ∧ stmt_denote wenv b
      | SOr a b => stmt_denote wenv a ∨ stmt_denote wenv b
      end.

    (* ---------------- surface semantics ---------------- *)

    Fixpoint seval (wenv : string -> F) (e : sexpr) : F :=
      match e with
      | SConst c => c
      | SPubV x => penv x
      | SPrivV x => wenv x
      | SAddE a b => seval wenv a + seval wenv b
      | SMulE a b => seval wenv a * seval wenv b
      | SOppE a => opp (seval wenv a)
      end.

    Fixpoint geval (wenv : string -> F) (e : gexpr) : G :=
      match e with
      | GIdE => gid
      | GPointV P => genv P
      | GAddE a b => gop (geval wenv a) (geval wenv b)
      | GInvE a => ginv (geval wenv a)
      | GSmulE sc a => (geval wenv a) ^ (seval wenv sc)
      end.

    Definition priv_fold (wenv : string -> F)
      (l : list (pexpr * string)) : F :=
      List.fold_right
        (fun cx acc => peval penv (fst cx) * wenv (snd cx) + acc)
        zero l.

    Definition lin_denote (wenv : string -> F) (l : lin) : F :=
      priv_fold wenv (fst l) + peval penv (snd l).

    Fixpoint sstmt_denote (wenv : string -> F) (s : sstmt) : Prop :=
      match s with
      | SSEq l r => geval wenv l = geval wenv r
      | SSNeq a b => seval wenv a <> seval wenv b
      | SSAndS a b => sstmt_denote wenv a ∧ sstmt_denote wenv b
      | SSOrS a b => sstmt_denote wenv a ∨ sstmt_denote wenv b
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
        (Vector.map (fun e => ginv (off_fold (eq_off e)))
          (Vector.of_list eqs)).

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

    (* ------- Public-scalar equality checks (pubscalareq) ------- *)
    (* sigma-compiler removes public equations from the ZK statement
       and emits runtime checks for both parties.  A checked spec is
       a statement together with the removed public checks; verify
       conjoins them. *)

    Definition check_denote (c : pexpr * pexpr) : Prop :=
      peval penv (fst c) = peval penv (snd c).

    Definition checkb (c : pexpr * pexpr) : bool :=
      match Fdec (peval penv (fst c)) (peval penv (snd c)) with
      | left _ => true
      | right _ => false
      end.

    Definition cspec_denote (wenv : string -> F)
      (checks : list (pexpr * pexpr)) (s : stmt) : Prop :=
      List.Forall check_denote checks ∧ stmt_denote wenv s.

    Definition cspec_verify (checks : list (pexpr * pexpr))
      (s : stmt) (c : F)
      (t : comp_transcriptC (compile s)) : bool :=
      List.forallb checkb checks && comp_verifyC (compile s) c t.

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

      Lemma gop_eq_gid_iff : ∀ (a b : G),
        gop a b = gid <-> a = ginv b.
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := fun z => gop z (ginv b)) in ha.
          rewrite <-associative, right_inverse, right_identity,
            left_identity in ha.
          exact ha.
        +
          rewrite ha.
          rewrite commutative, right_inverse.
          reflexivity.
      Qed.

      (* The readable  P = Π terms  reading of simple_eq *)
      Lemma simple_eq_denote :
        ∀ (Pn : string) (ts : list term) (wenv : string -> F),
        eq_denote wenv (simple_eq Pn ts) <->
        genv Pn = terms_fold wenv ts.
      Proof.
        intros *.
        unfold eq_denote, simple_eq; cbn.
        unfold off_fold, off_denote; cbn.
        rewrite right_identity.
        assert (ha : (genv Pn) ^ (opp one) = ginv (genv Pn)).
        rewrite <-connection_between_vopp_and_fopp.
        rewrite field_one. reflexivity.
        rewrite ha.
        rewrite gop_eq_gid_iff.
        rewrite group_inv_inv.
        split; intro hb; symmetry; exact hb.
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
              eapply gop_eq_gid_iff.
              unfold terms_fold.
              rewrite <-(row_of_terms_correct (eq_rhs e) wenv hae hb).
              exact hh.
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
              eapply gop_eq_gid_iff.
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
        unfold eq_denote, terms_fold in hb |- *.
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

      (* ------------- Checked specs (pubscalareq) ------------- *)

      Lemma checkb_correct : ∀ (c : pexpr * pexpr),
        checkb c = true <-> check_denote c.
      Proof.
        intros; unfold checkb, check_denote.
        destruct (Fdec (peval penv (fst c)) (peval penv (snd c)))
          as [he | hne]; split; intro ha.
        + exact he.
        + reflexivity.
        + congruence.
        + exfalso; eapply hne; exact ha.
      Qed.

      Lemma forallb_checkb : ∀ (cl : list (pexpr * pexpr)),
        List.forallb checkb cl = true <->
        List.Forall check_denote cl.
      Proof.
        induction cl as [|c cl ih]; cbn; split; intro ha.
        + constructor.
        + reflexivity.
        + eapply andb_true_iff in ha.
          destruct ha as (hal & har).
          constructor.
          eapply checkb_correct; exact hal.
          eapply ih; exact har.
        + inversion ha as [| ? ? hb hc]; subst.
          eapply andb_true_iff; split.
          eapply checkb_correct; exact hb.
          eapply ih; exact hc.
      Qed.

      Theorem cspec_protocol_completeness :
        ∀ (checks : list (pexpr * pexpr)) (s : stmt)
          (wenv : string -> F),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        cspec_denote wenv checks s ->
        ∃ (w : comp_witnessC (compile s)),
          ∀ (rnd : comp_randC (compile s)) (c : F),
          cspec_verify checks s c
            (comp_proveC (compile s) w rnd c) = true.
      Proof.
        intros * ha hb (hcheck & hst).
        destruct (compile_stmt_sound s wenv ha hb hst) as (w & hw).
        exists w; intros *.
        unfold cspec_verify.
        eapply andb_true_iff; split.
        eapply forallb_checkb; exact hcheck.
        eapply comp_completeness; exact hw.
      Qed.

      Theorem cspec_protocol_soundness :
        ∀ (checks : list (pexpr * pexpr)) (s : stmt) (c c' : F)
          (t t' : comp_transcriptC (compile s)),
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        c <> c' ->
        comp_same_announcementC (compile s) t t' ->
        cspec_verify checks s c t = true ->
        cspec_verify checks s c' t' = true ->
        ∃ (wenv : string -> F), cspec_denote wenv checks s.
      Proof.
        intros * ha hb hc hd he hf hg.
        unfold cspec_verify in hf, hg.
        eapply andb_true_iff in hf, hg.
        destruct hf as (hfc & hfv).
        destruct hg as (hgc & hgv).
        destruct (compile_protocol_soundness s c c' t t'
          ha hb hc hd he hfv hgv) as (wenv & hwenv).
        exists wenv.
        split.
        eapply forallb_checkb; exact hfc.
        exact hwenv.
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
        unfold commit_eq.
        rewrite simple_eq_denote.
        unfold terms_fold, term_denote; cbn.
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

      (* ------------- The not-equals pass ------------- *)

      Lemma neq_commit_denote :
        ∀ (Cn An Bn x r : string) (coeff off : pexpr)
          (wenv : string -> F),
        eq_denote wenv (neq_commit Cn An Bn x r coeff off) <->
        genv Cn =
          gop ((genv An) ^ (peval penv coeff * wenv x +
                            peval penv off))
              ((genv Bn) ^ (wenv r)).
      Proof.
        intros *.
        unfold eq_denote, neq_commit, terms_fold, off_fold,
          term_denote, off_denote; cbn.
        rewrite !right_identity.
        assert (ha : one * wenv r = wenv r). field.
        rewrite ha.
        assert (hb : (genv Cn) ^ (opp one) = ginv (genv Cn)).
        rewrite <-connection_between_vopp_and_fopp.
        rewrite field_one. reflexivity.
        rewrite hb.
        rewrite gop_simp.
        rewrite <-smul_distributive_fadd.
        rewrite associative.
        rewrite gop_eq_gid_iff.
        rewrite group_inv_inv.
        split; intro hc; symmetry; exact hc.
      Qed.

      (* Soundness: from a witness of the lowered statement, either
         the committed value is nonzero, or a discrete-log relation
         between the bases. *)
      Theorem neq_sound :
        ∀ (Cn An Bn x j s r : string) (coeff off : pexpr)
          (wenv : string -> F),
        stmt_denote wenv (neq_stmt Cn An Bn x j s r coeff off) ->
        (peval penv coeff * wenv x + peval penv off <> zero) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * hd.
        cbn in hd.
        inversion hd as [| ? ? h₁ hrest]; subst.
        inversion hrest as [| ? ? h₂ hnil]; subst.
        eapply neq_commit_denote in h₁.
        rewrite simple_eq_denote in h₂.
        unfold terms_fold, term_denote in h₂; cbn in h₂.
        destruct (Fdec (peval penv coeff * wenv x + peval penv off)
          zero) as [hz | hnz]; [right | left; exact hnz].
        rewrite hz in h₁.
        rewrite field_zero, left_identity in h₁.
        rewrite h₁ in h₂.
        rewrite right_identity in h₂.
        rewrite smul_pow_up in h₂.
        rewrite <-smul_distributive_fadd in h₂.
        exists (wenv r * (one * wenv j) + one * wenv s).
        exact h₂.
      Qed.

      (* Completeness: an honest prover with a nonzero committed
         value extends its environment with j = L(x)⁻¹ and
         s = −r·j. *)
      Theorem neq_complete :
        ∀ (Cn An Bn x j s r : string) (coeff off : pexpr)
          (wenv : string -> F),
        String.eqb j x = false -> String.eqb j r = false ->
        String.eqb s x = false -> String.eqb s r = false ->
        String.eqb s j = false ->
        peval penv coeff * wenv x + peval penv off <> zero ->
        genv Cn =
          gop ((genv An) ^ (peval penv coeff * wenv x +
                            peval penv off))
              ((genv Bn) ^ (wenv r)) ->
        ∃ (wenv' : string -> F),
          stmt_denote wenv' (neq_stmt Cn An Bn x j s r coeff off).
      Proof.
        intros * hjx hjr hsx hsr hsj hnz hcm.
        set (L := peval penv coeff * wenv x + peval penv off) in *.
        exists (override
          (override wenv j (inv L)) s (opp (wenv r) * inv L)).
        cbn.
        constructor; [| constructor; [| constructor]].
        +
          eapply neq_commit_denote.
          unfold override.
          rewrite hsx, hjx, hsr, hjr.
          exact hcm.
        +
          rewrite simple_eq_denote.
          unfold terms_fold, term_denote; cbn.
          unfold override.
          rewrite hsj, !String.eqb_refl.
          rewrite right_identity.
          rewrite hcm.
          rewrite smul_distributive_vadd.
          rewrite !smul_pow_up.
          rewrite <-associative.
          rewrite <-smul_distributive_fadd.
          assert (ha : L * (one * inv L) = one).
          field. exact hnz.
          assert (hb2 : wenv r * (one * inv L) +
            one * (opp (wenv r) * inv L) = zero).
          field. exact hnz.
          rewrite ha, hb2, field_one, field_zero, right_identity.
          reflexivity.
      Qed.

      (* ------------- Surface normalization: scalar side ------------- *)

      Lemma priv_fold_app :
        ∀ (la lb : list (pexpr * string)) (wenv : string -> F),
        priv_fold wenv (List.app la lb) =
        priv_fold wenv la + priv_fold wenv lb.
      Proof.
        induction la as [|cx la ih]; intros *; cbn.
        +
          unfold priv_fold; cbn. field.
        +
          unfold priv_fold in ih |- *; cbn.
          rewrite ih. field.
      Qed.

      Lemma priv_fold_opp :
        ∀ (la : list (pexpr * string)) (wenv : string -> F),
        priv_fold wenv
          (List.map (fun cx => (POpp (fst cx), snd cx)) la) =
        opp (priv_fold wenv la).
      Proof.
        induction la as [|cx la ih]; intros *.
        +
          unfold priv_fold; cbn. field.
        +
          unfold priv_fold in ih |- *; cbn.
          rewrite ih. field.
      Qed.

      Lemma priv_fold_scale :
        ∀ (la : list (pexpr * string)) (k : pexpr)
          (wenv : string -> F),
        priv_fold wenv
          (List.map (fun cx => (PMul k (fst cx), snd cx)) la) =
        peval penv k * priv_fold wenv la.
      Proof.
        induction la as [|cx la ih]; intros *.
        +
          unfold priv_fold; cbn. field.
        +
          unfold priv_fold in ih |- *; cbn.
          rewrite ih. field.
      Qed.

      Lemma snorm_correct :
        ∀ (e : sexpr) (l : lin) (wenv : string -> F),
        snorm e = Some l ->
        seval wenv e = lin_denote wenv l.
      Proof.
        induction e as [c | x | x | a iha b ihb | a iha b ihb | a iha];
        intros * hn; cbn in hn.
        +
          injection hn as hn; subst.
          unfold lin_denote, priv_fold; cbn. field.
        +
          injection hn as hn; subst.
          unfold lin_denote, priv_fold; cbn. field.
        +
          injection hn as hn; subst.
          unfold lin_denote, priv_fold; cbn. field.
        +
          destruct (snorm a) as [(la, pa)|] eqn:hna; [| congruence].
          destruct (snorm b) as [(lb, pb)|] eqn:hnb; [| congruence].
          injection hn as hn; subst.
          cbn.
          rewrite (iha _ wenv eq_refl), (ihb _ wenv eq_refl).
          unfold lin_denote; cbn [fst snd peval].
          rewrite priv_fold_app.
          field.
        +
          destruct (snorm a) as [(la, pa)|] eqn:hna; [| congruence].
          destruct (snorm b) as [(lb, pb)|] eqn:hnb; [| congruence].
          destruct la as [|cxa la'].
          ++
            injection hn as hn; subst.
            cbn.
            rewrite (iha _ wenv eq_refl), (ihb _ wenv eq_refl).
            unfold lin_denote; cbn [fst snd peval].
            rewrite priv_fold_scale.
            unfold priv_fold; cbn.
            field.
          ++
            destruct lb as [|cxb lb']; [| congruence].
            injection hn as hn; subst.
            cbn.
            rewrite (iha _ wenv eq_refl), (ihb _ wenv eq_refl).
            unfold lin_denote; cbn [fst snd peval].
            change (((PMul pb (fst cxa), snd cxa) ::
              List.map (fun cx => (PMul pb (fst cx), snd cx))
                la')%list) with
              (List.map (fun cx => (PMul pb (fst cx), snd cx))
                ((cxa :: la')%list)).
            rewrite priv_fold_scale.
            unfold priv_fold; cbn.
            field.
        +
          destruct (snorm a) as [(la, pa)|] eqn:hna; [| congruence].
          injection hn as hn; subst.
          cbn.
          rewrite (iha _ wenv eq_refl).
          unfold lin_denote; cbn [fst snd peval].
          rewrite priv_fold_opp.
          field.
      Qed.

      (* ------------- Surface normalization: group side ------------- *)

      Lemma gfold_app :
        ∀ (A : Type) (f : A -> G) (la lb : list A),
        List.fold_right (fun a acc => gop (f a) acc) gid
          (List.app la lb) =
        gop (List.fold_right (fun a acc => gop (f a) acc) gid la)
            (List.fold_right (fun a acc => gop (f a) acc) gid lb).
      Proof.
        intros A f.
        induction la as [|a la ih]; intros *; cbn.
        +
          rewrite left_identity; reflexivity.
        +
          rewrite ih, associative; reflexivity.
      Qed.

      Lemma gfold_map_inv :
        ∀ (A : Type) (f : A -> G) (g : A -> A) (la : list A),
        (∀ a, f (g a) = ginv (f a)) ->
        List.fold_right (fun a acc => gop (f a) acc) gid
          (List.map g la) =
        ginv (List.fold_right (fun a acc => gop (f a) acc) gid la).
      Proof.
        intros * hpt.
        induction la as [|a la ih]; cbn.
        +
          rewrite group_inv_id; reflexivity.
        +
          rewrite hpt, ih.
          rewrite group_inv_flip.
          rewrite commutative.
          reflexivity.
      Qed.

      Lemma gfold_map_pow :
        ∀ (A : Type) (f : A -> G) (g : A -> A) (k : F) (la : list A),
        (∀ a, f (g a) = (f a) ^ k) ->
        List.fold_right (fun a acc => gop (f a) acc) gid
          (List.map g la) =
        (List.fold_right (fun a acc => gop (f a) acc) gid la) ^ k.
      Proof.
        intros * hpt.
        induction la as [|a la ih]; cbn.
        +
          rewrite vid_identity; reflexivity.
        +
          rewrite hpt, ih, smul_distributive_vadd.
          reflexivity.
      Qed.

      Lemma term_denote_opp :
        ∀ (wenv : string -> F) (t : term),
        term_denote wenv
          (mkterm (POpp (t_coeff t)) (t_var t) (t_base t)) =
        ginv (term_denote wenv t).
      Proof.
        intros *; unfold term_denote; cbn.
        assert (ha : opp (peval penv (t_coeff t)) * wenv (t_var t) =
          opp (peval penv (t_coeff t) * wenv (t_var t))). field.
        rewrite ha.
        rewrite <-connection_between_vopp_and_fopp.
        reflexivity.
      Qed.

      Lemma off_denote_opp :
        ∀ (o : pexpr * string),
        off_denote (POpp (fst o), snd o) = ginv (off_denote o).
      Proof.
        intros *; unfold off_denote; cbn.
        rewrite <-connection_between_vopp_and_fopp.
        reflexivity.
      Qed.

      Lemma term_denote_scale :
        ∀ (wenv : string -> F) (k : pexpr) (t : term),
        term_denote wenv
          (mkterm (PMul k (t_coeff t)) (t_var t) (t_base t)) =
        (term_denote wenv t) ^ (peval penv k).
      Proof.
        intros *; unfold term_denote; cbn.
        rewrite smul_pow_up.
        assert (ha : peval penv k * peval penv (t_coeff t) *
          wenv (t_var t) =
          peval penv (t_coeff t) * wenv (t_var t) * peval penv k).
        field.
        rewrite ha; reflexivity.
      Qed.

      Lemma off_denote_scale :
        ∀ (k : pexpr) (o : pexpr * string),
        off_denote (PMul k (fst o), snd o) =
        (off_denote o) ^ (peval penv k).
      Proof.
        intros *; unfold off_denote; cbn.
        rewrite smul_pow_up.
        assert (ha : peval penv k * peval penv (fst o) =
          peval penv (fst o) * peval penv k).
        field.
        rewrite ha; reflexivity.
      Qed.

      (* one offset raised to a private linear form is a term list *)
      Lemma smul_priv_fold :
        ∀ (ls : list (pexpr * string)) (o : pexpr * string)
          (wenv : string -> F),
        (off_denote o) ^ (priv_fold wenv ls) =
        terms_fold wenv
          (List.map (fun cx =>
            mkterm (PMul (fst cx) (fst o)) (snd cx) (snd o)) ls).
      Proof.
        induction ls as [|cx ls ih]; intros *;
        unfold priv_fold, terms_fold in *; cbn.
        +
          rewrite field_zero; reflexivity.
        +
          rewrite smul_distributive_fadd.
          rewrite ih.
          f_equal.
          unfold term_denote, off_denote; cbn.
          rewrite smul_pow_up.
          assert (ha : peval penv (fst o) *
            (peval penv (fst cx) * wenv (snd cx)) =
            peval penv (fst cx) * peval penv (fst o) *
            wenv (snd cx)).
          field.
          rewrite ha; reflexivity.
      Qed.

      (* a pure-point value raised to a private linear form is the
         flat_map of the per-offset term lists *)
      Lemma off_fold_priv_pow :
        ∀ (oa ls : list (pexpr * string)) (wenv : string -> F),
        (off_fold oa) ^ (priv_fold wenv ls) =
        terms_fold wenv
          (List.flat_map (fun o =>
            List.map (fun cx =>
              mkterm (PMul (fst cx) (fst o)) (snd cx) (snd o)) ls)
            oa).
      Proof.
        induction oa as [|o oa ih]; intros *.
        +
          unfold off_fold, terms_fold; cbn.
          rewrite vid_identity; reflexivity.
        +
          unfold off_fold, terms_fold in ih |- *; cbn.
          rewrite smul_distributive_vadd.
          rewrite ih.
          pose proof (smul_priv_fold ls o wenv) as hs.
          unfold terms_fold in hs.
          rewrite hs.
          pose proof (gfold_app _ (term_denote wenv)
            (List.map (fun cx => mkterm (PMul (fst cx) (fst o))
              (snd cx) (snd o)) ls)
            (List.flat_map (fun o' =>
              List.map (fun cx => mkterm (PMul (fst cx) (fst o'))
                (snd cx) (snd o')) ls) oa)) as hap.
          rewrite hap.
          reflexivity.
      Qed.

      Lemma gnorm_correct :
        ∀ (e : gexpr) (ts : list term)
          (os : list (pexpr * string)) (wenv : string -> F),
        gnorm e = Some (ts, os) ->
        geval wenv e = gop (terms_fold wenv ts) (off_fold os).
      Proof.
        induction e as [| P | a iha b ihb | a iha | sc a iha];
        intros * hn; cbn in hn.
        +
          injection hn as h₁ h₂; subst.
          cbn.
          unfold terms_fold, off_fold; cbn.
          rewrite left_identity.
          reflexivity.
        +
          injection hn as h₁ h₂; subst.
          cbn.
          unfold terms_fold, off_fold, off_denote; cbn.
          rewrite field_one, right_identity, left_identity.
          reflexivity.
        +
          destruct (gnorm a) as [(ta, oa)|] eqn:hga; [| congruence].
          destruct (gnorm b) as [(tb, ob)|] eqn:hgb; [| congruence].
          injection hn as h₁ h₂; subst.
          cbn.
          rewrite (iha _ _ wenv eq_refl), (ihb _ _ wenv eq_refl).
          unfold terms_fold, off_fold.
          rewrite !gfold_app.
          rewrite gop_simp.
          reflexivity.
        +
          destruct (gnorm a) as [(ta, oa)|] eqn:hga; [| congruence].
          injection hn as h₁ h₂; subst.
          cbn.
          rewrite (iha _ _ wenv eq_refl).
          unfold terms_fold, off_fold.
          rewrite (gfold_map_inv _ _ _ ta (term_denote_opp wenv)).
          rewrite (gfold_map_inv _ _ _ oa off_denote_opp).
          rewrite group_inv_flip.
          rewrite commutative.
          reflexivity.
        +
          destruct (snorm sc) as [(ls, ps)|] eqn:hs; [| congruence].
          destruct (gnorm a) as [(ta, oa)|] eqn:hga; [| congruence].
          destruct ta as [|t₀ ta'].
          ++
            destruct ls as [|cx₀ ls'].
            +++
              injection hn as h₁ h₂; subst.
              cbn.
              rewrite (iha _ _ wenv eq_refl).
              rewrite (snorm_correct sc _ wenv hs).
              unfold lin_denote; cbn [fst snd].
              assert (hz : priv_fold wenv Datatypes.nil +
                peval penv ps = peval penv ps).
              unfold priv_fold; cbn; field.
              rewrite hz.
              unfold terms_fold at 1, off_fold at 1; cbn.
              rewrite left_identity.
              unfold terms_fold, off_fold; cbn.
              rewrite left_identity.
              symmetry.
              eapply (gfold_map_pow _ _ _ _ oa
                (off_denote_scale ps)).
            +++
              injection hn as h₁ h₂; subst.
              cbn.
              rewrite (iha _ _ wenv eq_refl).
              rewrite (snorm_correct sc _ wenv hs).
              unfold lin_denote; cbn [fst snd].
              unfold terms_fold at 1, off_fold at 1; cbn.
              rewrite left_identity.
              rewrite smul_distributive_fadd.
              pose proof (off_fold_priv_pow oa
                ((cx₀ :: ls')%list) wenv) as hp.
              unfold off_fold, priv_fold, terms_fold in hp;
              cbn in hp.
              rewrite hp.
              f_equal.
              symmetry.
              unfold off_fold.
              eapply (gfold_map_pow _ _ _ _ oa
                (off_denote_scale ps)).
          ++
            destruct ls as [|]; [| congruence].
            injection hn as h₁ h₂; subst.
            cbn.
            rewrite (iha _ _ wenv eq_refl).
            rewrite (snorm_correct sc _ wenv hs).
            unfold lin_denote; cbn [fst snd].
            assert (hz : priv_fold wenv Datatypes.nil +
              peval penv ps = peval penv ps).
            unfold priv_fold; cbn; field.
            rewrite hz.
            rewrite smul_distributive_vadd.
            unfold terms_fold, off_fold.
            rewrite <-(gfold_map_pow _ _ _ _ ((t₀ :: ta')%list)
              (term_denote_scale wenv ps)).
            rewrite <-(gfold_map_pow _ _ _ _ oa
              (off_denote_scale ps)).
            cbn [List.map].
            reflexivity.
      Qed.

      (* ------------- Elaboration correctness ------------- *)

      Lemma elab_eq_correct :
        ∀ (l r : gexpr) (e : equation) (wenv : string -> F),
        elab_eq l r = Some e ->
        (eq_denote wenv e <-> geval wenv l = geval wenv r).
      Proof.
        intros * he.
        unfold elab_eq in he.
        destruct (gnorm (GAddE r (GInvE l))) as [(ts, os)|] eqn:hg;
        [| congruence].
        injection he as he; subst.
        unfold eq_denote.
        cbn [eq_rhs eq_off].
        pose proof (gnorm_correct _ _ _ wenv hg) as hv.
        cbn in hv.
        rewrite <-hv.
        rewrite gop_eq_gid_iff, group_inv_inv.
        split; intro h; symmetry; exact h.
      Qed.

      (* the neq-free fragment elaborates to an equivalent statement *)
      Lemma elab_correct_pos :
        ∀ (An Bn : string) (ss : sstmt) (s : stmt)
          (wenv : string -> F),
        neq_free ss = true ->
        elab An Bn ss = Some s ->
        (stmt_denote wenv s <-> sstmt_denote wenv ss).
      Proof.
        intros An Bn ss.
        induction ss as [l r | a b | a iha b ihb | a iha b ihb];
        intros * hf hn; cbn [neq_free] in hf; cbn [elab] in hn.
        +
          destruct (elab_eq l r) as [e|] eqn:he; [| congruence].
          injection hn as hn; subst.
          cbn; split.
          ++
            intro hd.
            inversion hd as [|? ? hb hc]; subst.
            exact (proj1 (elab_eq_correct _ _ _ wenv he) hb).
          ++
            intro hd.
            constructor; [| constructor].
            exact (proj2 (elab_eq_correct _ _ _ wenv he) hd).
        +
          congruence.
        +
          eapply andb_true_iff in hf.
          destruct hf as (hfa & hfb).
          destruct (elab An Bn a) as [a'|] eqn:hea; [| congruence].
          destruct (elab An Bn b) as [b'|] eqn:heb; [| congruence].
          injection hn as hn; subst.
          cbn.
          rewrite (iha _ wenv hfa eq_refl), (ihb _ wenv hfb eq_refl).
          reflexivity.
        +
          eapply andb_true_iff in hf.
          destruct hf as (hfa & hfb).
          destruct (elab An Bn a) as [a'|] eqn:hea; [| congruence].
          destruct (elab An Bn b) as [b'|] eqn:heb; [| congruence].
          injection hn as hn; subst.
          cbn.
          rewrite (iha _ wenv hfa eq_refl), (ihb _ wenv hfb eq_refl).
          reflexivity.
      Qed.

      (* full elaboration soundness, not-equals included: a witness
         environment of the elaborated statement satisfies the
         surface statement, or exhibits a dlog relation between the
         cind bases *)
      Lemma elab_sound :
        ∀ (An Bn : string) (ss : sstmt) (s : stmt)
          (wenv : string -> F),
        elab An Bn ss = Some s ->
        stmt_denote wenv s ->
        sstmt_denote wenv ss ∨ (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros An Bn ss.
        induction ss as [l r | a b | a iha b ihb | a iha b ihb];
        intros * hn hd; cbn [elab] in hn.
        +
          destruct (elab_eq l r) as [e|] eqn:he; [| congruence].
          injection hn as hn; subst.
          left; cbn.
          inversion hd as [|? ? hb hc]; subst.
          exact (proj1 (elab_eq_correct _ _ _ wenv he) hb).
        +
          destruct (snorm (SAddE a (SOppE b))) as [(l, off)|]
            eqn:hsn; cbn in hn; [| congruence].
          destruct l as [|cx l']; cbn in hn; [congruence |].
          destruct cx as (c, x).
          destruct l' as [|]; cbn in hn; [| congruence].
          injection hn as hn; subst.
          unfold neq_auto in hd.
          destruct (neq_sound _ _ _ _ _ _ _ _ _ _ hd)
            as [hne | hdlog].
          ++
            left; cbn.
            intro heq.
            eapply hne.
            pose proof (snorm_correct _ _ wenv hsn) as hsc.
            cbn in hsc.
            rewrite heq in hsc.
            assert (hz : seval wenv b + opp (seval wenv b) = zero).
            field.
            rewrite hz in hsc.
            assert (hw : peval penv c * wenv x + peval penv off =
              peval penv c * wenv x + zero + peval penv off).
            field.
            rewrite hw.
            symmetry; exact hsc.
          ++
            right; exact hdlog.
        +
          destruct (elab An Bn a) as [a'|] eqn:hea; [| congruence].
          destruct (elab An Bn b) as [b'|] eqn:heb; [| congruence].
          injection hn as hn; subst.
          cbn in hd.
          destruct hd as (hda & hdb).
          destruct (iha _ wenv eq_refl hda) as [ha | ha];
          [| right; exact ha].
          destruct (ihb _ wenv eq_refl hdb) as [hb | hb];
          [| right; exact hb].
          left; cbn; exact (conj ha hb).
        +
          destruct (elab An Bn a) as [a'|] eqn:hea; [| congruence].
          destruct (elab An Bn b) as [b'|] eqn:heb; [| congruence].
          injection hn as hn; subst.
          cbn in hd.
          destruct hd as [hd | hd].
          ++
            destruct (iha _ wenv eq_refl hd) as [ha | ha];
            [left; cbn; left; exact ha | right; exact ha].
          ++
            destruct (ihb _ wenv eq_refl hd) as [hb | hb];
            [left; cbn; right; exact hb | right; exact hb].
      Qed.

      (* ------------- Substitution semantics (A1) ------------- *)

      Lemma sexpr_subst_eval :
        ∀ (e : sexpr) (x : string) (v : sexpr)
          (wenv : string -> F),
        seval wenv (sexpr_subst x v e) =
        seval (override wenv x (seval wenv v)) e.
      Proof.
        induction e as [c | y | y | a iha b ihb | a iha b ihb | a iha];
        intros *; cbn;
        try (rewrite ?iha, ?ihb; reflexivity).
        destruct (String.eqb y x) eqn:h.
        +
          eapply String.eqb_eq in h; subst.
          unfold override.
          rewrite String.eqb_refl.
          reflexivity.
        +
          cbn.
          unfold override.
          rewrite String.eqb_sym in h.
          rewrite h.
          reflexivity.
      Qed.

      Lemma gexpr_subst_eval :
        ∀ (e : gexpr) (x : string) (v : sexpr)
          (wenv : string -> F),
        geval wenv (gexpr_subst x v e) =
        geval (override wenv x (seval wenv v)) e.
      Proof.
        induction e as [| P | a iha b ihb | a iha | sc a iha];
        intros *; cbn;
        rewrite ?iha, ?ihb, ?sexpr_subst_eval; reflexivity.
      Qed.

      Lemma sstmt_subst_denote :
        ∀ (ss : sstmt) (x : string) (v : sexpr)
          (wenv : string -> F),
        sstmt_denote wenv (sstmt_subst x v ss) <->
        sstmt_denote (override wenv x (seval wenv v)) ss.
      Proof.
        induction ss as [l r | a b | a iha b ihb | a iha b ihb];
        intros *; cbn.
        +
          rewrite !gexpr_subst_eval.
          reflexivity.
        +
          rewrite !sexpr_subst_eval.
          reflexivity.
        +
          rewrite (iha x v wenv), (ihb x v wenv).
          reflexivity.
        +
          rewrite (iha x v wenv), (ihb x v wenv).
          reflexivity.
      Qed.

      (* ------------- End-to-end surface theorems ------------- *)

      Theorem surface_protocol_completeness :
        ∀ (An Bn : string) (ss : sstmt) (s : stmt)
          (wenv : string -> F),
        neq_free ss = true ->
        elab An Bn ss = Some s ->
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        sstmt_denote wenv ss ->
        ∃ (w : comp_witnessC (compile s)),
          ∀ (rnd : comp_randC (compile s)) (c : F),
          comp_verifyC (compile s) c
            (comp_proveC (compile s) w rnd c) = true.
      Proof.
        intros * hf he hw hn hd.
        eapply (compile_protocol_completeness s wenv).
        exact hw. exact hn.
        eapply elab_correct_pos.
        exact hf. exact he. exact hd.
      Qed.

      Theorem surface_protocol_soundness :
        ∀ (An Bn : string) (ss : sstmt) (s : stmt) (c c' : F)
          (t t' : comp_transcriptC (compile s)),
        elab An Bn ss = Some s ->
        wf_stmt s = true ->
        nodupb (Vector.to_list privs) = true ->
        disj_inv s = true ->
        c <> c' ->
        comp_same_announcementC (compile s) t t' ->
        comp_verifyC (compile s) c t = true ->
        comp_verifyC (compile s) c' t' = true ->
        (∃ wenv : string -> F, sstmt_denote wenv ss) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * he hw hn hdisj hcc hsame hv₁ hv₂.
        destruct (compile_protocol_soundness s c c' t t'
          hw hn hdisj hcc hsame hv₁ hv₂) as (wenv & hwenv).
        destruct (elab_sound An Bn ss s wenv he hwenv) as [hd | hd].
        left; exists wenv; exact hd.
        right; exact hd.
      Qed.

      (* ------------- Vectors and SIMD ------------- *)

      Lemma big_sand_denote :
        ∀ (l : list sstmt) (s : sstmt) (wenv : string -> F),
        sstmt_denote wenv (big_sand s l) <->
        (sstmt_denote wenv s ∧ List.Forall (sstmt_denote wenv) l).
      Proof.
        induction l as [|a l ih]; intros *; cbn.
        +
          split.
          intro ha; exact (conj ha (List.Forall_nil _)).
          intros (ha & hb); exact ha.
        +
          split.
          ++
            intros (ha & hb).
            eapply ih in hb.
            destruct hb as (hbl & hbr).
            split; [exact hbl | constructor; [exact ha | exact hbr]].
          ++
            intros (ha & hb).
            inversion hb as [| ? ? hc hd]; subst.
            split; [exact hc | eapply ih; exact (conj ha hd)].
      Qed.

      Lemma big_gop_map_eval :
        ∀ (A : Type) (g : A -> gexpr) (l : list A) (e : gexpr)
          (wenv : string -> F),
        geval wenv (big_gop e (List.map g l)) =
        List.fold_right
          (fun i acc => gop (geval wenv (g i)) acc)
          (geval wenv e) l.
      Proof.
        intros A g.
        induction l as [|a l ih]; intros *; cbn.
        +
          reflexivity.
        +
          rewrite ih; reflexivity.
      Qed.

      (* The dot-product statement means exactly
           C = Π_{i<nv}  A@i ^ x@i
         — for every runtime length nv (compare
         sigma-compiler's dot_product.rs test, which checks
         vecsize ∈ {0,1,2,20} empirically). *)
      (* ------------- Range soundness (Milestone E) ------------- *)

      Lemma fnat_add : ∀ (a b : nat),
        fnat (a + b)%nat = fnat a + fnat b.
      Proof.
        induction a as [|a ih]; intros *; cbn.
        field.
        rewrite ih. field.
      Qed.

      Lemma fnat_mul : ∀ (a b : nat),
        fnat (a * b)%nat = fnat a * fnat b.
      Proof.
        induction a as [|a ih]; intros *; cbn.
        field.
        rewrite fnat_add, ih. field.
      Qed.

      Lemma fmul_zero_factor : ∀ (a b : F),
        a * b = zero -> a = zero ∨ b = zero.
      Proof.
        intros * ha.
        destruct (Fdec a zero) as [hz | hnz].
        left; exact hz.
        right.
        assert (hb : b = inv a * (a * b)). field. exact hnz.
        rewrite hb, ha. field. exact hnz.
      Qed.

      Lemma bitof_fnat : ∀ (v : F),
        v = zero ∨ v = one ->
        fnat (bitof v) = v.
      Proof.
        intros * ha.
        unfold bitof.
        destruct (Fdec v zero) as [hz | hnz].
        +
          cbn. rewrite hz. reflexivity.
        +
          destruct ha as [ha | ha]; [congruence |].
          cbn. rewrite ha. field.
      Qed.

      (* the b = b² dichotomy for one bit *)
      Lemma bit_dichotomy :
        ∀ (Cb An Bn b r sn : string) (wenv : string -> F),
        eq_denote wenv (commit_eq Cb An Bn b r) ->
        eq_denote wenv (simple_eq Cb
          (List.cons (mkterm (PConst one) b Cb)
            (List.cons (mkterm (PConst one) sn Bn) List.nil))) ->
        (wenv b = zero ∨ wenv b = one) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * h₁ h₂.
        eapply commit_eq_denote in h₁.
        rewrite simple_eq_denote in h₂.
        unfold terms_fold, term_denote in h₂; cbn in h₂.
        rewrite right_identity in h₂.
        rewrite h₁ in h₂.
        rewrite smul_distributive_vadd, !smul_pow_up in h₂.
        rewrite <-associative in h₂.
        rewrite <-smul_distributive_fadd in h₂.
        assert (ha : wenv b * (one * wenv b) = wenv b * wenv b).
        field.
        rewrite ha in h₂.
        destruct (pedersen_binding_dichotomy _ _ _ _ _ _ h₂)
          as [heq | hdlog]; [| right; exact hdlog].
        left.
        assert (hz : wenv b * (one + opp (wenv b)) = zero).
        assert (hh : wenv b * (one + opp (wenv b)) =
          wenv b + opp (wenv b * wenv b)). field.
        rewrite hh, <-heq. field.
        destruct (fmul_zero_factor _ _ hz) as [h0 | h1].
        left; exact h0.
        right.
        assert (hh : wenv b = one + opp (one + opp (wenv b))).
        field.
        rewrite hh, h1. field.
      Qed.

      (* the A-power collapse of the linking equation *)
      Lemma range_terms_fold :
        ∀ (An x : string) (iws : list (nat * nat))
          (wenv : string -> F),
        terms_fold wenv
          (List.map (fun iw =>
            mkterm (PConst (opp (fnat (snd iw))))
              (bit_b x (fst iw)) An) iws) =
        (genv An) ^
          (List.fold_right (fun iw acc =>
            opp (fnat (snd iw)) * wenv (bit_b x (fst iw)) + acc)
            zero iws).
      Proof.
        induction iws as [|iw iws ih]; intros *;
        unfold terms_fold in *; cbn.
        +
          rewrite field_zero; reflexivity.
        +
          rewrite ih.
          rewrite smul_distributive_fadd.
          unfold term_denote; cbn.
          reflexivity.
      Qed.

      Lemma fold_opp_coeff :
        ∀ (x : string) (iws : list (nat * nat))
          (wenv : string -> F),
        List.fold_right (fun iw acc =>
          opp (fnat (snd iw)) * wenv (bit_b x (fst iw)) + acc)
          zero iws =
        opp (List.fold_right (fun iw acc =>
          fnat (snd iw) * wenv (bit_b x (fst iw)) + acc)
          zero iws).
      Proof.
        induction iws as [|iw iws ih]; intros *; cbn.
        field.
        rewrite ih. field.
      Qed.

      Lemma range_link_sound :
        ∀ (An x : string) (iws : list (nat * nat))
          (wenv : string -> F),
        eq_denote wenv (range_link An x iws) ->
        (genv An = gid) ∨
        (wenv x = List.fold_right (fun iw acc =>
          fnat (snd iw) * wenv (bit_b x (fst iw)) + acc)
          zero iws).
      Proof.
        intros * hd.
        unfold eq_denote, range_link in hd; cbn in hd.
        rewrite right_identity in hd.
        pose proof (range_terms_fold An x iws wenv) as hf.
        unfold terms_fold in hf; cbn in hf.
        rewrite hf in hd.
        unfold term_denote in hd; cbn in hd.
        rewrite <-smul_distributive_fadd in hd.
        destruct (@gid_power_zero F (@eq F) zero one add mul sub div
          opp inv G (@eq G) gid ginv gop gpow Hvec Fdec _ _ hd)
          as [hg | hz].
        left; exact hg.
        right.
        rewrite fold_opp_coeff in hz.
        assert (hh : wenv x =
          one * wenv x +
          opp (List.fold_right (fun iw acc =>
            fnat (snd iw) * wenv (bit_b x (fst iw)) + acc)
            zero iws) +
          List.fold_right (fun iw acc =>
            fnat (snd iw) * wenv (bit_b x (fst iw)) + acc)
            zero iws).
        field.
        rewrite hh, hz. field.
      Qed.

      (* good bits: the F-value fold is the embedding of the
         nat-side weighted bit sum *)
      Lemma range_bits_value :
        ∀ (x : string) (iws : list (nat * nat))
          (wenv : string -> F),
        (∀ iw, List.In iw iws ->
          wenv (bit_b x (fst iw)) = zero ∨
          wenv (bit_b x (fst iw)) = one) ->
        List.fold_right (fun iw acc =>
          fnat (snd iw) * wenv (bit_b x (fst iw)) + acc)
          zero iws =
        fnat (List.fold_right (fun iw acc =>
          (snd iw * bitof (wenv (bit_b x (fst iw)))) + acc)%nat
          0%nat iws).
      Proof.
        induction iws as [|iw iws ih]; intros * hb; cbn.
        reflexivity.
        rewrite fnat_add, fnat_mul.
        rewrite (bitof_fnat _ (hb iw (or_introl eq_refl))).
        rewrite ih.
        reflexivity.
        intros iw' hin; eapply hb; right; exact hin.
      Qed.

      (* ---- nat side: the weighted bit sum is below u ---- *)

      Lemma fold_add_base : ∀ (l : list nat) (b : nat),
        (List.fold_right Nat.add b l =
         List.fold_right Nat.add 0 l + b)%nat.
      Proof.
        induction l as [|a l ih]; intros *; cbn.
        lia.
        rewrite ih; lia.
      Qed.

      Lemma pow2_sum : ∀ (m : nat),
        (List.fold_right Nat.add 0
          (List.map (fun i => Nat.pow 2 i) (List.seq 0 m)) =
          Nat.pow 2 m - 1)%nat.
      Proof.
        induction m as [|m ih].
        reflexivity.
        rewrite List.seq_S, List.map_app, List.fold_right_app.
        cbn.
        rewrite fold_add_base, ih.
        assert (hp : Nat.pow 2 m <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; lia.
        cbn [Nat.pow].
        lia.
      Qed.

      Lemma sum_mono :
        ∀ (x : string) (iws : list (nat * nat))
          (wenv : string -> F),
        (List.fold_right (fun iw acc =>
          (snd iw * bitof (wenv (bit_b x (fst iw)))) + acc)%nat
          0%nat iws <=
        List.fold_right (fun iw acc => (snd iw + acc)%nat)
          0%nat iws)%nat.
      Proof.
        induction iws as [|iw iws ih]; intros *; cbn.
        lia.
        pose proof (ih wenv).
        assert (hb : (bitof (wenv (bit_b x (fst iw))) <= 1)%nat).
        unfold bitof;
        destruct (Fdec (wenv (bit_b x (fst iw))) zero); lia.
        nia.
      Qed.

      Lemma snd_fold_combine :
        ∀ (ws : list nat) (a : nat),
        (List.fold_right (fun iw acc => (snd iw + acc)%nat) 0%nat
          (List.combine (List.seq a (List.length ws)) ws) =
        List.fold_right Nat.add 0%nat ws)%nat.
      Proof.
        induction ws as [|w ws ih]; intros *; cbn.
        reflexivity.
        rewrite ih.
        reflexivity.
      Qed.

      Lemma weights_sum : ∀ (u : nat),
        (2 <= u)%nat ->
        (List.fold_right Nat.add 0 (range_weights u) = u - 1)%nat.
      Proof.
        intros * hu.
        unfold range_weights.
        rewrite List.fold_right_app.
        cbn.
        rewrite fold_add_base, pow2_sum.
        destruct (PeanoNat.Nat.log2_spec u) as (hl & hr); [lia |].
        assert (hp : Nat.pow 2 (Nat.log2 u) <> 0%nat).
        eapply PeanoNat.Nat.pow_nonzero; lia.
        lia.
      Qed.

      (* ---- assembling the soundness theorem ---- *)

      Lemma forall_flat_map_in :
        ∀ (A B : Type) (P : B -> Prop) (f : A -> list B)
          (l : list A) (a : A),
        List.Forall P (List.flat_map f l) ->
        List.In a l ->
        List.Forall P (f a).
      Proof.
        intros * hf hin.
        rewrite List.Forall_forall in hf.
        rewrite List.Forall_forall.
        intros b hb.
        eapply hf.
        eapply List.in_flat_map.
        exists a; exact (conj hin hb).
      Qed.

      Lemma find_nonbit_none :
        ∀ (l : list (nat * nat)) (wenv : string -> F) (x : string),
        find_nonbit wenv x l = None ->
        ∀ iw, List.In iw l ->
        wenv (bit_b x (fst iw)) = zero ∨
        wenv (bit_b x (fst iw)) = one.
      Proof.
        induction l as [|iw l ih]; intros * hf iw' hin.
        destruct hin.
        cbn in hf.
        destruct (Fdec (wenv (bit_b x (fst iw))) zero) as [h0 | h0].
        +
          destruct hin as [hin | hin].
          subst; left; exact h0.
          eapply ih; eauto.
        +
          destruct (Fdec (wenv (bit_b x (fst iw))) one) as [h1 | h1];
          [| congruence].
          destruct hin as [hin | hin].
          subst; right; exact h1.
          eapply ih; eauto.
      Qed.

      Lemma find_nonbit_some :
        ∀ (l : list (nat * nat)) (wenv : string -> F)
          (x : string) (iw : nat * nat),
        find_nonbit wenv x l = Some iw ->
        List.In iw l ∧
        wenv (bit_b x (fst iw)) <> zero ∧
        wenv (bit_b x (fst iw)) <> one.
      Proof.
        induction l as [|iw₀ l ih]; intros * hf; cbn in hf.
        congruence.
        destruct (Fdec (wenv (bit_b x (fst iw₀))) zero).
        +
          destruct (ih _ _ _ hf) as (ha & hb & hc).
          split; [right; exact ha | exact (conj hb hc)].
        +
          destruct (Fdec (wenv (bit_b x (fst iw₀))) one).
          ++
            destruct (ih _ _ _ hf) as (ha & hb & hc).
            split; [right; exact ha | exact (conj hb hc)].
          ++
            injection hf as hf; subst.
            split; [left; reflexivity | eauto].
      Qed.

      (* Range soundness: a witness of the lowered statement either
         places x in [0, u) — as the embedding of an integer — or
         yields a degenerate base (A = 1) or a dlog relation between
         the cind bases. *)
      Theorem range_sound :
        ∀ (An Bn x : string) (u : nat) (wenv : string -> F),
        (2 <= u)%nat ->
        stmt_denote wenv (range_stmt An Bn x u) ->
        (∃ k : nat, (k < u)%nat ∧ wenv x = fnat k) ∨
        (genv An = gid) ∨
        (∃ d : F, genv An = (genv Bn) ^ d).
      Proof.
        intros * hu hd.
        cbn in hd.
        inversion hd as [| ? ? hlink hbits]; subst.
        destruct (find_nonbit wenv x (indexed_weights u)) eqn:hf.
        +
          destruct (find_nonbit_some _ _ _ _ hf)
            as (hin & hnz & hno).
          pose proof (forall_flat_map_in _ _ _ _ _ _ hbits hin)
            as hbe.
          inversion hbe as [| ? ? he₁ hbe']; subst.
          inversion hbe' as [| ? ? he₂ hnil]; subst.
          destruct (bit_dichotomy _ _ _ _ _ _ wenv he₁ he₂)
            as [[h0 | h1] | hdlog].
          exfalso; eapply hnz; exact h0.
          exfalso; eapply hno; exact h1.
          right; right; exact hdlog.
        +
          destruct (range_link_sound _ _ _ _ hlink) as [hg | hv].
          right; left; exact hg.
          left.
          pose proof (find_nonbit_none _ _ _ hf) as hgood.
          rewrite (range_bits_value _ _ _ hgood) in hv.
          eexists; split; [| exact hv].
          pose proof (sum_mono x (indexed_weights u) wenv) as hm.
          pose proof (snd_fold_combine (range_weights u) 0) as hsf.
          pose proof (weights_sum u hu) as hws.
          unfold indexed_weights in *.
          lia.
      Qed.

      Theorem dot_product_denote :
        ∀ (nv : nat) (C x A : string) (wenv : string -> F),
        sstmt_denote wenv (dot_product_stmt C x A nv) <->
        genv C =
        List.fold_right
          (fun i acc =>
            gop ((genv (vname A i)) ^ (wenv (vname x i))) acc)
          gid (List.seq 0 nv).
      Proof.
        intros *.
        unfold dot_product_stmt, dot_terms.
        cbn [sstmt_denote].
        rewrite big_gop_map_eval.
        cbn [geval].
        reflexivity.
      Qed.

    End Proofs.

  End Spec.

  (* ---------------- Example: Schnorr ---------------- *)

  Section SchnorrExample.

    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.

    #[local] Open Scope string_scope.

    (* One private scalar x; the statement  H = G^x  *)
    Definition schnorr_privs : Vector.t string 1 := ["x"].

    Definition schnorr_stmt : stmt :=
      SLeaf (List.cons
        (simple_eq "H" (List.cons (mkterm (PConst one) "x" "G") List.nil))
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
          (simple_eq "H1" (List.cons (mkterm (PConst one) "x" "G")
            List.nil)) List.nil))
        (SLeaf (List.cons
          (simple_eq "H2" (List.cons (mkterm (PConst one) "y" "G")
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
          (simple_eq "C" (List.cons (mkterm (PConst one) "x" "G")
            List.nil)) List.nil))
        (SOr
          (SLeaf (List.cons
            (simple_eq "H1" (List.cons (mkterm (PConst one) "x" "G")
              List.nil)) List.nil))
          (SLeaf (List.cons
            (simple_eq "H2" (List.cons (mkterm (PConst one) "y" "G")
              List.nil)) List.nil))).

    Example bad_disj : disj_inv bad_stmt = false := eq_refl.

    (* The automated repair pass turns the rejected pattern into an
       accepted one; the checker, the pass, and its side conditions
       all run by computation. *)
    Definition bad_sc : stmt :=
      SLeaf (List.cons
        (simple_eq "C" (List.cons (mkterm (PConst one) "x" "G")
          List.nil)) List.nil).
    Definition bad_sa : stmt :=
      SLeaf (List.cons
        (simple_eq "H1" (List.cons (mkterm (PConst one) "x" "G")
          List.nil)) List.nil).
    Definition bad_sb : stmt :=
      SLeaf (List.cons
        (simple_eq "H2" (List.cons (mkterm (PConst one) "y" "G")
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
        rewrite simple_eq_denote in hb.
        exact hb.
        exact Hvec.
      +
        intro ha.
        constructor; [| constructor].
        rewrite simple_eq_denote.
        exact ha.
        exact Hvec.
    Qed.

  End SchnorrExample.

End Dsl.
