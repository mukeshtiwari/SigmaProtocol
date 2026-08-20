From Stdlib Require Import Utf8 ZArith
  Vector String List.
From Utility Require Import Zpstar.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl Nizk.
From Examples Require Import Prime.
Import Vspace Schnorr Zpfield
  VectorNotations.

(*
  A concrete instance of the verified compiler, over the same small
  Schnorr group (p = 5927, q = 2963, g = 4) used by the other
  executable examples in this repository.

  The statement is the compiled OR:

      "I know the discrete log of H1, or of H2, base G."

  The prover holds x = 3 with H1 = G^3 (and does not need the
  discrete log of H2 = G^5).  The exported wrappers (or_prove,
  or_verify, or_run_left, ...) have concrete types and are extracted
  to OCaml by src/Extraction (Compilerlib); the driver is
  src/Executable/Compilercode/main.ml.
*)
Section CompilerIns.

  (* Prime q *)
  Definition q : Z := 2963.

  (* Prime p *)
  Definition p : Z := 2 * q + 1.

  Theorem prime_q : Znumtheory.prime q.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  Theorem prime_p : Znumtheory.prime p.
  Proof.
    eapply is_prime_sqrt_correct.
    compute; reflexivity.
  Qed.

  Theorem safe_prime : p = (2 * q + 1)%Z.
  Proof. compute. exact eq_refl. Qed.

  (* the concrete field and group *)
  Definition F : Type := @Zp q.
  Definition G : Type := @Schnorr_group p q.

  Definition fzero : F := @Zpfield.zero q prime_q.
  Definition fone : F := @Zpfield.one q prime_q.
  Definition fadd : F -> F -> F := @zp_add q.
  Definition fmul : F -> F -> F := @zp_mul q.
  Definition fsub : F -> F -> F := @zp_sub q.
  Definition fopp : F -> F := @zp_opp q prime_q.
  Definition gone : G := @Schnorr.one p q prime_p prime_q.
  Definition gmul : G -> G -> G :=
    @mul_schnorr_group p q prime_p prime_q.
  Definition gpow : G -> F -> G :=
    @pow 2 p q safe_prime prime_p prime_q.
  Definition gdec : forall x y : G, {x = y} + {x <> y} :=
    @dec_zpstar p q.

  (* build a field element from an arbitrary integer *)
  Definition mk_field (z : Z) : F.
  Proof.
    refine {| Zpfield.v := Z.modulo z q; Zpfield.Hv := _ |}.
    eapply Z.mod_mod.
    intro ha; discriminate ha.
  Defined.

  (* witness x = 3 for the left branch; h2's dlog (5) is only used
     here to *construct* the public point h2 *)
  Definition xval : F :=
    {| Zpfield.v := 3; Zpfield.Hv := eq_refl : (3 mod q)%Z = 3%Z |}.
  Definition yval : F :=
    {| Zpfield.v := 5; Zpfield.Hv := eq_refl : (5 mod q)%Z = 5%Z |}.

  (* group generator (same as SigmaIns.v) *)
  Definition gen : G.
  Proof.
    refine
    {| Schnorr.v := 4;
       Ha := conj eq_refl eq_refl : (0 < 4 < p)%Z;
       Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod 4 q p)).
  Defined.

  Definition h1 : G := Eval compute in gpow gen xval.
  Definition h2 : G := Eval compute in gpow gen yval.

  (* ---------------- the DSL statement ---------------- *)

  #[local] Open Scope string_scope.

  Definition privsI : Vector.t string 2 := ["x"; "y"].

  Definition genvI : string -> G :=
    fun s =>
      if String.eqb s "G" then gen
      else if String.eqb s "H1" then h1
      else if String.eqb s "H2" then h2
      else gone.

  Definition penvI : string -> F := fun _ => fone.

  Definition or_stmtI : @stmt F :=
    SOr
      (SLeaf (List.cons (mkeq "H1"
        (List.cons (mkterm (PConst fone) "x" "G") List.nil))
        List.nil))
      (SLeaf (List.cons (mkeq "H2"
        (List.cons (mkterm (PConst fone) "y" "G") List.nil))
        List.nil)).

  (* the typechecker and the invariant checker run by computation *)
  Example or_wf : wf_stmt privsI or_stmtI = true := eq_refl.
  Example or_nodup : nodupb (Vector.to_list privsI) = true := eq_refl.
  Example or_disj : disj_inv or_stmtI = true := eq_refl.

  (* ---------------- the compiled protocol ---------------- *)

  Definition or_relI : @comp_rel G :=
    @compile F fadd fmul fopp G gone gmul gpow 2
      privsI genvI penvI or_stmtI.

  Definition or_witness_left (xv yv : F) :
    @comp_witness F G or_relI := inl [xv; yv].

  Definition or_witness_right (xv yv : F) :
    @comp_witness F G or_relI := inr [xv; yv].

  Definition or_rand (u₁ u₂ s₁ s₂ cs : F) :
    @comp_rand F G or_relI := ([u₁; u₂], [s₁; s₂], cs).

  Definition or_prove (w : @comp_witness F G or_relI)
    (rnd : @comp_rand F G or_relI) (c : F) :
    @comp_transcript F G or_relI :=
    @comp_prove F fadd fmul fsub fopp G gone gmul gpow
      or_relI w rnd c.

  Definition or_verify (c : F)
    (t : @comp_transcript F G or_relI) : bool :=
    @comp_verify F fsub G gone gmul gpow gdec or_relI c t.

  (* flatten the transcript for printing on the OCaml side:
     ((announcement, responses) per branch, left challenge) *)
  Definition or_transcript_flat
    (t : @comp_transcript F G or_relI) :
    (G * list F) * (G * list F) * F :=
    match t with
    | (tl, tr, c₁) =>
        ((Vector.hd (fst tl), Vector.to_list (snd tl)),
         (Vector.hd (fst tr), Vector.to_list (snd tr)),
         c₁)
    end.

  (* end-to-end runs used by the OCaml driver *)
  Definition or_run_left (u₁ u₂ s₁ s₂ cs c : F) :
    bool * ((G * list F) * (G * list F) * F) :=
    let t := or_prove (or_witness_left xval fzero)
               (or_rand u₁ u₂ s₁ s₂ cs) c in
    (or_verify c t, or_transcript_flat t).

  Definition or_run_right (u₁ u₂ s₁ s₂ cs c : F) :
    bool * ((G * list F) * (G * list F) * F) :=
    let t := or_prove (or_witness_right fzero yval)
               (or_rand u₁ u₂ s₁ s₂ cs) c in
    (or_verify c t, or_transcript_flat t).

End CompilerIns.
