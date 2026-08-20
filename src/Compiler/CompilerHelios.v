From Stdlib Require Import Utf8 ZArith
  Vector String List Ascii
  DecimalString DecimalZ.
From Utility Require Import Zpstar Sha256.
From Crypto Require Import Sigma.
From Compiler Require Import
  LinearRelation Composition Dsl Nizk.
From Examples Require Import primeP primeQ.
Import Vspace Schnorr Zpfield
  VectorNotations.

(*
  Production-size instance of the verified compiler over the 2048-bit
  Helios safe-prime group (RFC-3526-style modulus), reusing the
  primality proofs already machine-checked in primeP.v / primeQ.v —
  no re-verification of primality is performed here.

  Same OR statement as CompilerIns.v ("I know the discrete log of H1
  or of H2"), now instantiated at the real Helios group; the exported
  wrappers are extracted and benchmarked in
  src/Executable/Compilercode.
*)
Section CompilerHelios.

  Definition q : Z := 61329566248342901292543872769978950870633559608669337131139375508370458778917%Z.

  Theorem prime_q : Znumtheory.prime q.
  Proof. eapply primeQ.prime_q. Qed.

  Definition p : Z := 16328632084933010002384055033805457329601614771185955389739167309086214800406465799038583634953752941675645562182498120750264980492381375579367675648771293800310370964745767014243638518442553823973482995267304044326777047662957480269391322789378384619428596446446984694306187644767462460965622580087564339212631775817895958409016676398975671266179637898557687317076177218843233150695157881061257053019133078545928983562221396313169622475509818442661047018436264806901023966236718367204710755935899013750306107738002364137917426595737403871114187750804346564731250609196846638183903982387884578266136503697493474682071%Z.

  Theorem prime_p : Znumtheory.prime p.
  Proof. eapply primeP.prime_p. Qed.

  Definition k : Z := Z.div p q.

  Theorem safe_prime : p = (k * q + 1)%Z.
  Proof. vm_cast_no_check (eq_refl p). Qed.

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
    @pow k p q safe_prime prime_p prime_q.
  Definition gdec : forall x y : G, {x = y} + {x <> y} :=
    @dec_zpstar p q.
  Definition ginv_g : G -> G :=
    @inv_schnorr_group k p q safe_prime prime_p prime_q.

  Definition mk_field (z : Z) : F.
  Proof.
    refine {| Zpfield.v := Z.modulo z q; Zpfield.Hv := _ |}.
    eapply Z.mod_mod.
    intro ha; discriminate ha.
  Defined.

  (* small secret exponents suffice to exercise the group *)
  Definition xval : F := mk_field 3.
  Definition yval : F := mk_field 5.

  Definition gval : Z := 14887492224963187634282421537186040801304008017743492304481737382571933937568724473847106029915040150784031882206090286938661464458896494215273989547889201144857352611058572236578734319505128042602372864570426550855201448111746579871811249114781674309062693442442368697449970648232621880001709535143047913661432883287150003429802392229361583608686643243349727791976247247948618930423866180410558458272606627111270040091203073580238905303994472202930783207472394578498507764703191288249547659899997131166130259700604433891232298182348403175947450284433411265966789131024573629546048637848902243503970966798589660808533%Z.

  Definition gen : G.
  Proof.
    refine
    {| Schnorr.v := gval;
       Ha := conj eq_refl eq_refl : (0 < gval < p)%Z;
       Hb := _ |}.
    vm_cast_no_check (eq_refl (Zpow_facts.Zpow_mod gval q p)).
  Defined.

  (* left lazy: computed by extracted OCaml (fast via zarith),
     avoiding two 2048-bit kernel modexps at compile time *)
  Definition h1 : G := gpow gen xval.
  Definition h2 : G := gpow gen yval.

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
      (SLeaf (List.cons (@simple_eq F fone "H1"
        (List.cons (mkterm (PConst fone) "x" "G") List.nil))
        List.nil))
      (SLeaf (List.cons (@simple_eq F fone "H2"
        (List.cons (mkterm (PConst fone) "y" "G") List.nil))
        List.nil)).

  Example or_wf : wf_stmt privsI or_stmtI = true := eq_refl.
  Example or_nodup : nodupb (Vector.to_list privsI) = true := eq_refl.
  Example or_disj : disj_inv or_stmtI = true := eq_refl.

  Definition or_relI : @comp_rel G :=
    @compile F fadd fmul fopp G gone ginv_g gmul gpow 2
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

  Definition or_transcript_flat
    (t : @comp_transcript F G or_relI) :
    (G * list F) * (G * list F) * F :=
    match t with
    | (tl, tr, c₁) =>
        ((Vector.hd (fst tl), Vector.to_list (snd tl)),
         (Vector.hd (fst tr), Vector.to_list (snd tr)),
         c₁)
    end.

  Definition g_to_string (g : G) : string :=
    NilEmpty.string_of_int (Z.to_int (@Schnorr.v p q g)).

  Definition or_hash (a : @comp_ann_t G or_relI) : F :=
    mk_field (Z.of_N (sha256_string (String.concat ","
      (List.cons (g_to_string gen)
      (List.cons (g_to_string h1)
      (List.cons (g_to_string h2)
      (List.cons (g_to_string (Vector.hd (fst a)))
      (List.cons (g_to_string (Vector.hd (snd a)))
        List.nil)))))))).

  Definition or_nizk_prove
    (w : @comp_witness F G or_relI)
    (rnd : @comp_rand F G or_relI) :
    @comp_transcript F G or_relI :=
    @nizk_prove F fzero fadd fmul fsub fopp G gone gmul gpow
      or_relI or_hash w rnd.

  Definition or_nizk_verify
    (t : @comp_transcript F G or_relI) : bool :=
    @nizk_verify F fsub G gone gmul gpow gdec or_relI or_hash t.

  Definition or_nizk_run_left (u₁ u₂ s₁ s₂ cs : F) :
    bool * ((G * list F) * (G * list F) * F) :=
    let t := or_nizk_prove (or_witness_left xval fzero)
               (or_rand u₁ u₂ s₁ s₂ cs) in
    (or_nizk_verify t, or_transcript_flat t).

  Definition or_nizk_run_right (u₁ u₂ s₁ s₂ cs : F) :
    bool * ((G * list F) * (G * list F) * F) :=
    let t := or_nizk_prove (or_witness_right fzero yval)
               (or_rand u₁ u₂ s₁ s₂ cs) in
    (or_nizk_verify t, or_transcript_flat t).

End CompilerHelios.
