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
From Utility Require Import Util. 
From ExtLib Require Import Monad. 
From Crypto Require Import 
  Sigma EqSigma.


Import MonadNotation 
  VectorNotations.

#[local] Open Scope monad_scope.

(* Discrete Logarithm Zero Knowlege Proof *) 
Section DL. 
  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}. 
    (* decidable equality on Field *)

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}. 
    (* decidable equality on G *)
    

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section CP.
    Section Def.
      (*     
          Chaum-Pedersen protocol is an instance of EQ-Sigma 
          x : randomness used for the encryption
          g, h and  (c₁, c₂) : public inputs 
          c : single challenge
          c₁ = g^x ∧ c₂ = h^x 

        
      *)
      Definition construct_cp_conversations_schnorr 
        (x : F) (g h : G) (u c : F) : @sigma_proto F G 2 1 1 := 
        @construct_eq_conversations_schnorr F add mul G gpow _ x 
          [g; h] u c.
    
      (* simulator *)
      (* c₁ = g^x, c₂ = h^x *)
      Definition construct_cp_conversations_simulator 
        (g h : G) (c₁ c₂ : G) (u c : F) : @sigma_proto F G 2 1 1 := 
        @construct_eq_conversations_simulator F opp G gop gpow _ 
        [g; h] [c₁; c₂] u c.

      (* verifier *)
      Definition generalised_cp_accepting_conversations (g h : G) (c₁ c₂ : G) 
        (s : @sigma_proto F G 2 1 1) : bool := 
        @generalised_eq_accepting_conversations F G gop gpow Gdec _ [g; h]
        [c₁; c₂] s.

      (* distribution involving witness *)
      Definition generalised_cp_schnorr_distribution  
        (lf : list F) (Hlfn : lf <> List.nil) (x : F)
        (g h : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_eq_schnorr_distribution F add mul G gpow _ 
          lf Hlfn x [g; h] c.

      (* Without secret *)
      Definition generalised_cp_simulator_distribution 
        (lf : list F) (Hlfn : lf <> List.nil) (g h : G)
        (c₁ c₂ : G) c : dist (@sigma_proto F G 2 1 1) :=
        @generalised_eq_simulator_distribution  F opp G gop 
        gpow _ lf Hlfn [g; h] [c₁; c₂] c.


    End Def.

    Section Proofs.

      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub 
          div opp inv G (@eq G) gid ginv gop gpow}
        {n : nat}
        (x : F) (* randomness used for encryption  *)
        (g h c₁ c₂ : G)
        (R : g^x = c₁ ∧ h^x = c₂).

      (* Completeness *)
      Lemma construct_cp_conversations_schnorr_completeness : 
        forall (u c : F),
        generalised_cp_accepting_conversations g h c₁ c₂
          (construct_cp_conversations_schnorr x g h u c) = true.
      Proof.
        intros *. destruct R as (Ra & Rb).
        eapply construct_eq_conversations_schnorr_completeness.
        intro f. 
        destruct (fin_inv_S _ f) as [ea | (fi & ea)].
        subst; cbn. exact eq_refl.
        destruct (fin_inv_S _ fi) as [eaa | (fii & eaa)].
        subst; cbn. exact eq_refl.
        refine match (fin_inv_0 fii) with end.
      Qed.

      (* simulator completeness *)
      Lemma construct_cp_conversations_simulator_completeness : 
        forall (u c : F),
        generalised_cp_accepting_conversations g h c₁ c₂
          (construct_cp_conversations_simulator g h c₁ c₂ u c) = true.
      Proof.
        intros *.
        eapply construct_eq_conversations_simulator_completeness.
        Unshelve. eapply Fdec.
      Qed.

      (* Soundness (POK) *)
      Lemma generalise_cp_sigma_soundness :
        forall (a : Vector.t G 2) 
        (cr₁ cr₂ : F) (r₁ r₂ : F),
        generalised_cp_accepting_conversations g h c₁ c₂ (a; [cr₁]; [r₁]) = true ->
        generalised_cp_accepting_conversations g h c₁ c₂ (a; [cr₂]; [r₂]) = true ->
        cr₁ <> cr₂ ->
        ∃ y : F, (forall (f : Fin.t 2),
          (nth [g; h] f)^y = (nth [c₁; c₂] f)).
      Proof.
        intros * ha hb hc.
        eapply generalise_eq_sigma_soundness
        with (a := a) (c₁ := cr₁)
        (c₂ := cr₂) (r₁ := r₁) (r₂ := r₂).
        exact ha. exact hb. exact hc.
        Unshelve. eapply Fdec.
      Qed.


      (* zero-knowledge *)
      Lemma generalised_cp_special_honest_verifier_zkp : 
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.map (fun '(a, p) => 
          (generalised_cp_accepting_conversations g h c₁ c₂ a, p))
          (@generalised_cp_schnorr_distribution lf Hlfn x g h c) = 
        List.map (fun '(a, p) => 
          (generalised_cp_accepting_conversations g h c₁ c₂ a, p))
          (@generalised_cp_simulator_distribution lf Hlfn g h c₁ c₂ c).
      Proof.
        intros *. destruct R as (Ra & Rb).
        eapply generalised_eq_special_honest_verifier_zkp.
        intro f. 
        destruct (fin_inv_S _ f) as [ea | (fi & ea)].
        subst; cbn.  exact eq_refl.
        destruct (fin_inv_S _ fi) as [eaa | (fii & eaa)].
        subst; cbn. exact eq_refl.
        refine match (fin_inv_0 fii) with end.
        Unshelve. eapply Fdec.
      Qed.

    End Proofs.
  End CP.
End DL.