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
        @construct_eq_conversations_schnorr F add mul G gpow 1 x 
          [g; h] u c.
    
      (* simulator *)
      (* c₁ = g^x, c₂ = h^x *)
      Definition construct_cp_conversations_simulator 
        (g h : G) (c₁ c₂ : G) (u c : F) : @sigma_proto F G 2 1 1 := 
        @construct_eq_conversations_simulator F opp G gop gpow 1 
        [g; h] [c₁; c₂] u c.

      (* verifier *)
      Definition generalised_cp_accepting_conversations (g h : G) (c₁ c₂ : G) 
        (s : @sigma_proto F G 2 1 1) : bool := 
        @generalised_eq_accepting_conversations F G gop gpow Gdec 1 [g; h]
        [c₁; c₂] s.

      (* distribution involving witness *)
      Definition generalised_cp_schnorr_distribution  
        (lf : list F) (Hlfn : lf <> List.nil) (x : F)
        (g h : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_eq_schnorr_distribution F add mul G gpow 1 
          lf Hlfn x [g; h] c.

      (* Without secret *)
      Definition generalised_cp_simulator_distribution 
        (lf : list F) (Hlfn : lf <> List.nil) (g h : G)
        (c₁ c₂ : G) c : dist (@sigma_proto F G 2 1 1) :=
        @generalised_eq_simulator_distribution  F opp G gop 
        gpow 1 lf Hlfn [g; h] [c₁; c₂] c.


    End Def.

    Section Proofs.

    End Proofs.
  End CP.
End DL.