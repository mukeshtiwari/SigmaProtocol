From Coq Require Import Setoid
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
From Crypto Require Import Sigma.
  

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

  Section Parallel.

    Section Def. 

  
      Definition compose_two_parallel_sigma_protocols {n m r u v w : nat} 
        (s₁ : @sigma_proto F G n m r) (s₂ : @sigma_proto F G u v w) :
        @sigma_proto F G (n + u) (m + v) (r + w) :=
        match s₁, s₂ with 
        | (a₁; c₁; r₁), (a₂; c₂; r₂) =>
          (a₁ ++ a₂; c₁ ++ c₂; r₁ ++ r₂)
        end.


      

    End Def.
      
    Section Proofs.


    End Proofs.
  End Parallel.
End DL.