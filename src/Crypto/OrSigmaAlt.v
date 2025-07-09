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
From Crypto Require Import Sigma OrSigma.

Import MonadNotation 
  VectorNotations EqNotations.

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


  Section Or. 

    (* Generalised Or composition where you know 1 out of n statements
      ∃ x : g₁^x = h₁ ∨ g₂^x = h₂ ∨ g₃^x= h₃ ... 
      
      Only difference between this and OrSigma.v is the simulator 
      definition and thereby proofs. 
    *)

    Section Def.

      
        (* simulator *)
        (* does not involve secret x *)
        (* Berry suggested to run the schnorr simulator for the first element *)
        Definition construct_or_conversations_simulator {m n : nat} :
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros gs hs usrs c.
          destruct m as [|m].
          +
            cbn in * |- .
            (* gs = g :: gsr *)
            destruct (vector_inv_S gs) as (g & (gsr & _)).
            (* hs = h :: hsr *)
            destruct (vector_inv_S hs) as (h & (hsr & _)).
            (* usrs = u :: usrsr *)
            destruct (vector_inv_S usrs) as (u & (usrsr & _)).
            (* compute r  *)
            remember (c - (Vector.fold_right add usrsr zero)) 
            as r.
            (* run schnorr simulator for the first element *)
            remember (@schnorr_simulator F opp G gop gpow g h u r) as Ha.
            (* run simulator on gsr hsr usr rsr *)
            destruct (splitat n usrsr) as (usr & rsr).
            remember (@OrSigma.construct_or_conversations_simulator_supplement 
              F opp G gop gpow n gsr hsr usr rsr) as Hb.
            (* now combine all and put the 
            c at front of challenges *)
            refine 
              match Ha, Hb with 
              |(a₁; c₁; r₁), (a₂; c₂; r₂) => 
                ((a₁ ++ a₂); c :: c₁ ++ c₂; r₁ ++ r₂)
              end.
          +
            cbn in * |- .
            (* gs = g :: gsr *)
            destruct (vector_inv_S gs) as (g & (gsr & _)).
            (* hs = h :: hsr *)
            destruct (vector_inv_S hs) as (h & (hsr & _)).
            (* usrs = u :: usrsr *)
            destruct (vector_inv_S usrs) as (u & (usrsr & _)).
            (* compute r  *)
            remember (c - (Vector.fold_right add usrsr zero)) 
            as r.
            (* run schnorr simulator for the first element *)
            remember (@schnorr_simulator F opp G gop gpow g h u r) as Ha.
            (* run simulator on gsr hsr usr rsr *)
            destruct (splitat (m + S n) usrsr) as (usr & rsr).
            remember (@OrSigma.construct_or_conversations_simulator_supplement 
              F opp G gop gpow _ gsr hsr usr (rew [Vector.t F] (plus_n_Sm m n) in rsr)) as Hb.
            (* now combine all and put the 
              c at front of challenges *)
            refine 
            match Ha, Hb with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂) => 
              ((a₁ ++ a₂); c :: c₁ ++ c₂; r₁ ++ r₂)
            end.
        Defined.

    End Def.


    Section Proofs.

    End Proofs.
  End Or.
End DL.