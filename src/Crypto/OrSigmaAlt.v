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
From Crypto Require Import Sigma.

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

        Definition compose_two_or_sigma_protocols {n m r u v w : nat} 
          (s₁ : @sigma_proto F G n m r) (s₂ : @sigma_proto F G u v w) :
          @sigma_proto F G (n + u) (m + v) (r + w) :=
        match s₁, s₂ with 
        |(a₁; c₁; r₁), (a₂; c₂; r₂) =>
          (a₁ ++ a₂; c₁ ++ c₂; r₁ ++ r₂)
        end.

        (* Does not involve the secret x *)
        (* gs hs us rs *)
        #[local]
        Definition construct_or_conversations_simulator_supplement :
          forall {n : nat}, 
          Vector.t G n ->  Vector.t G n -> Vector.t F n -> 
          Vector.t F n -> @sigma_proto F G n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun gs hs us rs => _
          | S n' => fun gs hs us rs  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S hs) as (hsh & hstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S rs) as (rsh & rstl & _).
            exact (compose_two_or_sigma_protocols 
              (@schnorr_simulator F opp G gop gpow gsh hsh ush rsh)
              (Fn _ gstl hstl ustl rstl)).
        Defined.


        (* Prover knows the ith relation *)
        (* The way out is that the verifier may let the prover “cheat” a 
          little bit by allowing the prover to use the simulator of the 
          Σ-protocol for the relation Ri for which the prover does not 
          know witness wi (i = 1 or i = 2). The verifier will do so by 
          providing a single challenge c which the prover is allowed to 
          split into two challenges c1, c2 provided c1, c2 satisfy a 
          linear constraint in terms of c. For example, the constraint 
          may be c = c1 ⊕ c2 if the challenges happen to be bit strings. 
          Essentially, the prover gets one degree of freedom to cheat. 
        *)
        (* 
          prover knowns ith relation 
          x is the secret 
          rs is randomly generated scalors 
          us = usl ++ [u_i] ++ usr
          rs = rsl ++ [_] ++ rsr 
          Prover recomputes: 
          r_i := c - Σ rsl + rsr 

          Uses simulator on (usl ++ usr) (rsl ++ rsr)
          Uses Schnorr protocol u_i r_i 
          Package them together.

          Verifier check the if all the individual 
          sigma protocols are valid and 
          challenges sum up to c.
        *)


        (* 
          x gs hs us rs c. 
          x is secret  
          gs and hs are public group elements 
          and prover knows the (m + 1)th relation.
          us and rs -- verifier let prover cheat -- are randomness 
          c is challenge

          Important: discuss this with Berry. 
        *)

         Definition construct_or_conversations_schnorr {m n : nat} :
          F -> Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros x gs hs usrs c.
          destruct (splitat (m + (1 + n)) usrs) as (us & rs).
          destruct (splitat m gs) as (gsl & gsrt).
          destruct (vector_inv_S gsrt) as (g & gsr & _).
          destruct (splitat m hs) as (hsl & hsrt).
          (* discard h because it is not needed in schnorr protocol *)
          destruct (vector_inv_S hsrt) as (_ & hsr & _).
          (* us := usl ++ [u_i] ++ usr *)
          destruct (splitat m us) as (usl & rurt).
          destruct (vector_inv_S rurt) as (u_i & usr & _).
          (* rs := rsl ++ [_] ++ rsr *)
          destruct (splitat m rs) as (rsl & rsr).
          (* compute r_i  *)
          remember (c - (Vector.fold_right add (rsl ++ rsr) zero)) 
          as r_i.
          (* we will return rsl ++ [r_i] ++ rsr in c field *)
          (* run simulator on gsl hsl usl rsl *)
          remember (construct_or_conversations_simulator_supplement 
            gsl hsl usl rsl) as Ha.
          (* run protocol for known relation *)
          remember (@schnorr_protocol F add mul G gpow x g u_i r_i) as Hb.
          (* run simulator on gsr hsr usr rsr *)
          remember (construct_or_conversations_simulator_supplement 
            gsr hsr usr rsr) as Hc.
          (* now combine all and put the 
            c at front of challenges *)
          refine 
            match Ha, Hb, Hc with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂), (a₃; c₃; r₃) => 
              ((a₁ ++ (a₂ ++ a₃)); c :: c₁ ++ (c₂ ++ c₃); (r₁ ++ (r₂ ++ r₃)))
            end.
        Defined.

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
            remember (construct_or_conversations_simulator_supplement 
              gsr hsr usr rsr) as Hb.
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
            remember (construct_or_conversations_simulator_supplement 
              gsr hsr usr (rew [Vector.t F] (plus_n_Sm m n) in rsr)) as Hb.
            (* now combine all and put the 
              c at front of challenges *)
            refine 
            match Ha, Hb with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂) => 
              ((a₁ ++ a₂); c :: c₁ ++ c₂; r₁ ++ r₂)
            end.
        Defined.

        #[local]
        Definition generalised_or_accepting_conversations_supplement : 
          forall {n : nat}, 
          Vector.t G n -> Vector.t G n ->
          @sigma_proto F G n n n -> bool.
        Proof.
          refine
            (fix Fn n := 
            match n with 
            | 0 => fun gs hs Ha => true
            | S n' => fun gs hs Ha => 
              match Ha with 
              | (a₁; c₁; r₁) => _ 
              end 
            end).
          destruct (vector_inv_S gs) as (g & gsr & _).
          destruct (vector_inv_S hs) as (h & hsr & _).
          destruct (vector_inv_S a₁) as (a & asr & _).
          destruct (vector_inv_S c₁) as (c & csr & _).
          destruct (vector_inv_S r₁) as (r & rsr & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([a]; [c]; [r])) && 
            (Fn _ gsr hsr (asr; csr; rsr))).
        Defined.


        (* verify or sigma protocol *)
        Definition generalised_or_accepting_conversations : 
          forall {m n : nat}, 
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)) ->
          bool.
        Proof.
          intros ? ? gs hs Ha.
          refine 
            match Ha with 
            |(a; ct; r) => _ 
            end.
          (* Verifier first checks if challenge c is equal 
            to the rest of challenges *)
          destruct (vector_inv_S ct) as (c & cs & _).
          refine
            match Fdec c (Vector.fold_right add cs zero) with 
            | left _ => 
                (* now check sigma *)
                generalised_or_accepting_conversations_supplement gs hs (a; cs; r)
            | right _ => false (* if it's false, there is 
              no point for checking further *)
            end.
        Defined.


        (* schnorr distribution *)
        Definition generalised_or_schnorr_distribution  
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (x : F) (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_schnorr x gs hs usrs c).

        (* simulator distribution *)
        Definition generalised_or_simulator_distribution  
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_simulator gs hs usrs c).

    End Def.


    Section Proofs.

    End Proofs.
  End Or.
End DL.