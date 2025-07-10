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
        Definition construct_or_conversations_simulator_alt {m n : nat} :
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros gs hs usrs c.
          (* separate us and rs *)
          destruct (splitat (m + (1 + n)) usrs) as (us & rs).
          destruct m as [|m].
          +
            cbn in * |- .
            (* gs = g :: gsr *)
            destruct (vector_inv_S gs) as (g & (gsr & _)).
            (* hs = h :: hsr *)
            destruct (vector_inv_S hs) as (h & (hsr & _)).
            (* us = u :: ust *)
            destruct (vector_inv_S us) as (u & (usr & _)).
            (* compute r  *)
            remember (c - (Vector.fold_right add rs zero)) 
            as r.
            (* run schnorr simulator for the first element *)
            remember (@schnorr_simulator F opp G gop gpow g h u r) as Ha.
            remember (@OrSigma.construct_or_conversations_simulator_supplement 
              F opp G gop gpow n gsr hsr usr rs) as Hb.
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
            destruct (vector_inv_S us) as (u & (usr & _)).
            (* compute r  *)
            remember (c - (Vector.fold_right add rs zero)) 
            as r.
            (* run schnorr simulator for the first element *)
            remember (@schnorr_simulator F opp G gop gpow g h u r) as Ha.
            remember (@OrSigma.construct_or_conversations_simulator_supplement 
              F opp G gop gpow _ gsr hsr usr (rew [Vector.t F] (plus_n_Sm m n) in rs)) as Hb.
            (* now combine all and put the 
              c at front of challenges *)
            refine 
            match Ha, Hb with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂) => 
              ((a₁ ++ a₂); c :: c₁ ++ c₂; r₁ ++ r₂)
            end.
        Defined.


        (* alternate simulator distribution *)
        Definition generalised_or_simulator_distribution_alt 
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_simulator_alt gs hs usrs c).

    End Def.

    Section Proofs.

        Theorem fold_righ_rew : forall (n m : nat) (rs : Vector.t F n) (e : n = m), 
          fold_right add rs zero = fold_right add (rew [t F] e in rs) zero.
        Proof.
          intros *. subst. 
          exact eq_refl.
        Qed.


        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).


        (* prove that simulator is correct and it's distribution is same Schnorr one *)
           
        Context
          {m n : nat}
          (gsl : Vector.t G m) 
          (gsr : Vector.t G n)
          (x : F) (* secret witness *)
          (g h : G) (* public values *)
          (hsl : Vector.t G m) 
          (hsr : Vector.t G n) 
          (R : h = g ^ x).  (* Prover knows (m + 1)th relation *)
      

        (*alt simulator completeness*)

        Lemma construct_or_conversations_simulator_completeness : 
          ∀ (usrs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          @OrSigma.generalised_or_accepting_conversations F zero add Fdec 
            G gop gpow Gdec m n (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
            (construct_or_conversations_simulator_alt
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
              usrs c) = true.
        Proof using -(x R).
          clear x R.
          intros *.
          destruct m as [|m'].
          +
            unfold generalised_or_accepting_conversations,
            construct_or_conversations_simulator_alt.
            cbn in * |- *.
            assert (hb : gsl = []). eapply vector_inv_0.
            assert (hc : hsl = []). eapply vector_inv_0.
            subst. cbn in * |- *.  
            destruct (vector_inv_S usrs) as (u & usrsr & ha).
            rewrite ha. cbn.
            destruct (splitat n usrsr) as (usr & rs) eqn:hb.
            cbn.
            remember (@OrSigma.construct_or_conversations_simulator_supplement F opp G gop 
              gpow _ gsr hsr usr rs) as sa.
            refine
            (match sa as s'
            return sa = s' -> _ with 
            |(a₁; c₁; r₁) => fun Hg => _  
            end eq_refl).
            cbn.
            assert (hc : c = (c - fold_right add rs zero + fold_right add c₁ zero)).
            rewrite Hg in Heqsa.
            eapply construct_or_conversations_simulator_challenge in Heqsa.
            rewrite <-Heqsa. field.
            rewrite <-hc.
            destruct (Fdec c c) as [Hk | Hk]; try congruence.
            eapply andb_true_iff; split.
            ++ 
              rewrite dec_true.
              remember (c - fold_right add rs zero) as ct.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
              zero one add mul sub div 
              opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              rewrite <-Hg, Heqsa.  
              eapply OrSigma.construct_or_conversations_simulator_completeness_supplement. 
          +
            unfold generalised_or_accepting_conversations,
            construct_or_conversations_simulator_alt.
            cbn in * |- *.
            destruct (vector_inv_S gsl) as (gh & gslr & ha).
            destruct (vector_inv_S hsl) as (hh & hslr & hb).
            subst. cbn.
            destruct (vector_inv_S usrs) as (u & usrsr & ha).
            rewrite ha. cbn.
            destruct (splitat (m' + S n) usrsr) as (usr & rs) eqn:hb.
            cbn.
            remember (OrSigma.construct_or_conversations_simulator_supplement
            (gslr ++ g :: gsr) (hslr ++ h :: hsr) usr
            (rew [t F] plus_n_Sm m' n in rs))  as sa.
            refine
            (match sa as s'
            return sa = s' -> _ with 
            |(a₁; c₁; r₁) => fun Hg => _  
            end eq_refl).
            cbn.
            assert (hc : c = (c - fold_right add rs zero + fold_right add c₁ zero)).
            rewrite Hg in Heqsa.
            eapply construct_or_conversations_simulator_challenge in Heqsa.
            rewrite <-Heqsa, <-fold_righ_rew.
            field.
            rewrite <-hc.
            destruct (Fdec c c) as [Hk | Hk]; try congruence.
            eapply andb_true_iff; split.
            ++ 
              rewrite dec_true.
              remember (c - fold_right add rs zero) as ct.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
              zero one add mul sub div 
              opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              rewrite <-Hg, Heqsa.  
              eapply OrSigma.construct_or_conversations_simulator_completeness_supplement.
          Unshelve. 
          eapply Fdec.
          eapply Fdec.
        Qed.

    End Proofs.
  End Or.
End DL.