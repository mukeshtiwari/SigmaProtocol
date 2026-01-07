From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef 
  BinPos Arith Eqdep_dec.
From Algebra Require Import 
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import 
  Prob Distr. 
From Utility Require Import Util. 
From ExtLib Require Import Monad. 
From Crypto Require Import Sigma 
  AndSigmaGen Okamoto.

Import MonadNotation 
  VectorNotations 
  EqNotations.
          
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

  #[local] Notation "( a ; c ; r )" := 
    (mk_sigma _ _ _ a c r).

  Section Neq.

     (* 
          In this section, we prove that 
          ∃ x₁ x₂ x₃ : g^x₁ = h₁ ∧ g^x₂ = h₂ ∧ g^x₃ = h₃ .... 
          ∧ x₁ <> x₂ ∧ x₁ <> x₃ ∧ x₁ <> ..... ∧ 
          x₂ <> x₃ <> x₂ <> x₄ ...... 
          ...
          ..
          .
      *)
    Section Def. 


       

       (* 
          xs : secrets 
          gs  hs : public values such h := g^x 
          us: randomness 
          c : challenge  

          O (n^2) proof terms! 
          Is there efficient way to model NEQ
        
          Key question: how much randomness I need? 
          We have (2 + n) gs and hs and for 
          (2 * (1 + n) + 2 * n + ...... + 2 = 
          (1 + n) (2 + n)

          The amount of randomenss I need is : ((2 + n) + ((2 + n) * (1 + n)))
        *)
        

       
        Definition generalised_construct_neq_commitment {n : nat} : 
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> 
          Vector.t G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2).
        Proof.
          intros gs hs us.
          (* split the randomness us at 2 + n *)
          destruct (splitat (2 + n) us) as (usl & usr).
          (* usl for AND commitment and usr for Okamoto protocol *)
          set (and_commit := @construct_and_conversations_schnorr_commitment
            F G gpow _ gs usl).
          (* construct gs pairs*)
          set (gs_pairs := Vector.map (fun '(g₁, g₂) => gop g₁ g₂)
            (generate_pairs_of_vector gs)).
          set (hs_pairs := Vector.map (fun '(h₁, h₂) => gop h₁ h₂) 
            (generate_pairs_of_vector hs)).
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) + 
           (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in usr; clear ha.
          (* Okamoto commitment *)
          set (oka_commitment := zip_with (fun '(gg, hh) us =>
            @okamoto_commitment F G gid gop gpow
            [gg; hh] us) (zip_with pair gs_pairs hs_pairs)
            (pair_zip usr)).
          refine(and_commit ++ oka_commitment).
        Defined.

        
        
        Definition generalised_construct_neq_response {n : nat} : 
          Vector.t F (2 + n) -> Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> 
          F -> Vector.t F ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          intros xs us c.
          set (xs_pair := generate_pairs_of_vector xs).
          (* split the randomness us at 2 + n *)
          destruct (splitat (2 + n) us) as (usl & usr).
          (* usl goes for AND response *)
          set (and_response := @construct_and_conversations_schnorr_response
            F add mul _ xs usl c).
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) + 
           (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in usr; clear ha.
          (* Okamoto response *)
          set (oka_response := pair_unzip (zip_with (fun '(x₁, x₂) us => 
              @okamoto_response F add mul [x₁ * inv (x₁ - x₂); inv (x₂ - x₁)]
              us c) xs_pair (pair_zip usr))).
          rewrite nat_div_2 in oka_response.
          exact (and_response ++ oka_response).
        Defined.

        (* input xs, gs, hs, us, c *)
        (* size of proofs is O(n^2) for NEQ if 
          we have n statements.
        *) 
        Definition generalised_construct_neq_conversations_real_transcript {n : nat} : 
          Vector.t F (2 + n) -> Vector.t G (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          intros xs gs hs us c.
          exact (generalised_construct_neq_commitment gs hs us; [c];
          generalised_construct_neq_response xs us c).
        Defined.

        
        Definition generalised_construct_neq_conversations_simulator_transcript 
          {n : nat} : Vector.t G (2 + n) -> Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          intros gs hs us c.
          destruct (splitat (2 + n) us) as (usl & usr).
          (* AND simulator commitment *)
          set (and_sim_comm := 
            @construct_and_conversations_simulator_commitment
            F opp G gop gpow _ gs hs usl c).
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) + 
           (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in usr; clear ha.
          set (oka_sim_comm := zip_with (fun '((g₁, g₂), (h₁, h₂)) vs =>
            @okamoto_simulator_protocol_commitment F opp G gid gop gpow 
              [gop g₁ g₂; gop h₁ h₂] g₂ vs c)
              (zip_with pair 
                (generate_pairs_of_vector gs) 
                (generate_pairs_of_vector hs))
              (pair_zip usr)).
          refine (and_sim_comm ++ oka_sim_comm; [c]; us).
        Defined.

        (* verification *)
        Definition generalised_neq_accepting_conversations {n : nat} :
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)) -> bool.
        Proof.
          intros gs hs pf.
          (* split the sig at (2 + n) *)
          refine 
            match pf with 
            |(a; c; r) => _ 
            end.
          (* split commitments at (2 + n )*)
          destruct (splitat (2 + n) a) as (al & ar).
          (* split responses at (2 + n)*)
          destruct (splitat (2 + n) r) as (rl & rr).
          (* Run AND verifier on (al; c; rl) *)
          refine 
            match 
              @generalised_and_accepting_conversations F G gop gpow Gdec _ 
              gs hs (al; c; rl)
            with 
            | true => _ 
            | _ => false (* No point of checking futher *) 
            end.
          assert(ha : ((Nat.div ((2 + n) * (1 + n)) 2) + 
           (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          rewrite <-ha in rr; clear ha.
          (* run Okamoto verifier on (ar; c; rr) *)
          set (oka_veri :=  
            (zip_with (fun '((g₁, g₂), (h₁, h₂)) '(a, rs) =>
            @okamoto_accepting_conversation F G gid gop gpow Gdec 
              [gop g₁ g₂; gop h₁ h₂] g₂ ([a]; c; rs))
              (zip_with pair 
                (generate_pairs_of_vector gs) 
                (generate_pairs_of_vector hs))
              (zip_with pair ar (pair_zip rr)))).
            exact (vector_forallb (fun x => x) oka_veri).
        Defined.

        (* distribution (zero-knowledge) *)

        Definition generalised_neq_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          (* draw ((2 + n) + ((1 + n) + (1 + n))) random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_real_transcript xs gs hs us c).


        Definition generalised_neq_simulator_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          (* draw ((2 + n) + ((1 + n) + (1 + n))) random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_simulator_transcript gs hs us c).

    End Def. 

    Section Proofs.


        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

      Theorem generalised_construct_neq_commitment_proof : 
        ∀ (n : nat) (gs hs al : Vector.t G (2 + n))
        (ar : Vector.t G ((2 + n) * (1 + n) / 2))
        (usl : Vector.t F (2 + n)) 
        (usrl usrr : Vector.t F (Nat.div ((2 + n) * (1 + n)) 2)), 
        generalised_construct_neq_commitment gs hs 
          (usl ++ @eq_rect _ _ (Vector.t F) 
          (usrl ++ usrr) _ (nat_div_2 n)) = al ++ ar ->
        @construct_and_conversations_schnorr_commitment F G gpow _ 
        gs usl = al ∧
        zip_with (λ '(gg, hh) us, 
          @okamoto_commitment F G gid gop gpow [gg; hh] us)
          (zip_with pair
          (map (λ '(g₁, g₂), gop g₁ g₂) (generate_pairs_of_vector gs))
          (map (λ '(h₁, h₂), gop h₁ h₂) (generate_pairs_of_vector hs)))
          (pair_zip (usrl ++ usrr)) = ar.
      Proof.
        intros * ha.
        unfold generalised_construct_neq_commitment in ha.
        rewrite !VectorSpec.splitat_append in ha.
        rewrite rew_opp_l in ha.
        eapply VectorSpec.append_inj in ha.
        exact ha.
      Qed.
      

      (* completeness *)
      Theorem generalised_neq_real_transcript_accepting_conversations : 
        ∀ (n : nat) (gs hs : Vector.t G (2 + n)) (xs : Vector.t F (2 + n))
        (us : Vector.t F (2 + n + (2 + n) * (1 + n))) (c : F), 
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) -> 
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        generalised_neq_accepting_conversations gs hs 
          (generalised_construct_neq_conversations_real_transcript xs gs hs us c) = true.
      Proof.
        intros * ha hb.
        unfold generalised_neq_accepting_conversations,
        generalised_construct_neq_conversations_real_transcript.
        destruct (splitat (2 + n) (generalised_construct_neq_commitment gs hs us)) as 
        [al ar] eqn:hc.
        destruct (splitat (2 + n) (generalised_construct_neq_response xs us c)) as
        [rl rr] eqn:hd.
        (* al; [c]; rl is AND accpeting conversation *)
        destruct (splitat (2 + n) us) as (usl & usr) eqn:he.
        eapply append_splitat in hc, hd, he.
        subst.
        unfold generalised_construct_neq_commitment in hc.
        rewrite !VectorSpec.splitat_append in hc.
        unfold generalised_construct_neq_response in hd.
        rewrite splitat_append in hd.
        eapply VectorSpec.append_inj in hc, hd.
        destruct hc as (hcl & hcd).
        destruct hd as (hdl & hdr).
        subst.
        pose proof (@construct_and_conversations_schnorr_completeness F zero one 
          add mul sub div opp inv G gid ginv gop gpow Gdec Hvec
          _ xs gs hs ha usl c) as hf.
        unfold construct_and_conversations_schnorr in hf.
        rewrite hf; clear hf.
        rewrite !rew_opp_l.
        rewrite vector_forallb_correct.
        intro i. 
        rewrite !nth_zip_with.
        destruct ((generate_pairs_of_vector gs)[@i]) as (g₁ & g₂) eqn:hc.
        destruct ((generate_pairs_of_vector hs)[@i]) as (h₁ & h₂) eqn:hd.
        destruct ((generate_pairs_of_vector xs)[@i]) as (x₁ & x₂) eqn:hf.
        unfold okamoto_accepting_conversation, okamoto_commitment,
        okamoto_response.
        rewrite !map_fin.
        rewrite !hc, !hd, !pair_zip_unzip_id.
        rewrite !nth_zip_with.
        rewrite hf.
        pose proof @generalised_okamoto_real_accepting_conversation F zero one 
          add mul sub div opp inv G gid ginv gop gpow Gdec Hvec _
          ([x₁ * inv (x₁ - x₂); inv (x₂ - x₁)])
          ([gop g₁ g₂; gop h₁ h₂])
          g₂ ((pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr))[@i]) as hg.
        unfold generalised_okamoto_real_protocol in hg.
        eapply hg; clear hg.
        cbn. 
        destruct (@generate_pairs_distinct_triple G F _ 
        gs hs xs i g₁ g₂ h₁ h₂ x₁ x₂ hc hd hf) as (j & k & hg & hi & 
        hj & hk & hl & hm & hn).
        clear hc hd hf.
        pose proof (ha j) as hc.
        rewrite <- hi, <-hk, <-hm in hc.
        rewrite <-hc.
        clear hc.
        pose proof (ha k) as hc.
        rewrite <- hj, <-hl, <-hn in hc.
        rewrite <-hc.
        rewrite right_identity, !smul_distributive_vadd,
        <-!smul_associative_fmul.
        rewrite gop_simp.
        rewrite <-!smul_distributive_fadd.
        assert (hd : (x₁ * inv (x₁ - x₂) + x₁ * inv (x₂ - x₁)) = zero). field.
        (* 
          x₂ - x₁ ≠ zero ∧ x₁ - x₂ ≠ zero
        *)
        pose proof (hb j k hg) as hd.
        rewrite <-hm, <-hn in hd.
        split. intro hw. 
        eapply hd. 
        eapply eq_sym, ring_sub_zero_iff.
        exact hw.
        intro hw. eapply hd.
        eapply ring_sub_zero_iff.
        exact hw.
        rewrite !hd; clear hd.
        rewrite field_zero, left_identity.
        assert (hd : (x₁ * inv (x₁ - x₂) + x₂ * inv (x₂ - x₁)) = 
          (x₂ - x₁) * inv (x₂ - x₁)). field.
        pose proof (hb j k hg) as hd.
        rewrite <-hm, <-hn in hd.
        split. intro hw. 
        eapply hd. 
        eapply eq_sym, ring_sub_zero_iff.
        exact hw.
        intro hw. eapply hd.
        eapply ring_sub_zero_iff.
        exact hw.
        rewrite !hd; clear hd.
        assert (hd : ((x₂ - x₁) * inv (x₂ - x₁)) = one).
        field.
        pose proof (hb j k hg) as hd.
        rewrite <-hm, <-hn in hd.
        intro hw. 
        eapply hd. 
        eapply eq_sym, ring_sub_zero_iff.
        exact hw.
        rewrite hd, field_one.
        reflexivity.
      Qed.


      Theorem generalised_neq_simulator_transcript_accepting_conversations : 
        ∀ (n : nat) (gs hs : Vector.t G (2 + n))
        (us : Vector.t F (2 + n + (2 + n) * (1 + n))) (c : F),
        generalised_neq_accepting_conversations gs hs 
          (generalised_construct_neq_conversations_simulator_transcript gs hs us c) = true.
      Proof.
        intros *.
        unfold generalised_neq_accepting_conversations,
        generalised_construct_neq_conversations_simulator_transcript.
        destruct (splitat (2 + n) us) as (usl & usr) eqn:ha.
        rewrite ha, splitat_append.
        setoid_rewrite construct_and_conversations_simulator_completeness.
        rewrite vector_forallb_correct.
        intro i.
        rewrite !nth_zip_with.
        destruct ((generate_pairs_of_vector gs)[@i]) as (g₁ & g₂) eqn:hc.
        destruct ((generate_pairs_of_vector hs)[@i]) as (h₁ & h₂) eqn:hd.
        pose proof @generalised_okamoto_simulator_accepting_conversation F 
        zero one add mul sub div opp inv G gid ginv gop gpow Gdec Hvec
        _ [gop g₁ g₂; gop h₁ h₂] g₂ 
        ((pair_zip (rew <- [λ n0 : nat, t F n0] nat_div_2 n in usr))[@i]) c as he.
        eapply he.
        exact Fdec.
      Qed.


      (* Special soundness.

        We do not assume a priori that discrete-logarithm relations between the
        generators are unknown. Instead, we prove a dichotomy: either the extracted
        witnesses are unique, or a non-trivial discrete-logarithm relation between
        the generators can be derived.

        In particular, to establish uniqueness of the exponents xs in the Okamoto
        protocol, one may assume the independence hypothesis

          H_independent :
            ∀ i j, i ≠ j → ¬ (∃ α, gs[@j] = gs[@i] ^ α)

        and prove the following theorem:

          Theorem generalised_neq_accepting_conversations_soundness :
            ∀ (n : nat) a c₁ c₂ rs₁ rs₂ gs hs,
              [c₁] <> [c₂] →
              generalised_neq_accepting_conversations gs hs (a; [c₁]; rs₁) = true →
              generalised_neq_accepting_conversations gs hs (a; [c₂]; rs₂) = true →
              ∃ (xs : Vector.t F (2 + n)),
                (∀ i, hs[@i] = gs[@i] ^ xs[@i]) ∧
                (∀ i j, i ≠ j → xs[@i] ≠ xs[@j]).

        However, logically, an implication P → Q can be reformulated as Q ∨ ¬P.
        While this equivalence relies on classical reasoning for arbitrary
        propositions, it is constructively valid when the propositions involved
        are decidable.

        Since both generator independence and equality of extracted exponents
        are decidable in our setting, we can internalise the independence assumption
        into the conclusion. We therefore strengthen the result by proving the
        following unconditional theorem, which captures special soundness without
        assuming independence explicitly.
      *)

      Theorem dec_prop_equiv (ha : ∀ (A : Prop), A + ~A) : ∀ (P Q : Prop),
        (P -> Q) <-> ~P ∨ Q.
      Proof.
        intros *; split.
        +
          intro f.
          destruct (ha P) as [hb | hb];
          [(right; eapply f; exact hb) |
          (left; exact hb)].
        +
          intros hb p.
          destruct hb as [hb | hb];
          [congruence | exact hb].
      Qed.
          


      Theorem generalised_neq_accepting_conversations_soundenss :
        ∀ (n : nat) a c₁ c₂ rs₁ rs₂ gs hs, [c₁] <> [c₂] ->
        generalised_neq_accepting_conversations gs hs (a; [c₁]; rs₁) = true ->
        generalised_neq_accepting_conversations gs hs (a; [c₂]; rs₂) = true ->
        ∃ (xs : Vector.t F (2 + n)), 
        (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) ∧
        ((∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ∨
        (∃ (i j : Fin.t (2 + n)), i ≠ j ∧ ((∃ (α : F), gs[@j] = gs[@i] ^ α) ∨
        gs[@i] = gid ∨ gs[@j] = gid))).
      Proof.
        intros * hn ha hb.
        (* Unfold the accepting conversation definition *)
        (* Split commitments and responses *)
        unfold generalised_neq_accepting_conversations in ha, hb.
        destruct (splitat (2 + n) a) as (al & ar) eqn:hc.
        destruct (splitat (2 + n) rs₁) as (rl₁ & rr₁) eqn:hd.
        destruct (splitat (2 + n) rs₂) as (rl₂ & rr₂) eqn:he.
        eapply append_splitat in hc, hd, he.
        destruct (generalised_and_accepting_conversations gs hs (al; [c₁]; rl₁)) 
        eqn:hf; try congruence.
        destruct (generalised_and_accepting_conversations gs hs (al; [c₂]; rl₂))
        eqn:hg; try congruence.
        destruct (@generalise_and_sigma_soundness_neq F zero one add mul sub div 
        opp inv Fdec G gid ginv gop gpow Gdec Hvec _ gs hs al [c₁] rl₁
        [c₂] rl₂ hf hg hn) as (ys & hi & hir). cbn in hir.
        exists ys. split. exact (fun f => eq_sym (hi f)).
        rewrite vector_forallb_correct in ha, hb.
        clear hf hg.
        destruct (@vector_unique_decidable _ Fdec _ ys) as [hj | 
          (ii & jj & hj & hk)].
        ++
          left. exact hj.
        ++
          right.
          destruct (@generate_pairs_contains_triple _ _ _ gs hs ys 
            ii jj hj) as (kk & hl).
          specialize (ha kk).
          specialize (hb kk).
          rewrite !nth_zip_with in ha, hb.
          destruct (generate_pairs_of_vector gs)[@kk] as (g₁, g₂).
          destruct (generate_pairs_of_vector hs)[@kk] as (h₁, h₂).
          destruct (generate_pairs_of_vector ys)[@kk] as (y₁, y₂).
          cbn in hl.
          assert (hw : c₁ ≠ c₂).
          intro hw. eapply hn. 
          subst. reflexivity.
          destruct (@generalised_okamoto_real_special_soundenss F zero 
          one add mul sub div opp inv G gid ginv gop gpow Gdec Hvec _ 
          [gop g₁ g₂; gop h₁ h₂]  g₂ ar[@kk] c₁ c₂ 
          (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₁))[@kk]
          (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₂))[@kk]
          hw ha hb) as (xs & hm & ho). clear hw.
          destruct hl as [hl | hl].
          -
            destruct hl as (hl₁ & hl₂ & hl₃ & hl₄ & hl₅ & hl₆).
            exists ii, jj. split. exact hj. 
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₁))[@kk] 
            as rrs₁; clear Heqrrs₁.
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₂))[@kk] 
            as rrs₂; clear Heqrrs₂.
            setoid_rewrite <-hl₂. 
            setoid_rewrite <-hl₁.
            pose proof (hi ii) as hii.
            pose proof (hi jj) as hjj.
            setoid_rewrite <-hl₁ in hii.
            setoid_rewrite <-hl₃ in hii.
            setoid_rewrite <-hl₅ in hii.
            setoid_rewrite <-hl₂ in hjj.
            setoid_rewrite <-hl₄ in hjj.
            setoid_rewrite <-hl₆ in hjj.
            setoid_rewrite <-hl₅ in hk.
            setoid_rewrite <-hl₆ in hk.
            destruct (vector_inv_S xs) as (xsh & xst & hx).
            destruct (vector_inv_S xst) as (xsth & xstt & hxx).
            pose proof (vector_inv_0 xstt) as hxxx.
            clear ho.
            subst xs. subst xst.
            subst xstt. cbn in hm.
            rewrite <-hii, <-hjj, <-hk in hm.
            rewrite !smul_distributive_vadd,
            <-!smul_associative_fmul, 
            gop_simp, right_identity,
            associative in hm.
            pose proof (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow Hvec) as hp.
            unfold  is_smul_distributive_fadd in hp.
            rewrite <-hp, <-associative, 
            <-hp in hm.
            assert (ht : (y₁ * xsth + xsh) = xsh + y₁ * xsth).
            field. rewrite ht in hm. clear ht.
            remember ((xsh + y₁ * xsth)) as gamma.
            (* case analysis on gamma *)
            destruct (Fdec gamma zero) as [hf | hf].
            *
              (* gamma zero *)
              rewrite hf, field_zero, left_identity,
              field_zero in hm.
              right. right. exact hm.
            *
              destruct (Fdec gamma one) as [hfo | hfo].
              **
                (* gamma = one *)
                rewrite hfo, !field_one in hm.
                eapply f_equal with (f := fun x => gop x (ginv g₂)) in hm.
                rewrite right_inverse, <-associative, 
                right_inverse, right_identity in hm.
                right. left. now rewrite hm.
              **
                (* gamma <> 0 ∧ gamma <> one *)
                eapply f_equal with (f := fun x => gop x (ginv (g₂ ^ gamma))) 
                in hm.
                rewrite !connection_between_vopp_and_fopp in hm.
                assert (ht : gop g₂ (g₂ ^ opp gamma) = 
                  gop (g₂ ^ one) (g₂ ^ opp gamma)).
                f_equal. now rewrite field_one.
                rewrite ht in hm. clear ht.
                rewrite <-hp, <-associative in hm.
                rewrite <-hp in hm.
                assert (ht : (gamma + opp gamma) = zero).
                field. rewrite ht in hm.
                clear ht. rewrite field_zero, right_identity in hm.
                eapply f_equal with (f := fun x => x ^ inv (one + opp gamma)) in hm.
                rewrite <-!smul_associative_fmul in hm.
                assert (ht : ((one + opp gamma) * inv (one + opp gamma)) = one).
                field. intro hg. eapply hfo. 
                eapply f_equal with (f := fun x => x + gamma) in hg.
                rewrite <-associative in hg.
                assert (hgg : opp gamma + gamma = zero). field.
                rewrite hgg in hg. clear hgg.
                rewrite right_identity, left_identity in hg.
                now rewrite hg.
                rewrite ht, field_one in hm.
                left.
                exists ((gamma * inv (one + opp gamma))).
                exact hm.
          -
            destruct hl as (hl₁ & hl₂ & hl₃ & hl₄ & hl₅ & hl₆).
            exists ii, jj. split. exact hj. 
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₁))[@kk] 
            as rrs₁; clear Heqrrs₁.
            remember (pair_zip (rew <- [λ n : nat, t F n] nat_div_2 n in rr₂))[@kk] 
            as rrs₂; clear Heqrrs₂.
            setoid_rewrite <-hl₂. 
            setoid_rewrite <-hl₁.
            pose proof (hi ii) as hii.
            pose proof (hi jj) as hjj.
            setoid_rewrite <-hl₂ in hii.
            setoid_rewrite <-hl₄ in hii.
            setoid_rewrite <-hl₆ in hii.
            setoid_rewrite <-hl₁ in hjj.
            setoid_rewrite <-hl₃ in hjj.
            setoid_rewrite <-hl₅ in hjj.
            setoid_rewrite <-hl₅ in hk.
            setoid_rewrite <-hl₆ in hk.
            destruct (vector_inv_S xs) as (xsh & xst & hx).
            destruct (vector_inv_S xst) as (xsth & xstt & hxx).
            pose proof (vector_inv_0 xstt) as hxxx.
            clear ho.
            subst xs. subst xst.
            subst xstt. cbn in hm.
            rewrite <-hii, <-hjj, <-hk in hm.
            rewrite !smul_distributive_vadd,
            <-!smul_associative_fmul, 
            gop_simp, right_identity,
            associative in hm.
            pose proof (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow Hvec) as hp.
            unfold  is_smul_distributive_fadd in hp.
            rewrite <-hp, <-associative, 
            <-hp in hm.
            assert (ht : (y₂ * xsth + xsh) = xsh + y₂ * xsth).
            field. rewrite ht in hm. clear ht.
            remember ((xsh + y₂ * xsth)) as gamma.
            (* case analysis on gamma *)
            destruct (Fdec gamma zero) as [hf | hf].
            *
              (* gamma zero *)
              rewrite hf, field_zero, left_identity,
              field_zero in hm.
              right. left. exact hm.
            *
              destruct (Fdec gamma one) as [hfo | hfo].
              **
                (* gamma = one *)
                rewrite hfo, !field_one in hm.
                eapply f_equal with (f := fun x => gop x (ginv g₂)) in hm.
                rewrite right_inverse, <-associative, 
                right_inverse, right_identity in hm.
                right. right. now rewrite hm.
              **
                (* gamma <> 0 ∧ gamma <> one *)
                eapply f_equal with (f := fun x => gop x (ginv (g₂ ^ gamma))) 
                in hm.
                rewrite !connection_between_vopp_and_fopp in hm.
                assert (ht : gop g₂ (g₂ ^ opp gamma) = 
                  gop (g₂ ^ one) (g₂ ^ opp gamma)).
                f_equal. now rewrite field_one.
                rewrite ht in hm. clear ht.
                rewrite <-hp, <-associative in hm.
                rewrite <-hp in hm.
                assert (ht : (gamma + opp gamma) = zero).
                field. rewrite ht in hm.
                clear ht. rewrite field_zero, right_identity in hm.
                eapply f_equal with (f := fun x => x ^ inv (one + opp gamma)) in hm.
                rewrite <-!smul_associative_fmul in hm.
                assert (ht : ((one + opp gamma) * inv (one + opp gamma)) = one).
                field. intro hg. eapply hfo. 
                eapply f_equal with (f := fun x => x + gamma) in hg.
                rewrite <-associative in hg.
                assert (hgg : opp gamma + gamma = zero). field.
                rewrite hgg in hg. clear hgg.
                rewrite right_identity, left_identity in hg.
                now rewrite hg.
                rewrite ht, field_one in hm.
                eapply f_equal with (f := fun x => 
                  x ^ inv (gamma * inv (one + opp gamma))) in hm.
                rewrite <-!smul_associative_fmul in hm.
                assert (hgam : (gamma * inv (one + opp gamma) * inv (gamma * inv (one + opp gamma))) = one). field.
                split; [| exact hf].
                intro hg. eapply hfo.
                eapply f_equal with (f := fun x => x + gamma) in hg.
                assert (hgg : opp gamma + gamma = zero). field.
                rewrite <-associative in hg.
                rewrite hgg in hg. clear hgg.
                rewrite right_identity, left_identity in hg.
                now rewrite hg.
                rewrite hgam, field_one in hm.
                left.
                exists (inv (gamma * inv (one + opp gamma))).
                exact (eq_sym hm).
      Qed.
      


       
      (* zero-knowledge proof *)

      (* special honest-verifier zero-knowledge proof *)
      (* honest verifier zero knowledge proof *)

      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      Lemma generalised_neq_real_distribution_transcript_accepting_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) (xs : Vector.t F (2 + n))
        (gs hs : Vector.t G (2 + n)) 
        (trans : sigma_proto) (pr : prob) (c : F),
        (* relationship between gs, hs, and xs *)
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] =  hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)), 
            Ret (generalised_construct_neq_conversations_real_transcript xs gs hs us c))) → 
        generalised_neq_accepting_conversations gs hs trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Hrel Hr Ha.
          cbn in Ha; 
          inversion Ha.
        +
          (* destruct l *)
          destruct l as [|(la, lp) l].
          ++
            intros * Hrel Hr Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply generalised_neq_real_transcript_accepting_conversations; 
            assumption.
          ++
            intros * Hrel Hr Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply generalised_neq_real_transcript_accepting_conversations; 
              assumption.
            +++
              eapply IHl; try assumption.
              exact Hrel. exact Hr.
              exact Ha.
      Qed.

      Lemma generalised_neq_real_distribution_transcript_probability_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) (xs : Vector.t F (2 + n))
        (gs hs : Vector.t G (2 + n))
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n + (2 + n) * (1 + n))) (prx : prob), 
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)), 
          Ret (generalised_construct_neq_conversations_real_transcript xs gs hs us c))) → 
        pr = 1 / m.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst; 
          clear Hwa.
          unfold mul_prob, 
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.


      Lemma generalised_neq_real_distribution_transcript_generic {n : nat} : 
        forall (lf : list F) (Hlf : lf <> List.nil) 
        (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) 
        (a : sigma_proto) (b : prob) (c : F),
        (* relationship between gs, hs, and xs *)
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.In (a, b) (generalised_neq_schnorr_distribution lf Hlf xs gs hs c) ->
        generalised_neq_accepting_conversations gs hs a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n + (2 + n) * (1 + n)))).
      Proof.
        intros * Hrel Hr Ha.
        refine(conj _ _).
        +
          eapply generalised_neq_real_distribution_transcript_accepting_generic.
          exact Hrel. exact Hr. exact Ha.
        +
          eapply generalised_neq_real_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.


       Lemma generalised_neq_simulator_distribution_transcript_accepting_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) 
        (gs hs : Vector.t G (2 + n)) (trans : sigma_proto) (pr : prob) (c : F),
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)), 
            Ret (generalised_construct_neq_conversations_simulator_transcript gs hs us c))) → 
        generalised_neq_accepting_conversations gs hs trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Ha.
          cbn in Ha; 
          inversion Ha.
        +
          (* destruct l *)
          destruct l as [|(la, lp) l].
          ++
            intros * Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply generalised_neq_simulator_transcript_accepting_conversations.
          ++
            intros * Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply generalised_neq_simulator_transcript_accepting_conversations.
            +++
              eapply IHl; exact Ha.
      Qed.


      Lemma generalised_neq_simulator_distribution_transcript_probability_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) 
        (gs hs : Vector.t G (2 + n)) 
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n + (2 + n) * (1 + n))) (prx : prob), 
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ us : Vector.t F (2 + n + (2 + n) * (1 + n)), 
          Ret (generalised_construct_neq_conversations_simulator_transcript gs hs us c))) → 
        pr = 1 / m.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst; 
          clear Hwa.
          unfold mul_prob, 
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.


       Lemma generalised_neq_simulator_distribution_transcript_generic {n : nat} : 
        forall (lf : list F) (Hlf : lf <> List.nil) 
        (gs hs : Vector.t G (2 + n)) 
        (a : sigma_proto) (b : prob) (c : F),
        List.In (a, b) (generalised_neq_simulator_distribution lf Hlf gs hs c) ->
        generalised_neq_accepting_conversations gs hs a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n + (2 + n) * (1 + n)))).
      Proof.
        intros * Ha.
        refine(conj _ _).
        +
          eapply generalised_neq_simulator_distribution_transcript_accepting_generic.
          exact Ha.
        +
          eapply generalised_neq_simulator_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.


      (* Two distributions are identical (information theoretic security)*)
      Lemma generalised_okamoto_special_honest_verifier_zkp {n : nat} : 
        forall (lf : list F) (Hlfn : lf <> List.nil) 
        (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F),
        (∀ (i : Fin.t (2 + n)), gs[@i] ^ xs[@i] = hs[@i]) ->
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]) ->
        List.map (fun '(a, p) => 
          (generalised_neq_accepting_conversations gs hs a, p))
          (@generalised_neq_schnorr_distribution n lf Hlfn xs gs hs c) = 
        List.map (fun '(a, p) => 
          (generalised_neq_accepting_conversations gs hs a, p))
          (@generalised_neq_simulator_distribution n lf Hlfn gs hs c).
      Proof.
        intros * Hrel Hr.
        eapply map_ext_eq.
        + 
          unfold generalised_neq_schnorr_distribution,
          generalised_neq_simulator_distribution; cbn.
          repeat rewrite distribution_length.
          reflexivity.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_neq_real_distribution_transcript_generic.
          exact Hrel. exact Hr. exact Ha.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_neq_simulator_distribution_transcript_generic.
          exact Ha.
      Qed.
    
    End Proofs. 
  End Neq.
End DL.