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

Section Util.

   

    Theorem generate_pairs_of_vector_proof : 
      ∀ (n m : nat), m + Nat.div (m * n) 2 = 
      Nat.div ((2 + n) * m) 2.
    Proof.
        intros *. 
        rewrite div_add.
        f_equal. rewrite add_mul_dist.
        assert (ha : (2 + n) * m = m * (2 + n)) by 
        (now rewrite mul_comm). 
        rewrite ha; clear ha.
        rewrite add_mul_dist.
        exact eq_refl.
    Defined.

    
    (* computes pair of vectors: *)
    Fixpoint generate_pairs_of_vector {A : Type} {n : nat}  
      (gs : Vector.t A (2 + n)) : Vector.t (A * A) (Nat.div ((2 + n) * (1 + n)) 2).
    Proof.
      destruct n as [|n].
      +
        destruct (vector_inv_S gs) as (gsh & gst & _).
        destruct (vector_inv_S gst) as (gsth & _).
        exact [(gsh, gsth)].
      +
        destruct (vector_inv_S gs) as (gsh & gst & _).
        (* map gsh over gst *)
        set (reta := Vector.map (fun x => (gsh, x)) gst).
        specialize (generate_pairs_of_vector _ _ gst).
        refine(@eq_rect nat _ (Vector.t (A * A)) 
        (reta ++ generate_pairs_of_vector) _ _).
        eapply generate_pairs_of_vector_proof.
    Defined.

   
    Fixpoint pair_unzip {A : Type} {n : nat} : 
      Vector.t (Vector.t A 2) n -> Vector.t A (n + n).
    Proof.
      intros v.
      refine
        (match v in Vector.t _ n' return Vector.t _ (n' + n')  
        with 
        | [] => []
        | Vector.cons _ vh nt vt => _ 
        end). 
        replace (S nt +  S nt) with  (S (S (nt + nt))).
        exact (vh ++ pair_unzip _ _ vt).
        cbn. f_equal.
        rewrite add_succ_r.
        reflexivity.
    Defined.
      
    Fixpoint pair_zip {A : Type} {n : nat} : 
      Vector.t A (n + n) ->  Vector.t (Vector.t A 2) n.
    Proof.
      destruct n as [|n].
      +
        intros vs.
        exact [].
      +
        intros vs.
        replace (S n +  S n) with  (S (S (n + n))) in vs.
        destruct (vector_inv_S vs) as (vsh & vst & _).
        destruct (vector_inv_S vst) as (vsth & vstt & _).
        refine(Vector.cons _ [vsh; vsth] _ (pair_zip _ _ vstt)).
        cbn. f_equal.
        rewrite add_succ_r.
        reflexivity.
    Defined.

    Theorem pair_zip_unzip_id {A : Type} : 
      ∀ (n : nat) (vs : Vector.t (Vector.t A 2) n), 
        @pair_zip A n (@pair_unzip A n vs) = vs.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        pose proof (vector_inv_0 vs) as ha.
        subst; reflexivity.
      +
        intros *.
        destruct (vector_inv_S vs) as (vsh & vst & ha).
        subst; cbn.
        rewrite rew_opp_l.
        destruct (vector_inv_S (vsh ++ pair_unzip vst)) as (vh & vt & ha).
        destruct (vector_inv_S vsh) as (vshh & vsht & hb).
        rewrite hb in ha.
        cbn in ha. 
        eapply vec_inv in ha.
        destruct ha as (hal & har).
        subst. 
        destruct (vector_inv_S vsht) as (vshth & vshtt & ha).
        pose proof (vector_inv_0 vshtt) as hb.
        subst. cbn. 
        rewrite ihn; reflexivity.
    Qed.

    Lemma nth_zip_with : forall (A B C : Type) (f : A -> B -> C) (n : nat)
      (i : Fin.t n) (vsa : Vector.t A n) (vsb  : Vector.t B n) ,
      (zip_with f vsa vsb)[@i] = f (vsa[@i]) (vsb[@i]).
    Proof.
      intros until f.
      induction n as [|n ihn].
      +
        intros *.
        refine match i with end.
      +
        intros *.
        destruct (vector_inv_S vsa) as (vsah & vsat & ha).
        destruct (vector_inv_S vsb) as (vsbh & vsbt & hb).
        subst. 
        destruct (fin_inv_S _ i) as [hc | (i' & ha)].
        ++
          subst; cbn; reflexivity.
        ++
          subst; cbn.
          eapply ihn.
    Qed.

    Lemma map_fin {A B : Type} (f : A -> B) :
      ∀ (n : nat) (i : Fin.t n) (vs : Vector.t A n), 
      (Vector.map f vs)[@i] = f (vs[@i]).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        refine match i with end.
      +
        intros *.
        destruct (vector_inv_S vs) as (vsh & vst & ha).
        subst. 
        destruct (fin_inv_S _ i) as [hc | (i' & ha)].
        ++
          subst; cbn; reflexivity.
        ++
          subst; cbn; eapply ihn.
    Qed.

    
    Lemma Fin_append_inv : ∀ (m n : nat) (i : Fin.t (m+n)),
      (∃ j : Fin.t m, i = Fin.L n j) ∨ (∃ j : Fin.t n, i = Fin.R m j).
    Proof.
    Admitted.



    Lemma generate_pairs_distinct {A : Type} : 
      ∀ (n : nat) (vs : Vector.t A (2+n)) 
      (i : Fin.t ((2 + n) * (1 + n)/ 2)) (a b : A),
      (generate_pairs_of_vector vs)[@i] = (a, b) ->
      ∃ (j k : Fin.t (2 + n)), j ≠ k ∧ a = vs[@j] ∧ b = vs[@k].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        cbn in vs, i.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        destruct (vector_inv_S vst) as (vsth & vstt & hc).
        pose proof (vector_inv_0 vstt) as hd.
        subst.
        destruct (fin_inv_S _ i) as [i' | (i' & hb)]; 
        subst.
        exists (Fin.F1), (Fin.FS (Fin.F1)); split.
        intro hb. congruence.
        cbn in ha |- *.
        inversion ha; subst; split; reflexivity.
        refine match i' with end.
      +
        intros * ha.
    Admitted.

   

    Lemma invert_eq_rect {A : Type} {x y : A} 
      (P : A -> Type) (hb : y = x) (ha : P x) (hc : P y) :
      rew <-[P] hb in ha = hc → rew [P] hb in hc = ha.
    Proof.
      intros hd. subst.
      cbn. reflexivity.
    Defined.
        





End Util.


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

      (* 
      Theorem generalised_construct_neq_response_proof : 
        ∀ (n : nat), (xs : Vector.t F (2 + n)) 
        (usl : Vector.t F (2 + n))
        (usrl usrr : Vector.t F (Nat.div ((2 + n) * (1 + n)) 2))
        (c : F) (rl : Vector.t F (2 + n))
        (rr : Vector.t F ((2 + n) * (1 + n)))
        generalised_construct_neq_response xs (usl ++ @eq_rect _ _ (Vector.t F) 
        (usrl ++ usrr) _ (nat_div_2 n)) c = rl ++ rr -> 
        construct_and_conversations_schnorr_response xs usl c = true ∧
      *)
      

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



        pose proof @generalised_okamoto_real_accepting_conversation F zero one 
          add mul sub div opp inv G gid ginv gop gpow Gdec Hvec _
          ([x₁ * inv (x₁ - x₂); inv (x₂ - x₁)])
          ([gop g₁ g₂; gop h₁ h₂])
          g₂ as hg.
          cbn in hg |- *.
        setoid_rewrite dec_true.  *.
        eapply f_equal with (f := pair_zip) in hw.
        rewrite pair_zip_unzip_id in hw.
        
      Admitted.


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
        destruct (splitat ((2 + n) * (1 + n) / 2)
        (eq_rect_r (λ n0 : nat, t F n0) usr (nat_div_2 n))) as (usrl & usrr) eqn:hb.
        rewrite ha, splitat_append.
        setoid_rewrite construct_and_conversations_simulator_completeness.
        eapply append_splitat, invert_eq_rect in hb.
        rewrite <-hb. rewrite rew_opp_l.
        rewrite splitat_append.
        rewrite vector_forallb_correct.
        intro i.
        rewrite !nth_zip_with.
        destruct ((generate_pairs_of_vector gs)[@i]) as (g₁ & g₂) eqn:hc.
        destruct ((generate_pairs_of_vector hs)[@i]) as (h₁ & h₂) eqn:hd.
        pose proof @generalised_okamoto_simulator_accepting_conversation F 
        zero one add mul sub div opp inv G gid ginv gop gpow Gdec Hvec
        _ [gop g₁ g₂; gop h₁ h₂] g₂ [usrl[@i]; usrr[@i]] c as he.
        rewrite <-he.
        unfold okamoto_accepting_conversation, okamoto_simulator_protocol_commitment,
        generalised_okamoto_simulator_protocol_commitment.
        f_equal.
        exact Fdec.
      Qed.


      (* special soundness *)

      Theorem generalised_neq_accepting_conversations_soundenss :
        ∀ (n : nat) a c₁ c₂ rs₁ rs₂ gs hs, 
        generalised_neq_accepting_conversations gs hs (a; [c₁]; rs₁) = true ->
        generalised_neq_accepting_conversations gs hs (a; [c₂]; rs₂) = true ->
        ∃ (xs : Vector.t F (2 + n)), (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) ∧
        (∀ (i j : Fin.t (2 + n)), i ≠ j -> xs[@i] ≠ xs[@j]).
      Proof.
      Admitted.

      (* zero-knowledge proof *)

      (* special honest-verifier zero-knowledge proof *)
      (* honest verifier zero knowledge proof *)

      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      Lemma generalised_neq_real_distribution_transcript_accepting_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n + (2 + n) * (1 + n)))) (xs : Vector.t F (2 + n))
        (gs hs : Vector.t G (2 + n)) 
        (trans : sigma_proto) (pr : prob) (c : F),
        (* relationship between gs, hs, and xs *)
        (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) ->
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
        (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) ->
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
        (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) ->
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