From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef 
  BinPos Arith.
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
  VectorNotations.
          
#[local] Open Scope monad_scope.

Section Util.

  (* 
    Theorem add_zero_trans : ∀ (n : nat), n + 0 = n.
    Admitted. 
    
    Theorem add_commutative : ∀ (a b : nat), a + b = b + a.
    Admitted.

    Theorem add_mul_comm : ∀ (a b : nat), a * b = b * a. 
    Admitted. 

    Theorem add_comm_dist_transparent : ∀ (a b c : nat), 
     (a + b) * c = a * c + b * c.
    Proof.
    Admitted.
      
      

    Theorem add_comm_transparent : ∀ (n : nat),
      (1 + S n) * 2 + ((2 + n) * (1 + n)) = (2 + S n) * (1 + S n).
    Proof.
      intros *. change (S n) with (1 + n).
      rewrite !add_comm_dist_transparent.
      setoid_rewrite add_mul_comm.
      cbn.  f_equal. f_equal.
      f_equal. f_equal.
      rewrite add_zero_trans.
      rewrite add_commutative.
      setoid_rewrite add_commutative at 1.
      f_equal. 
      change 2 with (1 + 1).
      rewrite add_mul_comm, add_comm_dist_transparent.
      cbn; rewrite !add_zero_trans; reflexivity.
      f_equal. f_equal.
      cbn. change 2 with (1 + 1).
      rewrite add_mul_comm, add_comm_dist_transparent.
      cbn; rewrite !add_zero_trans.
    Admitted.
    *)

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
        (* make this proof transparent. *)
        assert (ha : ((1 + S n) * 2 + ((2 + n) * (1 + n)) = 
        ((2 + S n) * (1 + S n)))%nat) by (abstract nia).
        eapply f_equal with (f := fun x => Nat.div x 2) in ha.
        rewrite PeanoNat.Nat.div_add_l in ha; try (abstract nia).
        refine(@eq_rect nat _ (Vector.t (A * A)) (reta ++ generate_pairs_of_vector) _
          ha).
    Defined.

   
    Definition nat_div_2 : ∀ (n : nat), 
        (2 * Nat.div ((2 + n) * (1 + n)) 2)%nat = ((2 + n) * (1 + n))%nat.
      Proof.
        induction n as [| n IH].
        - (* Base case: n = 0 *)
          cbn; reflexivity.
        - (* Inductive step *)
          change ((2 + S n))%nat with (3 + n)%nat.
          change ((1 + S n))%nat with (2 + n)%nat.
          (* We show that (n+3)(n+2) = (n+2)(n+1) + 2(n+2) *)
          replace ((3 + n) * (2 + n))%nat
            with (((2 + n) * (1 + n)) + 2 * (2 + n))%nat
            by (abstract nia).
          replace (2 * (2 + n))%nat with 
          ((2 + n) * 2)%nat by (abstract nia).
          rewrite Nat.div_add; 
          try (abstract nia).
    Defined.

   
    Fixpoint pair_unzip {A : Type} {n : nat} : 
      Vector.t (Vector.t A 2) n -> Vector.t A (2 * n).
    Proof.
      intros v.
      refine
        (match v in Vector.t _ n' return Vector.t _ (2 * n')  
        with 
        | [] => []
        | Vector.cons _ vh nt vt => _ 
        end).
        replace (2 * S nt) with  (2 + 2 * nt); try (abstract nia).
        exact (vh ++ pair_unzip _ _ vt).
    Defined.
      
    Fixpoint pair_zip {A : Type} {n : nat} : 
      Vector.t A (2 * n) ->  Vector.t (Vector.t A 2) n.
    Proof.
      destruct n as [|n].
      +
        intros vs.
        exact [].
      +
        intros vs.
        replace (2 * S n) with  (S (S (2 * n))) in vs; try (abstract nia).
        destruct (vector_inv_S vs) as (vsh & vst & _).
        destruct (vector_inv_S vst) as (vsth & vstt & _).
        refine(Vector.cons _ [vsh; vsth] _ (pair_zip _ _ vstt)).
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
          assert(ha : (2 * (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          replace (2 * Nat.div ((2 + n) * (1 + n)) 2)%nat with 
          (Nat.div ((2 + n) * (1 + n)) 2 + Nat.div ((2 + n) * (1 + n)) 2)%nat in ha;
          try (abstract nia).
          rewrite <-ha in usr; clear ha.
          destruct (splitat (Nat.div ((2 + n) * (1 + n)) 2) usr) as 
          (usrl & usrr).
          (* Okamoto commitment *)
          set (oka_commitment := zip_with (fun '(gg, hh) '(u₁, u₂) =>
            @okamoto_commitment F G gid gop gpow
            [gg; hh] [u₁; u₂]) (zip_with pair gs_pairs hs_pairs)
            (zip_with pair usrl usrr)).
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
          assert(ha : (2 * (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          replace (2 * Nat.div ((2 + n) * (1 + n)) 2)%nat with 
          (Nat.div ((2 + n) * (1 + n)) 2 + Nat.div ((2 + n) * (1 + n)) 2)%nat in ha;
          try (abstract nia).
          rewrite <-ha in usr; clear ha.
          destruct (splitat (Nat.div ((2 + n) * (1 + n)) 2) usr) as 
          (usrl & usrr).
          (* Okamoto response *)
          set (oka_response := pair_unzip (zip_with (fun '(x₁, x₂) '(u₁, u₂) => 
              @okamoto_response F add mul [x₁ * inv (x₁ - x₂); inv (x₂ - x₁)]
              [u₁; u₂] c) xs_pair (zip_with pair usrl usrr))).
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
          assert(ha : (2 * (Nat.div ((2 + n) * (1 + n)) 2) = 
          ((2 + n) * (1 + n)))%nat). eapply nat_div_2.
          replace (2 * Nat.div ((2 + n) * (1 + n)) 2)%nat with 
          (Nat.div ((2 + n) * (1 + n)) 2 + Nat.div ((2 + n) * (1 + n)) 2)%nat in ha;
          try (abstract nia).
          rewrite <-ha in usr; clear ha.
          destruct (splitat (Nat.div ((2 + n) * (1 + n)) 2) usr) as 
          (usrl & usrr).
          set (oka_sim_comm := zip_with (fun '((g₁, g₂), (h₁, h₂)) '(u₁, u₂) =>
            @okamoto_simulator_protocol_commitment F opp G gid gop gpow 
              [gop g₁ g₂; gop h₁ h₂] g₂ [u₁; u₂] c)
              (zip_with pair 
                (generate_pairs_of_vector gs) 
                (generate_pairs_of_vector hs))
              (zip_with pair usrl usrr)).
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
          assert(ha : (2 * (Nat.div ((2 + n) * (1 + n)) 2) = 
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
            exact (vector_forallb id oka_veri).
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

      (* completeness *)
      Theorem generalised_neq_real_transcript_accepting_conversations : 
        ∀ (n : nat) (gs hs : Vector.t G (2 + n)) (xs : Vector.t F (2 + n))
        (us : Vector.t F (2 + n + (2 + n) * (1 + n))) (c : F), 
        (∀ (i : Fin.t (2 + n)), hs[@i] = gs[@i] ^ xs[@i]) -> 
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

      Admitted.


      Theorem generalised_neq_simulator_transcript_accepting_conversations : 
        ∀ (n : nat) (gs hs : Vector.t G (2 + n))
        (us : Vector.t F (2 + n + (2 + n) * (1 + n))) (c : F),
        generalised_neq_accepting_conversations gs hs 
          (generalised_construct_neq_conversations_simulator_transcript gs hs us c) = true.
      Proof.
        intros *.
      Admitted.


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