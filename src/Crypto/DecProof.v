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
From Crypto Require Import Sigma ChaumPedersen.
  

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

  Section DecProof.
    Section Def.

      (* Decryption proof (c₁, c₂) m *)
      (* https://github.com/benadida/helios-server/blob/master/helios/crypto/elgamal.py#L174 *)
      (* """
        given g, y, alpha, beta/(encoded m), prove equality of discrete log
        with Chaum Pedersen, and that discrete log is x, the secret key.

        Prover sends a=g^u, b=c₁^u for random u
        Challenge c 
        Prover sends t = u + x * c

        Verifier will check that g^t = a * h^c
        and c₁^t = b * c₂/m ^ c
        """
      *)
      Definition construct_decryption_proof_elgamal_real 
        (x : F) (g : G) (cp : G * G) (u c : F) :  @sigma_proto F G 2 1 1 :=
        @construct_cp_conversations_schnorr F add mul G gpow x 
        g (fst cp) u c.

     
      (* Simulator 
        random u and c 
        (g^c * h^{-c}, c, u)
        (c₁^c * (c₂ * ginv m)^-{-c}, c, u)
      
      *)
      Definition construct_decryption_proof_elgamal_simulator 
        (g h : G) (c₁ c₂ : G) (m : G) (u c : F) :  @sigma_proto F G 2 1 1 := 
        @construct_cp_conversations_simulator F opp G gop gpow 
        g c₁ h (gop c₂ (ginv m)) u c.

       
      (* g^t = a * h^c mod p
         c₁^t = b * (c₂/m)^c mod p *)
      Definition decryption_proof_accepting_conversations (g h : G) (c₁ c₂ : G) (m : G)
        (s : @sigma_proto F G 2 1 1) : bool :=
        @generalised_cp_accepting_conversations F G gop gpow 
          Gdec g c₁ h (gop c₂ (ginv m)) s.



      
      (* distribution involving witness *)
      Definition construct_decryption_proof_elgamal_real_distribution  
        (lf : list F) (Hlfn : lf <> List.nil) (x : F)
        (g c₁ : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_cp_schnorr_distribution F add mul G gpow 
          lf Hlfn x g c₁ c.

      (* Without secret *)
      Definition construct_decryption_proof_elgama_simulator_distribution 
        (lf : list F) (Hlfn : lf <> List.nil) (g h : G)
        (c₁ c₂ : G) (m : G) (c : F) : dist (@sigma_proto F G 2 1 1) :=
        @generalised_cp_simulator_distribution  F opp G gop 
        gpow lf Hlfn g c₁ h (gop c₂ (ginv m)) c.
      

      (* These two function are just a convenience for tally code *)
      Fixpoint construct_decryption_proof_elgamal_real_vector {n : nat} 
        (x : F) (g : G) (cps : Vector.t (G * G) n) (us cs : Vector.t F n) :
        Vector.t (@sigma_proto F G 2 1 1) n.
      Proof.
        destruct n as [|n].
        +
          exact [].
        +
          destruct (vector_inv_S cps) as (cph & cpt & _).
          destruct (vector_inv_S us) as (ush & ust & _).
          destruct (vector_inv_S cs) as (csh & cst & _).
          exact ((construct_decryption_proof_elgamal_real x g cph ush csh) :: 
            (construct_decryption_proof_elgamal_real_vector _ x g cpt ust cst)).
      Defined.

      Fixpoint decryption_proof_accepting_conversations_vector {n : nat} (g h : G) 
        (cps : Vector.t (G * G) n) (ms : Vector.t G n)
        (pf : Vector.t (@sigma_proto F G 2 1 1) n ) : bool.
      Proof.
        destruct n as [|n].
        +
          exact true.
        +
          destruct (vector_inv_S cps) as ((c₁, c₂) & cpst & _).
          destruct (vector_inv_S ms) as (msh & mst & _).
          destruct (vector_inv_S pf) as (pfh & pft & _).
          exact ((decryption_proof_accepting_conversations g h c₁ c₂ msh pfh) && 
          (decryption_proof_accepting_conversations_vector n g h cpst mst pft)).
      Defined.
      

    End Def.

    Section Proofs.

      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub 
          div opp inv G (@eq G) gid ginv gop gpow}.
        
        (* 
          (x : F) 
          (g h m c₁ c₂ : G)
          (R : g^x = h ∧ c₁^x = gop c₂  (ginv m)). 
        *)
      (* add field *)
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (* real proof completeness *)
      Lemma construct_decryption_proof_elgamal_real_completeness 
        (x : F) 
        (g h m c₁ c₂ : G)
        (R : g^x = h ∧ c₁^x = gop c₂ (ginv m)) :
        forall (u c : F), 
        decryption_proof_accepting_conversations g h c₁ c₂ m
          (construct_decryption_proof_elgamal_real x g (c₁, c₂) u c) = true.
      Proof.
        intros *. cbn.
        eapply andb_true_iff; split; 
        rewrite dec_true.
        +
          destruct R as [ra rb].
          pose proof (@schnorr_completeness F zero one add mul sub div opp inv 
            G gid ginv gop gpow Gdec Hvec g h x (eq_sym ra) u c) as ha.
          cbn in ha. rewrite dec_true in ha.
          exact ha.
        +
          destruct R as [ra rb].
          rewrite <-rb.
          assert (Hg : (c₁ ^ x) ^ c = (c₁ ^ (x * c))).
          rewrite smul_pow_up. 
          reflexivity.
          rewrite Hg; clear Hg.
          assert (Hxc : x * c = c * x) by field.
          rewrite Hxc; clear Hxc.
          rewrite <- (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow);
          subst; [exact eq_refl 
          | assumption].
      Qed.


      (* simulator proof completeness *)
      Lemma construct_decryption_proof_elgamal_simulator_completeness 
        (g h m c₁ c₂ : G) : 
        forall (u c : F),
        decryption_proof_accepting_conversations g h c₁ c₂ m
          (construct_decryption_proof_elgamal_simulator g h c₁ c₂ m u c) = true.
      Proof.
        intros *. cbn.
        eapply andb_true_iff; split;
        rewrite dec_true.
        +
          rewrite <-associative.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto. 
        +
          remember (gop c₂ (ginv m)) as ct.
          rewrite <-associative.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto. 
      Qed.


      (* special soundness *)
      Lemma special_soundness_construct_decryption_proof_elgamal (g h m cp₁ cp₂ : G) : 
        forall (a : Vector.t G 2) (c₁ r₁ c₂ r₂ : F),
        c₁ <> c₂ -> 
        decryption_proof_accepting_conversations g h cp₁ cp₂ m 
          (a; [c₁]; [r₁]) = true -> (* and it's accepting *) 
        decryption_proof_accepting_conversations g h cp₁ cp₂ m 
          (a; [c₂]; [r₂]) = true -> (* and it's accepting *)
        ∃ y : F, g^y = h ∧ cp₁^y = gop cp₂  (ginv m).
      Proof.
        intros * ha hb hc.
        cbn in hb, hc.
        destruct (vector_inv_S a) as (ah & atl & hd).
        destruct (vector_inv_S atl) as (ahh & atll & he).
        subst. 
        eapply andb_true_iff in hb, hc.
        rewrite !dec_true in hb, hc.
        destruct hc as (hcl & hcr).
        destruct hb as (hbl & hbr).
        exists ((r₁ - r₂) * inv (c₁ - c₂)).
        split.
        +
          eapply f_equal with (f := ginv) in hcl.
          rewrite connection_between_vopp_and_fopp in hcl.
          rewrite group_inv_flip  in hcl.
          rewrite commutative in hcl.
          pose proof (@rewrite_gop G gop _ _ _ _ hbl hcl) as Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          assert (Hwt : (gop ah (h ^ c₁))= (gop (h ^ c₁) ah)).
          rewrite commutative; reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
          in Hcom.
          assert (Hwt : (gop ah (gop (ginv ah) (ginv (h ^ c₂)))) = 
           (ginv (h ^ c₂))).
          rewrite associative.
          rewrite group_is_right_inverse,
          monoid_is_left_idenity;
          reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          rewrite connection_between_vopp_and_fopp in Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          apply f_equal with (f := fun x => x^(inv (c₁ + opp c₂)))
          in Hcom.
          rewrite !smul_pow_up in Hcom.
          assert (Hw : (c₁ + opp c₂) * inv (c₁ + opp c₂) = 
          (inv (c₁ + opp c₂) * (c₁ + opp c₂))).
          rewrite commutative; reflexivity.
          rewrite Hw in Hcom; clear Hw.
          rewrite field_is_left_multiplicative_inverse in Hcom.
          pose proof vector_space_field_one as Hone.
          unfold is_field_one in Hone.
          specialize (Hone h).
          rewrite Hone in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          exact Hcom.
          intros Hf.
          pose proof ring_neq_sub_neq_zero c₁ c₂ ha as Hw.
          apply Hw.
          rewrite ring_sub_definition.
          exact Hf.
          all:typeclasses eauto.
        +
          cbn in * |- .
          remember (gop cp₂ (ginv m)) as ct.
          eapply f_equal with (f := ginv) in hcr.
          rewrite connection_between_vopp_and_fopp in hcr.
          rewrite group_inv_flip  in hcr.
          rewrite commutative in hcr.
          pose proof (@rewrite_gop G gop _ _ _ _ hbr hcr) as Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          assert (Hwt : (gop ahh (ct ^ c₁)) = (gop (ct ^ c₁) ahh)).
          rewrite commutative; reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
          in Hcom.
          assert (Hwt : (gop ahh (gop (ginv ahh) (ginv (ct ^ c₂)))) = 
           (ginv (ct ^ c₂))).
          rewrite associative.
          rewrite group_is_right_inverse,
          monoid_is_left_idenity;
          reflexivity.
          rewrite Hwt in Hcom; clear Hwt.
          rewrite connection_between_vopp_and_fopp in Hcom.
          rewrite <-(@vector_space_smul_distributive_fadd 
            F (@eq F) zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow) in Hcom.
          apply f_equal with (f := fun x => x^(inv (c₁ + opp c₂)))
          in Hcom.
          rewrite !smul_pow_up in Hcom.
          assert (Hw : (c₁ + opp c₂) * inv (c₁ + opp c₂) = 
          (inv (c₁ + opp c₂) * (c₁ + opp c₂))).
          rewrite commutative; reflexivity.
          rewrite Hw in Hcom; clear Hw.
          rewrite field_is_left_multiplicative_inverse in Hcom.
          pose proof vector_space_field_one as Hone.
          unfold is_field_one in Hone.
          specialize (Hone ct).
          rewrite Hone in Hcom.
          rewrite <-ring_sub_definition in Hcom.
          exact Hcom.
          intros Hf.
          pose proof ring_neq_sub_neq_zero c₁ c₂ ha as Hw.
          apply Hw.
          rewrite ring_sub_definition.
          exact Hf.
          all:typeclasses eauto.
      Qed.



      (* zero-knowledge *)
      Lemma construct_decryption_proof_elgamal_special_honest_verifier_zkp 
        (x : F) 
        (g h m c₁ c₂ : G)
        (R : g^x = h ∧ c₁^x = gop c₂ (ginv m)) : 
        forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
        List.map (fun '(a, p) => 
          (decryption_proof_accepting_conversations g h c₁ c₂ m a, p))
          (construct_decryption_proof_elgamal_real_distribution lf Hlfn x g c₁ c) = 
        List.map (fun '(a, p) => 
          (decryption_proof_accepting_conversations g h c₁ c₂ m a, p))
          (construct_decryption_proof_elgama_simulator_distribution lf Hlfn g h c₁ c₂ m c).
      Proof.
        intros *.
        eapply generalised_cp_special_honest_verifier_zkp.
        exact R.
      Qed.


    Theorem decryption_proof_accepting_conversations_vector_completeness : 
      ∀ (n : nat) (x : F) (g h : G) 
      (cps : Vector.t (G * G) n) (ms : Vector.t G n) (us cs : Vector.t F n), 
      (g^x = h) -> (∀ (i : Fin.t n), (fst (Vector.nth cps i))^x = 
      gop (snd (Vector.nth cps i)) (ginv ((Vector.nth ms i)))) ->
      decryption_proof_accepting_conversations_vector g h 
        cps ms (construct_decryption_proof_elgamal_real_vector x g cps us cs) = true. 
    Proof.
      induction n as [|n ihn].
      + 
        intros * ha hb. 
        reflexivity.
      + 
        intros * ha hb.
        destruct (vector_inv_S cps) as ((c₁, c₂) & cpst & hc).
        destruct (vector_inv_S ms) as (msh & mst & hd).
        destruct (vector_inv_S us) as (ush & ust & he).
        destruct (vector_inv_S cs) as (csh & cst & hf).
        subst. cbn.
        eapply Bool.andb_true_iff. split.
        eapply construct_decryption_proof_elgamal_real_completeness.
        ++
          specialize (hb Fin.F1).
          cbn in hb. 
          exact (conj eq_refl hb).
        ++
          eapply ihn;
          [exact eq_refl | ].
          intro f. exact (hb (Fin.FS f)).
    Qed.
    
    End Proofs.
  End DecProof. 
End DL.

