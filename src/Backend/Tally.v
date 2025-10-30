From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import 
  Util.
From Crypto Require Import 
  Elgamal EncProof Sigma DecProof.
From Frontend Require Import 
  Approval.

Import VectorNotations.

Section Tally.
  
  (* This code runs at backend. *)

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

  Section Defs.

    (* We have n + 1 candidates *)
    Context {n : nat} 
      (g h : G).

   
    (* 
    Definition wins_type {n : nat} (c : @cand n) (f : Vector.t F n) : Type := 
      ∀ (d : cand), f d <= f c.

    Definition loses_type {cand : Type} (c : cand) (f : cand -> nat) : Type :=
      existsT (d : cand), f c < f d.

    Fixpoint wins_loses_type {cand : Type} (l : list cand) (f : cand -> nat) 
      : ∀ (c : cand), wins_type c f + loses_type c f. 
    *)

    (* each ciphertext comes with encryption sigma proof so a ballot is 
    a ciphertext and encryption proof of 0 or 1: 
    G * G *  @Sigma.sigma_proto F (G * G) 2 3 2 *)
    Inductive state : Type :=
    | partial : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) ->  
      list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) -> 
      list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) -> 
      Vector.t (G * G) n -> state
    | finished : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) ->  
      list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) -> 
      list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) -> 
      Vector.t F n -> state.

    
    Inductive count : state -> Type :=
    (* 
    - ax bootstraps the election 
      ms is a vector of (gid, gid) 
    *)
    | ax  (ms : Vector.t (G * G) n) :  
      (∀ (i : Fin.t n), Vector.nth ms i = (gid, gid)) -> 
      count (partial (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n))
        (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) 
        (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) ms)
    (* 
      u is a valid ballot with encryption proof of 0 or 1 
      ms is the tally so far and nms is the new tally nms = ms + u 
      us the ballot seen so far 
      vbs is the valid ballots and included in the count 
      inbs is the invalid ballots  
      count (partial us vbs inbs ms) is the partial count seen so far
    *)
    | cvalid 
      (u : Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) 
      (ms nms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h u = true (* u is valid vote *) ->
      nms = @mul_encrypted_ballots G gop _ ms (Vector.map fst u) ->
      count (partial (@List.cons _ u us) (@List.cons _ u vbs) inbs nms)
    (* 
      u is invalid ballot 
      ms is the tally so far 
      us the ballot seen so far 
      vbs is the valid ballots and included in the count 
      inbs is the invalid ballots 
      count (partial us vbs inbs ms) is the partial count seen so far
    *)
    | cinvalid 
      (u : Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) 
      (ms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h u = false (* u is invalid vote *) ->
      count (partial (@List.cons _ u us) vbs (@List.cons _ u inbs) ms)
    (*
      us all the ballots in an election 
      vbs is the valid ballots and included in the count 
      inbs is the invalid ballots 
      ms final tally 
      ds is decryption of finally (it's group elements)
      pt is obtained by discrete logarithm search over ds 
    *)
    | cfinish 
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) 
      (ms : Vector.t (G * G) n) (ds : Vector.t G n) 
      (pf : Vector.t (@sigma_proto F G 2 1 1) n) 
      (pt : Vector.t F n) : 
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      (∀ (i : Fin.t n), g ^ (Vector.nth pt i) = Vector.nth ds i) -> 
      @decryption_proof_accepting_conversations_vector F G ginv gop gpow 
        Gdec _ g h ms ds pf = true -> 
      count (finished us vbs inbs pt).



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


    Theorem  compute_final_tally_aux2 : ∀ (m : nat) (f : Fin.t m) 
      (ms : Vector.t (G * G) m) (x : F), g^x = h -> 
      fst ms[@f] ^ x = gop (snd ms[@f]) 
        (ginv (@decrypted_ballot F G ginv gop gpow x _ ms)[@f]). 
    Proof.
      induction m as [|m ihm].
      +
        intros *. refine match f with end.
      +
        intros * ha.
        destruct (vector_inv_S ms) as ((c₁, c₂) & mst & hb).
        destruct (fin_inv_S _ f) as [f' | (f' & hc)].
        ++
          subst; cbn.
          remember (ginv (c₁ ^ x)) as ct.
          (* c₁ ^ x = gop c₂ (ginv (gop c₂ (ginv (c₁ ^ x)))) *)
          assert (ha : (ginv (gop c₂ ct)) = 
            gop (ginv ct) (ginv c₂)).
          rewrite group_inv_flip. reflexivity.
          rewrite ha; clear ha.
          assert (ha : (gop (ginv ct) (ginv c₂)) = gop (ginv c₂) (ginv ct)).
          rewrite commutative. reflexivity. 
          rewrite ha; clear ha.
          assert (Hwt : (gop c₂ (gop (ginv c₂) (ginv ct))) = (ginv ct)).
          {
            rewrite associative.
            rewrite group_is_right_inverse,
            monoid_is_left_idenity;
            reflexivity.
          }
          rewrite Hwt; clear Hwt. subst.
          rewrite group_inv_inv.
          reflexivity.
        ++
          subst; cbn.
          eapply ihm.
          reflexivity.
    Qed.
  
         
    (* 
      us and cs is the randomess used to construct 
      decryption proof. 
    *)
    Definition compute_final_tally (x : F) (* rs us cs : Vector.t F n *) : 
      g^x = h -> (* relation between public key and group generator *)  
      ∀ (bs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)), 
      existsT (vbs inbs :  list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n))
        (ms : Vector.t (G * G) n), (count (partial bs vbs inbs ms) *
        Permutation bs (vbs ++ inbs))%type.
    Proof.
      intro ha.
      (* we walk through the whole bs and and build up a tally bottom-up *)
      refine(fix fn (bs : list (Vector.t (G * G * sigma_proto) n)) {struct bs} := 
        match bs with 
        | @List.nil _ => _ 
        | @List.cons _ bh bt => _ 
        end).
      + 
        set (ms := repeat_ntimes n (gid, gid)).
        exists (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)),
        (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)), ms.
        refine(pair (ax ms _) _).
        ++
          intros *.
          unfold ms.
          eapply repeat_ntimes_correct.
        ++
          reflexivity.
      +
        (* check if bh is valid ballot or not *)
        refine 
          (match @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
          _ g h bh as v return 
          @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
          _ g h bh = v -> _ 
          with 
          | true => fun hv => _ 
          | false => fun hv => _ 
          end eq_refl). 
        (* check if u is valid ballot or not? *)
        (* true case *)
        ++
          destruct (fn bt) as (vbs & inbs &  ms & hb & hc).
          exists (@List.cons _ bh vbs), inbs, 
            (@mul_encrypted_ballots G gop _ ms (Vector.map fst bh)).
          refine(pair _ _ ). 
          *
            eapply cvalid. exact hb. 
            exact hc.
            exact hv. reflexivity.
          *
            cbn.
            eapply Permutation_cons;
            [exact eq_refl | exact hc]. 
        ++
          (* false case *)
          destruct (fn bt) as (vbs & inbs &  ms & hb & hc).
          exists vbs, (@List.cons _ bh inbs), ms.
          refine(pair _ _).
          *
            eapply cinvalid; assumption.
          *
            cbn.
            eapply Permutation_trans with (l' := List.cons bh (vbs ++ inbs)).
            eapply Permutation_cons; [exact eq_refl | exact hc].
            eapply Permutation_middle.
    Defined.

    (* Discrete logarithms search and coherence axiom on it. This is for 
    searching the exponent values in the tally. *)
    Variable (discrete_logarithm_search : G -> G -> F).
    Axiom (hdiscrete : ∀ (y : F) (hx hy : G), discrete_logarithm_search hx hy = y ->
      hx^y = hy). 

    Theorem compute_final_count_aux : ∀ (m : nat) (i : Fin.t m) 
      (ds : Vector.t G m) (pt : Vector.t F m), 
      pt = map (λ hy : G, discrete_logarithm_search g hy) ds -> 
      g ^ pt[@i] = ds[@i].
    Proof.
      induction m as [|m ihm].
      +
        intros * ha.
        refine match i with end.
      +
        intros * ha.
        destruct (vector_inv_S ds) as (dsh & dst & hb).
        destruct (vector_inv_S pt) as (pth & ptt & hc).
        destruct (fin_inv_S _ i) as [f' | (f' & hd)].
        ++
          subst; cbn.
          now erewrite hdiscrete.
        ++
          subst; cbn.
          now eapply ihm.
    Qed.
   
    (* us and cs is the randomness to produce final honest decryption proof *)
    Definition compute_final_count (x : F) (us cs : Vector.t F n) : 
      g^x = h -> (* relation between public key and group generator *)  
      ∀ (bs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)), 
      existsT (vbs inbs :  
        list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n))
        (pt : Vector.t F n), count (finished bs vbs inbs pt).
    Proof.
      intros * ha *.
      destruct (compute_final_tally x ha bs) as (vbs & inbs & ms & hb & hc).
      set (ds := @decrypted_ballot F G ginv gop gpow x _ ms).
      set (pt := (map (fun hy => discrete_logarithm_search g hy) ds)).
      set (pf := @construct_decryption_proof_elgamal_real_vector F add mul G gpow 
          _ x g ms us cs).
      exists vbs, inbs, pt.
      refine(cfinish bs vbs inbs ms ds pf pt hb hc _ _).
      intro f. eapply compute_final_count_aux;
      unfold pt; reflexivity.
      eapply decryption_proof_accepting_conversations_vector_completeness;
      [exact ha | ].
      intro f.
      unfold ds.
      eapply compute_final_tally_aux2; exact ha.
    Defined.

  End Defs.

End Tally.
