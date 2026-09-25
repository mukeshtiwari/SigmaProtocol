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

    (* A ballot: one ElGamal ciphertext with its 0/1 encryption proof per 
      candidate, and the overall proof that the ballot carries between 0 and 
      n approvals (a disjunctive proof over the homomorphic product of the 
      ciphertexts, see Approval.v). *)
    Definition ballot : Type := 
      (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n * 
       @Sigma.sigma_proto F (G * G) (S n) (S (S n)) (S n))%type.

    (* both the individual proofs and the overall proof must be accepted *)
    Definition verify_ballot_full (b : ballot) : bool :=
      @verify_ballot F zero one add Fdec G gid ginv gop gpow Gdec n g h b.

   
    (* each ciphertext comes with encryption sigma proof so a ballot is 
    a ciphertext and encryption proof of 0 or 1: 
    G * G *  @Sigma.sigma_proto F (G * G) 2 3 2 *)
    Inductive state : Type :=
    | partial : list (ballot) ->  
      list (ballot) -> 
      list (ballot) -> 
      Vector.t (G * G) n -> state
    | finished : list (ballot) ->  
      list (ballot) -> 
      list (ballot) -> 
      Vector.t F n -> bool -> state.

    
    Inductive count : state -> Type :=
    (* 
    - ax bootstraps the election 
      ms is a vector of (gid, gid) 
    *)
    | ax  (ms : Vector.t (G * G) n) :  
      (∀ (i : Fin.t n), Vector.nth ms i = (gid, gid)) -> 
      count (partial (@List.nil (ballot))
        (@List.nil (ballot)) 
        (@List.nil (ballot)) ms)
    (* 
      u is a valid ballot with encryption proof of 0 or 1 
      ms is the tally so far and nms is the new tally nms = ms + u 
      us the ballot seen so far 
      vbs is the valid ballots and included in the count 
      inbs is the invalid ballots  
      count (partial us vbs inbs ms) is the partial count seen so far
    *)
    | cvalid 
      (u : ballot)
      (us vbs inbs : list (ballot)) 
      (ms nms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      verify_ballot_full u = true (* u is valid vote *) ->
      nms = @mul_encrypted_ballots G gop _ ms (Vector.map fst (fst u)) ->
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
      (u : ballot)
      (us vbs inbs : list (ballot)) 
      (ms : Vector.t (G * G) n) :
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      verify_ballot_full u = false (* u is invalid vote *) ->
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
      (us vbs inbs : list (ballot)) 
      (ms : Vector.t (G * G) n) (ds : Vector.t G n) 
      (pf : Vector.t (@sigma_proto F G 2 1 1) n) 
      (pt : Vector.t F n) (b : bool) : 
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      (* pt is checked against ds: b records whether g ^ pt_i = ds_i holds 
        for every candidate i. The check is explicit, so no assumption on 
        the discrete-logarithm search is needed; a certificate with 
        b = true is what finished_true_correct below unpacks. *)
      vector_forallb (fun u => u) 
        (zip_with (fun u v => match Gdec (g ^ u) v with
          | left _ => true 
          | right _ => false 
          end) pt ds) = b -> 
      @decryption_proof_accepting_conversations_vector F G ginv gop gpow 
        Gdec _ g h ms ds pf = true -> 
      count (finished us vbs inbs pt b).



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
      ∀ (bs : list (ballot)), 
      existsT (vbs inbs :  list (ballot))
        (ms : Vector.t (G * G) n), (count (partial bs vbs inbs ms) *
        Permutation bs (vbs ++ inbs))%type.
    Proof.
      intro ha.
      (* we walk through the whole bs and and build up a tally bottom-up *)
      refine(fix fn (bs : list (ballot)) {struct bs} := 
        match bs with 
        | @List.nil _ => _ 
        | @List.cons _ bh bt => _ 
        end).
      + 
        set (ms := repeat_ntimes n (gid, gid)).
        exists (@List.nil (ballot)),
        (@List.nil (ballot)), ms.
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
          (match verify_ballot_full bh as v return 
          verify_ballot_full bh = v -> _ 
          with 
          | true => fun hv => _ 
          | false => fun hv => _ 
          end eq_refl). 
        (* check if u is valid ballot or not? *)
        (* true case *)
        ++
          destruct (fn bt) as (vbs & inbs &  ms & hb & hc).
          exists (@List.cons _ bh vbs), inbs, 
            (@mul_encrypted_ballots G gop _ ms (Vector.map fst (fst bh))).
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

    (* Discrete-logarithm search, supplied by the caller (the extracted 
      driver uses a linear search). Its result is checked, not trusted: 
      the b component of the final state records whether g ^ pt_i = ds_i 
      for every i. *)
    Variable (discrete_logarithm_search : G -> G -> F).

    (* us and cs is the randomness to produce final honest decryption proof *)
    Definition compute_final_count (x : F) (us cs : Vector.t F n) : 
      g^x = h -> (* relation between public key and group generator *)  
      ∀ (bs : list (ballot)), 
      existsT (vbs inbs : list (ballot)) (pt : Vector.t F n) (b : bool), 
        count (finished bs vbs inbs pt b).
    Proof.
      intros * ha *.
      destruct (compute_final_tally x ha bs) as (vbs & inbs & ms & hb & hc).
      set (ds := @decrypted_ballot F G ginv gop gpow x _ ms).
      set (pt := (map (fun hy => discrete_logarithm_search g hy) ds)).
      set (pf := @construct_decryption_proof_elgamal_real_vector F add mul G gpow 
          _ x g ms us cs).
      set (b := vector_forallb (fun u => u) 
        (zip_with (fun u v => match Gdec (g ^ u) v with
          | left _ => true 
          | right _ => false 
          end) pt ds)).
      exists vbs, inbs, pt, b.
      refine(cfinish bs vbs inbs ms ds pf pt b hb hc eq_refl _).
      eapply decryption_proof_accepting_conversations_vector_completeness;
      [exact ha | ].
      intro f.
      unfold ds.
      eapply compute_final_tally_aux2; exact ha.
    Defined.

    (* A certificate whose final flag is true says that every plaintext 
      count is the discrete logarithm of the corresponding entry of the 
      decrypted tally, and that the decryption proofs are accepted. *)
    Theorem finished_true_correct : 
      forall (us vbs inbs : list ballot) (pt : Vector.t F n),
      count (finished us vbs inbs pt true) ->
      ∃ (ms : Vector.t (G * G) n) (ds : Vector.t G n) 
        (pf : Vector.t (@sigma_proto F G 2 1 1) n),
        Permutation us (vbs ++ inbs) ∧
        (∀ (i : Fin.t n), g ^ (Vector.nth pt i) = Vector.nth ds i) ∧
        @decryption_proof_accepting_conversations_vector F G ginv gop gpow 
          Gdec _ g h ms ds pf = true.
    Proof.
      intros * hc.
      inversion hc as [| | | us' vbs' inbs' ms ds pf pt' b hcount hperm hb hdec]; 
      subst.
      exists ms, ds, pf.
      refine (conj hperm (conj _ hdec)).
      intro i.
      rewrite vector_forallb_correct in hb.
      specialize (hb i).
      rewrite nth_zip_with in hb.
      destruct (Gdec (g ^ pt[@i]) ds[@i]) as [he | he]; 
      [exact he | inversion hb].
    Qed.

  End Defs.

End Tally.
