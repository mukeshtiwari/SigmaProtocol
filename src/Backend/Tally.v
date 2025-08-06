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
    | winners : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) ->  
      list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) -> 
      list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n) -> 
      Vector.t F n -> state.

    Print Permutation.
    Inductive count : state -> Type :=
    (* 
    - ax bootstraps the election 
      ms is encryption of zero -- ms = (@encrypted_ballot F G gop gpow g h _
        (repeat_ntimes n zero) rs)
      pf is decryption proof that ms decryptions to g^zero.

      Is it overkill? Can I not simply reveal the randomness rs used to 
      produce ms? 
    *)
    | ax 
      (ms : Vector.t (G * G) n) (pf : Vector.t (@sigma_proto F G 2 1 1) n) : 
      Vector.fold_left  (fun acc '((c₁, c₂), pfv) => 
        (acc && (@decryption_proof_accepting_conversations F 
          G ginv gop gpow Gdec g h c₁ c₂ (g ^ zero) pfv))%bool) true 
        (@zip_with _ _ _ _ (fun cp pfcp => (cp, pfcp)) ms pf) = true ->
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
      (ms nms : Vector.t (G * G) n)
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) :
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
      (ms : Vector.t (G * G) n)
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) :
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
      pt is discrete logarithm search over ds 
    *)
    | cfinish 
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) 
      (ms : Vector.t (G * G) n) (ds : Vector.t G n) 
      (pf : Vector.t (@sigma_proto F G 2 1 1) n) 
      (pt : Vector.t F n) : 
      count (partial us vbs inbs ms) -> 
      Permutation us (vbs ++ inbs) -> 
      (∀ (i : Fin.t n), g ^ (Vector.nth pt i) = Vector.nth ds i) -> 
      Vector.fold_left  (fun acc '(p, ((c₁, c₂), pfv)) => 
        (acc && (@decryption_proof_accepting_conversations F 
          G ginv gop gpow Gdec g h c₁ c₂ p pfv))%bool) true
        (@zip_with _ _ _ _ (fun pt cppfcp => (pt, cppfcp)) ds 
        ((@zip_with _ _ _ _ (fun cp pfcp => (cp, pfcp)) ms pf))) = true ->
      count (partial us vbs inbs ms) -> count (winners us vbs inbs pt).



    Fixpoint compute_final_tally (rs : Vector.t F n) 
      (us : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) : 
      existsT (vbs inbs :  list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n))
        (ms : Vector.t (G * G) n), count (partial us vbs inbs ms).
    Proof.
      destruct us as [| u us'].
      +
        set (ms :=  (@encrypted_ballot F G gop gpow g h _ (repeat_ntimes n zero) rs)).
        exists (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)),
        (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)), ms.
        refine (ax ms _ _).
        admit.
      +
        refine 
          (match @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h u return _  
        with 
        | true => _
        | false => _ 
        end ). 
        (* check if u is valid ballot or not? *)
    Admitted.






  End Defs.

  Section Proofs.

  End Proofs.
End Tally.