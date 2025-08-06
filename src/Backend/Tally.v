From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin. 
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
      Vector.t bool n -> state.

    Print verify_encryption_ballot_proof.
    Inductive count : state -> Type :=
    | ax (ms : Vector.t (G * G) n) (pf : Vector.t (@sigma_proto F G 2 1 1) n) : 
        Vector.fold_left  (fun acc '((c₁, c₂), pfv) => 
          (acc && (@decryption_proof_accepting_conversations F 
          G ginv gop gpow Gdec g h c₁ c₂ gid pfv))%bool) true 
        (@zip_with _ _ _ _ (fun cp pfcp => (cp, pfcp)) ms pf) = true ->
        count (partial (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n))
          (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) 
          (@List.nil (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) ms) 
          (* initial tally ms encryption of 0 *)
    | cvalid (u : Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)
      (ms nms : Vector.t (G * G) n)
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) :
      count (partial us vbs inbs ms) -> 
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h u = true (* u is valid vote *) ->
      nms = @mul_encrypted_ballots G gop _ ms (Vector.map fst u) ->
      count (partial (@List.cons _ u us) (@List.cons _ u vbs) inbs nms)
    | cinvalid (u : Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)
      (ms : Vector.t (G * G) n)
      (us vbs inbs : list (Vector.t (G * G * @Sigma.sigma_proto F (G * G) 2 3 2) n)) :
      count (partial us vbs inbs ms) -> 
      @verify_encryption_ballot_proof F zero one add Fdec G ginv gop gpow Gdec
        _ g h u = false (* u is invalid vote *) ->
      count (partial (@List.cons _ u us) vbs (@List.cons _ u inbs) ms).



      
      


  End Defs.

  Section Proofs.

  End Proofs.
End Tally.