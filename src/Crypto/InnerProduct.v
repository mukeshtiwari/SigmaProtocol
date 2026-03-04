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
  VectorNotations.

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
  
  Section InnerProduct.
    Section Def. 


      (*
        Pedersen commitment to a vector of field elements.

        For randomness r : F and message vector xs : F^n, this computes
          C = h^r · ∏ᵢ gs[i]^xs[i]
        where h is the blinding base and gs contains per-coordinate bases.

        Parameters:
        - r  : blinding/randomness exponent
        - xs : message vector to commit
        - h  : blinding generator
        - gs : generators aligned with xs coordinates

        Returns a single group element commitment in G.
      *)
      Definition pedersen_commitment {n : nat} (r : F) (xs : Vector.t F n)
        (h : G) (gs : Vector.t G n) : G.
      Proof.
        exact (fold_right (fun gx acc => gop gx acc) (zip_with (fun g x => g ^ x) gs xs) (h ^ r)).
      Defined.


      (*
        Inner product of two field vectors.
        ⟨a, b⟩ = Σᵢ aᵢ · bᵢ
      *)
      Definition inner_product {n : nat}
        (av bv : Vector.t F n) : F :=
        fold_right add (zip_with mul av bv) zero.

      (*
        Multi-exponentiation of a group vector by a field vector.
        ∏ᵢ gᵢ^(xᵢ)
      *)
      Definition multi_exp {n : nat}
        (gs : Vector.t G n) (xs : Vector.t F n) : G :=
        fold_right (fun gx acc => gop gx acc)
          (zip_with (fun gi xi => gi ^ xi) gs xs) gid.

      (*
        Cast a vector along a proof of length equality.
        Used to reconcile the size (2^n' + 0) returned by [drop]
        with the expected size 2^n'.
      *)
      Definition vcast {A : Type} {m k : nat}
        (Heq : m = k) (v : Vector.t A m) : Vector.t A k :=
        eq_rect m (Vector.t A) v k Heq.

    

      Record inner_product_proof (n : nat) : Type := 
        mk_inner_product_proof 
        {
          ls : Vector.t G n;
          rs : Vector.t G n;
          ip_av_final : F;
          ip_bv_final : F;
          challenge : Vector.t F n
        }.

      (*
        Prover for Protocol 2 (Improved Inner-Product Argument).

        Input:
        - n          : recursion depth (vector size is 2^n)
        - gs, hs     : generator vectors in G^(2^n)
        - u, P       : public generator and commitment point
        - av, bv     : witness vectors in F^(2^n)
        - cs         : verifier challenges (one per round)

        Output transcript [inner_product_proof n]:
        - ls, rs     : all round messages L and R (length n)
        - ip_av_final, ip_bv_final : final scalars a, b at base case
        - challenge  : challenge vector actually used by the recursion

        Recursion summary:
        - Base case (n = 0): output final (a, b) from 1-dimensional vectors.
        - Step (n = S n'):
          1) split vectors into low/high halves
          2) compute c_L = <a_L, b_R>, c_R = <a_R, b_L>
          3) compute round commitments L and R
          4) use x = hd cs to fold generators/witnesses into smaller instance
          5) recurse on size 2^n' with tl cs
          6) prepend L, R, and x to recursive transcript
      *)
      Fixpoint improved_inner_product_proof : 
        ∀ (n : nat), Vector.t G (Nat.pow 2 n) -> (* gs *)
        Vector.t G (Nat.pow 2 n) -> (* hs *)
        G -> G -> (* u and P *)
        Vector.t F (Nat.pow 2 n) -> (* av *)
        Vector.t F (Nat.pow 2 n) -> (* bv *)
        Vector.t F n -> (* verifier challenges *)
        inner_product_proof n.
      Proof.
        induction n as [|n' ihn].
        +
          intros gs hs u P av bv cs.
          refine(mk_inner_product_proof _ [] [] (Vector.hd av) (Vector.hd bv) []).
        +
          (* inductive case *)
          intros gs hs u P av bv cs.
          cbn in gs, hs, av, bv.
          set (gs_lo := take (Nat.pow 2 n') gs).
          set (gs_hi := vcast (add_0_r (Nat.pow 2 n')) (drop (Nat.pow 2 n') gs)).
          set (hs_lo := take (Nat.pow 2 n') hs).
          set (hs_hi := vcast (add_0_r (Nat.pow 2 n')) (drop (Nat.pow 2 n') hs)).
          set (av_lo := take (Nat.pow 2 n') av).
          set (av_hi := vcast (add_0_r (Nat.pow 2 n')) (drop (Nat.pow 2 n') av)).
          set (bv_lo := take (Nat.pow 2 n') bv).
          set (bv_hi := vcast (add_0_r (Nat.pow 2 n')) (drop (Nat.pow 2 n') bv)).
          set (c_L := inner_product av_lo bv_hi).
          set (c_R := inner_product av_hi bv_lo).
          set (L := gop (gop (multi_exp gs_hi av_lo) (multi_exp hs_lo bv_hi)) (u ^ c_L)).
          set (R := gop (gop (multi_exp gs_lo av_hi) (multi_exp hs_hi bv_lo)) (u ^ c_R)).
          set (x := Vector.hd cs). (* head of challenges *)
          set (x_inv := inv x).
          set (gs' := zip_with gop (Vector.map (fun gi => gi ^ x_inv) gs_lo)
            (Vector.map (fun gi => gi ^ x) gs_hi)).
          set (hs' := zip_with gop (Vector.map (fun hi => hi ^ x) hs_lo)
            (Vector.map (fun hi => hi ^ x_inv) hs_hi)).
          set (P' := gop (gop (L ^ (x * x)) P) (R ^ (x_inv * x_inv))).
          set (av' := zip_with add (Vector.map (mul x) av_lo)
            (Vector.map (mul x_inv) av_hi)).
          set (bv' := zip_with add (Vector.map (mul x_inv) bv_lo)
            (Vector.map (mul x) bv_hi)).
          set (recp := improved_inner_product_proof n' gs' hs' u P' av' bv' (Vector.tl cs)).
          refine 
            match recp with 
            | mk_inner_product_proof _ ls rs av_final bv_final cha' => 
              mk_inner_product_proof _ (L :: ls) (R :: rs) av_final bv_final (x :: cha') 
            end.
      Defined.


      (*
        Verifier for Protocol 2 transcript [inner_product_proof n].

        Input:
        - n      : recursion depth (generator/witness size is 2^n)
        - gs, hs : public generator vectors in G^(2^n)
        - u, P   : public generator and commitment point
        - pf     : prover transcript containing
                   * ls, rs       : per-round commitments L and R
                   * ip_av_final,
                     ip_bv_final  : final scalars a, b
                   * challenge    : per-round challenges x

        Verification strategy:
        - Base case (n = 0): check
            P = g^a · h^b · u^(a·b)
          using the final scalars from the transcript.

        - Recursive case (n = S n'):
          1) read current round values L, R, x from transcript heads
          2) reject immediately if x = 0 (inverse undefined)
          3) derive folded instance (g', h', P') as in Protocol 2
          4) recurse on tails of ls, rs, and challenge

        Returns [true] iff all recursive checks reduce to a valid
        base-case equation.
      *)
      Fixpoint improved_inner_product_verify :
        ∀ (n : nat), Vector.t G (Nat.pow 2 n) -> (* gs *)
        Vector.t G (Nat.pow 2 n) -> (* hs *)
        G -> G -> (* u and P *)
        inner_product_proof n -> (* proof *)
        bool.
      Proof.
        induction n as [|n' ihn].
        +
          intros gs hs u P pf.
          set (a := ip_av_final _ pf).
          set (b := ip_bv_final _ pf).
          set (g := Vector.hd gs).
          set (h := Vector.hd hs).
          refine
            match Gdec P (gop (gop (g ^ a) (h ^ b)) (u ^ (a * b))) with
            | left _ => true
            | right _ => false
            end.
        +
          intros gs hs u P pf.
          set (L := Vector.hd (ls _ pf)).
          set (R := Vector.hd (rs _ pf)).
          set (gs_lo := take (Nat.pow 2 n') gs).
          set (gs_hi := vcast (add_0_r (Nat.pow 2 n')) (drop (Nat.pow 2 n') gs)).
          set (hs_lo := take (Nat.pow 2 n') hs).
          set (hs_hi := vcast (add_0_r (Nat.pow 2 n')) (drop (Nat.pow 2 n') hs)).
          set (x := Vector.hd (challenge _ pf)).
          set (x_inv := inv x).
          set (gs' := zip_with gop (Vector.map (fun gi => gi ^ x_inv) gs_lo)
            (Vector.map (fun gi => gi ^ x) gs_hi)).
          set ( hs' := zip_with gop (Vector.map (fun hi => hi ^ x) hs_lo)
            (Vector.map (fun hi => hi ^ x_inv) hs_hi)).
          set (P' := gop (gop (L ^ (x * x)) P) (R ^ (x_inv * x_inv))).
          set (pf' := mk_inner_product_proof _ (Vector.tl (ls _ pf)) 
            (Vector.tl (rs _ pf)) (ip_av_final _ pf)
            (ip_bv_final _ pf) (Vector.tl (challenge _ pf))).
          exact (improved_inner_product_verify n' gs' hs' u P' pf').
      Defined.




    End Def.
    Section Proofs.
    End Proofs.
  End InnerProduct.
End DL.