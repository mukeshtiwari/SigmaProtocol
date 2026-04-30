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
        exact (fold_right (fun gx acc => gop gx acc) 
          (zip_with (fun g x => g ^ x) gs xs) (h ^ r)).
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
          set (gs_lo_hi := splitat (Nat.pow 2 n') gs).
          set (gs_lo := fst gs_lo_hi).
          set (gs_hi := vcast (add_0_r (Nat.pow 2 n')) (snd gs_lo_hi)).
          set (hs_lo_hi := splitat (Nat.pow 2 n') hs).
          set (hs_lo := fst hs_lo_hi).
          set (hs_hi := vcast (add_0_r (Nat.pow 2 n')) (snd hs_lo_hi)).
          set (av_lo_hi := splitat (Nat.pow 2 n') av).
          set (av_lo := fst av_lo_hi).
          set (av_hi := vcast (add_0_r (Nat.pow 2 n')) (snd av_lo_hi)).
          set (bv_lo_hi := splitat (Nat.pow 2 n') bv).
          set (bv_lo := fst bv_lo_hi).
          set (bv_hi := vcast (add_0_r (Nat.pow 2 n')) (snd bv_lo_hi)).
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
          2) derive folded instance (g', h', P') as in Protocol 2
          3) recurse on tails of ls, rs, and challenge

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
          set (gs_lo_hi := splitat (Nat.pow 2 n') gs).
          set (gs_lo := fst gs_lo_hi).
          set (gs_hi := vcast (add_0_r (Nat.pow 2 n')) (snd gs_lo_hi)).
          set (hs_lo_hi := splitat (Nat.pow 2 n') hs).
          set (hs_lo := fst hs_lo_hi).
          set (hs_hi := vcast (add_0_r (Nat.pow 2 n')) (snd hs_lo_hi)).
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

      (*
        Non-trivial discrete-log relation among a generator vector [gs].

        This property states that there exists a coefficient vector [xs]
        such that:
          1) multi_exp gs xs = gid, i.e., ∏ᵢ gs[i]^(xs[i]) is the group identity,
          2) xs is not the all-zero vector.

        Intuition: the generators are linearly dependent in the exponent,
        and the dependence is non-trivial (not the obvious zero relation).
      *)
      Definition has_non_trivial_dlog_relation {m : nat} 
        (gs : Vector.t G m) : Prop :=
        ∃ (xs : Vector.t F m), multi_exp gs xs = gid ∧ 
          (xs ≠ Vector.const zero m).

      Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
      Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).


      (*
        Lemma: multi_exp distributes over vector concatenation.
        multi_exp (gs1 ++ gs2) (xs1 ++ xs2) = multi_exp gs1 xs1 * multi_exp gs2 xs2
      *)
      Lemma multi_exp_append : ∀ n m (gs1 : Vector.t G n) (gs2 : Vector.t G m)
        (xs1 : Vector.t F n) (xs2 : Vector.t F m),
        multi_exp (gs1 ++ gs2) (xs1 ++ xs2) = gop (multi_exp gs1 xs1) (multi_exp gs2 xs2).
      Proof.
        induction n as [|n ihn]; intros m gs1 gs2 xs1 xs2.
        - pose proof (vector_inv_0 gs1) as h1.
          pose proof (vector_inv_0 xs1) as h2.
          subst; cbn. rewrite left_identity; reflexivity.
        - destruct (vector_inv_S gs1) as (gsh & gst & h1).
          destruct (vector_inv_S xs1) as (xsh & xst & h2).
          subst; cbn. rewrite ihn, associative; reflexivity.
      Qed.

      (*
        Lemma: inner_product distributes over vector concatenation.
        inner_product (av1 ++ av2) (bv1 ++ bv2) = inner_product av1 bv1 + inner_product av2 bv2
      *)
      Lemma inner_product_append : ∀ n m (av1 bv1 : Vector.t F n) (av2 bv2 : Vector.t F m),
        inner_product (av1 ++ av2) (bv1 ++ bv2) = add (inner_product av1 bv1) (inner_product av2 bv2).
      Proof.
        induction n as [|n ihn]; intros m av1 bv1 av2 bv2.
        - pose proof (vector_inv_0 av1) as h1.
          pose proof (vector_inv_0 bv1) as h2.
          subst; cbn. rewrite left_identity; reflexivity.
        - destruct (vector_inv_S av1) as (av1h & av1t & h1).
          destruct (vector_inv_S bv1) as (bv1h & bv1t & h2).
          subst; cbn. rewrite associative; rewrite ihn; reflexivity.
      Qed.

      (*
        Lemma: Re-arrange group products.
        (a * b) * (c * d) = (a * c) * (b * d)
      *)
      Lemma gop_simp : ∀ (a b c d : G),
        gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
      Proof.
        intros *.
        rewrite <-!associative.
        setoid_rewrite commutative at 2.
        rewrite <-!associative.
        setoid_rewrite commutative at 3.
        reflexivity.
      Qed.

      (*
        Lemma: multi_exp distributes over zip_with gop.
        multi_exp (zip_with gop gs1 gs2) xs = multi_exp gs1 xs * multi_exp gs2 xs
      *)
      Lemma multi_exp_zip_gop : ∀ n (gs1 gs2 : Vector.t G n) (xs : Vector.t F n),
        multi_exp (zip_with gop gs1 gs2) xs = gop (multi_exp gs1 xs) (multi_exp gs2 xs).
      Proof.
        induction n as [|n ihn]; intros gs1 gs2 xs.
        - pose proof (vector_inv_0 gs1) as h1.
          pose proof (vector_inv_0 gs2) as h2.
          pose proof (vector_inv_0 xs) as h3.
          subst; cbn. rewrite left_identity; reflexivity.
        - destruct (vector_inv_S gs1) as (gs1h & gs1t & h1).
          destruct (vector_inv_S gs2) as (gs2h & gs2t & h2).
          destruct (vector_inv_S xs) as (xsh & xst & h3).
          subst; cbn.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          rewrite !associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 7.
          rewrite !associative.
          setoid_rewrite commutative at 3.
          rewrite <-!associative.
          setoid_rewrite commutative at 4.
          rewrite associative.
          rewrite ihn.
          rewrite <-!associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          reflexivity.
      Qed.

      (*
        Lemma: multi_exp with exponentiated generators equals multi_exp with
        multiplied exponents.
      *)
      Lemma multi_exp_map_pow : ∀ n (gs : Vector.t G n) (xs : Vector.t F n) (a : F),
        multi_exp (Vector.map (fun g => g ^ a) gs) xs = multi_exp gs (Vector.map (fun x => a * x) xs).
      Proof.
        induction n as [|n ihn]; intros gs xs a.
        - pose proof (vector_inv_0 gs) as h1.
          pose proof (vector_inv_0 xs) as h2.
          subst; cbn; reflexivity.
        - destruct (vector_inv_S gs) as (gsh & gst & h1).
          destruct (vector_inv_S xs) as (xsh & xst & h2).
          subst; cbn.
          rewrite <-!smul_associative_fmul.
          rewrite !commutative.
          rewrite !smul_associative_fmul.
          rewrite ihn.
          reflexivity.
      Qed.

      (*
        Lemma: multi_exp distributes over zip_with add of exponents.
        multi_exp gs (zip_with add xs1 xs2) = multi_exp gs xs1 * multi_exp gs xs2
      *)
      Lemma multi_exp_add : ∀ n (gs : Vector.t G n) (xs1 xs2 : Vector.t F n),
        multi_exp gs (zip_with add xs1 xs2) = gop (multi_exp gs xs1) (multi_exp gs xs2).
      Proof.
        induction n as [|n ihn]; intros gs xs1 xs2.
        - pose proof (vector_inv_0 gs) as h1.
          pose proof (vector_inv_0 xs1) as h2.
          pose proof (vector_inv_0 xs2) as h3.
          subst; cbn. rewrite left_identity; reflexivity.
        - destruct (vector_inv_S gs) as (gsh & gst & h1).
          destruct (vector_inv_S xs1) as (xs1h & xs1t & h2).
          destruct (vector_inv_S xs2) as (xs2h & xs2t & h3).
          subst; cbn.
          rewrite <-smul_distributive_fadd.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          rewrite !associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 6.
          rewrite associative.
          rewrite ihn.
          rewrite <-!associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          reflexivity.
      Qed.

      (*
        Lemma: Bilinear expansion of inner_product over zip_with add.
        inner_product (zip_with add ws xs) (zip_with add ys zs) = 
          inner_product ws ys + inner_product ws zs + inner_product xs ys + inner_product xs zs
      *)
      Lemma inner_product_zip_add : ∀ n (ws xs ys zs : Vector.t F n),
        inner_product (zip_with add ws xs) (zip_with add ys zs) = 
          add (add (inner_product ws ys) (inner_product ws zs))
              (add (inner_product xs ys) (inner_product xs zs)).
      Proof.
        induction n as [|n ihn]; intros ws xs ys zs.
        - pose proof (vector_inv_0 ws) as h1.
          pose proof (vector_inv_0 xs) as h2.
          pose proof (vector_inv_0 ys) as h3.
          pose proof (vector_inv_0 zs) as h4.
          subst; cbn. field.
        - destruct (vector_inv_S ws) as (wsh & wst & h1).
          destruct (vector_inv_S xs) as (xsh & xst & h2).
          destruct (vector_inv_S ys) as (ysh & yst & h3).
          destruct (vector_inv_S zs) as (zsh & zst & h4).
          subst; cbn.
          rewrite ihn.
          field.
      Qed.

      (*
        Lemma: Pull scalar out of inner_product on the left.
        inner_product (Vector.map (mul a) xs) ys = a * inner_product xs ys
      *)
      Lemma inner_product_map_mul_left : ∀ n (a : F) (xs ys : Vector.t F n),
        inner_product (Vector.map (mul a) xs) ys = a * inner_product xs ys.
      Proof.
        induction n as [|n ihn]; intros a xs ys.
        - pose proof (vector_inv_0 xs) as h1.
          pose proof (vector_inv_0 ys) as h2.
          subst; cbn. field.
        - destruct (vector_inv_S xs) as (xsh & xst & h1).
          destruct (vector_inv_S ys) as (ysh & yst & h2).
          subst; cbn.
          rewrite ihn.
          ring.
      Qed.

      (*
        Lemma: Pull scalar out of inner_product on the right.
        inner_product xs (Vector.map (mul a) ys) = a * inner_product xs ys
      *)
      Lemma inner_product_map_mul_right : ∀ n (a : F) (xs ys : Vector.t F n),
        inner_product xs (Vector.map (mul a) ys) = a * inner_product xs ys.
      Proof.
        induction n as [|n ihn]; intros a xs ys.
        - pose proof (vector_inv_0 xs) as h1.
          pose proof (vector_inv_0 ys) as h2.
          subst; cbn. field.
        - destruct (vector_inv_S xs) as (xsh & xst & h1).
          destruct (vector_inv_S ys) as (ysh & yst & h2).
          subst; cbn.
          rewrite ihn.
          ring.
      Qed.

      (*
        Lemma: Map of scalar multiplication distributes over zip_with add.
        map (a*) (zip_with add xs ys) = zip_with add (map (a*) xs) (map (a*) ys)
      *)
      Lemma map_mul_zip_add : ∀ n (a : F) (xs ys : Vector.t F n),
        Vector.map (mul a) (zip_with add xs ys) = 
        zip_with add (Vector.map (mul a) xs) (Vector.map (mul a) ys).
      Proof.
        induction n as [|n ihn]; intros a xs ys.
        - pose proof (vector_inv_0 xs) as h1.
          pose proof (vector_inv_0 ys) as h2.
          subst; cbn; reflexivity.
        - destruct (vector_inv_S xs) as (xsh & xst & h1).
          destruct (vector_inv_S ys) as (ysh & yst & h2).
          subst; cbn.
          rewrite ihn; reflexivity.
      Qed.

      (*
        Core algebraic lemma: The folding identity for the improved inner-product argument.

        Given vectors gsl, gsh, hsl, hsh, avl, avh, bvl, bvh of length n, 
        generators u, and challenge x ≠ 0, define:
        - P = gsl^avl * gsh^avh * hsl^bvl * hsh^bvh * u^(<avl,bvl> + <avh,bvh>)
        - L = gsh^avl * hsl^bvh * u^(<avl,bvh>)
        - R = gsl^avh * hsh^bvl * u^(<avh,bvl>)
        - gs' = gsl^{x_inv} ∘ gsh^{x}  (pointwise product)
        - hs' = hsl^{x} ∘ hsh^{x_inv}  (pointwise product)
        - av' = x*avl + x_inv*avh       (pointwise)
        - bv' = x_inv*bvl + x*bvh       (pointwise)
        - P' = L^{x*x} * P * R^{x_inv*x_inv}

        Then: P' = (gs')^av' * (hs')^bv' * u^(<av', bv'>)
      *)
      Lemma folding_identity (n : nat) :
        ∀ (gsl gsh : Vector.t G n) (hsl hsh : Vector.t G n)
          (avl avh : Vector.t F n) (bvl bvh : Vector.t F n)
          (u : G) (x : F),
        x ≠ 0 →
        let x_inv := inv x in
        let P := gop (gop (multi_exp gsl avl) (multi_exp gsh avh))
                   (gop (gop (multi_exp hsl bvl) (multi_exp hsh bvh))
                     (u ^ (add (inner_product avl bvl) (inner_product avh bvh)))) in
        let L := gop (gop (multi_exp gsh avl) (multi_exp hsl bvh)) 
                   (u ^ (inner_product avl bvh)) in
        let R := gop (gop (multi_exp gsl avh) (multi_exp hsh bvl)) 
                   (u ^ (inner_product avh bvl)) in
        let gs' := zip_with gop (Vector.map (fun g => g ^ x_inv) gsl) 
                                (Vector.map (fun g => g ^ x) gsh) in
        let hs' := zip_with gop (Vector.map (fun h => h ^ x) hsl) 
                                (Vector.map (fun h => h ^ x_inv) hsh) in
        let av' := zip_with add (Vector.map (mul x) avl) 
                                (Vector.map (mul x_inv) avh) in
        let bv' := zip_with add (Vector.map (mul x_inv) bvl) 
                                (Vector.map (mul x) bvh) in
        let P' := gop (gop (L ^ (x * x)) P) (R ^ (x_inv * x_inv)) in
        P' = gop (multi_exp gs' av') (gop (multi_exp hs' bv') (u ^ (inner_product av' bv'))).
      Proof.
        induction n as [|n ihn]; intros gsl gsh hsl hsh avl avh bvl bvh u x hx.
        {
          (* Base case: n = 0, all vectors are empty *)
          pose proof (vector_inv_0 gsl) as h1.
          pose proof (vector_inv_0 gsh) as h2.
          pose proof (vector_inv_0 hsl) as h3.
          pose proof (vector_inv_0 hsh) as h4.
          pose proof (vector_inv_0 avl) as h5.
          pose proof (vector_inv_0 avh) as h6.
          pose proof (vector_inv_0 bvl) as h7.
          pose proof (vector_inv_0 bvh) as h8.
          subst; cbn.
          rewrite !right_identity, !left_identity.
          reflexivity.
        }
        {
          (* Inductive case: destruct each vector into head and tail *)
          destruct (vector_inv_S gsl) as (gslh & gslt & h1).
          destruct (vector_inv_S gsh) as (gshh & gsht & h2).
          destruct (vector_inv_S hsl) as (hslh & hslt & h3).
          destruct (vector_inv_S hsh) as (hshh & hsht & h4).
          destruct (vector_inv_S avl) as (avlh & avlt & h5).
          destruct (vector_inv_S avh) as (avhh & avht & h6).
          destruct (vector_inv_S bvl) as (bvlh & bvlt & h7).
          destruct (vector_inv_S bvh) as (bvlh0 & bvlt0 & h8). (* name collision, rename *)
          subst gsl gsh hsl hsh avl avh bvl bvh.
          rename bvlh0 into bvhh, bvlt0 into bvht.
          set (x_inv := inv x).
          set (x_inv_sq := x_inv * x_inv) in *.
          set (x_sq := x * x) in *.
          cbn.
          (* Unfold multi_exp and inner_product for the heads *)
          rewrite !multi_exp_append, !inner_product_append.
          (* Now apply the induction hypothesis to the tail vectors *)
          rewrite (ihn gslt gsht hslt hsht avlt avht bvlt bvht u x hx).
          cbn.
          (* The goal reduces to an equality in the field/group algebra for the head elements *)
          (* Expand all the definitions for the head scalars *)
          set (L_hd := gop (gop (gshh ^ avlh) (hslh ^ bvlh0)) (u ^ (avlh * bvlh0))).
          set (R_hd := gop (gop (gslh ^ avhh) (hshh ^ bvlh)) (u ^ (avhh * bvlh))).
          set (P_hd := gop (gop (gslh ^ avlh) (gshh ^ avhh))
                         (gop (gop (hslh ^ bvlh) (hshh ^ bvlh0))
                           (u ^ (add (avlh * bvlh) (avhh * bvlh0))))).
          set (gs'_hd := gop (gslh ^ x_inv) (gshh ^ x)).
          set (hs'_hd := gop (hslh ^ x) (hshh ^ x_inv)).
          set (av'_hd := add (x * avlh) (x_inv * avhh)).
          set (bv'_hd := add (x_inv * bvlh) (x * bvlh0)).
          set (P'_hd := gop (gop (L_hd ^ x_sq) P_hd) (R_hd ^ x_inv_sq)).
          set (expected_hd := gop (gs'_hd ^ av'_hd) 
                              (gop (hs'_hd ^ bv'_hd) (u ^ (av'_hd * bv'_hd)))).
          (* The goal is: P'_hd * (tail part) = (gs'_hd^av'_hd * hs'_hd^bv'_hd * u^(av'_hd*bv'_hd)) * (tail part) *)
          (* Where the tail parts are already equal by IH *)
          rewrite <-!associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          rewrite <-!associative.
          setoid_rewrite commutative at 4.
          rewrite !associative.
          f_equal.
          (* Now we need to prove P'_hd = expected_hd *)
          unfold L_hd, R_hd, P_hd, gs'_hd, hs'_hd, av'_hd, bv'_hd, P'_hd, expected_hd.
          clear.
          (* This is now a purely scalar/group element identity *)
          (* Let L = gsh^avl * hsl^bvh * u^(avl*bvh) *)
          (* Let R = gsl^avh * hsh^bvl * u^(avh*bvl) *)
          (* Let P = gsl^avl * gsh^avh * hsl^bvl * hsh^bvh * u^(avl*bvl + avh*bvh) *)
          (* We need: L^(x*x) * P * R^(x_inv*x_inv) = (gsl^x_inv * gsh^x)^(x*avl + x_inv*avh) *
                                                      (hsl^x * hsh^x_inv)^(x_inv*bvl + x*bvh) * 
                                                      u^((x*avl + x_inv*avh)*(x_inv*bvl + x*bvh)) *)
          (* Rename variables for readability *)
          set (a := avlh). set (b := avhh). set (c := bvlh). set (d := bvlh0).
          set (g1 := gslh). set (g2 := gshh). set (h1 := hslh). set (h2 := hshh).
          set (u' := u). set (x' := x). set (xi := x_inv).
          cbn.
          (* Use vector space lemmas to expand everything *)
          rewrite !smul_distributive_vadd.
          rewrite !smul_distributive_fadd.
          rewrite !smul_associative_fmul.
          rewrite field_one.
          rewrite !gop_simp.
          rewrite <-!associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          rewrite <-!associative.
          setoid_rewrite commutative at 4.
          rewrite <-!associative.
          setoid_rewrite commutative at 5.
          rewrite <-!associative.
          setoid_rewrite commutative at 6.
          rewrite <-!associative.
          setoid_rewrite commutative at 7.
          rewrite !associative.
          setoid_rewrite commutative at 2.
          rewrite <-!associative.
          setoid_rewrite commutative at 3.
          rewrite <-!associative.
          setoid_rewrite commutative at 4.
          rewrite <-!associative.
          setoid_rewrite commutative at 5.
          rewrite !associative.
          (* Now we can match terms: group elements are equal iff their exponents are equal *)
          (* Use the field tactic to compare exponents *)
          apply f_equal2; [apply f_equal2 |].
          - apply f_equal2; [apply f_equal2 | apply f_equal2];
            apply f_equal; apply f_equal; ring.
          - apply f_equal2; [apply f_equal2 | apply f_equal2];
            apply f_equal; apply f_equal; ring.
          - apply f_equal; ring.
        }
      Qed.

      Theorem improved_inner_product_completeness : ∀ (n : nat) 
        (gs hs : Vector.t G (Nat.pow 2 n)) (u P : G) 
        (av bv : Vector.t F (Nat.pow 2 n)) (cs : Vector.t F n),
        (* All challenges must be non-zero for the algebra to work *)
        (∀ (i : Fin.t n), Vector.nth cs i ≠ 0) →
        (* Assume the prover has a valid witness *)
        P = gop (multi_exp gs av) (gop (multi_exp hs bv) 
          (u ^ (inner_product av bv))) →
        improved_inner_product_verify n gs hs u P 
          (improved_inner_product_proof n gs hs u P av bv cs) = true.
      Proof.
        induction n as [|n' ihn].
        + 
          intros gs hs u P av bv cs hcs hP.
          cbn in gs, hs, av, bv, cs.
          pose proof (vector_inv_0 cs) as ha.
          destruct (vector_inv_S av) as (avh & avt & hb).
          destruct (vector_inv_S bv) as (bvh & bvt & hc).
          destruct (vector_inv_S gs) as (gsh & gst & hd).
          destruct (vector_inv_S hs) as (hsh & hst & he).
          pose proof (vector_inv_0 avt) as hf.
          pose proof (vector_inv_0 bvt) as hg.
          pose proof (vector_inv_0 gst) as hi.
          pose proof (vector_inv_0 hst) as hj.
          subst; cbn.
          (* Base case: cs is empty, so hcs is vacuous *)
          eapply dec_true.
          rewrite !right_identity, associative.
          reflexivity.
        + 
          intros gs hs u P av bv cs hcs hP.
          cbn in gs, hs, av, bv, cs.
          destruct (vector_inv_S cs) as (csh & cst & ha).
          destruct (splitat _ av) as (avl & avh) eqn:hb.
          destruct (splitat _ bv) as (bvl & bvh) eqn:hc.
          destruct (splitat _ gs) as (gsl & gsh) eqn:hd.
          destruct (splitat _ hs) as (hsl & hsh) eqn:he.
          eapply append_splitat in hb, hc, hd, he.
          (* hb: av = avl ++ avh, hc: bv = bvl ++ bvh, hd: gs = gsl ++ gsh, he: hs = hsl ++ hsh *)
          (* hcs gives us: hd cs = csh ≠ 0 (since Fin.F1 is a valid index) *)
          assert (hcsh0 : csh ≠ 0).
          {
            pose proof (hcs Fin.F1) as hcs_hd.
            subst; simpl in hcs_hd.
            exact hcs_hd.
          }
          assert (hcst0 : ∀ (i : Fin.t n'), Vector.nth cst i ≠ 0).
          {
            intro i.
            pose proof (hcs (Fin.FS i)) as hcs_tl.
            subst; simpl in hcs_tl.
            exact hcs_tl.
          }
          (* Compute L, R, gs', hs', av', bv', P' as defined by the prover *)
          set (x := csh).
          set (x_inv := inv x).
          set (c_L := inner_product avl bvh).
          set (c_R := inner_product avh bvl).
          set (L := gop (gop (multi_exp gsh avl) (multi_exp hsl bvh)) (u ^ c_L)).
          set (R := gop (gop (multi_exp gsl avh) (multi_exp hsh bvl)) (u ^ c_R)).
          set (gs' := zip_with gop (Vector.map (fun gi => gi ^ x_inv) gsl)
                        (Vector.map (fun gi => gi ^ x) gsh)).
          set (hs' := zip_with gop (Vector.map (fun hi => hi ^ x) hsl)
                        (Vector.map (fun hi => hi ^ x_inv) hsh)).
          set (av' := zip_with add (Vector.map (mul x) avl)
                        (Vector.map (mul x_inv) avh)).
          set (bv' := zip_with add (Vector.map (mul x_inv) bvl)
                        (Vector.map (mul x) bvh)).
          set (P' := gop (gop (L ^ (x * x)) P) (R ^ (x_inv * x_inv))).
          (* We need to show: the verifier accepts the proof *)
          unfold improved_inner_product_verify.
          simpl.
          (* The verifier reads L, R, x from the transcript, splits the generators,
             computes the same gs', hs', P', and recursively calls verify *)
          (* We need to prove P' = multi_exp gs' av' * multi_exp hs' bv' * u^(inner_product av' bv') *)
          (* Use the folding identity lemma *)
          assert (hfolding : P' = gop (multi_exp gs' av') 
                                 (gop (multi_exp hs' bv') (u ^ (inner_product av' bv')))).
          {
            subst P' av' bv' gs' hs' L R c_L c_R x_inv x.
            erewrite multi_exp_append, inner_product_append in hP.
            eapply folding_identity.
            exact hcsh0.
          }
          (* Apply the induction hypothesis *)
          apply ihn with (av := av') (bv := bv') (cs := cst).
          + exact hcst0.
          + exact hfolding.
      Qed.


      
      (*
        Soundness statement for the improved inner-product verifier.

        If a proof transcript [pf] is accepted for public input (gs, hs, u, P),
        then one of the following must hold:

        1) Degenerate-generator case:
           The combined generator family [gs ++ hs ++ [u]] has a non-trivial
           discrete-log relation (i.e., a non-zero exponent vector mapping to
           the group identity). In this case, binding/extractability can fail.

        2) Honest-relation case:
           There exist witness vectors [av], [bv] such that P encodes a valid
           inner-product commitment relation:
             P = ∏ g_i^{av_i} · ∏ h_i^{bv_i} · u^{<av,bv>}.

        Intuition:
        Acceptance implies either a structural weakness in generators or a
        genuine witness for the claimed statement (special-soundness flavor).
      *)
      Theorem improved_inner_product_soundness : ∀ (n : nat) 
        (gs hs : Vector.t G (Nat.pow 2 n)) (u : G) (P : G) 
        (pf : inner_product_proof n),
        improved_inner_product_verify n gs hs u P pf = true ->
        has_non_trivial_dlog_relation (gs ++ hs ++ [u]) ∨
        (∃ (av bv : Vector.t F (Nat.pow 2 n)),
          P = gop (multi_exp gs av) (gop (multi_exp hs bv)  
          (u ^ (inner_product av bv)))).
      Proof.
      Admitted.

      
      

    End Proofs.
  End InnerProduct.
End DL.