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
From Crypto Require Import Sigma 
  AndSigma.

Import MonadNotation 
  VectorNotations.

#[local] Open Scope monad_scope.


Section Okamoto.
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

  Section WI.

    Section Def. 

      (* 
          h = g₁^x₁ ⋅ g₂^x₂ ⋅ g₃^x₃ .... g_n^{x_n}
      *)

      Definition generalised_okamoto_commitment {n : nat} 
        (gs : Vector.t G (2 + n)) (us : Vector.t F (2 + n)) : G := 
        Vector.fold_right (fun '(g, u) acc => gop (g^u) acc) 
        (zip_with pair gs us) gid.

      Definition generalised_okamoto_response {n : nat}
        (xs : Vector.t F (2 + n)) (us : Vector.t F (2 + n)) (c : F) :=
      zip_with (fun x u => u + c * x) xs us.

      Definition generalised_okamoto_real_protocol {n : nat}
        (xs : Vector.t F (2 + n)) (gs : Vector.t G (2 + n)) 
        (h : G) (us : Vector.t F (2 + n)) (c : F) : 
        @sigma_proto F G 1 1 (2 + n) := 
        ([generalised_okamoto_commitment gs us]; [c]; 
        @generalised_okamoto_response n xs us c).

      (* https://cs.pwr.edu.pl/kutylowski/articles/prezentacja_SCC-AsiaCCS.pdf *)
      Definition generalised_okamoto_simulator_protocol {n : nat}
        (gs : Vector.t G (2 + n)) (h : G) (us : Vector.t F (2 + n)) (c : F) : 
        @sigma_proto F G 1 1 (2 + n) := 
        ([gop (generalised_okamoto_commitment gs us) (h ^ (opp c))]; 
        [c]; us).

      
      
      Definition generalised_okamoto_accepting_conversation 
        {n : nat} (gs : Vector.t G (2 + n)) (h : G) 
        (v : @sigma_proto F G 1 1 (2 + n)) : bool.
      Proof.
        refine
          match v with 
          | (a; c; rs) => _ 
          end.
        set (ret := zip_with (fun g r => g^r) gs rs).
        set (retval := Vector.fold_right (fun gr acc => gop gr acc) ret gid).
        refine 
          match Gdec retval (gop (hd a) (h^(hd c))) with 
          | left _ => true 
          | _ => false
          end.
      Defined.

      Definition generalised_okamoto_real_distribution {n : nat}
        (lf : list F) (Hlfn : lf <> List.nil) 
        (xs : Vector.t F (2 + n)) (gs : Vector.t G (2 + n)) (h : G) (c : F) : 
        dist (@sigma_proto F G 1 1 (2 + n))  := 
        us <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) (2 + n);; 
        Ret (@generalised_okamoto_real_protocol n xs gs h us c).

      Definition generalised_okamoto_simulator_distribution {n : nat}
        (lf : list F) (Hlfn : lf <> List.nil) 
        (gs : Vector.t G (2 + n)) (h : G) (c : F) : 
        dist (@sigma_proto F G 1 1 (2 + n)) :=
        us <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) (2 + n);; 
        Ret (generalised_okamoto_simulator_protocol gs h us c).
        
      
    End Def. 
    Section Proofs.
      

      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub 
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (* completeness *)
      Theorem generalised_okamoto_real_accepting_conversation : 
        ∀ (n : nat) (xs : Vector.t F (2 + n)) (gs : Vector.t G (2 + n)) 
        (h : G) (us : Vector.t F (2 + n)) (c : F), 
        h = Vector.fold_right 
          (fun '(g, x) acc => gop (g^x) acc) (zip_with pair gs xs) gid ->
        @generalised_okamoto_accepting_conversation n 
          gs h (@generalised_okamoto_real_protocol n
          xs gs h us c) = true.
      Proof.
        unfold generalised_okamoto_real_protocol.
        intros * R. cbn.
        unfold generalised_okamoto_commitment,
        generalised_okamoto_response. cbn.
        eapply dec_true.
        revert n xs gs us h R.
        induction n as [|n ihn].
        +
          intros *. 
          destruct (vector_inv_S xs) as (xh & xst & ha).
          destruct (vector_inv_S xst) as (xsth & xstt & hb).
          pose proof (vector_inv_0 xstt) as hc.
          destruct (vector_inv_S gs) as (gh & gst & hd).
          destruct (vector_inv_S gst) as (gsth & gstt & he).
          pose proof (vector_inv_0 gstt) as hf.
          destruct (vector_inv_S us) as (uh & ust & hg).
          destruct (vector_inv_S ust) as (usth & ustt & hh).
          pose proof (vector_inv_0 ustt) as hi.
          subst. cbn. intro R.
          rewrite R.
          admit.
        +
          (* inductive case *)
          intros * R.
          destruct (vector_inv_S xs) as (xh & xst & ha).
          destruct (vector_inv_S gs) as (gh & gst & hb).
          destruct (vector_inv_S us) as (uh & ust & hc).
          subst xs gs us. cbn. cbn in R.
          specialize (ihn xst gst ust (gop h (gh ^ (opp xh)))).
          remember (fold_right (λ '(g, x) (acc : G), gop (g ^ x) acc) 
          (zip_with pair gst xst) gid) as ret.
          setoid_rewrite <-Heqret in ihn. 
          assert (ha : gop h (gh ^ opp xh) = ret).
          {
            rewrite R, commutative, associative,
            <-smul_distributive_fadd. 
            assert (ha : opp xh + xh = zero) by field.
            rewrite ha, field_zero, left_identity.
            reflexivity.
          }
          specialize (ihn ha).
          rewrite ihn.
          clear ihn.
          remember (fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc) (zip_with pair gst ust) gid) as retw.
          rewrite R.
          (* automation like field 
            should discharge this goal. *)
      Admitted.

      Theorem generalised_okamoto_simulator_accepting_conversation :
        ∀ (n : nat) (gs : Vector.t G (2 + n)) 
        (h : G) (us : Vector.t F (2 + n)) (c : F), 
        @generalised_okamoto_accepting_conversation n 
          gs h (@generalised_okamoto_simulator_protocol n
          gs h us c) = true.
      Proof.
        intros *. cbn.
        unfold generalised_okamoto_commitment.
        eapply dec_true.
        revert n gs h us c.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S us) as (uh & ust & hd).
          destruct (vector_inv_S ust) as (usth & ustt & he).
          pose proof (vector_inv_0 ustt) as hf.
          subst. cbn.
          rewrite right_identity.
          rewrite <-associative,
          <-smul_distributive_fadd.
          assert (ha : opp c + c = zero) by field.
          rewrite ha, field_zero, right_identity.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S us) as (uh & ust & hb).
          specialize (ihn gst h ust c).
          subst gs us. cbn.
          rewrite ihn.
          remember (fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc) (zip_with pair gst ust) gid) as ret.
          setoid_rewrite <-Heqret.
          rewrite associative. f_equal.
          rewrite associative.
          reflexivity.
      Qed.
      

      (* special soundness *)
      Theorem generalised_okamoto_real_special_soundenss : 
        ∀ (n : nat) (gs : Vector.t G (2 + n)) (h : G)
        (a : G) (c₁ c₂ : F) (r₁ r₂ : Vector.t F (2 + n)),
        c₁ <> c₂ -> 
        @generalised_okamoto_accepting_conversation n gs h 
          ([a]; [c₁]; r₁) = true ->
        @generalised_okamoto_accepting_conversation n gs h 
          ([a]; [c₂]; r₂) = true ->
        ∃ (xi : Vector.t F (2 + n)), h = 
        Vector.fold_right (fun '(g, x) acc => gop (g^x) acc) 
        (zip_with pair gs xi) gid.
      Proof.
      Admitted.


      (* special honest-verifier zero-knowledge proof *)


      (* witness indistinguishability *)
    
      
    
    End Proofs.
  End WI.
End Okamoto. 
 