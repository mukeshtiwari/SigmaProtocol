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
        (xs : Vector.t F (2 + n)) (us : Vector.t F (2 + n)) (c : F) : 
        Vector.t F (2 + n) :=
        zip_with (fun x u => u + c * x) xs us.

      Definition generalised_okamoto_real_protocol {n : nat}
        (xs : Vector.t F (2 + n)) (gs : Vector.t G (2 + n)) 
        (h : G) (us : Vector.t F (2 + n)) (c : F) : 
        @sigma_proto F G 1 1 (2 + n) := 
        ([generalised_okamoto_commitment gs us]; [c]; 
        @generalised_okamoto_response n xs us c).

      (* https://cs.pwr.edu.pl/kutylowski/articles/prezentacja_SCC-AsiaCCS.pdf *)
      Definition generalised_okamoto_simulator_protocol_commitment {n : nat}
        (gs : Vector.t G (2 + n)) (h : G) (us : Vector.t F (2 + n)) 
        (c : F) : G := 
        gop (generalised_okamoto_commitment gs us) (h ^ (opp c)).


      Definition generalised_okamoto_simulator_protocol {n : nat}
        (gs : Vector.t G (2 + n)) (h : G) (us : Vector.t F (2 + n)) (c : F) : 
        @sigma_proto F G 1 1 (2 + n) := 
        ([generalised_okamoto_simulator_protocol_commitment gs h us c]; 
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
      
      (* WI *)
      Definition transform_us {n : nat} (xs₁ xs₂ : Vector.t F (2 + n)) 
        (c : F) (us : Vector.t F (2 + n)) : Vector.t F (2 + n) :=
        zip_with (fun u '(x₁, x₂) => u + c * (x₁ - x₂)) us 
        (zip_with pair xs₁ xs₂).
      

      Definition inverse_transform {n : nat} (xs₁ xs₂ : Vector.t F (2 + n)) 
        (c : F) (us : Vector.t F (2 + n)) : Vector.t F (2 + n) :=
        zip_with (fun u '(x₁, x₂) => u + c * (x₂ - x₁)) us 
        (zip_with pair xs₁ xs₂).

    End Def. 

    (* This is specialised Okamoto h = g₁ ^ x₁ ⋅ g₂ ^ x₂. I needed 
    this specialised instance for NEQ *)
    Section Ins.

      Definition okamoto_commitment
        (gs : Vector.t G 2) (us : Vector.t F 2) : G := 
        generalised_okamoto_commitment gs us. 
        
      
      Definition okamoto_response         
        (xs : Vector.t F 2) (us : Vector.t F 2) (c : F) : 
        Vector.t F 2 := 
        generalised_okamoto_response xs us c. 

      Definition okamoto_real_protocol 
        (xs : Vector.t F 2) (gs : Vector.t G 2) 
        (h : G) (us : Vector.t F 2) (c : F) : @sigma_proto F G 1 1 2 :=
        @generalised_okamoto_real_protocol 0 xs gs h us c.

      Definition okamoto_simulator_protocol_commitment 
        (gs : Vector.t G 2) (h : G) (us : Vector.t F 2) 
        (c : F) : G := generalised_okamoto_simulator_protocol_commitment 
          gs h us c.

      Definition okamoto_simulator_protocol 
        (gs : Vector.t G 2) (h : G) (us : Vector.t F 2) (c : F) : 
        @sigma_proto F G 1 1 2 := 
        @generalised_okamoto_simulator_protocol _ gs h us c. 

      
      Definition okamoto_accepting_conversation 
        (gs : Vector.t G 2) (h : G) (v : @sigma_proto F G 1 1 2) : bool :=
        @generalised_okamoto_accepting_conversation _ gs h v. 
        

    End Ins.

    Section Proofs.
      

      Theorem generalised_okamoto_accepting_conversation_true : 
        ∀ (n : nat)  (gs : Vector.t G (2 + n)) (h : G) 
        (v : @sigma_proto F G 1 1 (2 + n)),
        @generalised_okamoto_accepting_conversation n gs h v = true <->
        match v with 
        | (a; c; rs) => 
          Vector.fold_right (fun gr acc => gop gr acc) 
          (zip_with (fun g r => g^r) gs rs) gid = gop (hd a) (h ^ (hd c))
        end.
      Proof.
        intros *; split.
        intro ha.
        refine 
          (match v as v' in sigma_proto return v = v' -> _ 
          with 
          | (a; c; rs) => fun hb => _  
          end eq_refl).
        subst. unfold generalised_okamoto_accepting_conversation in ha.
        rewrite dec_true in ha. exact ha.
        intros ha.
        refine 
          (match v as v' in sigma_proto return v = v' -> _ 
          with 
          | (a; c; rs) => fun hb => _  
          end eq_refl); subst.
        unfold generalised_okamoto_accepting_conversation.
        rewrite dec_true.
        exact ha.
      Qed.



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
          rewrite R, !right_identity.
          rewrite <-associative,
           !smul_distributive_fadd, 
           <-associative. f_equal.
          rewrite smul_distributive_vadd,
          <-!smul_associative_fmul, 
          associative, associative.
          f_equal. 
          rewrite commutative.
          f_equal.
          assert (ha : c * xh = xh * c) by field.
          rewrite ha. reflexivity.
          assert (ha : c * xsth = xsth * c) by field.
          rewrite ha. reflexivity.
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
          rewrite !smul_distributive_vadd,
          <-!smul_associative_fmul,
          smul_distributive_fadd.
          rewrite <-!associative.
          f_equal.
          assert (hb : gop retw (gop (gh ^ (xh * c)) (ret ^ c)) = 
            gop (gh ^ (xh * c)) (gop retw (ret ^ c))).
          {
            rewrite associative.
            assert (hb : (gop retw (gh ^ (xh * c))) = 
              (gop (gh ^ (xh * c)) retw)).
            rewrite commutative. reflexivity.
            rewrite hb; clear hb.
            rewrite associative.
            reflexivity.
          }
          rewrite hb; clear hb. f_equal.
          assert (hb : c * xh = xh * c) by field.
          rewrite hb; clear hb; reflexivity.
          f_equal.
          rewrite commutative, <-associative.
          pose proof vector_space_smul_distributive_fadd as hb.
          unfold is_smul_distributive_fadd in hb.
          specialize (hb (opp xh * c) (xh * c) gh).
          rewrite <-hb. clear hb.
          assert (hb : (opp xh * c + xh * c) = zero).
          field. rewrite hb; clear hb.
          rewrite vector_space_field_zero, right_identity.
          reflexivity.
      Qed.
         
          (* automation like field 
            should discharge this goal. *)

      Theorem generalised_okamoto_simulator_accepting_conversation :
        ∀ (n : nat) (gs : Vector.t G (2 + n)) 
        (h : G) (us : Vector.t F (2 + n)) (c : F), 
        @generalised_okamoto_accepting_conversation n 
          gs h (@generalised_okamoto_simulator_protocol n
          gs h us c) = true.
      Proof.
        intros *. cbn.
        unfold generalised_okamoto_commitment,
        generalised_okamoto_simulator_protocol_commitment.
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
      
      Theorem ginv_fold_right_connection : 
        ∀ (n : nat) (gs : Vector.t G (2 + n))
        (rs : Vector.t F (2 + n)),
        ginv (fold_right (λ gr acc : G, gop gr acc)
        (zip_with (λ (g : G) (r : F), g ^ r) gs rs) gid) = 
        (fold_right (λ gr acc : G, gop gr acc)
        (zip_with (λ (g : G) (r : F), g ^ r) gs 
        (Vector.map opp rs)) gid).
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S rs) as (rh & rst & hd).
          destruct (vector_inv_S rst) as (rsth & rstt & he).
          pose proof (vector_inv_0 rstt) as hf.
          subst. cbn.
          rewrite !right_identity, group_inv_flip,
          !connection_between_vopp_and_fopp, 
          commutative; reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S rs) as (rh & rst & hb).
          subst. cbn.
          specialize (ihn gst rst).
          setoid_rewrite <-ihn.
          rewrite group_inv_flip, commutative,
          connection_between_vopp_and_fopp.
          reflexivity.
      Qed.

      Theorem zip_map_connection : 
        ∀ (n : nat) (rs₁ rs₂ : Vector.t F (2 + n)),
        (zip_with (λ x y : F, x + y) rs₁ (map opp rs₂)) = 
        (zip_with (λ x y : F, x + opp y) rs₁ rs₂).
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S rs₁) as (rh₁ & rst₁ & ha).
          destruct (vector_inv_S rst₁) as (rsth₁ & rstt₁ & hb).
          pose proof (vector_inv_0 rstt₁) as hc.
          destruct (vector_inv_S rs₂) as (rh₂ & rst₂ & hd).
          destruct (vector_inv_S rst₂) as (rsth₂ & rstt₂ & he).
          pose proof (vector_inv_0 rstt₂) as hf.
          subst. cbn.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S rs₁) as (rh₁ & rst₁ & ha).
          destruct (vector_inv_S rs₂) as (rh₂ & rst₂ & hb).
          subst. cbn.
          now rewrite ihn.
      Qed.

          



      Theorem gop_simp : ∀ (a b c d : G),
        gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
      Proof.
        intros *.
        rewrite <-!associative.
        setoid_rewrite commutative at 2.
        rewrite <-!associative.
        setoid_rewrite commutative at 3.
        reflexivity.
      Qed.

      Theorem gop_fold_right_connection : 
        ∀ (n : nat) (gs : Vector.t G (2 + n))
        (rs₁ rs₂ : Vector.t F (2 + n)),
        gop
        (fold_right (λ gr acc : G, gop gr acc)
        (zip_with (λ (g : G) (r : F), g ^ r) gs rs₁) gid)
        (fold_right (λ gr acc : G, gop gr acc)
        (zip_with (λ (g : G) (r : F), g ^ r) gs rs₂) gid) = 
        fold_right (λ gr acc : G, gop gr acc)
        (zip_with (λ (g : G) (r : F), g ^ r) gs
          (zip_with (fun x y => x + y) rs₁ rs₂)) gid.
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S rs₁) as (rh₁ & rst₁ & hd).
          destruct (vector_inv_S rst₁) as (rsth₁ & rstt₁ & he).
          pose proof (vector_inv_0 rstt₁) as hf.
          destruct (vector_inv_S rs₂) as (rh₂ & rst₂ & hg).
          destruct (vector_inv_S rst₂) as (rsth₂ & rstt₂ & hh).
          pose proof (vector_inv_0 rstt₂) as hi.
          subst. cbn.
          rewrite !right_identity.
          rewrite gop_simp.
          pose proof vector_space_smul_distributive_fadd as ha.
          unfold is_smul_distributive_fadd in ha.
          rewrite <-!ha.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S rs₁) as (rh₁ & rst₁ & hb).
          destruct (vector_inv_S rs₂) as (rh₂ & rst₂ & hc).
          subst. cbn.
          specialize (ihn gst rst₁ rst₂).
          setoid_rewrite <-ihn.
          remember (fold_right (λ gr acc : G, gop gr acc)
          (zip_with (λ (g : G) (r : F), g ^ r) gst rst₁) gid) as ret₁.
          setoid_rewrite <-Heqret₁.
          remember (fold_right (λ gr acc : G, gop gr acc)
          (zip_with (λ (g : G) (r : F), g ^ r) gst rst₂) gid) as ret₂.
          setoid_rewrite <-Heqret₂.
          rewrite gop_simp.
          pose proof vector_space_smul_distributive_fadd as ha.
          unfold is_smul_distributive_fadd in ha.
          rewrite <-!ha.
          reflexivity.
      Qed.

      Theorem fold_right_zip_connection : 
        ∀ (n : nat) (gs : Vector.t G (2 + n))
        (rs : Vector.t F (2 + n)),
        fold_right (λ gr acc : G, gop gr acc)
        (zip_with (λ (g : G) (r : F), g ^ r) gs rs) gid = 
        fold_right (λ '(g, x) (acc : G), gop (g ^ x) acc)
        (zip_with pair gs rs) gid.
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S rs) as (rh & rst & hd).
          destruct (vector_inv_S rst) as (rsth & rstt & he).
          pose proof (vector_inv_0 rstt) as hf.
          subst. cbn.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S rs) as (rh & rst & hd).
          subst. cbn.
          rewrite ihn.
          reflexivity.
      Qed.



      (* special soundness *)
      Theorem generalised_okamoto_real_special_soundenss : 
        ∀ (n : nat) (gs : Vector.t G (2 + n)) (h : G)
        (a : G) (c₁ c₂ : F) (rs₁ rs₂ : Vector.t F (2 + n)),
        c₁ <> c₂ -> 
        @generalised_okamoto_accepting_conversation n gs h 
          ([a]; [c₁]; rs₁) = true ->
        @generalised_okamoto_accepting_conversation n gs h 
          ([a]; [c₂]; rs₂) = true ->
        ∃ (xi : Vector.t F (2 + n)), h = 
        Vector.fold_right (fun '(g, x) acc => gop (g^x) acc) 
        (zip_with pair gs xi) gid.
      Proof.
        intros * ha hb hc. cbn in hb, hc; 
        rewrite dec_true in hb, hc.
        eapply f_equal with (f := fun x => 
            gop x (ginv (gop a (h ^ c₂))))
        in hb.
        rewrite <-hc in hb at 1.
        clear hc.
        assert (hc : gop (gop a (h ^ c₁)) (ginv (gop a (h ^ c₂))) = 
          h ^ (c₁ + opp c₂)).
        {
          
          rewrite group_inv_flip, associative, commutative, 
          <-associative, associative.
          rewrite left_inverse, left_identity,
          connection_between_vopp_and_fopp.
          pose proof vector_space_smul_distributive_fadd as hc.
          unfold is_smul_distributive_fadd in hc.
          rewrite <-hc.
          reflexivity.
        }
        rewrite hc in hb; clear hc.
        setoid_rewrite ginv_fold_right_connection in hb.
        setoid_rewrite gop_fold_right_connection in hb.
        rewrite zip_map_connection in hb.
        rewrite fold_right_zip_connection in hb.
        eapply f_equal with (f := fun x => 
          x ^ (inv (c₁ + opp c₂))) in hb.
        rewrite <-smul_associative_fmul in hb.
        assert (hc : c₁ + opp c₂ <> zero). 
        intro hc. eapply ha.
        eapply f_equal with (f := fun x => 
          x + c₂) in hc.
        rewrite left_identity in hc.
        rewrite <-hc. field. 
        assert (hd : ((c₁ + opp c₂) * inv (c₁ + opp c₂)) = one).
        field. exact hc.
        rewrite hd in hb; clear hc hd.
        setoid_rewrite field_one in hb.
        exists (zip_with (λ x y : F, inv (c₁ + opp c₂) * (x + opp y)) 
        rs₁ rs₂).
        rewrite <-hb.
        clear ha hb h a.
        revert n gs rs₁ rs₂.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S rs₁) as (rh₁ & rst₁ & hd).
          destruct (vector_inv_S rst₁) as (rsth₁ & rstt₁ & he).
          pose proof (vector_inv_0 rstt₁) as hf.
          destruct (vector_inv_S rs₂) as (rh₂ & rst₂ & hg).
          destruct (vector_inv_S rst₂) as (rsth₂ & rstt₂ & hh).
          pose proof (vector_inv_0 rstt₂) as hi.
          subst. cbn.
          rewrite !right_identity, 
          !smul_distributive_vadd,
          <-!smul_associative_fmul.
          assert (ha : (rh₁ + opp rh₂) * inv (c₁ + opp c₂) = 
          (inv (c₁ + opp c₂) * (rh₁ + opp rh₂))). 
          rewrite commutative. reflexivity.
          rewrite ha; clear ha.
          assert (ha : (rsth₁ + opp rsth₂) * inv (c₁ + opp c₂) = 
          (inv (c₁ + opp c₂) * (rsth₁ + opp rsth₂))).
          rewrite commutative. reflexivity.
          rewrite ha. reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S rs₁) as (rh₁ & rst₁ & hb).
          destruct (vector_inv_S rs₂) as (rh₂ & rst₂ & hc).
          subst. cbn.
          rewrite <-ihn.
          remember (fold_right (λ '(g, x) (acc : G), gop (g ^ x) acc)
          (zip_with pair gst (zip_with (λ x y : F, x + opp y) 
          rst₁ rst₂)) gid) as ret.
          setoid_rewrite <-Heqret. 
          rewrite !smul_distributive_vadd,
          <-!smul_associative_fmul.
          assert (ha : ((rh₁ + opp rh₂) * inv (c₁ + opp c₂)) = 
          (inv (c₁ + opp c₂) * (rh₁ + opp rh₂))). 
          rewrite commutative. reflexivity.
          rewrite ha. reflexivity.
      Qed.


      (* special honest-verifier zero-knowledge proof *)
      (* honest verifier zero knowledge proof *)

      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      Lemma generalised_okamoto_real_distribution_transcript_accepting_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n))) (xs : Vector.t F (2 + n))
        (gs : Vector.t G (2 + n)) (h : G)
        (trans : sigma_proto) (pr : prob) (c : F),
        (* relationship between gs, h, and xs *)
        h = fold_right (λ '(g, x) (acc : G), gop (g ^ x) acc) 
        (zip_with pair gs xs) gid ->
        List.In (trans, pr) (Bind l (λ us : t F (2 + n), 
            Ret (generalised_okamoto_real_protocol xs gs h us c))) → 
        generalised_okamoto_accepting_conversation gs h trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Hrel Ha.
          cbn in Ha; 
          inversion Ha.
        +
          (* destruct l *)
          destruct l as [|(la, lp) l].
          ++
            intros * Hrel Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply generalised_okamoto_real_accepting_conversation.
            exact Hrel.
          ++
            intros * Hrel Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply generalised_okamoto_real_accepting_conversation.
              exact Hrel.
            +++
              eapply IHl; try assumption.
              exact Hrel. exact Ha.
      Qed.

      Lemma generalised_okamoto_real_distribution_transcript_probability_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n))) (xs : Vector.t F (2 + n))
        (gs : Vector.t G (2 + n)) (h : G)
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n)) (prx : prob), 
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ us : t F (2 + n), 
          Ret (generalised_okamoto_real_protocol xs gs h us c))) → 
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


      Lemma generalised_okamoto_real_distribution_transcript_generic {n : nat} : 
        forall (lf : list F) (Hlf : lf <> List.nil) 
        (xs : Vector.t F (2 + n)) (gs : Vector.t G (2 + n)) (h : G)
        (a : sigma_proto) (b : prob) (c : F),
        (* relationship between gs, h, and xs *)
        h = fold_right (λ '(g, x) (acc : G), gop (g ^ x) acc) 
        (zip_with pair gs xs) gid ->
        List.In (a, b) (generalised_okamoto_real_distribution lf Hlf xs gs h c) ->
        generalised_okamoto_accepting_conversation gs h a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n))).
      Proof.
        intros * Hrel Ha.
        refine(conj _ _).
        +
          eapply generalised_okamoto_real_distribution_transcript_accepting_generic.
          exact Hrel. exact Ha.
        +
          eapply generalised_okamoto_real_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.


       Lemma generalised_okamoto_simulator_distribution_transcript_accepting_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n))) 
        (gs : Vector.t G (2 + n)) (h : G) (trans : sigma_proto) (pr : prob) (c : F),
        List.In (trans, pr) (Bind l (λ us : t F (2 + n), 
            Ret (generalised_okamoto_simulator_protocol gs h us c))) → 
        generalised_okamoto_accepting_conversation gs h trans = true.
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
            eapply generalised_okamoto_simulator_accepting_conversation.
          ++
            intros * Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply generalised_okamoto_simulator_accepting_conversation.
            +++
              eapply IHl; try assumption.
              exact Ha.
      Qed.


      Lemma generalised_okamoto_simulator_distribution_transcript_probability_generic {n : nat} : 
        forall (l : dist (Vector.t F (2 + n))) 
        (gs : Vector.t G (2 + n)) (h : G)
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n)) (prx : prob), 
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ us : t F (2 + n), 
          Ret (generalised_okamoto_simulator_protocol gs h us c))) → 
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


       Lemma generalised_okamoto_simulator_distribution_transcript_generic {n : nat} : 
        forall (lf : list F) (Hlf : lf <> List.nil) 
        (gs : Vector.t G (2 + n)) (h : G)
        (a : sigma_proto) (b : prob) (c : F),
        List.In (a, b) (generalised_okamoto_simulator_distribution lf Hlf gs h c) ->
        generalised_okamoto_accepting_conversation gs h a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n))).
      Proof.
        intros * Ha.
        refine(conj _ _).
        +
          eapply generalised_okamoto_simulator_distribution_transcript_accepting_generic.
          exact Ha.
        +
          eapply generalised_okamoto_simulator_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.


      (* Two distributions are identical (information theoretic security)*)
      Lemma generalised_okamoto_special_honest_verifier_zkp {n : nat} : 
        forall (lf : list F) (Hlfn : lf <> List.nil) 
        (xs : Vector.t F (2 + n)) (gs : Vector.t G (2 + n)) (h : G) (c : F),
        (* relationship between gs, h, and xs *)
        h = fold_right (λ '(g, x) (acc : G), gop (g ^ x) acc) 
          (zip_with pair gs xs) gid ->
        List.map (fun '(a, p) => 
          (generalised_okamoto_accepting_conversation gs h a, p))
          (@generalised_okamoto_real_distribution n lf Hlfn xs gs h c) = 
        List.map (fun '(a, p) => 
          (generalised_okamoto_accepting_conversation gs h a, p))
          (@generalised_okamoto_simulator_distribution n lf Hlfn gs h c).
      Proof.
        intros * Hrel.
        eapply map_ext_eq.
        + 
          unfold generalised_okamoto_real_distribution,
          generalised_okamoto_simulator_distribution; cbn.
          repeat rewrite distribution_length.
          reflexivity.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_okamoto_real_distribution_transcript_generic.
          exact Hrel. exact Ha.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_okamoto_simulator_distribution_transcript_generic.
          exact Ha.
      Qed.


      (* witness indistinguishability *)

    
      
      Lemma transform_inverse_foward {n : nat} :
        ∀ (xs₁ xs₂ : Vector.t F (2 + n)) (c : F) (us : Vector.t F (2 + n)),
        inverse_transform xs₁ xs₂ c (transform_us xs₁ xs₂ c us) = us.
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xst₁) as (xsth₁ & xstt₁ & hb).
          pose proof (vector_inv_0 xstt₁) as hc.
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hd).
          destruct (vector_inv_S xst₂) as (xsth₂ & xstt₂ & he).
          pose proof (vector_inv_0 xstt₂) as hf.
          destruct (vector_inv_S us) as (uh & ust & hg).
          destruct (vector_inv_S ust) as (usth & ustt & hh).
          pose proof (vector_inv_0 ustt) as hi.
          subst. cbn.
          assert (ha : c * (xh₁ - xh₂) + c * (xh₂ - xh₁) = zero).
          field.
          assert (hb : c * (xsth₁ - xsth₂) + c * (xsth₂ - xsth₁) = zero).
          field.
          f_equal. rewrite <-associative. rewrite ha.
          field. f_equal. rewrite <-associative. rewrite hb.
          field.
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hb).
          destruct (vector_inv_S us) as (uh & ust & hc).
          subst. cbn.
          specialize (ihn xst₁ xst₂ c ust).
          f_equal.
          rewrite <-associative. field.
          eapply ihn.
      Qed.

      Lemma transform_inverse_backward {n : nat} :
        ∀ (xs₁ xs₂ : Vector.t F (2 + n)) (c : F) (us : Vector.t F (2 + n)),
        transform_us xs₁ xs₂ c (inverse_transform xs₁ xs₂ c us) = us.
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xst₁) as (xsth₁ & xstt₁ & hb).
          pose proof (vector_inv_0 xstt₁) as hc.
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hd).
          destruct (vector_inv_S xst₂) as (xsth₂ & xstt₂ & he).
          pose proof (vector_inv_0 xstt₂) as hf.
          destruct (vector_inv_S us) as (uh & ust & hg).
          destruct (vector_inv_S ust) as (usth & ustt & hh).
          pose proof (vector_inv_0 ustt) as hi.
          subst. cbn.
          f_equal. rewrite <-associative. field.
          f_equal. rewrite <-associative. field.
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hb).
          destruct (vector_inv_S us) as (uh & ust & hc).
          subst. cbn.
          specialize (ihn xst₁ xst₂ c ust).
          f_equal.
          rewrite <-associative. field.
          eapply ihn.
      Qed.

      Lemma generalised_okamoto_commitment_homomorphic {n : nat} :
        ∀ (gs : Vector.t G (2+n)) (us vs : Vector.t F (2+n)),
          generalised_okamoto_commitment gs 
          (zip_with (λ x₁ x₂ : F, x₁ - x₂) us vs) =
          gop (generalised_okamoto_commitment gs us) 
              (generalised_okamoto_commitment gs (map opp vs)).
      Proof.
        (* By induction on vectors, using:
          - g^(u+v) = g^u * g^v  (distributivity of scalar multiplication)
          - Group is abelian (from vector_space structure) *)
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S us) as (uh & ust & hd).
          destruct (vector_inv_S ust) as (usth & ustt & he).
          pose proof (vector_inv_0 ustt) as hf.
          destruct (vector_inv_S vs) as (vh & vst & hg).
          destruct (vector_inv_S vst) as (vsth & vstt & hh).
          pose proof (vector_inv_0 vstt) as hi.
          subst; cbn.
          rewrite !right_identity.
          rewrite gop_simp, 
          <-!smul_distributive_fadd.
          assert (ha : uh + opp vh = uh - vh). field.
          rewrite ha; clear ha.
          assert (ha : (usth + opp vsth) = (usth - vsth)). field.
          rewrite ha; clear ha.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S us) as (uh & ust & hb).
          destruct (vector_inv_S vs) as (vh & vst & hc).
          subst; cbn.
          specialize (ihn gst ust vst).
          cbn in ihn.
          unfold generalised_okamoto_commitment in ihn.
          setoid_rewrite ihn.
          rewrite gop_simp,
          <-!smul_distributive_fadd.
          assert (ha : uh + opp vh = uh - vh). field.
          rewrite ha; clear ha.
          reflexivity.
      Qed.

      Lemma generalised_okamoto_commitment_inv {n : nat} :
        ∀ (gs : Vector.t G (2+n)) (us : Vector.t F (2+n)),
          generalised_okamoto_commitment gs (Vector.map opp us) =
          ginv (generalised_okamoto_commitment gs us).
      Proof.
        (* Using: g^(-u) = (g^u)^{-1} *)
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S gst) as (gsth & gstt & hb).
          pose proof (vector_inv_0 gstt) as hc.
          destruct (vector_inv_S us) as (uh & ust & hd).
          destruct (vector_inv_S ust) as (usth & ustt & he).
          pose proof (vector_inv_0 ustt) as hf.
          subst; cbn.
          rewrite !right_identity.
          setoid_rewrite <-connection_between_vopp_and_fopp.
          rewrite <-group_inv_flip, commutative.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S gs) as (gh & gst & ha).
          destruct (vector_inv_S us) as (uh & ust & hb).
          subst; cbn.
          specialize (ihn gst ust). 
          setoid_rewrite ihn.
          unfold generalised_okamoto_commitment.
          setoid_rewrite <-connection_between_vopp_and_fopp.
          rewrite <-group_inv_flip, commutative.
          reflexivity.
      Qed.

      Theorem generalised_okamoto_commitment_connection {n : nat} : 
        ∀ (gs : Vector.t G (2 + n)) (h : G) (xs₁ xs₂ : Vector.t F (2 + n)),
        h = generalised_okamoto_commitment gs xs₁ ->
        h = generalised_okamoto_commitment gs xs₂ ->
        generalised_okamoto_commitment gs 
          (zip_with (fun x₁ x₂ => x₁ - x₂) xs₁ xs₂) = gid.
      Proof.
        intros * ha hb.
        setoid_rewrite generalised_okamoto_commitment_homomorphic.
        setoid_rewrite generalised_okamoto_commitment_inv.
        rewrite <-ha, <-hb.
        rewrite right_inverse; reflexivity.
      Qed.



      Theorem generalised_okamoto_commitment_tranform_connection {n : nat} :
        ∀ (gs : Vector.t G (2 + n)) (xs₁ xs₂ : Vector.t F (2 + n))
          (us : Vector.t F (2 + n)) (c : F),
        fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc)
          (zip_with pair gs
          (zip_with (λ (u : F) '(x₁, x₂), u + c * (x₁ - x₂)) us
          (zip_with pair xs₁ xs₂))) gid = 
        gop 
          (fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc)
          (zip_with pair gs us) gid)
          ((fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc)
          (zip_with pair gs (zip_with (fun x₁ x₂ => (x₁ - x₂)) 
            xs₁ xs₂)) gid) ^ c).
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xst₁) as (xsth₁ & xstt₁ & hb).
          pose proof (vector_inv_0 xstt₁) as hc.
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hd).
          destruct (vector_inv_S xst₂) as (xsth₂ & xstt₂ & he).
          pose proof (vector_inv_0 xstt₂) as hf.
          destruct (vector_inv_S us) as (uh & ust & hg).
          destruct (vector_inv_S ust) as (usth & ustt & hh).
          pose proof (vector_inv_0 ustt) as hi.
          destruct (vector_inv_S gs) as (gh & gst & hj).
          destruct (vector_inv_S gst) as (gsth & gstt & hk).
          pose proof (vector_inv_0 gstt) as hl.
          subst; cbn.
          rewrite !right_identity, !smul_distributive_vadd,
          <-!smul_associative_fmul.
          rewrite gop_simp, 
          <-!smul_distributive_fadd.
          assert (ha : c * (xh₁ - xh₂) = (xh₁ - xh₂) * c). field.
          rewrite ha; clear ha.
          assert (ha : c * (xsth₁ - xsth₂) = (xsth₁ - xsth₂) * c). field.
          rewrite ha; clear ha.
          reflexivity.
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hb).
          destruct (vector_inv_S us) as (uh & ust & hc).
          destruct (vector_inv_S gs) as (gh & gst & hd).
          subst; cbn.
          rewrite ihn; clear ihn.
          remember (fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc)
          (zip_with pair gst ust) gid) as reta.
          remember (fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc)
          (zip_with pair gst (zip_with (λ x₁ x₂ : F, x₁ - x₂) xst₁ xst₂))
          gid) as retb.
          setoid_rewrite <-Heqreta. setoid_rewrite <-Heqretb.
          rewrite  !smul_distributive_vadd,
          <-!smul_associative_fmul.
          rewrite gop_simp, 
          <-!smul_distributive_fadd.
          assert (ha : c * (xh₁ - xh₂) = (xh₁ - xh₂) * c). field.
          rewrite ha; clear ha.
          reflexivity.
      Qed.


      Theorem zip_with_transform {n : nat} : 
        ∀ (xs₁ xs₂ : Vector.t F (2 + n)) 
        (us : Vector.t F (2 + n)) (c : F),
        zip_with (λ x u : F, u + c * x) xs₁ us =
        zip_with (λ x u : F, u + c * x) xs₂
        (zip_with (λ (u : F) '(x₁, x₂), u + c * (x₁ - x₂)) us 
        (zip_with pair xs₁ xs₂)).
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xst₁) as (xsth₁ & xstt₁ & hb).
          pose proof (vector_inv_0 xstt₁) as hc.
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hd).
          destruct (vector_inv_S xst₂) as (xsth₂ & xstt₂ & he).
          pose proof (vector_inv_0 xstt₂) as hf.
          destruct (vector_inv_S us) as (uh & ust & hg).
          destruct (vector_inv_S ust) as (usth & ustt & hh).
          pose proof (vector_inv_0 ustt) as hi.
          subst; cbn.
          f_equal. field.
          f_equal. field.
        +
          intros *.
          destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
          destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hb).
          destruct (vector_inv_S us) as (uh & ust & hc).
          subst; cbn.
          f_equal. field.
          eapply ihn.
      Qed.


      Theorem generalised_okamoto_witness_indistinguishable {n : nat} :
        ∀ (gs : Vector.t G (2 + n)) (h : G) (xs₁ xs₂ : Vector.t F (2 + n)),
        (* Both witnesses produce the same public key h *)
        h = generalised_okamoto_commitment gs xs₁ ->
        h = generalised_okamoto_commitment gs xs₂ ->
        (* For every conversation (a, c, rs) from xs, there exists unique us' 
          such that the same conversation is produced by xs' *)
        ∀ (us : Vector.t F (2 + n)) (a : G) (c : F) (rs : Vector.t F (2 + n)),
        ([a]; [c]; rs) = generalised_okamoto_real_protocol xs₁ gs h us c ->
        (* Then there exists unique us' producing the same transcript for xs' *)
        exists! us' : Vector.t F (2 + n),
          ([a]; [c]; rs) = generalised_okamoto_real_protocol xs₂ gs h us' c.
      Proof.
        intros * ha hb * hc.
        unfold unique.
        exists (transform_us xs₁ xs₂ c us).
        split.
        +
          rewrite hc; clear hc.
          pose proof @generalised_okamoto_commitment_connection n 
            gs h xs₁ xs₂ ha hb as hd.  
          unfold generalised_okamoto_real_protocol, 
          generalised_okamoto_commitment, 
          generalised_okamoto_response,
          transform_us.
          f_equal. 
          ++
            f_equal.
            unfold generalised_okamoto_commitment in hd.
            rewrite generalised_okamoto_commitment_tranform_connection.
            remember (fold_right (λ '(g, u) (acc : G), gop (g ^ u) acc) 
            (zip_with pair gs us) gid) as ret.
            rewrite hd.
            rewrite vid_identity, right_identity; reflexivity.
          ++
            eapply zip_with_transform.
        +
          intros ys hd.
          rewrite hc in hd; clear hc.
          unfold generalised_okamoto_real_protocol, 
          generalised_okamoto_commitment, 
          generalised_okamoto_response in hd.
          inversion hd as [[hu hv]]; clear hd.
          clear ha hb hu gs h a rs.
          revert n xs₁ xs₂ us c ys hv.
          induction n as [|n ihn].
          ++
            intros * haa.
            destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
            destruct (vector_inv_S xst₁) as (xsth₁ & xstt₁ & hb).
            pose proof (vector_inv_0 xstt₁) as hc.
            destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hd).
            destruct (vector_inv_S xst₂) as (xsth₂ & xstt₂ & he).
            pose proof (vector_inv_0 xstt₂) as hf.
            destruct (vector_inv_S us) as (uh & ust & hg).
            destruct (vector_inv_S ust) as (usth & ustt & hh).
            pose proof (vector_inv_0 ustt) as hi.
            destruct (vector_inv_S ys) as (yh & yst & hj).
            destruct (vector_inv_S yst) as (ysth & ystt & hk).
            pose proof (vector_inv_0 ystt) as hl.
            subst. cbn in haa |- *.
            inversion haa as [[haal haar]]; clear haa.
            f_equal.
            eapply f_equal with (f := fun x => 
               x - (c * xh₂)) in haal.
            assert (ha : yh + c * xh₂ - c * xh₂ = 
              yh + (c * xh₂ - c * xh₂)). field.
            rewrite ha in haal; clear ha.
            assert (ha : c * xh₂ - c * xh₂ = zero). field.
            rewrite ha in haal. 
            rewrite right_identity in haal. 
            rewrite <-haal. field.
            f_equal. 
            apply f_equal with (f := fun x => 
               x - (c * xsth₂)) in haar.
            assert (ha : ysth + c * xsth₂ - c * xsth₂ = 
              ysth + (c * xsth₂ - c * xsth₂)). field.
            rewrite ha in haar; clear ha.
            assert (ha : (c * xsth₂ - c * xsth₂) = zero).
            field.
            rewrite ha, right_identity in haar.
            rewrite <-haar; field.
          ++
            intros * haa.
            destruct (vector_inv_S xs₁) as (xh₁ & xst₁ & ha).
            destruct (vector_inv_S xs₂) as (xh₂ & xst₂ & hb).
            destruct (vector_inv_S us) as (uh & ust & hc).
            destruct (vector_inv_S ys) as (yh & yst & hd).
            subst. cbn in haa |- *.
            eapply vec_inv in haa. 
            destruct haa as [haal haar].
            f_equal. 
            eapply f_equal with (f := fun x => 
              x - (c * xh₂)) in haal.
            assert (ha : yh + c * xh₂ - c * xh₂ = 
              yh + (c * xh₂ - c * xh₂)). field.
            rewrite ha in haal; clear ha.
            assert (ha : c * xh₂ - c * xh₂ = zero). field.
            rewrite ha in haal. 
            rewrite right_identity in haal. 
            rewrite <-haal. field.
            eapply ihn. exact haar.
      Qed.

    End Proofs.
  End WI.
End Okamoto. 
 