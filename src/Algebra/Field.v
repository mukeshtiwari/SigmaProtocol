From Stdlib Require Import 
  Morphisms Lia Field_theory 
  Field_tac. 
From Algebra Require Import   
  Hierarchy Monoid Group
  Ring Integral_domain.




Section Field.

  Context 
    {T : Type} 
    {eq : T -> T -> Prop} 
    {zero one : T} 
    {opp : T -> T}
    {add mul sub : T -> T -> T}
    {inv : T -> T} 
    {div : T -> T -> T} 
    {Hfield: @field T eq zero one opp add sub mul inv div}.
  Local Infix "=" := eq : type_scope. 
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero. 
  Local Notation "1" := one.
  Local Infix "+" := add. 
  Local Infix "*" := mul.

  Lemma field_theory_for_stdlib_tactic : 
    Field_theory.field_theory 0 1 add mul sub opp div inv eq.
  Proof.
    constructor.
    apply ring_theory_for_stdlib_tactic.
    intro Hn. 
    symmetry in Hn.
    pose proof (zero_neq_one (eq:=eq)) as Ha.
    eapply Ha in Hn; assumption.
    apply field_div_definition.
    apply left_multiplicative_inverse.
  Qed. 

  Lemma field_zero_iff_left : 
    forall x, (opp x) + x = zero.
  Proof.
    intros ?; rewrite left_inverse.
    reflexivity.
  Qed. 
    

  Lemma field_zero_iff_right : 
    forall x, x + (opp x) = zero.
  Proof.
    intros ?; rewrite right_inverse;
    reflexivity.
  Qed.
  
  Lemma field_right_multiplicative_inverse : 
    forall x : T, x <> 0 -> mul x (inv x) = 1.
  Proof.
    intros ? Hx.
    rewrite commutative. 
    eapply left_multiplicative_inverse;
    assumption.
  Qed.

  
  Lemma field_left_inv_unique : 
  forall x y, y * x = one -> y = inv x.
  Proof.
    intros ? ? Hxy.
    assert (Ht : y * x * inv x = inv x).
    rewrite 
      Hxy, 
      left_identity; 
    reflexivity.
    rewrite 
      <-associative,  
      field_right_multiplicative_inverse, 
      right_identity in Ht; trivial.
    intros Hx. 
    rewrite Hx, ring_mul_0_r in Hxy.
    apply field_is_zero_neq_one in Hxy. 
    exact Hxy.
  Qed.

  Lemma field_right_inv_unique : 
    forall x y, x * y = one -> y = inv x.
  Proof.
    intros ? ? H. 
    rewrite commutative in H. 
    apply field_left_inv_unique. 
    exact H.
  Qed.

  Lemma field_div_one: 
    forall x, div x one = x.
  Proof.
    intros ?.
    rewrite field_div_definition.
    rewrite <-(field_left_inv_unique 1 1);
    apply monoid_is_right_identity.
  Qed.

  Lemma field_mul_cancel_l_iff : 
    forall x y, y <> 0 -> (x * y = y <-> x = one).
  Proof.
    intros x y Ht.
    split; intros H₁.
    + rewrite <-(field_right_multiplicative_inverse y) by assumption.
      rewrite <-H₁ at 1; 
      rewrite <-associative.
      rewrite field_right_multiplicative_inverse by assumption.
      rewrite right_identity.
      reflexivity.
    + rewrite H₁; 
      apply left_identity.
  Qed.

  Lemma field_mul_not_zero : 
    forall x y : T, x <> 0 -> y <> 0 -> x * y <> 0.
  Proof.
    intros x y Hx Hy Hn.
    apply field_right_multiplicative_inverse in Hx.
    apply field_right_multiplicative_inverse in Hy.
    assert (Ht: x * inv x * y * inv y = 1).
    rewrite Hx, left_identity, Hy; reflexivity.
    assert(Hab: x * inv x * y * inv y = x * y * inv x * inv y).
      rewrite <-!associative.
    assert (Htt: inv x * (y * inv y) = (y * inv y) * inv x).
      rewrite commutative; reflexivity.
    rewrite Htt, <-associative.
    assert (Httt: inv x * inv y = inv y * inv x) 
      by (rewrite commutative; reflexivity).
    rewrite Httt. 
    reflexivity.
    rewrite Hab in Ht. 
    clear Hab.
    rewrite Hn in Ht. 
    rewrite !ring_mul_0_l in Ht.
    apply zero_neq_one in Ht. 
    exact Ht.
  Qed.

  (* Require to check if x = 0 \/ y = 0 *)
  Context {eq_dec : forall x y : T, {x = y} + {x <> y}}.

  Global Instance is_mul_nonzero_nonzero : 
    @is_zero_product_zero_factor T eq 0 mul.
  Proof.
    intros x y Hxy.
    assert (Hx: {x = 0} + {x <> 0}) by apply eq_dec. 
    assert (Hy: {y = 0} + {y <> 0}) by apply eq_dec.
    destruct Hx as [Hx | Hx]; 
      destruct Hy as [Hy | Hy].
    left; exact Hx.
    left; exact Hx.
    right; exact Hy.
    pose proof (field_mul_not_zero _ _ Hx Hy). 
    rewrite Hxy in H. 
    unfold not in H.
    assert (Hf : 0 = 0) by reflexivity.
    pose proof (H Hf) as HF; 
    inversion HF.
  Qed.

    



  (* A field is integral domain, but without  *)
   
  Global Instance integral_domain : 
    @integral_domain T eq zero one opp add sub mul.
  Proof.
    split; 
    eauto using field_commutative_ring, 
    field_is_zero_neq_one, 
    is_mul_nonzero_nonzero.
  Qed.
  



End Field.