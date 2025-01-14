From Coq Require Import 
  Morphisms Lia.
From Algebra Require Import 
  Hierarchy Monoid Group
  Ring Integral_domain 
  Field.

Section Vector_Space.

  (* Underlying Field of Vector Space *)
  Context 
    {F : Type} 
    {eqf : F -> F -> Prop}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.


  
  (* Vector Element *)
  Context 
    {V : Type} 
    {eqv : V -> V -> Prop}
    {vid : V} {vopp : V -> V}
    {vadd : V -> V -> V} {smul : V -> F -> V}
    {Hvec: @vector_space F eqf zero one add mul 
      sub div opp inv V eqv vid vopp vadd smul}.
    
  Local Infix "=" := eqv : type_scope. 
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "*s" := smul (at level 40).
  Local Infix "+v" := vadd (at level 50).
  
  
  

  (* smul will be ^ pow function *)
  Lemma connection_between_vopp_and_fopp : 
    forall u v, vopp (u *s v) = u *s (opp v). 
  Proof.
    intros ? ?.
    eapply group_cancel_right with (z := smul u v).
    rewrite group_is_left_inverse,
     <-(@vector_space_smul_distributive_fadd F eqf zero one add mul sub div
      opp inv V eqv vid vopp vadd smul),
      field_zero_iff_left,
      vector_space_field_zero;
      try reflexivity; 
      exact Hvec.
  Qed.

  Lemma smul_pow_up : 
    forall g x r, (g *s x) *s r = g *s (mul x r).
  Proof.
    intros ? ? ?.
    rewrite (@vector_space_smul_associative_fmul F eqf); 
    try reflexivity; exact Hvec.
  Qed.

  Lemma smul_pow_mul : 
    forall g x r, smul (smul g x) r = smul g (mul r x).
  Proof.
    intros ? ? ?.
    rewrite smul_pow_up, commutative; 
    reflexivity.
  Qed.





End Vector_Space.    
  