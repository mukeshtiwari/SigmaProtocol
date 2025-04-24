From Stdlib Require Import 
  Ncring Cring ZArith 
  PArith Morphisms Lia.
From Algebra Require Import 
  Hierarchy Monoid Group.



Section Ring.

  Context 
    {T : Type}
    {eq : T -> T -> Prop} 
    {zero one : T} 
    {opp : T -> T} 
    {add sub mul : T -> T -> T} 
    {Hr : @ring T eq zero one opp add sub mul}.

  Local Infix "=" := eq : type_scope. 
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Notation "0" := zero. 
  Local Notation "1" := one.
  Local Infix "+" := add. 
  Local Infix "-" := sub. 
  Local Infix "*" := mul.   

  
  Global Instance Ncring_ops : 
    @Ncring.Ring_ops T 0 1 add mul sub opp eq.
  Defined.


  Global Instance Ncring_ring : 
    @Ncring.Ring T 0 1 add mul sub opp eq Ncring_ops.
  Proof.
    split; try (typeclasses eauto).
    + intros ?. 
      rewrite left_identity; 
      reflexivity.
    + intros ? ?. 
      rewrite commutative; 
      reflexivity.
    + intros ? ? ?. 
      rewrite associative; 
      reflexivity.
    + intros ?; 
      rewrite left_identity; 
      reflexivity.
    + intros ?; 
      rewrite right_identity; 
      reflexivity.
    + intros ? ? ?; 
      rewrite associative; 
      reflexivity.
    + intros ? ? ?; 
      rewrite right_distributive; 
      reflexivity.
    + intros ? ? ?; 
      rewrite left_distributive; 
      reflexivity.
    + intros ? ?; 
      rewrite ring_sub_definition; 
      reflexivity.
    + intros ?;
      rewrite right_inverse; 
      reflexivity.
  Defined.


  Lemma ring_mul_0_l : forall x, 0 * x = 0.
  Proof.
    apply Ncring.ring_mul_0_l.
  Qed. 

  Lemma ring_mul_0_r : forall x, x * 0 = 0.
  Proof.
    apply Ncring.ring_mul_0_r.
  Qed.

  Lemma ring_sub_0_l : forall x, 0 - x = opp x.
  Proof.
    intros ?.
    rewrite ring_sub_definition.
    rewrite commutative. 
    apply Ncring.ring_add_0_r.
  Qed.

  Lemma ring_mul_opp_r : forall x y, x * opp y = opp (x * y).
  Proof.
    intros ? ?.
    symmetry. 
    apply Ncring.ring_opp_mul_r.
  Qed.

  Lemma ring_mul_opp_l : forall x y, opp x * y = opp (x * y).
  Proof.
    intros ? ?.
    symmetry. 
    apply Ncring.ring_opp_mul_l.
  Qed.

  Lemma ring_opp_zero_iff : forall x, opp x = 0 <-> x = 0. 
  Proof. 
    apply Group.group_inv_id_iff. 
  Qed.

  Global Instance is_left_distributive_sub : 
    is_left_distributive (eq := eq)(add := sub)(mul := mul).
  Proof.
    intros ? ? ?.
    rewrite !ring_sub_definition.
    rewrite 
      left_distributive, 
      ring_mul_opp_r;
    reflexivity.
  Qed.
  
  Global Instance is_right_distributive_sub : 
    is_right_distributive (eq := eq)(add := sub)(mul := mul).
  Proof.
    intros ? ? ?.
    repeat rewrite ring_sub_definition.
    rewrite 
      right_distributive, 
      ring_mul_opp_l;
    reflexivity.
  Qed. 

  Lemma ring_sub_zero_iff : 
    forall x y, x - y = 0 <-> x = y.
  Proof.
    intros ? ?; 
    split; 
    intros H.
    rewrite ring_sub_definition,
    group_inv_unique, 
    group_inv_inv in H.
    exact H.
    rewrite H, 
    ring_sub_definition, 
    right_inverse;
    reflexivity.
  Qed.
  
  Lemma ring_neq_sub_neq_zero : 
    forall x y, x <> y -> x-y <> 0.
  Proof.
    intros ? ? H Hsub.
    pose proof (proj1 (ring_sub_zero_iff _ _) Hsub) as Ht.
    unfold not in H. 
    apply H in Ht.
    inversion Ht.
  Qed. 

  Lemma ring_zero_product_iff_zero_factor 
    {Hzpzf : @is_zero_product_zero_factor T eq zero mul} :
    forall x y : T, x * y = 0 <-> x = 0 \/ y = 0.
  Proof.
    intros ? ?; split; intros H.
    apply zero_product_zero_factor; exact H.
    destruct H; rewrite H;
     [apply ring_mul_0_l | apply ring_mul_0_r].
  Qed. 

  Lemma nonzero_product_iff_nonzero_factor 
    {Hzpzf : @is_zero_product_zero_factor T eq zero mul} :
    forall x y : T,  x * y <> 0 <-> x <> 0 /\ y <> 0.
  Proof.
    intros ? ?; 
    split; 
    intros H.
    split; 
    intro Ht; apply H;
    rewrite Ht; 
    [rewrite ring_mul_0_l | rewrite ring_mul_0_r];
    reflexivity. 
    intro Ht. 
    destruct H as [H1 H2].
    apply ring_zero_product_iff_zero_factor in Ht.
    destruct Ht as [Ht | Ht]. 
    apply H1 in Ht. 
    exact Ht. 
    apply H2 in Ht. 
    exact Ht.
  Qed. 

End Ring.

Section Cring.

  Context 
    {T eq zero one opp add sub mul} 
    {Hcring : @commutative_ring T eq zero one opp add sub mul}.

  Global Instance Cring_commutative_ring : 
   @Cring.Cring T zero one add mul sub opp eq Ncring_ops Ncring_ring. 
  Proof.
    intros ? ?.
    apply commutative.
  Defined.

  Lemma ring_theory_for_stdlib_tactic : 
    Ring_theory.ring_theory zero one add mul sub opp eq.
  Proof.
    split; intros; try (typeclasses eauto).
    + apply left_identity.
    + apply commutative.
    + apply associative.
    + apply left_identity.
    + apply commutative.
    + apply associative.
    + apply right_distributive.
    + apply ring_sub_definition.
    + apply right_inverse.
  Qed. 

End Cring. 

Section of_Z.

  
  Local Open Scope Z_scope.
  Context {R Req Rzero Rone Ropp Radd Rsub Rmul}
        {Rring : @ring R Req Rzero Rone Ropp Radd Rsub Rmul}.
  Local Infix "=" := Req : type_scope.
  
  
  Fixpoint of_nat (n : nat) : R := 
    match n with
    | 0%nat => Rzero
    | S n' => Radd Rone (of_nat n')
    end.
  
  
  Definition of_Z (n : Z) : R :=
    match n with
    | Z0 => Rzero
    | Zpos p => of_nat (Pos.to_nat p)
    | Zneg p => Ropp (of_nat (Pos.to_nat p))
    end.

  
  
  Lemma of_Z_0 : of_Z 0 = Rzero.
  Proof. reflexivity. Qed.

  Lemma of_nat_add : forall n,
    of_nat (Nat.add n 1) = Radd (of_nat n) Rone.
  Proof.
    unfold of_nat.
    induction n.
    + simpl. rewrite commutative; reflexivity.
    + simpl. rewrite IHn, associative; reflexivity.
  Qed.

End of_Z.

