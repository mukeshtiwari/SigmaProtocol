From Coq Require Import 
  Morphisms.
From Algebra Require Import 
  Hierarchy Monoid.

Section Group. 

  Context 
    {T : Type} 
    {eq : T -> T -> Prop} 
    {op : T -> T -> T} 
    {id : T} 
    {inv : T -> T}
    {Hgroup : @group T eq op id inv}.
  
    Local Infix "=" := eq : type_scope. 
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Infix "*" := op.
    
    
    Lemma group_cancel_right : 
      forall z x y, x * z = y * z <-> x = y.
    Proof. 
      intros ? ? ?; split; intro H.
      eapply monoid_cancel_right with (iz := inv z).
      instantiate (1 := z). 
      apply right_inverse.
      exact H. 
      rewrite H; reflexivity.
    Qed.

    Lemma group_cancel_left : 
      forall z x y, z * x = z * y <-> x = y.
    Proof. 
      intros ? ? ?; split; intro H.
      eapply monoid_cancel_left with (iz := inv z).
      instantiate (1 := z). 
      apply left_inverse.
      exact H. 
      rewrite H; reflexivity.
    Qed. 

    Lemma group_inv_inv : forall x, 
      inv (inv x) = x.
    Proof.
      intros ?.
      eapply monoid_inv_inv;
      try instantiate (1 := inv x);
      apply left_inverse.
    Qed. 

    Lemma group_inv_op_ext : 
      forall x y, (inv y * inv x) * (x * y) = id.
    Proof. 
      intros ? ?.
      eapply monoid_inv_op; 
      apply left_inverse.
    Qed. 

    Lemma group_inv_flip : 
      forall x y, inv (x * y) = inv y * inv x.
    Proof.
      intros ? ?.
      pose proof (group_cancel_right x (inv (x * y)) (inv y * inv x)) as Hg.
      apply Hg; clear Hg. 
      assert (Ht : inv y * inv x * x = inv y * (inv x * x)) by 
       (rewrite associative; reflexivity).
      rewrite Ht, left_inverse, right_identity.
      pose proof (group_cancel_right y (inv (x * y) * x) (inv y)) as Hg.
      apply Hg; clear Hg. 
      rewrite left_inverse.
      assert (H : inv (x * y) * x * y = inv (x * y) * (x * y)) by 
        (rewrite associative; reflexivity). 
      rewrite H.
      apply left_inverse.
    Qed. 
    
    Lemma group_inv_unique : 
      forall x y, y * x = id <-> y = inv x.
    Proof.
      intros ? ?; split; intros H.
      pose proof (group_cancel_right (inv x) (y * x) id) as Hg.
      apply Hg in H. 
      rewrite left_identity in H. 
      rewrite <- associative, right_inverse,
        right_identity in H. 
      exact H.
      rewrite H, left_inverse; reflexivity.
    Qed.
    
    Lemma group_inv_bijective : 
      forall x y, inv x = inv y <-> x = y.
    Proof.
      intros ? ?; split; intros H.
      apply group_cancel_right with (z := x) in H.
      rewrite left_inverse in H.
      apply group_cancel_left with (z := y) in H.
      rewrite 
        associative, 
        right_inverse,
        right_identity,
        left_identity in H.
      symmetry in H. 
      exact H.
      rewrite H; reflexivity.
    Qed. 

    Lemma group_inv_id : inv id = id.
    Proof.
      symmetry; 
      apply group_inv_unique,
      right_identity.
    Qed. 

    Lemma group_inv_id_iff : 
      forall x, inv x = id <-> x = id.
    Proof.
      intros ?; split; intros H.
      apply group_inv_bijective.
      rewrite group_inv_id.
      exact H.
      rewrite H; 
      apply group_inv_id.
    Qed. 

    Lemma group_inv_nonzero_nonzero : 
      forall x, x <> id <-> inv x <> id.
    Proof.
      intros ?. 
      rewrite group_inv_id_iff; reflexivity.
    Qed. 

    Lemma group_eq_r_opp_r_inv : 
      forall x y z, x = op z (inv y) <-> op x y = z.
    Proof.
      intros ? ? ?; split; intros H.
      apply group_cancel_right with (z := y) in H.
      rewrite 
        <- associative, 
        left_inverse, 
        right_identity in H. 
      exact H.
      apply group_cancel_right with (z := inv y) in H.
      rewrite 
        <- associative, 
        right_inverse, 
        right_identity in H. 
      exact H.
    Qed. 

    Section ZeroNeqOne.
      Context 
        {one : T} 
        {Hn : @is_zero_neq_one T eq id one}.
      
      Lemma opp_one_neq_zero : inv one <> id.
      Proof.
        intro Ht. 
        rewrite group_inv_id_iff in Ht.
        pose proof zero_neq_one as H.
        unfold not in H. 
        symmetry in Ht.
        apply H in Ht. 
        exact Ht.
      Qed. 
    End ZeroNeqOne.
End Group.

        
  



