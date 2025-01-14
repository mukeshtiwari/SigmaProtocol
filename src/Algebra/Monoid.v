From Coq Require Import 
  Setoid Morphisms Utf8.
From Algebra Require Import 
  Hierarchy.

Section Monoid.
  

  Context 
    {T : Type} 
    {eq : T -> T -> Prop} 
    {op : T -> T -> T}
    {id : T}
    {Hmonoid : @monoid T eq op id}.


  Local Infix "=" := eq : type_scope.
  Local Notation "a <> b" := (not (a = b)) : type_scope.
  Local Infix "*" := op.
  
  

  Lemma monoid_cancel_left z iz (Hinv : op iz z = id) :
    forall x y, (z * x) = (z * y) <-> x = y.
  Proof.
    intros ? ?; 
    split; intros H.
    assert (Hcut : (iz * (z * x))  = (iz * (z * y))).
    rewrite H. reflexivity.
    rewrite !(@monoid_is_associative T eq op id Hmonoid) in Hcut.
    rewrite Hinv in Hcut. 
    rewrite !monoid_is_left_idenity in Hcut.
    exact Hcut.
    rewrite H. 
    reflexivity.
  Qed.
  
  
  Lemma monoid_cancel_right z iz (Hinv : op z iz = id) :  
    forall x y, x * z = y * z <-> x = y.
  Proof.
    intros ? ?; split; intro H.
    assert (op (op x z) iz = op (op y z) iz) as Hcut.
    rewrite H; reflexivity.
    rewrite <- !(@monoid_is_associative T eq op id Hmonoid) in Hcut.
    rewrite Hinv in Hcut.
    rewrite !monoid_is_right_identity in Hcut.
    exact Hcut.
    rewrite H; reflexivity.
  Qed.


  

  (* what can I say about the reverse direction? *)
  Lemma monoid_both_identity : 
    forall a b, a = id ∧ b = id -> a * b = id.
  Proof. 
    intros ? ? H.
    destruct H as [H₁ H₂]; 
    rewrite H₁.
    rewrite monoid_is_left_idenity.
    exact H₂.
  Qed.
  
  
  
  Lemma monoid_inv_inv a b c : b * a = id -> c * b = id -> c = a.
  Proof.
    intros H₁ H₂. 
    assert (Ht : c * (b * a) = c * id) 
      by (rewrite H₁; reflexivity).
    rewrite (@monoid_is_associative T eq op id Hmonoid) in Ht.
    rewrite H₂, 
      monoid_is_left_idenity,
      monoid_is_right_identity in Ht. 
    symmetry in Ht.
    exact Ht.
  Qed.


  Lemma monoid_inv_op x y a b : 
    a * x = id -> b * y = id -> (b * a) * (x * y) = id.
  Proof.
    intros Hx Hy.
    assert(Ht : (a * (x * y)) = ((a * x) * y)) 
      by (rewrite associative; reflexivity).
    rewrite <- associative.
    rewrite Ht, Hx, left_identity. 
    exact Hy.
  Qed.
  
End Monoid. 
