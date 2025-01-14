From Coq Require Import 
  Morphisms.

Local Close Scope nat_scope. 
Local Close Scope type_scope.
Local Close Scope core_scope.

(* This code is inspired/taken from Fiat-Crypto and extended with 
  Vector Space to avoid the scalor_mult type class. Moreover, 
  some improvements have been added (pull request already 
  sent: https://github.com/mit-plv/fiat-crypto/pull/1012 
*)

Section Algebra.

    (* A Set S with one operation *)
  Section OneTypeOneOp.

    Context 
      {T : Type} 
      {eq : T -> T -> Prop}
      {op : T -> T -> T} 
      {id : T}.

    Local Infix "=" := eq : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    
    
   
    (* Print Visibility type_scope. *)
  
    Class is_associative :=
      associative : forall x y z, 
        op x (op y z) = op (op x y) z.
  
    Class is_left_identity := 
      left_identity : forall x, op id x = x.
    
    Class is_right_identity :=
      right_identity : forall x, op x id = x.
    
    Class monoid :=
    {
      monoid_is_associative : is_associative;
      monoid_is_left_idenity : is_left_identity;
      monoid_is_right_identity : is_right_identity;
      monoid_op_Proper: Proper (eq ==> eq ==> eq) op;
      monoid_Equivalence : Equivalence eq
    }.


    Global Existing Instance monoid_is_associative.
    Global Existing Instance monoid_is_left_idenity.
    Global Existing Instance monoid_is_right_identity.
    Global Existing Instance monoid_op_Proper.
    Global Existing Instance monoid_Equivalence.

    Context {inv : T -> T}.
    
    Class is_left_inverse :=
      left_inverse : forall x, op (inv x) x = id.
    
    Class is_right_inverse :=
      right_inverse : forall x, op x (inv x) = id. 
    
    Class group :=
    {
      group_monoid : monoid;
      group_is_left_inverse : is_left_inverse;
      group_is_right_inverse : is_right_inverse;
      group_inv_Proper : Proper (eq ==> eq) inv
    }.

    Global Existing Instance group_monoid.
    Global Existing Instance group_is_left_inverse.
    Global Existing Instance group_is_right_inverse.
    Global Existing Instance group_inv_Proper.

    Class is_commutative :=
      commutative : forall x y, op x y = op y x.

    (* commutative group is declared as record in fiat-crypto *)
    Class commutative_group :=
    {
      commutative_group_group : group;
      commutative_group_is_commutative : is_commutative
    }.

    Global Existing Instance commutative_group_group.
    Global Existing Instance commutative_group_is_commutative.

  End OneTypeOneOp.

  
  
  Section OneTypeTwoOp.

    Context 
      {T : Type} 
      {eq : T -> T -> Prop} 
      {zero one : T} 
      {opp : T -> T} 
      {add : T -> T -> T}
      {sub : T -> T -> T} 
      {mul : T -> T -> T}.


    Local Infix "=" := eq : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    Local Notation "0" := zero.
    Local Notation "1" := one.
    Local Notation "- x" := (opp x).
    Local Infix "+" := add.
    Local Infix "-" := sub. 
    Local Infix "*" := mul.

    Class is_left_distributive := 
      left_distributive : forall x y z, 
        x * (y + z) = x * y + x * z. 
    
    Class is_right_distributive :=
      right_distributive : forall x y z, (y + z) * x = y * x + z * x.

    Class ring :=
    {
      ring_commutative_group_add : 
        commutative_group (eq := eq) (op := add) (id := zero) (inv := opp);
      ring_monoid_mul : monoid (eq := eq) (op := mul) (id := one);
      ring_is_left_distributive : is_left_distributive;
      ring_is_right_distributive : is_right_distributive;
      ring_sub_definition : forall x y, x - y = x + opp y;
      ring_mul_Proper : Proper (eq ==> eq ==> eq) mul;
      ring_sub_Proper : Proper (eq ==> eq ==> eq) sub

    }.

    Global Existing Instance ring_commutative_group_add.
    Global Existing Instance ring_monoid_mul.
    Global Existing Instance ring_is_left_distributive.
    Global Existing Instance ring_is_right_distributive.
    Global Existing Instance ring_mul_Proper.
    Global Existing Instance ring_sub_Proper.

    
    Class commutative_ring :=
    {
      commutative_ring_ring : ring;
      commutative_ring_is_commutative : is_commutative (eq := eq) (op := mul)
    }.

    Global Existing Instance commutative_ring_ring.
    Global Existing Instance commutative_ring_is_commutative.

    Class is_zero_product_zero_factor :=
      zero_product_zero_factor : forall x y, x * y = 0 -> x = 0 \/ y = 0.
      
    Class is_zero_neq_one :=
      zero_neq_one : zero <> one.

    (* I don't see any immediate usage of Integral domain *)
    Class integral_domain :=
    {
      integral_domain_commutative_ring : commutative_ring;
      integral_domain_is_zero_product_zero_factor : is_zero_product_zero_factor;
      integral_domain_is_zero_neq_one : is_zero_neq_one
    }.


    Global Existing Instance integral_domain_commutative_ring.
    Global Existing Instance integral_domain_is_zero_product_zero_factor.
    Global Existing Instance integral_domain_is_zero_neq_one.
   
    Context 
      {inv : T -> T}
      {div : T -> T -> T}.

    
    Class is_left_multiplicative_inverse := 
      left_multiplicative_inverse : forall x, x <> 0 -> (inv x) * x = 1.

    Class field :=
    {
      field_commutative_ring : commutative_ring;
      field_is_left_multiplicative_inverse : is_left_multiplicative_inverse;
      field_is_zero_neq_one : is_zero_neq_one;
      field_div_definition : forall x y , div x y = x * inv y;
      field_inv_Proper : Proper (eq ==> eq) inv;
      field_div_Proper : Proper (eq ==> eq ==> eq) div
    }.


    Global Existing Instance field_commutative_ring.
    Global Existing Instance field_is_left_multiplicative_inverse.
    Global Existing Instance field_is_zero_neq_one.
    Global Existing Instance field_inv_Proper.
    Global Existing Instance field_div_Proper.


  End OneTypeTwoOp.

  Section VectorSpace.

   (* Scalar Elements *)
    Context 
      {F : Type} 
      {eqf : F -> F -> Prop}
      {zero one : F}
      {add mul sub div : F -> F -> F}
      {opp inv : F -> F}.

    Local Notation "0" := zero.
    Local Notation "1" := one.
    Local Notation "- x" := (opp x).
    Local Infix "+" := add.
    Local Infix "*" := mul.
    Local Infix "-" := sub. 
    Local Infix "/" := div.
    
    (* Vector Elements *)
    Context 
      {V : Type}
      {eqv : V -> V -> Prop}
      {vid : V} 
      {vopp : V -> V}
      {vadd : V -> V -> V} 
      {smul : V -> F -> V}.


    Local Infix "=" := eqv : type_scope.
    Local Notation "a <> b" := (not (a = b)) : type_scope.
    (* Print Grammar constr. *)
    Local Infix "*s" := smul 
      (at level 40).
    Local Infix "+v" := vadd 
      (at level 50).
      
    

    Class is_field_one :=
      field_one : forall v, v *s 1 = v.

    Class is_field_zero :=
      field_zero : forall v, v *s 0 = vid.
      
    (* what will be the correct name for this? *)  
    Class is_smul_associative_fmul := 
      smul_associative_fmul : forall r1 r2 v, 
        v *s (r1 * r2) = (v *s r1) *s r2.

    Class is_smul_distributive_fadd :=
      smul_distributive_fadd : forall r1 r2 v, 
        v *s (r1 + r2) = (v *s r1) +v (v *s r2).
  
    Class is_smul_distributive_vadd :=
      smul_distributive_vadd : forall r v1 v2, 
        (v1 +v v2) *s r = (v1 *s r) +v (v2 *s r).


    (* https://www.maths.usyd.edu.au/u/bobh/UoS/MATH2902/vswhole.pdf *)  
    Class vector_space :=
    {
      vector_space_commutative_group : 
        commutative_group (eq := eqv) (op := vadd) (id := vid) (inv := vopp);
      vector_space_field : 
        field (eq := eqf) (zero := zero) (one := one) 
        (opp := opp) (add := add) (sub := sub) (mul := mul) 
        (inv := inv) (div := div);
      vector_space_field_one : is_field_one;
      vector_space_field_zero : is_field_zero;
      vector_space_smul_associative_fmul : is_smul_associative_fmul;
      vector_space_smul_distributive_fadd : is_smul_distributive_fadd;
      vector_space_smul_distributive_vadd : is_smul_distributive_vadd;
      vector_space_smul_Proper : Proper (eqv ==> eqf ==> eqv) smul;
    }.

    Global Existing Instance vector_space_commutative_group.
    Global Existing Instance vector_space_field.
    Global Existing Instance vector_space_field_one.
    Global Existing Instance vector_space_field_zero.
    Global Existing Instance vector_space_smul_associative_fmul.
    Global Existing Instance vector_space_smul_distributive_fadd.
    Global Existing Instance vector_space_smul_distributive_vadd.
    Global Existing Instance vector_space_smul_Proper.

  End VectorSpace.

End Algebra.
    
Section ZeroNeqOne.
  Context 
    {T eq zero one} 
    {Hne: @is_zero_neq_one T eq zero one} 
    {He : @Equivalence T eq}.

  Lemma one_neq_zero : not (eq one zero).
  Proof.
    intro HH; 
    symmetry in HH. 
    auto using zero_neq_one.
  Qed.
End ZeroNeqOne.





  
