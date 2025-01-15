From Coq Require Import 
  PArith ZArith Lia
  Znumtheory
  Eqdep_dec Arith
  Zpow_facts Morphisms
  NArith Utf8.
From Utility Require Import 
  Util Functions Fermat. 
From Algebra Require Import 
  Hierarchy.

Module Zpgroup.

  
  (* multiplicative Group *)
  Section ZpstarGroup. 
    Context 
      {p : Z}
      {Hp : prime p}.
  
    Record Zpstar := 
      mk_zpstar {v : Z; Hv : 0 < v < p}.


    Lemma dec_lt_general : 
      forall x y (Hx Hy: (x < y)),  Hx = Hy.
    Proof.
      intros; apply Eqdep_dec.eq_proofs_unicity;
      intros u v; destruct u; destruct v; auto;
      try (right; intro Hpp; inversion Hpp).
    Qed.


    Lemma uniqueness_zpstar_proof : 
      forall x (Hx Hy : (0 < x < p)), Hx = Hy.
    Proof.
      intros ? [Hxl Hxr] [Hyl Hyr];
      f_equal; apply dec_lt_general.
    Qed.


    Lemma dec_zpstar : forall x y : Zpstar, {x = y} + {x <> y}.
    Proof.
      intros [x Hx] [y Hy].
      destruct (Z.eq_dec x y) as [Hl | Hr].
      left. subst. f_equal. 
      apply uniqueness_zpstar_proof.
      right. intro H; inversion H; 
      contradiction.
    Qed.


    Lemma construct_zpstar : 
      forall x y 
      (Hx : 0 < x < p) 
      (Hy : 0 < y < p), 
      x = y -> 
      mk_zpstar x Hx = mk_zpstar y Hy.
    Proof.
      intros; subst; f_equal.
      apply uniqueness_zpstar_proof.
    Qed. 



    (* Neutral Element *)
    Definition one : Zpstar.
      refine (mk_zpstar 1 _).
      pose proof (prime_ge_2 _ Hp).
      abstract nia.
    Defined.

    
    (* multiplication *)
    Definition mul_zpstar (u v : Zpstar) : Zpstar.
      refine(
        match u, v with 
        | mk_zpstar au Hu, mk_zpstar av Hv => 
          mk_zpstar 
            (Z.modulo (au * av) p) 
            (@multiplication_bound p Hp _ _ Hu Hv)
        end).
    Defined.
  
   
    Lemma fermat_theorem : 
      forall au, 
      0 < au < p ->
      Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 1)) (Z.to_N p)) = 1.
    Proof.
      intros ? Hau.
      rewrite zmod_nmod, 
      !Z2N.id.
      rewrite fermat_little_ZZ;
      try nia; try assumption.
      all:try nia.
      rewrite !Z2N.id.
      exact Hp.
      nia.
    Qed.



    Lemma mod_bound : forall au, 
      0 < au < p ->
      0 < Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)) < p.
    Proof.
      intros ? Ha.
      rewrite zmod_nmod, 
      !Z2N.id.
      apply fermat_bound.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.
    
     


    (* u ^ (p - 2) is inverse of u *)
    Definition inv_zpstar (u : Zpstar) : Zpstar.
      refine(
        match u with 
        | mk_zpstar au Hu => mk_zpstar 
            (Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)))
            (mod_bound _ Hu) 
        end).
    Defined.  
    
    (* Now I need to establish that it's a group *)

    Lemma zpstar_mul_associative : 
      forall x y z : Zpstar, 
      mul_zpstar x (mul_zpstar y z) =  
      mul_zpstar (mul_zpstar x y) z.
    Proof.
      pose proof @H_0_p p Hp.
      intros ? ? ?; 
      destruct x as [x Hx]; 
      destruct y as [y Hy]; 
      destruct z as [z Hz]; 
      simpl in * |- *.
      eapply construct_zpstar.
      rewrite Z.mul_mod_idemp_l.
      rewrite Z.mul_mod_idemp_r.
      rewrite Z.mul_assoc. 
      reflexivity.
      all:nia.
    Qed.

    Lemma one_is_left_identity : 
      forall x, mul_zpstar one x = x.
    Proof.
      intro x. 
      unfold mul_zpstar, one.
      destruct x as [x Hx]. 
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_1_l. 
      apply mod_not_zero_one. 
      exact Hx.
    Qed.

    Lemma one_is_right_identity : 
      forall x, mul_zpstar x one = x.
    Proof.
      intro x. 
      unfold mul_zpstar, one.
      destruct x as [x Hx]. 
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_1_r. 
      apply mod_not_zero_one. 
      exact Hx.
    Qed.

  
    Lemma zpstar_mul_commutative : 
      forall x y : Zpstar, 
      mul_zpstar x y =  mul_zpstar y x.
    Proof.
      destruct x as [x Hx]; 
      destruct y as [y Hy]; simpl.
      refine(construct_zpstar _ _ _ _ _).
      rewrite Z.mul_comm.
      reflexivity.
    Qed.

    Global Instance zpstar_mul_proper : 
      Proper (eq ==> eq ==> eq) mul_zpstar.
    Proof.
      intros x y Hxy z u Hzu.
      destruct x as [x Hx]; destruct y as [y Hy];
      destruct z as [z Hz]; destruct u as [u Hu]; simpl in * |- *.
      refine(construct_zpstar _ _ _ _ _).
      inversion Hxy; inversion Hzu; subst; reflexivity.
    Defined. 

    Lemma zpstar_left_inv :
      forall x, mul_zpstar (inv_zpstar x) x = one.
    Proof.
      intros ?.
      unfold mul_zpstar, inv_zpstar, one.
      destruct x as (v & Hv).
      apply construct_zpstar.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia. 
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp. 
      rewrite Z.pow_add_r. 
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp. 
      exact Hv.
      nia. 
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.
    
    Lemma zpstar_right_inv :
      forall x, mul_zpstar x (inv_zpstar x) = one.
    Proof.
      intros ?.
      unfold mul_zpstar, inv_zpstar, one.
      destruct x as (v & Hv).
      apply construct_zpstar.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia. 
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp. 
      rewrite Z.pow_add_r. 
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp. 
      exact Hv.
      nia. 
      rewrite Z2N.id.
      exact Hp.
      nia. 
    Qed.


    (* Zpstar is a commutative Group *)
    Global Instance zpstar_comm : @commutative_group 
      Zpstar (@eq Zpstar) mul_zpstar one inv_zpstar.
    Proof.
      repeat econstructor.
      + unfold is_associative; 
        intros ? ? ?.
        apply zpstar_mul_associative.
      + intro x. apply one_is_left_identity.
      + intro x. apply one_is_right_identity.
      + apply zpstar_mul_proper.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y z Hxy Hyz. rewrite Hxy. exact Hyz.
      + intro x. apply zpstar_left_inv.
      + intro x. apply zpstar_right_inv.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y. apply zpstar_mul_commutative.
    Qed. 


  End ZpstarGroup.
End Zpgroup.



Module Zpfield.

  (* Prime Field *)
  Section ZpField.

    Context 
      {p : Z}
      {Hp : prime p}.


      
    Record Zp := 
      mk_zp {v : Z; Hv : Z.modulo v p = v}.

    
    Definition zero : Zp. 
      refine (mk_zp 0 (Z.mod_0_l _ _)).
      pose proof prime_ge_2 _ Hp as Ht.
      abstract nia.
    Defined.



    Definition one : Zp. 
      refine(mk_zp 1 (Z.mod_1_l _ _ )).
      pose proof prime_ge_2 _ Hp as Ht.
      abstract nia.
    Defined.


    Definition zp_add (x y : Zp) : Zp.
      refine (match x, y with
        | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax + ay) p) _ 
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.
    

    Definition zp_sub (x y : Zp) : Zp.
      refine (match x, y with
      | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax - ay) p) _ 
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.


    Definition zp_opp (x : Zp) : Zp :=
      zp_sub zero x.

    
        
    Definition zp_mul (x y : Zp) : Zp.
      refine (match x, y with
        | mk_zp ax _, mk_zp ay _ => mk_zp (Z.modulo (ax * ay) p) _ 
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.



    Definition zp_inv (x : Zp) : Zp.
      refine (match x with
        | mk_zp ax Hu => mk_zp 
          (Z.modulo 
            (Z.of_N (Npow_mod (Z.to_N ax) (Z.to_N (p - 2)) (Z.to_N p)))
            p) _ 
      end).
      rewrite Zmod_mod.
      exact eq_refl.
    Defined.


    Definition zp_div (x y : Zp) : Zp :=
      zp_mul x (zp_inv y).
    
    (* Proofs about field element *)

    (*uniqueness of identity proof *)
    Lemma zple_gen : 
      forall v 
      (H₁ H₂ : Z.modulo v p = v), 
      H₁ = H₂.
    Proof.
      intros v ? ?.
      apply UIP_dec, 
      Z.eq_dec.
    Qed.


      
    Lemma construct_zp : 
      forall x y 
      (Hx : Z.modulo x p = x) 
      (Hy : Z.modulo y p = y), 
      x = y -> 
      mk_zp x Hx = mk_zp y Hy.
    Proof.
      intros; subst; f_equal.
      apply zple_gen.
    Qed. 
      
      
    Lemma zp_dec: forall x y : Zp, {x = y} + {x <> y}.
    Proof.
      intros x y. destruct x as [x Hx]; destruct y as [y Hy]; simpl.
      destruct (Z.eq_dec x y) as [Hl | Hr]. left.
      refine(construct_zp _ _ _ _ Hl).
      right. intro H; inversion H; contradiction.
    Defined.

    (* proof that opp x = sub 0 x (mod p) *)
    Lemma zp_opp_sub : 
      forall x, zp_opp x = zp_sub zero x.
    Proof. 
      intros [x Hx]; unfold zero, zp_opp, zp_sub; simpl.
      refine(construct_zp _ _ _ _ _); reflexivity.
    Qed.


    Lemma zp_mul_inv_div : 
    forall x y, zp_mul x (zp_inv y) = zp_div x y.
    Proof.
      intros [x Hx] [y Hy]; simpl.
      refine(construct_zp _ _ _ _ _).
      reflexivity.
    Qed.

    Lemma zp_add_assoc: 
      forall x y z : Zp, 
      zp_add x (zp_add y z) = zp_add (zp_add x y) z.
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.add_mod_idemp_l.
      rewrite Z.add_mod_idemp_r.
      rewrite Z.add_assoc. 
      reflexivity.
      all:nia.
    Qed.
      
    Lemma zp_add_zero_left_identity : 
      forall x, zp_add zero x = x.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      exact Hx.
    Qed.


    Lemma zp_add_zero_right_identity : 
      forall x, zp_add x zero = x.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.add_0_r.
      exact Hx.
    Qed.

    Global Instance zp_add_proper : Proper (eq ==> eq ==> eq) zp_add.
    Proof.
      intros x y Hxy u v Huv; subst; reflexivity.
    Qed.

    Global Instance eq_sym : @Symmetric Zp eq.
    Proof. 
      intros x y Hxy. subst; reflexivity.
    Qed.

    Global Instance eq_trans : @Transitive Zp eq.
    Proof.
      intros x y z Hxy Hyz; subst; reflexivity.
    Qed.

    Lemma zp_add_opp_left_inv : 
      forall x, zp_add (zp_opp x) x = zero.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Zplus_mod_idemp_l.
      rewrite Z.add_opp_diag_l.
      rewrite Zmod_0_l; reflexivity.
    Qed.

    Lemma zp_add_opp_right_inv : 
      forall x, zp_add x (zp_opp x) = zero.
    Proof.
      intros [x Hx]; simpl.
      refine (construct_zp  _ _ _ _ _).
      rewrite Zplus_mod_idemp_r.
      rewrite Z.add_opp_diag_r.
      rewrite Zmod_0_l; reflexivity.
    Qed.

    Global Instance zp_opp_proper : Proper (eq ==> eq) zp_opp.
    Proof.
      intros x y Hx; subst; reflexivity.
    Qed.

    Lemma zp_add_comm : 
      forall x y, zp_add x y = zp_add y x.
    Proof.
      intros [x Hx] [y Hy]; simpl; 
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.add_comm; reflexivity.
    Qed.

    Lemma zp_mul_assoc : 
      forall x y z, 
      zp_mul x (zp_mul y z) = zp_mul (zp_mul x y) z.
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz]; simpl;
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_mod_idemp_l.
      rewrite Z.mul_mod_idemp_r.
      rewrite Z.mul_assoc. reflexivity.
      all:nia.
    Qed.

    Lemma zp_mul_one_left_id : 
      forall x, zp_mul one x = x.
    Proof.
      intros [x Hx]; 
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_1_l.
      exact Hx.
    Qed.

    Lemma zp_mul_one_right_id : 
      forall x, zp_mul x one = x.
    Proof.
      intros [x Hx]; 
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_1_r; exact Hx.
    Qed.


    Global Instance zp_mul_proper: Proper (eq ==> eq ==> eq) zp_mul.
    Proof.
      intros x y Hxy u v Huv; subst; reflexivity.
    Qed.

    Lemma mul_dist_add_left : 
      forall x y z, 
      zp_mul x (zp_add y z) = zp_add (zp_mul x y) (zp_mul x z).
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_mod_idemp_r, 
        Z.add_mod_idemp_l,
        Z.add_mod_idemp_r,
        Z.mul_add_distr_l; 
        try reflexivity;
        try nia.
    Qed.

    Lemma mul_dist_add_right : 
      forall x y z, 
      zp_mul (zp_add y z) x = zp_add (zp_mul y x) (zp_mul z x).
    Proof.
      pose (@H_0_p p Hp) as Hpp.
      intros [x Hx] [y Hy] [z Hz];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_mod_idemp_l,
      Z.add_mod_idemp_r,  Z.mul_add_distr_r, 
      Zplus_mod_idemp_l;
      try reflexivity; try nia.
    Qed.
    

    Lemma zp_sub_add_opp : 
      forall x y : Zp, zp_sub x y = zp_add x (zp_opp y).
    Proof.
      intros [x Hx] [y Hy]; simpl;
      refine (construct_zp  _ _ _ _ _).
      rewrite Zplus_mod_idemp_r, Z.add_opp_r;
      reflexivity.
    Qed.
    
    Global Instance zp_sub_proper : Proper (eq ==> eq ==> eq) zp_sub.
    Proof.
      intros x y Hxy u v Huv; subst; reflexivity.
    Qed.
    
    Lemma zp_not_eq :
      forall x y : Zp, 
      x <> y -> v x <> v y.
    Proof.
      intros [x Hx] [y Hy] Hpp;
      cbn.
      intro Hf.
      apply Hpp.
      refine (construct_zp  _ _ _ _ _).
      exact Hf.
    Qed.

    Lemma zp_mul_comm : forall x y, zp_mul x y = zp_mul y x.
    Proof.
      intros [x Hx] [y Hy];
      refine (construct_zp  _ _ _ _ _).
      rewrite Z.mul_comm; reflexivity.
    Qed.
    
    Lemma zp_mul_left_inv: 
      forall x, x <> zero -> 
      zp_mul (zp_inv x) x = one.
    Proof.
      intros x Hx.
      unfold zp_mul, zp_inv.
      destruct x as (v & Hv).
      apply construct_zp.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmod_mod.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia. 
      assert (Ht : v * v ^ (p - 2) = v ^ (p - 1)).
      rewrite Hpp. 
      rewrite Z.pow_add_r. 
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp.
      unfold zero in Hx.
      pose proof (proj2 (@mod_more_gen_bound p Hp v) Hv) as Htt.
      assert (Hvnz : v <> 0).
      pose proof (zp_not_eq _ _ Hx) as Hppw.
      cbn in Hppw.
      exact Hppw.
      all:try nia.
      pose proof @Hp_2_p p Hp.
      nia.
      pose proof @Hp_2_p p Hp.
      nia.
      pose proof (proj2 (@mod_more_gen_bound p Hp v) Hv) as Htt.
      nia.
      rewrite Z2N.id.
      pose proof @Hp_2_p p Hp.
      nia.
      pose proof @Hp_2_p p Hp.
      nia.
      rewrite Z2N.id.
      exact Hp.
      pose proof @Hp_2_p p Hp.
      nia.
    Qed.
   


    Lemma zero_neq_one : zero <> one.
    Proof.
      intro Hx. 
      unfold zero, one in Hx.
      inversion Hx.
    Qed.

    Global Instance zp_inv_proper: Proper (eq ==> eq) zp_inv.
    Proof.
      intros x y Hxy; subst; reflexivity.
    Qed.

    Global Instance zp_div_proper : Proper (eq ==> eq ==> eq) zp_div.
    Proof.
      intros x y Hxy; subst; reflexivity.
    Qed.



      


    (* Now, I need to establish that it's a Field *)

    Global Instance zp_field : @field Zp (@eq Zp) zero 
      one zp_opp zp_add zp_sub zp_mul zp_inv zp_div.
    Proof.
      repeat constructor.
      + intros x y z. apply zp_add_assoc.
      + intro x. apply zp_add_zero_left_identity.
      + intro x. apply zp_add_zero_right_identity.
      + apply zp_add_proper.
      + apply eq_sym.
      + apply eq_trans.
      + intros x. apply zp_add_opp_left_inv.
      + intros x; apply zp_add_opp_right_inv.
      + apply zp_opp_proper.
      + intros x y; apply zp_add_comm.
      + intros x y z; apply zp_mul_assoc.
      + intro x; apply zp_mul_one_left_id.
      + intro x; apply zp_mul_one_right_id.
      + apply zp_mul_proper.
      + apply eq_sym.
      + apply eq_trans.
      + intros x y z; apply mul_dist_add_left.
      + intros x y z; apply mul_dist_add_right.
      + intros x y; apply zp_sub_add_opp.
      + apply zp_mul_proper.
      + apply zp_sub_proper.
      + intros x y. apply zp_mul_comm.
      + intros x y; apply zp_mul_left_inv; exact y.
      + exact zero_neq_one.
      + intros x y. symmetry. subst. exact eq_refl. 
      + exact zp_div_proper.
    Qed.
    

  End ZpField.

End Zpfield.


Module Schnorr.

  
  (* Schnorr Group *)
  Section SchnorrGroup. 
    Context 
      {k p q : Z}
      {Hk : p = k * q + 1}
      {Hp : prime p}
      {Hq : prime q}.
  
    
    (* 
      The element v is kth residue, i.e., 
      ∃ w :  Z in Fp such that v = w ^ k mod p.
      If I compute v^q => w ^ (k * q) mod p = 
      w^(p - 1) mod p = 1.
    *) 
    Record Schnorr_group := 
      mk_schnorr 
      {v : Z; Ha : 0 < v < p; Hb : (v ^ q mod p = 1)}.


    Lemma comparison_dec : 
      ∀ x y : comparison, {x = y} + {x ≠ y}.
    Proof.
      intros x y.
      refine
        match x, y with 
        | Eq, Eq 
        | Lt, Lt 
        | Gt, Gt => left eq_refl
        | _, _ => right _ 
        end.
        all: try (intro Hf; congruence).
    Defined.

    Lemma uniqueness_of_schnorr_proof_first : 
      forall v (Hx Hy : 0 < v < p),  
      Hx = Hy.
    Proof.
      intros v [Hxa Hxb] [Hya Hyb];
      f_equal;
      apply UIP_dec,
      comparison_dec.
    Qed.

    Lemma uniqueness_of_schnorr_proof_second : 
      forall v (Hx Hy : v ^ q mod p = 1),  
      Hx = Hy.
    Proof.
      intros v Hx Hy;
      f_equal;
      apply UIP_dec, Z.eq_dec.
    Qed.

    Lemma construct_schnorr_group : 
      forall x y
      (Hxa : (0 < x < p))
      (Hxb : (x ^ q mod p = 1))
      (Hya : (0 < y < p))
      (Hyb : (y ^ q mod p = 1)),
      x = y -> 
      mk_schnorr x Hxa Hxb = mk_schnorr y Hya Hyb.
    Proof.
      intros; subst; f_equal.
      apply uniqueness_of_schnorr_proof_first.
      apply uniqueness_of_schnorr_proof_second.
    Qed. 

    Lemma dec_zpstar : 
      forall x y : Schnorr_group, 
      {x = y} + {x <> y}.
    Proof.
      intros [x Hxa Hxb] [y Hya Hyb].
      destruct (Z.eq_dec x y) as [Hl | Hr].
      + left; subst. 
        apply construct_schnorr_group;
        reflexivity.
      + right; subst.
        intros Hf.
        inversion Hf as (Hft).
        congruence.
    Qed.


    Lemma one_mod_p : 0 < 1 < p.
    Proof.
      pose proof @Hp_2_p p Hp as Ha.
      nia.
    Qed.  

    Lemma one_pow_mod_q : 1 ^ q mod p = 1.
    Proof.
      pose proof @Hp_2_p p Hp as Ha.
      pose proof @Hp_2_p q Hq as Hb.
      rewrite Z.pow_1_l, 
      Z.mod_1_l.
      + exact eq_refl.
      + abstract nia.
      + abstract nia. 
    Qed. 



    (* Neutral Element *)
    Definition one : Schnorr_group.
      refine 
        (mk_schnorr 1 one_mod_p one_pow_mod_q).
    Defined. 

    
    (* multiplication *)
    Definition mul_schnorr_group 
      (u v : Schnorr_group) : Schnorr_group.
      refine(
        match u, v with 
        | mk_schnorr au Hua Hub, 
          mk_schnorr av Hva Hvb => 
            mk_schnorr (Z.modulo (au * av) p) 
            (@multiplication_bound p Hp au av Hua Hva)  _
        end).
        (* everything good upto this point*)
        + pose proof @Hp_2_p p Hp.
          pose proof @Hp_2_p q Hq.
          rewrite <-Zpower_mod,
          Zmult_power,
          Zmult_mod, Hub, Hvb,
          Z.mod_1_l;
          try reflexivity.
        all: try (abstract nia).
    Defined.
    

    Lemma inv_schnorr_group_subproof_first : 
      forall au, 
      0 < au < p ->
      0 < 
        Z.of_N 
        (Npow_mod 
          (Z.to_N au) 
          (Z.to_N (p - 2)) 
          (Z.to_N p)) < p.
    Proof.
      intros ? Ha.
      rewrite zmod_nmod, 
      !Z2N.id.
      apply fermat_bound.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.


    Lemma inv_schnorr_group_subproof_second : 
      forall au, 
      0 < au < p ->
      au ^ q mod p = 1 ->
      Z.of_N 
      (Npow_mod 
        (Z.to_N au) 
        (Z.to_N (p - 2)) 
        (Z.to_N p)) ^ q mod p = 1.
    Proof.
      intros ? Hu Hv.
      pose proof @Hp_2_p p Hp as Ha.
      pose proof @Hp_2_p q Hq as Hb.
      rewrite zmod_nmod,
      Zpow_mod_correct,
      !Z2N.id,
      <-Zpower_mod,
      <-Z.pow_mul_r,
      Z.mul_comm,
      Z.pow_mul_r,
      Zpower_mod,
      Hv, Z.pow_1_l,
      Z.mod_1_l;
      try reflexivity.
      all: try (abstract nia). 
      rewrite !Z2N.id.
      exact Hp.
      abstract nia.
    Qed.


    

    (* u ^ (p - 2) is inverse of u *)
    Definition inv_schnorr_group (u : Schnorr_group) : Schnorr_group.
      refine(
        match u with 
        | mk_schnorr au Hu Hv => mk_schnorr
            (Z.of_N (Npow_mod (Z.to_N au) (Z.to_N (p - 2)) (Z.to_N p)))
            (@inv_schnorr_group_subproof_first au Hu)
            (inv_schnorr_group_subproof_second au Hu Hv)
        end).
    Defined.
      

    
    
    (* Now I need to establish that it's a group *)

    Lemma schnorr_mul_associative : 
      forall x y z : Schnorr_group,
      mul_schnorr_group x (mul_schnorr_group y z) =  
      mul_schnorr_group (mul_schnorr_group x y) z.
    Proof.
      pose proof @H_0_p p Hp.
      intros ? ? ?; 
      destruct x as [x Hxa Hxb]; 
      destruct y as [y Hya Hyb]; 
      destruct z as [z Hza Hzb].
      refine (construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_mod_idemp_l,
      Z.mul_mod_idemp_r,
      Z.mul_assoc. 
      reflexivity.
      all:nia.
    Qed.

    Lemma one_is_left_identity : 
      forall x, mul_schnorr_group one x = x.
    Proof.
      intros [x Hxa Hxb].
      unfold mul_schnorr_group, one.
      refine (construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_1_l.
      apply mod_not_zero_one.
      exact Hxa.
    Qed.

    Lemma one_is_right_identity : 
      forall x, mul_schnorr_group x one = x.
    Proof.
      intros [x Hxa Hxb]. 
      unfold mul_schnorr_group, one. 
      refine(construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_1_r. 
      apply mod_not_zero_one. 
      exact Hxa.
    Qed.

  
    Lemma schnorr_mul_commutative : 
      forall x y : Schnorr_group,
      mul_schnorr_group x y =  mul_schnorr_group y x.
    Proof.
      destruct x as [x Hx]; 
      destruct y as [y Hy].
      refine(construct_schnorr_group _ _ _ _ _ _ _).
      rewrite Z.mul_comm.
      reflexivity.
    Qed.

    Global Instance schnorr_mul_proper : 
      Proper (eq ==> eq ==> eq) mul_schnorr_group.
    Proof.
      intros x y Hxy z u Hzu.
      destruct x as [x Hx]; destruct y as [y Hy];
      destruct z as [z Hz]; destruct u as [u Hu].
      refine(construct_schnorr_group _ _ _ _ _ _ _).
      inversion Hxy; inversion Hzu; subst; reflexivity.
    Defined. 

    Lemma schnorr_left_inv :
      forall x, mul_schnorr_group (inv_schnorr_group x) x = one.
    Proof.
      intros [x Hxa Hxb].
      unfold mul_schnorr_group, 
      inv_schnorr_group, one.
      apply construct_schnorr_group.
      rewrite Z.mul_comm.
      rewrite zmod_nmod, Zpow_mod_correct.
      rewrite !Z2N.id.
      rewrite Zmult_mod_idemp_r.
      pose proof @Hp_2_p p Hp.
      assert (Hpp : p - 1 = 1 + (p - 2)).
      nia. 
      assert (Ht : x * x ^ (p - 2) = x ^ (p - 1)).
      rewrite Hpp. 
      rewrite Z.pow_add_r. 
      all:try nia.
      rewrite Ht.
      rewrite <- Zpow_mod_correct.
      apply fermat_little_ZZ.
      exact Hp. 
      exact Hxa.
      nia. 
      rewrite Z2N.id.
      exact Hp.
      nia.
    Qed.

    
    Lemma schnorr_right_inv :
      forall x, mul_schnorr_group x (inv_schnorr_group x) = one.
    Proof.
      intros ?.
      rewrite schnorr_mul_commutative.
      apply schnorr_left_inv.
    Qed.


    (* Schnorr is a commutative Group *)
    Global Instance schnorr_comm : @commutative_group 
      Schnorr_group (@eq Schnorr_group) 
      mul_schnorr_group one inv_schnorr_group.
    Proof.
      repeat econstructor.
      + unfold is_associative; 
        intros ? ? ?.
        apply schnorr_mul_associative.
      + intro x. apply one_is_left_identity.
      + intro x. apply one_is_right_identity.
      + apply schnorr_mul_proper.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y z Hxy Hyz. rewrite Hxy. exact Hyz.
      + intro x. apply schnorr_left_inv.
      + intro x. apply schnorr_right_inv.
      + intros x y Hxy. rewrite Hxy. reflexivity.
      + intros x y. apply schnorr_mul_commutative.
    Qed. 


  End SchnorrGroup.
End Schnorr.


Module Vspace.

  Section VectorSpace.


    Context 
      {k p q : Z}
      {Hk : p = k * q + 1}
      {Hp : prime p}
      {Hq : prime q}.

    (* computes g ^ x 
      Scalar multiplication of vector space 
      p is the Group modulus 
      q is the Field modulus
    *)
    Lemma pow_subproof_first : 
      forall au yt, 
      0 < au < p ->
      yt mod q = yt ->
      0 < 
        Z.of_N 
        (Npow_mod 
          (Z.to_N au) 
          (Z.to_N yt) 
          (Z.to_N p)) < p.
    Proof.
      intros ? ? Ha Hb.
      eapply mod_more_gen_bound in Hb.
      rewrite zmod_nmod, 
      !Z2N.id.
      apply fermat_bound_gen.
      exact Hp.
      all:try nia.
      rewrite Z2N.id.
      exact Hp.
      nia.
      Unshelve.
      exact Hq.
    Qed.


    Lemma pow_subproof_second : 
      forall au yt,
      yt mod q = yt ->   
      0 < au < p ->
      au ^ q mod p = 1 ->
      Z.of_N 
      (Npow_mod 
        (Z.to_N au) 
        (Z.to_N yt) 
        (Z.to_N p)) ^ q mod p = 1.
    Proof.
      intros ? ? Ht Hu Hv.
      eapply mod_more_gen_bound in Ht.
      pose proof @Hp_2_p p Hp as Ha.
      pose proof @Hp_2_p q Hq as Hb.
      rewrite zmod_nmod,
      Zpow_mod_correct,
      !Z2N.id,
      <-Zpower_mod,
      <-Z.pow_mul_r,
      Z.mul_comm,
      Z.pow_mul_r,
      Zpower_mod,
      Hv, Z.pow_1_l,
      Z.mod_1_l;
      try reflexivity.
      all: try (abstract nia). 
      rewrite !Z2N.id.
      exact Hp.
      abstract nia.
      Unshelve.
      exact Hq.
    Qed.



    Definition pow (g : @Schnorr.Schnorr_group p q) 
      (y : @Zpfield.Zp q) : @Schnorr.Schnorr_group p q.
      refine 
        match g, y with 
        | Schnorr.mk_schnorr gt Hgta Hgtb, Zpfield.mk_zp yt Hyt => 
            Schnorr.mk_schnorr  
                (Z.of_N (Npow_mod (Z.to_N gt) (Z.to_N yt) (Z.to_N p))) 
                (pow_subproof_first gt yt Hgta Hyt)
                (pow_subproof_second _ _  Hyt Hgta Hgtb)
        end.
    Defined.

    
  


    Lemma is_field_one_proof : 
      forall (u : @Schnorr.Schnorr_group p q), 
      pow u (@Zpfield.one q Hq) = u.
    Proof.
      intros [u Hu].
      unfold Zpfield.one, pow.
      apply Schnorr.construct_schnorr_group.
      cbn.
      rewrite <-!Z2N.inj_mod,
      Z2N.id.
      apply (@mod_more_gen_bound p Hp u);
      try assumption.
      all:try nia. 
      assert (Hut : 0 <= u). nia.
      pose proof Z.mod_bound_pos u p Hut (@H_0_p p Hp).
      nia. 
    Qed.




    Lemma is_field_zero_proof : 
      forall (u : @Schnorr.Schnorr_group p q), 
      pow u (@Zpfield.zero q Hq) = @Schnorr.one p q Hp Hq.
    Proof.
      intros [u Hu].
      apply Schnorr.construct_schnorr_group;
      cbn.
      exact eq_refl.
    Qed.

   



    (* g ^ (x₁ * x₂) = (g^x₁)^x₂ *)
    Lemma is_smul_associative_fmul_proof : 
      forall 
      (g : @Schnorr.Schnorr_group p q) 
      (u v : @Zpfield.Zp q),
      pow g (Zpfield.zp_mul u v) = pow (pow g u) v.
    Proof.
      intros [g Hg] [u Hu] [v Hv].
      apply Schnorr.construct_schnorr_group.
      rewrite !zmod_nmod, 
      !Z2N.id, !Zpow_mod_correct,
      <-Zpower_mod,
      <-Z.pow_mul_r.
      eapply mod_more_gen_bound in Hu, Hv.
      assert (Htt : 0 <= u * v) by nia.
      destruct (@mod_exists_pos q Hq (u * v) Htt) as 
      [k₁ [w₁ [Hl [Hr Hw]]]].
      rewrite Hl.
      eapply mod_more_gen_bound in Hr.
      replace (k₁ * q + w₁) with 
      (w₁ + k₁ * q). 
      rewrite Z_mod_plus_full, 
      Hr,
      Z.pow_add_r,
      Zmult_mod.
      replace (k₁ * q) with (q * k₁).
      rewrite Z.pow_mul_r.
      assert (Hvt : (g ^ q) ^ k₁ mod p = 
        (g ^ q mod p) ^ k₁ mod p).
      rewrite Zpower_mod;
      try reflexivity.
      nia. 
      rewrite Hvt, Hb.
      rewrite Z.pow_1_l,
      Z.mod_1_l,
      Z.mul_1_r, 
      Zmod_mod;
      try reflexivity.
      all: try nia.
      eapply mod_more_gen_bound in Hr;
      try nia.
      try (eapply mod_more_gen_bound in Hu;
      try nia). 
      all : (eapply mod_more_gen_bound in Hv;
      try nia).
      eapply mod_more_gen_bound in Hu;
      try nia.
      rewrite Z2N.id.
      eapply mod_more_gen_bound in Hu.
      destruct Hu as [Hul Hur].
      pose proof fermat_bound_gen 
        g u p Hp Hul Hg. 
      nia. 
      eapply mod_more_gen_bound in Hu;
      try nia.
      eapply Z_mod_nonneg_nonneg;
      try nia.
      eapply mod_more_gen_bound in Hu.
      try nia.
      all: rewrite Z2N.id;
        try nia; exact Hp.
      Unshelve.
      all: try (exact Hp); try (exact Hq).
    Qed.




    (* g ^ (u + v) = g^u . g^v *)
    Lemma is_smul_distributive_fadd_proof : 
      forall 
      (g : @Schnorr.Schnorr_group p q) 
      (u v : @Zpfield.Zp q),
      pow g (Zpfield.zp_add u v) =
      @Schnorr.mul_schnorr_group p q Hp Hq (pow g u) (pow g v).
    Proof.
      intros [g Hg] [u Hu] [v Hv].
      apply Schnorr.construct_schnorr_group.
      rewrite !zmod_nmod, 
      !Z2N.id, !Zpow_mod_correct,
      <-Zmult_mod,
      <-Z.pow_add_r.
      eapply mod_more_gen_bound in Hu, Hv.
      assert (Htt : 0 <= u +  v) by nia.
      destruct (@mod_exists_pos q Hq (u +  v) Htt) as 
      [k₁ [w₁ [Hl [Hr Hw]]]].
      rewrite Hl.
      eapply mod_more_gen_bound in Hr.
      replace (k₁ * q + w₁) with 
      (w₁ + k₁ * q). 
      rewrite Z_mod_plus_full, 
      Hr,
      Z.pow_add_r,
      Zmult_mod.
      replace (k₁ * q) with (q * k₁).
      rewrite Z.pow_mul_r.
      assert (Hvt : (g ^ q) ^ k₁ mod p = 
        (g ^ q mod p) ^ k₁ mod p).
      rewrite Zpower_mod;
      try reflexivity.
      nia. 
      rewrite Hvt, Hb.
      rewrite Z.pow_1_l,
      Z.mod_1_l,
      Z.mul_1_r, 
      Zmod_mod;
      try reflexivity.
      all: try nia.
      eapply mod_more_gen_bound in Hr;
      try nia.
      try (eapply mod_more_gen_bound in Hu;
      try nia). 
      all : (eapply mod_more_gen_bound in Hv;
      try nia).
      eapply mod_more_gen_bound in Hu;
      try nia.
      all: eapply mod_more_gen_bound in Hu, Hv; try nia.
      all: try rewrite Z2N.id;
        try nia; try (exact Hp).
      eapply mod_more_gen_bound in Hu, Hv;
      eapply Z_mod_nonneg_nonneg;
      try nia. 
      eapply mod_more_gen_bound in Hu.
      nia. 
      Unshelve.
      all: try (exact Hp); try (exact Hq).
    Qed.




    (* pow (u * v ) r = pow u r *G pow v r *)
    Lemma is_smul_distributive_vadd_proof : 
      forall 
      (u v : @Schnorr.Schnorr_group p q)
      (r : @Zpfield.Zp q),
      pow (@Schnorr.mul_schnorr_group p q Hp Hq u v) r = 
      @Schnorr.mul_schnorr_group p q Hp Hq (pow u r) (pow v r).
    Proof.
      intros [u Hua Hub] [v Hva Hvb] [r Hr].
      apply Schnorr.construct_schnorr_group.
      rewrite !zmod_nmod, 
      !Z2N.id, !Zpow_mod_correct,
      <-Zpower_mod,
      Z.pow_mul_l,
      Zmult_mod;
      try reflexivity.
      all: try nia. 
      eapply mod_more_gen_bound in Hr.
      try nia.
      pose proof @multiplication_bound p Hp u v Hua Hva.
      try nia.
      all: rewrite Z2N.id;
      [exact Hp | nia].
      Unshelve.
      exact Hq.
    Qed.
    


    (* Proof that it's Vector Space *)

    Global Instance pow_vspace : 
      @vector_space 
        (* Field *)
        (@Zpfield.Zp q) 
        (@eq (@Zpfield.Zp q))
        (@Zpfield.zero q Hq) 
        (@Zpfield.one q Hq)
        (@Zpfield.zp_add q)
        (@Zpfield.zp_mul q)
        (@Zpfield.zp_sub q)
        (@Zpfield.zp_div q)
        (@Zpfield.zp_opp q Hq)
        (@Zpfield.zp_inv q)
        (* Vector *)
        (@Schnorr.Schnorr_group p q)
        (@eq (@Schnorr.Schnorr_group p q))
        (@Schnorr.one p q Hp Hq)
        (@Schnorr.inv_schnorr_group k p q Hk Hp Hq)
        (@Schnorr.mul_schnorr_group p q Hp Hq)
        pow.
    Proof.
      econstructor.
      + apply Schnorr.schnorr_comm.
      + apply Zpfield.zp_field.
      + intros ?; apply is_field_one_proof.
      + intros ?; apply is_field_zero_proof.
      + intros ? ? ?;
        apply is_smul_associative_fmul_proof.
      + intros ? ? ?;
        apply is_smul_distributive_fadd_proof.
      + intros ? ? ?;
        apply is_smul_distributive_vadd_proof.
      + intros x y Heq u v Huv.
        subst. reflexivity.  
    Qed.



  End VectorSpace.


End Vspace.