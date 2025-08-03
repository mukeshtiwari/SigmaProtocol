From Stdlib Require Import 
  Vector Fin Bool Utf8
  Psatz BinIntDef.

Import VectorNotations EqNotations. 


Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.


Section Dec.

  Context 
    {R : Type}
    {Hdec : forall x y : R, {x = y} + {x <> y}}.

  Lemma dec_true : forall x y, 
    (if Hdec x y then true else false) = true <-> x = y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split; 
    intro H; auto.
    inversion H.
  Qed.


  Lemma dec_false : forall x y, 
    (if Hdec x y then true else false) = false <-> x <> y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split; 
    intro H; auto.
    inversion H.
    congruence.
  Qed.

  Lemma dec_eq_true : forall x, 
    (if Hdec x x then true else false) = true.
  Proof.
    intros ?.
    destruct (Hdec x x).
    reflexivity.
    congruence.
  Qed.

   
  Definition eq_bool (x y : R) : bool :=
    match Hdec x y with 
    | left _ => true 
    | right _ => false
    end.


End Dec.


Section Vect.


  Context 
    {R : Type}
    {Hdec : forall x y : R, {x = y} + {x <> y}}.


  Lemma vector_inv_0 (v : Vector.t R 0) :
    v = @Vector.nil R.
  Proof.
    refine 
      (match v as v' in Vector.t _ n' return 
        (match n' return Vector.t R n' -> Type 
        with 
        | 0 => fun (ve : Vector.t R 0) => ve = []
        | _ => fun _ => IDProp 
        end v')
      with
      | @Vector.nil _ => eq_refl
      end).
  Defined.


  Lemma vector_inv_S : 
      forall {n : nat} (v : Vector.t R (S n)), {h & {t & v = h :: t}}.
  Proof.
    intros n v.
    refine 
      (match v as v' in Vector.t _ n' return
        (match n' return Vector.t R n' -> Type  
        with 
        | 0 => fun _ => IDProp
        | S n'' => fun (ea : Vector.t R (S n'')) => 
          {h : R & {t : Vector.t R n'' & ea = h :: t}}
        end v')
      with
      | cons _ h _ t => existT _ h (existT _ t eq_refl)
      end).
  Defined.


  Lemma fin_inv_0 (i : Fin.t 0) : False.
  Proof. refine (match i with end). Defined.

  Lemma fin_inv_S (n : nat) (i : Fin.t (S n)) :
    (i = Fin.F1) + {i' | i = Fin.FS i'}.
  Proof.
    refine (match i with
            | Fin.F1 => _
            | Fin.FS _ => _
            end); eauto.
  Defined.


  Definition vector_to_finite_fun : 
    forall n, Vector.t R n -> (Fin.t n -> R).
  Proof.
    induction n.
    + intros v f.
      apply fin_inv_0 in f.
      refine (match f with end).
    + intros v f.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      destruct (fin_inv_S _ f) as [h | [t p]].
      exact vhd.
      exact (IHn vtl t).
  Defined.


  Definition finite_fun_to_vector : 
    forall n,  (Fin.t n -> R) -> Vector.t R n.
  Proof.
    induction n.
    + intros f.
      apply Vector.nil.
    + intros f.
      apply Vector.cons.
      apply f, Fin.F1.
      apply IHn;
      intro m.
      apply f, Fin.FS, m.
  Defined.


  Lemma finite_fun_to_vector_correctness 
    (m : nat) (f : Fin.t m -> R) (i : Fin.t m) :
    Vector.nth (finite_fun_to_vector _ f) i = f i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S _ i as [-> | (i' & ->)].
      + reflexivity.
      + cbn. 
        now rewrite IHm.
  Defined.


  Lemma vector_to_finite_fun_correctness 
    (m : nat) (v : Vector.t R m) (i : Fin.t m) :
    Vector.nth v i = (vector_to_finite_fun _ v) i.
  Proof.
    induction m.
    - inversion i.
    - pose proof fin_inv_S _ i as [-> | (i' & ->)].
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp.
      reflexivity.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      rewrite vp;
      simpl; 
      now rewrite IHm.
  Defined.

  Lemma vector_finite_back_forth : 
    forall (n : nat) (v : Vector.t R n),
    v = finite_fun_to_vector _ (vector_to_finite_fun _ v).
  Proof.
    induction n.
    + intros v.
      pose proof (vector_inv_0 v) as Hv.
      subst; 
      reflexivity.
    + intros v.
      destruct (vector_inv_S v) as (vhd & vtl & vp).
      subst; simpl; f_equal.
      apply IHn.
  Defined.
        

  (* It combines two vectors pointwise using the function (f : R -> T -> U) *)
  Definition zip_with {P T U : Type} : 
    forall {n : nat}, (P -> T -> U) ->  
    Vector.t P n -> Vector.t T n -> Vector.t U n.
  Proof.
    refine(
      fix zip_with n f u {struct u} :=
      match u as u' in Vector.t _ n'  
        return
          forall (pf : n' = n), 
            u = eq_rect n' _ u' n pf -> 
            Vector.t T n' -> Vector.t U n'  
      with 
      | nil _ => 
          fun pf H v => @nil _ 
      | cons _ hu m tu => 
          fun pf H v => 
          match v as v' in Vector.t _ (S m')
            return 
              forall (pf : m' = m),
                v = eq_rect m' (fun w => Vector.t T (S w)) v' m pf ->
                Vector.t U (S m') 
          with 
          | nil _ => idProp
          | cons _ hv n tv => 
              fun pfv Hv => 
                cons _ 
                  (f hu hv) _ 
                  _ 
          end eq_refl eq_refl 
      end eq_refl eq_refl
    ).
    subst.
    exact (zip_with _ f tu tv).
  Defined.
  
 
  Fixpoint repeat_ntimes (n : nat) (w : R) : Vector.t R n :=
    match n as n' return Vector.t R n' with
    | 0 => []
    | S n' => w :: repeat_ntimes n' w 
    end.


  Definition take : forall (n : nat) {m : nat}, 
    Vector.t R (n + m) -> Vector.t R n.
  Proof.
    refine(
      fix Fn n {struct n} :=
      match n with 
      | 0 => fun _ _ => []
      | S n' => fun _ v => _
      end).
    cbn in v.
    destruct (vector_inv_S v) as (vh & vtl & _).
    exact (vh :: Fn _ _ vtl).
  Defined.


  Definition drop : forall (n : nat) {m : nat}, 
    Vector.t R (n + m) -> Vector.t R m.
  Proof.
    refine(
      fix Fn n {struct n} :=
      match n with 
      | 0 => fun _ v => v
      | S n' => fun _ v => _
      end).
    cbn in v.
    destruct (vector_inv_S v) as (_ & vtl & _).
    exact (Fn _ _ vtl).
  Defined.
    
  
  Definition flatten_pair {U : Type} {n : nat} :
    Vector.t (U * U) n ->  Vector.t U (n + n).
  Proof.
    revert n.
    refine(fix Fn n v {struct v} := 
      match v as v' in Vector.t _ n' 
      return _  
      with 
      | [] =>  _
      | (vhl, vhr) :: vtl => _ 
      end).
      +
        exact [].
      +
        assert (Hc : S n0 + S n0 = S (S (n0 + n0))). 
        abstract nia. rewrite Hc.
        exact (vhl :: vhr :: Fn _ vtl).
  Defined.

  
  
  (* Two challenge vectors are same pointwise *)
  Definition two_challenge_vectors_same_everyelem {n : nat} :
    Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∀ (f : Fin.t n),
    nth u f = nth v f.
  
  (* Two challenge vectors differs at atleast one point *)
  Definition two_challenge_vectors_disjoint_someelem {n : nat} :
     Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∃ (f : Fin.t n),
    nth u f <> nth v f.
    
  (* Two challenge vectors are different pointwise *)
  Definition two_challenge_vectors_different_everyelem {n : nat} :
    Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∀ (f : Fin.t n),
    nth u f <> nth v f.
  
  (* Two challenge vectors same at some point *)
  Definition two_challenge_vectors_same_someelem {n : nat} :
     Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∃ (f : Fin.t n),
    nth u f = nth v f.

  
  Lemma vector_not_equal_implies_disjoint_someelem : 
    forall (n : nat) (c d : Vector.t R n), 
    c <> d -> two_challenge_vectors_disjoint_someelem c d.
  Proof.
    induction n as [| n IHn].
    +
      intros * Ha.
      rewrite (vector_inv_0 c),
      (vector_inv_0 d) in Ha.
      pose proof (Ha eq_refl) as Hf.
      congruence.
    +
      intros * Ha.
      destruct (vector_inv_S c) as (hc & tc & Hb).
      destruct (vector_inv_S d) as (hd & td & Hc).
      rewrite Hb, Hc in Ha.
      unfold two_challenge_vectors_disjoint_someelem.
      destruct (Hdec hc hd) as [Hd | Hd].
      rewrite Hd in Ha.
      assert (He : tc <> td).
      intro Hf; eapply Ha; 
      rewrite Hf; reflexivity.
      destruct (IHn _ _ He) as (f & Hf).
      exists (Fin.FS f);
      rewrite Hb, Hc;
      cbn; exact Hf.
      exists (Fin.F1); 
      rewrite Hb, Hc; 
      cbn; exact Hd.
  Qed.


  Lemma vector_same_implies_same_everyelem : 
    forall (n : nat) (c d : Vector.t R n), 
    c = d -> 
    two_challenge_vectors_same_everyelem c d.
  Proof.
    induction n as [|n IHn].
    +
      intros * Ha Hb.
      destruct (fin_inv_0 Hb).
    +
      intros * Ha Hb.
      destruct (vector_inv_S c) as (hc & tc & Hc).
      destruct (vector_inv_S d) as (hd & td & Hd).
      rewrite Hc, Hd in Ha |- *.
      destruct (fin_inv_S _ Hb) as [hf | (hf & He)].
      ++
        rewrite hf; cbn.
        inversion Ha; 
        reflexivity.
      ++
        rewrite He; cbn.
        eapply IHn.
        inversion Ha.
        eapply Eqdep_dec.inj_pair2_eq_dec in H1.
        exact H1.
        eapply PeanoNat.Nat.eq_dec.
  Qed.  

  Theorem take_drop_inv : ∀ (n m : nat) (v : Vector.t R (n + m)),
    v = take n v ++ drop n v.
  Proof.
    induction n as [|n ihn].
    +
      cbn; intros *.
      reflexivity.
    +
      cbn; intros *.
      destruct (vector_inv_S v) as (vh & vt & ha).
      cbn. rewrite ha. f_equal.
      erewrite <-ihn.
      reflexivity.
  Qed.

  Theorem rew_eq_refl : ∀ (n m : nat) (v₁ : Vector.t R n)
    (v₂ : Vector.t R m) (vh : R) (pf : n = m), 
    v₁ = rew <-pf in v₂ -> 
    vh :: v₁ = rew <- [Vector.t R] f_equal S pf in (vh :: v₂).
  Proof.
    intros * ha.
    subst; cbn; reflexivity.
  Qed.
  
  Theorem vector_fin_app : ∀ (n : nat) (f : Fin.t n) (v : Vector.t R n),
     existsT (m₁ m₂ : nat) (v₁ : Vector.t R m₁) (vm : R) 
      (v₂ : Vector.t R m₂)
      (pf : n = m₁ + (1 + m₂)), 
      v = rew  <- [Vector.t R] pf in (v₁ ++ [vm] ++ v₂) ∧
      vm = Vector.nth v f ∧
      m₁ = proj1_sig  (Fin.to_nat f).
  Proof.
    induction n as [|n ihn].
    +
      intros *.
      refine match f with end.
    +
      intros *.
      destruct (fin_inv_S _ f) as [f' | (f' & ha)].
      ++
        subst; cbn.
        destruct (vector_inv_S v) as (vh & vt & hb).
        exists 0, n, [], vh, vt, eq_refl. 
        subst; cbn.
        repeat split; reflexivity.
      ++
        (* inductive case *)
        destruct (vector_inv_S v) as (vh & vt & hb).
        subst; cbn.
        destruct (ihn f' vt) as (m₁ & m₂ & v₁ & vm & v₂ & pf & ha & hb & hc).
        exists (S m₁), m₂, (vh :: v₁), vm, v₂, (f_equal S pf).
        cbn; split.
        eapply rew_eq_refl; exact ha.
        split. 
        exact hb.
        destruct (to_nat f') as (u & hu).
        cbn in hc |- *.
        subst. reflexivity.
  Defined.

  Theorem vector_fin_app_pred : ∀ (n : nat) (f : Fin.t (1 + n)) 
    (va : Vector.t R (1 + n)) (vb : Vector.t R n),
    existsT (m₁ m₂ : nat) (v₁ v₃ : Vector.t R m₁) (vm : R) 
      (v₂ v₄ : Vector.t R m₂)
      (pfa : 1 + n = (m₁ + (1 + m₂))) (pfb : n = m₁ + m₂), 
      va = rew  <- [Vector.t R] pfa in ((v₁ ++ [vm] ++ v₂)) ∧
      vm = Vector.nth va f ∧ 
      vb = rew  <- [Vector.t R] pfb in ((v₃ ++ v₄)) ∧
       m₁ = proj1_sig  (Fin.to_nat f).
  Proof.
    intros *.
    destruct (vector_fin_app _ f va) as 
    (m₁ & m₂ & v₁ & vm & v₂ & pf & ha & hb).
    assert (hc : n = m₁ + m₂) by nia. subst.
    exists m₁, m₂, v₁, (take m₁ vb), 
    vm, v₂, (drop m₁ vb), pf, eq_refl.
    subst; cbn in * |- *.
    split. reflexivity.
    destruct hb as (hb & hc).
    split. exact hb.
    split. 
    eapply take_drop_inv.
    destruct (to_nat f) as (u & hu).
    cbn in hc |- *.
    subst. reflexivity.
  Defined.


  Lemma fin_to_nat : ∀ (m n : nat) (rindex : Fin.t (m + S n)), 
    m = proj1_sig (Fin.to_nat rindex) ->
    rindex = Fin.R m (Fin.F1 : Fin.t (S n)).
  Proof.
    intros * ha.
    eapply Fin.to_nat_inj.
    rewrite Fin.R_sanity. 
    cbn. rewrite <-ha. nia.
  Qed.
  
  (* Write Ltac *)

End Vect. 

From Stdlib Require Import List.
Section ListUtil.

 
  Import ListNotations.
  Theorem map_ext_eq : 
    forall {A B : Type} (f : A -> bool) 
    (la lb : list (A * B)) (z : B),
    List.length la = List.length lb ->
    (forall x y, List.In (x, y) la -> f x = true ∧ y = z) ->
    (forall x y, List.In (x, y) lb -> f x = true ∧ y = z) ->
    List.map (fun '(a, p) => (f a, p)) la = 
    List.map (fun '(a, p) => (f a, p)) lb.
  Proof.
    intros ? ? ?. 
    induction la as [| (a, p) la IHla];
    intros lb z Ha Hb Hc.
    +
     assert(Hd : lb = []) by (destruct lb; auto; inversion Ha).
     subst; reflexivity.
    +
      destruct lb as [| (b, q) lb]; 
      simpl in * |- *. 
      ++ congruence. 
      ++
         assert (Hd : f a = true ∧ p = z) by (apply Hb; auto).
         assert (He : f b = true ∧ q = z) by (apply Hc; auto).
         destruct Hd as [Hd1 Hd2];
         destruct He as [He1 He2].
         f_equal. 
         +++ rewrite Hd1, He1; subst; reflexivity.
         +++ eapply IHla; auto.
  Qed. 

End ListUtil.

From Stdlib Require Import PArith.PArith 
  ZArith.ZArith Lia
  ZArith.Znumtheory
  Arith 
  Zpow_facts.

Section Modutil.

  Context 
      {p : Z}
      {Hp : prime p}.

  
  Fact Hp_2_p : 2 <= p.
  Proof.
    pose proof (prime_ge_2 p Hp) as Ht.
    nia.
  Qed.

  Fact H_0_p : 0 < p.
  Proof.
    pose proof (prime_ge_2 p Hp).
    nia.
  Qed.
  
  Fact Hp_1_p : 1 < p.
  Proof.
    pose proof (prime_ge_2 p Hp).
    nia.
  Qed.

  Lemma mod_eq_custom : 
    forall (a b : Z), 
    (0 < b)%Z -> 
    Z.modulo a b = (a - b * (a / b))%Z.
  Proof.
    intros a b Hb.
    rewrite Zmod_eq; nia.
  Qed. 


  Lemma mod_not_zero_one : 
    forall w,
    (0 < w < p)%Z -> Z.modulo w p = w.
  Proof.
    intros ? Hw.
    rewrite mod_eq_custom.
    assert (Hwp: (w/p = 0)%Z).
    apply Zdiv_small; nia.
    rewrite Hwp. nia. nia.
  Qed.

  Lemma mod_more_gen_bound : 
    forall w,
    (0 <= w < p)%Z <-> Z.modulo w p = w.
  Proof.
    intros ?. split; intro Hw.
    +
    rewrite mod_eq_custom.
    assert (Hwp: (w/p = 0)%Z).
    apply Zdiv_small; nia.
    rewrite Hwp. nia. nia.
    + rewrite <-Hw.
      apply Z_mod_lt.
      pose proof (Hp_2_p).
      nia. 
  Qed.


  Lemma mod_not_eq_zero : 
    forall m, 
    m mod p <> 0 <-> 
    exists k w, m = k * p + w /\ 1 <= w < p.
  Proof.
    intros ?; split; intros Hm.
    exists (Z.div m p), (Z.modulo m p). 
    split.
    rewrite mod_eq_custom. nia.
    apply H_0_p. 
    remember (m mod p) as mp.
    assert (Hpt : 0 <= mp < p)
      by (rewrite Heqmp; 
      apply Z.mod_pos_bound; apply H_0_p). 
    nia.
    destruct Hm as [k [w [Hk Hw]]].
    rewrite Hk, Z.add_comm, Z.mod_add.
    rewrite mod_eq_custom.
    assert (Hwp: w / p = 0). 
    apply Zdiv_small; nia.
    intro. rewrite Hwp in H. nia.
    apply H_0_p. pose Hp_2_p. nia.
  Qed.


  Lemma mod_exists: 
    forall m,
    exists k w, m = k * p + w /\ 0 <= w < p.
  Proof.
    intros ?.
    exists (Z.div m p), (Z.modulo m p). 
    split.
    rewrite mod_eq_custom. nia.
    apply H_0_p.
    apply Z.mod_pos_bound.
    apply H_0_p.
  Qed.


  Lemma mod_exists_pos : 
    forall m,
    0 <= m -> 
    exists k w, m = k * p + w /\ 0 <= w < p 
    /\ 0 <= k.
  Proof.
    intros ? Hm.
    exists (Z.div m p), (Z.modulo m p). 
    split.
    rewrite mod_eq_custom. nia.
    apply H_0_p.
    split.
    apply Z.mod_pos_bound.
    apply H_0_p.
    pose proof Hp_2_p as Hw.
    apply Z.div_pos;
    try nia.
  Qed.
 
  
  Lemma mod_not_zero : 
    forall w₁ w₂,  
    1 <= w₁ < p ->  
    1 <= w₂ < p -> 
    (w₁ * w₂) mod p <> 0.
  Proof.
    intros ? ? Hw₁ Hw₂.
    assert (Hwm: 1 <= w₁ * w₂ < p * p) by nia.
    pose proof Hp_2_p.
    pose proof (rel_prime_le_prime w₁ p Hp Hw₁) as Hwp1.
    pose proof (rel_prime_le_prime w₂ p Hp Hw₂) as Hwp2.
    apply rel_prime_sym in Hwp1; 
    apply rel_prime_sym in Hwp2.
    pose proof (rel_prime_mult _ _ _ Hwp1 Hwp2) as Hwpp.
    apply rel_prime_sym in Hwpp.
    apply Zrel_prime_neq_mod_0. 
    nia. exact Hwpp.
  Qed. 


  Lemma mod_single_not_zero : 
    forall w : Z,
    1 <= w < p ->
    w mod p <> 0.
  Proof.
    intros ? Hw.
    pose proof (rel_prime_le_prime w p Hp Hw) as Hwp.
    apply Zrel_prime_neq_mod_0.
    nia.
    exact Hwp.
  Qed.
      

  Lemma mod_not_zero_general: 
    forall vm vn, 
    vm mod p <> 0 -> 
    vn mod p <> 0 -> 
    ((vm * vn) mod p) mod p <> 0.
  Proof.
    intros ? ? Hvm Hvn. 
    apply mod_not_eq_zero in Hvm.
    apply mod_not_eq_zero in Hvn.
    apply mod_not_eq_zero.
    destruct Hvm as [k1 [w1 [Hk1 Hw1]]].
    destruct Hvn as [k2 [w2 [Hk2 Hw2]]].
    assert (Hvmn : (vn * vm) mod p = (w1 * w2) mod p).
    rewrite Hk1, Hk2. 
    rewrite Zmult_mod, Z.add_comm, 
    Z.mod_add, Z.add_comm, Z.mod_add.
    rewrite <-Zmult_mod, Z.mul_comm; 
    reflexivity.
    pose proof Hp_2_p. abstract nia.
    pose proof Hp_2_p. abstract nia.
    exists 0, ((w1 * w2) mod p).
    split. simpl. rewrite Z.mul_comm, Hvmn; 
    reflexivity.
    assert (Hwt: 0 <= (w1 * w2) mod p < p) by 
      apply (Z.mod_pos_bound (w1 * w2) p H_0_p).
    assert ((w1 * w2) mod p <> 0).
    pose proof (mod_not_zero w1 w2 Hw1 Hw2).
    exact H. abstract nia.
  Qed.

  (* moved the proof as a lemma to avoid blowing of proof terms *)
  Lemma znot_zero_mul_proof: 
    forall vx vy, 
    1 <= vx < p -> 
    1 <= vy < p -> 
    1 <= (vx * vy) mod p < p.
  Proof.
    intros ? ? Hvx Hvy.
    assert (Hwt: 0 <= (vx * vy) mod p < p) by 
    apply (Z.mod_pos_bound (vx * vy) p H_0_p).
    assert ((vx * vy) mod p <> 0).
    pose proof (@mod_not_zero vx vy Hvx Hvy).
    exact H.
    nia.
  Qed.

  Lemma multiplication_bound : 
    forall vx vy, 
    0 < vx < p -> 
    0 < vy < p -> 
    0 < (vx * vy) mod p < p.
  Proof.
    intros ? ? Ha Hb.
    assert (Hc : 1 <= vx < p) by
    nia.
    assert (Hd : 1 <= vy < p) by 
    nia.
    pose proof (znot_zero_mul_proof _ _ Hc Hd) as He.
    nia. 
  Qed.

  Lemma rewrite_gop {G : Type} (gop : G -> G -> G) : 
    forall a b c d : G, 
    a = b -> c = d -> gop a c = gop b d.
  Proof.
    intros * Hab Hcd;
    subst;
    reflexivity.
  Qed.

End Modutil. 

Section TransProofs. 

    (* begin proofs for computations *)
    (* Just to make sure  that my proofs are transparent *)
    Definition nat_succ_eq : 
      ∀ (n m : nat), S (Nat.add n (S m)) = Nat.add n (S (S m)).
    Proof.
      refine(fix Fn n {struct n} :=
        match n with 
        | 0%nat => fun m => eq_refl 
        | S n' => fun m => eq_ind_r 
          (fun w => S w = S (n' + S (S m))) eq_refl (Fn n' m)
        end).
    Defined.

    
    Definition nat_succ : 
      forall (m n : nat), ((m + (1 + n) = 1 + (m + n)))%nat.
    Proof.
      induction m as [|m Ihm];
      intro n.
      +
        cbn; reflexivity.
      +
        cbn; rewrite Ihm.
        reflexivity.
    Defined.

    Definition nat_succ_p : 
      forall (m n p : nat), (((m + (1 + n)) + p) = ((1 + (m + n)) + p))%nat.
    Proof.
      intros *.
      rewrite nat_succ.
      reflexivity.
    Qed.


        
    
    
    Definition nat_eq_succ : 
      ∀ (n m : nat), S (Nat.add n (S m)) = S (S (Nat.add n m)).
    Proof.
      refine(fix Fn n {struct n} :=
        match n with 
        | 0%nat => fun m => eq_refl 
        | S n' => fun m => @eq_ind_r _ _  
          (λ x : nat, S x = S (S (S (n' + m)))) eq_refl _ (Fn n' m)
        end).
    Defined.
  

    
    Theorem subst_vector {A : Type} : forall {n m : nat},
      Vector.t A n -> n = m -> Vector.t A m.
    Proof.
      intros * u Ha.
      exact (@eq_rect nat n (fun x => Vector.t A x) u m Ha).
    Defined.


  

    Lemma divmod_simplification : 
      forall (x y q u : nat),
      fst (Nat.divmod x y q u) = (q + fst (Nat.divmod x y 0 u))%nat.
    Proof.
      induction x;
      intros *; simpl;
      [ | destruct u; rewrite IHx;
      [erewrite IHx with (q := 1%nat) | erewrite IHx]];
      try nia.
    Defined.


    Lemma nat_divmod : 
      forall (n : nat),
      fst (Nat.divmod (n + S (S (n + S (S (n + n * S (S n)))))) 1 1 1) =
      (1 + S n + fst (Nat.divmod (n + S (n + n * S n)) 1 0 0))%nat.
    Proof.
      intros n.
      rewrite divmod_simplification;
      simpl; f_equal. 
      assert (Ha : (1 <= 1)%nat) by nia.
      pose proof PeanoNat.Nat.divmod_spec 
      (n + S (S (n + S (S (n + n * S (S n))))))%nat 1 0 1 Ha as Hb.
      destruct (PeanoNat.Nat.divmod 
        (n + S (S (n + S (S (n + n * S (S n)))))) 1 0 1) as 
      (qa & qb) eqn:Hc; simpl.
      assert (Hd : (0 <= 1)%nat) by nia. 
      pose proof PeanoNat.Nat.divmod_spec
      (n + S (n + n * S n)) 1 0 0 Hd as He. 
      destruct (Nat.divmod (n + S (n + n * S n)) 1 0 0) as 
      (qaa & qbb) eqn:Hf; simpl. 
      nia.
    Defined.
      
    (* end of proofs *)


  End TransProofs.