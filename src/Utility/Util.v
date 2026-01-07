From Stdlib Require Import 
  Vector Fin Bool Utf8
  Psatz BinIntDef Arith.

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
      forall {n : nat} (v : Vector.t R (S n)), 
      existsT h t, v = h :: t.
  Proof.
    intros n v.
    refine 
      (match v as v' in Vector.t _ n' return
        (match n' return Vector.t R n' -> Type  
        with 
        | 0 => fun _ => IDProp
        | S n'' => fun (ea : Vector.t R (S n'')) => 
            existsT (h : R) (t : Vector.t R n''), ea = h :: t 
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

  Theorem repeat_ntimes_correct : ∀ {n : nat}
    (i : Fin.t n) (w : R), (repeat_ntimes n w)[@i] = w. 
  Proof. 
    induction n as [|n ihn].
    + 
      intros i w.
      refine match i with end. 
    +
      intros *.
      cbn.
      destruct (fin_inv_S _ i) as [f | (f & ha)]; 
      subst; cbn;[reflexivity | eapply ihn; assumption].
  Qed.

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
  
  Record Box (P:Prop) : Type := { p : P }.
  Arguments p {_} _.
  
   Theorem vector_fin_app : ∀ (n : nat) (f : Fin.t n) (v : Vector.t R n),
     existsT (m₁ m₂ : nat) (v₁ : Vector.t R m₁) (vm : R) 
      (v₂ : Vector.t R m₂)
      (pf : Box (n = m₁ + (1 + m₂))), 
      Box (v = rew  <- [Vector.t R] (p pf) in (v₁ ++ [vm] ++ v₂) ∧
      vm = Vector.nth v f ∧
      m₁ = proj1_sig  (Fin.to_nat f)).
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
        exists 0, n, [], vh, vt, (Build_Box _ eq_refl). 
        subst; cbn.
        repeat split; reflexivity.
      ++
        (* inductive case *)
        destruct (vector_inv_S v) as (vh & vt & hb).
        subst; cbn.
        destruct (ihn f' vt) as (m₁ & m₂ & v₁ & vm & v₂ & pf & haa).
        destruct haa as [ha].
        destruct ha as (ha & hb & hc).
        exists (S m₁), m₂, (vh :: v₁), vm, v₂, (Build_Box _ (f_equal S (p pf))).
        cbn; split. split.
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
      (pfa : Box (1 + n = (m₁ + (1 + m₂)))) (pfb : Box (n = m₁ + m₂)),
      Box (va = rew  <- [Vector.t R] (p pfa) in ((v₁ ++ [vm] ++ v₂)) ∧
      vm = Vector.nth va f ∧
      vb = rew  <- [Vector.t R] (p pfb) in ((v₃ ++ v₄)) ∧
      m₁ = proj1_sig  (Fin.to_nat f)).
  Proof.
    intros *.
    destruct (vector_fin_app _ f va) as
    (m₁ & m₂ & v₁ & vm & v₂ & pff & haa).
    destruct pff as [pf].
    destruct haa as [ha].
    destruct ha as (ha & hb).
    assert (hc : n = m₁ + m₂) by nia. subst.
    exists m₁, m₂, v₁, (take m₁ vb),
    vm, v₂, (drop m₁ vb), (Build_Box _ pf), (Build_Box _ eq_refl).
    subst; cbn in * |- *.
    split. split. reflexivity.
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

 
  Definition vector_forallb {n : nat} (f : R -> bool) 
    (v : Vector.t R n) : bool :=
    Vector.fold_right (fun x acc => f x && acc) v true.

  Theorem vector_forallb_correct : 
    forall (n : nat) (f : R -> bool) (v : Vector.t R n),
    vector_forallb f v = true <->
    forall (i : Fin.t n), f (Vector.nth v i) = true.
  Proof.
    induction n as [| n ihn].
    +
      intros *.
      split. 
      ++
        intros ha i.
        refine match i with end.
      ++
        intros ha.
        pose proof (vector_inv_0 v) as hb.
        subst. reflexivity.
    +
      intros *.
      split.
      ++
        intros ha i.
        destruct (vector_inv_S v) as (vh & vt & hb).
        destruct (fin_inv_S _ i) as [i' | (i' & hc)].
        +++
          subst. cbn in ha |- *.
          apply andb_true_iff in ha.
          destruct ha as (ha & _).
          exact ha.
        +++
          subst. cbn in ha |- *.
          apply andb_true_iff in ha.
          destruct ha as (_ & ha).
          eapply ihn; exact ha.
      ++
        intros ha.
        destruct (vector_inv_S v) as (vh & vt & hb).
        subst. cbn in ha |- *.
        pose proof (ha Fin.F1) as hb.
        cbn in hb. rewrite hb.
        cbn. eapply ihn.
        intro i. specialize (ha (Fin.FS i)).
        cbn in ha. exact ha.
  Qed.
    
  (* Write Ltac *)

End Vect. 

Section Vecutil.
      (* small inversion is a life saviour*)
      Theorem vec_inv_head {n : nat} {A : Type} (a b : A) 
        (u v : Vector.t A n) (e : a :: u = b :: v) : a = b.
      Proof.
        refine 
          (match e in _ = y return 
            (match y in Vector.t _ n' return A -> Prop
            with 
            | [] => fun _ => False 
            | b' :: _ => fun i => i = b'
            end a)
          with 
          | eq_refl => eq_refl
          end).
      Defined.

      Theorem vec_inv_tail {n : nat} {A : Type} (a b : A) 
        (u v : Vector.t A n) (e : a :: u = b :: v) : u = v.
      Proof.
        refine 
          match e in _ = y return 
          (match y in Vector.t _ n' return Vector.t _ (pred n') -> Prop 
          with
          | [] => fun _ => False
          | _ :: y' => fun i => i = y'  
          end u)
          with 
          | eq_refl => eq_refl 
          end.
      Defined.

      Theorem vec_inv {n : nat} {A : Type} (a b : A) 
        (u v : Vector.t A n) (e : a :: u = b :: v) : a = b ∧ u = v.
      Proof.
        split;[eapply vec_inv_head | eapply vec_inv_tail]; exact e.
      Qed.

End Vecutil.



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
    Defined.

    Lemma add_0_r : forall (n : nat), (n + 0 = n)%nat.
    Proof.
      induction n as [|n ihn].
      - reflexivity.
      - simpl. rewrite ihn. reflexivity.
    Defined.

    (* Second helper lemma: right successor *)
    Lemma add_succ_r : forall (n m : nat), (n + S m = S (n + m))%nat.
    Proof.
      induction n as [|n ihn].
      - intro m. reflexivity.
      - intro m. simpl. 
        rewrite ihn. 
        reflexivity.
    Defined.

    (* Main theorem using the helper lemmas *)
    Theorem add_comm : forall (n m : nat), (n + m = m + n)%nat.
    Proof.
      induction n as [|n ihn].
      - intro m. simpl. rewrite add_0_r. reflexivity.
      - intro m. simpl. rewrite ihn. rewrite add_succ_r. reflexivity.
    Defined.


    Theorem add_assoc : ∀ (n m o : nat), 
      (n + m + o = n + (m + o))%nat.
    Proof.
      induction n as [|n ihn].
      - (* Case n = 0 *)
        simpl.
        reflexivity.
      - (* Case n = S n' *)
        simpl; intros *.
        rewrite ihn.
        reflexivity.
    Defined.


    (* Helper lemma 1: Right zero property *)
    Lemma mul_0_r : ∀ (n : nat), (n * 0 = 0)%nat.
    Proof.
      induction n as [|n ihn].
      - reflexivity.
      - simpl. rewrite ihn. 
        reflexivity.
    Defined.

    (* Helper lemma 2: Right successor property *)
    Lemma mul_succ_r : ∀ (n m : nat), 
      (n * (S m) = n * m + n)%nat.
    Proof.
      induction n as [|n ihn]; intro m.
      - reflexivity.
      - simpl. rewrite ihn.
        assert(ha : (m + n * m + S n = S n + (m + n * m))%nat).
        eapply add_comm.
        rewrite ha; clear ha; 
        cbn. f_equal.
        rewrite add_comm.
        assert (ha : (n * m + n = n + n * m)%nat) 
        by (eapply add_comm).
        rewrite ha; clear ha.
        rewrite add_assoc.
        assert(ha : (n * m + m = m + n * m)%nat) 
        by (eapply add_comm).
        rewrite ha; clear ha.
        reflexivity.
    Defined.


    (* Main theorem *)
    Theorem mul_comm : forall (n m : nat), (n * m = m * n)%nat.
    Proof.
      induction n as [|n ihn]; 
      intro m.
      - (* Base case: a = 0 *)
        simpl. rewrite mul_0_r. 
        reflexivity.
      - (* Inductive case: a = S a' *)
        simpl.
        rewrite ihn, mul_succ_r,
        add_comm;
        reflexivity.
    Defined.

    Theorem add_mul_dist : forall (n m o : nat), 
      (n * (m + o) = n * m + n * o)%nat.
    Proof.
      induction n as [|n ihn].
      - (* Base case: a = 0 *)
        intros *.
        reflexivity.
      - (* Inductive case: a = S a' *)
        intros *. cbn.
        rewrite ihn.
        rewrite <- add_assoc.
        rewrite <-add_assoc.
        f_equal.
        rewrite add_assoc.
        rewrite add_assoc.
        f_equal.
        eapply add_comm.
    Defined.

  
    
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
      exact (@eq_rect nat n (Vector.t A) u m Ha).
    Defined.


  

    Lemma divmod_simplification : 
      forall (x y q u : nat),
      fst (Nat.divmod x y q u) = (q + fst (Nat.divmod x y 0 u))%nat.
    Proof.
      induction x;
      intros *; simpl;
      [ | destruct u; rewrite IHx;
      [erewrite IHx with (q := 1%nat) | erewrite IHx]].
      rewrite add_comm. reflexivity.
      cbn.
      assert (ha : (q + S (fst (Nat.divmod x y 0 y)) = 
        S (fst (Nat.divmod x y 0 y)) + q)%nat).
      rewrite add_comm; reflexivity.
      rewrite ha; cbn. f_equal.
      eapply add_comm.
      reflexivity.
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
      

    Theorem div_add_ind : ∀ (n m : nat),
      (fst (Nat.divmod (2 * n + m) 1 0 1) =  
      n + fst (Nat.divmod m 1 0 1))%nat.
    Proof.
      induction n as [|n ihn].
      +
        cbn; intro m; 
        reflexivity.
      +
        intros *.
        replace (2 * S n)%nat with 
        (2 + 2 * n)%nat.
        cbn.
        rewrite divmod_simplification.
        replace (n + (n + 0))%nat with 
        (2 * n)%nat. 
        rewrite ihn. 
        reflexivity.
        reflexivity.
        cbn. 
        f_equal.
        assert (ha : (n + S (n + 0) = S (n + 0) + n)%nat).
        now rewrite add_comm.
        rewrite ha. cbn. f_equal.
        rewrite add_comm.
        reflexivity.
    Defined.


    Theorem div_add : ∀ (n m : nat),
      (m + (m * n) / 2 = (m * (2 + n)) / 2)%nat.
    Proof.
      destruct m as [|m]; cbn.
      +
        reflexivity.
      +
        change (S (S n)) with (2 + n)%nat.
        assert (ha : (fst (Nat.divmod (n + m * (2 + n)) 1 1 1) = 
          S (fst (Nat.divmod (n + m * (2 + n)) 1 0 1)))%nat).
        rewrite divmod_simplification.
        reflexivity. rewrite ha; clear ha.
        f_equal. 
        replace (n + m * (2 + n))%nat with 
        (2 * m + n + m * n)%nat.
        rewrite add_assoc.
        remember (n + m * n)%nat as a.
        rewrite div_add_ind.
        reflexivity.
        rewrite add_mul_dist, <-add_assoc.
        assert (ha : (n + m * 2 = m * 2 + n)%nat) 
        by (now eapply add_comm).
        rewrite ha; clear ha.
        assert (ha : (2 * m = m * 2)%nat) by 
        (eapply mul_comm).
        rewrite ha. reflexivity.
    Defined.

    Theorem nat_div_even : ∀ (n : nat), 
      ∃ (k : nat), ((1 + n) * n)%nat = (2 * k)%nat.
    Proof.
      induction n as [|n ihn].
      +
        exists 0%nat.
        reflexivity.
      +
        destruct ihn as (k & ihn).
        cbn. exists (k + n + 1)%nat.
        rewrite add_0_r.
        replace (n * S n)%nat with 
        ((1 + n) * n)%nat.
        rewrite ihn.
        rewrite add_comm.
        cbn.
        rewrite add_0_r.
        assert (ha : (k + n + 1 = 1 + n + k)%nat).
        rewrite add_comm, add_assoc.
        f_equal. eapply add_comm.
        rewrite !ha; clear ha.
        cbn. f_equal.
        assert (ha : (n + k + S (n + k))%nat = 
          (S (n + k) + n + k)%nat).
        rewrite add_comm. cbn.
        f_equal. rewrite <-add_assoc.
        reflexivity.
        rewrite !ha; clear ha.
        cbn; f_equal.
        rewrite <-add_assoc.
        rewrite add_comm.
        assert (ha : (n + k + n)%nat = 
        (n + n + k)%nat).
        rewrite add_assoc.
        rewrite add_assoc.
        f_equal. eapply add_comm.
        rewrite ha; clear ha.
        assert (ha : (n + n + k + k)%nat = 
          (n + (n + k + k))%nat).
        rewrite <-add_assoc.
        rewrite <-add_assoc.
        reflexivity.
        rewrite ha; clear ha.
        reflexivity.
        eapply mul_comm.
    Defined.
        

    Theorem nat_div_adds : ∀ (n : nat), 
      (2 * n / 2 + 2 * n / 2)%nat = (2 * n)%nat.
    Proof.
      induction n as [|n ihn].
      +
        reflexivity.
      +
        replace (2 * S n)%nat with (2 + 2 * n)%nat.
        cbn in ihn |- *.
        rewrite add_0_r in ihn |- *.
        rewrite divmod_simplification.
        remember (fst (Nat.divmod (n + n) 1 0 1)) as ret.
        cbn. f_equal.
        rewrite add_comm.
        cbn. f_equal.
        exact ihn.
        change (S n)%nat with (1 + n)%nat.
        rewrite add_mul_dist.
        reflexivity.
    Defined.
  

    Theorem nat_div_gen : ∀ (n : nat), 
      (Nat.div ((1 + n) * n) 2 +  Nat.div ((1 + n) * n) 2)%nat = 
      ((1 + n) * n)%nat.
    Proof.
      intros n.
      destruct (nat_div_even n) as (k & ha).
      rewrite !ha.
      eapply nat_div_adds.
    Defined.

   
      
    Definition nat_div_2 : ∀ (n : nat), 
      (Nat.div ((2 + n) * (1 + n)) 2 + 
      Nat.div ((2 + n) * (1 + n)) 2)%nat = ((2 + n) * (1 + n))%nat.
    Proof.
      intros *.
      specialize (nat_div_gen (S n)) as ha.
      change (1 + S n)%nat with (2 + n)%nat in ha.
      exact ha.
    Defined.
    (* end of proofs *)
End TransProofs.

From Stdlib Require Import Vector Fin.
Import VectorNotations EqNotations.

Section NeqUtil.

   

    Theorem generate_pairs_of_vector_proof : 
      ∀ (n m : nat), m + Nat.div (m * n) 2 = 
      Nat.div ((2 + n) * m) 2.
    Proof.
        intros *. 
        rewrite div_add.
        f_equal. rewrite add_mul_dist.
        assert (ha : (2 + n) * m = m * (2 + n)) by 
        (now rewrite mul_comm). 
        rewrite ha; clear ha.
        rewrite add_mul_dist.
        exact eq_refl.
    Defined.

    
    (* computes pair of vectors: *)
    Fixpoint generate_pairs_of_vector {A : Type} {n : nat}  
      (gs : Vector.t A (2 + n)) : Vector.t (A * A) (Nat.div ((2 + n) * (1 + n)) 2).
    Proof.
      destruct n as [|n].
      +
        destruct (vector_inv_S gs) as (gsh & gst & _).
        destruct (vector_inv_S gst) as (gsth & _).
        exact [(gsh, gsth)].
      +
        destruct (vector_inv_S gs) as (gsh & gst & _).
        (* map gsh over gst *)
        set (reta := Vector.map (fun x => (gsh, x)) gst).
        specialize (generate_pairs_of_vector _ _ gst).
        refine(@eq_rect nat _ (Vector.t (A * A)) 
        (reta ++ generate_pairs_of_vector) _ _).
        eapply generate_pairs_of_vector_proof.
    Defined.

   
    Fixpoint pair_unzip {A : Type} {n : nat} : 
      Vector.t (Vector.t A 2) n -> Vector.t A (n + n).
    Proof.
      intros v.
      refine
        (match v in Vector.t _ n' return Vector.t _ (n' + n')  
        with 
        | [] => []
        | Vector.cons _ vh nt vt => _ 
        end). 
        replace (S nt +  S nt) with  (S (S (nt + nt))).
        exact (vh ++ pair_unzip _ _ vt).
        cbn. f_equal.
        rewrite add_succ_r.
        reflexivity.
    Defined.
      
    Fixpoint pair_zip {A : Type} {n : nat} : 
      Vector.t A (n + n) ->  Vector.t (Vector.t A 2) n.
    Proof.
      destruct n as [|n].
      +
        intros vs.
        exact [].
      +
        intros vs.
        replace (S n +  S n) with  (S (S (n + n))) in vs.
        destruct (vector_inv_S vs) as (vsh & vst & _).
        destruct (vector_inv_S vst) as (vsth & vstt & _).
        refine(Vector.cons _ [vsh; vsth] _ (pair_zip _ _ vstt)).
        cbn. f_equal.
        rewrite add_succ_r.
        reflexivity.
    Defined.

    Theorem pair_zip_unzip_id {A : Type} : 
      ∀ (n : nat) (vs : Vector.t (Vector.t A 2) n), 
        @pair_zip A n (@pair_unzip A n vs) = vs.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        pose proof (vector_inv_0 vs) as ha.
        subst; reflexivity.
      +
        intros *.
        destruct (vector_inv_S vs) as (vsh & vst & ha).
        subst; cbn.
        rewrite rew_opp_l.
        destruct (vector_inv_S (vsh ++ pair_unzip vst)) as (vh & vt & ha).
        destruct (vector_inv_S vsh) as (vshh & vsht & hb).
        rewrite hb in ha.
        cbn in ha. 
        eapply vec_inv in ha.
        destruct ha as (hal & har).
        subst. 
        destruct (vector_inv_S vsht) as (vshth & vshtt & ha).
        pose proof (vector_inv_0 vshtt) as hb.
        subst. cbn. 
        rewrite ihn; reflexivity.
    Qed.

    Lemma nth_zip_with : forall (A B C : Type) (f : A -> B -> C) (n : nat)
      (i : Fin.t n) (vsa : Vector.t A n) (vsb  : Vector.t B n),
      (zip_with f vsa vsb)[@i] = f (vsa[@i]) (vsb[@i]).
    Proof.
      intros until f.
      induction n as [|n ihn].
      +
        intros *.
        refine match i with end.
      +
        intros *.
        destruct (vector_inv_S vsa) as (vsah & vsat & ha).
        destruct (vector_inv_S vsb) as (vsbh & vsbt & hb).
        subst. 
        destruct (fin_inv_S _ i) as [hc | (i' & ha)].
        ++
          subst; cbn; reflexivity.
        ++
          subst; cbn.
          eapply ihn.
    Qed.

    Lemma map_fin {A B : Type} (f : A -> B) :
      ∀ (n : nat) (i : Fin.t n) (vs : Vector.t A n), 
      (Vector.map f vs)[@i] = f (vs[@i]).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        refine match i with end.
      +
        intros *.
        destruct (vector_inv_S vs) as (vsh & vst & ha).
        subst. 
        destruct (fin_inv_S _ i) as [hc | (i' & ha)].
        ++
          subst; cbn; reflexivity.
        ++
          subst; cbn; eapply ihn.
    Qed.

    
    Lemma fin_append_inv : ∀ (m n : nat) (i : Fin.t (m+n)),
      (∃ j : Fin.t m, i = Fin.L n j) ∨ (∃ j : Fin.t n, i = Fin.R m j).
    Proof.
      induction m as [|m ihm].
      +
        intros *. 
        cbn in i. 
        right; exists i.
        reflexivity.
      +
        intros *.
        cbn in i.
        destruct (fin_inv_S _ i) as [i' | (i' & ha)].
        ++
          subst. cbn. left.
          unfold Fin.L.
          exists Fin.F1.
          reflexivity.
        ++
          destruct (ihm _ i') as [(j & hb) | (j & hb)].
          -
            subst. left.
            exists (Fin.FS j).
            reflexivity.
          -
            subst. right.
            exists j.
            reflexivity.
    Qed.



    Lemma nth_rew {A : Type} {n m : nat} (v : Vector.t A n) (ha : n = m) 
      (i : Fin.t m) :
      (rew [Vector.t A] ha in v)[@i] = v[@rew [Fin.t] (eq_sym ha) in i]. 
    Proof.
      revert v i.
      refine(
        match ha in _ = m' return 
          ∀ (v : Vector.t A n) (i : Fin.t m'), (rew [Vector.t A] ha in v)[@i] = v[@rew [Fin.t] eq_sym ha in i]
        with
        | eq_refl => fun v i => eq_refl
        end).
    Defined.

    Theorem fin_inv {n : nat} (a b : Fin.t n) 
      (e : Fin.FS a = Fin.FS b) : a = b.
    Proof.
      refine 
        match e in _ = y return 
          (match y in Fin.t n' return Fin.t (pred n') -> Prop 
          with 
          | Fin.FS i => fun x => x = i 
          | Fin.F1 => fun _ => False 
          end a)
        with 
        | eq_refl => eq_refl
        end.
    Defined.

    Lemma generate_pairs_distinct {A : Type} : 
      ∀ (n : nat) (vs : Vector.t A (2+n)) 
      (i : Fin.t ((2 + n) * (1 + n)/ 2)) (v₁ v₂ : A),
      (generate_pairs_of_vector vs)[@i] = (v₁, v₂) ->
      ∃ (j k : Fin.t (2 + n)), j ≠ k ∧ v₁ = vs[@j] ∧ v₂ = vs[@k].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        cbn in vs, i.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        destruct (vector_inv_S vst) as (vsth & vstt & hc).
        pose proof (vector_inv_0 vstt) as hd.
        subst.
        destruct (fin_inv_S _ i) as [i' | (i' & hb)]; 
        subst.
        exists (Fin.F1), (Fin.FS (Fin.F1)); split.
        intro hb. congruence.
        cbn in ha |- *.
        inversion ha; subst; split; reflexivity.
        refine match i' with end.
      +
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        subst. change (S (S n)) with (2 + n) in vst.
        cbn in ha.
        assert (hb : (2 + S n) * (1 + S n) = (2 + n) * 2 + (2 + n) * (1 + n)) 
        by nia.
        assert (hc : ((2 + S n) * (1 + S n) / 2) = 
          (2 + n) + ((2 + n) * (1 + n) / 2)).
        rewrite hb; clear hb. 
        rewrite <-Nat.div_add_l.
        reflexivity. nia. clear hb.
        rename hc into hb.
        revert i ha.
        generalize (generate_pairs_of_vector_proof 
          (S n) (S (S n))). 
        intros * ha.
        rewrite nth_rew in ha.
        assert (hc : hb = eq_sym e).
        eapply UIP_nat.
        setoid_rewrite <-hc in ha.
        clear e hc.
        remember (rew [Fin.t] hb in i) as i'.
        setoid_rewrite <-Heqi' in ha.
        clear Heqi' i hb.
        rename i' into i. cbn in ha.
        destruct (fin_append_inv _ _ i) as [(j & hb) | (j & hb)].
        ++
          subst.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (vsh, x)) vst)
          (generate_pairs_of_vector vst) j as hb.
          cbn in ha, hb. rewrite hb in ha.
          clear hb. 
          exists Fin.F1, (Fin.FS j).
          split. intro hb. congruence.
          cbn. rewrite map_fin in ha.
          inversion ha; subst.
          split; reflexivity.
        ++
          subst.
          cbn in ha. 
          (* why rewrite is not working? *)
          pose proof @nth_append_R _ _ _ (map (λ x : A, (vsh, x)) vst)
          (generate_pairs_of_vector vst) j as hb.
          cbn in hb. rewrite hb in ha.
          clear hb.
          destruct (ihn vst j v₁ v₂ ha) as (jj & kk & hb & hc & hd).
          exists (Fin.FS jj), (Fin.FS kk).
          cbn. split. intro he. eapply hb.
          eapply fin_inv in he. exact he.
          subst. split; reflexivity.
    Qed.

    Lemma generate_pairs_distinct_triple {A B : Type} : 
      ∀ (n : nat) (gs hs : Vector.t A (2+n)) 
      (xs :  Vector.t B (2+n)) (i : Fin.t ((2 + n) * (1 + n)/ 2)) 
      (g₁ g₂ h₁ h₂ : A) (x₁ x₂ : B),
      (generate_pairs_of_vector gs)[@i] = (g₁, g₂) ->
      (generate_pairs_of_vector hs)[@i] = (h₁, h₂) ->
      (generate_pairs_of_vector xs)[@i] = (x₁, x₂) ->
      ∃ (j k : Fin.t (2 + n)), j ≠ k ∧ g₁ = gs[@j] ∧ g₂ = gs[@k] ∧
      h₁ = hs[@j] ∧ h₂ = hs[@k] ∧ x₁ = xs[@j] ∧ x₂ = xs[@k].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha hb hc.
        destruct (vector_inv_S gs) as (gsh & gst & hd).
        destruct (vector_inv_S gst) as (gsth & gstt & he).
        pose proof (vector_inv_0 gstt) as hf.
        subst.
        destruct (vector_inv_S hs) as (hsh & hst & hd).
        destruct (vector_inv_S hst) as (hsth & hstt & he).
        pose proof (vector_inv_0 hstt) as hf.
        subst.
        destruct (vector_inv_S xs) as (xsh & xst & hd).
        destruct (vector_inv_S xst) as (xsth & xstt & he).
        pose proof (vector_inv_0 xstt) as hf.
        subst.
        destruct (fin_inv_S _ i) as [i' | (i' & hd)]; 
        subst.
        ++
          exists (Fin.F1), (Fin.FS (Fin.F1)); split.
          intro he. congruence.
          cbn in ha, hb, hc |- *.
          inversion ha; inversion hb; 
          inversion hc; subst;
          try (repeat split; reflexivity).
        ++
          refine match i' with end.
      +
        (* inductive case *)
        intros * ha hb hc.
        destruct (vector_inv_S gs) as (gsh & gst & hd).
        destruct (vector_inv_S hs) as (hsh & hst & he).
        destruct (vector_inv_S xs) as (xsh & xst & hf).
        subst. change (S (S n)) with (2 + n) in gst, hst, xst.
        cbn in ha, hb, hc.
        assert (hd : (2 + S n) * (1 + S n) = (2 + n) * 2 + (2 + n) * (1 + n)) 
        by nia.
        assert (he : ((2 + S n) * (1 + S n) / 2) = 
          (2 + n) + ((2 + n) * (1 + n) / 2)).
        rewrite hd; clear hd. 
        rewrite <-Nat.div_add_l.
        reflexivity. nia. clear hd.
        rename he into hd.
        revert i ha hb hc.
        generalize (generate_pairs_of_vector_proof 
          (S n) (S (S n))). 
        intros * ha hb hc.
        rewrite nth_rew in ha, hb.
         rewrite nth_rew in hc.
        assert (he : hd = eq_sym e).
        eapply UIP_nat.
        setoid_rewrite <-he in ha.
        setoid_rewrite <-he in hb.
        setoid_rewrite <-he in hc.
        clear e he.
        remember (rew [Fin.t] hd in i) as i'.
        setoid_rewrite <-Heqi' in ha.
        setoid_rewrite <-Heqi' in hb.
        setoid_rewrite <-Heqi' in hc.
        clear Heqi' i hd.
        rename i' into i. 
        destruct (fin_append_inv _ _ i) as [(j & hd) | (j & hd)].
        ++
          subst.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (gsh, x)) gst)
          (generate_pairs_of_vector gst) j as hd.
          cbn in ha, hd. rewrite hd in ha.
          clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (hsh, x)) hst)
          (generate_pairs_of_vector hst) j as hd.
          cbn in hb, hd. rewrite hd in hb.
          clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : B, (xsh, x)) xst)
          (generate_pairs_of_vector xst) j as hd.
          cbn in hc, hd. rewrite hd in hc.
          clear hd.
          exists Fin.F1, (Fin.FS j).
          split. intro hd. congruence.
          cbn. rewrite map_fin in ha, hb.
          rewrite map_fin in hc.
          inversion ha; inversion hb; inversion hc; 
          subst.
          try (repeat split; reflexivity).
        ++
          subst.
          cbn in ha, hb, hc. 
          (* why rewrite is not working? *)
          pose proof @nth_append_R _ _ _ (map (λ x : A, (gsh, x)) gst)
          (generate_pairs_of_vector gst) j as hd.
          cbn in hd. rewrite hd in ha.
          clear hd.
          pose proof @nth_append_R _ _ _ (map (λ x : A, (hsh, x)) hst)
          (generate_pairs_of_vector hst) j as hd.
          cbn in hd. rewrite hd in hb.
          clear hd.
          pose proof @nth_append_R _ _ _ (map (λ x : B, (xsh, x)) xst)
          (generate_pairs_of_vector xst) j as hd.
          cbn in hd. rewrite hd in hc.
          clear hd.
          destruct (ihn gst hst xst j g₁ g₂ h₁ h₂ x₁ x₂ 
            ha hb hc) as (jj & kk & hd & he & hf & hg & hi & hj & hk).
          exists (Fin.FS jj), (Fin.FS kk).
          cbn. split. intro hl. eapply hd.
          eapply fin_inv in hl. exact hl.
          subst. try (repeat split; reflexivity).
    Qed.
   

    Lemma invert_eq_rect {A : Type} {x y : A} 
      (P : A -> Type) (hb : y = x) (ha : P x) (hc : P y) :
      rew <-[P] hb in ha = hc → rew [P] hb in hc = ha.
    Proof.
      revert ha hc.
      refine
      (match hb in  _ = x' return 
        ∀ (ha : P x') (hc : P y), rew <- [P] hb in ha = hc → rew [P] hb in hc = ha
      with 
      | eq_refl => fun ha hb hc => eq_sym hc
      end).
    Defined.


    Fixpoint vector_member {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}}
      {n : nat} (v : A) 
      (vs : Vector.t A n) : bool :=
      match vs with
      | [] => false
      | vsh :: vst => match dec v vsh with 
        | left _ => true 
        | right _ => @vector_member _ dec _ v vst 
        end
      end.


    Fixpoint vector_unique {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}} 
      {n : nat} (vs : Vector.t A n) : bool :=
      match vs with
      | [] => true
      | vsh :: vst  => negb (@vector_member _ dec _ vsh vst) && 
        @vector_unique _ dec _ vst
      end.


    Theorem vector_member_true {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}} : 
      ∀ (n : nat) (v : A) (vs : Vector.t A (1 + n)),
      @vector_member _ dec _ v vs = true -> ∃ (i : Fin.t (1 + n)), v = vs[@i].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        pose proof (vector_inv_0 vst) as hc.
        subst. cbn in ha.
        exists Fin.F1; cbn.
        destruct (dec v vsh) as [hb | hb]; try congruence.
      +
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        subst. cbn in ha.
        destruct (dec v vsh) as [hb | hb].
        ++ exists Fin.F1; cbn. exact hb.
        ++ 
          destruct (ihn v vst ha) as (j & hc).
          exists (Fin.FS j); cbn.
          exact hc.
    Qed.


    Theorem vector_member_false {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}} : 
      ∀ (n : nat) (v : A) (vs : Vector.t A (1 + n)),
      @vector_member _ dec _ v vs = false -> ∀ (i : Fin.t (1 + n)), v ≠ vs[@i].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha *.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        pose proof (vector_inv_0 vst) as hc.
        destruct (fin_inv_S _ i) as [i' | (i' & hd)];
        subst. cbn in ha |- *.
        destruct (dec v vsh) as [hb | hb]; try congruence.
        refine match i' with end.
      +
        intros * ha *.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        destruct (fin_inv_S _ i) as [i' | (i' & hc)];
        subst; cbn in ha |- *.
        destruct (dec v vsh) as [hb | hb]; try congruence.
        destruct (dec v vsh) as [hb | hb]; try congruence.
        eapply ihn; try assumption.
    Qed.

    
    Theorem vector_unique_true {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}} : 
      ∀ (n : nat) (vs : Vector.t A (2 + n)), 
      @vector_unique _ dec _ vs = true -> ∀ (i j : Fin.t (2 + n)), 
        i ≠ j -> vs[@i] ≠ vs[@j].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha * hb hc. 
        destruct (vector_inv_S vs) as (vsh & vst & hd).
        destruct (vector_inv_S vst) as (vsth & vstt & he).
        pose proof (vector_inv_0 vstt) as hf.
        subst. 
        destruct (fin_inv_S _ i) as [i' | (i' & hd)];
        destruct (fin_inv_S _ j) as [j' | (j' & he)];
        subst; try congruence.
        destruct (fin_inv_S _ j') as [j'' | (j'' & hd)];
        subst; cbn in ha, hc.
        rewrite <-hc in ha.
        destruct (dec vsh vsh) as [hd | hd];
        try congruence. cbn in ha.
        congruence. refine match j'' with end.
        destruct (fin_inv_S _ i') as [i'' | (i'' & hd)];
        subst; cbn in ha, hc.
        rewrite <-hc in ha.
        destruct (dec vsth vsth) as [hd | hd];
        try congruence. cbn in ha.
        congruence. refine match i'' with end.
        destruct (fin_inv_S _ i') as [i'' | (i'' & hd)];
        destruct (fin_inv_S _ j') as [j'' | (j'' & he)];
        subst; try congruence.
        refine match j'' with end.
        refine match i'' with end.
        refine match i'' with end.
      +
        intros * ha * hb.
        destruct (vector_inv_S vs) as (vsh & vst & hc).
        subst. cbn in ha.
        eapply andb_true_iff in ha.
        destruct ha as (hal & har).
        rewrite negb_true_iff in hal.
        destruct (fin_inv_S _ i) as [i' | (i' & hd)];
        destruct (fin_inv_S _ j) as [j' | (j' & he)]; 
        subst; try congruence.
        cbn. eapply vector_member_false. exact hal.  
        cbn. eapply vector_member_false with (i := i') in hal. 
        auto.
        cbn. eapply ihn; try assumption.
        intro hc. eapply hb.
        subst. reflexivity.
    Qed.


    Theorem vector_unique_false {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}} : 
      ∀ (n : nat) (vs : Vector.t A (2 + n)), 
      @vector_unique _ dec _ vs = false -> ∃ (i j : Fin.t (2 + n)), i ≠ j ∧ vs[@i] = vs[@j].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hd).
        destruct (vector_inv_S vst) as (vsth & vstt & he).
        pose proof (vector_inv_0 vstt) as hf.
        subst. cbn in ha.
        eapply andb_false_iff in ha.
        destruct ha as [ha | ha]; try congruence.
        eapply negb_false_iff in ha.
        destruct (dec vsh vsth) as [hb | hb]; try congruence.
        exists Fin.F1, (Fin.FS Fin.F1).
        cbn; split. intro hc. congruence.
        assumption.
      +
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        subst. cbn in ha.
        eapply andb_false_iff in ha.
        destruct ha as [ha | ha].
        ++
          rewrite negb_false_iff in ha.
          eapply vector_member_true in ha.
          destruct ha as (i & ha).
          exists (Fin.F1), (Fin.FS i).
          cbn. split. intro hb; try congruence.
          exact ha.
        ++
          destruct (ihn vst ha) as (ii & jj & hb & hc).
          exists (Fin.FS ii), (Fin.FS jj).
          cbn. split. intro hd.
          eapply hb. eapply fin_inv in hd.
          exact hd.
          exact hc. 
    Qed.


    Theorem vector_unique_decidable  {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}} : 
      ∀ (n : nat) (vs : Vector.t A (2 + n)),
      {∀ (i j : Fin.t (2 + n)), i ≠ j -> vs[@i] ≠ vs[@j]} + 
      {∃ (i j : Fin.t (2 + n)), i ≠ j ∧ vs[@i] = vs[@j]}.
    Proof.
      intros *.
      destruct (@vector_unique _ dec _ vs) eqn:hb.
      +
        left.
        intros * hc.
        eapply vector_unique_true.
        exact hb. exact hc.
      +
      
      right.
      eapply vector_unique_false.
      exact hb.
    Qed.


    Lemma generate_pairs_contains {A : Type} : 
      ∀ (n : nat) (vs : Vector.t A (2+n)) 
      (i j : Fin.t (2+n)), i ≠ j ->
      ∃ (k : Fin.t ((2+n)*(1+n)/2)),
      (fst ((generate_pairs_of_vector vs)[@k]) = vs[@i] ∧ 
      snd ((generate_pairs_of_vector vs)[@k]) = vs[@j]) ∨ 
      (fst ((generate_pairs_of_vector vs)[@k]) = vs[@j] ∧ 
      snd ((generate_pairs_of_vector vs)[@k]) = vs[@i]).
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        change (2 + 0) with 2 in i, j, vs |- *.
        change (1 + 0) with 1. 
        change (2 * 1/2) with 1. 
        exists Fin.F1.
        destruct (vector_inv_S vs) as (vsh & vst & hd).
        destruct (vector_inv_S vst) as (vsth & vstt & he).
        pose proof (vector_inv_0 vstt) as hf.
        subst. 
        refine 
         (match i as i' in Fin.t n' return 
            ∀ (pf : n' = 2), @eq_rect _ n' Fin.t i' 2 pf ≠ j -> 
            (match n' return Fin.t n' -> Type 
            with 
            | 2 => fun w => 
                  (fst ((generate_pairs_of_vector [vsh; vsth])[@F1]) = [vsh; vsth][@w] ∧ 
                  snd ((generate_pairs_of_vector [vsh; vsth])[@F1]) = [vsh; vsth][@j]) ∨ 
                  (fst ((generate_pairs_of_vector [vsh; vsth])[@F1]) = [vsh; vsth][@j] ∧ 
                  snd ((generate_pairs_of_vector [vsh; vsth])[@F1]) = [vsh; vsth][@w])
            | _ => fun _ => IDProp 
            end i')
          with 
          | @Fin.F1 nw => fun (pfa : S nw = 2) he => _
          | @Fin.FS nw i' => fun (pfa : S nw = 2) he => 
            match i' as ir in Fin.t nv return 
              nw = nv -> _ 
             with 
            | @Fin.F1 nt => fun ha => _ 
            | @Fin.FS nt i'' => fun ha => _
            end eq_refl
          end eq_refl ha);
          destruct (fin_inv_S _ j) as [j' | (j' & hc)].
          ++
            assert (hb : nw = 1) by nia.
            subst. cbn. 
            assert (hb : pfa = eq_refl) by (eapply UIP_nat).
            subst; cbn in he.
            congruence.
          ++
            assert (hb : nw = 1) by nia.
            subst.
            assert (hb : pfa = eq_refl) by (eapply UIP_nat).
            subst; cbn in he.
            destruct (fin_inv_S _ j') as [j'' | (j'' & hc)].
            -
              subst; cbn.
              left; split; reflexivity.
            -
              refine match j'' with end.
            ++
              assert (hb : nt = 0) by nia.
              subst; cbn. 
              right; split; reflexivity.
            ++
              assert (hb : nt = 0) by nia.
              subst; cbn. 
              destruct (fin_inv_S _ j') as [j'' | (j'' & hc)]; subst.
              -
                assert (hb : pfa = eq_refl) by (eapply UIP_nat).
                subst; cbn in he.
                destruct (fin_inv_S _ i') as [i'' | (i'' & hc)]; subst; 
                try congruence.
                refine match i'' with end.
              -
                refine match j'' with end.
            ++
              assert (hb : nt = 0) by nia.
              subst. refine match i'' with end.
            ++
              assert (hb : nt = 0) by nia.
              subst. refine match i'' with end.
      +
        (* inductive case *)
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        subst.
        destruct (fin_inv_S _ i) as [i' | (i' & hb)];
        destruct (fin_inv_S _ j) as [j' | (j' & hc)]; 
        try congruence.
        ++
          subst. 
          assert (hb : (2 + S n) * (1 + S n) = 
            (2 + n) * 2 + (2 + n) * (1 + n)) by nia.
          assert (hc : ((2 + S n) * (1 + S n) / 2) = 
            (2 + n) + ((2 + n) * (1 + n) / 2)).
          rewrite hb; clear hb. 
          rewrite <-Nat.div_add_l.
          reflexivity. nia. clear hb.
          set (kr := @Fin.L (2+n) ((2+n)*(1+n)/2) j').
          exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
            Fin.t kr ((2 + S n) * (1 + S n) / 2)
            (eq_sym hc)).
          cbn. rewrite nth_rew. 
          generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e.
          intro e.
          assert (hb : hc = eq_sym e).
          eapply UIP_nat.
          rewrite hb, eq_sym_involutive. 
          clear hb hc.
          subst.
          rewrite rew_compose, eq_trans_sym_inv_r.
          cbn. clear e.
          unfold kr.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (vsh, x)) vst)
          (generate_pairs_of_vector vst) j' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          destruct ((map (λ x : A, (vsh, x)) vst)[@j']) as (a, b) eqn:hb.
          rewrite map_fin in hb.
          inversion hb; subst.
          left; split; reflexivity.
        ++
          rename hb into hw.
          assert (hb : (2 + S n) * (1 + S n) = 
            (2 + n) * 2 + (2 + n) * (1 + n)) by nia.
          assert (hc : ((2 + S n) * (1 + S n) / 2) = 
            (2 + n) + ((2 + n) * (1 + n) / 2)).
          rewrite hb; clear hb. 
          rewrite <-Nat.div_add_l.
          reflexivity. nia. clear hb.
          set (kr := @Fin.L (2+n) ((2+n)*(1+n)/2) i').
          exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
            Fin.t kr ((2 + S n) * (1 + S n) / 2)
            (eq_sym hc)).
          cbn. rewrite nth_rew. 
          generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e.
          intro e.
          assert (hb : hc = eq_sym e).
          eapply UIP_nat.
          rewrite hb, eq_sym_involutive.
          clear hb hc.
          subst.
          rewrite rew_compose, eq_trans_sym_inv_r.
          cbn. clear e.
          unfold kr.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (vsh, x)) vst)
          (generate_pairs_of_vector vst) i' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          destruct ((map (λ x : A, (vsh, x)) vst)[@i']) as (a, b) eqn:hb.
          rewrite map_fin in hb.
          inversion hb; subst.
          right; split; reflexivity.
        ++
          subst.
          assert (hb : i' ≠ j').
          intro hb. eapply ha.
          subst; reflexivity.
          destruct (ihn vst i' j' hb) as (kr & hc).
          assert (hd : (2 + S n) * (1 + S n) = 
            (2 + n) * 2 + (2 + n) * (1 + n)) by nia.
          assert (he : ((2 + S n) * (1 + S n) / 2) = 
            (2 + n) + ((2 + n) * (1 + n) / 2)).
          rewrite hd; clear hd. 
          rewrite <-Nat.div_add_l.
          reflexivity. nia. clear hd.
          destruct ((generate_pairs_of_vector vst)[@kr]) as (a, b) eqn:hf.
          destruct hc as [hcl | hcl].
          -
            rename hb into hw. 
            set (kw := @Fin.R ((2+n)*(1+n)/2)  (2+n) kr).
            exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
              Fin.t kw ((2 + S n) * (1 + S n) / 2)
              (eq_sym he)).
            cbn. rewrite nth_rew.
            generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e. intro e.
            assert (hc : he = eq_sym e).
            eapply UIP_nat.
            rewrite hc, eq_sym_involutive. 
            clear hc he.
            subst.
            rewrite rew_compose, eq_trans_sym_inv_r.
            cbn. clear e.
            change (FS (FS (R n kr))) with (R (2 + n) kr).
            clear ihn.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : A, (vsh, x)) vst)
            (generate_pairs_of_vector vst) kr as hv.
            simpl in hv |- *.
            rewrite hv.
            setoid_rewrite hf.
            cbn in hcl |- *.
            left. exact hcl.
          -
            rename hb into hw. 
            set (kw := @Fin.R ((2+n)*(1+n)/2)  (2+n) kr).
            exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
              Fin.t kw ((2 + S n) * (1 + S n) / 2)
              (eq_sym he)).
            cbn. rewrite nth_rew.
            generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e. intro e.
            assert (hc : he = eq_sym e).
            eapply UIP_nat.
            rewrite hc, eq_sym_involutive. 
            clear hc he.
            subst.
            rewrite rew_compose, eq_trans_sym_inv_r.
            cbn. clear e.
            change (FS (FS (R n kr))) with (R (2 + n) kr).
            clear ihn.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : A, (vsh, x)) vst)
            (generate_pairs_of_vector vst) kr as hv.
            simpl in hv |- *.
            rewrite hv.
            setoid_rewrite hf.
            cbn in hcl |- *.
            right; exact hcl.
    Qed.

    Lemma generate_pairs_contains_triple {A B : Type} : 
      ∀ (n : nat) (gs hs : Vector.t A (2+n)) (ys : Vector.t B (2+n))
      (i j : Fin.t (2+n)), i ≠ j ->
      ∃ (k : Fin.t ((2+n)*(1+n)/2)),
      (fst ((generate_pairs_of_vector gs)[@k]) = gs[@i] ∧ 
      snd ((generate_pairs_of_vector gs)[@k]) = gs[@j] ∧
      fst ((generate_pairs_of_vector hs)[@k]) = hs[@i] ∧ 
      snd ((generate_pairs_of_vector hs)[@k]) = hs[@j] ∧
      fst ((generate_pairs_of_vector ys)[@k]) = ys[@i] ∧ 
      snd ((generate_pairs_of_vector ys)[@k]) = ys[@j]) ∨ 
      (fst ((generate_pairs_of_vector gs)[@k]) = gs[@j] ∧ 
      snd ((generate_pairs_of_vector gs)[@k]) = gs[@i] ∧
      fst ((generate_pairs_of_vector hs)[@k]) = hs[@j] ∧ 
      snd ((generate_pairs_of_vector hs)[@k]) = hs[@i] ∧
      fst ((generate_pairs_of_vector ys)[@k]) = ys[@j] ∧ 
      snd ((generate_pairs_of_vector ys)[@k]) = ys[@i]).
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        change (2 + 0) with 2 in i, j, gs, hs, ys |- *.
        change (1 + 0) with 1. 
        change (2 * 1/2) with 1. 
        exists Fin.F1.
        destruct (vector_inv_S gs) as (gsh & gst & hd).
        destruct (vector_inv_S gst) as (gsth & gstt & he).
        pose proof (vector_inv_0 gstt) as hf.
        subst.
        destruct (vector_inv_S hs) as (hsh & hst & hd).
        destruct (vector_inv_S hst) as (hsth & hstt & he).
        pose proof (vector_inv_0 hstt) as hf.
        subst.
        destruct (vector_inv_S ys) as (ysh & yst & hd).
        destruct (vector_inv_S yst) as (ysth & ystt & he).
        pose proof (vector_inv_0 ystt) as hf.
        subst.
        refine 
         (match i as i' in Fin.t n' return 
            ∀ (pf : n' = 2), @eq_rect _ n' Fin.t i' 2 pf ≠ j -> 
            (match n' return Fin.t n' -> Type 
            with 
            | 2 => fun w => 
                  fst (generate_pairs_of_vector [gsh; gsth])[@F1] = [gsh; gsth][@w]
                  ∧ snd (generate_pairs_of_vector [gsh; gsth])[@F1] = [gsh; gsth][@j]
                  ∧ fst (generate_pairs_of_vector [hsh; hsth])[@F1] = [hsh; hsth][@w]
                  ∧ snd (generate_pairs_of_vector [hsh; hsth])[@F1] =[hsh; hsth][@j]
                  ∧ fst (generate_pairs_of_vector [ysh; ysth])[@F1] = [ysh; ysth][@w]
                  ∧ snd (generate_pairs_of_vector [ysh; ysth])[@F1] = [ysh; ysth][@j]
                                                ∨ 
                  fst (generate_pairs_of_vector [gsh; gsth])[@F1] = [gsh; gsth][@j]
                  ∧ snd (generate_pairs_of_vector [gsh; gsth])[@F1] = [gsh; gsth][@w]
                  ∧ fst (generate_pairs_of_vector [hsh; hsth])[@F1] = [hsh; hsth][@j]
                  ∧ snd (generate_pairs_of_vector [hsh; hsth])[@F1] = [hsh; hsth][@w]
                  ∧ fst (generate_pairs_of_vector [ysh; ysth])[@F1] = [ysh; ysth][@j]
                  ∧ snd (generate_pairs_of_vector [ysh; ysth])[@F1] = [ysh; ysth][@w]
            | _ => fun _ => IDProp 
            end i')
          with 
          | @Fin.F1 nw => fun (pfa : S nw = 2) he => _
          | @Fin.FS nw i' => fun (pfa : S nw = 2) he => 
            match i' as ir in Fin.t nv return 
              nw = nv -> _ 
             with 
            | @Fin.F1 nt => fun ha => _ 
            | @Fin.FS nt i'' => fun ha => _
            end eq_refl
          end eq_refl ha);
          destruct (fin_inv_S _ j) as [j' | (j' & hc)].
          ++
            assert (hb : nw = 1) by nia.
            subst. cbn. 
            assert (hb : pfa = eq_refl) by (eapply UIP_nat).
            subst; cbn in he.
            congruence.
          ++
            assert (hb : nw = 1) by nia.
            subst.
            assert (hb : pfa = eq_refl) by (eapply UIP_nat).
            subst; cbn in he.
            destruct (fin_inv_S _ j') as [j'' | (j'' & hc)].
            -
              subst; cbn.
              left; (repeat split; reflexivity).
            -
              refine match j'' with end.
            ++
              assert (hb : nt = 0) by nia.
              subst; cbn. 
              right; repeat split; reflexivity.
            ++
              assert (hb : nt = 0) by nia.
              subst; cbn. 
              destruct (fin_inv_S _ j') as [j'' | (j'' & hc)]; subst.
              -
                assert (hb : pfa = eq_refl) by (eapply UIP_nat).
                subst; cbn in he.
                destruct (fin_inv_S _ i') as [i'' | (i'' & hc)]; subst; 
                try congruence.
                refine match i'' with end.
              -
                refine match j'' with end.
            ++
              assert (hb : nt = 0) by nia.
              subst. refine match i'' with end.
            ++
              assert (hb : nt = 0) by nia.
              subst. refine match i'' with end.
      +
        (* inductive case *)
        intros * ha.
        destruct (vector_inv_S gs) as (gsh & gst & hb).
        destruct (vector_inv_S hs) as (hsh & hst & hc).
        destruct (vector_inv_S ys) as (ysh & yst & hd).
        subst.
        destruct (fin_inv_S _ i) as [i' | (i' & hb)];
        destruct (fin_inv_S _ j) as [j' | (j' & hc)]; 
        try congruence.
        ++
          subst. 
          assert (hb : (2 + S n) * (1 + S n) = 
            (2 + n) * 2 + (2 + n) * (1 + n)) by nia.
          assert (hc : ((2 + S n) * (1 + S n) / 2) = 
            (2 + n) + ((2 + n) * (1 + n) / 2)).
          rewrite hb; clear hb. 
          rewrite <-Nat.div_add_l.
          reflexivity. nia. clear hb.
          set (kr := @Fin.L (2+n) ((2+n)*(1+n)/2) j').
          exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
            Fin.t kr ((2 + S n) * (1 + S n) / 2)
            (eq_sym hc)).
          cbn. rewrite !nth_rew. 
          generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e.
          intro e.
          assert (hb : hc = eq_sym e).
          eapply UIP_nat.
          rewrite !hb, !eq_sym_involutive. 
          clear hb hc.
          subst.
          rewrite !rew_compose, !eq_trans_sym_inv_r.
          cbn. clear e.
          unfold kr.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (gsh, x)) gst)
          (generate_pairs_of_vector gst) j' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (hsh, x)) hst)
          (generate_pairs_of_vector hst) j' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : B, (ysh, x)) yst)
          (generate_pairs_of_vector yst) j' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          destruct ((map (λ x : A, (gsh, x)) gst)[@j']) as (a, b) eqn:hb.
          rewrite map_fin in hb.
          inversion hb; subst. cbn.
          destruct ((map (λ x : A, (hsh, x)) hst)[@j']) as (c, d) eqn:hc.
          rewrite map_fin in hc.
          inversion hc; subst. cbn.
          destruct ((map (λ x : B, (ysh, x)) yst)[@j']) as (e, f) eqn:hd.
          rewrite map_fin in hd.
          inversion hd; subst. cbn.
          left; repeat split; reflexivity.
        ++
          rename hb into hw.
          assert (hb : (2 + S n) * (1 + S n) = 
            (2 + n) * 2 + (2 + n) * (1 + n)) by nia.
          assert (hc : ((2 + S n) * (1 + S n) / 2) = 
            (2 + n) + ((2 + n) * (1 + n) / 2)).
          rewrite hb; clear hb. 
          rewrite <-Nat.div_add_l.
          reflexivity. nia. clear hb.
          set (kr := @Fin.L (2+n) ((2+n)*(1+n)/2) i').
          exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
            Fin.t kr ((2 + S n) * (1 + S n) / 2)
            (eq_sym hc)).
          cbn. rewrite !nth_rew. 
          generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e.
          intro e.
          assert (hb : hc = eq_sym e).
          eapply UIP_nat.
          rewrite !hb, !eq_sym_involutive.
          clear hb hc.
          subst.
          rewrite !rew_compose, !eq_trans_sym_inv_r.
          cbn. clear e.
          unfold kr.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (gsh, x)) gst)
          (generate_pairs_of_vector gst) i' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (hsh, x)) hst)
          (generate_pairs_of_vector hst) i' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : B, (ysh, x)) yst)
          (generate_pairs_of_vector yst) i' as hd.
          cbn in hd |- *. (* If I don't do this, it won't work *)
          rewrite hd; clear hd.
          destruct ((map (λ x : A, (gsh, x)) gst)[@i']) as (a, b) eqn:hb.
          rewrite map_fin in hb.
          inversion hb; subst. cbn.
          destruct ((map (λ x : A, (hsh, x)) hst)[@i']) as (c, d) eqn:hc.
          rewrite map_fin in hc.
          inversion hc; subst. cbn.
          destruct ((map (λ x : B, (ysh, x)) yst)[@i']) as (e, f) eqn:hd.
          rewrite map_fin in hd.
          inversion hd; subst. cbn.
          right; repeat split; reflexivity.
        ++
          subst.
          assert (hb : i' ≠ j').
          intro hb. eapply ha.
          subst; reflexivity.
          destruct (ihn gst hst yst i' j' hb) as (kr & hc).
          assert (hd : (2 + S n) * (1 + S n) = 
            (2 + n) * 2 + (2 + n) * (1 + n)) by nia.
          assert (he : ((2 + S n) * (1 + S n) / 2) = 
            (2 + n) + ((2 + n) * (1 + n) / 2)).
          rewrite hd; clear hd. 
          rewrite <-Nat.div_add_l.
          reflexivity. nia. clear hd.
          destruct ((generate_pairs_of_vector gst)[@kr]) as (a, b) eqn:hf.
          destruct ((generate_pairs_of_vector hst))[@kr] as (c, d) eqn:hg.
          destruct (generate_pairs_of_vector yst)[@kr] as (ey, fy) eqn:hi.
          cbn in hc.
          destruct hc as [hcl | hcl].
          -
            rename hb into hw. 
            set (kw := @Fin.R ((2+n)*(1+n)/2)  (2+n) kr).
            exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
              Fin.t kw ((2 + S n) * (1 + S n) / 2)
              (eq_sym he)).
            cbn. rewrite !nth_rew.
            generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e. intro e.
            assert (hc : he = eq_sym e).
            eapply UIP_nat.
            rewrite !hc, !eq_sym_involutive. 
            clear hc he.
            subst.
            rewrite !rew_compose, !eq_trans_sym_inv_r.
            cbn. clear e.
            change (FS (FS (R n kr))) with (R (2 + n) kr).
            clear ihn.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : A, (gsh, x)) gst)
            (generate_pairs_of_vector gst) kr as hv.
            simpl in hv |- *.
            rewrite hv; clear hv.
            setoid_rewrite hf.
            cbn in |- *.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : A, (hsh, x)) hst)
            (generate_pairs_of_vector hst) kr as hv.
            simpl in hv |- *.
            rewrite hv; clear hv.
            setoid_rewrite hg.
            cbn in |- *.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : B, (ysh, x)) yst)
            (generate_pairs_of_vector yst) kr as hv.
            simpl in hv |- *.
            rewrite hv; clear hv.
            setoid_rewrite hi.
            cbn in  |- *.
            left. exact hcl.
          -
            rename hb into hw. 
            set (kw := @Fin.R ((2+n)*(1+n)/2)  (2+n) kr).
            exists (@eq_rect _ (2 + n + (2 + n) * (1 + n) / 2)
              Fin.t kw ((2 + S n) * (1 + S n) / 2)
              (eq_sym he)).
            cbn. rewrite !nth_rew.
            generalize ((generate_pairs_of_vector_proof (S n) (S (S n)))) as e. intro e.
            assert (hc : he = eq_sym e).
            eapply UIP_nat.
            rewrite !hc, !eq_sym_involutive. 
            clear hc he.
            subst.
            rewrite !rew_compose, !eq_trans_sym_inv_r.
            cbn. clear e.
            change (FS (FS (R n kr))) with (R (2 + n) kr).
            clear ihn.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : A, (gsh, x)) gst)
            (generate_pairs_of_vector gst) kr as hv.
            simpl in hv |- *.
            rewrite hv; clear hv.
            setoid_rewrite hf.
            cbn in |- *.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : A, (hsh, x)) hst)
            (generate_pairs_of_vector hst) kr as hv.
            simpl in hv |- *.
            rewrite hv; clear hv.
            setoid_rewrite hg.
            cbn in |- *.
            pose proof @nth_append_R _ _ _ 
            (map (λ x : B, (ysh, x)) yst)
            (generate_pairs_of_vector yst) kr as hv.
            simpl in hv |- *.
            rewrite hv; clear hv.
            setoid_rewrite hi.
            cbn in  |- *.
            right; exact hcl.
    Qed.

End NeqUtil.


From Stdlib Require Import PArith.PArith 
  ZArith.ZArith Lia
  ZArith.Znumtheory
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




