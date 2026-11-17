(** * General utilities: vectors, finite indices, arithmetic and residues

    This file collects the generic lemmas and functions that almost every
    other file of the development uses.  Most of it is about length-indexed
    vectors ([Vector.t A n]) and finite indices ([Fin.t n]) from the
    standard library.  Sigma protocols, shuffles and tallies all handle
    fixed-size tuples of group elements, challenges and ciphertexts.

    The parts are:

    - [Dec]: turning a decidable equality into booleans ([dec_true],
      [eq_bool]).
    - [Vect]: inversion principles for vectors and indices
      ([vector_inv_0], [vector_inv_S], [fin_inv_S]); pointwise operations
      ([zip_with], [repeat_ntimes], [take], [drop], [vector_forallb]); the
      challenge-vector relations used by the special soundness of parallel
      composition ([two_challenge_vectors_disjoint_someelem]); and the
      splitting of a vector around a position ([vector_fin_app],
      [vector_fin_app_pred]) used by OR-composition.
    - [Vecutil] and [ListUtil]: injectivity of vector [cons] ([vec_inv]) and
      a list map equality ([map_ext_eq]).
    - [TransProofs]: elementary [nat] arithmetic re-proved with [Defined]
      instead of [Qed].  These equations are used as casts inside
      computational definitions (for example [generate_pairs_of_vector]),
      so they must be transparent: the casts then reduce under [cbn] and
      [vm_compute], and the definitions extract to plain code.
    - [NeqUtil]: [generate_pairs_of_vector], which lists all unordered pairs
      of a vector, together with its specification ([generate_pairs_distinct],
      [generate_pairs_contains] and their three-vector variants), plus a
      Boolean distinctness check ([vector_unique]).  These are used by the
      inequality-of-discrete-logs protocol in [Crypto/NeqSigma.v].
    - [Modutil]: arithmetic facts modulo a prime [p] over [Z]
      ([mod_more_gen_bound], [multiplication_bound], …), used by
      [Zpstar.v] and [Fermat.v].
    - [FinEnum]: an explicit enumeration [fin_enum] of [Fin.t n], a
      Boolean universal quantifier [forall_fin] over it, and [nat_to_F], the
      embedding of naturals into a ring-like type.  These are used by the
      Schulze and approval-voting front- and back-ends.

    Many definitions here end with [Defined] rather than [Qed] on purpose,
    because their computational content is extracted or evaluated. *)
From Stdlib Require Import
  Vector Fin Bool Utf8
  Psatz BinIntDef Arith.

Import VectorNotations EqNotations.

(** [existsT x .. y, p] is notation for nested [sigT], a Type-valued
    existential whose witnesses can be computed with and extracted.  It is
    used, for example, by [vector_inv_S] and by the tally back-ends. *)
Notation "'existsT' x .. y , p" :=
  (sigT (fun x => .. (sigT (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'existsT' '/ ' x .. y , '/ ' p ']'") : type_scope.

(** ** Decidable equality as booleans *)
Section Dec.

  (** [R] is any type with a decidable equality [Hdec]. *)
  Context
    {R : Type}
    {Hdec : forall x y : R, {x = y} + {x <> y}}.

  (** The boolean test [if Hdec x y then true else false] is [true] exactly
      when [x = y]. *)
  Lemma dec_true : forall x y,
    (if Hdec x y then true else false) = true <-> x = y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split;
    intro H; auto.
    inversion H.
  Qed.

  (** The boolean test is [false] exactly when [x ≠ y]. *)
  Lemma dec_false : forall x y,
    (if Hdec x y then true else false) = false <-> x <> y.
  Proof.
    intros ? ?.
    destruct (Hdec x y); split;
    intro H; auto.
    inversion H.
    congruence.
  Qed.

  (** The boolean test of [x] against itself is [true]. *)
  Lemma dec_eq_true : forall x,
    (if Hdec x x then true else false) = true.
  Proof.
    intros ?.
    destruct (Hdec x x).
    reflexivity.
    congruence.
  Qed.

  (** [eq_bool x y] is the boolean equality test induced by [Hdec]. *)
  Definition eq_bool (x y : R) : bool :=
    match Hdec x y with
    | left _ => true
    | right _ => false
    end.

End Dec.

(** ** Vectors and finite indices

    Generic lemmas and functions on [Vector.t R n] and [Fin.t n].  The
    inversion lemmas are defined by dependent pattern matching (the small
    inversion technique) and closed with [Defined], so they can be used
    inside computational definitions. *)
Section Vect.

  (** [R] is the element type; [Hdec] is a decidable equality on it, needed
      only by [vector_not_equal_implies_disjoint_someelem]. *)
  Context
    {R : Type}
    {Hdec : forall x y : R, {x = y} + {x <> y}}.

  (** Every vector of length [0] is [nil]. *)
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

  (** Every vector of length [n+1] is [h :: t] for some head [h] and tail
      [t].  The witnesses live in [Type] ([existsT]), so this lemma doubles as
      a computable head/tail destructor. *)
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

  (** [Fin.t 0] is empty. *)
  Lemma fin_inv_0 (i : Fin.t 0) : False.
  Proof. refine (match i with end). Defined.

  (** Every index [i : Fin.t (n+1)] is either [Fin.F1] or [Fin.FS i'] for some
      [i'] (a computable case analysis). *)
  Lemma fin_inv_S (n : nat) (i : Fin.t (S n)) :
    (i = Fin.F1) + {i' | i = Fin.FS i'}.
  Proof.
    refine (match i with
            | Fin.F1 => _
            | Fin.FS _ => _
            end); eauto.
  Defined.

  (** [vector_to_finite_fun n v] views a vector as the function
      [i ↦ v[@i]] on [Fin.t n]. *)
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

  (** [finite_fun_to_vector n f] tabulates a function on [Fin.t n] as the
      vector [[f 0; …; f (n-1)]]. *)
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

  (** Tabulating then indexing gives the function back:
      [(finite_fun_to_vector f)[@i] = f i]. *)
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

  (** [vector_to_finite_fun] is indexing: [v[@i] = vector_to_finite_fun v i]. *)
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

  (** Round trip: [v = finite_fun_to_vector (vector_to_finite_fun v)]. *)
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

  (** [zip_with f u v] combines two vectors of the same length pointwise:
      [(zip_with f u v)[@i] = f u[@i] v[@i]] ([nth_zip_with]).  It is written
      with explicit dependent matches (rather than [Vector.map2]) so that it
      is structurally recursive on [u] and reduces well.  It is the workhorse
      for componentwise operations in the Sigma-protocol files (for example
      [AndSigma.v], [ParallelSigma.v] and [Elgamal.v]). *)
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

  (** [repeat_ntimes n w] is the vector of length [n] with every entry [w]. *)
  Fixpoint repeat_ntimes (n : nat) (w : R) : Vector.t R n :=
    match n as n' return Vector.t R n' with
    | 0 => []
    | S n' => w :: repeat_ntimes n' w
    end.

  (** Every entry of [repeat_ntimes n w] is [w]. *)
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

  (** [take n v] is the first [n] entries of a vector of length [n + m]. *)
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

  (** [drop n v] is the last [m] entries of a vector of length [n + m]. *)
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

  (** [flatten_pair v] turns a vector of [n] pairs into the vector of [2n]
      entries [[a₁; b₁; a₂; b₂; …]]. *)
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

  (** *** Relations between two challenge vectors

      In the special soundness proofs of parallel and AND-composed Sigma
      protocols, two accepting transcripts have challenge vectors [u] and [v]
      of the same length.  The following four predicates compare them
      position by position. *)

  (** [u] and [v] agree at every position. *)
  Definition two_challenge_vectors_same_everyelem {n : nat} :
    Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∀ (f : Fin.t n),
    nth u f = nth v f.

  (** [u] and [v] differ at some position (used by [ParallelSigma.v]). *)
  Definition two_challenge_vectors_disjoint_someelem {n : nat} :
     Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∃ (f : Fin.t n),
    nth u f <> nth v f.

  (** [u] and [v] differ at every position. *)
  Definition two_challenge_vectors_different_everyelem {n : nat} :
    Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∀ (f : Fin.t n),
    nth u f <> nth v f.

  (** [u] and [v] agree at some position. *)
  Definition two_challenge_vectors_same_someelem {n : nat} :
     Vector.t R n -> Vector.t R n -> Prop :=
    fun u v => ∃ (f : Fin.t n),
    nth u f = nth v f.

  (** Distinct vectors differ at some position (uses the decidable equality
      [Hdec] on entries to find the first difference). *)
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

  (** Equal vectors agree at every position. *)
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

  (** [v = take n v ++ drop n v]. *)
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

  (** Consing commutes with a length cast: if [v₁ = rew <- pf in v₂] then
      [vh :: v₁ = rew <- (f_equal S pf) in (vh :: v₂)]. *)
  Theorem rew_eq_refl : ∀ (n m : nat) (v₁ : Vector.t R n)
    (v₂ : Vector.t R m) (vh : R) (pf : n = m),
    v₁ = rew <-pf in v₂ ->
    vh :: v₁ = rew <- [Vector.t R] f_equal S pf in (vh :: v₂).
  Proof.
    intros * ha.
    subst; cbn; reflexivity.
  Qed.

  (** [Box P] wraps a proposition into [Type].  Packaging the length
      equations and properties of [vector_fin_app] in [Box] keeps the
      statement in [Type] (so that the decomposition is computational) while
      marking which parts are only logical. *)
  Record Box (P:Prop) : Type := { p : P }.
  Arguments p {_} _.

   (** Splitting a vector around a position: for [f : Fin.t n], [v] is (up to a
       cast along [n = m₁ + (1 + m₂)]) [v₁ ++ [vm] ++ v₂] where [vm = v[@f]]
       and [m₁] is the numeric value of [f].  Proved by induction on [n] and
       closed with [Defined] so that the pieces can be computed. *)
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

  (** Two-vector version of [vector_fin_app]: given [va] of length [n+1] and
      [vb] of length [n], split [va] around position [f] as
      [v₁ ++ [vm] ++ v₂] and [vb] at the same point as [v₃ ++ v₄], with
      [|v₁| = |v₃|] and [|v₂| = |v₄|].  This is the decomposition used by
      OR-composition ([OrSigma.v], [OrSigmaGen.v], [EncProof.v]) and by the
      ballot front-ends: the real branch sits at [f] and the simulated
      branches are on either side. *)
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

  (** An index of [Fin.t (m + S n)] whose numeric value is [m] is
      [Fin.R m Fin.F1]. *)
  Lemma fin_to_nat : ∀ (m n : nat) (rindex : Fin.t (m + S n)),
    m = proj1_sig (Fin.to_nat rindex) ->
    rindex = Fin.R m (Fin.F1 : Fin.t (S n)).
  Proof.
    intros * ha.
    eapply Fin.to_nat_inj.
    rewrite Fin.R_sanity.
    cbn. rewrite <-ha. nia.
  Qed.

  (** [vector_forallb f v] checks the boolean predicate [f] on every entry
      of [v]. *)
  Definition vector_forallb {n : nat} (f : R -> bool)
    (v : Vector.t R n) : bool :=
    Vector.fold_right (fun x acc => f x && acc) v true.

  (** Specification of [vector_forallb]: it returns [true] iff [f v[@i] = true]
      for every index [i].  Induction on [n]. *)
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

End Vect.

(** ** Injectivity of vector [cons] *)
Section Vecutil.
      (** From [a :: u = b :: v], the heads are equal: [a = b]. *)
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

      (** From [a :: u = b :: v], the tails are equal: [u = v] (proved by small
          inversion, without [Eqdep]). *)
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

      (** Both conclusions of [vec_inv_head] and [vec_inv_tail]. *)
      Theorem vec_inv {n : nat} {A : Type} (a b : A)
        (u v : Vector.t A n) (e : a :: u = b :: v) : a = b ∧ u = v.
      Proof.
        split;[eapply vec_inv_head | eapply vec_inv_tail]; exact e.
      Qed.

End Vecutil.

From Stdlib Require Import List.
(** ** A list lemma *)
Section ListUtil.

  Import ListNotations.
  (** Let [la] and [lb] be lists of pairs of equal length.  Suppose every
      pair [(x, y)] in either list has [f x = true] and [y = z].  Then mapping
      [(a, p) ↦ (f a, p)] gives the same list for both: every entry becomes
      [(true, z)].  The Sigma-protocol files use it to compare per-component
      verification results. *)
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

(** ** Transparent arithmetic on [nat]

    Re-proofs of standard facts about [+], [*] and [/ 2] on [nat], all
    closed with [Defined].  The standard library versions are opaque
    ([Qed]), which would block reduction of the casts in
    [generate_pairs_of_vector], [pair_zip] and [pair_unzip]. *)
Section TransProofs.

    (** [S (n + S m) = n + S (S m)], by a transparent fixpoint. *)
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

    (** [m + (1 + n) = 1 + (m + n)]. *)
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

    (** [(m + (1 + n)) + p = (1 + (m + n)) + p]. *)
    Definition nat_succ_p :
      forall (m n p : nat), (((m + (1 + n)) + p) = ((1 + (m + n)) + p))%nat.
    Proof.
      intros *.
      rewrite nat_succ.
      reflexivity.
    Defined.

    (** [n + 0 = n]. *)
    Lemma add_0_r : forall (n : nat), (n + 0 = n)%nat.
    Proof.
      induction n as [|n ihn].
      - reflexivity.
      - simpl. rewrite ihn. reflexivity.
    Defined.

    (** [n + S m = S (n + m)]. *)
    Lemma add_succ_r : forall (n m : nat), (n + S m = S (n + m))%nat.
    Proof.
      induction n as [|n ihn].
      - intro m. reflexivity.
      - intro m. simpl.
        rewrite ihn.
        reflexivity.
    Defined.

    (** Commutativity of addition. *)
    Theorem add_comm : forall (n m : nat), (n + m = m + n)%nat.
    Proof.
      induction n as [|n ihn].
      - intro m. simpl. rewrite add_0_r. reflexivity.
      - intro m. simpl. rewrite ihn. rewrite add_succ_r. reflexivity.
    Defined.

    (** Associativity of addition. *)
    Theorem add_assoc : ∀ (n m o : nat),
      (n + m + o = n + (m + o))%nat.
    Proof.
      induction n as [|n ihn].
      -
        simpl.
        reflexivity.
      -
        simpl; intros *.
        rewrite ihn.
        reflexivity.
    Defined.

    (** [n · 0 = 0]. *)
    Lemma mul_0_r : ∀ (n : nat), (n * 0 = 0)%nat.
    Proof.
      induction n as [|n ihn].
      - reflexivity.
      - simpl. rewrite ihn.
        reflexivity.
    Defined.

    (** [n · S m = n · m + n]. *)
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

    (** Commutativity of multiplication. *)
    Theorem mul_comm : forall (n m : nat), (n * m = m * n)%nat.
    Proof.
      induction n as [|n ihn];
      intro m.
      -
        simpl. rewrite mul_0_r.
        reflexivity.
      -
        simpl.
        rewrite ihn, mul_succ_r,
        add_comm;
        reflexivity.
    Defined.

    (** Left distributivity: [n · (m + o) = n · m + n · o]. *)
    Theorem add_mul_dist : forall (n m o : nat),
      (n * (m + o) = n * m + n * o)%nat.
    Proof.
      induction n as [|n ihn].
      -
        intros *.
        reflexivity.
      -
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

    (** [S (n + S m) = S (S (n + m))]. *)
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

    (** Transports a vector along a length equation [n = m] (a named
        [eq_rect]). *)
    Theorem subst_vector {A : Type} : forall {n m : nat},
      Vector.t A n -> n = m -> Vector.t A m.
    Proof.
      intros * u Ha.
      exact (@eq_rect nat n (Vector.t A) u m Ha).
    Defined.

    (** The quotient accumulator of [Nat.divmod] is additive:
        [fst (Nat.divmod x y q u) = q + fst (Nat.divmod x y 0 u)].  [Nat.div]
        is implemented with [Nat.divmod], so this lemma is what lets the
        following lemmas reason about [/ 2] by computation. *)
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

    (** A specific unfolding identity for [Nat.divmod] that arises when
        [cbn] reduces a division by [2] of a product of successors. *)
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

    (** Halving absorbs even summands: [(2n + m) / 2 = n + m / 2], phrased
        with [Nat.divmod]. *)
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

    (** [m + (m · n) / 2 = (m · (2 + n)) / 2]. *)
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

    (** [(1 + n) · n] is even: it equals [2k] for some [k]. *)
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

    (** [2n / 2 + 2n / 2 = 2n]. *)
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

    (** [((1 + n) · n) / 2 + ((1 + n) · n) / 2 = (1 + n) · n], since the
        product of consecutive numbers is even. *)
    Theorem nat_div_gen : ∀ (n : nat),
      (Nat.div ((1 + n) * n) 2 +  Nat.div ((1 + n) * n) 2)%nat =
      ((1 + n) * n)%nat.
    Proof.
      intros n.
      destruct (nat_div_even n) as (k & ha).
      rewrite !ha.
      eapply nat_div_adds.
    Defined.

    (** The instance of [nat_div_gen] at [n + 1]:
        [x / 2 + x / 2 = x] for [x = (2 + n)(1 + n)], twice the number of
        unordered pairs of [n + 2] elements. *)
    Definition nat_div_2 : ∀ (n : nat),
      (Nat.div ((2 + n) * (1 + n)) 2 +
      Nat.div ((2 + n) * (1 + n)) 2)%nat = ((2 + n) * (1 + n))%nat.
    Proof.
      intros *.
      specialize (nat_div_gen (S n)) as ha.
      change (1 + S n)%nat with (2 + n)%nat in ha.
      exact ha.
    Defined.
End TransProofs.

From Stdlib Require Import Vector Fin.
Import VectorNotations EqNotations.

(** ** All pairs of a vector

    [generate_pairs_of_vector] lists the [(n+2)(n+1)/2] unordered pairs
    [(gᵢ, gⱼ)] with [i < j] of a vector [g] of length [n+2].  The proof of
    the NEQ protocol in [Crypto/NeqSigma.v] needs two facts about it:
    every listed pair consists of entries at distinct positions
    ([generate_pairs_distinct]), and every pair of distinct positions
    occurs, in one orientation or the other ([generate_pairs_contains]).
    The [_triple] variants state the same thing for three vectors that are
    paired in lockstep (generators, bases and witnesses). *)
Section NeqUtil.

    (** The length equation behind the recursion of
        [generate_pairs_of_vector]: [m + (m · n)/2 = ((2 + n) · m)/2]
        (transparent). *)
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

    (** [generate_pairs_of_vector [g₀; g₁; …; g_{n+1}]] is
        [[(g₀, g₁); (g₀, g₂); …; (g₀, g_{n+1})] ++ generate_pairs_of_vector [g₁; …; g_{n+1}]],
        a vector of length [(2 + n)(1 + n)/2].  The append has length
        [(n+1) + (n+1)n/2], which is cast to the stated length along
        [generate_pairs_of_vector_proof]. *)
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
        set (reta := Vector.map (fun x => (gsh, x)) gst).
        specialize (generate_pairs_of_vector _ _ gst).
        refine(@eq_rect nat _ (Vector.t (A * A))
        (reta ++ generate_pairs_of_vector) _ _).
        eapply generate_pairs_of_vector_proof.
    Defined.

    (** [pair_unzip] flattens a vector of [n] two-element vectors into a vector
        of length [n + n]. *)
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

    (** [pair_zip] regroups a vector of length [n + n] into [n] consecutive
        two-element vectors; it inverts [pair_unzip] ([pair_zip_unzip_id]). *)
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

    (** [pair_zip (pair_unzip vs) = vs]. *)
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

    (** Indexing [zip_with]: [(zip_with f u v)[@i] = f u[@i] v[@i]]. *)
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

    (** Indexing [Vector.map]: [(map f v)[@i] = f v[@i]]. *)
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

    (** An index into [Fin.t (m + n)] lies either in the left part
        ([Fin.L n j]) or in the right part ([Fin.R m j]). *)
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

    (** Indexing a vector transported along [n = m] is indexing the original
        vector at the transported index. *)
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

    (** Injectivity of [Fin.FS]. *)
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

    (** Every pair listed by [generate_pairs_of_vector vs] consists of entries
        of [vs] at two distinct positions: if the [i]-th pair is [(v₁, v₂)]
        then [v₁ = vs[@j]] and [v₂ = vs[@k]] with [j ≠ k].  Induction on [n],
        splitting the index into the first block (pairs with the head) and the
        recursive block. *)
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
        (* Remove the length cast of the recursive definition; the two equality
           proofs are identified by [UIP_nat]. *)
        rewrite nth_rew in ha.
        assert (hc : hb = eq_sym e).
        eapply UIP_nat.
        setoid_rewrite <-hc in ha.
        clear e hc.
        remember (rew [Fin.t] hb in i) as i'.
        setoid_rewrite <-Heqi' in ha.
        clear Heqi' i hb.
        rename i' into i. cbn in ha.
        (* The index falls in the head block [(vsh, x)], giving positions [0] and
           [j + 1], or in the recursive block, where the induction hypothesis
           applies and both positions are shifted by one. *)
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

    (** Lockstep version of [generate_pairs_distinct] for three vectors
        [gs], [hs] and [xs] of the same length: the [i]-th pairs of all three
        come from the same two distinct positions [j ≠ k]. *)
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
        (* Same case split as in [generate_pairs_distinct], carried out for all
           three vectors at once. *)
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

    (** Moving a transport to the other side of an equation:
        [rew <- hb in ha = hc] implies [rew hb in hc = ha]. *)
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

    (** [vector_member v vs] tests membership of [v] in [vs] with the decidable
        equality [dec]. *)
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

    (** [vector_unique vs] tests that the entries of [vs] are pairwise
        distinct (quadratic, by repeated [vector_member]). *)
    Fixpoint vector_unique {A : Type} {dec : ∀ (x y : A), {x = y} + {x ≠ y}}
      {n : nat} (vs : Vector.t A n) : bool :=
      match vs with
      | [] => true
      | vsh :: vst  => negb (@vector_member _ dec _ vsh vst) &&
        @vector_unique _ dec _ vst
      end.

    (** If [vector_member v vs = true] then [v = vs[@i]] for some [i]. *)
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

    (** If [vector_member v vs = false] then [v] differs from every entry. *)
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

    (** Soundness of [vector_unique]: if it returns [true] then entries at
        distinct positions are distinct.  Stated for vectors of length at least
        [2]. *)
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
        (* Inductive case: the head is not a member of the tail, and the tail is
           unique by the induction hypothesis. *)
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

    (** Completeness of [vector_unique]: if it returns [false] then two
        distinct positions hold equal entries. *)
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

    (** Decidability of pairwise distinctness for vectors of length at least
        [2], computed by [vector_unique]. *)
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

    (** Completeness of [generate_pairs_of_vector]: for any two distinct
        positions [i ≠ j] there is an index [k] whose pair is
        [(vs[@i], vs[@j])] or [(vs[@j], vs[@i])].  The proof is long
        because the cast in [generate_pairs_of_vector] has to be removed
        explicitly at each step ([nth_rew], [UIP_nat], [rew_compose]). *)
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
        (* Base case [n = 0]: the only pair is [(vs[@0], vs[@1])]; enumerate the
           possible [i] and [j] by dependent matching. *)
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
        intros * ha.
        destruct (vector_inv_S vs) as (vsh & vst & hb).
        subst.
        (* Inductive case.  If [i] or [j] is the head, the pair lies in the head
           block at the position of the other index; otherwise use the induction
           hypothesis on the tail and shift into the recursive block. *)
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
          cbn in hd |- *.
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
          cbn in hd |- *.
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
          (* Both indices are in the tail: the induction hypothesis gives [kr], and
             the answer is [Fin.R (2+n) kr], cast to the stated length. *)
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

    (** Lockstep version of [generate_pairs_contains] for three vectors [gs],
        [hs] and [ys]: for [i ≠ j] a single index [k] picks out the pair at
        positions [(i, j)], or [(j, i)], in all three vectors simultaneously.
        This is the form used in [NeqSigma.v]. *)
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
        intros * ha.
        destruct (vector_inv_S gs) as (gsh & gst & hb).
        destruct (vector_inv_S hs) as (hsh & hst & hc).
        destruct (vector_inv_S ys) as (ysh & yst & hd).
        subst.
        (* Inductive case: the same three-way split as in
           [generate_pairs_contains], for all three vectors. *)
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
          cbn in hd |- *.
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (hsh, x)) hst)
          (generate_pairs_of_vector hst) j' as hd.
          cbn in hd |- *.
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : B, (ysh, x)) yst)
          (generate_pairs_of_vector yst) j' as hd.
          cbn in hd |- *.
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
          cbn in hd |- *.
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : A, (hsh, x)) hst)
          (generate_pairs_of_vector hst) i' as hd.
          cbn in hd |- *.
          rewrite hd; clear hd.
          pose proof @nth_append_L _ _ _ (map (λ x : B, (ysh, x)) yst)
          (generate_pairs_of_vector yst) i' as hd.
          cbn in hd |- *.
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
          (* Both indices are in the tails: use the induction hypothesis and shift
             into the recursive block. *)
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

(** ** Arithmetic modulo a prime

    Facts about [Z.modulo] for a prime modulus [p].  They are used by
    [Fermat.v] and [Zpstar.v] to show that the group operations stay in
    range. *)
Section Modutil.

  (** [p] is a prime ([Znumtheory.prime]). *)
  Context
      {p : Z}
      {Hp : prime p}.

  (** [p ≥ 2], [p > 0] and [p > 1]. *)
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

  (** [a mod b = a - b · (a / b)] for [b > 0]. *)
  Lemma mod_eq_custom :
    forall (a b : Z),
    (0 < b)%Z ->
    Z.modulo a b = (a - b * (a / b))%Z.
  Proof.
    intros a b Hb.
    rewrite Zmod_eq; nia.
  Qed.

  (** [w mod p = w] for [0 < w < p]. *)
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

  (** Canonical residues: [0 ≤ w < p ↔ w mod p = w].  This is the bridge
      between the range representation of [Z_p^*] and the canonical-form
      representation of [Z_p] in [Zpstar.v]. *)
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

  (** [m mod p ≠ 0] iff [m = k·p + w] for some [k] and [1 ≤ w < p]. *)
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

  (** Euclidean division by [p]: [m = k·p + w] with [0 ≤ w < p]. *)
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

  (** Euclidean division of a non-negative [m] by [p], with non-negative
      quotient [k]. *)
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

  (** Euclid's lemma on residues: for [1 ≤ w₁, w₂ < p],
      [(w₁ · w₂) mod p ≠ 0]. *)
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

  (** [w mod p ≠ 0] for [1 ≤ w < p]. *)
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

  (** The product of two integers that are nonzero modulo [p] is nonzero
      modulo [p]. *)
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

  (** For [1 ≤ x, y < p], [1 ≤ (x · y) mod p < p]. *)
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

  (** For [0 < x, y < p], [0 < (x · y) mod p < p]: [Z_p^*] is closed under
      multiplication.  Used in the definition of [mul_zpstar] and
      [mul_schnorr_group] in [Zpstar.v]. *)
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

  (** Congruence of a binary operation: from [a = b] and [c = d] infer
      [gop a c = gop b d].  A convenience for the Sigma-protocol proofs. *)
  Lemma rewrite_gop {G : Type} (gop : G -> G -> G) :
    forall a b c d : G,
    a = b -> c = d -> gop a c = gop b d.
  Proof.
    intros * Hab Hcd;
    subst;
    reflexivity.
  Qed.

End Modutil.

(** ** Enumerating finite indices

    Executable enumeration of [Fin.t n] and a boolean universal quantifier
    over it, used by the Schulze and approval-voting code to state and
    check per-candidate conditions. *)
Section FinEnum.

  Local Open Scope nat_scope.

  (** [fin_enum n] is the vector [[0; 1; …; n-1]] of all elements of
      [Fin.t n], in order. *)
  Fixpoint fin_enum (n : nat) : Vector.t (Fin.t n) n :=
    match n with
    | 0 => []
    | S n' => Fin.F1 :: Vector.map Fin.FS (fin_enum n')
    end.

  (** The [i]-th entry of [fin_enum n] is [i]. *)
  Lemma fin_enum_nth : ∀ (n : nat) (i : Fin.t n),
    Vector.nth (fin_enum n) i = i.
  Proof.
    induction n as [| n ihn]; intro i.
    + inversion i.
    + apply (Fin.caseS' i); cbn; [reflexivity | intro j].
      rewrite (Vector.nth_map _ _ j j eq_refl), ihn; reflexivity.
  Qed.

  (** [fin_idx i] is the numeric value of the index [i]. *)
  Definition fin_idx {n : nat} (i : Fin.t n) : nat := proj1_sig (Fin.to_nat i).

  (** [fin_of_nat_default i n] converts [i] to [Fin.t (S n)] if [i ≤ n], and
      returns [Fin.F1] otherwise. *)
  Definition fin_of_nat_default (i n : nat) : Fin.t (S n) :=
    match Fin.of_nat i (S n) with
    | inleft f => f
    | inright _ => Fin.F1
    end.

  (** If [Fin.of_nat i n] succeeds with [f], then [fin_idx f = i]. *)
  Lemma of_nat_idx : ∀ (n i : nat) (f : Fin.t n),
    Fin.of_nat i n = inleft f -> fin_idx f = i.
  Proof.
    induction n as [| n ihn]; intros i f h.
    + inversion f.
    + destruct i as [| i]; cbn in h.
      - inversion h; subst; reflexivity.
      - destruct (Fin.of_nat i n) as [f' | arg] eqn:he; [| inversion h].
        inversion h; subst. specialize (ihn _ _ he).
        unfold fin_idx in *; cbn.
        destruct (Fin.to_nat f') as [j hj]; cbn in *; lia.
  Qed.

  (** For [i ≤ n], [fin_of_nat_default i n] has value [i]. *)
  Lemma fin_of_nat_default_idx : ∀ (i n : nat), i <= n ->
    fin_idx (fin_of_nat_default i n) = i.
  Proof.
    intros i n hi; unfold fin_of_nat_default.
    destruct (Fin.of_nat i (S n)) as [f | [k hk]] eqn:he.
    + exact (of_nat_idx _ _ _ he).
    + lia.
  Qed.

  (** [forall_fin n f] checks the boolean predicate [f] on all of [Fin.t n]. *)
  Definition forall_fin (n : nat) (f : Fin.t n -> bool) : bool :=
    Vector.fold_right andb (Vector.map f (fin_enum n)) true.

  (** Specification: [forall_fin n f = true] iff [f i = true] for every
      [i : Fin.t n]. *)
  Lemma forall_fin_true : ∀ (n : nat) (f : Fin.t n -> bool),
    forall_fin n f = true <-> (∀ i : Fin.t n, f i = true).
  Proof.
    induction n as [| n ihn]; intro f; split; intro h.
    + intro i; inversion i.
    + reflexivity.
    + intro i; cbn in h; apply andb_true_iff in h; destruct h as [h1 h2].
      rewrite Vector.map_map in h2.
      apply (Fin.caseS' i); [exact h1 | intro j].
      exact (proj1 (ihn (fun j => f (Fin.FS j))) h2 j).
    + cbn; apply andb_true_iff; split; [exact (h Fin.F1) |].
      rewrite Vector.map_map.
      apply (proj2 (ihn (fun j => f (Fin.FS j)))); intro j; exact (h (Fin.FS j)).
  Qed.

  (** For [nat_to_F], [F] is any type with a zero, a one and an addition. *)
  Context {F : Type} (zero one : F) (add : F -> F -> F).

  (** [nat_to_F k = 1 + (1 + (… + 0))] with [k] ones: the image of the natural
      [k] in [F].  It is used to turn counts (for example vote counts) into
      field or exponent elements. *)
  Fixpoint nat_to_F (k : nat) : F :=
    match k with
    | 0 => zero
    | S k' => add one (nat_to_F k')
    end.

End FinEnum.
