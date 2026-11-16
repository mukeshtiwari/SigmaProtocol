(* The Terelius–Wikström proof of a shuffle (Terelius, Wikström, "Proofs of
   Restricted Shuffles", AFRICACRYPT 2010; Wikström, "A Commitment-Consistent
   Proof of a Shuffle", ACISP 2009), as implemented by the Verificatum
   mix-net, built from the library's generalised Okamoto protocol
   (Crypto/Okamoto.v).

   Setting. N + 1 ElGamal ciphertexts w are re-encrypted and permuted into
   w'. The prover has published a commitment u = (u_i) to the permutation
   matrix (u_i = g^{r_i} h_{π(i)} with independent generators h_i), the
   verifier has sent a random vector e, and the prover has published
   bridging commitments B_0..B_N with B_i = g^{β_i} B_{i-1}^{e'_i}, B_{-1} = h_0,
   where e' is the permutation of e. The verifier derives

     A = ∏ u_i^{e_i}     C = ∏ u_i / ∏ h_i     D = B_N · h_0^{−∏ e_i}
     F = ∏ w_i^{e_i}  (componentwise)

   and the prover then proves knowledge of (a, c, d, f, β, e') with

     A   = g^a · ∏ h_i^{e'_i}
     C   = g^c
     D   = g^d
     B_i = g^{β_i} · B_{i-1}^{e'_i}          (i = 0..N)
     F   = Enc(1; −f) · ∏ w'_i^{e'_i}        (Enc(1; r) = (g^r, pk^r))

   All five equations are linear in the witness once e is fixed, and the
   e'_i are shared between them, so they are one statement Y = ∏_j gs_j^{x_j}
   in the vector space

     V = G × G × G × G^{N+1} × (G × G)      (slots A, C, D, B, F)

   with the witness vector x = (a, c, d, f, β_0..β_N, e'_0..e'_N) and one
   base vector gs_j per witness coordinate. This file defines V, the bases
   and the target, proves that the multi-base relation unfolds to exactly
   the five equations (tw_relation_iff), and instantiates the generalised
   Okamoto protocol: its completeness, special soundness and honest-verifier
   zero knowledge are the library's theorems at V. Verificatum publishes the
   announcement, derives the challenge v by hashing, and publishes the
   response k = ω + v·x, which is exactly the library's transcript
   (announcement; v; k): the verifier's five equations Y^v · Y' = ∏ gs_j^{k_j}
   are the Okamoto acceptance test. The theorems about the whole five-move
   protocol (completeness of the derived witness, zero knowledge of the
   bridging chain, extraction of the permutation) are in Crypto/ShuffleTWProps.v. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List
  RelationClasses Morphisms.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto MultiExp.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

Section ShuffleTW.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.


  (* multi-exponentiation in G and in G × G *)
  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation cexp := (mexp (vid := (gid, gid)) (vadd := fun x y : G * G => (gop (fst x) (fst y), gop (snd x) (snd y)))
    (smul := fun (x : G * G) (r : F) => (gpow (fst x) r, gpow (snd x) r))).

  (* ---------------------------------------------------------------- *)
  (* Multi-exponentiation in G^m, coordinatewise                       *)
  (* ---------------------------------------------------------------- *)

  Local Notation gassoc := (@associative G (@eq G) gop (@monoid_is_associative G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv G (@eq G)
        gid ginv gop gpow Hvec))))).
  Local Notation gid_l := (@left_identity G (@eq G) gop gid (@monoid_is_left_idenity G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv G (@eq G)
        gid ginv gop gpow Hvec))))).
  Local Notation gid_r := (@right_identity G (@eq G) gop gid (@monoid_is_right_identity G (@eq G) gop gid
    (@group_monoid G (@eq G) gop gid ginv (@commutative_group_group G (@eq G) gop gid ginv
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv G (@eq G)
        gid ginv gop gpow Hvec))))).
  Local Notation ginv_l := (@left_inverse G (@eq G) gop gid ginv (@group_is_left_inverse G (@eq G) gop gid ginv
    (@commutative_group_group G (@eq G) gop gid ginv
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv G (@eq G)
        gid ginv gop gpow Hvec)))).
  Local Notation ginv_r := (@right_inverse G (@eq G) gop gid ginv (@group_is_right_inverse G (@eq G) gop gid ginv
    (@commutative_group_group G (@eq G) gop gid ginv
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv G (@eq G)
        gid ginv gop gpow Hvec)))).
  Local Notation gcomm := (@commutative G (@eq G) gop (@commutative_group_is_commutative G (@eq G) gop gid ginv
      (@vector_space_commutative_group F (@eq F) zero one add mul sub div opp inv G (@eq G)
        gid ginv gop gpow Hvec))).

  Section MExpVec.

    Local Notation vexp m := (mexp (vid := vec_id (V := G) (vid := gid) m)
      (vadd := vec_add (vadd := gop)) (smul := vec_smul (smul := gpow))).

    Lemma gid_pow : forall r : F, gid ^ r = gid.
    Proof. intro r; exact (smul_vid (HV := Hvec) r). Qed.

    (* a diagonal family of bases: base i has b_i at position i and the
      identity elsewhere *)
    Fixpoint diag {m : nat} (bs : Vector.t G m) : Vector.t (Vector.t G m) m :=
      match bs with
      | [] => []
      | b :: bs' => (b :: Vector.const gid _) :: Vector.map (fun v => gid :: v) (diag bs')
      end.

    Lemma mexp_map_cons : forall (m k : nat) (a : G) (gs : Vector.t (Vector.t G m) k) (xs : Vector.t F k),
      vexp (S m) (Vector.map (fun v => a :: v) gs) xs = gexp (Vector.const a k) xs :: vexp m gs xs.
    Proof.
      intros m k a; induction k as [| k ih]; intros gs xs.
      + rewrite (vector_inv_0 gs), (vector_inv_0 xs); reflexivity.
      + destruct (vector_inv_S gs) as (g & gs' & ->).
        destruct (vector_inv_S xs) as (x & xs' & ->).
        cbn [Vector.map]; rewrite const_S, !mexp_cons, ih.
        unfold vec_add, vec_smul; cbn [Vector.map Vector.map2]; reflexivity.
    Qed.

    Lemma mexp_diag : forall (m : nat) (bs : Vector.t G m) (xs : Vector.t F m),
      vexp m (diag bs) xs = Vector.map2 gpow bs xs.
    Proof.
      induction m as [| m ih]; intros bs xs.
      + rewrite (vector_inv_0 bs), (vector_inv_0 xs); reflexivity.
      + destruct (vector_inv_S bs) as (b & bs' & ->).
        destruct (vector_inv_S xs) as (x & xs' & ->).
        cbn [diag Vector.map2]; rewrite mexp_cons, mexp_map_cons, ih.
        rewrite (mexp_const_vid (HV := Hvec)).
        unfold vec_add, vec_smul; cbn [Vector.map]; rewrite !map2_cons.
        rewrite gid_r, map_const, gid_pow.
        f_equal.
        exact (vec_add_id_l (HV := Hvec) m (Vector.map2 gpow bs' xs')).
    Qed.

  End MExpVec.

  (* ---------------------------------------------------------------- *)
  (* The statement space V = G × G × G × G^{N+1} × (G × G)             *)
  (* ---------------------------------------------------------------- *)

  Context {N : nat}.
  Local Notation M := (S N).   (* number of ciphertexts *)

  Definition V : Type := (G * (G * (G * (Vector.t G M * (G * G)))))%type.

  (* the five components *)
  Definition cA (x : V) : G := fst x.
  Definition cC (x : V) : G := fst (snd x).
  Definition cD (x : V) : G := fst (snd (snd x)).
  Definition cB (x : V) : Vector.t G M := fst (snd (snd (snd x))).
  Definition cF (x : V) : G * G := snd (snd (snd (snd x))).

  (* the operations, by projections so that they compute on any term *)
  Definition Vid : V := (gid, (gid, (gid, (vec_id (vid := gid) M, (gid, gid))))).
  Definition Vopp (x : V) : V :=
    (ginv (cA x), (ginv (cC x), (ginv (cD x), (vec_opp (vopp := ginv) (cB x),
      (ginv (fst (cF x)), ginv (snd (cF x))))))).
  Definition Vadd (x y : V) : V :=
    (gop (cA x) (cA y), (gop (cC x) (cC y), (gop (cD x) (cD y), (vec_add (vadd := gop) (cB x) (cB y),
      (gop (fst (cF x)) (fst (cF y)), gop (snd (cF x)) (snd (cF y))))))).
  Definition Vsmul (x : V) (r : F) : V :=
    (cA x ^ r, (cC x ^ r, (cD x ^ r, (vec_smul (smul := gpow) (cB x) r,
      (fst (cF x) ^ r, snd (cF x) ^ r))))).

  Definition Vdec : forall x y : V, {x = y} + {x <> y}.
  Proof.
    intros (a1 & c1 & d1 & b1 & f1 & f1') (a2 & c2 & d2 & b2 & f2 & f2').
    destruct (Gdec a1 a2) as [-> | h]; [| right; intro e; apply h; congruence].
    destruct (Gdec c1 c2) as [-> | h]; [| right; intro e; apply h; congruence].
    destruct (Gdec d1 d2) as [-> | h]; [| right; intro e; apply h; congruence].
    destruct (vec_dec (V := G) Gdec b1 b2) as [-> | h]; [| right; intro e; apply h; congruence].
    destruct (Gdec f1 f2) as [-> | h]; [| right; intro e; apply h; congruence].
    destruct (Gdec f1' f2') as [-> | h]; [| right; intro e; apply h; congruence].
    left; reflexivity.
  Defined.

  Local Ltac V_law :=
    intros; repeat match goal with x : V |- _ => destruct x as (? & ? & ? & ? & ? & ?) end;
    unfold Vid, Vopp, Vadd, Vsmul, cA, cC, cD, cB, cF; cbn [fst snd];
    repeat match goal with |- (_, _) = (_, _) => f_equal end.

  (* the laws of V, componentwise *)
  Lemma Vadd_assoc : forall x y z : V, Vadd x (Vadd y z) = Vadd (Vadd x y) z.
  Proof. V_law; first [apply gassoc | apply (vec_add_assoc (HV := Hvec))]. Qed.
  Lemma Vadd_id_l : forall x : V, Vadd Vid x = x.
  Proof. V_law; first [apply gid_l | apply (vec_add_id_l (HV := Hvec))]. Qed.
  Lemma Vadd_id_r : forall x : V, Vadd x Vid = x.
  Proof. V_law; first [apply gid_r | apply (vec_add_id_r (HV := Hvec))]. Qed.
  Lemma Vadd_opp_l : forall x : V, Vadd (Vopp x) x = Vid.
  Proof. V_law; first [apply ginv_l | apply (vec_add_opp_l (HV := Hvec))]. Qed.
  Lemma Vadd_opp_r : forall x : V, Vadd x (Vopp x) = Vid.
  Proof. V_law; first [apply ginv_r | apply (vec_add_opp_r (HV := Hvec))]. Qed.
  Lemma Vadd_comm : forall x y : V, Vadd x y = Vadd y x.
  Proof. V_law; first [apply gcomm | apply (vec_add_comm (HV := Hvec))]. Qed.
  Lemma Vadd_proper : Proper (eq ==> eq ==> eq) Vadd.
  Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Vopp_proper : Proper (eq ==> eq) Vopp.
  Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Vsmul_proper : Proper (eq ==> eq ==> eq) Vsmul.
  Proof. repeat intro; subst; reflexivity. Qed.

  Lemma Vsmul_one : forall x : V, Vsmul x one = x.
  Proof.
    pose proof (@vector_space_field_one _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h.
    V_law; first [apply h | apply (vec_smul_one (HV := Hvec))].
  Qed.
  Lemma Vsmul_zero : forall x : V, Vsmul x zero = Vid.
  Proof.
    pose proof (@vector_space_field_zero _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h.
    V_law; first [apply h | apply (vec_smul_zero (HV := Hvec))].
  Qed.
  Lemma Vsmul_assoc : forall (r1 r2 : F) (x : V), Vsmul x (r1 * r2) = Vsmul (Vsmul x r1) r2.
  Proof.
    pose proof (@vector_space_smul_associative_fmul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h.
    V_law; first [apply h | apply (vec_smul_assoc (HV := Hvec))].
  Qed.
  Lemma Vsmul_fadd : forall (r1 r2 : F) (x : V), Vsmul x (r1 + r2) = Vadd (Vsmul x r1) (Vsmul x r2).
  Proof.
    pose proof (@vector_space_smul_distributive_fadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h.
    V_law; first [apply h | apply (vec_smul_fadd (HV := Hvec))].
  Qed.
  Lemma Vsmul_vadd : forall (r : F) (x y : V), Vsmul (Vadd x y) r = Vadd (Vsmul x r) (Vsmul y r).
  Proof.
    pose proof (@vector_space_smul_distributive_vadd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec) as h; hnf in h.
    V_law; first [apply h | apply (vec_smul_vadd (HV := Hvec))].
  Qed.

  Definition V_monoid : @monoid V (@eq V) Vadd Vid :=
    @Build_monoid V (@eq V) Vadd Vid Vadd_assoc Vadd_id_l Vadd_id_r Vadd_proper eq_equivalence.
  Definition V_group : @group V (@eq V) Vadd Vid Vopp :=
    @Build_group V (@eq V) Vadd Vid Vopp V_monoid Vadd_opp_l Vadd_opp_r Vopp_proper.
  Global Instance V_comm_group : @commutative_group V (@eq V) Vadd Vid Vopp :=
    @Build_commutative_group V (@eq V) Vadd Vid Vopp V_group Vadd_comm.

  Global Instance V_vspace :
    @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) Vid Vopp Vadd Vsmul :=
    @Build_vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) Vid Vopp Vadd Vsmul
      V_comm_group (@vector_space_field _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec)
      Vsmul_one Vsmul_zero Vsmul_assoc Vsmul_fadd Vsmul_vadd Vsmul_proper.

  Local Notation Vexp := (mexp (vid := Vid) (vadd := Vadd) (smul := Vsmul)).
  Local Notation vexp := (mexp (vid := vec_id (V := G) (vid := gid) M)
    (vadd := vec_add (vadd := gop)) (smul := vec_smul (smul := gpow))).

  (* the components of a product in V are the products of the components *)

  Lemma mexp_V_components : forall (k : nat) (gs : Vector.t V k) (xs : Vector.t F k),
    Vexp gs xs =
    (gexp (Vector.map cA gs) xs,
     (gexp (Vector.map cC gs) xs,
      (gexp (Vector.map cD gs) xs,
       (vexp (Vector.map cB gs) xs,
        cexp (Vector.map cF gs) xs)))).
  Proof.
    induction k as [| k ih]; intros gs xs.
    + rewrite (vector_inv_0 gs), (vector_inv_0 xs); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      cbn [Vector.map]; rewrite !mexp_cons, ih.
      destruct g as (a & c & d & b & f1 & f2); reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Public data, bases and target                                     *)
  (* ---------------------------------------------------------------- *)

  Record public : Type := mk_public {
    g : G;                          (* commitment generator *)
    h0 : G;                         (* B_{-1} *)
    hs : Vector.t G M;              (* independent generators h_0..h_N *)
    pk : G;                         (* ElGamal public key *)
    us : Vector.t G M;              (* permutation commitment *)
    es : Vector.t F M;              (* the verifier's first challenge *)
    Bs : Vector.t G M;              (* bridging commitments *)
    ws : Vector.t (G * G) M;        (* input ciphertexts *)
    ws' : Vector.t (G * G) M        (* output ciphertexts *)
  }.

  (* B_{i-1}: h_0 followed by B_0..B_{N-1} *)
  Definition Bprev (P : public) : Vector.t G M := Vector.shiftout (h0 P :: Bs P).

  Definition idB : Vector.t G M := vec_id (vid := gid) M.

  Definition baseA (P : public) : V := (g P, (gid, (gid, (idB, (gid, gid))))).
  Definition baseC (P : public) : V := (gid, (g P, (gid, (idB, (gid, gid))))).
  Definition baseD (P : public) : V := (gid, (gid, (g P, (idB, (gid, gid))))).
  Definition baseF (P : public) : V := (gid, (gid, (gid, (idB, (ginv (g P), ginv (pk P)))))).
  Definition basesB (P : public) : Vector.t V M :=
    Vector.map (fun v => (gid, (gid, (gid, (v, (gid, gid)))))) (diag (Vector.const (g P) M)).
  Definition basesE (P : public) : Vector.t V M :=
    Vector.map2 (fun '(hi, v) wi => (hi, (gid, (gid, (v, wi)))))
      (Vector.map2 pair (hs P) (diag (Bprev P))) (ws' P).

  (* the witness is (a, c, d, f, β_0..β_N, e'_0..e'_N) *)
  Local Notation nwit := (Nat.add 4 (Nat.add M M)).

  Definition bases (P : public) : Vector.t V nwit :=
    [baseA P; baseC P; baseD P; baseF P] ++ basesB P ++ basesE P.

  Definition witness (a c d f : F) (betas es' : Vector.t F M) : Vector.t F nwit :=
    [a; c; d; f] ++ betas ++ es'.

  Definition gprod {m : nat} (v : Vector.t G m) : G := Vector.fold_right gop v gid.
  Definition fprod {m : nat} (v : Vector.t F m) : F := Vector.fold_right mul v one.

  (* the derived statement A, C, D, B, F *)
  Definition target (P : public) : V :=
    (gexp (us P) (es P),
     (gop (gprod (us P)) (ginv (gprod (hs P))),
      (gop (Vector.last (Bs P)) (ginv ((h0 P) ^ (fprod (es P)))),
       (Bs P,
        cexp (ws P) (es P))))).

  (* ---------------------------------------------------------------- *)
  (* The relation, unfolded                                            *)
  (* ---------------------------------------------------------------- *)

  Lemma map_const_fun : forall {A B : Type} (b : B) (m : nat) (v : Vector.t A m),
    Vector.map (fun _ => b) v = Vector.const b m.
  Proof.
    intros A B b m; induction m as [| m ih]; intros v.
    + rewrite (vector_inv_0 v); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->); cbn; f_equal; apply ih.
  Qed.

  Lemma map_map2 : forall {A B C D : Type} (f : A -> B -> C) (h : C -> D) (m : nat)
    (v : Vector.t A m) (w : Vector.t B m),
    Vector.map h (Vector.map2 f v w) = Vector.map2 (fun a b => h (f a b)) v w.
  Proof.
    intros A B C D f h m; induction m as [| m ih]; intros v w.
    + rewrite (vector_inv_0 v), (vector_inv_0 w); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (b & w' & ->); cbn; f_equal; apply ih.
  Qed.

  Lemma map2_fst_pair : forall {A B : Type} (m : nat) (v : Vector.t A m) (w : Vector.t B m),
    Vector.map2 (fun a _ => a) v w = v.
  Proof.
    intros A B m; induction m as [| m ih]; intros v w.
    + rewrite (vector_inv_0 v), (vector_inv_0 w); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (b & w' & ->); cbn; f_equal; apply ih.
  Qed.

  Lemma map2_fst_gen : forall {A B C : Type} (h : A -> C) (m : nat) (v : Vector.t A m) (w : Vector.t B m),
    Vector.map2 (fun a _ => h a) v w = Vector.map h v.
  Proof.
    intros A B C h m; induction m as [| m ih]; intros v w.
    + rewrite (vector_inv_0 v), (vector_inv_0 w); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (b & w' & ->); cbn; f_equal; apply ih.
  Qed.

  Lemma map2_snd_pair : forall {A B : Type} (m : nat) (v : Vector.t A m) (w : Vector.t B m),
    Vector.map2 (fun _ b => b) v w = w.
  Proof.
    intros A B m; induction m as [| m ih]; intros v w.
    + rewrite (vector_inv_0 v), (vector_inv_0 w); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (b & w' & ->); cbn; f_equal; apply ih.
  Qed.

  Lemma map2_const : forall {A A' B : Type} (b : B) (m : nat) (v : Vector.t A m) (w : Vector.t A' m),
    Vector.map2 (fun _ _ => b) v w = Vector.const b m.
  Proof.
    intros A A' B b m; induction m as [| m ih]; intros v w.
    + rewrite (vector_inv_0 v), (vector_inv_0 w); reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (a' & w' & ->); cbn; f_equal; apply ih.
  Qed.

  (* the components of the bases *)
  Lemma bases_cA : forall P, Vector.map cA (bases P) = [g P; gid; gid; gid] ++ Vector.const gid M ++ hs P.
  Proof.
    intro P; unfold bases, cA; rewrite !Vector.map_append; f_equal; f_equal.
    + unfold basesB; rewrite Vector.map_map; cbn [fst snd]; apply map_const_fun.
    + unfold basesE; rewrite map_map2.
      erewrite Vector.map2_ext with (g := fun a _ => fst a).
      2: { intros [hi v] wi; reflexivity. }
      rewrite map2_fst_gen, map_map2; cbn [fst]. apply map2_fst_pair.
  Qed.

  Lemma bases_cC : forall P, Vector.map cC (bases P) = [gid; g P; gid; gid] ++ Vector.const gid M ++ Vector.const gid M.
  Proof.
    intro P; unfold bases, cC; rewrite !Vector.map_append; f_equal; f_equal.
    + unfold basesB; rewrite Vector.map_map; cbn [fst snd]; apply map_const_fun.
    + unfold basesE; rewrite map_map2.
      erewrite Vector.map2_ext with (g := fun _ _ => gid).
      2: { intros [hi v] wi; reflexivity. }
      apply map2_const.
  Qed.

  Lemma bases_cD : forall P, Vector.map cD (bases P) = [gid; gid; g P; gid] ++ Vector.const gid M ++ Vector.const gid M.
  Proof.
    intro P; unfold bases, cD; rewrite !Vector.map_append; f_equal; f_equal.
    + unfold basesB; rewrite Vector.map_map; cbn [fst snd]; apply map_const_fun.
    + unfold basesE; rewrite map_map2.
      erewrite Vector.map2_ext with (g := fun _ _ => gid).
      2: { intros [hi v] wi; reflexivity. }
      apply map2_const.
  Qed.

  Lemma bases_cB : forall P, Vector.map cB (bases P) =
    [idB; idB; idB; idB] ++ diag (Vector.const (g P) M) ++ diag (Bprev P).
  Proof.
    intro P; unfold bases, cB; rewrite !Vector.map_append; f_equal; f_equal.
    + unfold basesB; rewrite Vector.map_map; cbn [fst snd]; apply Vector.map_id.
    + unfold basesE; rewrite map_map2.
      erewrite Vector.map2_ext with (g := fun a _ => snd a).
      2: { intros [hi v] wi; reflexivity. }
      rewrite map2_fst_gen, map_map2; cbn [snd]. apply map2_snd_pair.
  Qed.

  Lemma bases_cF : forall P, Vector.map cF (bases P) =
    [(gid, gid); (gid, gid); (gid, gid); (ginv (g P), ginv (pk P))] ++ Vector.const (gid, gid) M ++ ws' P.
  Proof.
    intro P; unfold bases, cF; rewrite !Vector.map_append; f_equal; f_equal.
    + unfold basesB; rewrite Vector.map_map; cbn [fst snd]; apply map_const_fun.
    + unfold basesE; rewrite map_map2.
      erewrite Vector.map2_ext with (g := fun _ b => b).
      2: { intros [hi v] wi; reflexivity. }
      apply map2_snd_pair.
  Qed.

  (* the five equations *)
  Definition equations (P : public) (a c d f : F) (betas es' : Vector.t F M) : Prop :=
    gexp (us P) (es P) = gop (g P ^ a) (gexp (hs P) es') /\
    gop (gprod (us P)) (ginv (gprod (hs P))) = g P ^ c /\
    gop (Vector.last (Bs P)) (ginv (h0 P ^ fprod (es P))) = g P ^ d /\
    Bs P = Vector.map2 gop (Vector.map2 gpow (Vector.const (g P) M) betas)
                          (Vector.map2 gpow (Bprev P) es') /\
    cexp (ws P) (es P) = ((gop (ginv (g P) ^ f) (gexp (Vector.map fst (ws' P)) es')),
                          (gop (ginv (pk P) ^ f) (gexp (Vector.map snd (ws' P)) es'))).

  Lemma cexp_components : forall (m : nat) (cs : Vector.t (G * G) m) (xs : Vector.t F m),
    cexp cs xs = (gexp (Vector.map fst cs) xs, gexp (Vector.map snd cs) xs).
  Proof.
    induction m as [| m ih]; intros cs xs.
    + rewrite (vector_inv_0 cs), (vector_inv_0 xs); reflexivity.
    + destruct (vector_inv_S cs) as ([c1 c2] & cs' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      cbn [Vector.map]; rewrite !mexp_cons, ih; reflexivity.
  Qed.

  Lemma mexp_four : forall (g0 g1 g2 g3 : G) (a c d f : F),
    gexp [g0; g1; g2; g3] [a; c; d; f] = gop (g0 ^ a) (gop (g1 ^ c) (gop (g2 ^ d) (g3 ^ f))).
  Proof. intros; rewrite !mexp_cons, mexp_nil, gid_r; reflexivity. Qed.

  (* The multi-base relation is the conjunction of the five equations. *)
  Theorem tw_relation_iff : forall (P : public) (a c d f : F) (betas es' : Vector.t F M),
    target P = Vexp (bases P) (witness a c d f betas es') <-> equations P a c d f betas es'.
  Proof.
    intros *; unfold witness, equations, target.
    rewrite mexp_V_components, bases_cA, bases_cC, bases_cD, bases_cB, bases_cF.
    rewrite !(mexp_app (HV := Hvec)), !(mexp_app (HV := vec_vspace (HV := Hvec) M)).
    rewrite !cexp_components, !Vector.map_append; cbn [Vector.map].
    rewrite !(mexp_app (HV := Hvec)).
    rewrite !(mexp_const_vid (HV := Hvec)), !mexp_four, !gid_pow, !gid_l, !gid_r.
    rewrite (mexp_const_vid (HV := vec_vspace (HV := Hvec) M)), !mexp_diag.
    rewrite !map_const; cbn [fst snd].
    rewrite !(mexp_const_vid (HV := Hvec)), !gid_l.
    rewrite (vec_add_id_l (HV := Hvec)); unfold vec_add.
    split.
    + intro h; injection h as h1 h2 h3 h4 h5 h6.
      split; [exact h1 | split; [exact h2 | split; [exact h3 | split; [exact h4 |]]]].
      rewrite h5, h6; reflexivity.
    + intros (h1 & h2 & h3 & h4 & h5); injection h5 as h5 h6.
      rewrite h1, h2, h3, h4, h5, h6; reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The protocol: the generalised Okamoto protocol at V                *)
  (* ---------------------------------------------------------------- *)

  Local Notation nw := (Nat.add 2 (Nat.add M M)).   (* nwit = 2 + nw *)

  Definition tw_real_protocol (P : public) (x : Vector.t F nwit) (omega : Vector.t F nwit) (v : F) :
    @sigma_proto F V 1 1 nwit :=
    generalised_okamoto_real_protocol (add := add) (mul := mul) (gop := Vadd) (gpow := Vsmul)
      (gid := Vid) (n := nw) x (bases P) (target P) omega v.

  Definition tw_simulator (P : public) (k : Vector.t F nwit) (v : F) : @sigma_proto F V 1 1 nwit :=
    generalised_okamoto_simulator_protocol (opp := opp) (gid := Vid) (gop := Vadd) (gpow := Vsmul)
      (n := nw) (bases P) (target P) k v.

  (* Verificatum's verification of round 2: the five equations
    Y^v · Y' = ∏ gs_j^{k_j}, i.e. the Okamoto acceptance test at V *)
  Definition tw_verify (P : public) (t : @sigma_proto F V 1 1 nwit) : bool :=
    generalised_okamoto_accepting_conversation (gid := Vid) (gop := Vadd) (gpow := Vsmul) (Gdec := Vdec)
      (n := nw) (bases P) (target P) t.

  Theorem tw_completeness : forall (P : public) (a c d f : F) (betas es' : Vector.t F M)
    (omega : Vector.t F nwit) (v : F),
    equations P a c d f betas es' ->
    tw_verify P (tw_real_protocol P (witness a c d f betas es') omega v) = true.
  Proof.
    intros * he. apply tw_relation_iff in he.
    unfold tw_verify, tw_real_protocol.
    apply (generalised_okamoto_real_accepting_conversation (Hvec := V_vspace)); exact he.
  Qed.

  Theorem tw_special_soundness : forall (P : public) (Y' : V) (v1 v2 : F) (k1 k2 : Vector.t F nwit),
    v1 <> v2 ->
    tw_verify P (mk_sigma _ _ _ [Y'] [v1] k1) = true ->
    tw_verify P (mk_sigma _ _ _ [Y'] [v2] k2) = true ->
    exists x : Vector.t F nwit, target P = Vexp (bases P) x /\
      x = zip_with (fun r1 r2 => inv (v1 + opp v2) * (r1 + opp r2)) k1 k2.
  Proof.
    intros * hne h1 h2.
    destruct (generalised_okamoto_real_special_soundness (Hvec := V_vspace) nw (bases P) (target P)
      Y' v1 v2 k1 k2 hne h1 h2) as (x & hx & hx').
    exists x; split; [exact hx | exact hx'].
  Qed.

  Definition tw_real_distribution (P : public) (lf : list F) (Hlfn : lf <> List.nil)
    (x : Vector.t F nwit) (v : F) : dist (@sigma_proto F V 1 1 nwit) :=
    generalised_okamoto_real_distribution (add := add) (mul := mul) (gid := Vid) (gop := Vadd)
      (gpow := Vsmul) (n := nw) lf Hlfn x (bases P) (target P) v.

  Definition tw_simulator_distribution (P : public) (lf : list F) (Hlfn : lf <> List.nil) (v : F) :
    dist (@sigma_proto F V 1 1 nwit) :=
    generalised_okamoto_simulator_distribution (opp := opp) (gid := Vid) (gop := Vadd) (gpow := Vsmul)
      (n := nw) lf Hlfn (bases P) (target P) v.

  Theorem tw_special_honest_verifier_zkp_enum : forall (P : public) (lf : list F) (Hlfn : lf <> List.nil)
    (a c d f : F) (betas es' : Vector.t F M) (v : F),
    equations P a c d f betas es' ->
    List.NoDup lf -> (forall y : F, List.In y lf) ->
    Permutation
      (tw_real_distribution P lf Hlfn (witness a c d f betas es') v)
      (tw_simulator_distribution P lf Hlfn v).
  Proof.
    intros * he hnd hall. apply tw_relation_iff in he.
    apply (generalised_okamoto_special_honest_verifier_zkp_enum (Hvec := V_vspace)); assumption.
  Qed.

End ShuffleTW.
