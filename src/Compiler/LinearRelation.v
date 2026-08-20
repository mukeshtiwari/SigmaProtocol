From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import
  Util.
From ExtLib.Structures Require Import
  Monad.
From Crypto Require Import
  Sigma.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(*
  Generic Maurer / Cramer sigma protocol for linear relations.

  Statement: given a matrix of bases mat : Vector.t (Vector.t G n) m
  and a target vector pub : Vector.t G m, the prover knows
  xs : Vector.t F n such that

      ∀ j, pub[j] = Π_i mat[j][i] ^ xs[i].

  This single protocol generalizes Schnorr (m = n = 1),
  Okamoto (m = 1), Chaum-Pedersen / EqSigma (n = 1), and the
  Pedersen linear-relation protocol: it is the compilation target
  for every leaf statement of the compiler DSL.
*)
Section LinearRelation.

  (* Underlying Field of Vector Space *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}.

  (* Vector Element *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section Def.

    (* Evaluate one linear equation: Π_i row[i] ^ xs[i] *)
    Definition row_eval {n : nat}
      (row : Vector.t G n) (xs : Vector.t F n) : G :=
      Vector.fold_right gop (zip_with gpow row xs) gid.

    (* Evaluate the whole system of equations *)
    Definition mat_eval {m n : nat}
      (mat : Vector.t (Vector.t G n) m) (xs : Vector.t F n) :
      Vector.t G m :=
      Vector.map (fun row => row_eval row xs) mat.

    (*
      Identity-like matrix: row i has g in column i and gid in
      every other column.  Used to fold a per-witness family of
      equations (e.g. Pedersen commitments C_i = g^{v_i}·h^{r_i})
      into the single matrix form.
    *)
    Fixpoint diag_mat (n : nat) (g : G) :
      Vector.t (Vector.t G n) n :=
      match n with
      | 0 => []
      | S n' =>
        (g :: Vector.const gid n') ::
        Vector.map (fun row => gid :: row) (diag_mat n' g)
      end.

    (*
      Real transcript. us is the commitment randomness, c the
      challenge.
        commitment : mat_eval mat us
        response   : us + c · xs   (componentwise)
    *)
    Definition construct_linear_relation_real_proof {m n : nat}
      (mat : Vector.t (Vector.t G n) m)
      (xs us : Vector.t F n) (c : F) : @sigma_proto F G m 1 n :=
      (mat_eval mat us; [c];
        zip_with (fun u x => u + c * x) us xs).

    (*
      Simulated transcript (no witness). zs plays the role of the
      response; the commitment is computed backwards:
        commitment[j] : row_eval mat[j] zs · pub[j] ^ (- c)
    *)
    Definition construct_linear_relation_simulator_proof {m n : nat}
      (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (zs : Vector.t F n) (c : F) : @sigma_proto F G m 1 n :=
      (zip_with (fun row p => gop (row_eval row zs) (p ^ (opp c)))
        mat pub; [c]; zs).

    (*
      Verification: for every equation j,
        row_eval mat[j] response = commitment[j] · pub[j] ^ challenge
    *)
    Definition verify_linear_relation_proof {m n : nat}
      (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (pf : @sigma_proto F G m 1 n) : bool :=
      match pf with
      | (comm; cha; res) =>
        vector_forallb (fun '(row, (p, cm)) =>
          match Gdec (row_eval row res) (gop cm (p ^ (hd cha))) with
          | left _ => true
          | right _ => false
          end)
        (zip_with pair mat (zip_with pair pub comm))
      end.

    (* Real distribution: draw us uniformly, output real transcript *)
    Definition linear_relation_real_distribution {m n : nat}
      (lf : list F) (Hlfn : lf <> List.nil)
      (mat : Vector.t (Vector.t G n) m)
      (xs : Vector.t F n) (c : F) :
      dist (@sigma_proto F G m 1 n) :=
      us <- repeat_dist_ntimes_vector
        (uniform_with_replacement lf Hlfn) n ;;
      Ret (construct_linear_relation_real_proof mat xs us c).

    (* Simulator distribution: draw zs uniformly, simulate *)
    Definition linear_relation_simulator_distribution {m n : nat}
      (lf : list F) (Hlfn : lf <> List.nil)
      (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
      (c : F) : dist (@sigma_proto F G m 1 n) :=
      zs <- repeat_dist_ntimes_vector
        (uniform_with_replacement lf Hlfn) n ;;
      Ret (construct_linear_relation_simulator_proof mat pub zs c).

  End Def.

  Section Proofs.

    (* Verification success is equivalent to the per-equation
       group identities. *)
    Theorem verify_linear_relation_forward :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub comm : Vector.t G m) (c : F) (res : Vector.t F n),
      verify_linear_relation_proof mat pub (comm; [c]; res) = true ->
      ∀ (i : Fin.t m),
        row_eval (nth mat i) res = gop (nth comm i) ((nth pub i) ^ c).
    Proof.
      intros * ha i.
      unfold verify_linear_relation_proof in ha.
      rewrite vector_forallb_correct in ha.
      specialize (ha i).
      rewrite !nth_zip_with in ha.
      rewrite dec_true in ha.
      exact ha.
    Qed.

    Theorem verify_linear_relation_backward :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub comm : Vector.t G m) (c : F) (res : Vector.t F n),
      (∀ (i : Fin.t m),
        row_eval (nth mat i) res = gop (nth comm i) ((nth pub i) ^ c)) ->
      verify_linear_relation_proof mat pub (comm; [c]; res) = true.
    Proof.
      intros * ha.
      unfold verify_linear_relation_proof.
      rewrite vector_forallb_correct.
      intro i.
      rewrite !nth_zip_with, dec_true.
      exact (ha i).
    Qed.

    Context
      {Hvec : @vector_space F (@eq F) zero one add mul sub
        div opp inv G (@eq G) gid ginv gop gpow}.
    Add Field field : (@field_theory_for_stdlib_tactic F
      eq zero one opp add mul sub inv div vector_space_field).

    (* same as Okamoto.v / PedLinearRel.v; local copy to avoid
       importing those files just for this. *)
    Theorem gop_simp : ∀ (a b c d : G),
      gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
    Proof.
      intros *.
      rewrite <-!associative.
      setoid_rewrite commutative at 2.
      rewrite <-!associative.
      setoid_rewrite commutative at 3.
      reflexivity.
    Qed.

    Lemma row_eval_cons : ∀ (n : nat) (g : G) (row : Vector.t G n)
      (x : F) (xs : Vector.t F n),
      row_eval (g :: row) (x :: xs) = gop (g ^ x) (row_eval row xs).
    Proof.
      intros *.
      unfold row_eval; cbn.
      reflexivity.
    Qed.

    Lemma row_eval_nil : ∀ (row : Vector.t G 0) (xs : Vector.t F 0),
      row_eval row xs = gid.
    Proof.
      intros *.
      rewrite (vector_inv_0 row), (vector_inv_0 xs).
      reflexivity.
    Qed.

    (* row_eval is homomorphic in the response construction:
       evaluating at us + c · xs multiplies the evaluations. *)
    Lemma row_eval_response :
      ∀ (n : nat) (row : Vector.t G n) (us xs : Vector.t F n) (c : F),
      row_eval row (zip_with (fun u x => u + c * x) us xs) =
      gop (row_eval row us) ((row_eval row xs) ^ c).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 row), (vector_inv_0 us), (vector_inv_0 xs).
        unfold row_eval; cbn.
        rewrite vid_identity, left_identity.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S row) as (rh & rt & ha).
        destruct (vector_inv_S us) as (uh & ut & hb).
        destruct (vector_inv_S xs) as (xh & xt & hc).
        subst.
        specialize (ihn rt ut xt c).
        unfold row_eval in ihn |- *; cbn.
        rewrite ihn.
        assert (hd : uh + c * xh = uh + xh * c). field.
        rewrite hd; clear hd.
        rewrite smul_distributive_fadd,
          smul_associative_fmul,
          smul_distributive_vadd, gop_simp.
        reflexivity.
    Qed.

    (* row_eval applied to the extracted witness
       (z₁ - z₂) · k gives (eval z₁ · (eval z₂)⁻¹) ^ k. *)
    Lemma row_eval_sub_scale :
      ∀ (n : nat) (row : Vector.t G n) (zs₁ zs₂ : Vector.t F n) (k : F),
      row_eval row (zip_with (fun z₁ z₂ => (z₁ - z₂) * k) zs₁ zs₂) =
      (gop (row_eval row zs₁) (ginv (row_eval row zs₂))) ^ k.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 row), (vector_inv_0 zs₁), (vector_inv_0 zs₂).
        unfold row_eval; cbn.
        rewrite group_inv_id, left_identity, vid_identity.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S row) as (rh & rt & ha).
        destruct (vector_inv_S zs₁) as (zh₁ & zt₁ & hb).
        destruct (vector_inv_S zs₂) as (zh₂ & zt₂ & hc).
        subst.
        specialize (ihn rt zt₁ zt₂ k).
        unfold row_eval in ihn |- *; cbn.
        rewrite ihn.
        rewrite smul_associative_fmul.
        rewrite ring_sub_definition.
        rewrite smul_distributive_fadd.
        rewrite <-connection_between_vopp_and_fopp.
        rewrite <-smul_distributive_vadd.
        rewrite group_inv_flip.
        rewrite gop_simp.
        f_equal.
        f_equal.
        rewrite commutative.
        reflexivity.
    Qed.

    (* Structural lemmas about row_eval / mat_eval, used to fold
       block-structured statements (Pedersen commitments, public
       scalars in exponents) into the matrix form. *)

    Lemma row_eval_const_gid :
      ∀ (n : nat) (xs : Vector.t F n),
      row_eval (Vector.const gid n) xs = gid.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 xs).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S xs) as (xh & xt & ha); subst.
        specialize (ihn xt).
        unfold row_eval in ihn |- *; cbn.
        rewrite vid_identity, left_identity.
        exact ihn.
    Qed.

    Lemma row_eval_app :
      ∀ (n₁ n₂ : nat) (r₁ : Vector.t G n₁) (r₂ : Vector.t G n₂)
        (x₁ : Vector.t F n₁) (x₂ : Vector.t F n₂),
      row_eval (r₁ ++ r₂) (x₁ ++ x₂) =
      gop (row_eval r₁ x₁) (row_eval r₂ x₂).
    Proof.
      induction n₁ as [|n₁ ihn].
      +
        intros *.
        rewrite (vector_inv_0 r₁), (vector_inv_0 x₁).
        unfold row_eval; cbn.
        rewrite left_identity.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S r₁) as (rh & rt & ha).
        destruct (vector_inv_S x₁) as (xh & xt & hb).
        subst.
        specialize (ihn n₂ rt r₂ xt x₂).
        unfold row_eval in ihn |- *; cbn.
        rewrite ihn, associative.
        reflexivity.
    Qed.

    Lemma mat_eval_cons_col_gid :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (x : F) (xs : Vector.t F n),
      mat_eval (Vector.map (fun row => gid :: row) mat) (x :: xs) =
      mat_eval mat xs.
    Proof.
      induction m as [|m ihm].
      +
        intros *.
        rewrite (vector_inv_0 mat).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S mat) as (rh & rt & ha); subst.
        specialize (ihm n rt x xs).
        unfold mat_eval in ihm |- *; cbn.
        f_equal.
        ++
          unfold row_eval; cbn.
          rewrite vid_identity, left_identity.
          reflexivity.
        ++
          exact ihm.
    Qed.

    Lemma mat_eval_diag :
      ∀ (n : nat) (g : G) (xs : Vector.t F n),
      mat_eval (diag_mat n g) xs = Vector.map (gpow g) xs.
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 xs).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S xs) as (xh & xt & ha); subst.
        cbn; f_equal.
        ++
          pose proof (row_eval_const_gid n xt) as hb.
          unfold row_eval in hb |- *; cbn.
          rewrite hb, right_identity.
          reflexivity.
        ++
          pose proof (mat_eval_cons_col_gid n n (diag_mat n g) xh xt) as hb.
          specialize (ihn g xt).
          unfold mat_eval in hb, ihn |- *.
          rewrite hb, ihn.
          reflexivity.
    Qed.

    (* A public scalar coefficient α on a witness v folds into the
       base as g^α; a public scalar z on the right-hand side folds
       into the target as g^z.  This row realizes the linear
       constraint Σ αᵢ·vᵢ = z as the group equation
       Π (g^{αᵢ})^{vᵢ} = g^z. *)
    Lemma row_eval_pow_row :
      ∀ (n : nat) (g : G) (αs vs : Vector.t F n),
      row_eval (Vector.map (gpow g) αs) vs =
      g ^ (fold_right (fun '(α, v) acc => α * v + acc)
        (zip_with pair αs vs) zero).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        rewrite (vector_inv_0 αs), (vector_inv_0 vs).
        unfold row_eval; cbn.
        rewrite field_zero.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S αs) as (αh & αt & ha).
        destruct (vector_inv_S vs) as (vh & vt & hb).
        subst.
        specialize (ihn g αt vt).
        unfold row_eval in ihn |- *; cbn.
        rewrite smul_distributive_fadd, ihn.
        f_equal.
        rewrite <-smul_associative_fmul.
        reflexivity.
    Qed.

    Lemma mat_eval_app_rows :
      ∀ (m₁ m₂ n : nat) (M₁ : Vector.t (Vector.t G n) m₁)
        (M₂ : Vector.t (Vector.t G n) m₂) (xs : Vector.t F n),
      mat_eval (M₁ ++ M₂) xs = mat_eval M₁ xs ++ mat_eval M₂ xs.
    Proof.
      induction m₁ as [|m₁ ihm].
      +
        intros *.
        rewrite (vector_inv_0 M₁).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S M₁) as (rh & rt & ha); subst.
        specialize (ihm m₂ n rt M₂ xs).
        unfold mat_eval in ihm |- *; cbn.
        rewrite ihm.
        reflexivity.
    Qed.

    Lemma mat_eval_zip_app :
      ∀ (m n₁ n₂ : nat) (M₁ : Vector.t (Vector.t G n₁) m)
        (M₂ : Vector.t (Vector.t G n₂) m)
        (x₁ : Vector.t F n₁) (x₂ : Vector.t F n₂),
      mat_eval (zip_with (fun r₁ r₂ => r₁ ++ r₂) M₁ M₂) (x₁ ++ x₂) =
      zip_with gop (mat_eval M₁ x₁) (mat_eval M₂ x₂).
    Proof.
      induction m as [|m ihm].
      +
        intros *.
        rewrite (vector_inv_0 M₁), (vector_inv_0 M₂).
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S M₁) as (r₁h & r₁t & ha).
        destruct (vector_inv_S M₂) as (r₂h & r₂t & hb).
        subst.
        specialize (ihm n₁ n₂ r₁t r₂t x₁ x₂).
        unfold mat_eval in ihm |- *; cbn.
        rewrite ihm.
        f_equal.
        eapply row_eval_app.
    Qed.

    (* ------------------ Completeness ------------------ *)

    Theorem linear_relation_completeness :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) (xs us : Vector.t F n) (c : F),
      pub = mat_eval mat xs ->
      verify_linear_relation_proof mat pub
        (construct_linear_relation_real_proof mat xs us c) = true.
    Proof.
      intros * ha.
      unfold construct_linear_relation_real_proof.
      eapply verify_linear_relation_backward.
      intro i.
      rewrite row_eval_response.
      subst; unfold mat_eval.
      rewrite !(nth_map _ _ i i eq_refl).
      reflexivity.
    Qed.

    (* ------------------ Simulator correctness ------------------ *)

    Theorem linear_relation_simulator_completeness :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub : Vector.t G m) (zs : Vector.t F n) (c : F),
      verify_linear_relation_proof mat pub
        (construct_linear_relation_simulator_proof mat pub zs c) = true.
    Proof.
      intros *.
      unfold construct_linear_relation_simulator_proof.
      eapply verify_linear_relation_backward.
      intro i.
      rewrite !nth_zip_with.
      rewrite <-associative.
      rewrite <-smul_distributive_fadd.
      assert (ha : opp c + c = zero). field.
      rewrite ha, field_zero, right_identity.
      reflexivity.
    Qed.

    (* ------------------ Special soundness ------------------ *)

    Theorem linear_relation_special_soundness :
      ∀ (m n : nat) (mat : Vector.t (Vector.t G n) m)
        (pub comm : Vector.t G m) (c₁ c₂ : F)
        (res₁ res₂ : Vector.t F n),
      c₁ <> c₂ ->
      verify_linear_relation_proof mat pub (comm; [c₁]; res₁) = true ->
      verify_linear_relation_proof mat pub (comm; [c₂]; res₂) = true ->
      ∃ (xs : Vector.t F n), mat_eval mat xs = pub.
    Proof.
      intros * ha hb hc.
      pose proof (verify_linear_relation_forward _ _ _ _ _ _ _ hb) as hd.
      pose proof (verify_linear_relation_forward _ _ _ _ _ _ _ hc) as he.
      exists (zip_with (fun z₁ z₂ => (z₁ - z₂) * inv (c₁ - c₂))
        res₁ res₂).
      eapply eq_nth_iff.
      intros i j hij; subst.
      unfold mat_eval.
      rewrite !(nth_map _ _ j j eq_refl).
      rewrite row_eval_sub_scale.
      rewrite (hd j), (he j).
      rewrite group_inv_flip.
      rewrite gop_simp.
      setoid_rewrite commutative at 2;
      rewrite gop_simp, right_inverse, right_identity.
      rewrite commutative.
      rewrite connection_between_vopp_and_fopp.
      rewrite <-smul_distributive_fadd.
      rewrite <-smul_associative_fmul.
      assert (hf : (c₁ + opp c₂) * inv (c₁ - c₂) = one).
      field. intro hf. eapply ha.
      eapply f_equal with (f := fun x => x + c₂) in hf.
      rewrite left_identity in hf.
      rewrite <-hf. field.
      rewrite hf, field_one.
      reflexivity.
    Qed.

    (* ------------------ SHVZK ------------------ *)

    #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

    Lemma linear_relation_real_distribution_transcript_accepting_generic :
      ∀ (m n : nat) (l : dist (Vector.t F n))
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (xs : Vector.t F n) (trans : sigma_proto)
        (pr : prob) (c : F),
      pub = mat_eval mat xs ->
      List.In (trans, pr)
        (Bind l (λ us : Vector.t F n,
          Ret (construct_linear_relation_real_proof mat xs us c))) ->
      verify_linear_relation_proof mat pub trans = true.
    Proof.
      intros m n l.
      induction l as [|(a, p) l ihl].
      +
        intros * ha hb.
        cbn in hb.
        inversion hb.
      +
        intros * ha hb.
        cbn in hb.
        destruct hb as [hb | hb].
        ++
          inversion hb.
          eapply linear_relation_completeness;
          assumption.
        ++
          eapply ihl.
          exact ha.
          exact hb.
    Qed.

    Lemma linear_relation_real_distribution_transcript_probability_generic :
      ∀ (m n : nat) (l : dist (Vector.t F n))
        (mat : Vector.t (Vector.t G n) m)
        (xs : Vector.t F n) (trans : sigma_proto)
        (pr : prob) (c : F) (w : nat),
      (∀ (trx : Vector.t F n) (prx : prob),
        List.In (trx, prx) l -> prx = 1 / w) ->
      List.In (trans, pr)
        (Bind l (λ us : Vector.t F n,
          Ret (construct_linear_relation_real_proof mat xs us c))) ->
      pr = 1 / w.
    Proof.
      intros m n l.
      induction l as [|(a, p) l ihl].
      +
        intros * ha hb.
        cbn in hb.
        inversion hb.
      +
        intros * ha hb.
        pose proof (ha a p (or_introl eq_refl)) as hc.
        destruct hb as [hb | hb].
        ++
          inversion hb; subst; clear hb.
          unfold mul_prob, Prob.one; cbn.
          f_equal.
          nia.
        ++
          cbn in hb.
          eapply ihl.
          intros ? ? hd.
          exact (ha trx prx (or_intror hd)).
          exact hb.
    Qed.

    Lemma linear_relation_real_distribution_transcript_generic :
      ∀ (m n : nat) (lf : list F) (Hlf : lf <> List.nil)
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (xs : Vector.t F n) (a : sigma_proto) (b : prob) (c : F),
      pub = mat_eval mat xs ->
      List.In (a, b)
        (linear_relation_real_distribution lf Hlf mat xs c) ->
      verify_linear_relation_proof mat pub a = true ∧
      b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
    Proof.
      intros * ha hb.
      refine (conj _ _).
      +
        eapply linear_relation_real_distribution_transcript_accepting_generic.
        exact ha.
        exact hb.
      +
        eapply linear_relation_real_distribution_transcript_probability_generic.
        intros * hc.
        eapply uniform_probability_multidraw_prob.
        exact hc.
        exact hb.
    Qed.

    Lemma linear_relation_simulator_distribution_transcript_accepting_generic :
      ∀ (m n : nat) (l : dist (Vector.t F n))
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (trans : sigma_proto) (pr : prob) (c : F),
      List.In (trans, pr)
        (Bind l (λ zs : Vector.t F n,
          Ret (construct_linear_relation_simulator_proof mat pub zs c))) ->
      verify_linear_relation_proof mat pub trans = true.
    Proof.
      intros m n l.
      induction l as [|(a, p) l ihl].
      +
        intros * ha.
        cbn in ha.
        inversion ha.
      +
        intros * ha.
        cbn in ha.
        destruct ha as [ha | ha].
        ++
          inversion ha.
          eapply linear_relation_simulator_completeness.
        ++
          eapply ihl.
          exact ha.
    Qed.

    Lemma linear_relation_simulator_distribution_transcript_probability_generic :
      ∀ (m n : nat) (l : dist (Vector.t F n))
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (trans : sigma_proto) (pr : prob) (c : F) (w : nat),
      (∀ (trx : Vector.t F n) (prx : prob),
        List.In (trx, prx) l -> prx = 1 / w) ->
      List.In (trans, pr)
        (Bind l (λ zs : Vector.t F n,
          Ret (construct_linear_relation_simulator_proof mat pub zs c))) ->
      pr = 1 / w.
    Proof.
      intros m n l.
      induction l as [|(a, p) l ihl].
      +
        intros * ha hb.
        cbn in hb.
        inversion hb.
      +
        intros * ha hb.
        pose proof (ha a p (or_introl eq_refl)) as hc.
        destruct hb as [hb | hb].
        ++
          inversion hb; subst; clear hb.
          unfold mul_prob, Prob.one; cbn.
          f_equal.
          nia.
        ++
          cbn in hb.
          eapply ihl.
          intros ? ? hd.
          exact (ha trx prx (or_intror hd)).
          exact hb.
    Qed.

    Lemma linear_relation_simulator_distribution_transcript_generic :
      ∀ (m n : nat) (lf : list F) (Hlf : lf <> List.nil)
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (a : sigma_proto) (b : prob) (c : F),
      List.In (a, b)
        (linear_relation_simulator_distribution lf Hlf mat pub c) ->
      verify_linear_relation_proof mat pub a = true ∧
      b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
    Proof.
      intros * ha.
      refine (conj _ _).
      +
        eapply linear_relation_simulator_distribution_transcript_accepting_generic.
        exact ha.
      +
        eapply linear_relation_simulator_distribution_transcript_probability_generic.
        intros * hb.
        eapply uniform_probability_multidraw_prob.
        exact hb.
        exact ha.
    Qed.

    (* Special honest-verifier zero-knowledge: the real and the
       simulated distributions are identical (information-theoretic). *)
    Theorem linear_relation_special_honest_verifier_zkp :
      ∀ (m n : nat) (lf : list F) (Hlfn : lf <> List.nil)
        (mat : Vector.t (Vector.t G n) m) (pub : Vector.t G m)
        (xs : Vector.t F n) (c : F),
      pub = mat_eval mat xs ->
      List.map (fun '(a, p) =>
        (verify_linear_relation_proof mat pub a, p))
        (linear_relation_real_distribution lf Hlfn mat xs c) =
      List.map (fun '(a, p) =>
        (verify_linear_relation_proof mat pub a, p))
        (linear_relation_simulator_distribution lf Hlfn mat pub c).
    Proof.
      intros * ha.
      eapply map_ext_eq.
      +
        unfold linear_relation_real_distribution,
        linear_relation_simulator_distribution; cbn.
        repeat rewrite distribution_length.
        reflexivity.
      +
        intros (aa, cc, rr) y hb.
        eapply linear_relation_real_distribution_transcript_generic.
        exact ha.
        exact hb.
      +
        intros (aa, cc, rr) y hb.
        eapply linear_relation_simulator_distribution_transcript_generic.
        exact hb.
    Qed.

    (* ------------------ Instances ------------------ *)
    (*
      Sanity checks: the relations proven by the existing
      protocols in src/Crypto are instances of the generic
      linear relation.
    *)
    Section Instances.

      (* Schnorr (m = n = 1): ∃ x, h = g^x  (Sigma.v) *)
      Lemma schnorr_instance : ∀ (g h : G) (x : F),
        mat_eval [[g]] [x] = [h] <-> h = g ^ x.
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := Vector.hd) in ha; cbn in ha.
          rewrite right_identity in ha.
          subst; reflexivity.
        +
          subst; unfold mat_eval, row_eval; cbn.
          f_equal; rewrite right_identity;
          reflexivity.
      Qed.

      (* Okamoto (m = 1, n = 2): ∃ x₁ x₂, h = g₁^x₁ · g₂^x₂ *)
      Lemma okamoto_instance : ∀ (g₁ g₂ h : G) (x₁ x₂ : F),
        mat_eval [[g₁; g₂]] [x₁; x₂] = [h] <->
        h = gop (g₁ ^ x₁) (g₂ ^ x₂).
      Proof.
        intros *; split; intro ha.
        +
          eapply f_equal with (f := Vector.hd) in ha; cbn in ha.
          rewrite right_identity in ha.
          subst; reflexivity.
        +
          subst; unfold mat_eval, row_eval; cbn.
          f_equal; rewrite right_identity;
          reflexivity.
      Qed.

      (* Chaum-Pedersen / EqSigma (m = 2, n = 1):
         ∃ x, h₁ = g₁^x ∧ h₂ = g₂^x *)
      Lemma chaum_pedersen_instance : ∀ (g₁ g₂ h₁ h₂ : G) (x : F),
        mat_eval [[g₁]; [g₂]] [x] = [h₁; h₂] <->
        (h₁ = g₁ ^ x ∧ h₂ = g₂ ^ x).
      Proof.
        intros *; split; intro ha.
        +
          pose proof (f_equal Vector.hd ha) as hb; cbn in hb.
          eapply f_equal with (f := fun v => Vector.hd (Vector.tl v))
            in ha; cbn in ha.
          rewrite right_identity in ha, hb.
          subst; split; reflexivity.
        +
          destruct ha as (ha & hb).
          subst; unfold mat_eval, row_eval; cbn.
          repeat f_equal;
          try (rewrite right_identity; reflexivity).
      Qed.

      (*
        Pedersen linear relation (PedLinearRel.v):
          ∃ (vs, rs) : (∀ i, C_i = g^{v_i}·h^{r_i}) ∧ Σ αᵢ·vᵢ = z.

        As a linear relation over the witness vs ++ rs:
        - rows 1..n are the commitment equations, built from two
          diagonal blocks (g-block for vs, h-block for rs);
        - the last row realizes the *public-scalar* constraint by
          folding the public coefficients αᵢ into the bases (g^{αᵢ})
          and the public z into the target (g^z) — the same
          transformation the compiler will perform for any public
          scalar appearing in a statement.

        The first component of the right-hand side is definitionally
        PedLinearRel.pedersen_commitment_vector g h vs rs.
      *)
      Theorem pedersen_linear_relation_as_instance :
        ∀ (n : nat) (g h : G) (αs vs rs : Vector.t F n),
        mat_eval
          (zip_with (fun r₁ r₂ => r₁ ++ r₂) (diag_mat n g) (diag_mat n h) ++
            [Vector.map (gpow g) αs ++ Vector.const gid n])
          (vs ++ rs) =
        zip_with (fun v r => gop (g ^ v) (h ^ r)) vs rs ++
        [g ^ (fold_right (fun '(α, v) acc => α * v + acc)
          (zip_with pair αs vs) zero)].
      Proof.
        intros *.
        rewrite mat_eval_app_rows, mat_eval_zip_app.
        f_equal.
        +
          rewrite !mat_eval_diag.
          eapply eq_nth_iff.
          intros i j hij; subst.
          rewrite !nth_zip_with, !(nth_map _ _ j j eq_refl).
          reflexivity.
        +
          unfold mat_eval; cbn.
          f_equal.
          rewrite row_eval_app, row_eval_pow_row,
            row_eval_const_gid, right_identity.
          reflexivity.
      Qed.

    End Instances.
  End Proofs.
End LinearRelation.
