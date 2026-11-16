(* The simplified batched Schulze ballot. Everything is committed under one Pedersen key
   gs₁ of length m², and most checks are done by the verifier through the
   homomorphism instead of being proved:

     the differences δ = Ms are committed under the derived key
     g'_i = ∏_k g_k^{M_ki}, so that C_δ = com_{g'}(s; ρ_δ) = com_{gs₁}(Ms; ρ_δ)
     and δ = Ms holds by construction (com_gd);

     the bit vectors X^(t) of v = −δ + 2p − b are committed separately,
     and the verifier forms C₀ = C_δ · C_b · C_p^{-2} · ∏_t C_{X(t)}^{2^t},
     which the voter opens as a commitment to the zero vector, h₁^{ρ*};

     the three Hadamard checks (p = b ∘ δ, X^(t) ∈ {0,1}, b ∈ {0,1}) are one
     zero argument with L + 3 rows, weighted by powers of a challenge z.

   The linear argument (Crypto/LinearSigma.v) has five rows into G^5:
   C_δ, C_b, the two components of the link C_β = ∏ c_k^{β_k}, and C₀;
   its witness is (s, b, ρ_δ, ρ_b, R, ρ^{*}). Five challenges: β, y, z, c, x.

   This file: the definitions, the honest voter, completeness
   (ballot3_valid), the Fiat–Shamir form (nizk_ballot3_valid), special
   soundness (ballot3_sound) in the same rewinding form as
   Frontend/SchulzeBatched.v, reusing its extractors (beta_bits,
   decode_positions) and polynomial lemmas, and SHVZK (ballot3_zk). *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List Arith PeanoNat
  RelationClasses Morphisms.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space Product_space.
From Crypto Require Import Sigma MultiExp SigmaK PolyRoots BayerGroth BayerGrothSound BayerGrothZK LinearSigma Elgamal.
From Frontend Require Import Schulze SchulzeBatched.
From Utility Require Import Util.
Import ListNotations.

Section SchulzeSimple.

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
  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.

  Local Notation natF := (nat_to_F zero one add).
  Local Notation lscale := (lscale (mul := mul)).
  Local Notation ladd := (ladd (add := add)).
  Local Notation fsum := (fsum (zero := zero) (add := add)).
  Local Notation fpow := (fpow (one := one) (mul := mul)).
  Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).
  Local Notation gmexp := (lmexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation com := (com (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation com_list := (com_list (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation star := (star (zero := zero) (add := add) (mul := mul)).
  Local Notation star_w := (star_w (zero := zero) (add := add) (mul := mul)).
  Local Notation hmul := (hmul (mul := mul)).
  Local Notation zero_verify := (zero_verify (zero := zero) (one := one) (add := add) (mul := mul)
    (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation zero_prove := (zero_prove (zero := zero) (one := one) (add := add) (mul := mul)
    (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation zero_argument := (@zero_argument F G).
  Local Notation enc := (@enc F G gop gpow).
  Local Notation cmul := (Schulze.cmul (gop := gop)).
  Local Notation cpow := (Schulze.cpow (gpow := gpow)).
  Local Notation cid := (Schulze.cid (gid := gid)).
  Local Notation wslice := (wslice (zero := zero)).
  Local Notation wat := (wat (zero := zero)).
  Local Notation dot := (dot (zero := zero) (add := add) (mul := mul)).
  Local Notation pow2F := (pow2F (zero := zero) (one := one) (add := add)).
  Local Notation cneg := (cneg (zero := zero) (one := one) (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation cbeta := (cbeta (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation zero_accepts := (zero_accepts (zero := zero) (one := one) (add := add) (mul := mul)
    (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation binding_break := (binding_break (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation cdec := (Schulze.cdec (ginv := ginv) (gop := gop) (gpow := gpow)).

  (* group laws by name (typeclass search is unreliable with the product instances) *)
  Local Notation gop_assoc := (gop_assoc (Hvec := Hvec)).
  Local Notation gop_comm := (gop_comm (Hvec := Hvec)).
  Local Notation gop_gid_l := (gop_gid_l (Hvec := Hvec)).
  Local Notation gop_gid_r := (gop_gid_r (Hvec := Hvec)).
  Local Notation pow_add := (pow_add (Hvec := Hvec)).
  Local Notation pow_mul := (pow_mul (Hvec := Hvec)).
  Local Notation pow_zero := (pow_zero (Hvec := Hvec)).
  Local Notation pow_one := (pow_one (Hvec := Hvec)).
  Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
  Local Notation gop_rearrange := (gop_rearrange (Hvec := Hvec)).
  Local Notation enc_mul := (enc_mul (Hvec := Hvec)).
  Local Notation enc_pow := (enc_pow (Hvec := Hvec)).
  Local Notation com_add := (com_add (Hvec := Hvec)).
  Local Notation com_scale := (com_scale (Hvec := Hvec)).

  (* ---------------------------------------------------------------- *)
  (* the statement space G^5                                           *)
  (* ---------------------------------------------------------------- *)

  Definition G5vs := vec_vspace (HV := Hvec) 5.
  Definition vec5 (a b c d e : G) : Vector.t G 5 :=
    Vector.cons G a 4 (Vector.cons G b 3 (Vector.cons G c 2 (Vector.cons G d 1 (Vector.cons G e 0 (Vector.nil G))))).

  Lemma vec_add5 : forall a b c d e a' b' c' d' e',
    vec_add (vadd := gop) (vec5 a b c d e) (vec5 a' b' c' d' e') =
    vec5 (gop a a') (gop b b') (gop c c') (gop d d') (gop e e').
  Proof. reflexivity. Qed.
  Lemma vec_smul5 : forall a b c d e x,
    vec_smul (smul := gpow) (vec5 a b c d e) x = vec5 (a ^ x) (b ^ x) (c ^ x) (d ^ x) (e ^ x).
  Proof. reflexivity. Qed.
  Lemma vec5_inj : forall a b c d e a' b' c' d' e',
    vec5 a b c d e = vec5 a' b' c' d' e' -> a = a' /\ b = b' /\ c = c' /\ d = d' /\ e = e'.
  Proof.
    intros * H.
    pose proof (f_equal (fun v => Vector.nth v Fin.F1) H) as e1.
    pose proof (f_equal (fun v => Vector.nth v (Fin.FS Fin.F1)) H) as e2.
    pose proof (f_equal (fun v => Vector.nth v (Fin.FS (Fin.FS Fin.F1))) H) as e3.
    pose proof (f_equal (fun v => Vector.nth v (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) H) as e4.
    pose proof (f_equal (fun v => Vector.nth v (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) H) as e5.
    cbn in e1, e2, e3, e4, e5; repeat split; assumption.
  Qed.

  Local Notation lin_proof := (@lin_proof F (Vector.t G 5)).
  Local Notation lin_verify := (lin_verify (vadd := vec_add (vadd := gop)) (smul := vec_smul (smul := gpow))
    (Vdec := vec_dec Gdec (n := 5))).
  Local Notation lin_prove := (lin_prove (add := add) (mul := mul)).

  (* ---------------------------------------------------------------- *)
  (* list and polynomial helpers                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma fsum_add' : forall (f g : nat -> F) (k : nat),
    fsum (fun i => f i + g i) k = fsum f k + fsum g k.
  Proof. intros f g k; induction k as [| k ih]; cbn [SigmaK.fsum]; [field | rewrite ih; field]. Qed.

  Lemma fsum_scale' : forall (c : F) (f : nat -> F) (k : nat),
    fsum (fun i => c * f i) k = c * fsum f k.
  Proof. intros c f k; induction k as [| k ih]; cbn [SigmaK.fsum]; [field | rewrite ih; field]. Qed.

  Lemma lscale_length' : forall c xs, length (lscale c xs) = length xs.
  Proof. intros; unfold SigmaK.lscale; apply map_length. Qed.
  Lemma ladd_length' : forall xs ys, length xs = length ys -> length (ladd xs ys) = length xs.
  Proof. intros; unfold SigmaK.ladd; rewrite map_length, combine_length; lia. Qed.
  Lemma nth_lscale' : forall c xs i, (i < length xs)%nat -> nth i (lscale c xs) zero = c * nth i xs zero.
  Proof.
    intros c xs; induction xs as [| x xs ih]; intros i hi; [cbn in hi; lia |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.lscale map nth]; apply ih; cbn in hi; lia].
  Qed.
  Lemma nth_ladd' : forall xs ys i, length xs = length ys -> (i < length xs)%nat ->
    nth i (ladd xs ys) zero = nth i xs zero + nth i ys zero.
  Proof.
    induction xs as [| x xs ih]; intros ys i hl hi; [cbn in hi; lia |].
    destruct ys as [| y ys]; [discriminate |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.ladd combine map nth fst snd]; apply ih; cbn in *; lia].
  Qed.

  (* a fold over a mapped segment is a finite sum *)
  Lemma fold_map_seq : forall (f : nat -> F) (st k : nat),
    fold_right add zero (map f (seq st k)) = fsum (fun i => f (st + i)%nat) k.
  Proof.
    intros f st k; revert st; induction k as [| k ih]; intros st; [reflexivity |].
    cbn [seq map fold_right]; rewrite ih, (fsum_shift (Hvec := Hvec)), Nat.add_0_r.
    f_equal; apply fsum_ext; intros i hi; f_equal; lia.
  Qed.

  Lemma fold_combine_fsum : forall (y : F) (A B : list (list F)), length A = length B ->
    fold_right add zero (map (fun p => star y (fst p) (snd p)) (combine A B)) =
    fsum (fun i => star y (nth i A []) (nth i B [])) (length A).
  Proof.
    intros y A; induction A as [| a A ih]; intros B hl; [reflexivity |].
    destruct B as [| b B]; [discriminate |].
    cbn [combine map fold_right fst snd length nth].
    rewrite ih by (cbn in hl; lia). rewrite (fsum_shift (Hvec := Hvec)); cbn [nth]; reflexivity.
  Qed.

  Lemma combine_map_same : forall {A B C : Type} (f : A -> B) (g : A -> C) (l : list A),
    combine (map f l) (map g l) = map (fun a => (f a, g a)) l.
  Proof. intros; induction l as [| a l ih]; [reflexivity | cbn; rewrite ih; reflexivity]. Qed.

  Lemma com_list_map : forall (h : G) (gs : list G) {A : Type} (f : A -> list F) (g : A -> F) (l : list A),
    com_list h gs (map f l) (map g l) = map (fun a => com h gs (f a) (g a)) l.
  Proof. intros; unfold BayerGroth.com_list; rewrite combine_map_same, map_map; reflexivity. Qed.

  (* Horner evaluation of a mapped segment *)
  Lemma eval_map_seq : forall (c : nat -> F) (z : F) (st k : nat),
    eval (map c (seq st k)) z = fsum (fun j => fpow z j * c (st + j)%nat) k.
  Proof.
    intros c z st k; revert st; induction k as [| k ih]; intros st; [reflexivity |].
    cbn [seq map PolyRoots.eval]; rewrite ih, (fsum_shift (Hvec := Hvec)).
    cbn [SigmaK.fpow]; rewrite Nat.add_0_r, <-fsum_scale'; f_equal; [field |].
    apply fsum_ext; intros j hj; cbn [SigmaK.fpow]; replace (st + S j)%nat with (S st + j)%nat by lia; field.
  Qed.

  Lemma fpow_nonzero : forall (z : F) (k : nat), z <> zero -> fpow z k <> zero.
  Proof.
    intros z k hz; induction k as [| k ih]; cbn [SigmaK.fpow].
    + exact (Fone_neq_zero (Hvec := Hvec)).
    + intro e; destruct (mul_eq_zero (Fdec := Fdec) (Hf := vector_space_field) _ _ e); [exact (hz H) | exact (ih H)].
  Qed.

  Lemma com_zeros : forall (h : G) (gs : list G) (k : nat) (r : F), com h gs (repeat zero k) r = h ^ r.
  Proof. intros; unfold BayerGroth.com; rewrite (lmexp_repeat_zero (HV := Hvec)), gop_gid_r; reflexivity. Qed.

  Lemma com_rand_zero : forall (h : G) (gs : list G) (v : list F), com h gs v zero = gmexp gs v.
  Proof. intros; unfold BayerGroth.com; rewrite pow_zero, gop_gid_l; reflexivity. Qed.

  Lemma list_as_map_nth : forall (l : list F), l = map (fun i => nth i l zero) (seq 0 (length l)).
  Proof.
    intros l; apply (nth_ext _ _ zero zero); [rewrite map_length, seq_length; reflexivity |].
    intros i hi; rewrite nth_map_seq by exact hi; reflexivity.
  Qed.

  (* Σ_{t<k} c(st+t) · V(st+t), as a vector of length len *)
  Fixpoint lincomb (len : nat) (c : nat -> F) (V : nat -> list F) (st k : nat) : list F :=
    match k with
    | 0 => repeat zero len
    | S k' => ladd (lscale (c st) (V st)) (lincomb len c V (S st) k')
    end.

  Lemma lincomb_length : forall len c V st k, (forall t, (st <= t < st + k)%nat -> length (V t) = len) ->
    length (lincomb len c V st k) = len.
  Proof.
    intros len c V st k; revert st; induction k as [| k ih]; intros st hV; cbn [lincomb].
    + apply repeat_length.
    + assert (hl2 : length (lincomb len c V (S st) k) = len) by (apply ih; intros t ht; apply hV; lia).
      rewrite ladd_length', lscale_length'; [apply hV; lia | rewrite lscale_length', hl2; apply hV; lia].
  Qed.

  Lemma nth_lincomb : forall len c V st k j, (j < len)%nat -> (forall t, (st <= t < st + k)%nat -> length (V t) = len) ->
    nth j (lincomb len c V st k) zero = fsum (fun t => c (st + t)%nat * nth j (V (st + t)%nat) zero) k.
  Proof.
    intros len c V st k; revert st; induction k as [| k ih]; intros st j hj hV; cbn [lincomb].
    + apply nth_repeat.
    + assert (hl1 : length (lscale (c st) (V st)) = len) by (rewrite lscale_length'; apply hV; lia).
      assert (hl2 : length (lincomb len c V (S st) k) = len) by (apply lincomb_length; intros t ht; apply hV; lia).
      rewrite nth_ladd' by (rewrite hl1, ?hl2; lia).
      rewrite nth_lscale' by (rewrite hV; lia).
      rewrite ih by (try lia; intros t ht; apply hV; lia).
      rewrite (fsum_shift (Hvec := Hvec)), Nat.add_0_r; f_equal.
      apply fsum_ext; intros t ht; replace (st + S t)%nat with (S st + t)%nat by lia; reflexivity.
  Qed.

  (* ∏_t com(V t; r t)^{c t} = com(Σ_t c t · V t; Σ_t c t · r t) *)
  Lemma com_lincomb : forall (h : G) (gs : list G) (len : nat) (c r : nat -> F) (V : nat -> list F) (st k : nat),
    (forall t, (st <= t < st + k)%nat -> length (V t) = len) ->
    gmexp (map (fun t => com h gs (V t) (r t)) (seq st k)) (map c (seq st k)) =
    com h gs (lincomb len c V st k) (fsum (fun t => c (st + t)%nat * r (st + t)%nat) k).
  Proof.
    intros h gs len c r V st k; revert st; induction k as [| k ih]; intros st hV.
    + cbn [seq map lincomb SigmaK.fsum]; rewrite lmexp_nil_l, com_zeros, pow_zero; reflexivity.
    + cbn [seq map lincomb]; rewrite lmexp_cons, ih by (intros t ht; apply hV; lia).
      rewrite <-com_scale, (fsum_shift (Hvec := Hvec)), Nat.add_0_r.
      rewrite <-com_add by (rewrite lscale_length', lincomb_length; [apply hV; lia | intros t ht; apply hV; lia]).
      f_equal; f_equal; apply fsum_ext; intros t ht; replace (st + S t)%nat with (S st + t)%nat by lia; reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* the ballot                                                        *)
  (* ---------------------------------------------------------------- *)

  Section Ballot3.

    (* m = S n candidates, L bits per difference, keys: the election key
       (g, h), the commitment key (h1, gs1) of length K = m² *)
    Context {n : nat} (L : nat) (g h h1 : G) (gs1 : list G).
    Local Notation m := (S n).
    Local Notation K := (SchulzeBatched.K (n := n)).
    Local Notation hon_s := (hon_s (zero := zero) (one := one) (add := add)).
    Local Notation hon_d := (hon_d (zero := zero) (one := one) (add := add) (sub := sub) (n := n)).
    Local Notation hon_b := (hon_b (zero := zero) (one := one) (add := add) (n := n)).
    Local Notation hon_p := (hon_p (zero := zero) (one := one) (add := add) (mul := mul) (sub := sub) (n := n)).
    Local Notation pos_bit := (pos_bit (n := n)).
    Local Notation pos_v := (pos_v (n := n)).
    Local Notation vbits := (vbits (zero := zero) (one := one) (add := add) (mul := mul) (n := n) L).
    Local Notation posn := (posn (zero := zero) (one := one) (Fdec := Fdec) (n := n) L).
    Local Notation differ_at := (differ_at (zero := zero) (n := n)).
    Local Notation K_pos := (K_pos (n := n)).
    Local Notation kdm_lt := (kdm_lt (n := n)).
    Local Notation hon_s_length := (hon_s_length (zero := zero) (one := one) (add := add) (n := n)).
    Local Notation hon_b_length := (hon_b_length (zero := zero) (one := one) (add := add) (n := n)).
    Local Notation hon_d_length := (hon_d_length (zero := zero) (one := one) (add := add) (sub := sub) (n := n)).
    Local Notation hon_p_length := (hon_p_length (zero := zero) (one := one) (add := add) (mul := mul) (sub := sub) (n := n)).
    Local Notation nth_hon_s := (nth_hon_s (zero := zero) (one := one) (add := add)).
    Local Notation nth_hon_b := (nth_hon_b (zero := zero) (one := one) (add := add) (n := n)).
    Local Notation nth_hon_d := (nth_hon_d (zero := zero) (one := one) (add := add) (sub := sub) (n := n)).
    Local Notation nth_hon_p := (nth_hon_p (zero := zero) (one := one) (add := add) (mul := mul) (sub := sub) (n := n)).

    (* witness layout: s | b | ρ_δ ρ_b R ρ* *)
    Definition oB3 : nat := m.
    Definition oR3 : nat := (m + K)%nat.
    Definition W3 : nat := (oR3 + 4)%nat.
    Definition R : nat := (L + 3)%nat.

    (* the difference matrix M: row k = (i, j) (k = i·m + j) is e_j − e_i *)
    Definition mcoef (k i : nat) : F :=
      (if Nat.eqb (k mod m) i then one else zero) - (if Nat.eqb (k / m) i then one else zero).
    Definition mcol (i : nat) : list F := map (fun k => mcoef k i) (seq 0 K).
    Definition Ms (s : list F) : list F :=
      map (fun k => nth (k mod m) s zero - nth (k / m) s zero) (seq 0 K).
    (* the derived position key g'_i = ∏_k g_k^{M_ki} *)
    Definition gd : list G := map (fun i => gmexp gs1 (mcol i)) (seq 0 m).

    (* the exponents 2^t and C₀ = C_δ · C_b · C_p^{-2} · ∏_t C_{X(t)}^{2^t} *)
    Definition pows2 : list F := map pow2F (seq 0 L).
    Definition C0 (Cd Cb Cp : G) (CX : list G) : G :=
      gop (gop Cd Cb) (gop (Cp ^ (opp (one + one))) (gmexp CX pows2)).

    (* the statement of the linear proof as a function of the witness *)
    Definition phi3 (beta : list F) (w : list F) : Vector.t G 5 :=
      vec5 (com h1 gd (wslice w 0 m) (wat w oR3))
           (com h1 gs1 (wslice w oB3 K) (wat w (oR3 + 1)))
           (g ^ wat w (oR3 + 2))
           (gop (g ^ dot beta (wslice w oB3 K) K) (h ^ wat w (oR3 + 2)))
           (h1 ^ wat w (oR3 + 3)).

    Record ballot3 : Type := mk_ballot3 {
      b3_cs : list (G * G);
      b3_Cd : G; b3_Cb : G; b3_Cp : G; b3_CX : list G;
      b3_lin : lin_proof;
      b3_z : zero_argument }.

    Record chal3 : Type := mk_chal3 { c3_beta : list F; c3_y : F; c3_z : F; c3_c : F; c3_x : F }.

    Definition target3 (beta : list F) (bt : ballot3) : Vector.t G 5 :=
      let cb := cbeta beta (b3_cs bt) in
      vec5 (b3_Cd bt) (b3_Cb bt) (fst cb) (snd cb) (C0 (b3_Cd bt) (b3_Cb bt) (b3_Cp bt) (b3_CX bt)).

    (* the rows of the zero argument, weighted by powers of z:
         row 0:     z·b        against δ
         row 1:     z·p        against −1
         row 2+t:   z^{2+t}·X(t) against X(t) − 1   (t < L)
         row 2+L:   z^{2+L}·b  against b − 1 *)
    Definition zwt (z : F) (i : nat) : F := match i with 0 | 1 => z | _ => fpow z i end.
    Definition baseA (bt : ballot3) (i : nat) : G :=
      match i with
      | 0 => b3_Cb bt
      | 1 => b3_Cp bt
      | S (S t) => if Nat.ltb t L then nth t (b3_CX bt) gid else b3_Cb bt
      end.
    Definition rowA (z : F) (bt : ballot3) (i : nat) : G := baseA bt i ^ zwt z i.
    Definition rowB (bt : ballot3) (i : nat) : G :=
      match i with
      | 0 => b3_Cd bt
      | 1 => cneg h1 gs1 K
      | S (S t) => gop (baseA bt i) (cneg h1 gs1 K)
      end.
    Definition zA (z : F) (bt : ballot3) : list G := map (rowA z bt) (seq 0 R).
    Definition zB (bt : ballot3) : list G := map (rowB bt) (seq 0 R).

    Definition verify_ballot3 (ch : chal3) (bt : ballot3) : bool :=
      (Nat.eqb (length (b3_cs bt)) K) && (Nat.eqb (length (b3_CX bt)) L) &&
      lin_verify W3 (phi3 (c3_beta ch)) (target3 (c3_beta ch) bt) (c3_c ch) (b3_lin bt) &&
      zero_verify h1 gs1 (zA (c3_z ch) bt) (zB bt) (c3_y ch) (c3_x ch) (b3_z bt).

    (* the ciphertexts as the m × m matrix of Frontend/Schulze.v, for aggregation *)
    Definition ballot3_bits (bt : ballot3) : Vector.t (Vector.t (G * G) m) m :=
      Vector.map (fun i => Vector.map (fun j =>
        nth (fin_idx i * m + fin_idx j) (b3_cs bt) cid) (fin_enum m)) (fin_enum m).

    (* ---------------------------------------------------------------- *)
    (* the derived key                                                   *)
    (* ---------------------------------------------------------------- *)

    Lemma mcol_length : forall i, length (mcol i) = K.
    Proof. intros; unfold mcol; rewrite map_length, seq_length; reflexivity. Qed.
    Lemma Ms_length : forall s, length (Ms s) = K.
    Proof. intros; unfold Ms; rewrite map_length, seq_length; reflexivity. Qed.
    Lemma nth_Ms : forall s k, (k < K)%nat -> nth k (Ms s) zero = nth (k mod m) s zero - nth (k / m) s zero.
    Proof. intros; unfold Ms; rewrite nth_map_seq by assumption; reflexivity. Qed.

    Lemma fsum_indicator : forall (f : nat -> F) (i len : nat), (i < len)%nat ->
      fsum (fun j => f j * (if Nat.eqb i j then one else zero)) len = f i.
    Proof.
      intros f i len hi.
      rewrite (fsum_single (Hvec := Hvec) _ i len hi).
      + rewrite Nat.eqb_refl; field.
      + intros j hj hji; rewrite (proj2 (Nat.eqb_neq i j)) by lia; field.
    Qed.

    Lemma lincomb_mcol : forall s, length s = m ->
      lincomb K (fun i => nth i s zero) mcol 0 m = Ms s.
    Proof.
      intros s hs; apply (nth_ext _ _ zero zero).
      + rewrite lincomb_length, Ms_length; [reflexivity | intros; apply mcol_length].
      + intros k hk; rewrite lincomb_length in hk by (intros; apply mcol_length).
        rewrite nth_lincomb by (try exact hk; intros; apply mcol_length).
        rewrite nth_Ms by exact hk; destruct (kdm_lt k hk) as (hd & hm).
        rewrite (fsum_ext _ (fun i => nth i s zero * (if Nat.eqb (k mod m) i then one else zero) +
          opp one * (nth i s zero * (if Nat.eqb (k / m) i then one else zero))));
          [| intros i hi; unfold mcol; rewrite nth_map_seq by exact hk; unfold mcoef; cbn [Nat.add]; field].
        rewrite fsum_add', fsum_scale', !fsum_indicator by assumption; field.
    Qed.

    (* com_{g'}(s; ρ) = com_{gs₁}(Ms; ρ) *)
    Lemma com_gd : forall s rho, length s = m -> com h1 gd s rho = com h1 gs1 (Ms s) rho.
    Proof.
      intros s rho hs; unfold BayerGroth.com at 1; unfold gd.
      transitivity (gop (h1 ^ rho) (gmexp (map (fun i => com h1 gs1 (mcol i) zero) (seq 0 m))
        (map (fun i => nth i s zero) (seq 0 m)))).
      { f_equal; f_equal.
        + apply map_ext; intros i; rewrite com_rand_zero; reflexivity.
        + rewrite <-hs; apply list_as_map_nth. }
      rewrite (com_lincomb h1 gs1 K) by (intros; apply mcol_length).
      rewrite lincomb_mcol by exact hs.
      rewrite (fsum_ext _ (fun _ => zero)) by (intros j hj; cbn beta; field).
      rewrite (fsum_zero (Hf := vector_space_field)), com_rand_zero; reflexivity.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* linearity of phi3                                                 *)
    (* ---------------------------------------------------------------- *)

    Lemma wslice_ladd3 : forall w w' off len, length w = W3 -> length w' = W3 -> (off + len <= W3)%nat ->
      wslice (ladd w w') off len = ladd (wslice w off len) (wslice w' off len).
    Proof.
      intros * hw hw' hl; unfold SchulzeBatched.wslice.
      rewrite ladd_map; apply map_ext_in; intros i hi; apply in_seq in hi.
      apply nth_ladd'; lia.
    Qed.
    Lemma wslice_lscale3 : forall c w off len, length w = W3 -> (off + len <= W3)%nat ->
      wslice (lscale c w) off len = lscale c (wslice w off len).
    Proof.
      intros * hw hl; unfold SchulzeBatched.wslice.
      rewrite lscale_map; apply map_ext_in; intros i hi; apply in_seq in hi.
      apply nth_lscale'; lia.
    Qed.
    Lemma wat_ladd3 : forall w w' i, length w = W3 -> length w' = W3 -> (i < W3)%nat ->
      wat (ladd w w') i = wat w i + wat w' i.
    Proof. intros; unfold SchulzeBatched.wat; apply nth_ladd'; lia. Qed.
    Lemma wat_lscale3 : forall c w i, length w = W3 -> (i < W3)%nat -> wat (lscale c w) i = c * wat w i.
    Proof. intros; unfold SchulzeBatched.wat; apply nth_lscale'; lia. Qed.
    Lemma dot_ladd3 : forall beta u v k, length u = k -> length v = k ->
      dot beta (ladd u v) k = dot beta u k + dot beta v k.
    Proof.
      intros * hu hv; unfold SchulzeBatched.dot; rewrite <-fsum_add'; apply fsum_ext; intros i hi.
      rewrite nth_ladd' by lia; field.
    Qed.
    Lemma dot_lscale3 : forall beta c u k, length u = k -> dot beta (lscale c u) k = c * dot beta u k.
    Proof.
      intros * hu; unfold SchulzeBatched.dot; rewrite <-fsum_scale'; apply fsum_ext; intros i hi.
      rewrite nth_lscale' by lia; field.
    Qed.

    Lemma W3_offsets : (0 + m <= W3 /\ oB3 + K <= W3 /\ oR3 + 3 < W3)%nat.
    Proof. unfold W3, oR3, oB3; lia. Qed.

    Lemma phi3_add : forall beta w w', length w = W3 -> length w' = W3 ->
      phi3 beta (ladd w w') = vec_add (vadd := gop) (phi3 beta w) (phi3 beta w').
    Proof.
      intros * hw hw'; destruct W3_offsets as (ho1 & ho2 & ho3).
      unfold phi3; rewrite vec_add5.
      rewrite !wslice_ladd3 by lia. rewrite !wat_ladd3 by lia. rewrite !dot_ladd3 by apply wslice_length.
      rewrite !com_add by (rewrite !wslice_length; reflexivity). rewrite !pow_add.
      f_equal. apply gop_rearrange.
    Qed.

    Lemma phi3_scale : forall beta c w, length w = W3 ->
      phi3 beta (lscale c w) = vec_smul (smul := gpow) (phi3 beta w) c.
    Proof.
      intros * hw; destruct W3_offsets as (ho1 & ho2 & ho3).
      unfold phi3; rewrite vec_smul5.
      rewrite !wslice_lscale3 by lia. rewrite !wat_lscale3 by lia. rewrite !dot_lscale3 by apply wslice_length.
      rewrite !com_scale, !(pow_cmul (Hvec := Hvec)).
      f_equal. rewrite gop_pow; reflexivity.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* the honest voter                                                  *)
    (* ---------------------------------------------------------------- *)

    (* bit t of every v_k *)
    Definition hon_Xt (sn : list nat) (t : nat) : list F :=
      map (fun k => natF (bit (pos_v sn k) t)) (seq 0 K).

    Record rand3 : Type := mk_rand3 {
      r3_r : list F;                       (* K encryption randomnesses *)
      r3_rd : F; r3_rb : F; r3_rp : F;     (* commitment randomness *)
      r3_rX : list F;                      (* L commitment randomnesses for the bit vectors *)
      r3_a : list F;                       (* W3, the linear proof *)
      r3_a0 : list F; r3_bm : list F; r3_r0 : F; r3_sm : F; r3_t1 : list F; r3_t2 : list F }.

    Definition hon_cs3 (sn : list nat) (rd : rand3) : list (G * G) :=
      map (fun k => enc g h (natF (pos_bit sn k)) (nth k (r3_r rd) zero)) (seq 0 K).

    (* ρ* = ρ_δ + ρ_b − 2ρ_p + Σ_t 2^t ρ_X(t) *)
    Definition rho_star (rd : rand3) : F :=
      r3_rd rd + r3_rb rd + (opp (one + one) * r3_rp rd + fsum (fun t => pow2F t * nth t (r3_rX rd) zero) L).

    Definition hon_w3 (beta : list F) (sn : list nat) (rd : rand3) : list F :=
      hon_s sn ++ hon_b sn ++ [r3_rd rd; r3_rb rd; dot beta (r3_r rd) K; rho_star rd].

    (* the rows of the honest zero argument *)
    Definition hon_vecA (sn : list nat) (i : nat) : list F :=
      match i with
      | 0 => hon_b sn
      | 1 => hon_p sn
      | S (S t) => if Nat.ltb t L then hon_Xt sn t else hon_b sn
      end.
    Definition hon_vecB (sn : list nat) (i : nat) : list F :=
      match i with
      | 0 => hon_d sn
      | 1 => repeat (opp one) K
      | S (S t) => ladd (hon_vecA sn i) (repeat (opp one) K)
      end.
    Definition hon_rA (rd : rand3) (i : nat) : F :=
      match i with
      | 0 => r3_rb rd
      | 1 => r3_rp rd
      | S (S t) => if Nat.ltb t L then nth t (r3_rX rd) zero else r3_rb rd
      end.
    Definition hon_rB (rd : rand3) (i : nat) : F :=
      match i with 0 => r3_rd rd | 1 => zero | S (S t) => hon_rA rd i end.

    Definition encrypt_ballot3 (ch : chal3) (sn : list nat) (rd : rand3) : ballot3 :=
      let beta := c3_beta ch in let z := c3_z ch in
      mk_ballot3 (hon_cs3 sn rd)
        (com h1 gd (hon_s sn) (r3_rd rd)) (com h1 gs1 (hon_b sn) (r3_rb rd)) (com h1 gs1 (hon_p sn) (r3_rp rd))
        (map (fun t => com h1 gs1 (hon_Xt sn t) (nth t (r3_rX rd) zero)) (seq 0 L))
        (lin_prove (phi3 beta) (hon_w3 beta sn rd) (r3_a rd) (c3_c ch))
        (zero_prove h1 gs1
          (map (fun i => lscale (zwt z i) (hon_vecA sn i)) (seq 0 R)) (map (hon_vecB sn) (seq 0 R))
          (map (fun i => zwt z i * hon_rA rd i) (seq 0 R)) (map (hon_rB rd) (seq 0 R))
          (c3_y ch) (r3_a0 rd) (r3_bm rd) (r3_r0 rd) (r3_sm rd) (r3_t1 rd) (r3_t2 rd) (c3_x ch)).

    (* ---------------------------------------------------------------- *)
    (* completeness                                                      *)
    (* ---------------------------------------------------------------- *)

    Lemma hon_Xt_length : forall sn t, length (hon_Xt sn t) = K.
    Proof. intros; unfold hon_Xt; rewrite map_length, seq_length; reflexivity. Qed.
    Lemma nth_hon_Xt : forall sn t k, (k < K)%nat -> nth k (hon_Xt sn t) zero = natF (bit (pos_v sn k) t).
    Proof. intros; unfold hon_Xt; rewrite nth_map_seq by assumption; reflexivity. Qed.
    Lemma hon_Xt_bits : forall sn t x, In x (hon_Xt sn t) -> x = zero \/ x = one.
    Proof.
      intros sn t x hx; unfold hon_Xt in hx; apply in_map_iff in hx; destruct hx as (k & <- & _).
      destruct (bit_01 (pos_v sn k) t) as [e | e]; rewrite e; [left; reflexivity | right; apply (natF_one (Hvec := Hvec))].
    Qed.

    Lemma Ms_hon : forall sn, length sn = m -> Ms (hon_s sn) = hon_d sn.
    Proof.
      intros sn hsn; apply (nth_ext _ _ zero zero); [rewrite Ms_length, hon_d_length; reflexivity |].
      intros k hk; rewrite Ms_length in hk; rewrite nth_Ms, nth_hon_d by exact hk.
      destruct (kdm_lt k hk) as (hd & hm); rewrite !nth_hon_s by lia; reflexivity.
    Qed.

    Lemma cbeta_hon3 : forall beta sn rd, length beta = K ->
      cbeta beta (hon_cs3 sn rd) = enc g h (dot beta (hon_b sn) K) (dot beta (r3_r rd) K).
    Proof.
      intros beta sn rd hb; unfold SchulzeBatched.cbeta, hon_cs3.
      rewrite (lmexp_enc (Hvec := Hvec) g h (fun k => natF (pos_bit sn k)) (fun k => nth k (r3_r rd) zero) K 0 beta hb).
      apply enc_ext; apply fsum_ext; intros i hi; rewrite Nat.add_0_l; [rewrite nth_hon_b by exact hi |]; reflexivity.
    Qed.

    Lemma hon_w3_length : forall beta sn rd, length sn = m -> length (hon_w3 beta sn rd) = W3.
    Proof.
      intros * hsn; unfold hon_w3, W3, oR3; rewrite !app_length, hon_s_length, hon_b_length by exact hsn.
      cbn [length]; lia.
    Qed.

    Lemma hon_w3_slices : forall beta sn rd, length sn = m ->
      wslice (hon_w3 beta sn rd) 0 m = hon_s sn /\ wslice (hon_w3 beta sn rd) oB3 K = hon_b sn /\
      wat (hon_w3 beta sn rd) oR3 = r3_rd rd /\ wat (hon_w3 beta sn rd) (oR3 + 1) = r3_rb rd /\
      wat (hon_w3 beta sn rd) (oR3 + 2) = dot beta (r3_r rd) K /\ wat (hon_w3 beta sn rd) (oR3 + 3) = rho_star rd.
    Proof.
      intros * hsn; pose proof (hon_s_length sn hsn) as l1; pose proof (hon_b_length sn) as l2; unfold hon_w3.
      repeat split.
      + apply wslice_prefix; exact l1.
      + replace oB3 with (length (hon_s sn) + 0)%nat by (unfold oB3; lia).
        rewrite wslice_app_shift by reflexivity; apply wslice_prefix; exact l2.
      + replace oR3 with (length (hon_s sn) + (length (hon_b sn) + 0))%nat by (unfold oR3; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR3 + 1)%nat with (length (hon_s sn) + (length (hon_b sn) + 1))%nat by (unfold oR3; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR3 + 2)%nat with (length (hon_s sn) + (length (hon_b sn) + 2))%nat by (unfold oR3; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR3 + 3)%nat with (length (hon_s sn) + (length (hon_b sn) + 3))%nat by (unfold oR3; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
    Qed.

    (* the 2^t-combination of the bit commitments *)
    Lemma gmexp_CX : forall (X : nat -> list F) (rX : nat -> F),
      (forall t, (t < L)%nat -> length (X t) = K) ->
      gmexp (map (fun t => com h1 gs1 (X t) (rX t)) (seq 0 L)) pows2 =
      com h1 gs1 (lincomb K pow2F X 0 L) (fsum (fun t => pow2F t * rX t) L).
    Proof.
      intros X rX hX; unfold pows2.
      rewrite (com_lincomb h1 gs1 K pow2F rX X 0 L) by (intros t ht; apply hX; lia).
      f_equal; apply fsum_ext; intros t ht; rewrite Nat.add_0_l; reflexivity.
    Qed.

    (* C₀ on openings: a commitment to δ + b − 2p + Σ_t 2^t X(t) *)
    Lemma C0_com : forall (d b p : list F) (rd rb rp : F) (X : nat -> list F) (rX : nat -> F),
      length d = K -> length b = K -> length p = K -> (forall t, (t < L)%nat -> length (X t) = K) ->
      C0 (com h1 gs1 d rd) (com h1 gs1 b rb) (com h1 gs1 p rp) (map (fun t => com h1 gs1 (X t) (rX t)) (seq 0 L)) =
      com h1 gs1 (ladd (ladd d b) (ladd (lscale (opp (one + one)) p) (lincomb K pow2F X 0 L)))
        (rd + rb + (opp (one + one) * rp + fsum (fun t => pow2F t * rX t) L)).
    Proof.
      intros * hd hb hp hX; unfold C0.
      rewrite gmexp_CX by exact hX.
      assert (hlc : length (lincomb K pow2F X 0 L) = K) by (apply lincomb_length; intros t ht; apply hX; lia).
      assert (hls : length (lscale (opp (one + one)) p) = K) by (rewrite lscale_length'; exact hp).
      assert (hl1 : length (ladd d b) = K) by (rewrite ladd_length'; lia).
      assert (hl2 : length (ladd (lscale (opp (one + one)) p) (lincomb K pow2F X 0 L)) = K)
        by (rewrite ladd_length'; lia).
      rewrite <-com_scale.
      rewrite <-!com_add by (rewrite ?hl1, ?hl2, ?hls, ?hlc, ?hd, ?hb; reflexivity).
      reflexivity.
    Qed.

    Lemma hon_zero_vec : forall sn, length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) ->
      (m < Nat.pow 2 L)%nat ->
      ladd (ladd (hon_d sn) (hon_b sn)) (ladd (lscale (opp (one + one)) (hon_p sn)) (lincomb K pow2F (hon_Xt sn) 0 L)) =
      repeat zero K.
    Proof.
      intros sn hsn hs hL.
      assert (hlc : length (lincomb K pow2F (hon_Xt sn) 0 L) = K) by (apply lincomb_length; intros; apply hon_Xt_length).
      assert (hls : length (lscale (opp (one + one)) (hon_p sn)) = K) by (rewrite lscale_length'; apply hon_p_length).
      assert (hl1 : length (ladd (hon_d sn) (hon_b sn)) = K)
        by (rewrite ladd_length', hon_d_length; [reflexivity | rewrite hon_d_length, hon_b_length; reflexivity]).
      assert (hl2 : length (ladd (lscale (opp (one + one)) (hon_p sn)) (lincomb K pow2F (hon_Xt sn) 0 L)) = K)
        by (rewrite ladd_length', hls; [reflexivity | rewrite hls, hlc; reflexivity]).
      apply (nth_ext _ _ zero zero).
      + rewrite ladd_length', hl1, repeat_length; [reflexivity | rewrite hl1, hl2; reflexivity].
      + intros k hk; rewrite ladd_length', hl1 in hk by (rewrite hl1, hl2; reflexivity).
        rewrite nth_repeat' by exact hk.
        rewrite nth_ladd' by (rewrite ?hl1, ?hl2; try reflexivity; exact hk).
        rewrite nth_ladd' by (rewrite ?hon_d_length, ?hon_b_length; try reflexivity; exact hk).
        rewrite nth_ladd' by (rewrite ?hls, ?hlc; try reflexivity; exact hk).
        rewrite nth_lscale' by (rewrite hon_p_length; exact hk).
        rewrite nth_lincomb by (try exact hk; intros; apply hon_Xt_length).
        rewrite (fsum_ext _ (fun t => pow2F t * natF (bit (pos_v sn k) t)))
          by (intros t ht; rewrite Nat.add_0_l, nth_hon_Xt by exact hk; reflexivity).
        rewrite bits_sum, Nat.mod_small by (pose proof (pos_v_bound sn k hs hk); lia).
        rewrite nth_hon_p, nth_hon_b, nth_hon_d by exact hk.
        destruct (kdm_lt k hk) as (hd & hm); pose proof (hs _ hd); pose proof (hs _ hm).
        unfold SchulzeBatched.pos_v, SchulzeBatched.pos_bit.
        destruct (Nat.ltb (nth (k / m) sn 0) (nth (k mod m) sn 0)) eqn:hlt.
        * apply Nat.ltb_lt in hlt.
          rewrite (natF_sub (Hvec := Hvec)) by lia; rewrite (natF_sub (Hvec := Hvec)) by lia.
          rewrite (natF_one (Hvec := Hvec)); field.
        * apply Nat.ltb_ge in hlt.
          rewrite (natF_sub (Hvec := Hvec)) by lia; cbn [nat_to_F]; field.
    Qed.

    Lemma target3_phi3 : forall ch sn rd, length sn = m -> length (c3_beta ch) = K ->
      (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
      target3 (c3_beta ch) (encrypt_ballot3 ch sn rd) = phi3 (c3_beta ch) (hon_w3 (c3_beta ch) sn rd).
    Proof.
      intros * hsn hb hs hL; unfold target3, encrypt_ballot3, phi3; cbn [b3_cs b3_Cd b3_Cb b3_Cp b3_CX].
      destruct (hon_w3_slices (c3_beta ch) sn rd hsn) as (e1 & e2 & e3 & e4 & e5 & e6).
      rewrite e1, e2, e3, e4, e5, e6, cbeta_hon3 by exact hb.
      unfold Elgamal.enc; cbn [fst snd]. f_equal.
      rewrite com_gd by (apply hon_s_length; exact hsn); rewrite Ms_hon by exact hsn.
      rewrite (C0_com (hon_d sn) (hon_b sn) (hon_p sn) _ _ _ (hon_Xt sn) (fun t => nth t (r3_rX rd) zero)
        (hon_d_length sn) (hon_b_length sn) (hon_p_length sn) (fun t _ => hon_Xt_length sn t)).
      rewrite hon_zero_vec by assumption; rewrite com_zeros; reflexivity.
    Qed.

    (* the honest zero argument: rows and sum *)
    Lemma hon_vecA_length : forall sn i, length (hon_vecA sn i) = K.
    Proof.
      intros sn i; destruct i as [| [| t]]; cbn [hon_vecA];
        [apply hon_b_length | apply hon_p_length | destruct (Nat.ltb t L); [apply hon_Xt_length | apply hon_b_length]].
    Qed.
    Lemma hon_vecB_length : forall sn i, length (hon_vecB sn i) = K.
    Proof.
      intros sn i; destruct i as [| [| t]]; cbn [hon_vecB];
        [apply hon_d_length | apply repeat_length | rewrite ladd_length', hon_vecA_length; [reflexivity |]].
      rewrite hon_vecA_length, repeat_length; reflexivity.
    Qed.
    Lemma hon_vecA_bits : forall sn i x, (2 <= i)%nat -> In x (hon_vecA sn i) -> x = zero \/ x = one.
    Proof.
      intros sn i x hi hx; destruct i as [| [| t]]; [lia | lia |]; cbn [hon_vecA] in hx.
      destruct (Nat.ltb t L); [exact (hon_Xt_bits sn t x hx) | exact (hon_b_bits (Hvec := Hvec) sn x hx)].
    Qed.

    Lemma hon_zA : forall ch sn rd, length (r3_rX rd) = L ->
      zA (c3_z ch) (encrypt_ballot3 ch sn rd) =
      com_list h1 gs1 (map (fun i => lscale (zwt (c3_z ch) i) (hon_vecA sn i)) (seq 0 R))
        (map (fun i => zwt (c3_z ch) i * hon_rA rd i) (seq 0 R)).
    Proof.
      intros ch sn rd hrX; unfold zA; rewrite com_list_map; apply map_ext_in; intros i hi; apply in_seq in hi.
      rewrite com_scale; unfold rowA; f_equal.
      destruct i as [| [| t]]; cbn [baseA hon_vecA hon_rA encrypt_ballot3 b3_Cb b3_Cp b3_CX]; try reflexivity.
      destruct (Nat.ltb t L) eqn:ht; [| reflexivity].
      apply Nat.ltb_lt in ht; rewrite nth_map_seq by exact ht; reflexivity.
    Qed.

    Lemma hon_zB : forall ch sn rd, length sn = m -> length (r3_rX rd) = L ->
      zB (encrypt_ballot3 ch sn rd) = com_list h1 gs1 (map (hon_vecB sn) (seq 0 R)) (map (hon_rB rd) (seq 0 R)).
    Proof.
      intros ch sn rd hsn hrX; unfold zB; rewrite com_list_map; apply map_ext_in; intros i hi; apply in_seq in hi.
      destruct i as [| [| t]]; cbn [rowB baseA hon_vecB hon_rB encrypt_ballot3 b3_Cd b3_Cb b3_Cp b3_CX].
      + rewrite com_gd by (apply hon_s_length; exact hsn); rewrite Ms_hon by exact hsn; reflexivity.
      + reflexivity.
      + replace (hon_rA rd (S (S t))) with (hon_rA rd (S (S t)) + zero) by field.
        rewrite com_add by (rewrite hon_vecA_length, repeat_length; reflexivity).
        unfold SchulzeBatched.cneg; f_equal.
        cbn [hon_vecA hon_rA]; destruct (Nat.ltb t L) eqn:ht; [| reflexivity].
        apply Nat.ltb_lt in ht; rewrite nth_map_seq by exact ht; reflexivity.
    Qed.

    Lemma hon_zero_sum : forall sn y z, length sn = m ->
      fold_right add zero (map (fun p => star y (fst p) (snd p))
        (combine (map (fun i => lscale (zwt z i) (hon_vecA sn i)) (seq 0 R)) (map (hon_vecB sn) (seq 0 R)))) = zero.
    Proof.
      intros sn y z hsn; rewrite combine_map_same, map_map; cbn [fst snd].
      rewrite fold_map_seq.
      unfold R; replace (L + 3)%nat with (S (S (S L))) by lia.
      rewrite (fsum_shift (Hvec := Hvec)), (fsum_shift (Hvec := Hvec)).
      rewrite (fsum_ext _ (fun _ => zero)).
      2: { intros i hi; cbn beta; cbn [Nat.add hon_vecB]; unfold BayerGroth.star; rewrite star_w_lscale_l.
           rewrite (star_w_bits (Hvec := Hvec) _ _ _ K (hon_vecA_length sn (S (S i))) (fun x hx => hon_vecA_bits sn (S (S i)) x (le_n_S _ _ (le_n_S _ _ (Nat.le_0_l i))) hx)); field. }
      rewrite (fsum_zero (Hf := vector_space_field)).
      cbn beta; cbn [Nat.add hon_vecA hon_vecB zwt]; unfold BayerGroth.star; rewrite !star_w_lscale_l.
      pose proof (star_w_prod (Hvec := Hvec) y y (hon_b sn) (hon_d sn) K (hon_b_length sn) (hon_d_length sn)) as hp.
      unfold SchulzeBatched.hon_p; transitivity (z * (star_w y y (hon_b sn) (hon_d sn) +
        star_w y y (hmul (hon_b sn) (hon_d sn)) (repeat (opp one) K))); [field | rewrite hp; field].
    Qed.

    Theorem ballot3_valid : forall (ch : chal3) (sn : list nat) (rd : rand3),
      length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
      length gs1 = K -> length (c3_beta ch) = K ->
      length (r3_r rd) = K -> length (r3_rX rd) = L -> length (r3_a rd) = W3 ->
      length (r3_a0 rd) = K -> length (r3_bm rd) = K -> length (r3_t1 rd) = S R -> length (r3_t2 rd) = (R - 1)%nat ->
      verify_ballot3 ch (encrypt_ballot3 ch sn rd) = true.
    Proof.
      intros * hsn hs hL hg1 hb hr hrX ha ha0 hbm ht1 ht2.
      unfold verify_ballot3.
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split |] |].
      + cbn [b3_cs encrypt_ballot3]; unfold hon_cs3; apply Nat.eqb_eq; rewrite map_length, seq_length; reflexivity.
      + cbn [b3_CX encrypt_ballot3]; apply Nat.eqb_eq; rewrite map_length, seq_length; reflexivity.
      + rewrite target3_phi3 by assumption. cbn [b3_lin encrypt_ballot3].
        apply (lin_completeness W3 (phi3 (c3_beta ch)) (phi3_add (c3_beta ch)) (phi3_scale (c3_beta ch)));
          [apply hon_w3_length; exact hsn | exact ha].
      + rewrite hon_zA by exact hrX; rewrite hon_zB by assumption. cbn [b3_z encrypt_ballot3].
        apply (zero_completeness (Hvec := Hvec) (Gdec := Gdec)); rewrite ?map_length, ?seq_length;
          try (unfold R; lia); try assumption.
        * constructor; [rewrite ha0; exact (eq_sym hg1) |].
          apply Forall_map, Forall_forall; intros i _; rewrite lscale_length', hon_vecA_length; exact (eq_sym hg1).
        * constructor; [rewrite hbm; exact (eq_sym hg1) |].
          apply Forall_map, Forall_forall; intros i _; rewrite hon_vecB_length; exact (eq_sym hg1).
        * apply hon_zero_sum; exact hsn.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* Fiat–Shamir: every challenge from one random oracle               *)
    (* ---------------------------------------------------------------- *)

    Inductive b3_item : Type := B3G (x : G) | B3F (x : F) | B3N (k : nat).

    Section NIZK3.
      Context (H : list b3_item -> F).

      Definition items_cs3 (cs : list (G * G)) : list b3_item :=
        concat (map (fun c => [B3G (fst c); B3G (snd c)]) cs).
      (* the ciphertexts and the commitments: what β, y and z are derived from *)
      Definition items_base3 (bt : ballot3) : list b3_item :=
        items_cs3 (b3_cs bt) ++ [B3G (b3_Cd bt); B3G (b3_Cb bt); B3G (b3_Cp bt)] ++ map B3G (b3_CX bt).
      Definition items_st3 (st : Vector.t G 5) : list b3_item := map B3G (Vector.to_list st).
      Definition items_zero3 (z : zero_argument) : list b3_item :=
        B3G (za_cA0 z) :: B3G (za_cBm z) :: map B3G (za_cd z).

      (* tag 1: β (K values); 2: y; 3: z; 4: c from the linear announcement;
         5: x from the zero announcement *)
      Definition vec_chal3 (tag : nat) (bt : ballot3) : list F :=
        map (fun k => H (B3N tag :: B3N k :: items_base3 bt)) (seq 0 K).
      Definition challenges_of3 (bt : ballot3) : chal3 :=
        mk_chal3 (vec_chal3 1 bt) (H (B3N 2 :: items_base3 bt)) (H (B3N 3 :: items_base3 bt))
          (H (B3N 4 :: items_base3 bt ++ items_st3 (lin_a (b3_lin bt))))
          (H (B3N 5 :: items_base3 bt ++ items_zero3 (b3_z bt))).

      Definition nizk_verify_ballot3 (bt : ballot3) : bool :=
        verify_ballot3 (challenges_of3 bt) bt.

      (* the honest voter in three passes: the first fixes β, y, z (from the
         ciphertexts and commitments), the second fixes c and x (the linear
         announcement depends on β, the zero announcement on y and z), the
         third is the ballot *)
      Definition chal30 : chal3 := mk_chal3 (repeat zero K) zero zero zero zero.
      Definition nizk_encrypt_ballot3 (sn : list nat) (rd : rand3) : ballot3 :=
        let b0 := encrypt_ballot3 chal30 sn rd in
        let b1 := encrypt_ballot3 (challenges_of3 b0) sn rd in
        encrypt_ballot3 (challenges_of3 b1) sn rd.

      (* the announcements of the honest ballot do not depend on c and x *)
      Lemma challenges_announcements3 : forall ch ch' sn rd,
        c3_beta ch = c3_beta ch' -> c3_y ch = c3_y ch' -> c3_z ch = c3_z ch' ->
        challenges_of3 (encrypt_ballot3 ch sn rd) = challenges_of3 (encrypt_ballot3 ch' sn rd).
      Proof.
        intros [] [] sn rd e1 e2 e3; cbn in e1, e2, e3; subst; reflexivity.
      Qed.

      Lemma vec_chal3_length : forall tag bt, length (vec_chal3 tag bt) = K.
      Proof. intros; unfold vec_chal3; rewrite map_length, seq_length; reflexivity. Qed.

      Theorem nizk_ballot3_valid : forall (sn : list nat) (rd : rand3),
        length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
        length gs1 = K ->
        length (r3_r rd) = K -> length (r3_rX rd) = L -> length (r3_a rd) = W3 ->
        length (r3_a0 rd) = K -> length (r3_bm rd) = K -> length (r3_t1 rd) = S R -> length (r3_t2 rd) = (R - 1)%nat ->
        nizk_verify_ballot3 (nizk_encrypt_ballot3 sn rd) = true.
      Proof.
        intros; unfold nizk_verify_ballot3, nizk_encrypt_ballot3.
        set (b0 := encrypt_ballot3 chal30 sn rd).
        set (ch1 := challenges_of3 b0).
        set (b1 := encrypt_ballot3 ch1 sn rd).
        set (ch2 := challenges_of3 b1).
        assert (e : challenges_of3 (encrypt_ballot3 ch2 sn rd) = ch2).
        { transitivity (challenges_of3 (encrypt_ballot3 ch1 sn rd)); [| reflexivity].
          apply challenges_announcements3; reflexivity. }
        rewrite e. apply ballot3_valid; try assumption. apply vec_chal3_length.
      Qed.

    End NIZK3.

    (* ---------------------------------------------------------------- *)
    (* soundness: the linear argument                                    *)
    (* ---------------------------------------------------------------- *)

    Local Notation natF_injective := (natF_injective (zero := zero) (one := one) (add := add)).

    Definition lin_accepts3 (beta : list F) (bt : ballot3) (c0 c1 : F) : Prop :=
      exists (A : Vector.t G 5) (z0 z1 : list F),
        lin_verify W3 (phi3 beta) (target3 beta bt) c0 (mk_lin A z0) = true /\
        lin_verify W3 (phi3 beta) (target3 beta bt) c1 (mk_lin A z1) = true.

    Lemma lin_open3 : forall beta bt c0 c1, c0 <> c1 -> lin_accepts3 beta bt c0 c1 ->
      exists w, length w = W3 /\ phi3 beta w = target3 beta bt.
    Proof.
      intros * hc (A & z0 & z1 & h0 & hz1).
      destruct (lin_soundness (HV := G5vs) W3 (phi3 beta) (phi3_add beta) (phi3_scale beta)
        (target3 beta bt) A c0 c1 z0 z1 hc h0 hz1) as (hl & he).
      exists (lin_extract (sub := sub) (mul := mul) (inv := inv) (add := add) (opp := opp) (one := one) c0 c1 z0 z1); split; assumption.
    Qed.

    Lemma phi3_target_open : forall beta bt w, phi3 beta w = target3 beta bt ->
      b3_Cd bt = com h1 gs1 (Ms (wslice w 0 m)) (wat w oR3) /\
      b3_Cb bt = com h1 gs1 (wslice w oB3 K) (wat w (oR3 + 1)) /\
      cbeta beta (b3_cs bt) = enc g h (dot beta (wslice w oB3 K) K) (wat w (oR3 + 2)) /\
      C0 (b3_Cd bt) (b3_Cb bt) (b3_Cp bt) (b3_CX bt) = h1 ^ wat w (oR3 + 3).
    Proof.
      intros * H; unfold phi3, target3 in H.
      apply vec5_inj in H; destruct H as (e1 & e2 & e3 & e4 & e5).
      repeat split; try (symmetry; assumption).
      + rewrite <-e1; apply com_gd; apply wslice_length.
      + rewrite (surjective_pairing (cbeta beta (b3_cs bt))); unfold Elgamal.enc; rewrite <-e3, <-e4; reflexivity.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* soundness: the zero argument                                      *)
    (* ---------------------------------------------------------------- *)

    (* the rows on openings (b, p, X(t)) of C_b, C_p, C_X(t) and (d) of C_δ *)
    Definition vecA (b p : list F) (X : nat -> list F) (i : nat) : list F :=
      match i with 0 => b | 1 => p | S (S t) => if Nat.ltb t L then X t else b end.
    Definition vecB (d b p : list F) (X : nat -> list F) (i : nat) : list F :=
      match i with 0 => d | 1 => repeat (opp one) K | S (S t) => ladd (vecA b p X i) (repeat (opp one) K) end.
    Definition rA (rb rp : F) (rX : nat -> F) (i : nat) : F :=
      match i with 0 => rb | 1 => rp | S (S t) => if Nat.ltb t L then rX t else rb end.
    Definition rB (rd rb rp : F) (rX : nat -> F) (i : nat) : F :=
      match i with 0 => rd | 1 => zero | S (S t) => rA rb rp rX i end.

    Lemma vecA_length : forall b p X i, length b = K -> length p = K -> (forall t, (t < L)%nat -> length (X t) = K) ->
      length (vecA b p X i) = K.
    Proof.
      intros b p X i hb hp hX; destruct i as [| [| t]]; cbn [vecA]; [exact hb | exact hp |].
      destruct (Nat.ltb t L) eqn:ht; [apply hX; apply Nat.ltb_lt; exact ht | exact hb].
    Qed.
    Lemma vecB_length : forall d b p X i, length d = K -> length b = K -> length p = K ->
      (forall t, (t < L)%nat -> length (X t) = K) -> length (vecB d b p X i) = K.
    Proof.
      intros d b p X i hd hb hp hX; destruct i as [| [| t]]; cbn [vecB]; [exact hd | apply repeat_length |].
      assert (hA : length (vecA b p X (S (S t))) = K) by (apply vecA_length; assumption).
      rewrite ladd_length', hA; [reflexivity | rewrite hA, repeat_length; reflexivity].
    Qed.

    Lemma zwt_nonzero : forall z i, z <> zero -> zwt z i <> zero.
    Proof. intros z i hz; destruct i as [| [| i]]; cbn [zwt]; [exact hz | exact hz | apply fpow_nonzero; exact hz]. Qed.

    Lemma baseA_com : forall bt (b p : list F) (X : nat -> list F) (rb rp : F) (rX : nat -> F) i, (i < R)%nat ->
      b3_Cb bt = com h1 gs1 b rb -> b3_Cp bt = com h1 gs1 p rp ->
      (forall t, (t < L)%nat -> nth t (b3_CX bt) gid = com h1 gs1 (X t) (rX t)) ->
      baseA bt i = com h1 gs1 (vecA b p X i) (rA rb rp rX i).
    Proof.
      intros * hi eCb eCp eCX; destruct i as [| [| t]]; cbn [baseA vecA rA]; [exact eCb | exact eCp |].
      destruct (Nat.ltb t L) eqn:ht; [apply eCX; apply Nat.ltb_lt; exact ht | exact eCb].
    Qed.

    Lemma rows_com : forall bt z (d b p : list F) (X : nat -> list F) (rd rb rp : F) (rX : nat -> F) i, (i < R)%nat ->
      length b = K -> length p = K -> (forall t, (t < L)%nat -> length (X t) = K) ->
      b3_Cb bt = com h1 gs1 b rb -> b3_Cd bt = com h1 gs1 d rd -> b3_Cp bt = com h1 gs1 p rp ->
      (forall t, (t < L)%nat -> nth t (b3_CX bt) gid = com h1 gs1 (X t) (rX t)) ->
      rowA z bt i = com h1 gs1 (lscale (zwt z i) (vecA b p X i)) (zwt z i * rA rb rp rX i) /\
      rowB bt i = com h1 gs1 (vecB d b p X i) (rB rd rb rp rX i).
    Proof.
      intros * hi hb hp hX eCb eCd eCp eCX; split.
      + unfold rowA; rewrite com_scale, (baseA_com bt b p X rb rp rX i hi eCb eCp eCX); reflexivity.
      + destruct i as [| [| t]]; cbn [rowB vecB rB]; [exact eCd | reflexivity |].
        rewrite (baseA_com bt b p X rb rp rX (S (S t)) hi eCb eCp eCX).
        transitivity (com h1 gs1 (ladd (vecA b p X (S (S t))) (repeat (opp one) K)) (rA rb rp rX (S (S t)) + zero));
          [| f_equal; field].
        rewrite com_add by (rewrite vecA_length, repeat_length by assumption; reflexivity).
        unfold SchulzeBatched.cneg; reflexivity.
    Qed.

    (* one accepted zero argument at (y, z), with all commitments opened: the
       weighted sum of the star products of the openings vanishes *)
    Lemma zero_open_at : forall bt y z (d b p : list F) (X : nat -> list F) (rd rb rp : F) (rX : nat -> F),
      length gs1 = K -> length b = K -> length d = K -> length p = K -> (forall t, (t < L)%nat -> length (X t) = K) ->
      b3_Cb bt = com h1 gs1 b rb -> b3_Cd bt = com h1 gs1 d rd -> b3_Cp bt = com h1 gs1 p rp ->
      (forall t, (t < L)%nat -> nth t (b3_CX bt) gid = com h1 gs1 (X t) (rX t)) ->
      zero_accepts h1 gs1 (zA z bt) (zB bt) y ->
      binding_break h1 gs1 \/ fsum (fun i => zwt z i * star y (vecA b p X i) (vecB d b p X i)) R = zero.
    Proof.
      intros * hg1 hb hd hp hX eCb eCd eCp eCX (cA0 & cBm & cd & xs & a & bb & r & s' & t & hnd & hlen & htr).
      pose proof K_pos as hK.
      assert (hzA : length (zA z bt) = R) by (unfold zA; rewrite map_length, seq_length; reflexivity).
      assert (hzB : length (zB bt) = R) by (unfold zB; rewrite map_length, seq_length; reflexivity).
      destruct (zero_soundness (Hvec := Hvec) (Fdec := Fdec) h1 gs1 (zA z bt) (zB bt) y cA0 cBm cd xs a bb r s' t
        ltac:(lia) hnd hlen htr) as [(A & B & ra & sb & eA & eB & lA & lB & lra & lsb & hAn & hBn & hsum) | hbk];
        [| left; exact hbk].
      rewrite hzA in lA, lB, lra, lsb.
      assert (hrow : forall i, (i < R)%nat ->
        (nth i A [] = lscale (zwt z i) (vecA b p X i) /\ nth i B [] = vecB d b p X i) \/ binding_break h1 gs1).
      { intros i hi.
        destruct (rows_com bt z d b p X rd rb rp rX i hi hb hp hX eCb eCd eCp eCX) as (erA & erB).
        assert (eAi : com h1 gs1 (nth i A []) (nth i ra zero) = rowA z bt i).
        { rewrite <-nth_com_list by lia; rewrite <-eA; unfold zA; apply nth_map_seq; exact hi. }
        assert (eBi : com h1 gs1 (nth i B []) (nth i sb zero) = rowB bt i).
        { rewrite <-nth_com_list by lia; rewrite <-eB; unfold zB; apply nth_map_seq; exact hi. }
        rewrite erA in eAi; rewrite erB in eBi.
        assert (hiA : (i < length A)%nat) by lia. assert (hiB : (i < length B)%nat) by lia.
        assert (hlA : length (lscale (zwt z i) (vecA b p X i)) = length gs1).
        { rewrite lscale_length', hg1; apply vecA_length; assumption. }
        assert (hlB : length (vecB d b p X i) = length gs1) by (rewrite hg1; apply vecB_length; assumption).
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 _ _ _ _
          (hAn _ (nth_In A [] hiA)) hlA eAi) as [(ea & _) | hbk]; [| right; exact hbk].
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 _ _ _ _
          (hBn _ (nth_In B [] hiB)) hlB eBi) as [(eb & _) | hbk]; [| right; exact hbk].
        left; split; assumption. }
      destruct (forall_or _ _ R hrow) as [hall | hbk]; [right | left; exact hbk].
      rewrite fold_combine_fsum in hsum by lia. rewrite lA in hsum.
      refine (eq_trans _ hsum); apply fsum_ext; intros i hi.
      destruct (hall i hi) as (ea & eb); rewrite ea, eb.
      unfold BayerGroth.star; rewrite star_w_lscale_l; reflexivity.
    Qed.

    (* one accepted zero argument at a non-zero z: openings of C_p and the C_X(t) *)
    Lemma zero_open_ref : forall bt y z, length gs1 = K -> z <> zero ->
      zero_accepts h1 gs1 (zA z bt) (zB bt) y ->
      binding_break h1 gs1 \/ exists (p : list F) (rp : F) (X : nat -> list F) (rX : nat -> F),
        length p = K /\ (forall t, (t < L)%nat -> length (X t) = K) /\
        b3_Cp bt = com h1 gs1 p rp /\ (forall t, (t < L)%nat -> nth t (b3_CX bt) gid = com h1 gs1 (X t) (rX t)).
    Proof.
      intros * hg1 hz (cA0 & cBm & cd & xs & a & bb & r & s' & t & hnd & hlen & htr).
      pose proof K_pos as hK.
      assert (hzA : length (zA z bt) = R) by (unfold zA; rewrite map_length, seq_length; reflexivity).
      destruct (zero_soundness (Hvec := Hvec) (Fdec := Fdec) h1 gs1 (zA z bt) (zB bt) y cA0 cBm cd xs a bb r s' t
        ltac:(lia) hnd hlen htr) as [(A & B & ra & sb & eA & eB & lA & lB & lra & lsb & hAn & hBn & hsum) | hbk];
        [| left; exact hbk].
      rewrite hzA in lA, lra.
      assert (hopen : forall i, (i < R)%nat ->
        baseA bt i = com h1 gs1 (lscale (inv (zwt z i)) (nth i A [])) (inv (zwt z i) * nth i ra zero)).
      { intros i hi.
        assert (eAi : com h1 gs1 (nth i A []) (nth i ra zero) = baseA bt i ^ zwt z i).
        { rewrite <-nth_com_list by lia; rewrite <-eA; unfold zA; rewrite nth_map_seq by exact hi; reflexivity. }
        rewrite com_scale, eAi, <-pow_mul.
        replace (zwt z i * inv (zwt z i)) with one by (field; apply zwt_nonzero; exact hz).
        rewrite pow_one; reflexivity. }
      right.
      exists (lscale (inv (zwt z 1)) (nth 1 A [])), (inv (zwt z 1) * nth 1 ra zero),
        (fun t => lscale (inv (zwt z (S (S t)))) (nth (S (S t)) A [])),
        (fun t => inv (zwt z (S (S t))) * nth (S (S t)) ra zero).
      repeat split.
      + rewrite lscale_length', hAn by (apply nth_In; unfold R in *; lia); exact hg1.
      + intros t' ht'; rewrite lscale_length', hAn by (apply nth_In; unfold R in *; lia); exact hg1.
      + exact (hopen 1 ltac:(unfold R in *; lia)).
      + intros t' ht'; pose proof (hopen (S (S t')) ltac:(unfold R in *; lia)) as e; cbn [baseA] in e.
        rewrite (proj2 (Nat.ltb_lt t' L) ht') in e; exact e.
    Qed.

    (* the weighted sum as a polynomial in z *)
    Definition qpoly (y : F) (d b p : list F) (X : nat -> list F) : list F :=
      (star y b d + star y p (repeat (opp one) K)) ::
      map (fun t => star y (vecA b p X (S (S t))) (vecB d b p X (S (S t)))) (seq 0 (S L)).

    Lemma qpoly_length : forall y d b p X, length (qpoly y d b p X) = (L + 2)%nat.
    Proof. intros; unfold qpoly; cbn [length]; rewrite map_length, seq_length; lia. Qed.

    Lemma weighted_sum_eval : forall y z d b p X,
      fsum (fun i => zwt z i * star y (vecA b p X i) (vecB d b p X i)) R = z * eval (qpoly y d b p X) z.
    Proof.
      intros; unfold R; replace (L + 3)%nat with (S (S (S L))) by lia.
      set (c := fun i => star y (vecA b p X i) (vecB d b p X i)).
      change (fsum (fun i => zwt z i * c i) (S (S (S L))) =
        z * eval ((c 0 + c 1) :: map (fun t => c (S (S t))) (seq 0 (S L))) z).
      rewrite (fsum_shift (Hvec := Hvec)), (fsum_shift (Hvec := Hvec)); cbn [PolyRoots.eval]; rewrite eval_map_seq.
      cbn beta.
      rewrite (fsum_ext (fun i => zwt z (S (S i)) * c (S (S i))) (fun i => (z * z) * (fpow z i * c (S (S i)))))
        by (intros i hi; cbn [zwt SigmaK.fpow]; field).
      rewrite (fsum_ext (fun j => fpow z j * c (S (S (0 + j)))) (fun j => fpow z j * c (S (S j))))
        by (intros j hj; rewrite Nat.add_0_l; reflexivity).
      rewrite fsum_scale'. cbn [zwt]. field.
    Qed.

    (* the coefficients vanish on L + 2 distinct non-zero z *)
    Lemma coeffs_vanish : forall y d b p X (Z : list F), NoDup Z -> length Z = (L + 2)%nat ->
      (forall z, In z Z -> z <> zero) ->
      (forall z, In z Z -> fsum (fun i => zwt z i * star y (vecA b p X i) (vecB d b p X i)) R = zero) ->
      star y b d + star y p (repeat (opp one) K) = zero /\
      forall t, (t < S L)%nat -> star y (vecA b p X (S (S t))) (vecB d b p X (S (S t))) = zero.
    Proof.
      intros * hnd hZ hz0 hall.
      pose proof (poly_vanish_mul (Hvec := Hvec) (Fdec := Fdec) (qpoly y d b p X) Z hnd
        ltac:(rewrite qpoly_length; lia) hz0
        (fun z hz => eq_trans (eq_sym (weighted_sum_eval y z d b p X)) (hall z hz))) as hv.
      split.
      + exact (hv 0).
      + intros t ht; pose proof (hv (S t)) as e; unfold qpoly in e; cbn [nth] in e.
        rewrite nth_map_seq in e by exact ht; exact e.
    Qed.

    (* the rows at K distinct non-zero y: p = b ∘ d, and the bit rows are bits *)
    Lemma prod_of_star : forall (b p d : list F) (Y : list F), length b = K -> length p = K -> length d = K ->
      NoDup Y -> length Y = K -> (forall y, In y Y -> y <> zero) ->
      (forall y, In y Y -> star y b d + star y p (repeat (opp one) K) = zero) ->
      forall j, (j < K)%nat -> nth j p zero = nth j b zero * nth j d zero.
    Proof.
      intros * hb hp hd hnd hY hy0 hall.
      set (q := SigmaK.padd (add := add) (hmul b d) (lscale (opp one) p)).
      assert (hq : length q = K) by (unfold q; rewrite SigmaK.padd_length, hmul_length, lscale_length'; lia).
      assert (hz : forall y, In y Y -> y * eval q y = zero).
      { intros y hy; pose proof (hall y hy) as e.
        rewrite (star_hmul_eval (Hvec := Hvec)) in e by lia. rewrite (star_neg_eval (Hvec := Hvec) y p K hp) in e.
        unfold q; rewrite (eval_padd (Hf := vector_space_field)), (eval_lscale (Hf := vector_space_field)).
        etransitivity; [| exact e]; field. }
      intros j hj.
      pose proof (poly_vanish_mul (Hvec := Hvec) (Fdec := Fdec) q Y hnd ltac:(lia) hy0 hz j) as e.
      unfold q in e.
      rewrite (nth_padd (Hf := vector_space_field)), (SigmaK.nth_lscale (Hf := vector_space_field)) in e.
      rewrite nth_hmul in e by lia.
      apply (sub_eq_zero (Hf := vector_space_field)).
      transitivity (opp (nth j b zero * nth j d zero + opp one * nth j p zero)); [field | rewrite e; field].
    Qed.

    Lemma bits_of_star : forall (v : list F) (Y : list F), length v = K ->
      NoDup Y -> length Y = K -> (forall y, In y Y -> y <> zero) ->
      (forall y, In y Y -> star y v (ladd v (repeat (opp one) K)) = zero) ->
      forall j, (j < K)%nat -> nth j v zero = zero \/ nth j v zero = one.
    Proof.
      intros * hv hnd hY hy0 hall.
      set (q := hmul v (ladd v (repeat (opp one) K))).
      assert (hl : length (ladd v (repeat (opp one) K)) = K) by (rewrite ladd_length'; [exact hv | rewrite repeat_length; exact hv]).
      assert (hq : length q = K) by (unfold q; rewrite hmul_length, hl; lia).
      assert (hz : forall y, In y Y -> y * eval q y = zero).
      { intros y hy; pose proof (hall y hy) as e; unfold q.
        rewrite <-(star_hmul_eval (Hvec := Hvec) y v (ladd v (repeat (opp one) K))) by (rewrite hl; exact hv).
        exact e. }
      intros j hj.
      pose proof (poly_vanish_mul (Hvec := Hvec) (Fdec := Fdec) q Y hnd ltac:(lia) hy0 hz j) as e.
      unfold q in e.
      rewrite nth_hmul in e by lia.
      rewrite nth_ladd' in e by (rewrite ?repeat_length; lia).
      rewrite nth_repeat' in e by lia.
      destruct (mul_eq_zero (Fdec := Fdec) (Hf := vector_space_field) _ _ e) as [e0 | e0]; [left; exact e0 |].
      right. apply (sub_eq_zero (Hf := vector_space_field)). etransitivity; [| exact e0]; field.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* soundness: C₀ and the bit decomposition                           *)
    (* ---------------------------------------------------------------- *)

    (* C₀ opened as h₁^{ρ*}: the committed vector is zero entry by entry *)
    Lemma C0_open : forall (d b p : list F) (X : nat -> list F) (rd rb rp rs : F) (rX : nat -> F) (CX : list G),
      length gs1 = K -> length d = K -> length b = K -> length p = K -> (forall t, (t < L)%nat -> length (X t) = K) ->
      length CX = L -> (forall t, (t < L)%nat -> nth t CX gid = com h1 gs1 (X t) (rX t)) ->
      C0 (com h1 gs1 d rd) (com h1 gs1 b rb) (com h1 gs1 p rp) CX = h1 ^ rs ->
      binding_break h1 gs1 \/
      forall k, (k < K)%nat ->
        fsum (fun t => pow2F t * nth k (X t) zero) L + nth k d zero - (one + one) * nth k p zero + nth k b zero = zero.
    Proof.
      intros * hg1 hd hb hp hX hCX eCX e.
      assert (eC : CX = map (fun t => com h1 gs1 (X t) (rX t)) (seq 0 L)).
      { apply (nth_ext _ _ gid gid); [rewrite map_length, seq_length; exact hCX |].
        intros t ht; rewrite hCX in ht; rewrite nth_map_seq by exact ht; apply eCX; exact ht. }
      rewrite eC, (C0_com d b p rd rb rp X rX hd hb hp hX) in e.
      rewrite <-(com_zeros h1 gs1 K rs) in e.
      assert (hlc : length (lincomb K pow2F X 0 L) = K) by (apply lincomb_length; intros t ht; apply hX; lia).
      assert (hls : length (lscale (opp (one + one)) p) = K) by (rewrite lscale_length'; exact hp).
      assert (hl1 : length (ladd d b) = K) by (rewrite ladd_length'; lia).
      assert (hl2 : length (ladd (lscale (opp (one + one)) p) (lincomb K pow2F X 0 L)) = K) by (rewrite ladd_length'; lia).
      assert (hl3 : length (ladd (ladd d b) (ladd (lscale (opp (one + one)) p) (lincomb K pow2F X 0 L))) = K)
        by (rewrite ladd_length'; lia).
      destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 _ _ _ _ ltac:(rewrite hl3; exact (eq_sym hg1))
        ltac:(rewrite repeat_length; exact (eq_sym hg1)) e) as [(ev & _) | hbk]; [right | left; exact hbk].
      intros k hk.
      pose proof (f_equal (fun l => nth k l zero) ev) as ek; cbn beta in ek.
      rewrite nth_repeat' in ek by exact hk.
      rewrite nth_ladd' in ek by (rewrite ?hl1, ?hl2; try reflexivity; exact hk).
      rewrite nth_ladd' in ek by (rewrite ?hd, ?hb; try reflexivity; exact hk).
      rewrite nth_ladd' in ek by (rewrite ?hls, ?hlc; try reflexivity; exact hk).
      rewrite nth_lscale' in ek by (rewrite hp; exact hk).
      rewrite nth_lincomb in ek by (try exact hk; intros t ht; apply hX; lia).
      rewrite (fsum_ext _ (fun t => pow2F t * nth k (X t) zero)) in ek by (intros t ht; rewrite Nat.add_0_l; reflexivity).
      transitivity (nth k d zero + nth k b zero + (opp (one + one) * nth k p zero + fsum (fun t => pow2F t * nth k (X t) zero) L));
        [field | exact ek].
    Qed.

    (* the bit vectors stacked as one vector of length L·K, as decode_positions reads them *)
    Definition Xflat (X : nat -> list F) : list F :=
      map (fun u => nth (u mod K) (X (u / K)) zero) (seq 0 (L * K)).

    Lemma Xflat_length : forall X, length (Xflat X) = (L * K)%nat.
    Proof. intros; unfold Xflat; rewrite map_length, seq_length; reflexivity. Qed.

    Lemma nth_Xflat : forall X t k, (t < L)%nat -> (k < K)%nat -> nth (t * K + k) (Xflat X) zero = nth k (X t) zero.
    Proof.
      intros X t k ht hk; pose proof K_pos.
      unfold Xflat; rewrite nth_map_seq by nia.
      rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.div_add by lia.
      rewrite Nat.mod_small, Nat.div_small by lia; reflexivity.
    Qed.

    Lemma vbits_Xflat : forall X k, (k < K)%nat -> vbits (Xflat X) k = fsum (fun t => pow2F t * nth k (X t) zero) L.
    Proof.
      intros; unfold SchulzeBatched.vbits; apply fsum_ext; intros t ht; rewrite nth_Xflat by assumption; reflexivity.
    Qed.

    Lemma Xflat_bits : forall X, (forall t k, (t < L)%nat -> (k < K)%nat -> nth k (X t) zero = zero \/ nth k (X t) zero = one) ->
      forall j, (j < L * K)%nat -> nth j (Xflat X) zero = zero \/ nth j (Xflat X) zero = one.
    Proof.
      intros X hX j hj; pose proof K_pos; unfold Xflat; rewrite nth_map_seq by exact hj.
      apply hX; [apply Nat.Div0.div_lt_upper_bound; lia | apply Nat.mod_upper_bound; lia].
    Qed.

    (* ---------------------------------------------------------------- *)
    (* soundness: the theorem                                            *)
    (* ---------------------------------------------------------------- *)

    (* a prover accepted by the linear argument on a base β and on a β
       differing in each single coordinate (two challenges each), and by the
       zero argument on K distinct non-zero y and L + 2 distinct non-zero z
       (2(L+3)+1 challenges each), either breaks the binding of the commitment
       key or has committed to one ranking: positions pos with every pairwise
       ciphertext encrypting [pos_i < pos_j] *)
    Theorem ballot3_sound : forall (x : F) (bt : ballot3) (beta0 : list F) (c0 c1 : F) (Y Z : list F),
      h = g ^ x -> (1 <= L)%nat -> length gs1 = K -> natF_injective (3 * Nat.pow 2 L + 2) ->
      length (b3_cs bt) = K -> length (b3_CX bt) = L -> length beta0 = K -> c0 <> c1 ->
      lin_accepts3 beta0 bt c0 c1 ->
      (forall k, (k < K)%nat -> exists beta', differ_at k beta' beta0 /\ lin_accepts3 beta' bt c0 c1) ->
      NoDup Y -> length Y = K -> (forall y, In y Y -> y <> zero) ->
      NoDup Z -> length Z = (L + 2)%nat -> (forall z, In z Z -> z <> zero) ->
      (forall y z, In y Y -> In z Z -> zero_accepts h1 gs1 (zA z bt) (zB bt) y) ->
      binding_break h1 gs1 \/
      exists (pos : Vector.t nat m),
        (forall i, (Vector.nth pos i <= 2 * Nat.pow 2 L)%nat) /\
        forall i j : Fin.t m,
          cdec x (nth (fin_idx i * m + fin_idx j) (b3_cs bt) cid) =
          g ^ (if Nat.ltb (Vector.nth pos i) (Vector.nth pos j) then one else zero).
    Proof.
      intros x bt beta0 c0 c1 Y Z hh hL hg1 hinj hcs hCX hb0l hc hacc0 hfamb hndY hY hy0 hndZ hZ hz0 hzero.
      pose proof K_pos as hK; pose proof (m_le_K (n := n)) as hmle.
      (* the base witness *)
      destruct (lin_open3 beta0 bt c0 c1 hc hacc0) as (w0 & hw0 & hphi0).
      destruct (phi3_target_open beta0 bt w0 hphi0) as (eCd & eCb & ecb0 & eC0).
      set (s0 := wslice w0 0 m) in *; set (b0 := wslice w0 oB3 K) in *; set (d0 := Ms s0) in *.
      assert (hs0 : length s0 = m) by apply wslice_length.
      assert (hb0 : length b0 = K) by apply wslice_length.
      assert (hd0 : length d0 = K) by apply Ms_length.
      (* any other accepted β opens C_b to b0, or breaks the key *)
      assert (hagree : forall beta, length beta = K -> lin_accepts3 beta bt c0 c1 ->
        binding_break h1 gs1 \/ exists Rb, cbeta beta (b3_cs bt) = enc g h (dot beta b0 K) Rb).
      { intros beta hbl hacc.
        destruct (lin_open3 beta bt c0 c1 hc hacc) as (w & hw & hphi).
        destruct (phi3_target_open beta bt w hphi) as (_ & eCb' & ecb & _).
        assert (hl1 : length (wslice w oB3 K) = length gs1) by (rewrite wslice_length; exact (eq_sym hg1)).
        assert (hl2 : length b0 = length gs1) by (rewrite hb0; exact (eq_sym hg1)).
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 _ _ _ _ hl1 hl2
          (eq_trans (eq_sym eCb') eCb)) as [(eb & _) | hbk]; [| left; exact hbk].
        right; exists (wat w (oR3 + 2)); rewrite ecb, eb; reflexivity. }
      (* every ciphertext encrypts its committed bit *)
      assert (hbits : binding_break h1 gs1 \/
        forall k, (k < K)%nat -> cdec x (nth k (b3_cs bt) cid) = g ^ nth k b0 zero).
      { destruct (forall_or (fun k => exists beta', differ_at k beta' beta0 /\ cdec x (cbeta beta' (b3_cs bt)) = g ^ dot beta' b0 K)
          (binding_break h1 gs1) K) as [hfam | hbk]; [| right | left; exact hbk].
        - intros k hk; destruct (hfamb k hk) as (beta' & hd & hacc).
          destruct (hagree beta' (proj1 hd) hacc) as [hbk | (Rb & ecb)]; [right; exact hbk |].
          left; exists beta'; split; [exact hd |]. rewrite ecb; apply (cdec_enc (Hvec := Hvec)); exact hh.
        - apply (beta_bits (Hvec := Hvec) g h x (b3_cs bt) beta0 b0 hh hcs hb0); [| exact hfam].
          rewrite ecb0; apply (cdec_enc (Hvec := Hvec)); exact hh. }
      (* the reference openings of C_p and the C_X(t), from one accepted zero argument *)
      assert (hY1 : (1 <= length Y)%nat) by lia.
      assert (hZ1 : (1 <= length Z)%nat) by lia.
      assert (hy0in : In (nth 0 Y zero) Y) by (apply nth_In; lia).
      assert (hz0in : In (nth 0 Z zero) Z) by (apply nth_In; lia).
      destruct (zero_open_ref bt (nth 0 Y zero) (nth 0 Z zero) hg1 (hz0 _ hz0in) (hzero _ _ hy0in hz0in))
        as [hbk | (p & rp & X & rX & hp & hX & eCp & eCX)]; [left; exact hbk |].
      (* every accepted (y, z) gives the weighted sum on the same openings *)
      assert (hsums : binding_break h1 gs1 \/
        forall y z, In y Y -> In z Z -> fsum (fun i => zwt z i * star y (vecA b0 p X i) (vecB d0 b0 p X i)) R = zero).
      { destruct (forall_or (fun iy => forall iz, (iz < length Z)%nat ->
          fsum (fun i => zwt (nth iz Z zero) i * star (nth iy Y zero) (vecA b0 p X i) (vecB d0 b0 p X i)) R = zero)
          (binding_break h1 gs1) (length Y)) as [hall | hbk]; [| right | left; exact hbk].
        - intros iy hiy.
          destruct (forall_or (fun iz => fsum (fun i => zwt (nth iz Z zero) i *
              star (nth iy Y zero) (vecA b0 p X i) (vecB d0 b0 p X i)) R = zero) (binding_break h1 gs1) (length Z))
            as [hall | hbk]; [| left; exact hall | right; exact hbk].
          intros iz hiz.
          destruct (zero_open_at bt (nth iy Y zero) (nth iz Z zero) d0 b0 p X _ _ rp rX hg1 hb0 hd0 hp hX eCb eCd eCp eCX
            (hzero _ _ (nth_In Y zero hiy) (nth_In Z zero hiz))) as [hbk | e]; [right; exact hbk | left; exact e].
        - intros y z hy hz.
          destruct (In_nth Y y zero hy) as (iy & hiy & ey); destruct (In_nth Z z zero hz) as (iz & hiz & ez).
          rewrite <-ey, <-ez; exact (hall iy hiy iz hiz). }
      destruct hsums as [hbk | hsums]; [left; exact hbk |].
      (* separate the rows by z, then the coordinates by y *)
      assert (hrows : forall y, In y Y ->
        star y b0 d0 + star y p (repeat (opp one) K) = zero /\
        forall t, (t < S L)%nat -> star y (vecA b0 p X (S (S t))) (vecB d0 b0 p X (S (S t))) = zero).
      { intros y hy; apply (coeffs_vanish y d0 b0 p X Z hndZ hZ hz0); intros z hz; exact (hsums y z hy hz). }
      assert (hprod : forall j, (j < K)%nat -> nth j p zero = nth j b0 zero * nth j d0 zero).
      { apply (prod_of_star b0 p d0 Y hb0 hp hd0 hndY hY hy0); intros y hy; exact (proj1 (hrows y hy)). }
      assert (hXbits : forall t k, (t < L)%nat -> (k < K)%nat -> nth k (X t) zero = zero \/ nth k (X t) zero = one).
      { intros t k ht hk; apply (bits_of_star (X t) Y (hX t ht) hndY hY hy0); [| exact hk].
        intros y hy; pose proof (proj2 (hrows y hy) t ltac:(lia)) as e; cbn [vecA vecB] in e.
        rewrite (proj2 (Nat.ltb_lt t L) ht) in e; exact e. }
      assert (hbbits : forall k, (k < K)%nat -> nth k b0 zero = zero \/ nth k b0 zero = one).
      { apply (bits_of_star b0 Y hb0 hndY hY hy0).
        intros y hy; pose proof (proj2 (hrows y hy) L ltac:(lia)) as e; cbn [vecA vecB] in e.
        rewrite Nat.ltb_irrefl in e; exact e. }
      (* C₀: the binary expansion of v *)
      rewrite eCd, eCb, eCp in eC0.
      destruct (C0_open d0 b0 p X _ _ rp _ rX (b3_CX bt) hg1 hd0 hb0 hp hX hCX eCX eC0) as [hbk | hrow]; [left; exact hbk |].
      destruct hbits as [hbk | hbits]; [left; exact hbk |].
      (* decode *)
      assert (hdm : forall k, (k < K)%nat -> nth k d0 zero = nth (k mod m) s0 zero - nth (k / m) s0 zero).
      { intros k hk; unfold d0; apply nth_Ms; exact hk. }
      assert (hXf : length (Xflat X) = SchulzeBatched.NX (n := n) L) by (rewrite Xflat_length; reflexivity).
      assert (hrow' : forall k, (k < K)%nat ->
        vbits (Xflat X) k + nth k d0 zero - (one + one) * nth k p zero + nth k b0 zero = zero).
      { intros k hk; rewrite vbits_Xflat by exact hk; exact (hrow k hk). }
      pose proof (decode_positions (Hvec := Hvec) (Fdec := Fdec) L s0 d0 b0 p (Xflat X) hs0 hd0 hb0 hp hXf hinj hdm hbbits
        (Xflat_bits X hXbits) hprod hrow') as hdec.
      right.
      exists (Vector.map (fun i => posn b0 (Xflat X) (fin_idx i)) (fin_enum m)); split.
      + intro i; rewrite (Vector.nth_map _ _ i i eq_refl), fin_enum_nth; apply posn_le.
      + intros i j; rewrite (Vector.nth_map _ _ i i eq_refl), (Vector.nth_map _ _ j j eq_refl), !fin_enum_nth.
        pose proof (fin_idx_lt m i) as hi; pose proof (fin_idx_lt m j) as hj.
        rewrite hbits by (unfold SchulzeBatched.K; nia).
        rewrite hdec by assumption.
        destruct (Nat.ltb (posn b0 (Xflat X) (fin_idx i)) (posn b0 (Xflat X) (fin_idx j)));
          [rewrite (natF_one (Hvec := Hvec)) | cbn [nat_to_F]]; reflexivity.
    Qed.

    (* the rewinding hypotheses of ballot3_sound as one predicate on the ballot *)
    Definition ballot3_rewound (bt : ballot3) : Prop :=
      length (b3_cs bt) = K /\ length (b3_CX bt) = L /\
      exists (beta0 : list F) (c0 c1 : F) (Y Z : list F),
        length beta0 = K /\ c0 <> c1 /\
        lin_accepts3 beta0 bt c0 c1 /\
        (forall k, (k < K)%nat -> exists beta', differ_at k beta' beta0 /\ lin_accepts3 beta' bt c0 c1) /\
        NoDup Y /\ length Y = K /\ (forall y, In y Y -> y <> zero) /\
        NoDup Z /\ length Z = (L + 2)%nat /\ (forall z, In z Z -> z <> zero) /\
        (forall y z, In y Y -> In z Z -> zero_accepts h1 gs1 (zA z bt) (zB bt) y).

    (* soundness restated on the m × m matrix of ciphertexts *)
    Corollary ballot3_sound_bits : forall (x : F) (bt : ballot3),
      h = g ^ x -> (1 <= L)%nat -> length gs1 = K -> natF_injective (3 * Nat.pow 2 L + 2) ->
      ballot3_rewound bt ->
      binding_break h1 gs1 \/
      exists (pos : Vector.t nat m),
        (forall i, (Vector.nth pos i <= 2 * Nat.pow 2 L)%nat) /\
        forall i j : Fin.t m, cdec x (Vector.nth (Vector.nth (ballot3_bits bt) i) j) =
          g ^ (if Nat.ltb (Vector.nth pos i) (Vector.nth pos j) then one else zero).
    Proof.
      intros x bt hh hL hg1 hinj (hcs & hCX & beta0 & c0 & c1 & Y & Z & hb0 & hc & hacc & hf & hndY & hY & hy0 & hndZ & hZ & hz0 & hz).
      destruct (ballot3_sound x bt beta0 c0 c1 Y Z hh hL hg1 hinj hcs hCX hb0 hc hacc hf hndY hY hy0 hndZ hZ hz0 hz)
        as [hbk | (pos & hpos & hdec)]; [left; exact hbk | right].
      exists pos; split; [exact hpos |].
      intros i j; unfold ballot3_bits.
      rewrite (Vector.nth_map _ _ i i eq_refl), (Vector.nth_map _ _ j j eq_refl), !fin_enum_nth.
      apply hdec.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* special honest-verifier zero knowledge                            *)
    (* ---------------------------------------------------------------- *)

    (* The honest ballot, as a distribution over the voter's randomness, is
       a permutation of the output of a simulator that has the ciphertexts
       and the challenges only: the L + 3 commitments are uniform in the
       group generated by h₁ (the key has known discrete logarithms in base
       h₁, as in the library's zero-argument simulator; the derived key
       inherits them through com_gd), and the linear proof and the zero
       argument are simulated from the commitments by the library's
       simulators. *)
    Import Distr.
    Section ZK3.
      Context (lf : list F) (Hlfn : lf <> []).
      Context (γ : list F).
      Hypothesis hg1 : length gs1 = K.
      Hypothesis hγl : length γ = K.
      Hypothesis hγ : forall j, (j < K)%nat -> nth j gs1 gid = h1 ^ (nth j γ zero).

      Local Notation lin_real_distribution := (lin_real_distribution (add := add) (mul := mul)).
      Local Notation lin_sim_distribution := (lin_sim_distribution (vopp := vec_opp (vopp := ginv))
        (vadd := vec_add (vadd := gop)) (smul := vec_smul (smul := gpow))).
      Local Notation zero_real_distribution := (BayerGrothZK.zero_real_distribution (zero := zero) (one := one)
        (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)).
      Local Notation zero_sim_distribution := (zero_sim_distribution (zero := zero) (one := one) (add := add) (mul := mul)
        (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)).
      Local Notation zdot := (BayerGrothZK.dot (zero := zero) (add := add) (mul := mul)).
      Local Notation NC := (L + 3)%nat.

      Lemma bind_ext3 : forall {A B : Type} (d : dist A) (f f' : A -> dist B),
        (forall a, f a = f' a) -> Bind d f = Bind d f'.
      Proof. intros A B d f f' e; induction d as [| (a & p) d ih]; [reflexivity | cbn; rewrite e, ih; reflexivity]. Qed.

      (* the commitment randomness of the bit vectors: entries 3, …, L + 2 of t *)
      Definition tX (t : list F) : list F := map (fun j => nth (3 + j) t zero) (seq 0 L).
      Lemma tX_length : forall t, length (tX t) = L.
      Proof. intros; unfold tX; rewrite map_length, seq_length; reflexivity. Qed.

      (* the voter's randomness as four independent uniform draws: the K
         encryption randomnesses, the L + 3 commitment randomnesses, the
         announcement of the linear proof and the randomness of the zero
         argument in the library's layout *)
      Definition rand3_of (r t a l : list F) : rand3 :=
        mk_rand3 r (nth 0 t zero) (nth 1 t zero) (nth 2 t zero) (tX t) a
          (slice l 0 (length gs1)) (slice l (length gs1) (length gs1))
          (nth (2 * length gs1) l zero) (nth (2 * length gs1 + 1) l zero)
          (slice l (2 * length gs1 + 2) (S R)) (slice l (2 * length gs1 + 3 + R) (R - 1)).

      Definition honest_cs3 (sn : list nat) (r : list F) : list (G * G) :=
        map (fun k => enc g h (natF (pos_bit sn k)) (nth k r zero)) (seq 0 K).

      (* the honest voter *)
      Definition ballot3_real_dist (ch : chal3) (sn : list nat) : dist ballot3 :=
        Bind (rand lf Hlfn K) (fun r => Bind (rand lf Hlfn NC) (fun t => Bind (rand lf Hlfn W3) (fun a =>
        Bind (rand lf Hlfn (zR gs1 R)) (fun l =>
          Ret (encrypt_ballot3 ch sn (rand3_of r t a l)))))).

      (* a ballot with the given ciphertexts and commitments; only those
         fields are read by target3, zA and zB *)
      Definition sim_bt (cs : list (G * G)) (C : list G) : ballot3 :=
        mk_ballot3 cs (nth 0 C gid) (nth 1 C gid) (nth 2 C gid) (skipn 3 C)
          (mk_lin (vec5 gid gid gid gid gid) []) (mk_zero gid gid [] [] [] zero zero zero).

      (* the simulator of the proofs, from the ciphertexts and the L + 3 commitments *)
      Definition sim_proofs3 (ch : chal3) (cs : list (G * G)) (C : list G) : dist ballot3 :=
        let bt0 := sim_bt cs C in
        Bind (lin_sim_distribution W3 (phi3 (c3_beta ch)) lf Hlfn (target3 (c3_beta ch) bt0) (c3_c ch)) (fun lp =>
        Bind (zero_sim_distribution h1 gs1 (c3_y ch) (c3_x ch) R lf Hlfn (zA (c3_z ch) bt0) (zB bt0)) (fun za =>
          Ret (mk_ballot3 cs (nth 0 C gid) (nth 1 C gid) (nth 2 C gid) (skipn 3 C) lp za))).

      (* the simulator of a ballot: L + 3 uniform commitments, then the proofs *)
      Definition ballot3_sim_dist (ch : chal3) (cs : list (G * G)) : dist ballot3 :=
        Bind (rand lf Hlfn NC) (fun u => sim_proofs3 ch cs (map (fun e => h1 ^ e) u)).

      (* the honest commitments *)
      Definition com_vals3 (sn : list nat) (t : list F) : list G :=
        [com h1 gd (hon_s sn) (nth 0 t zero); com h1 gs1 (hon_b sn) (nth 1 t zero); com h1 gs1 (hon_p sn) (nth 2 t zero)] ++
        map (fun i => com h1 gs1 (hon_Xt sn i) (nth i (tX t) zero)) (seq 0 L).

      (* the honest proofs given the ciphertexts and the commitment randomness *)
      Definition real_proofs3 (ch : chal3) (sn : list nat) (r t : list F) : dist ballot3 :=
        let rd0 := rand3_of r t [] [] in
        let C := com_vals3 sn t in
        Bind (lin_real_distribution W3 (phi3 (c3_beta ch)) lf Hlfn (hon_w3 (c3_beta ch) sn rd0) (c3_c ch)) (fun lp =>
        Bind (zero_real_distribution h1 gs1
                (map (fun i => lscale (zwt (c3_z ch) i) (hon_vecA sn i)) (seq 0 R)) (map (hon_vecB sn) (seq 0 R))
                (map (fun i => zwt (c3_z ch) i * hon_rA rd0 i) (seq 0 R)) (map (hon_rB rd0) (seq 0 R))
                (c3_y ch) (c3_x ch) R lf Hlfn) (fun za =>
          Ret (mk_ballot3 (honest_cs3 sn r) (nth 0 C gid) (nth 1 C gid) (nth 2 C gid) (skipn 3 C) lp za))).

      Lemma real_dist_proofs3 : forall ch sn,
        ballot3_real_dist ch sn = Bind (rand lf Hlfn K) (fun r => Bind (rand lf Hlfn NC) (fun t => real_proofs3 ch sn r t)).
      Proof.
        intros ch sn; unfold ballot3_real_dist, real_proofs3, lin_real_distribution, BayerGrothZK.zero_real_distribution.
        apply bind_ext3; intro r; apply bind_ext3; intro t.
        rewrite !bind_assoc; apply bind_ext3; intro a. rewrite bind_ret_left.
        rewrite !bind_assoc; apply bind_ext3; intro l. rewrite bind_ret_left.
        reflexivity.
      Qed.

      (* given the ciphertexts and the commitments, the proofs are simulatable *)
      Lemma real_proofs_perm3 : forall (ch : chal3) (sn : list nat) (r t : list F),
        NoDup lf -> (forall v : F, In v lf) ->
        length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
        length (c3_beta ch) = K ->
        Permutation (real_proofs3 ch sn r t) (sim_proofs3 ch (honest_cs3 sn r) (com_vals3 sn t)).
      Proof.
        intros ch sn r t hnd hall hsn hs hL hb.
        pose proof K_pos as hK.
        unfold real_proofs3, sim_proofs3; cbv zeta.
        set (rd0 := rand3_of r t [] []).
        replace (target3 (c3_beta ch) (sim_bt (honest_cs3 sn r) (com_vals3 sn t)))
          with (phi3 (c3_beta ch) (hon_w3 (c3_beta ch) sn rd0))
          by (rewrite <-(target3_phi3 ch sn rd0); [reflexivity | assumption ..]).
        eapply Permutation_trans; [apply bind_perm_left; apply (lin_shvzk (HV := G5vs) W3 (phi3 (c3_beta ch))
          (phi3_add (c3_beta ch)) (phi3_scale (c3_beta ch))); [apply hon_w3_length; exact hsn | exact hnd | exact hall] |].
        apply bind_perm_right; intros lp _ _.
        change (zA (c3_z ch) (sim_bt (honest_cs3 sn r) (com_vals3 sn t))) with (zA (c3_z ch) (encrypt_ballot3 ch sn rd0)).
        change (zB (sim_bt (honest_cs3 sn r) (com_vals3 sn t))) with (zB (encrypt_ballot3 ch sn rd0)).
        rewrite hon_zA by apply tX_length. rewrite hon_zB by (try apply tX_length; exact hsn).
        eapply Permutation_trans; [apply bind_perm_left; apply (zero_shvzk (Hvec := Hvec) (Gdec := Gdec) h1 gs1 γ);
          rewrite ?map_length, ?seq_length; try (unfold R; lia); try assumption;
          first [ apply Forall_map, Forall_forall; intros i _;
                  rewrite ?lscale_length', ?hon_vecA_length, ?hon_vecB_length; exact (eq_sym hg1)
                | rewrite hg1; exact hγl
                | rewrite hg1; exact hγ
                | apply hon_zero_sum; exact hsn ] |].
        apply bind_perm_right; intros za _ _. apply Permutation_refl.
      Qed.

      (* the commitments are uniform: the bijection t ↦ t + ⟨γ, v⟩ on the
         L + 3 commitment randomnesses, where C_δ is read as com_{gs₁}(δ) *)
      Definition dlog3 (sn : list nat) (i : nat) : F :=
        match i with
        | 0 => zdot γ (hon_d sn) | 1 => zdot γ (hon_b sn) | 2 => zdot γ (hon_p sn)
        | S (S (S j)) => zdot γ (hon_Xt sn j)
        end.
      Definition com_phi3 (sn : list nat) (t : list F) : list F :=
        map (fun i => nth i t zero + dlog3 sn i) (seq 0 NC).
      Definition com_psi3 (sn : list nat) (u : list F) : list F :=
        map (fun i => nth i u zero - dlog3 sn i) (seq 0 NC).

      Lemma com_vals3_length : forall sn t, length (com_vals3 sn t) = NC.
      Proof. intros; unfold com_vals3; rewrite app_length, map_length, seq_length; cbn [length]; lia. Qed.

      Lemma com_vals_perm3 : forall (sn : list nat), NoDup lf -> (forall v : F, In v lf) -> length sn = m ->
        Permutation (Bind (rand lf Hlfn NC) (fun t => Ret (com_vals3 sn t)))
                    (Bind (rand lf Hlfn NC) (fun u => Ret (map (fun e => h1 ^ e) u))).
      Proof.
        intros sn hnd hall hsn.
        assert (k1 : length γ = length gs1) by congruence.
        assert (k2 : forall j, (j < length gs1)%nat -> nth j gs1 gid = h1 ^ nth j γ zero) by (rewrite hg1; exact hγ).
        apply (zk_of_bijection (zero := zero) lf Hlfn NC (com_vals3 sn) (map (fun e => h1 ^ e)) (com_phi3 sn) (com_psi3 sn) hnd hall).
        + intros l hl; unfold com_phi3; rewrite map_length, seq_length; reflexivity.
        + intros l hl; unfold com_psi3; rewrite map_length, seq_length; reflexivity.
        + intros l hl; unfold com_psi3, com_phi3; apply (nth_ext _ _ zero zero);
            [rewrite map_length, seq_length; exact (eq_sym hl) |].
          intros i hi; rewrite map_length, seq_length in hi; rewrite !nth_map_seq by exact hi; field.
        + intros l hl; unfold com_psi3, com_phi3; apply (nth_ext _ _ zero zero);
            [rewrite map_length, seq_length; exact (eq_sym hl) |].
          intros i hi; rewrite map_length, seq_length in hi; rewrite !nth_map_seq by exact hi; field.
        + intros l hl. apply (nth_ext _ _ gid gid).
          { rewrite com_vals3_length; unfold com_phi3; rewrite !map_length, seq_length; reflexivity. }
          intros i hi; rewrite com_vals3_length in hi.
          unfold com_phi3; rewrite map_map, nth_map_seq by exact hi.
          destruct i as [| [| [| j]]]; cbn [com_vals3 app nth dlog3].
          * rewrite com_gd by (apply hon_s_length; exact hsn); rewrite Ms_hon by exact hsn.
            apply (com_dlog (Hvec := Hvec)); assumption.
          * apply (com_dlog (Hvec := Hvec)); assumption.
          * apply (com_dlog (Hvec := Hvec)); assumption.
          * rewrite nth_map_seq by lia. unfold tX; rewrite nth_map_seq by lia.
            apply (com_dlog (Hvec := Hvec)); assumption.
      Qed.

      (* SHVZK of the simplified ballot: for valid positions, the honest
         ballot is distributed as the simulator's output given the
         ciphertexts *)
      Theorem ballot3_zk : forall (ch : chal3) (sn : list nat),
        NoDup lf -> (forall v : F, In v lf) ->
        length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
        length (c3_beta ch) = K ->
        Permutation (ballot3_real_dist ch sn)
                    (Bind (rand lf Hlfn K) (fun r => ballot3_sim_dist ch (honest_cs3 sn r))).
      Proof.
        intros ch sn hnd hall hsn hs hL hb.
        rewrite real_dist_proofs3. apply bind_perm_right; intros r _ _.
        unfold ballot3_sim_dist.
        transitivity (Bind (Bind (rand lf Hlfn NC) (fun t => Ret (com_vals3 sn t))) (fun C => sim_proofs3 ch (honest_cs3 sn r) C)).
        { rewrite bind_assoc. apply bind_perm_right; intros t p hin. rewrite bind_ret_left.
          apply real_proofs_perm3; assumption. }
        eapply Permutation_trans; [apply bind_perm_left; apply com_vals_perm3; assumption |].
        rewrite bind_assoc. apply bind_perm_right; intros u _ _. rewrite bind_ret_left. apply Permutation_refl.
      Qed.

    End ZK3.

  End Ballot3.

End SchulzeSimple.
