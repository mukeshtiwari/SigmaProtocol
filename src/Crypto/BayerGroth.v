(* The Bayer–Groth argument for the correctness of a shuffle (S. Bayer,
   J. Groth, "Efficient Zero-Knowledge Argument for Correctness of a
   Shuffle", EUROCRYPT 2012), in the variant of the Swiss Post Voting System
   ("Cryptographic Primitives of the Swiss Post Voting System", pseudocode
   specification version 1.6.0, Section 9: Algorithms 9.7–9.26), built from
   the library's algebra.

   The shuffle argument is the composition of five sub-arguments over
   Pedersen commitments com(a; r) = h^r ∏ g_i^{a_i} to vectors of Z_q and
   ElGamal ciphertexts of the multi-recipient form (g^r, pk_1^r m_1, …):

     single value product   ∏ a_i = b for a committed vector a          (9.25/9.26)
     zero                   Σ_i a_i ⋆ b_{i−1} = 0 for committed matrices  (9.22/9.23)
     Hadamard               b = a_0 ∘ ⋯ ∘ a_{m−1} for committed columns   (9.20/9.21)
     product                ∏_{i,j} a_{i,j} = b for a committed matrix    (9.18/9.19)
     multi-exponentiation   C = Enc(1; ρ) ∏_i C_i^{a_i} for committed a  (9.15/9.16)

   and the shuffle argument itself (9.11/9.12): commit to the permutation,
   receive x, commit to x^{π(i)}, receive y, z, and prove with the product
   argument that ∏ (y·π(i) + x^{π(i)} − z) = ∏ (y·i + x^i − z) and with the
   multi-exponentiation argument that ∏ C_i^{x^i} = Enc(1; ρ) ∏ C'_i^{x^{π(i)}}.

   Vectors of Z_q and of group elements are lists; a ciphertext with ℓ
   recipients is a vector of ℓ + 1 group elements, so that the ciphertext
   space is the product vector space of Algebra/Vector_product_space.v and
   the multi-exponentiation of ciphertexts is the same fold as the one of
   group elements. The challenges are parameters of the verifiers (the
   protocols are interactive here; Backend/BayerGrothVerifier.v adds the
   Fiat–Shamir challenges as oracles). This file contains, for each
   sub-argument, the verifier of the specification, the prover with its
   randomness as parameters, and the completeness theorem: the honest
   prover's argument is accepted for every challenge. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List Arith
  RelationClasses Morphisms.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma MultiExp OkamotoRows PolyRoots SigmaK.
From Utility Require Import Util.
Import ListNotations.

Section BayerGroth.

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

  (* the scalar helpers of Crypto/SigmaK.v at the operations of the context *)
  Local Notation lscale := (lscale (mul := mul)).
  Local Notation ladd := (ladd (add := add)).
  Local Notation fpow := (fpow (one := one) (mul := mul)).
  Local Notation lpows := (lpows (one := one) (mul := mul)).
  Local Notation padd := (padd (add := add)).
  Local Notation fnat := (fnat (zero := zero) (one := one) (add := add)).

  Local Notation gcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation ggroup := (@commutative_group_group G (@eq G) gop gid ginv gcg).
  Local Notation gmonoid := (@group_monoid G (@eq G) gop gid ginv ggroup).
  Local Notation gassoc := (@associative G (@eq G) gop
    (@monoid_is_associative G (@eq G) gop gid gmonoid)).
  Local Notation gid_l := (@left_identity G (@eq G) gop gid
    (@monoid_is_left_idenity G (@eq G) gop gid gmonoid)).
  Local Notation gid_r := (@right_identity G (@eq G) gop gid
    (@monoid_is_right_identity G (@eq G) gop gid gmonoid)).
  Local Notation gcomm := (@commutative G (@eq G) gop
    (@commutative_group_is_commutative G (@eq G) gop gid ginv gcg)).
  Local Notation ginv_l := (@left_inverse G (@eq G) gop gid ginv
    (@group_is_left_inverse G (@eq G) gop gid ginv ggroup)).
  Local Notation ginv_r := (@right_inverse G (@eq G) gop gid ginv
    (@group_is_right_inverse G (@eq G) gop gid ginv ggroup)).
  Local Notation pow_opp := (pow_opp (Hvec := Hvec)).
  Local Notation gpow_add := (gpow_add (Hvec := Hvec)).
  Local Notation gpow_mul := (gpow_mul (Hvec := Hvec)).
  Local Notation gpow_one := (gpow_one (Hvec := Hvec)).
  Local Notation gpow_zero := (gpow_zero (Hvec := Hvec)).
  Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
  Local Notation gop4 := (gop4 (Hvec := Hvec)).
  Local Notation gid_pow := (smul_vid (HV := Hvec)).

  (* ---------------------------------------------------------------- *)
  (* The field as a vector space over itself                          *)
  (* ---------------------------------------------------------------- *)

  Lemma Fadd_assoc : forall x y z : F, x + (y + z) = (x + y) + z. Proof. intros; field. Qed.
  Lemma Fadd_id_l : forall x : F, zero + x = x. Proof. intros; field. Qed.
  Lemma Fadd_id_r : forall x : F, x + zero = x. Proof. intros; field. Qed.
  Lemma Fadd_opp_l : forall x : F, opp x + x = zero. Proof. intros; field. Qed.
  Lemma Fadd_opp_r : forall x : F, x + opp x = zero. Proof. intros; field. Qed.
  Lemma Fadd_comm : forall x y : F, x + y = y + x. Proof. intros; field. Qed.
  Lemma Fadd_proper : Proper (eq ==> eq ==> eq) add. Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Fopp_proper : Proper (eq ==> eq) opp. Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Fmul_proper : Proper (eq ==> eq ==> eq) mul. Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Fmul_one_r : forall x : F, x * one = x. Proof. intros; field. Qed.
  Lemma Fmul_zero_r : forall x : F, x * zero = zero. Proof. intros; field. Qed.
  Lemma Fmul_assoc : forall (r1 r2 x : F), x * (r1 * r2) = (x * r1) * r2. Proof. intros; field. Qed.
  Lemma Fmul_fadd : forall (r1 r2 x : F), x * (r1 + r2) = x * r1 + x * r2. Proof. intros; field. Qed.
  Lemma Fmul_vadd : forall (r x y : F), (x + y) * r = x * r + y * r. Proof. intros; field. Qed.

  Definition F_monoid : @monoid F (@eq F) add zero :=
    @Build_monoid F (@eq F) add zero Fadd_assoc Fadd_id_l Fadd_id_r Fadd_proper eq_equivalence.
  Definition F_group : @group F (@eq F) add zero opp :=
    @Build_group F (@eq F) add zero opp F_monoid Fadd_opp_l Fadd_opp_r Fopp_proper.
  Local Instance F_comm_group : @commutative_group F (@eq F) add zero opp :=
    @Build_commutative_group F (@eq F) add zero opp F_group Fadd_comm.
  Local Instance F_vspace :
    @vector_space F (@eq F) zero one add mul sub div opp inv F (@eq F) zero opp add mul :=
    @Build_vector_space F (@eq F) zero one add mul sub div opp inv F (@eq F) zero opp add mul
      F_comm_group (@vector_space_field _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec)
      Fmul_one_r Fmul_zero_r Fmul_assoc Fmul_fadd Fmul_vadd Fmul_proper.

  (* ---------------------------------------------------------------- *)
  (* Lists over a vector space: multi-exponentiation and evaluation    *)
  (* ---------------------------------------------------------------- *)

  Lemma padd_nil_r : forall xs, padd xs [] = xs.
  Proof. intros xs; destruct xs; reflexivity. Qed.

  Lemma padd_length : forall xs ys, length (padd xs ys) = Nat.max (length xs) (length ys).
  Proof.
    induction xs as [| a xs ih]; intros ys; [reflexivity |].
    destruct ys as [| b ys]; [reflexivity | cbn; rewrite ih; reflexivity].
  Qed.

  Lemma lpows_length : forall x k, length (lpows x k) = k.
  Proof. intros x k; induction k as [| k ih]; [reflexivity | cbn; unfold SigmaK.lscale; rewrite map_length, ih; reflexivity]. Qed.

  Section LMexp.

    Context
      {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
      {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

    Local Notation vcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vgroup := (@commutative_group_group V (@eq V) vadd vid vopp vcg).
    Local Notation vmonoid := (@group_monoid V (@eq V) vadd vid vopp vgroup).
    Local Notation vassoc := (@associative V (@eq V) vadd
      (@monoid_is_associative V (@eq V) vadd vid vmonoid)).
    Local Notation vid_l := (@left_identity V (@eq V) vadd vid
      (@monoid_is_left_idenity V (@eq V) vadd vid vmonoid)).
    Local Notation vid_r := (@right_identity V (@eq V) vadd vid
      (@monoid_is_right_identity V (@eq V) vadd vid vmonoid)).
    Local Notation vcomm := (@commutative V (@eq V) vadd
      (@commutative_group_is_commutative V (@eq V) vadd vid vopp vcg)).
    Local Notation vfadd := (@vector_space_smul_distributive_fadd F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vfmul := (@vector_space_smul_associative_fmul F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vvadd := (@vector_space_smul_distributive_vadd F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).
    Local Notation vone := (@vector_space_field_one F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).

    Lemma smul_add : forall (v : V) (r s : F), smul v (r + s) = vadd (smul v r) (smul v s).
    Proof. intros; apply vfadd. Qed.
    Lemma smul_mul : forall (v : V) (r s : F), smul v (r * s) = smul (smul v r) s.
    Proof. intros; apply vfmul. Qed.
    Lemma vadd_smul : forall (u v : V) (r : F), smul (vadd u v) r = vadd (smul u r) (smul v r).
    Proof. intros; apply vvadd. Qed.
    Lemma smul_one : forall v : V, smul v one = v.
    Proof. intros; apply vone. Qed.
    Lemma vadd4 : forall a b c d : V, vadd (vadd a b) (vadd c d) = vadd (vadd a c) (vadd b d).
    Proof.
      intros a b c d.
      rewrite <-(vassoc a b (vadd c d)), (vassoc b c d), (vcomm b c), <-(vassoc c b d),
        (vassoc a c (vadd b d)); reflexivity.
    Qed.

    (* ∏ gs_i^{xs_i} over the common prefix of the two lists *)
    Definition lmexp (gs : list V) (xs : list F) : V :=
      fold_right (fun p acc => vadd (smul (fst p) (snd p)) acc) vid (combine gs xs).

    Lemma lmexp_nil_l : forall xs, lmexp [] xs = vid.
    Proof. reflexivity. Qed.
    Lemma lmexp_nil_r : forall gs, lmexp gs [] = vid.
    Proof. intros gs; destruct gs; reflexivity. Qed.
    Lemma lmexp_cons : forall g gs x xs, lmexp (g :: gs) (x :: xs) = vadd (smul g x) (lmexp gs xs).
    Proof. reflexivity. Qed.

    Lemma lmexp_app : forall gs1 gs2 xs1 xs2, length gs1 = length xs1 ->
      lmexp (gs1 ++ gs2) (xs1 ++ xs2) = vadd (lmexp gs1 xs1) (lmexp gs2 xs2).
    Proof.
      induction gs1 as [| g gs1 ih]; intros gs2 xs1 xs2 hl.
      + destruct xs1; [| discriminate]; cbn [app]; rewrite lmexp_nil_l, vid_l; reflexivity.
      + destruct xs1 as [| x xs1]; [discriminate |]; cbn [app]; rewrite !lmexp_cons, ih; [| cbn in hl; lia].
        rewrite vassoc; reflexivity.
    Qed.

    Lemma lmexp_add : forall gs xs ys, length xs = length ys ->
      lmexp gs (ladd xs ys) = vadd (lmexp gs xs) (lmexp gs ys).
    Proof.
      induction gs as [| g gs ih]; intros xs ys hl; [rewrite !lmexp_nil_l, vid_l; reflexivity |].
      destruct xs as [| x xs]; destruct ys as [| y ys]; try discriminate.
      + rewrite lmexp_nil_r, vid_l; reflexivity.
      + unfold SigmaK.ladd; cbn [combine map fst snd]; rewrite !lmexp_cons; fold (ladd xs ys).
        rewrite ih; [| cbn in hl; lia]. rewrite smul_add, vadd4; reflexivity.
    Qed.

    Lemma lmexp_scale : forall gs xs c, lmexp gs (lscale c xs) = smul (lmexp gs xs) c.
    Proof.
      induction gs as [| g gs ih]; intros xs c.
      + rewrite !lmexp_nil_l; symmetry; apply (smul_vid (HV := HV)).
      + destruct xs as [| x xs]; [rewrite !lmexp_nil_r; symmetry; apply (smul_vid (HV := HV)) |].
        unfold SigmaK.lscale; cbn [map]; rewrite !lmexp_cons; fold (lscale c xs); rewrite ih, vadd_smul, <-smul_mul.
        replace (c * x) with (x * c) by field; reflexivity.
    Qed.

    Lemma lmexp_repeat_vid : forall k xs, lmexp (repeat vid k) xs = vid.
    Proof.
      induction k as [| k ih]; intros xs; [reflexivity |].
      destruct xs as [| x xs]; [apply lmexp_nil_r |].
      cbn [repeat]; rewrite lmexp_cons, ih, (smul_vid (HV := HV)), vid_l; reflexivity.
    Qed.

    (* the bases combined pointwise *)
    Lemma lmexp_map2_vadd : forall gs hs xs, length gs = length hs ->
      lmexp (map (fun p => vadd (fst p) (snd p)) (combine gs hs)) xs = vadd (lmexp gs xs) (lmexp hs xs).
    Proof.
      induction gs as [| g gs ih]; intros hs xs hl.
      + destruct hs; [| discriminate]; rewrite !lmexp_nil_l, vid_l; reflexivity.
      + destruct hs as [| h hs]; [discriminate |].
        destruct xs as [| x xs]; [rewrite !lmexp_nil_r, vid_l; reflexivity |].
        cbn [combine map fst snd]; rewrite !lmexp_cons, ih; [| cbn in hl; lia].
        rewrite vadd_smul, vadd4; reflexivity.
    Qed.

    (* evaluation of a "polynomial" with coefficients in V: Σ_i cs_i x^i *)
    Definition veval (cs : list V) (x : F) : V := lmexp cs (lpows x (length cs)).

    Lemma veval_nil : forall x, veval [] x = vid.
    Proof. reflexivity. Qed.

    Lemma veval_cons : forall c cs x, veval (c :: cs) x = vadd c (smul (veval cs x) x).
    Proof.
      intros; unfold veval; cbn [length SigmaK.lpows]; rewrite lmexp_cons, smul_one, lmexp_scale; reflexivity.
    Qed.

    Lemma veval_shift : forall s cs x, veval (repeat vid s ++ cs) x = smul (veval cs x) (fpow x s).
    Proof.
      induction s as [| s ih]; intros cs x.
      + cbn [repeat app SigmaK.fpow]; rewrite smul_one; reflexivity.
      + cbn [repeat app SigmaK.fpow]; rewrite veval_cons, ih, vid_l, <-smul_mul.
        replace (fpow x s * x) with (x * fpow x s) by field; reflexivity.
    Qed.

    Lemma veval_map2 : forall u v x, length u = length v ->
      veval (map (fun p => vadd (fst p) (snd p)) (combine u v)) x = vadd (veval u x) (veval v x).
    Proof.
      intros u v x hl; unfold veval.
      rewrite map_length, combine_length, hl, Nat.min_id.
      apply lmexp_map2_vadd; exact hl.
    Qed.

    Lemma veval_scale_coeffs : forall (cs : list V) (c : F) x,
      veval (map (fun v => smul v c) cs) x = smul (veval cs x) c.
    Proof.
      intros cs c x; unfold veval; rewrite map_length; generalize (lpows x (length cs)); intro ps.
      revert ps; induction cs as [| v cs ih]; intros ps.
      + rewrite !lmexp_nil_l; symmetry; apply (smul_vid (HV := HV)).
      + destruct ps as [| p ps]; [rewrite !lmexp_nil_r; symmetry; apply (smul_vid (HV := HV)) |].
        cbn [map]; rewrite !lmexp_cons, ih, vadd_smul, <-!smul_mul.
        replace (c * p) with (p * c) by field; reflexivity.
    Qed.


    Local Notation vzero := (@vector_space_field_zero F (@eq F) zero one add mul sub div
      opp inv V (@eq V) vid vopp vadd smul HV).

    Lemma smul_zero : forall v : V, smul v zero = vid.
    Proof. intros; apply vzero. Qed.

    Lemma lmexp_repeat_zero : forall gs n, lmexp gs (repeat zero n) = vid.
    Proof.
      induction gs as [| g gs ih]; intros n; [apply lmexp_nil_l |].
      destruct n as [| n]; [apply lmexp_nil_r |].
      cbn [repeat]; rewrite lmexp_cons, ih, smul_zero, vid_l; reflexivity.
    Qed.

    Lemma lmexp_padd : forall gs xs ys, lmexp gs (padd xs ys) = vadd (lmexp gs xs) (lmexp gs ys).
    Proof.
      induction gs as [| g gs ih]; intros xs ys; [rewrite !lmexp_nil_l, vid_l; reflexivity |].
      destruct xs as [| x xs]; [cbn [SigmaK.padd]; rewrite lmexp_nil_r, vid_l; reflexivity |].
      destruct ys as [| y ys]; [rewrite padd_nil_r, lmexp_nil_r, vid_r; reflexivity |].
      cbn [SigmaK.padd]; rewrite !lmexp_cons, ih, smul_add, vadd4; reflexivity.
    Qed.

    (* zero-padded pointwise sum of coefficient lists *)
    Fixpoint vpadd (xs ys : list V) : list V :=
      match xs, ys with
      | [], _ => ys
      | _, [] => xs
      | x :: xs', y :: ys' => vadd x y :: vpadd xs' ys'
      end.

    Lemma vpadd_length : forall xs ys, length (vpadd xs ys) = Nat.max (length xs) (length ys).
    Proof.
      induction xs as [| a xs ih]; intros ys; [reflexivity |].
      destruct ys as [| b ys]; [reflexivity | cbn; rewrite ih; reflexivity].
    Qed.

    Lemma veval_vpadd : forall xs ys x, veval (vpadd xs ys) x = vadd (veval xs x) (veval ys x).
    Proof.
      induction xs as [| a xs ih]; intros ys x; [cbn [vpadd]; rewrite veval_nil, vid_l; reflexivity |].
      destruct ys as [| b ys]; [cbn [vpadd]; rewrite veval_nil, vid_r; reflexivity |].
      cbn [vpadd]; rewrite !veval_cons, ih, vadd_smul, vadd4; reflexivity.
    Qed.

    Lemma veval_cons_vid : forall cs x, veval (vid :: cs) x = smul (veval cs x) x.
    Proof. intros; rewrite veval_cons, vid_l; reflexivity. Qed.

    (* Σ x^i f(u_i) for f linear *)
    Lemma veval_map_linear : forall {A : Type} (f : A -> V) (fz : A) (fadd : A -> A -> A)
      (fscale : F -> A -> A),
      f fz = vid -> (forall u v, f (fadd u v) = vadd (f u) (f v)) ->
      (forall c u, f (fscale c u) = smul (f u) c) ->
      forall (us : list A) (x : F),
      veval (map f us) x = f (fold_right (fun u acc => fadd u (fscale x acc)) fz us).
    Proof.
      intros A f fz fadd fscale hz hadd hscale us x; induction us as [| u us ih].
      + cbn [map fold_right]; rewrite veval_nil, hz; reflexivity.
      + cbn [map fold_right]; rewrite veval_cons, ih, hadd, hscale; reflexivity.
    Qed.

    (* the polynomial product with a bilinear coefficient map:
      (pmul f u v)_k = Σ_{i+j=k} f u_i v_j *)
    Fixpoint pmul {A B : Type} (f : A -> B -> V) (u : list A) (v : list B) : list V :=
      match u with
      | [] => []
      | u0 :: u' => vpadd (map (f u0) v) (vid :: pmul f u' v)
      end.

    Lemma pmul_length : forall {A B : Type} (f : A -> B -> V) (u : list A) (v : list B),
      u <> [] -> v <> [] -> length (pmul f u v) = (length u + length v - 1)%nat.
    Proof.
      intros A B f u v hu hv; induction u as [| u0 u ih]; [contradiction |].
      cbn [pmul]; rewrite vpadd_length, map_length; cbn [length].
      destruct u as [| u1 u].
      + cbn; destruct v; [contradiction | cbn; lia].
      + rewrite ih by discriminate; cbn [length]; destruct v; [contradiction | cbn; lia].
    Qed.

    (* Σ_k x^k (pmul f u v)_k = f (Σ x^i u_i) (Σ x^j v_j) for f bilinear with
      respect to the given Horner operations *)
    Lemma veval_pmul : forall {A B : Type} (f : A -> B -> V)
      (az : A) (aadd : A -> A -> A) (ascale : F -> A -> A)
      (bz : B) (badd : B -> B -> B) (bscale : F -> B -> B),
      (forall b, f az b = vid) -> (forall u u' b, f (aadd u u') b = vadd (f u b) (f u' b)) ->
      (forall c u b, f (ascale c u) b = smul (f u b) c) ->
      (forall a, f a bz = vid) -> (forall a v v', f a (badd v v') = vadd (f a v) (f a v')) ->
      (forall c a v, f a (bscale c v) = smul (f a v) c) ->
      forall (u : list A) (v : list B) (x : F),
      veval (pmul f u v) x =
      f (fold_right (fun a acc => aadd a (ascale x acc)) az u)
        (fold_right (fun b acc => badd b (bscale x acc)) bz v).
    Proof.
      intros * haz hadd hscale hbz hbadd hbscale u v x; induction u as [| u0 u ih].
      + cbn [pmul fold_right]; rewrite veval_nil, haz; reflexivity.
      + cbn [pmul fold_right]; rewrite veval_vpadd, veval_cons_vid, ih.
        rewrite (veval_map_linear (f u0) bz badd bscale); [| intros; apply hbz | intros; apply hbadd | intros; apply hbscale].
        rewrite hadd, hscale; reflexivity.
    Qed.

    (* the coefficients of a product, as a recursion: Σ_{i ≤ k} f u_i v_{k−i}
      with out-of-range entries read as the defaults *)
    Fixpoint conv_coeff {A B : Type} (f : A -> B -> V) (dB : B) (u : list A) (v : list B) (k : nat) : V :=
      match u with
      | [] => vid
      | u0 :: u' => vadd (f u0 (nth k v dB)) (match k with 0 => vid | S k' => conv_coeff f dB u' v k' end)
      end.

    Lemma nth_vpadd : forall xs ys k, nth k (vpadd xs ys) vid = vadd (nth k xs vid) (nth k ys vid).
    Proof.
      induction xs as [| a xs ih]; intros ys k.
      + cbn [vpadd]; destruct k; cbn [nth]; rewrite vid_l; reflexivity.
      + destruct ys as [| b ys]; [destruct k; cbn [vpadd nth]; rewrite vid_r; reflexivity |].
        destruct k as [| k]; [reflexivity | cbn [vpadd nth]; apply ih].
    Qed.

    Lemma nth_pmul : forall {A B : Type} (f : A -> B -> V) (dB : B),
      (forall a, f a dB = vid) ->
      forall (u : list A) (v : list B) (k : nat),
      nth k (pmul f u v) vid = conv_coeff f dB u v k.
    Proof.
      intros A B f dB hB u; induction u as [| u0 u ih]; intros v k.
      + cbn [pmul conv_coeff]; destruct k; reflexivity.
      + cbn [pmul conv_coeff]; rewrite nth_vpadd.
        assert (hm : nth k (map (f u0) v) vid = f u0 (nth k v dB)).
        { destruct (Nat.lt_ge_cases k (length v)) as [hk | hk].
          - rewrite (nth_indep _ vid (f u0 dB)) by (rewrite map_length; exact hk); apply map_nth.
          - rewrite !nth_overflow by (try rewrite map_length; exact hk); rewrite hB; reflexivity. }
        rewrite hm; destruct k as [| k]; [reflexivity | cbn [nth]; rewrite ih; reflexivity].
    Qed.

    (* only the first k + 1 entries of v matter *)
    Lemma conv_coeff_app : forall {A B : Type} (f : A -> B -> V) (dB : B) (u : list A) (v w : list B) (k : nat),
      (k < length v)%nat -> conv_coeff f dB u (v ++ w) k = conv_coeff f dB u v k.
    Proof.
      intros A B f dB u; induction u as [| u0 u ih]; intros v w k hk; [reflexivity |].
      cbn [conv_coeff]; rewrite app_nth1 by exact hk.
      destruct k as [| k]; [reflexivity | rewrite ih by lia; reflexivity].
    Qed.


    (* the fold of a permuted list *)
    Lemma fold_vadd_perm : forall (l1 l2 : list V), Permutation l1 l2 ->
      fold_right vadd vid l1 = fold_right vadd vid l2.
    Proof.
      intros l1 l2 hp; induction hp as [| a l1 l2 hp ih | a b l | l1 l2 l3 hp1 ih1 hp2 ih2].
      + reflexivity.
      + cbn [fold_right]; rewrite ih; reflexivity.
      + cbn [fold_right]; rewrite !vassoc, (vcomm b a); reflexivity.
      + rewrite ih1; exact ih2.
    Qed.

    Lemma lmexp_as_fold : forall gs xs,
      lmexp gs xs = fold_right vadd vid (map (fun p => smul (fst p) (snd p)) (combine gs xs)).
    Proof.
      intros gs xs; unfold lmexp; generalize (combine gs xs); intro l.
      induction l as [| p l ih]; [reflexivity | cbn [fold_right map]; rewrite ih; reflexivity].
    Qed.

    Lemma fold_map_vadd : forall {A : Type} (f g : A -> V) (L : list A),
      fold_right vadd vid (map (fun a => vadd (f a) (g a)) L) =
      vadd (fold_right vadd vid (map f L)) (fold_right vadd vid (map g L)).
    Proof.
      intros A f g L; induction L as [| a L ih]; [cbn; rewrite vid_l; reflexivity |].
      cbn [map fold_right]; rewrite ih, vadd4; reflexivity.
    Qed.


    Lemma vadd_assoc : forall a b c : V, vadd a (vadd b c) = vadd (vadd a b) c.
    Proof. intros; apply vassoc. Qed.
    Lemma vadd_vid_l : forall a : V, vadd vid a = a.
    Proof. intros; apply vid_l. Qed.

  End LMexp.

  (* the instances used below: group elements, and scalars *)
  Local Notation gmexp := (lmexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation geval := (veval (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation fmexp := (lmexp (vid := zero) (vadd := add) (smul := mul)).
  Local Notation feval := (veval (vid := zero) (vadd := add) (smul := mul)).

  (* scalar evaluation is the Horner evaluation of Crypto/PolyRoots.v *)
  Lemma feval_eval : forall (cs : list F) (x : F), feval cs x = eval (add := add) (mul := mul) (zero := zero) cs x.
  Proof.
    induction cs as [| c cs ih]; intros x; [reflexivity |].
    rewrite (veval_cons (HV := F_vspace)); cbn [eval]; rewrite ih; field.
  Qed.

  Lemma fpow_add : forall x a b, fpow x (a + b)%nat = fpow x a * fpow x b.
  Proof. induction a as [| a ih]; intros b; cbn [SigmaK.fpow Nat.add]; [field | rewrite ih; field]. Qed.

  (* ---------------------------------------------------------------- *)
  (* Pedersen commitments (Algorithm 9.7)                              *)
  (* ---------------------------------------------------------------- *)

  (* com(a; r) = h^r ∏ g_i^{a_i}, over the first length(a) generators *)
  Definition com (h : G) (gs : list G) (a : list F) (r : F) : G := gop (h ^ r) (gmexp gs a).

  Lemma com_add : forall h gs a b r s, length a = length b ->
    com h gs (ladd a b) (r + s) = gop (com h gs a r) (com h gs b s).
  Proof.
    intros * hl; unfold com; rewrite gpow_add, (lmexp_add (HV := Hvec)); [| exact hl].
    rewrite gop4; reflexivity.
  Qed.

  Lemma com_scale : forall h gs a r c, com h gs (lscale c a) (c * r) = (com h gs a r) ^ c.
  Proof.
    intros; unfold com; rewrite (lmexp_scale (HV := Hvec)), gop_pow, <-gpow_mul.
    replace (r * c) with (c * r) by field; reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* List helpers                                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma nth_map_seq : forall {A : Type} (f : nat -> A) (d : A) (n i : nat),
    (i < n)%nat -> nth i (map f (seq 0 n)) d = f i.
  Proof.
    intros A f d n i hi.
    rewrite (nth_indep _ d (f 0)) by (rewrite map_length, seq_length; exact hi).
    rewrite map_nth, seq_nth by exact hi; reflexivity.
  Qed.

  Lemma ladd_map : forall {A : Type} (f g : A -> F) (l : list A),
    ladd (map f l) (map g l) = map (fun i => f i + g i) l.
  Proof. intros A f g l; induction l as [| a l ih]; [reflexivity | cbn; rewrite <-ih; reflexivity]. Qed.

  Lemma lscale_map : forall {A : Type} (c : F) (f : A -> F) (l : list A),
    lscale c (map f l) = map (fun i => c * f i) l.
  Proof. intros; unfold SigmaK.lscale; rewrite map_map; reflexivity. Qed.

  Lemma ladd_length : forall xs ys, length xs = length ys -> length (ladd xs ys) = length xs.
  Proof. intros; unfold SigmaK.ladd; rewrite map_length, combine_length; lia. Qed.

  Lemma nth_lscale : forall c xs i, (i < length xs)%nat -> nth i (lscale c xs) zero = c * nth i xs zero.
  Proof.
    intros c xs; induction xs as [| x xs ih]; intros i hi; [cbn in hi; lia |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.lscale map nth]; apply ih; cbn in hi; lia].
  Qed.

  Lemma nth_ladd : forall xs ys i, length xs = length ys -> (i < length xs)%nat ->
    nth i (ladd xs ys) zero = nth i xs zero + nth i ys zero.
  Proof.
    induction xs as [| x xs ih]; intros ys i hl hi; [cbn in hi; lia |].
    destruct ys as [| y ys]; [discriminate |].
    destruct i as [| i]; [reflexivity | cbn [SigmaK.ladd combine map nth fst snd]; apply ih; cbn in *; lia].
  Qed.

  (* closes a goal (if dec a b then true else false) = true by proving a = b *)
  Local Ltac dec_true := match goal with
    | |- (if ?d then true else false) = true => destruct d as [_ | hne]; [reflexivity | exfalso; apply hne]
    end.

  (* ---------------------------------------------------------------- *)
  (* Single value product argument (Algorithms 9.25, 9.26)             *)
  (* ---------------------------------------------------------------- *)

  Section SingleValueProduct.

    (* the argument (c_d, c_δ, c_Δ, ã, b̃, r̃, s̃) *)
    Record svp_argument : Type := mk_svp {
      svp_cd : G; svp_cdelta : G; svp_cDelta : G;
      svp_a : list F; svp_b : list F; svp_r : F; svp_s : F }.

    (* Algorithm 9.26, statement (c_a, b), challenge x *)
    Definition svp_verify (h : G) (gs : list G) (ca : G) (b : F) (x : F) (arg : svp_argument) : bool :=
      let n := length (svp_a arg) in
      let at_ := svp_a arg in let bt := svp_b arg in
      (2 <=? n) && (length bt =? n) &&
      (if Gdec (gop (ca ^ x) (svp_cd arg)) (com h gs at_ (svp_r arg)) then true else false) &&
      (let e := map (fun i => x * nth (S i) bt zero - nth i bt zero * nth (S i) at_ zero) (seq 0 (n - 1)) in
       if Gdec (gop ((svp_cDelta arg) ^ x) (svp_cdelta arg)) (com h gs e (svp_s arg)) then true else false) &&
      (if Fdec (nth 0 bt zero) (nth 0 at_ zero) then true else false) &&
      (if Fdec (nth (n - 1) bt zero) (x * b) then true else false) &&
      (length at_ =? length gs).

    (* the prefix products b_k = ∏_{i ≤ k} a_i *)
    Definition prefix_prod (a : list F) (k : nat) : F := fold_right mul one (firstn (S k) a).

    (* Algorithm 9.25 with its randomness as parameters: d (length n), r_d,
      δ_1..δ_{n−2} (dmid), s_0, s_x *)
    Definition svp_prove (h : G) (gs : list G) (a : list F) (r : F)
      (d : list F) (rd : F) (dmid : list F) (s0 sx : F) (x : F) : svp_argument :=
      let n := length a in
      let bf := prefix_prod a in
      let af := fun i => nth i a zero in
      let df := fun i => nth i d zero in
      let delta := fun i => nth i (df 0 :: dmid ++ [zero]) zero in
      let delta' := map (fun k => opp (delta k * df (S k))) (seq 0 (n - 1)) in
      let Delta := map (fun k => delta (S k) - af (S k) * delta k - bf k * df (S k)) (seq 0 (n - 1)) in
      mk_svp (com h gs d rd) (com h gs delta' s0) (com h gs Delta sx)
        (map (fun k => x * af k + df k) (seq 0 n))
        (map (fun k => x * bf k + delta k) (seq 0 n))
        (x * r + rd) (x * sx + s0).

    Lemma firstn_S_nth : forall (l : list F) (k : nat), (k < length l)%nat ->
      firstn (S k) l = firstn k l ++ [nth k l zero].
    Proof.
      induction l as [| a l ih]; intros k hk; [cbn in hk; lia |].
      destruct k as [| k]; [reflexivity |].
      change (a :: firstn (S k) l = a :: (firstn k l ++ [nth k l zero])).
      rewrite ih; [reflexivity | cbn in hk; lia].
    Qed.

    Lemma fold_right_mul_init : forall (l : list F) (c : F), fold_right mul c l = fold_right mul one l * c.
    Proof. induction l as [| a l ih]; intros c; cbn [fold_right]; [field | rewrite ih; field]. Qed.

    Lemma prefix_prod_S : forall a k, (S k < length a)%nat ->
      prefix_prod a (S k) = prefix_prod a k * nth (S k) a zero.
    Proof.
      intros a k hk; unfold prefix_prod.
      rewrite (firstn_S_nth a (S k) hk), fold_right_app; cbn [fold_right].
      rewrite fold_right_mul_init; field.
    Qed.

    Lemma prefix_prod_last : forall a, a <> [] ->
      prefix_prod a (length a - 1) = fold_right mul one a.
    Proof.
      intros a ha; unfold prefix_prod.
      replace (S (length a - 1)) with (length a) by (destruct a; [contradiction | cbn; lia]).
      rewrite firstn_all; reflexivity.
    Qed.

    (* nth of the honest responses *)
    Lemma nth_resp : forall (f g : nat -> F) x n i, (i < n)%nat ->
      nth i (map (fun k => x * f k + g k) (seq 0 n)) zero = x * f i + g i.
    Proof. intros f g x n i hi; exact (nth_map_seq (fun k => x * f k + g k) zero n i hi). Qed.

    Theorem svp_completeness : forall (h : G) (gs : list G) (a : list F) (r : F)
      (d : list F) (rd : F) (dmid : list F) (s0 sx x : F),
      (2 <= length a)%nat -> length d = length a -> length dmid = (length a - 2)%nat -> length a = length gs ->
      svp_verify h gs (com h gs a r) (fold_right mul one a) x (svp_prove h gs a r d rd dmid s0 sx x) = true.
    Proof.
      intros * hn hd hmid hga; unfold svp_verify, svp_prove;
      cbn [svp_a svp_b svp_cd svp_cdelta svp_cDelta svp_r svp_s]; cbv zeta.
      rewrite !map_length, !seq_length.
      apply andb_true_iff; split; [| apply Nat.eqb_eq; exact hga].
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split; [apply andb_true_iff; split |] |] |] |].
      + apply Nat.leb_le; exact hn.
      + apply Nat.eqb_eq; reflexivity.
      + (* c_a^x c_d = com(ã; r̃) *)
        dec_true.
        rewrite <-com_scale, <-com_add; [| unfold SigmaK.lscale; rewrite map_length; exact (eq_sym hd)].
        f_equal. apply (nth_ext _ _ zero zero).
        - rewrite ladd_length by (unfold SigmaK.lscale; rewrite map_length; exact (eq_sym hd)).
          unfold SigmaK.lscale; rewrite !map_length, seq_length; reflexivity.
        - intros i hi.
          rewrite ladd_length in hi by (unfold SigmaK.lscale; rewrite map_length; exact (eq_sym hd)).
          unfold SigmaK.lscale in hi; rewrite map_length in hi.
          rewrite nth_map_seq by exact hi.
          rewrite nth_ladd by (unfold SigmaK.lscale; rewrite map_length; lia).
          rewrite nth_lscale by exact hi; reflexivity.
      + (* c_Δ^x c_δ = com(e; s̃) *)
        dec_true.
        rewrite <-com_scale, <-com_add; [| unfold SigmaK.lscale; rewrite !map_length, !seq_length; reflexivity].
        f_equal; unfold SigmaK.lscale; rewrite map_map, ladd_map.
        apply map_ext_in; intros k hk; apply in_seq in hk; destruct hk as (_ & hk).
        repeat (rewrite nth_map_seq by lia).
        rewrite (prefix_prod_S a k) by lia; field.
      + (* b̃_0 = ã_0 *)
        dec_true.
        repeat (rewrite nth_map_seq by lia).
        unfold prefix_prod; destruct a as [| a0 a']; [cbn in hn; lia |]; cbn [firstn fold_right nth]; field.
      + (* b̃_{n−1} = x·b *)
        dec_true.
        repeat (rewrite nth_map_seq by lia).
        rewrite prefix_prod_last by (destruct a; [cbn in hn; lia | discriminate]).
        rewrite app_comm_cons.
        replace (length a - 1)%nat with (length (nth 0 d zero :: dmid)) by (cbn; lia).
        rewrite nth_middle; field.
    Qed.

  End SingleValueProduct.

  (* ---------------------------------------------------------------- *)
  (* Scalar polynomials, the bilinear map ⋆, Horner sums of vectors    *)
  (* ---------------------------------------------------------------- *)

  Local Notation fpmul := (pmul (vid := zero) (vadd := add)).
  Local Notation fconv := (conv_coeff (vid := zero) (vadd := add)).

  Lemma feval_cons : forall c cs x, feval (c :: cs) x = c + x * feval cs x.
  Proof. intros; rewrite (veval_cons (HV := F_vspace)); field. Qed.
  Lemma feval_nil : forall x, feval [] x = zero.
  Proof. reflexivity. Qed.

  (* the F-instance of vpadd is padd *)
  Lemma vpadd_padd : forall xs ys, vpadd (vadd := add) xs ys = padd xs ys.
  Proof.
    induction xs as [| a xs ih]; intros ys; [reflexivity |].
    destruct ys as [| b ys]; [reflexivity | cbn [vpadd SigmaK.padd]; rewrite ih; reflexivity].
  Qed.

  (* a ⋆ b = Σ_j a_j b_j y^{j+1} (Algorithm 9.10), with the running weight w *)
  Fixpoint star_w (w y : F) (a b : list F) : F :=
    match a, b with
    | a0 :: a', b0 :: b' => a0 * b0 * w + star_w (w * y) y a' b'
    | _, _ => zero
    end.
  Definition star (y : F) (a b : list F) : F := star_w y y a b.

  Lemma star_w_nil_r : forall w y a, star_w w y a [] = zero.
  Proof. intros w y a; destruct a; reflexivity. Qed.
  Lemma star_nil_r : forall y a, star y a [] = zero.
  Proof. intros; apply star_w_nil_r. Qed.

  Lemma star_w_padd_l : forall w y a a' b, star_w w y (padd a a') b = star_w w y a b + star_w w y a' b.
  Proof.
    intros w y a; revert w; induction a as [| a0 a ih]; intros w a' b; [cbn [SigmaK.padd star_w]; field |].
    destruct a' as [| a0' a']; [rewrite padd_nil_r; cbn [star_w]; destruct b; field |].
    destruct b as [| b0 b]; [rewrite !star_w_nil_r; field |].
    cbn [SigmaK.padd star_w]; rewrite ih; field.
  Qed.

  Lemma star_w_lscale_l : forall w y c a b, star_w w y (lscale c a) b = c * star_w w y a b.
  Proof.
    intros w y c a; revert w; induction a as [| a0 a ih]; intros w b; [cbn; field |].
    destruct b as [| b0 b]; [rewrite !star_w_nil_r; field |].
    unfold SigmaK.lscale; cbn [map star_w]; fold (lscale c a); rewrite ih; field.
  Qed.

  Lemma star_w_padd_r : forall w y a b b', star_w w y a (padd b b') = star_w w y a b + star_w w y a b'.
  Proof.
    intros w y a; revert w; induction a as [| a0 a ih]; intros w b b'; [cbn; field |].
    destruct b as [| b0 b]; [cbn [SigmaK.padd star_w]; field |].
    destruct b' as [| b0' b']; [rewrite padd_nil_r; cbn [star_w]; field |].
    cbn [SigmaK.padd star_w]; rewrite ih; field.
  Qed.

  Lemma star_w_lscale_r : forall w y c a b, star_w w y a (lscale c b) = c * star_w w y a b.
  Proof.
    intros w y c a; revert w; induction a as [| a0 a ih]; intros w b; [cbn; field |].
    destruct b as [| b0 b]; [cbn; field |].
    unfold SigmaK.lscale; cbn [map star_w]; fold (lscale c b); rewrite ih; field.
  Qed.

  (* Σ_i x^i A_i for a list of vectors (Horner, zero-padded) *)
  Definition lveval (As : list (list F)) (x : F) : list F :=
    fold_right (fun a acc => padd a (lscale x acc)) [] As.

  Lemma lveval_cons : forall a As x, lveval (a :: As) x = padd a (lscale x (lveval As x)).
  Proof. reflexivity. Qed.

  Lemma lveval_length : forall (As : list (list F)) x n, As <> [] -> (forall v, In v As -> length v = n) ->
    length (lveval As x) = n.
  Proof.
    intros As x n hne hlen; induction As as [| a As ih]; [contradiction |].
    rewrite lveval_cons, SigmaK.padd_length; unfold SigmaK.lscale; rewrite length_map.
    rewrite (hlen a (or_introl eq_refl)). destruct As as [| a' As]; [cbn; lia |].
    rewrite ih by (discriminate || (intros v hv; apply hlen; right; exact hv)); lia.
  Qed.


  (* the Horner sum of singletons is the singleton of the scalar sum *)
  Lemma lveval_singletons : forall (d : list F) (x : F), d <> [] ->
    lveval (map (fun dk => [dk]) d) x = [feval d x].
  Proof.
    induction d as [| d0 d ih]; intros x hd; [contradiction |].
    destruct d as [| d1 d].
    + cbn [map lveval fold_right SigmaK.lscale SigmaK.padd]; rewrite feval_cons, feval_nil; f_equal; field.
    + cbn [map]; rewrite lveval_cons, ih by discriminate; cbn [SigmaK.lscale map SigmaK.padd].
      rewrite (feval_cons d0 (d1 :: d) x); reflexivity.
  Qed.

  (* Σ_k x^k (pmul ⋆ u v)_k = (Σ x^i u_i) ⋆ (Σ x^j v_j) *)
  Lemma feval_pmul_star : forall y (u v : list (list F)) x,
    feval (fpmul (star y) u v) x = star y (lveval u x) (lveval v x).
  Proof.
    intros y u v x; unfold lveval.
    apply (veval_pmul (HV := F_vspace) (star y) [] padd lscale [] padd lscale).
    + reflexivity.
    + intros; apply star_w_padd_l.
    + intros; unfold star; rewrite star_w_lscale_l; field.
    + intros; apply star_w_nil_r.
    + intros; apply star_w_padd_r.
    + intros; unfold star; rewrite star_w_lscale_r; field.
  Qed.

  (* ---- commitments of Horner sums ---- *)

  Lemma com_padd : forall h gs a b r s, com h gs (padd a b) (r + s) = gop (com h gs a r) (com h gs b s).
  Proof. intros; unfold com; rewrite gpow_add, (lmexp_padd (HV := Hvec)), gop4; reflexivity. Qed.

  Definition com_list (h : G) (gs : list G) (As : list (list F)) (rs : list F) : list G :=
    map (fun p => com h gs (fst p) (snd p)) (combine As rs).

  Lemma com_list_cons : forall h gs a As r rs, com_list h gs (a :: As) (r :: rs) = com h gs a r :: com_list h gs As rs.
  Proof. reflexivity. Qed.

  Lemma com_list_length : forall h gs As rs, length (com_list h gs As rs) = Nat.min (length As) (length rs).
  Proof. intros; unfold com_list; rewrite map_length, combine_length; reflexivity. Qed.

  (* ∏_i com(A_i; r_i)^{x^i} = com(Σ x^i A_i; Σ x^i r_i) *)
  Lemma geval_com_list : forall h gs As rs x, length As = length rs ->
    geval (com_list h gs As rs) x = com h gs (lveval As x) (feval rs x).
  Proof.
    intros h gs As; induction As as [| a As ih]; intros rs x hl.
    + destruct rs; [| discriminate]; cbn [com_list combine map lveval fold_right].
      rewrite veval_nil, feval_nil; unfold com; rewrite gpow_zero, gid_l, lmexp_nil_r; reflexivity.
    + destruct rs as [| r rs]; [discriminate |].
      rewrite com_list_cons, (veval_cons (HV := Hvec)), ih by (cbn in hl; lia).
      rewrite lveval_cons, feval_cons, <-com_scale, <-com_padd.
      replace (x * feval rs x) with (feval rs x * x) by field; reflexivity.
  Qed.

  Lemma combine_app_eq : forall {A B : Type} (l1 l1' : list A) (l2 l2' : list B), length l1 = length l2 ->
    combine (l1 ++ l1') (l2 ++ l2') = combine l1 l2 ++ combine l1' l2'.
  Proof.
    induction l1 as [| a l1 ih]; intros l1' l2 l2' hl; destruct l2 as [| b l2]; try discriminate; [reflexivity |].
    cbn [app combine]; rewrite ih by (cbn in hl; lia); reflexivity.
  Qed.

  Lemma combine_rev : forall {A B : Type} (l1 : list A) (l2 : list B), length l1 = length l2 ->
    rev (combine l1 l2) = combine (rev l1) (rev l2).
  Proof.
    induction l1 as [| a l1 ih]; intros l2 hl; destruct l2 as [| b l2]; try discriminate; [reflexivity |].
    cbn [combine rev]; rewrite ih by (cbn in hl; lia).
    rewrite combine_app_eq by (rewrite !rev_length; cbn in hl; lia); reflexivity.
  Qed.

  Lemma com_list_rev : forall h gs As rs, length As = length rs ->
    rev (com_list h gs As rs) = com_list h gs (rev As) (rev rs).
  Proof. intros; unfold com_list; rewrite <-map_rev, combine_rev by assumption; reflexivity. Qed.

  Lemma nth_com_list : forall h gs As rs k, length As = length rs -> (k < length As)%nat ->
    nth k (com_list h gs As rs) gid = com h gs (nth k As []) (nth k rs zero).
  Proof.
    intros * hl hk; unfold com_list.
    rewrite (nth_indep _ gid (com h gs (fst (@nil F, zero)) (snd (@nil F, zero))))
      by (rewrite map_length, combine_length; lia).
    rewrite (map_nth (fun p => com h gs (fst p) (snd p)) (combine As rs) (@nil F, zero) k).
    rewrite (combine_nth As rs k [] zero hl); reflexivity.
  Qed.

  Lemma com_zero_single : forall h gs, com h gs [zero] zero = gid.
  Proof.
    intros; unfold com; rewrite gpow_zero, gid_l.
    change [zero] with (repeat zero 1); apply (lmexp_repeat_zero (HV := Hvec)).
  Qed.

  (* the middle coefficient of the zero argument's d: Σ_i a_i ⋆ b_{i−1} *)
  Lemma conv_middle : forall y (A B : list (list F)) (bm : list F), length A = length B ->
    fconv (star y) [] A (bm :: rev B) (length B) =
    fold_right add zero (map (fun p => star y (fst p) (snd p)) (combine A B)).
  Proof.
    intros y A; induction A as [| a1 A ih]; intros B bm hl; [reflexivity |].
    destruct B as [| b0 B]; [discriminate |].
    cbn [conv_coeff combine map fold_right fst snd length rev].
    rewrite app_comm_cons, app_nth2 by (cbn; rewrite rev_length; lia).
    replace (S (length B) - length (bm :: rev B))%nat with 0%nat by (cbn; rewrite rev_length; lia).
    cbn [nth].
    rewrite conv_coeff_app by (cbn; rewrite rev_length; lia).
    rewrite ih by (cbn in hl; lia); reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Zero argument (Algorithms 9.22, 9.23)                             *)
  (* ---------------------------------------------------------------- *)

  Section ZeroArgument.

    Record zero_argument : Type := mk_zero {
      za_cA0 : G; za_cBm : G; za_cd : list G;
      za_a : list F; za_b : list F; za_r : F; za_s : F; za_t : F }.

    (* Algorithm 9.23; statement cA = (c_{A1}, …, c_{Am}), cB = (c_{B0}, …, c_{B(m−1)}), y *)
    Definition zero_verify (h : G) (gs : list G) (cA cB : list G) (y x : F) (arg : zero_argument) : bool :=
      let m := length cA in
      (1 <=? m) && (length cB =? m) && (length (za_cd arg) =? 2 * m + 1) &&
      (if Gdec (nth (S m) (za_cd arg) gid) gid then true else false) &&
      (if Gdec (geval (za_cA0 arg :: cA) x) (com h gs (za_a arg) (za_r arg)) then true else false) &&
      (if Gdec (geval (za_cBm arg :: rev cB) x) (com h gs (za_b arg) (za_s arg)) then true else false) &&
      (if Gdec (geval (za_cd arg) x) (com h gs [star y (za_a arg) (za_b arg)] (za_t arg)) then true else false) &&
      (length (za_a arg) =? length gs) && (length (za_b arg) =? length gs).

    (* Algorithm 9.22 with its randomness as parameters: a_0, b_m, r_0, s_m and
      t = t1 ++ 0 :: t2 (t_{m+1} = 0) *)
    Definition zero_prove (h : G) (gs : list G) (A B : list (list F)) (r s : list F) (y : F)
      (a0 bm : list F) (r0 sm : F) (t1 t2 : list F) (x : F) : zero_argument :=
      let As := a0 :: A in
      let Bs := bm :: rev B in
      let d := fpmul (star y) As Bs in
      let tz := t1 ++ zero :: t2 in
      mk_zero (com h gs a0 r0) (com h gs bm sm) (com_list h gs (map (fun dk => [dk]) d) tz)
        (lveval As x) (lveval Bs x) (feval (r0 :: r) x) (feval (sm :: rev s) x) (feval tz x).

    Theorem zero_completeness : forall (h : G) (gs : list G) (A B : list (list F)) (r s : list F) (y : F)
      (a0 bm : list F) (r0 sm : F) (t1 t2 : list F) (x : F),
      (1 <= length A)%nat -> length B = length A -> length r = length A -> length s = length A ->
      length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
      Forall (fun v => length v = length gs) (a0 :: A) -> Forall (fun v => length v = length gs) (bm :: B) ->
      fold_right add zero (map (fun p => star y (fst p) (snd p)) (combine A B)) = zero ->
      zero_verify h gs (com_list h gs A r) (com_list h gs B s) y x
        (zero_prove h gs A B r s y a0 bm r0 sm t1 t2 x) = true.
    Proof.
      intros * hm hB hr hs ht1 ht2 hAn hBn hzero; unfold zero_verify, zero_prove;
      cbn [za_cA0 za_cBm za_cd za_a za_b za_r za_s za_t]; cbv zeta.
      set (m := length A) in *.
      assert (hmA : length A = m) by reflexivity.
      assert (hd : length (fpmul (star y) (a0 :: A) (bm :: rev B)) = (2 * m + 1)%nat).
      { rewrite pmul_length by discriminate; cbn [length]; rewrite rev_length; lia. }
      assert (htz : length (t1 ++ zero :: t2) = (2 * m + 1)%nat) by (rewrite app_length; cbn; lia).
      rewrite !com_list_length, !map_length, hd, htz, hB, hr, hs, !Nat.min_id.
      rewrite Forall_forall in hAn, hBn.
      apply andb_true_iff; split; [apply andb_true_iff; split;
        [| apply Nat.eqb_eq; apply lveval_length; [discriminate | exact hAn]]
        | apply Nat.eqb_eq; apply lveval_length; [discriminate |];
          intros v [<- | hv]; [apply hBn; left; reflexivity | apply hBn; right; apply in_rev; exact hv]].
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split |] |] |] |] |].
      + apply Nat.leb_le; exact hm.
      + apply Nat.eqb_eq; reflexivity.
      + apply Nat.eqb_eq; reflexivity.
      + (* c_{d,m+1} = 1 *)
        dec_true.
        rewrite nth_com_list by (rewrite map_length; lia).
        rewrite (nth_indep (map (fun dk : F => [dk]) _) [] ((fun dk : F => [dk]) zero)) by (rewrite map_length; lia).
        rewrite (map_nth (fun dk : F => [dk])).
        rewrite (nth_pmul (HV := F_vspace) (star y) []) by (intros; apply star_w_nil_r).
        rewrite app_nth2 by lia; replace (S m - length t1)%nat with 0%nat by lia; cbn [nth].
        cbn [conv_coeff]; rewrite nth_overflow by (cbn; rewrite rev_length; lia).
        rewrite star_nil_r.
        replace m with (length B) by (unfold m; lia).
        rewrite conv_middle by lia; rewrite hzero, Fadd_id_l; apply com_zero_single.
      + (* prodCa *)
        dec_true; rewrite <-com_list_cons, geval_com_list by (cbn; lia); reflexivity.
      + (* prodCb *)
        dec_true; rewrite com_list_rev by lia; rewrite <-com_list_cons, geval_com_list
          by (cbn; rewrite !rev_length; lia); reflexivity.
      + (* prodCd *)
        dec_true; rewrite geval_com_list by (rewrite map_length; lia).
        rewrite lveval_singletons by (intro e; apply (f_equal (@length F)) in e; cbn in e; lia).
        rewrite feval_pmul_star; reflexivity.
    Qed.

  End ZeroArgument.

  (* ---------------------------------------------------------------- *)
  (* Hadamard argument (Algorithms 9.20, 9.21)                         *)
  (* ---------------------------------------------------------------- *)

  Section Hadamard.

    (* the entry-wise product and the prefix products b_j = a_0 ∘ ⋯ ∘ a_j *)
    Definition hmul (a b : list F) : list F := map (fun p => fst p * snd p) (combine a b).

    Definition hprefix (A : list (list F)) (j : nat) : list F :=
      match firstn (S j) A with
      | [] => []
      | a :: rest => fold_left hmul rest a
      end.

    Lemma hmul_length : forall a b, length (hmul a b) = Nat.min (length a) (length b).
    Proof. intros; unfold hmul; rewrite map_length, combine_length; reflexivity. Qed.

    Lemma hmul_ones : forall n a, length a = n -> hmul (repeat one n) a = a.
    Proof.
      induction n as [| n ih]; intros a hl; destruct a as [| a0 a]; try discriminate; [reflexivity |].
      unfold hmul; cbn [repeat combine map fst snd]; fold (hmul (repeat one n) a).
      rewrite ih by (cbn in hl; lia); f_equal; field.
    Qed.

    Lemma star_w_hmul : forall w y a b c, star_w w y a (hmul b c) = star_w w y (hmul a b) c.
    Proof.
      intros w y a; revert w; induction a as [| a0 a ih]; intros w b c; [destruct b, c; reflexivity |].
      destruct b as [| b0 b]; [rewrite star_w_nil_r; reflexivity |].
      destruct c as [| c0 c]; [cbn; reflexivity |].
      unfold hmul; cbn [combine map fst snd star_w]; fold (hmul b c) (hmul a b); rewrite ih; f_equal; field.
    Qed.

    Lemma star_w_comm : forall w y a b, star_w w y a b = star_w w y b a.
    Proof.
      intros w y a; revert w; induction a as [| a0 a ih]; intros w b; [destruct b; reflexivity |].
      destruct b as [| b0 b]; [reflexivity | cbn [star_w]; rewrite ih; f_equal; field].
    Qed.

    Lemma star_lscale_l : forall y c a b, star y (lscale c a) b = c * star y a b.
    Proof. intros; apply star_w_lscale_l. Qed.
    Lemma star_lscale_r : forall y c a b, star y a (lscale c b) = c * star y a b.
    Proof. intros; apply star_w_lscale_r. Qed.

    Lemma firstn_S_nth_gen : forall {X : Type} (d : X) (l : list X) (k : nat), (k < length l)%nat ->
      firstn (S k) l = firstn k l ++ [nth k l d].
    Proof.
      intros X d; induction l as [| a l ih]; intros k hk; [cbn in hk; lia |].
      destruct k as [| k]; [reflexivity |].
      change (a :: firstn (S k) l = a :: (firstn k l ++ [nth k l d])).
      rewrite ih; [reflexivity | cbn in hk; lia].
    Qed.

    Lemma hprefix_0 : forall A, A <> [] -> hprefix A 0 = nth 0 A [].
    Proof. intros A hA; destruct A; [contradiction | reflexivity]. Qed.

    Lemma hprefix_S : forall A j, (S j < length A)%nat ->
      hprefix A (S j) = hmul (hprefix A j) (nth (S j) A []).
    Proof.
      intros A j hj; unfold hprefix.
      rewrite (firstn_S_nth_gen [] A (S j) hj).
      destruct (firstn (S j) A) as [| a0 rest] eqn:hf.
      + exfalso; pose proof (firstn_length (S j) A) as hl; rewrite hf in hl; cbn [length] in hl; lia.
      + cbn [app]; rewrite fold_left_app; reflexivity.
    Qed.

    Lemma hprefix_length : forall n A j, Forall (fun a => length a = n) A -> (j < length A)%nat ->
      length (hprefix A j) = n.
    Proof.
      intros n A j hA; revert j; induction j as [| j ih]; intros hj.
      + rewrite hprefix_0 by (destruct A; [cbn in hj; lia | discriminate]).
        rewrite Forall_forall in hA; apply hA; apply nth_In; exact hj.
      + rewrite hprefix_S by exact hj; rewrite hmul_length, ih by lia.
        rewrite Forall_forall in hA; rewrite (hA (nth (S j) A [])) by (apply nth_In; exact hj); apply Nat.min_id.
    Qed.

    (* a_{j+1} ⋆ b_j = 1 ⋆ b_{j+1} for the prefix products *)
    Lemma star_ones_hprefix : forall n y A j, Forall (fun a => length a = n) A -> (S j < length A)%nat ->
      star y (nth (S j) A []) (hprefix A j) = star y (repeat one n) (hprefix A (S j)).
    Proof.
      intros n y A j hA hj; rewrite hprefix_S by exact hj; unfold star.
      rewrite star_w_hmul, hmul_ones by (apply hprefix_length with (n := n); [exact hA | lia]).
      apply star_w_comm.
    Qed.

    Lemma neg_ones : forall n, repeat (opp one) n = lscale (opp one) (repeat one n).
    Proof. induction n as [| n ih]; [reflexivity | cbn [repeat]; unfold SigmaK.lscale; cbn [map]; fold (lscale (opp one) (repeat one n)); rewrite <-ih; f_equal; field]. Qed.

    (* ⋆ with a fixed left argument is linear in the Horner sum *)
    Lemma star_lveval_r : forall y a Bs x, feval (map (star y a) Bs) x = star y a (lveval Bs x).
    Proof.
      intros; unfold lveval.
      apply (veval_map_linear (HV := F_vspace) (star y a) [] padd lscale).
      + apply star_nil_r.
      + intros; apply star_w_padd_r.
      + intros; unfold star; rewrite star_w_lscale_r; field.
    Qed.

    Lemma sum_pow_feval_w : forall (g : nat -> F) (x w : F) (k : nat),
      fold_right add zero (map (fun i => w * fpow x i * g i) (seq 0 k)) = w * feval (map g (seq 0 k)) x.
    Proof.
      intros g x w k; revert g w; induction k as [| k ih]; intros g w; [cbn; field |].
      cbn [seq map fold_right]; rewrite feval_cons, <-seq_shift, !map_map.
      rewrite (map_ext (fun i => w * fpow x (S i) * g (S i)) (fun i => (w * x) * fpow x i * g (S i)))
        by (intro i; cbn [SigmaK.fpow]; field).
      rewrite (ih (fun i => g (S i)) (w * x)); cbn [SigmaK.fpow]; field.
    Qed.

    (* Σ_{i<k} x^{i+1} g_i = x · Σ_{i<k} x^i g_i *)
    Lemma sum_pow_feval : forall (g : nat -> F) (x : F) (k : nat),
      fold_right add zero (map (fun i => fpow x (S i) * g i) (seq 0 k)) = x * feval (map g (seq 0 k)) x.
    Proof.
      intros g x k.
      rewrite (map_ext (fun i => fpow x (S i) * g i) (fun i => x * fpow x i * g i))
        by (intro i; cbn [SigmaK.fpow]; field).
      apply sum_pow_feval_w.
    Qed.

    Lemma com_list_app : forall h gs As As' rs rs', length As = length rs ->
      com_list h gs (As ++ As') (rs ++ rs') = com_list h gs As rs ++ com_list h gs As' rs'.
    Proof. intros; unfold com_list; rewrite combine_app_eq by assumption; apply map_app. Qed.

    Lemma com_list_tl : forall h gs As rs, tl (com_list h gs As rs) = com_list h gs (tl As) (tl rs).
    Proof.
      intros h gs As rs; destruct As as [| a As], rs as [| r rs]; try reflexivity.
      unfold com_list; destruct As; reflexivity.
    Qed.

    Lemma nth_tl : forall {X : Type} (l : list X) (i : nat) (d : X), l <> [] -> nth i (tl l) d = nth (S i) l d.
    Proof. intros X l i d hl; destruct l; [contradiction | reflexivity]. Qed.

    Lemma in_tl : forall {X : Type} (l : list X) (v : X), In v (tl l) -> In v l.
    Proof. intros X l v hv; destruct l; [contradiction | right; exact hv]. Qed.

    Lemma sum_app : forall l1 l2 : list F,
      fold_right add zero (l1 ++ l2) = fold_right add zero l1 + fold_right add zero l2.
    Proof. induction l1 as [| a l1 ih]; intros l2; cbn [app fold_right]; [field | rewrite ih; field]. Qed.

    Lemma tl_len : forall {X : Type} (l : list X), length (tl l) = (length l - 1)%nat.
    Proof. intros X l; destruct l; cbn; lia. Qed.

    Local Ltac len_tac := rewrite ?app_length, ?tl_len, ?map_length, ?seq_length; cbn [length]; lia.

    Record hadamard_argument : Type := mk_had { ha_cB : list G; ha_zero : zero_argument }.

    (* Algorithm 9.21; statement (cA = (c_{A0}, …, c_{A(m−1)}), c_b), vectors of
      length n; challenges x, y of the Hadamard argument and xz of its zero argument *)
    (* the statement of the zero argument inside the Hadamard argument:
      ((c_{A1}, …, c_{A(m−1)}, c_{−1}), (c_{D0}, …, c_{D(m−2)}, c_D)) *)
    Definition hadamard_zero_stmt (h : G) (gs : list G) (n : nat) (cA cB : list G) (x : F) : list G * list G :=
      let m := length cA in
      let cDs := map (fun i => (nth i cB gid) ^ (fpow x (S i))) (seq 0 (m - 1)) in
      let cD := (geval (tl cB) x) ^ x in
      let cneg := com h gs (repeat (opp one) n) zero in
      (tl cA ++ [cneg], cDs ++ [cD]).

    Definition hadamard_verify (h : G) (gs : list G) (n : nat) (cA : list G) (cb : G) (x y xz : F)
      (arg : hadamard_argument) : bool :=
      let m := length cA in
      let cB := ha_cB arg in
      (2 <=? m) && (length cB =? m) &&
      (if Gdec (nth 0 cB gid) (nth 0 cA gid) then true else false) &&
      (if Gdec (nth (m - 1) cB gid) cb then true else false) &&
      (let st := hadamard_zero_stmt h gs n cA cB x in
       zero_verify h gs (fst st) (snd st) y xz (ha_zero arg)) &&
      (if Fdec x zero then false else true) && (if Fdec y zero then false else true).

    (* Algorithm 9.20 with its randomness as parameters: s_1..s_{m−2} (smid) and
      the zero argument's a_0, b_m, r_0, s_m, t *)
    Definition hadamard_prove (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F) (s : F)
      (smid : list F) (x y : F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F) (xz : F) : hadamard_argument :=
      let m := length A in
      let Bs := map (hprefix A) (seq 0 m) in
      let ss := nth 0 r zero :: smid ++ [s] in
      let cB := com_list h gs Bs ss in
      let ds := map (fun i => lscale (fpow x (S i)) (hprefix A i)) (seq 0 (m - 1)) in
      let ts := map (fun i => fpow x (S i) * nth i ss zero) (seq 0 (m - 1)) in
      let d := lscale x (lveval (tl Bs) x) in
      let t := x * feval (tl ss) x in
      mk_had cB (zero_prove h gs (tl A ++ [repeat (opp one) n]) (ds ++ [d]) (tl r ++ [zero]) (ts ++ [t])
        y a0z bmz r0z smz t1 t2 xz).

    Theorem hadamard_completeness : forall (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F)
      (s : F) (smid : list F) (x y : F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F) (xz : F),
      (2 <= length A)%nat -> Forall (fun a => length a = n) A -> length r = length A ->
      length smid = (length A - 2)%nat -> length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
      n = length gs -> length a0z = length gs -> length bmz = length gs -> x <> zero -> y <> zero ->
      hadamard_verify h gs n (com_list h gs A r) (com h gs (hprefix A (length A - 1)) s) x y xz
        (hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 xz) = true.
    Proof.
      intros * hm hA hr hsmid ht1 ht2 hng ha0z hbmz hx0 hy0; unfold hadamard_verify, hadamard_prove, hadamard_zero_stmt;
      cbn [ha_cB ha_zero fst snd]; cbv zeta.
      set (m := length A) in *.
      assert (hmA : length A = m) by reflexivity.
      assert (hA0 : A <> []) by (intro e; rewrite e in hmA; cbn in hmA; lia).
      assert (hss : length (nth 0 r zero :: smid ++ [s]) = m) by (cbn; rewrite app_length; cbn; lia).
      assert (hBs : length (map (hprefix A) (seq 0 m)) = m) by (rewrite map_length, seq_length; reflexivity).
      assert (htl : tl (map (hprefix A) (seq 0 m)) = map (fun i => hprefix A (S i)) (seq 0 (m - 1))).
      { destruct m as [| m']; [lia |]; cbn [seq map tl]; rewrite <-seq_shift, map_map.
        replace (S m' - 1)%nat with m' by lia; reflexivity. }
      rewrite !com_list_length, hBs, hss, hr, !Nat.min_id.
      apply andb_true_iff; split; [apply andb_true_iff; split;
        [| destruct (Fdec x zero); [contradiction | reflexivity]] | destruct (Fdec y zero); [contradiction | reflexivity]].
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split |] |] |].
      + apply Nat.leb_le; exact hm.
      + apply Nat.eqb_eq; reflexivity.
      + (* c_{B0} = c_{A0} *)
        dec_true.
        rewrite (nth_com_list h gs (map (hprefix A) (seq 0 m)) (nth 0 r zero :: smid ++ [s]) 0);
          [| rewrite hBs, hss; reflexivity | rewrite hBs; lia].
        rewrite (nth_com_list h gs A r 0); [| lia | lia].
        rewrite nth_map_seq by lia; rewrite hprefix_0 by exact hA0; reflexivity.
      + (* c_{B(m−1)} = c_b *)
        dec_true.
        rewrite (nth_com_list h gs (map (hprefix A) (seq 0 m)) (nth 0 r zero :: smid ++ [s]) (m - 1));
          [| rewrite hBs, hss; reflexivity | rewrite hBs; lia].
        rewrite nth_map_seq by lia.
        rewrite app_comm_cons; replace (m - 1)%nat with (length (nth 0 r zero :: smid)) at 2 by (cbn; lia).
        rewrite nth_middle; reflexivity.
      + (* the zero argument *)
        (* the statement lists are commitment lists *)
        assert (hzA : tl (com_list h gs A r) ++ [com h gs (repeat (opp one) n) zero] =
          com_list h gs (tl A ++ [repeat (opp one) n]) (tl r ++ [zero])).
        { rewrite com_list_app by (destruct A, r; cbn in *; lia); rewrite com_list_tl; reflexivity. }
        assert (hzB : map (fun i => (nth i (com_list h gs (map (hprefix A) (seq 0 m)) (nth 0 r zero :: smid ++ [s])) gid) ^ (fpow x (S i))) (seq 0 (m - 1))
            ++ [(geval (tl (com_list h gs (map (hprefix A) (seq 0 m)) (nth 0 r zero :: smid ++ [s]))) x) ^ x] =
          com_list h gs (map (fun i => lscale (fpow x (S i)) (hprefix A i)) (seq 0 (m - 1)) ++ [lscale x (lveval (tl (map (hprefix A) (seq 0 m))) x)])
            (map (fun i => fpow x (S i) * nth i (nth 0 r zero :: smid ++ [s]) zero) (seq 0 (m - 1)) ++ [x * feval (tl (nth 0 r zero :: smid ++ [s])) x])).
        { rewrite com_list_app by (rewrite !map_length, !seq_length; reflexivity).
          f_equal.
          - apply (nth_ext _ _ gid gid).
            * rewrite com_list_length, !map_length, !seq_length; lia.
            * intros i hi; rewrite map_length, seq_length in hi.
              rewrite nth_map_seq by exact hi.
              rewrite (nth_com_list h gs (map (hprefix A) (seq 0 m)) (nth 0 r zero :: smid ++ [s]) i);
                [| rewrite hBs, hss; reflexivity | rewrite hBs; lia].
              rewrite (nth_com_list h gs (map (fun i => lscale (fpow x (S i)) (hprefix A i)) (seq 0 (m - 1)))
                (map (fun i => fpow x (S i) * nth i (nth 0 r zero :: smid ++ [s]) zero) (seq 0 (m - 1))) i);
                [| rewrite !map_length, !seq_length; reflexivity | rewrite map_length, seq_length; lia].
              rewrite !nth_map_seq by lia.
              symmetry; apply com_scale.
          - rewrite com_list_tl, htl; cbn [tl].
            rewrite geval_com_list by (rewrite map_length, seq_length, app_length; cbn; lia).
            unfold com_list; cbn [combine map fst snd]; rewrite com_scale; reflexivity. }
        rewrite hzA, hzB.
        apply zero_completeness.
        * len_tac.
        * len_tac.
        * len_tac.
        * len_tac.
        * len_tac.
        * len_tac.
        * (* the rows of (a_0, a_1, …, a_{m−1}, −1) have the key's length *)
          constructor; [exact ha0z |]. apply Forall_app; split.
          - rewrite Forall_forall in hA |- *; intros v hv; rewrite <-hng; apply hA, in_tl; exact hv.
          - constructor; [rewrite repeat_length; exact hng | constructor].
        * (* the rows of (b_m, x b_0, …, x^{m−1} b_{m−2}, d) have the key's length *)
          constructor; [exact hbmz |]. apply Forall_app; split.
          - rewrite Forall_forall; intros v hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi.
            unfold SigmaK.lscale; rewrite length_map, <-hng; apply (hprefix_length n A i hA); lia.
          - constructor; [| constructor]. unfold SigmaK.lscale; rewrite length_map.
            apply lveval_length.
            { rewrite htl; intro e; apply (f_equal (@length (list F))) in e; rewrite map_length, seq_length in e; cbn in e; lia. }
            rewrite htl; intros v hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi.
            rewrite <-hng; apply (hprefix_length n A (S i) hA); lia.
        * (* Σ_{i<m−1} a_{i+1} ⋆ (x^{i+1} b_i) + (−1) ⋆ d = 0 *)
          rewrite combine_app_eq by (rewrite map_length, seq_length; destruct A; [contradiction | cbn; lia]).
          rewrite map_app, sum_app; cbn [combine map fold_right fst snd].
          set (S_ := fun i => star y (repeat one n) (hprefix A (S i))).
          assert (hfirst : fold_right add zero (map (fun p => star y (fst p) (snd p))
              (combine (tl A) (map (fun i => lscale (fpow x (S i)) (hprefix A i)) (seq 0 (m - 1))))) =
            fold_right add zero (map (fun i => fpow x (S i) * S_ i) (seq 0 (m - 1)))).
          { f_equal. apply (nth_ext _ _ zero zero).
            + rewrite !map_length, combine_length, map_length, seq_length; destruct A; [contradiction | cbn; lia].
            + intros i hi; rewrite map_length, combine_length, map_length, seq_length in hi.
              rewrite (nth_indep _ zero ((fun p : list F * list F => star y (fst p) (snd p)) (@nil F, @nil F)))
                by (rewrite map_length, combine_length, map_length, seq_length; exact hi).
              rewrite (map_nth (fun p : list F * list F => star y (fst p) (snd p))).
              rewrite combine_nth by (rewrite map_length, seq_length; destruct A; [contradiction | cbn; lia]).
              cbn [fst snd]; rewrite !nth_map_seq by lia.
              rewrite nth_tl by exact hA0.
              rewrite star_lscale_r; unfold S_; rewrite (star_ones_hprefix n) by (assumption || lia); reflexivity. }
          rewrite hfirst, sum_pow_feval.
          rewrite neg_ones, star_lscale_l, star_lscale_r, <-star_lveval_r, htl, map_map.
          fold S_; field.
    Qed.

  End Hadamard.

  (* ---------------------------------------------------------------- *)
  (* Multi-exponentiation argument (Algorithms 9.15, 9.16, 9.17)       *)
  (* ---------------------------------------------------------------- *)

  Section MultiExponentiation.

    (* ciphertexts with l recipients: (γ, φ_0, …, φ_{l−1}), the product vector space *)
    Context {l : nat}.
    Local Notation CT := (Vector.t G (S l)).
    Local Notation cone := (vec_id (V := G) (vid := gid) (S l)).
    Local Notation cmul := (vec_add (vadd := gop) (n := S l)).
    Local Notation cpow := (vec_smul (smul := gpow) (n := S l)).
    Local Notation CTvs := (vec_vspace (HV := Hvec) (S l)).
    Local Notation cmexp := (lmexp (vid := cone) (vadd := cmul) (smul := cpow)).
    Local Notation ceval := (veval (vid := cone) (vadd := cmul) (smul := cpow)).
    Local Notation cpadd := (vpadd (vadd := cmul)).
    Local Notation cprod := (fold_right cmul cone).

    (* Algorithm 8.6: Enc(m; r) = (g^r, pk_j^r m_j) *)
    Definition enc (g : G) (pk : Vector.t G l) (ms : Vector.t G l) (r : F) : CT :=
      Vector.cons G (g ^ r) l (Vector.map2 (fun y m => gop (y ^ r) m) pk ms).

    (* Enc(g^b, …, g^b; τ) *)
    Definition encg (g : G) (pk : Vector.t G l) (b τ : F) : CT := enc g pk (Vector.const (g ^ b) l) τ.

    Lemma encg_mul : forall g pk b1 τ1 b2 τ2,
      cmul (encg g pk b1 τ1) (encg g pk b2 τ2) = encg g pk (b1 + b2) (τ1 + τ2).
    Proof.
      intros; unfold encg, enc, vec_add.
      apply Vector.eq_nth_iff; intros j ? <-.
      destruct (fin_inv_S _ j) as [-> | (j' & ->)].
      + cbn [Vector.map2 Vector.nth Vector.caseS]; symmetry; apply gpow_add.
      + rewrite (Vector.nth_map2 _ _ _ (Fin.FS j') (Fin.FS j') (Fin.FS j') eq_refl eq_refl).
        cbn [Vector.nth Vector.caseS].
        rewrite !(Vector.nth_map2 _ _ _ j' j' j' eq_refl eq_refl), !Vector.const_nth.
        rewrite gop4, <-gpow_add, <-gpow_add; reflexivity.
    Qed.

    Lemma encg_pow : forall g pk b τ c, cpow (encg g pk b τ) c = encg g pk (b * c) (τ * c).
    Proof.
      intros; unfold encg, enc, vec_smul.
      apply Vector.eq_nth_iff; intros j ? <-.
      destruct (fin_inv_S _ j) as [-> | (j' & ->)].
      + cbn [Vector.map Vector.map2 Vector.nth Vector.caseS]; symmetry; apply gpow_mul.
      + rewrite (Vector.nth_map _ _ (Fin.FS j') (Fin.FS j') eq_refl); cbn [Vector.nth Vector.caseS].
        rewrite !(Vector.nth_map2 _ _ _ j' j' j' eq_refl eq_refl), !Vector.const_nth.
        rewrite gop_pow, <-!gpow_mul; reflexivity.
    Qed.

    (* Σ_k x^k Enc(g^{b_k}; τ_k) = Enc(g^{Σ x^k b_k}; Σ x^k τ_k) *)
    Lemma ceval_encg : forall g pk (bs τs : list F) x, length bs = length τs ->
      ceval (map (fun p => encg g pk (fst p) (snd p)) (combine bs τs)) x = encg g pk (feval bs x) (feval τs x).
    Proof.
      intros g pk bs; induction bs as [| b bs ih]; intros τs x hl.
      + destruct τs; [| discriminate]; cbn [combine map]; rewrite veval_nil, !feval_nil.
        unfold encg, enc, vec_id; apply Vector.eq_nth_iff; intros j ? <-.
        destruct (fin_inv_S _ j) as [-> | (j' & ->)].
        - cbn [Vector.nth Vector.caseS Vector.const]; rewrite gpow_zero; reflexivity.
        - cbn [Vector.nth Vector.caseS Vector.const].
          rewrite (Vector.nth_map2 _ _ _ j' j' j' eq_refl eq_refl), !Vector.const_nth, !gpow_zero, gid_l; reflexivity.
      + destruct τs as [| τ τs]; [discriminate |].
        cbn [combine map fst snd]; rewrite (veval_cons (HV := CTvs)), ih by (cbn in hl; lia).
        rewrite encg_pow, encg_mul, !feval_cons.
        replace (feval bs x * x) with (x * feval bs x) by field.
        replace (feval τs x * x) with (x * feval τs x) by field; reflexivity.
    Qed.

    (* ---- diagonal products via shifted evaluation ---- *)

    (* the row i contributes C_i^{a_0}, …, C_i^{a_m} shifted by m − i − 1 places *)
    Definition diag_row (m : nat) (As : list (list F)) (p : nat * list CT) : list CT :=
      repeat cone (m - fst p - 1) ++ map (fun a => cmexp (snd p) a) As.

    (* the products of the diagonals D_0, …, D_{2m−1} (Algorithm 9.17) *)
    Definition diagonals (m : nat) (Cs : list (list CT)) (As : list (list F)) : list CT :=
      fold_right (fun row acc => cpadd row acc) [] (map (diag_row m As) (combine (seq 0 m) Cs)).

    Lemma ceval_fold_cpadd : forall (L : list (list CT)) x,
      ceval (fold_right (fun row acc => cpadd row acc) [] L) x = cprod (map (fun row => ceval row x) L).
    Proof.
      induction L as [| row L ih]; intros x; [reflexivity |].
      cbn [fold_right map]; rewrite (veval_vpadd (HV := CTvs)), ih; reflexivity.
    Qed.

    Lemma nth_fold_cpadd : forall (L : list (list CT)) k,
      nth k (fold_right (fun row acc => cpadd row acc) [] L) cone = cprod (map (fun row => nth k row cone) L).
    Proof.
      induction L as [| row L ih]; intros k; [destruct k; reflexivity |].
      cbn [fold_right map]; rewrite (nth_vpadd (HV := CTvs)), ih; reflexivity.
    Qed.

    Lemma fold_cpadd_length_le : forall (L : list (list CT)) (b : nat),
      Forall (fun row => (length row <= b)%nat) L -> (length (fold_right (fun row acc => cpadd row acc) [] L) <= b)%nat.
    Proof.
      induction L as [| row L ih]; intros b hL; [cbn; lia |].
      inversion hL as [| ? ? hrow hL']; subst; cbn [fold_right]; rewrite vpadd_length; specialize (ih b hL'); lia.
    Qed.

    (* C^{Σ x^i a_i} as an evaluation *)
    Lemma ceval_map_cmexp : forall (Ci : list CT) (As : list (list F)) x,
      ceval (map (fun a => cmexp Ci a) As) x = cmexp Ci (lveval As x).
    Proof.
      intros; unfold lveval.
      apply (veval_map_linear (HV := CTvs) (fun a => cmexp Ci a) [] padd lscale).
      + apply lmexp_nil_r.
      + intros; apply (lmexp_padd (HV := CTvs)).
      + intros; apply (lmexp_scale (HV := CTvs)).
    Qed.

    Lemma ceval_diag_row : forall m As x (p : nat * list CT),
      ceval (diag_row m As p) x = cmexp (snd p) (lscale (fpow x (m - fst p - 1)) (lveval As x)).
    Proof.
      intros; unfold diag_row; rewrite (veval_shift (HV := CTvs)), ceval_map_cmexp, (lmexp_scale (HV := CTvs)).
      reflexivity.
    Qed.

    (* ---- the argument ---- *)

    Record multiexp_argument : Type := mk_mexp {
      me_cA0 : G; me_cB : list G; me_E : list CT; me_a : list F; me_r : F; me_b : F; me_s : F; me_tau : F }.

    (* Algorithm 9.16; statement (rows Cs, C, cA); challenge x *)
    Definition multiexp_verify (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
      (Cs : list (list CT)) (C : CT) (cA : list G) (x : F) (arg : multiexp_argument) : bool :=
      let m := length cA in
      let cB := me_cB arg in let E := me_E arg in let a := me_a arg in
      (1 <=? m) && (length Cs =? m) && (length cB =? 2 * m) && (length E =? 2 * m) &&
      (if Gdec (nth m cB gid) gid then true else false) &&
      (if vec_dec Gdec (nth m E cone) C then true else false) &&
      (if Gdec (geval (me_cA0 arg :: cA) x) (com h gs a (me_r arg)) then true else false) &&
      (if Gdec (geval cB x) (com h gs [me_b arg] (me_s arg)) then true else false) &&
      (let prodC := cprod (map (fun p => cmexp (snd p) (lscale (fpow x (m - fst p - 1)) a)) (combine (seq 0 m) Cs)) in
       if vec_dec Gdec (ceval E x) (cmul (encg g pk (me_b arg) (me_tau arg)) prodC) then true else false) &&
      (length a =? length gs).

    (* set the m-th entry of a list *)
    Definition set_nth (k : nat) (v : F) (xs : list F) : list F :=
      map (fun p => if Nat.eqb (fst p) k then v else snd p) (combine (seq 0 (length xs)) xs).

    Lemma set_nth_length : forall k v xs, length (set_nth k v xs) = length xs.
    Proof. intros; unfold set_nth; rewrite map_length, combine_length, seq_length; lia. Qed.

    Lemma nth_set_nth : forall k v xs i, (i < length xs)%nat ->
      nth i (set_nth k v xs) zero = if Nat.eqb i k then v else nth i xs zero.
    Proof.
      intros k v xs i hi; unfold set_nth.
      rewrite (nth_indep _ zero ((fun p => if Nat.eqb (fst p) k then v else snd p) (0%nat, zero)))
        by (rewrite map_length, combine_length, seq_length; lia).
      rewrite (map_nth (fun p => if Nat.eqb (fst p) k then v else snd p)).
      rewrite combine_nth by (rewrite seq_length; reflexivity); cbn [fst snd].
      rewrite seq_nth by exact hi; reflexivity.
    Qed.

    (* Algorithm 9.15 with its randomness as parameters: a_0, r_0, and the
      2m values b_k, s_k, τ_k (whose m-th entries are replaced by 0, 0, ρ) *)
    Definition multiexp_prove (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
      (Cs : list (list CT)) (A : list (list F)) (r : list F) (ρ : F)
      (a0 : list F) (r0 : F) (bs ss τs : list F) (x : F) : multiexp_argument :=
      let m := length A in
      let As := a0 :: A in
      let bz := set_nth m zero bs in
      let sz := set_nth m zero ss in
      let τz := set_nth m ρ τs in
      let D := diagonals m Cs As in
      let E := cpadd (map (fun p => encg g pk (fst p) (snd p)) (combine bz τz)) D in
      mk_mexp (com h gs a0 r0) (com_list h gs (map (fun bk => [bk]) bz) sz) E
        (lveval As x) (feval (r0 :: r) x) (feval bz x) (feval sz x) (feval τz x).

    Lemma nth_diag_row_m : forall m As i (Ci : list CT), (i < m)%nat -> (length As = S m) ->
      nth m (diag_row m As (i, Ci)) cone = cmexp Ci (nth (S i) As []).
    Proof.
      intros m As i Ci hi hA; unfold diag_row; cbn [fst snd].
      rewrite app_nth2 by (rewrite repeat_length; lia); rewrite repeat_length.
      replace (m - (m - i - 1))%nat with (S i) by lia.
      rewrite (nth_indep _ cone ((fun a => cmexp Ci a) [])) by (rewrite map_length; lia).
      apply map_nth.
    Qed.

    Theorem multiexp_completeness : forall (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
      (Cs : list (list CT)) (A : list (list F)) (r : list F) (ρ : F) (a0 : list F) (r0 : F) (bs ss τs : list F) (x : F),
      (1 <= length A)%nat -> length Cs = length A -> length r = length A ->
      length bs = (2 * length A)%nat -> length ss = (2 * length A)%nat -> length τs = (2 * length A)%nat ->
      Forall (fun v => length v = length gs) (a0 :: A) ->
      multiexp_verify h gs g pk Cs
        (cmul (enc g pk (Vector.const gid l) ρ) (cprod (map (fun p => cmexp (snd p) (nth (fst p) A [])) (combine (seq 0 (length A)) Cs))))
        (com_list h gs A r) x (multiexp_prove h gs g pk Cs A r ρ a0 r0 bs ss τs x) = true.
    Proof.
      intros * hm hC hr hb hs ht hAn; unfold multiexp_verify, multiexp_prove;
      cbn [me_cA0 me_cB me_E me_a me_r me_b me_s me_tau]; cbv zeta.
      set (m := length A) in *.
      assert (hmA : length A = m) by reflexivity.
      assert (hlenD : (length (diagonals m Cs (a0 :: A)) <= 2 * m)%nat).
      { unfold diagonals; apply fold_cpadd_length_le.
        rewrite Forall_forall; intros row hrow; apply in_map_iff in hrow; destruct hrow as ((i & Ci) & <- & hp).
        apply in_combine_l in hp; apply in_seq in hp.
        unfold diag_row; cbn [fst snd]; rewrite app_length, repeat_length, map_length; cbn [length]; lia. }
      assert (hE : length (cpadd (map (fun p => encg g pk (fst p) (snd p)) (combine (set_nth m zero bs) (set_nth m ρ τs)))
        (diagonals m Cs (a0 :: A))) = (2 * m)%nat).
      { rewrite vpadd_length, map_length, combine_length, !set_nth_length; lia. }
      rewrite !com_list_length, hE, !map_length, !set_nth_length, hr, hb, hs, hC, !Nat.min_id.
      repeat (apply andb_true_iff; split).
      + apply Nat.leb_le; exact hm.
      + apply Nat.eqb_eq; reflexivity.
      + apply Nat.eqb_eq; lia.
      + apply Nat.eqb_eq; reflexivity.
      + (* c_{Bm} = 1 *)
        dec_true.
        rewrite (nth_com_list h gs (map (fun bk => [bk]) (set_nth m zero bs)) (set_nth m zero ss) m);
          [| rewrite map_length, !set_nth_length; lia | rewrite map_length, set_nth_length; lia].
        rewrite (nth_indep (map (fun bk : F => [bk]) _) [] ((fun bk : F => [bk]) zero))
          by (rewrite map_length, set_nth_length; lia).
        rewrite (map_nth (fun bk : F => [bk])), !nth_set_nth by lia; rewrite Nat.eqb_refl.
        apply com_zero_single.
      + (* E_m = C *)
        dec_true.
        rewrite (nth_vpadd (HV := CTvs)).
        rewrite (nth_indep (map _ (combine _ _)) cone ((fun p => encg g pk (fst p) (snd p)) (zero, zero)))
          by (rewrite map_length, combine_length, !set_nth_length; lia).
        rewrite (map_nth (fun p => encg g pk (fst p) (snd p))).
        rewrite combine_nth by (rewrite !set_nth_length; lia); cbn [fst snd].
        rewrite !nth_set_nth by lia; rewrite Nat.eqb_refl; cbv iota.
        unfold diagonals; rewrite nth_fold_cpadd, map_map.
        f_equal.
        - unfold encg; rewrite gpow_zero; reflexivity.
        - f_equal; apply map_ext_in; intros (i & Ci) hp.
          apply in_combine_l in hp; apply in_seq in hp; cbn [fst snd].
          rewrite nth_diag_row_m by (cbn; lia); cbn [nth]; reflexivity.
      + (* c_{A0} ∏ c_{Ai}^{x^i} = com(a; r) *)
        dec_true; rewrite <-com_list_cons, geval_com_list by (cbn; lia); reflexivity.
      + (* c_{B0} ∏ c_{Bk}^{x^k} = com(b; s) *)
        dec_true; rewrite geval_com_list by (rewrite map_length, !set_nth_length; lia).
        rewrite lveval_singletons; [reflexivity |].
        intro e; apply (f_equal (@length F)) in e; rewrite set_nth_length in e; cbn in e; lia.
      + (* E_0 ∏ E_k^{x^k} = Enc(g^b; τ) ∏_i C_i^{x^{m−i−1} a} *)
        dec_true.
        rewrite (veval_vpadd (HV := CTvs)), ceval_encg by (rewrite !set_nth_length; lia).
        f_equal.
        unfold diagonals; rewrite ceval_fold_cpadd, map_map.
        f_equal; apply map_ext_in; intros (i & Ci) hp; rewrite ceval_diag_row; reflexivity.
      + (* the response has the key's length *)
        apply Nat.eqb_eq; apply lveval_length; [discriminate | rewrite Forall_forall in hAn; exact hAn].
    Qed.

  End MultiExponentiation.

  (* ---------------------------------------------------------------- *)
  (* Product argument (Algorithms 9.18, 9.19)                          *)
  (* ---------------------------------------------------------------- *)

  Section ProductArgument.

    Record product_argument : Type := mk_prod {
      pa_cb : G; pa_had : option hadamard_argument; pa_svp : svp_argument }.

    (* Algorithm 9.19; statement (cA = (c_{A1}, …, c_{Am}), b), vectors of length n;
      challenges xh, yh, xz for the Hadamard and zero arguments, xs for the
      single value product argument *)
    Definition product_verify (h : G) (gs : list G) (n : nat) (cA : list G) (b : F) (xh yh xz xs : F)
      (arg : product_argument) : bool :=
      let m := length cA in
      if 1 <? m then
        match pa_had arg with
        | Some had => hadamard_verify h gs n cA (pa_cb arg) xh yh xz had && svp_verify h gs (pa_cb arg) b xs (pa_svp arg)
        | None => false
        end
      else svp_verify h gs (nth 0 cA gid) b xs (pa_svp arg).

    (* Algorithm 9.18 with its randomness as parameters *)
    Definition product_prove (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F)
      (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
      (d : list F) (rd : F) (dmid : list F) (s0 sx : F) (xh yh xz xs : F) : product_argument :=
      let m := length A in
      let bvec := hprefix A (m - 1) in
      if 1 <? m then
        mk_prod (com h gs bvec s) (Some (hadamard_prove h gs n A r s smid xh yh a0z bmz r0z smz t1 t2 xz))
          (svp_prove h gs bvec s d rd dmid s0 sx xs)
      else
        mk_prod gid None (svp_prove h gs (nth 0 A []) (nth 0 r zero) d rd dmid s0 sx xs).

    Theorem product_completeness : forall (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F)
      (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
      (d : list F) (rd : F) (dmid : list F) (s0 sx : F) (xh yh xz xs : F),
      (1 <= length A)%nat -> (2 <= n)%nat -> Forall (fun a => length a = n) A -> length r = length A ->
      length smid = (length A - 2)%nat -> length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
      length d = n -> length dmid = (n - 2)%nat ->
      n = length gs -> length a0z = length gs -> length bmz = length gs ->
      ((1 < length A)%nat -> xh <> zero) -> ((1 < length A)%nat -> yh <> zero) ->
      product_verify h gs n (com_list h gs A r) (fold_right mul one (hprefix A (length A - 1))) xh yh xz xs
        (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs) = true.
    Proof.
      intros * hm hn hA hr hsmid ht1 ht2 hd hdmid hng ha0z hbmz hx0 hy0; unfold product_verify, product_prove; cbv zeta.
      rewrite com_list_length, hr, Nat.min_id.
      assert (hbl : length (hprefix A (length A - 1)) = n) by (apply hprefix_length with (n := n); [exact hA | lia]).
      destruct (1 <? length A) eqn:hlt; cbn [pa_cb pa_had pa_svp].
      + apply Nat.ltb_lt in hlt.
        apply andb_true_iff; split.
        - apply hadamard_completeness; first [assumption | lia | apply hx0; exact hlt | apply hy0; exact hlt].
        - apply svp_completeness; [lia | rewrite hd; symmetry; exact hbl | rewrite hdmid, hbl; reflexivity | rewrite hbl; exact hng].
      + apply Nat.ltb_ge in hlt.
        assert (hm1 : length A = 1%nat) by lia.
        rewrite (nth_com_list h gs A r 0) by lia.
        replace (length A - 1)%nat with 0%nat by lia.
        rewrite hprefix_0 by (destruct A; [cbn in hm1; lia | discriminate]).
        assert (ha0 : length (nth 0 A []) = n).
        { rewrite Forall_forall in hA; apply hA; apply nth_In; lia. }
        apply svp_completeness; [lia | rewrite hd; symmetry; exact ha0 | rewrite hdmid, ha0; reflexivity | rewrite ha0; exact hng].
    Qed.

  End ProductArgument.

  (* ---------------------------------------------------------------- *)
  (* The shuffle argument (Algorithms 9.11, 9.12)                      *)
  (* ---------------------------------------------------------------- *)

  Lemma fold_mul_perm : forall (l1 l2 : list F), Permutation l1 l2 ->
    fold_right mul one l1 = fold_right mul one l2.
  Proof.
    intros l1 l2 hp; induction hp as [| a l1 l2 hp ih | a b l | l1 l2 l3 hp1 ih1 hp2 ih2].
    + reflexivity.
    + cbn [fold_right]; rewrite ih; reflexivity.
    + cbn [fold_right]; field.
    + rewrite ih1; exact ih2.
  Qed.

  Lemma combine_map_same : forall {A B C : Type} (f : A -> B) (g : A -> C) (l : list A),
    combine (map f l) (map g l) = map (fun a => (f a, g a)) l.
  Proof. induction l as [| a l ih]; [reflexivity | cbn; rewrite ih; reflexivity]. Qed.

  Lemma map_nth_seq : forall {A B : Type} (f : A -> B) (d : A) (l : list A),
    map (fun i => f (nth i l d)) (seq 0 (length l)) = map f l.
  Proof.
    intros A B f d l; apply (nth_ext _ _ (f d) (f d)); [rewrite !map_length, seq_length; reflexivity |].
    intros i hi; rewrite map_length, seq_length in hi.
    rewrite nth_map_seq by exact hi; symmetry; apply map_nth.
  Qed.

  Lemma map_nth_seq' : forall {A B : Type} (f : A -> B) (d : A) (l : list A) (N : nat), length l = N ->
    map (fun i => f (nth i l d)) (seq 0 N) = map f l.
  Proof. intros * hl; rewrite <-hl; apply map_nth_seq. Qed.

  Lemma lpows_map : forall x N, lpows x N = map (fpow x) (seq 0 N).
  Proof.
    intros x N; induction N as [| N ih]; [reflexivity |].
    cbn [SigmaK.lpows seq map SigmaK.fpow]; rewrite ih, <-seq_shift, map_map; unfold SigmaK.lscale; rewrite map_map.
    f_equal; apply map_ext; intro i; cbn [SigmaK.fpow]; reflexivity.
  Qed.

  Lemma nth_skipn' : forall {X : Type} (l : list X) k i (d : X), nth i (skipn k l) d = nth (k + i) l d.
  Proof.
    intros X l k; revert l; induction k as [| k ih]; intros l i d; [reflexivity |].
    destruct l as [| a l]; [destruct i; reflexivity | cbn [skipn Nat.add nth]; apply ih].
  Qed.

  Lemma nth_firstn' : forall {X : Type} (l : list X) n i (d : X), (i < n)%nat -> nth i (firstn n l) d = nth i l d.
  Proof.
    intros X l n; revert l; induction n as [| n ih]; intros l i d hi; [lia |].
    destruct l as [| a l]; [destruct i; reflexivity |].
    destruct i as [| i]; [reflexivity | cbn [firstn nth]; apply ih; lia].
  Qed.

  Lemma nth_repeat' : forall (x : F) k i, (i < k)%nat -> nth i (repeat x k) zero = x.
  Proof.
    intros x k; induction k as [| k ih]; intros i hi; [lia |].
    destruct i as [| i]; [reflexivity | cbn [repeat nth]; apply ih; lia].
  Qed.

  (* m chunks of n consecutive entries (Algorithm 9.13, the rows; the
    transposed exponent matrices have the same chunks as columns) *)
  Fixpoint chunk {X : Type} (n m : nat) (xs : list X) : list (list X) :=
    match m with 0 => [] | S m' => firstn n xs :: chunk n m' (skipn n xs) end.

  Lemma chunk_length : forall {X : Type} n m (xs : list X), length (chunk n m xs) = m.
  Proof. intros X n m; revert n; induction m as [| m ih]; intros n xs; [reflexivity | cbn; rewrite ih; reflexivity]. Qed.

  Lemma concat_chunk : forall {X : Type} n m (xs : list X), length xs = (m * n)%nat -> concat (chunk n m xs) = xs.
  Proof.
    intros X n m; revert n; induction m as [| m ih]; intros n xs hl.
    + cbn in hl; destruct xs; [reflexivity | cbn in hl; lia].
    + cbn [chunk concat]; rewrite ih by (rewrite skipn_length; cbn in hl; lia); apply firstn_skipn.
  Qed.

  Lemma chunk_forall_length : forall {X : Type} n m (xs : list X), length xs = (m * n)%nat ->
    Forall (fun c => length c = n) (chunk n m xs).
  Proof.
    intros X n m; revert n; induction m as [| m ih]; intros n xs hl; [constructor |].
    cbn [chunk]; constructor.
    + rewrite firstn_length; cbn in hl; lia.
    + apply ih; rewrite skipn_length; cbn in hl; lia.
  Qed.

  Lemma nth_chunk : forall {X : Type} n m (xs : list X) j, (j < m)%nat ->
    nth j (chunk n m xs) [] = firstn n (skipn (j * n) xs).
  Proof.
    intros X n m; revert n; induction m as [| m ih]; intros n xs j hj; [lia |].
    destruct j as [| j]; [reflexivity |].
    cbn [chunk nth]; rewrite ih by lia; rewrite skipn_skipn; f_equal; f_equal; lia.
  Qed.

  Lemma nth_firstn_skipn : forall {X : Type} n k (xs : list X) t (d : X), (t < n)%nat ->
    nth t (firstn n (skipn k xs)) d = nth (k + t) xs d.
  Proof. intros; rewrite nth_firstn' by assumption; apply nth_skipn'. Qed.

  (* the product of all entries of a matrix is the product of its Hadamard product *)
  Lemma fold_mul_hmul : forall a b, length a = length b ->
    fold_right mul one (hmul a b) = fold_right mul one a * fold_right mul one b.
  Proof.
    induction a as [| a0 a ih]; intros b hl; destruct b as [| b0 b]; try discriminate; [cbn; field |].
    unfold hmul; cbn [combine map fst snd fold_right]; fold (hmul a b); rewrite ih by (cbn in hl; lia); field.
  Qed.

  Lemma fold_mul_fold_left_hmul : forall n (cs : list (list F)) (c : list F),
    Forall (fun c => length c = n) cs -> length c = n ->
    fold_right mul one (fold_left hmul cs c) = fold_right mul one c * fold_right mul one (concat cs).
  Proof.
    intros n cs; induction cs as [| c1 cs ih]; intros c hcs hc; [cbn; field |].
    inversion hcs as [| ? ? hc1 hcs']; subst.
    cbn [fold_left concat]; rewrite ih by (try assumption; rewrite hmul_length; lia).
    rewrite fold_mul_hmul by lia; rewrite fold_right_app, (fold_right_mul_init c1 (fold_right mul one (concat cs))); field.
  Qed.

  Lemma prod_hprefix_concat : forall n (A : list (list F)), A <> [] -> Forall (fun a => length a = n) A ->
    fold_right mul one (hprefix A (length A - 1)) = fold_right mul one (concat A).
  Proof.
    intros n A hA hl; unfold hprefix.
    replace (S (length A - 1)) with (length A) by (destruct A; [contradiction | cbn; lia]).
    rewrite firstn_all; destruct A as [| a0 A]; [contradiction |].
    apply Forall_cons_iff in hl; destruct hl as (ha0 & hA'); cbn [concat].
    rewrite (fold_mul_fold_left_hmul n) by assumption; rewrite fold_right_app, (fold_right_mul_init a0 (fold_right mul one (concat A))); field.
  Qed.

  (* the natural number i as a field element *)
  Section Shuffle.

    Context {l : nat}.
    Local Notation CT := (Vector.t G (S l)).
    Local Notation cone := (vec_id (V := G) (vid := gid) (S l)).
    Local Notation cmul := (vec_add (vadd := gop) (n := S l)).
    Local Notation cpow := (vec_smul (smul := gpow) (n := S l)).
    Local Notation CTvs := (vec_vspace (HV := Hvec) (S l)).
    Local Notation cmexp := (lmexp (vid := cone) (vadd := cmul) (smul := cpow)).
    Local Notation cprod := (fold_right cmul cone).
    Local Notation enc1 g pk := (encg (l := l) g pk zero).

    Lemma encg_zero_zero : forall g pk, encg (l := l) g pk zero zero = cone.
    Proof.
      intros; unfold encg, enc, vec_id; apply Vector.eq_nth_iff; intros j ? <-.
      destruct (fin_inv_S _ j) as [-> | (j' & ->)].
      + cbn [Vector.nth Vector.caseS]; rewrite Vector.const_nth; apply gpow_zero.
      + cbn [Vector.nth Vector.caseS]; rewrite Vector.const_nth.
        rewrite (Vector.nth_map2 _ _ _ j' j' j' eq_refl eq_refl), !Vector.const_nth, !gpow_zero, gid_l; reflexivity.
    Qed.

    Lemma enc1_ones : forall g pk ρ, enc1 g pk ρ = enc (l := l) g pk (Vector.const gid l) ρ.
    Proof. intros; unfold encg; rewrite gpow_zero; reflexivity. Qed.

    (* ∏_i Enc(g^0; f_i) = Enc(g^0; Σ f_i) *)
    Lemma cprod_enc1 : forall g pk (f : nat -> F) (L : list nat),
      cprod (map (fun i => enc1 g pk (f i)) L) = enc1 g pk (fold_right add zero (map f L)).
    Proof.
      intros g pk f L; induction L as [| i L ih]; [cbn [map fold_right]; symmetry; apply encg_zero_zero |].
      cbn [map fold_right]; rewrite ih, encg_mul; f_equal; field.
    Qed.

    (* the multi-exponentiation of the rows with the columns is the flat one *)
    Lemma cmexp_chunks_pairs : forall n m (Cs : list CT) (b : list F), length Cs = (m * n)%nat -> length b = (m * n)%nat ->
      cprod (map (fun p => cmexp (fst p) (snd p)) (combine (chunk n m Cs) (chunk n m b))) = cmexp Cs b.
    Proof.
      intros n m; revert n; induction m as [| m ih]; intros n Cs b hC hb.
      + cbn in hC; destruct Cs; [| cbn in hC; lia]; reflexivity.
      + cbn [chunk combine map fst snd fold_right].
        rewrite (ih n (skipn n Cs) (skipn n b)) by (rewrite skipn_length; cbn in *; lia).
        rewrite <-(lmexp_app (HV := CTvs) (firstn n Cs) (skipn n Cs) (firstn n b) (skipn n b))
          by (rewrite !firstn_length; cbn in *; lia).
        rewrite !firstn_skipn; reflexivity.
    Qed.

    Lemma cmexp_chunks : forall n m (Cs : list CT) (b : list F), length Cs = (m * n)%nat -> length b = (m * n)%nat ->
      cprod (map (fun p => cmexp (snd p) (nth (fst p) (chunk n m b) [])) (combine (seq 0 m) (chunk n m Cs))) = cmexp Cs b.
    Proof.
      intros n m Cs b hC hb; rewrite <-(cmexp_chunks_pairs n m Cs b hC hb).
      f_equal; apply (nth_ext _ _ cone cone).
      + rewrite !map_length, !combine_length, seq_length, !chunk_length; reflexivity.
      + intros j hj; rewrite map_length, combine_length, seq_length, chunk_length, Nat.min_id in hj.
        rewrite (nth_indep _ cone ((fun p => cmexp (snd p) (nth (fst p) (chunk n m b) [])) (0%nat, []))) by (rewrite map_length, combine_length, seq_length, chunk_length; lia).
        rewrite (map_nth (fun p => cmexp (snd p) (nth (fst p) (chunk n m b) []))).
        rewrite combine_nth by (rewrite seq_length, chunk_length; reflexivity); cbn [fst snd].
        rewrite seq_nth by exact hj; cbn [Nat.add].
        rewrite (nth_indep _ cone ((fun p => cmexp (fst p) (snd p)) ([], []))) by (rewrite map_length, combine_length, !chunk_length; lia).
        rewrite (map_nth (fun p => cmexp (fst p) (snd p))).
        rewrite combine_nth by (rewrite !chunk_length; reflexivity); reflexivity.
    Qed.

    Record shuffle_argument : Type := mk_shuffle {
      sh_cA : list G; sh_cB : list G; sh_prod : product_argument; sh_mexp : multiexp_argument (l := l) }.

    (* Algorithm 9.12; statement (Cs, Cs') with N = m·n; challenges x, y, z of the
      shuffle argument, xh, yh, xz, xs of the product argument and xm of the
      multi-exponentiation argument *)
    (* the statement of the product argument: the commitments c_D c_{−z} and the
      product ∏_i (y·i + x^i − z) *)
    Definition shuffle_product_stmt (h : G) (gs : list G) (n N : nat) (cA cB : list G) (x y z : F) : list G * F :=
      let cneg := com h gs (repeat (opp z) n) zero in
      let cD := map (fun p => gop ((fst p) ^ y) (snd p)) (combine cA cB) in
      (map (fun c => gop c cneg) cD, fold_right mul one (map (fun i => y * fnat i + fpow x i - z) (seq 0 N))).

    (* the ciphertext C = ∏_i C_i^{x^i} of the multi-exponentiation statement *)
    Definition shuffle_mexp_C (Cs : list CT) (x : F) (N : nat) : CT := cmexp Cs (lpows x N).

    Definition shuffle_verify (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
      (Cs Cs' : list CT) (x y z xh yh xz xs xm : F) (arg : shuffle_argument) : bool :=
      let N := (m * n)%nat in
      let cA := sh_cA arg in let cB := sh_cB arg in
      (1 <=? m) && (2 <=? n) && (length Cs =? N) && (length Cs' =? N) && (length cA =? m) && (length cB =? m) &&
      (let st := shuffle_product_stmt h gs n N cA cB x y z in
       product_verify h gs n (fst st) (snd st) xh yh xz xs (sh_prod arg)) &&
      multiexp_verify h gs g pk (chunk n m Cs') (shuffle_mexp_C Cs x N) cB xm (sh_mexp arg).

    (* Algorithm 9.11 with the witness (π as the list of its values, ρ) and the
      randomness of every sub-argument as parameters *)
    Definition shuffle_prove (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
      (Cs' : list CT) (perm : list nat) (ρs : list F) (r s : list F)
      (sp : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
      (d : list F) (rd : F) (dmid : list F) (s0 sx : F)
      (a0 : list F) (r0 : F) (bs ss τs : list F)
      (x y z xh yh xz xs xm : F) : shuffle_argument :=
      let a := map fnat perm in
      let A := chunk n m a in
      let b := map (fun i => fpow x i) perm in
      let B := chunk n m b in
      let dz := map (fun p => y * fst p + snd p - z) (combine a b) in
      let t := ladd (lscale y r) s in
      let ρ := opp (fold_right add zero (map (fun p => fst p * snd p) (combine ρs b))) in
      mk_shuffle (com_list h gs A r) (com_list h gs B s)
        (product_prove h gs n (chunk n m dz) t sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)
        (multiexp_prove h gs g pk (chunk n m Cs') B s ρ a0 r0 bs ss τs xm).

    Theorem shuffle_completeness : forall (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
      (Cs Cs' : list CT) (perm : list nat) (ρs : list F) (r s : list F)
      (sp : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
      (d : list F) (rd : F) (dmid : list F) (s0 sx : F) (a0 : list F) (r0 : F) (bs ss τs : list F)
      (x y z xh yh xz xs xm : F),
      let N := (m * n)%nat in
      (1 <= m)%nat -> (2 <= n)%nat -> length Cs = N -> length Cs' = N ->
      Permutation perm (seq 0 N) -> length ρs = N ->
      (forall i, (i < N)%nat -> nth i Cs' cone = cmul (enc1 g pk (nth i ρs zero)) (nth (nth i perm 0%nat) Cs cone)) ->
      length r = m -> length s = m -> length smid = (m - 2)%nat -> length t1 = S m -> length t2 = (m - 1)%nat ->
      length d = n -> length dmid = (n - 2)%nat ->
      length bs = (2 * m)%nat -> length ss = (2 * m)%nat -> length τs = (2 * m)%nat ->
      n = length gs -> length a0z = n -> length bmz = n -> length a0 = n ->
      ((1 < m)%nat -> xh <> zero) -> ((1 < m)%nat -> yh <> zero) ->
      shuffle_verify h gs g pk m n Cs Cs' x y z xh yh xz xs xm
        (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
          x y z xh yh xz xs xm) = true.
    Proof.
      intros * hm hn hC hC' hperm hρ hrel hr hs hsmid ht1 ht2 hd hdmid hb hss hτ hng ha0z hbmz ha0 hx0 hy0.
      unfold shuffle_verify, shuffle_prove, shuffle_product_stmt, shuffle_mexp_C; cbn [sh_cA sh_cB sh_prod sh_mexp fst snd]; cbv zeta.
      subst N.
      assert (hpl : length perm = (m * n)%nat) by (rewrite (Permutation_length hperm), seq_length; reflexivity).
      set (a := map fnat perm). set (b := map (fun i => fpow x i) perm).
      set (dz := map (fun p => y * fst p + snd p - z) (combine a b)).
      set (t := ladd (lscale y r) s).
      assert (hal : length a = (m * n)%nat) by (unfold a; rewrite map_length; exact hpl).
      assert (hbl : length b = (m * n)%nat) by (unfold b; rewrite map_length; exact hpl).
      assert (hdz : length dz = (m * n)%nat) by (unfold dz; rewrite map_length, combine_length; lia).
      assert (htl : length t = m) by (unfold t; rewrite ladd_length; unfold SigmaK.lscale; rewrite map_length; lia).
      assert (hdzn : forall i, (i < (m * n)%nat)%nat -> nth i dz zero = y * nth i a zero + nth i b zero - z).
      { intros i hi; unfold dz.
        rewrite (nth_indep (map (fun p => y * fst p + snd p - z) (combine a b)) zero
          ((fun p => y * fst p + snd p - z) (zero, zero))) by (rewrite map_length, combine_length; lia).
        rewrite (map_nth (fun p => y * fst p + snd p - z)), combine_nth by lia; reflexivity. }
      rewrite !com_list_length, !chunk_length, hr, hs, !Nat.min_id.
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split;
        [apply andb_true_iff; split |] |] |] |] |] |].
      + apply Nat.leb_le; exact hm.
      + apply Nat.leb_le; exact hn.
      + apply Nat.eqb_eq; exact hC.
      + apply Nat.eqb_eq; exact hC'.
      + apply Nat.eqb_eq; reflexivity.
      + apply Nat.eqb_eq; reflexivity.
      + (* the product argument *)
        assert (hcD : map (fun c => gop c (com h gs (repeat (opp z) n) zero))
            (map (fun p => gop ((fst p) ^ y) (snd p)) (combine (com_list h gs (chunk n m a) r) (com_list h gs (chunk n m b) s))) =
          com_list h gs (chunk n m dz) t).
        { apply (nth_ext _ _ gid gid).
          - rewrite !map_length, combine_length, !com_list_length, !chunk_length, hr, hs, htl; lia.
          - intros j hj; rewrite !map_length, combine_length, !com_list_length, !chunk_length, hr, hs, Nat.min_id in hj.
            rewrite (nth_indep _ gid ((fun c => gop c (com h gs (repeat (opp z) n) zero)) gid))
              by (rewrite !map_length, combine_length, !com_list_length, !chunk_length, hr, hs; lia).
            rewrite (map_nth (fun c => gop c (com h gs (repeat (opp z) n) zero))).
            rewrite (nth_indep _ gid ((fun p => gop ((fst p) ^ y) (snd p)) (gid, gid)))
              by (rewrite map_length, combine_length, !com_list_length, !chunk_length, hr, hs; lia).
            rewrite (map_nth (fun p => gop ((fst p) ^ y) (snd p))).
            rewrite combine_nth by (rewrite !com_list_length, !chunk_length, hr, hs; reflexivity); cbn [fst snd].
            rewrite (nth_com_list h gs (chunk n m a) r j) by (rewrite chunk_length; lia).
            rewrite (nth_com_list h gs (chunk n m b) s j) by (rewrite chunk_length; lia).
            rewrite (nth_com_list h gs (chunk n m dz) t j) by (rewrite chunk_length; lia).
            rewrite <-com_scale, <-!com_padd.
            f_equal.
            + rewrite !nth_chunk by lia.
              apply (nth_ext _ _ zero zero).
              * rewrite !padd_length, !firstn_length, !skipn_length, repeat_length; unfold SigmaK.lscale;
                rewrite map_length, firstn_length, skipn_length; nia.
              * intros u hu.
                rewrite !padd_length, repeat_length in hu; unfold SigmaK.lscale in hu;
                rewrite map_length, !firstn_length, !skipn_length in hu.
                assert (hun : (u < n)%nat) by nia.
                rewrite nth_firstn_skipn by exact hun.
                rewrite <-!vpadd_padd, !(nth_vpadd (HV := F_vspace)).
                rewrite nth_lscale by (rewrite firstn_length, skipn_length; nia).
                rewrite !nth_firstn_skipn by exact hun.
                rewrite nth_repeat' by exact hun.
                rewrite hdzn by nia; field.
            + unfold t; rewrite nth_ladd by (unfold SigmaK.lscale; rewrite map_length; lia); rewrite nth_lscale by lia; field. }
        rewrite hcD.
        assert (hne : chunk n m dz <> []).
        { intro e; apply (f_equal (@length (list F))) in e; rewrite chunk_length in e; cbn in e; lia. }
        assert (hprod : fold_right mul one (map (fun i => y * fnat i + fpow x i - z) (seq 0 (m * n)%nat)) =
          fold_right mul one (hprefix (chunk n m dz) (length (chunk n m dz) - 1))).
        { rewrite (prod_hprefix_concat n) by (assumption || (apply chunk_forall_length; lia)).
          rewrite concat_chunk by lia.
          unfold dz, a, b; rewrite combine_map_same, map_map.
          apply fold_mul_perm; apply Permutation_map; apply Permutation_sym; exact hperm. }
        rewrite hprod.
        apply product_completeness; rewrite ?chunk_length; try assumption; try lia.
        apply chunk_forall_length; lia.
      + (* the multi-exponentiation argument *)
        set (inner := fold_right add zero (map (fun p => fst p * snd p) (combine ρs b))).
        assert (hmexp : cmexp Cs' b = cmul (enc1 g pk inner) (cmexp Cs (lpows x (m * n)%nat))).
        { rewrite !lmexp_as_fold.
          replace (map (fun p => cpow (fst p) (snd p)) (combine Cs' b)) with
            (map (fun i => cmul (cpow (enc1 g pk (nth i ρs zero)) (fpow x (nth i perm 0%nat)))
                                (cpow (nth (nth i perm 0%nat) Cs cone) (fpow x (nth i perm 0%nat)))) (seq 0 (m * n)%nat)).
          2: { apply (nth_ext _ _ cone cone).
               - rewrite !map_length, seq_length, combine_length; lia.
               - intros i hi; rewrite map_length, seq_length in hi.
                 rewrite nth_map_seq by exact hi.
                 rewrite (nth_indep (map (fun p => cpow (fst p) (snd p)) (combine Cs' b)) cone
                   ((fun p => cpow (fst p) (snd p)) (cone, zero))) by (rewrite map_length, combine_length; lia).
                 rewrite (map_nth (fun p => cpow (fst p) (snd p))), combine_nth by lia; cbn [fst snd].
                 rewrite hrel by exact hi.
                 unfold b; rewrite (nth_indep (map _ perm) zero ((fun i => fpow x i) 0%nat)) by (rewrite map_length; lia).
                 rewrite (map_nth (fun i => fpow x i)).
                 rewrite (vadd_smul (HV := CTvs)); reflexivity. }
          rewrite (fold_map_vadd (HV := CTvs)).
          f_equal.
          - (* the randomness *)
            rewrite (map_ext (fun i => cpow (enc1 g pk (nth i ρs zero)) (fpow x (nth i perm 0%nat)))
              (fun i => enc1 g pk (nth i ρs zero * fpow x (nth i perm 0%nat))))
              by (intro i; rewrite encg_pow; f_equal; field).
            rewrite cprod_enc1; unfold inner; f_equal; f_equal.
            apply (nth_ext _ _ zero zero).
            + rewrite !map_length, seq_length, combine_length; lia.
            + intros i hi; rewrite map_length, seq_length in hi.
              rewrite nth_map_seq by exact hi.
              rewrite (nth_indep (map (fun p => fst p * snd p) (combine ρs b)) zero ((fun p => fst p * snd p) (zero, zero)))
                by (rewrite map_length, combine_length; lia).
              rewrite (map_nth (fun p => fst p * snd p)), combine_nth by lia; cbn [fst snd].
              unfold b; rewrite (nth_indep (map _ perm) zero ((fun i => fpow x i) 0%nat)) by (rewrite map_length; lia).
              rewrite (map_nth (fun i => fpow x i)); reflexivity.
          - (* the permuted product *)
            rewrite (map_nth_seq' (fun j => cpow (nth j Cs cone) (fpow x j)) 0%nat perm (m * n)%nat hpl).
            rewrite (fold_vadd_perm (HV := CTvs) _ _ (Permutation_map _ hperm)).
            f_equal; rewrite lpows_map.
            apply (nth_ext _ _ cone cone).
            + rewrite !map_length, combine_length, map_length, !seq_length; lia.
            + intros j hj; rewrite map_length, seq_length in hj.
              rewrite nth_map_seq by exact hj.
              rewrite (nth_indep (map (fun p => cpow (fst p) (snd p)) (combine Cs (map (fpow x) (seq 0 (m * n)%nat)))) cone
                ((fun p => cpow (fst p) (snd p)) (cone, zero)))
                by (rewrite map_length, combine_length, map_length, seq_length; lia).
              rewrite (map_nth (fun p => cpow (fst p) (snd p))), combine_nth by (rewrite map_length, seq_length; lia); cbn [fst snd].
              rewrite (nth_indep (map _ (seq 0 (m * n)%nat)) zero ((fun i => fpow x i) 0%nat)) by (rewrite map_length, seq_length; lia).
              rewrite (map_nth (fun i => fpow x i)), seq_nth by exact hj; reflexivity. }
        assert (hC0 : cmexp Cs (lpows x (m * n)%nat) =
          cmul (enc g pk (Vector.const gid l) (opp inner))
            (cprod (map (fun p => cmexp (snd p) (nth (fst p) (chunk n m b) [])) (combine (seq 0 (length (chunk n m b))) (chunk n m Cs'))))).
        { rewrite chunk_length, cmexp_chunks by lia; rewrite hmexp, <-enc1_ones, (vadd_assoc (HV := CTvs)), encg_mul.
          replace (zero + zero) with zero by field; replace (opp inner + inner) with zero by field.
          rewrite encg_zero_zero, (vadd_vid_l (HV := CTvs)); reflexivity. }
        rewrite hC0.
        apply multiexp_completeness; rewrite ?chunk_length; try lia.
        constructor; [lia | rewrite <-hng; apply chunk_forall_length; lia].
    Qed.

  End Shuffle.

End BayerGroth.
