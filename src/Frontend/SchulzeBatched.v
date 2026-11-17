(** * Receipt-free Schulze ballots, version 2: the batched ballot

    This file formalises a batched voter protocol for the receipt-free
    Schulze ballot of [Frontend/Schulze.v]. The published content that the
    tally consumes is the same: the [m²] exponential-ElGamal ciphertexts
    [c_k = Enc(b_k)] of the pairwise preference bits [b_(i,j) = [s_i < s_j] ]
    of a ranking, laid out row-major ([k = i·m + j]). Instead of one
    disjunctive proof per cell, the voter publishes Pedersen vector
    commitments (with keys [h1], [gs1] of length [K = m²] and [gs2] of
    length [NX = L·K]) to

    - the position vector [s] (length [m]), as [C_s];
    - the differences [δ_(i,j) = s_j - s_i], as [C_δ];
    - the bits [b], as [C_b];
    - the products [p = b ∘ δ] (Hadamard product), as [C_p];
    - the [L]-bit binary decompositions [X] of [v = -δ + 2p - b], as [C_X].
      Note that [v_(i,j) = s_i - s_j ≥ 0] when [b_(i,j) = 0] and
      [v_(i,j) = s_j - s_i - 1 ≥ 0] when [b_(i,j) = 1], so [v] is a
      natural number exactly when [b] is consistent with [s].

    and four Sigma-style arguments:

    - a linear-relation proof ([Crypto/LinearSigma.v]) for a linear map
      [phi] into [G^7 × F^2]: the commitments open to the witness
      vectors; the ciphertexts combined with random coefficients [β],
      [∏_k c_k ^ β_k], encrypt [⟨β, b⟩]; and two random linear
      combinations (coefficients [γ₁], [γ₂]) of the scalar equations
      [δ = M s] and [Σ_t 2^t X^(t) + δ - 2p + b = 0] vanish;
    - a Bayer–Groth zero argument ([Crypto/BayerGroth.v]; Bayer and Groth,
      EUROCRYPT 2012) with rows [(b, p)] against [(δ, -1)], showing
      [p = b ∘ δ];
    - a zero argument with row [X] against [X - 1], showing every entry of
      [X] is a bit;
    - a zero argument with row [b] against [b - 1], showing every [b_k] is
      a bit.

    Compared with version 1 (one disjunctive proof per cell, about [2m³]
    branches in total) the cost is [O(m² log m)] exponentiations and
    [O(m²)] field elements; at [m = 17] the ballot shrinks from about 6 MB
    to about 350 KB. The price is extra assumptions: the binding of the
    Pedersen keys (soundness is stated as ‘the keys are broken or the
    ballot encodes a ranking’), and for zero knowledge the commitment keys
    must have known discrete logarithms in base [h1].

    _Results._

    - Completeness: [ballot2_valid] (challenges given) and
      [nizk_ballot2_valid] (Fiat–Shamir: all ten challenges derived by
      hashing with domain-separation tags; three prover passes).
    - Special soundness: [ballot2_sound] is stated for a rewinding family
      of accepting transcripts rather than for two transcripts: a base
      tuple of coefficients [β], [γ₁], [γ₂] and, for every coordinate, a
      tuple differing in that coordinate alone, all accepted by the linear
      proof at two challenges; and the zero arguments accepted at [K]
      (resp. [NX]) distinct non-zero [y], each at [2r + 1] challenges [x].
      The conclusion is a binding break of [gs1] or [gs2], or positions
      [pos_i ≤ 2 · 2^L] with every ciphertext decrypting to
      [g ^ [pos_i < pos_j] ]. Hypotheses: [h = g ^ x], [L ≥ 1] and the
      characteristic of [F] exceeds [3 · 2^L + 2].
    - Special honest-verifier zero knowledge: [ballot2_zk]. The honest
      ballot (over uniform voter randomness) is a permutation of a
      simulator's output given the ciphertexts and the challenges only.

    The aggregation and the tally reuse [Frontend/Schulze.v] via
    [ballot2_bits]; the end-to-end theorem is in
    [Backend/SchulzeBatchedTally.v]. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List Arith PeanoNat
  RelationClasses Morphisms.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space Product_space.
From Crypto Require Import Sigma MultiExp SigmaK PolyRoots BayerGroth BayerGrothSound BayerGrothZK LinearSigma Elgamal.
From Frontend Require Import Schulze.
From Utility Require Import Util.
Import ListNotations.

(** ** Parameters and the statement space

    The field [F] and the group [G] form a vector space ([Hvec]). The local
    notations instantiate the generic list operations ([lscale], [ladd],
    [fsum]), multi-exponentiation [gmexp], Pedersen commitment
    [com h gs a r = h ^ r · ∏_i gs_i ^ a_i], the weighted star product
    [star y a b = Σ_j a_j b_j y ^ (j+1)] and the zero argument of
    [Crypto/BayerGroth.v], and the ciphertext algebra of
    [Frontend/Schulze.v]. The group laws are taken by name from
    [Frontend/Schulze.v] with [Hvec] explicit, because the global instances
    of [Algebra/Product_space.v] make typeclass search unreliable. *)
Section SchulzeBatched.

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

  Local Notation gop_assoc := (gop_assoc (Hvec := Hvec)).
  Local Notation gop_comm := (gop_comm (Hvec := Hvec)).
  Local Notation gop_gid_l := (gop_gid_l (Hvec := Hvec)).
  Local Notation gop_gid_r := (gop_gid_r (Hvec := Hvec)).
  Local Notation pow_add := (pow_add (Hvec := Hvec)).
  Local Notation pow_mul := (pow_mul (Hvec := Hvec)).
  Local Notation pow_zero := (pow_zero (Hvec := Hvec)).
  Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
  Local Notation gop_rearrange := (gop_rearrange (Hvec := Hvec)).
  Local Notation enc_mul := (enc_mul (Hvec := Hvec)).
  Local Notation enc_pow := (enc_pow (Hvec := Hvec)).
  Local Notation com_add := (com_add (Hvec := Hvec)).
  Local Notation com_scale := (com_scale (Hvec := Hvec)).

  (** *** [F] as a vector space over itself

      The commutative-group and module laws of [(F, +)] with scalar
      multiplication [mul], needed to form the statement space
      [G^7 × F^2] of the linear proof. *)
  Lemma Fv_add_assoc : forall x y z : F, x + (y + z) = (x + y) + z. Proof. intros; field. Qed.
  Lemma Fv_add_id_l : forall x : F, zero + x = x. Proof. intros; field. Qed.
  Lemma Fv_add_id_r : forall x : F, x + zero = x. Proof. intros; field. Qed.
  Lemma Fv_add_opp_l : forall x : F, opp x + x = zero. Proof. intros; field. Qed.
  Lemma Fv_add_opp_r : forall x : F, x + opp x = zero. Proof. intros; field. Qed.
  Lemma Fv_add_comm : forall x y : F, x + y = y + x. Proof. intros; field. Qed.
  Lemma Fv_add_proper : Proper (eq ==> eq ==> eq) add. Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Fv_opp_proper : Proper (eq ==> eq) opp. Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Fv_mul_proper : Proper (eq ==> eq ==> eq) mul. Proof. repeat intro; subst; reflexivity. Qed.
  Lemma Fv_mul_one_r : forall x : F, x * one = x. Proof. intros; field. Qed.
  Lemma Fv_mul_zero_r : forall x : F, x * zero = zero. Proof. intros; field. Qed.
  Lemma Fv_mul_assoc : forall (r1 r2 x : F), x * (r1 * r2) = (x * r1) * r2. Proof. intros; field. Qed.
  Lemma Fv_mul_fadd : forall (r1 r2 x : F), x * (r1 + r2) = x * r1 + x * r2. Proof. intros; field. Qed.
  Lemma Fv_mul_vadd : forall (r x y : F), (x + y) * r = x * r + y * r. Proof. intros; field. Qed.

  (** The additive monoid, group and commutative group of [F], and [F]
      as a vector space over itself. *)
  Definition Fv_monoid : @monoid F (@eq F) add zero :=
    @Build_monoid F (@eq F) add zero Fv_add_assoc Fv_add_id_l Fv_add_id_r Fv_add_proper eq_equivalence.
  Definition Fv_group : @group F (@eq F) add zero opp :=
    @Build_group F (@eq F) add zero opp Fv_monoid Fv_add_opp_l Fv_add_opp_r Fv_opp_proper.
  Definition Fv_comm_group : @commutative_group F (@eq F) add zero opp :=
    @Build_commutative_group F (@eq F) add zero opp Fv_group Fv_add_comm.
  Definition F_vspace :
    @vector_space F (@eq F) zero one add mul sub div opp inv F (@eq F) zero opp add mul :=
    @Build_vector_space F (@eq F) zero one add mul sub div opp inv F (@eq F) zero opp add mul
      Fv_comm_group (@vector_space_field _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hvec)
      Fv_mul_one_r Fv_mul_zero_r Fv_mul_assoc Fv_mul_fadd Fv_mul_vadd Fv_mul_proper.

  (** The statement space [St = G^7 × F^2] of the linear proof, with its
      componentwise vector-space structure [st_vspace] and decidable
      equality [st_dec]. *)
  Definition G7vs := vec_vspace (HV := Hvec) 7.
  Definition F2vs := vec_vspace (HV := F_vspace) 2.
  Definition St : Type := (Vector.t G 7 * Vector.t F 2)%type.
  Definition st_id : St := Product_space.pid (vid1 := vec_id (vid := gid) 7) (vid2 := vec_id (vid := zero) 2).
  Definition st_opp : St -> St :=
    Product_space.popp (vopp1 := vec_opp (vopp := ginv)) (vopp2 := vec_opp (vopp := opp)).
  Definition st_add : St -> St -> St :=
    Product_space.padd (vadd1 := vec_add (vadd := gop)) (vadd2 := vec_add (vadd := add)).
  Definition st_smul : St -> F -> St :=
    Product_space.psmul (smul1 := vec_smul (smul := gpow)) (smul2 := vec_smul (smul := mul)).
  Definition st_vspace : @vector_space F (@eq F) zero one add mul sub div opp inv St (@eq St)
    st_id st_opp st_add st_smul := prod_vspace (H1 := G7vs) (H2 := F2vs).
  Definition st_dec : forall x y : St, {x = y} + {x <> y} :=
    prod_dec (vec_dec Gdec (n := 7)) (vec_dec Fdec (n := 2)).

  (** Constructors for vectors of length 7 and 2. *)
  Definition vec7 (a b c d e f k : G) : Vector.t G 7 :=
    Vector.cons G a 6 (Vector.cons G b 5 (Vector.cons G c 4 (Vector.cons G d 3
      (Vector.cons G e 2 (Vector.cons G f 1 (Vector.cons G k 0 (Vector.nil G))))))).
  Definition vec2 (a b : F) : Vector.t F 2 := Vector.cons F a 1 (Vector.cons F b 0 (Vector.nil F)).

  (** The linear-relation Sigma protocol of [Crypto/LinearSigma.v] over
      [St]: announcement [phi a], response [a + c·w], verification
      [phi z = A + c·T]. *)
  Local Notation lin_proof := (@lin_proof F St).
  Local Notation lin_verify := (lin_verify (vadd := st_add) (smul := st_smul) (Vdec := st_dec)).
  Local Notation lin_prove := (lin_prove (add := add) (mul := mul)).

  (** *** Scalar helpers *)

  (** [fsum] is additive. *)
  Lemma fsum_add : forall (f g : nat -> F) (k : nat),
    fsum (fun i => f i + g i) k = fsum f k + fsum g k.
  Proof. intros f g k; induction k as [| k ih]; cbn [SigmaK.fsum]; [field | rewrite ih; field]. Qed.

  (** [fsum] commutes with scaling. *)
  Lemma fsum_scale : forall (c : F) (f : nat -> F) (k : nat),
    fsum (fun i => c * f i) k = c * fsum f k.
  Proof. intros c f k; induction k as [| k ih]; cbn [SigmaK.fsum]; [field | rewrite ih; field]. Qed.

  (** [dot u v k] is the inner product of [u] and [v] over the first [k]
      entries. *)
  Definition dot (u v : list F) (k : nat) : F := fsum (fun i => nth i u zero * nth i v zero) k.

  (** Lengths and entries of [lscale] and [ladd], and out-of-range [nth]. *)
  Lemma lscale_length : forall c xs, length (lscale c xs) = length xs.
  Proof. intros; unfold SigmaK.lscale; apply map_length. Qed.
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
  Lemma nth_overflow_F : forall (xs : list F) i, (length xs <= i)%nat -> nth i xs zero = zero.
  Proof. intros; apply nth_overflow; assumption. Qed.

  (** ** The batched ballot

      The section fixes the number of candidates [m = n + 1], the bit
      length [L] of the differences, the election key [(g, h)] and the
      commitment key [(h1, gs1, gs2)]. *)
  Section Ballot2.

    Context {n : nat} (L : nat) (g h h1 : G) (gs1 gs2 : list G).
    Local Notation m := (S n).

    (** [K = m²] cells and [NX = L·K] bits. *)
    Definition K : nat := (m * m)%nat.
    Definition NX : nat := (L * K)%nat.
    (** Layout of the witness of the linear proof, a flat list of length
        [W]: [s] at [oS], [δ] at [oD], [b] at [oB], [p] at [oP], [X] at
        [oX], then six scalars at [oR]: the commitment randomness
        [ρ_s, ρ_δ, ρ_b, ρ_p, ρ_X] and the combined encryption randomness
        [R = ⟨β, r⟩]. *)
    Definition oS : nat := 0.
    Definition oD : nat := m.
    Definition oB : nat := (m + K)%nat.
    Definition oP : nat := (m + 2 * K)%nat.
    Definition oX : nat := (m + 3 * K)%nat.
    Definition oR : nat := (m + 3 * K + NX)%nat.
    Definition W : nat := (oR + 6)%nat.

    (** [wslice w off len] is the sub-list of [w] at [off] of length [len];
        [wat w i] is the [i]-th entry. *)
    Definition wslice (w : list F) (off len : nat) : list F :=
      map (fun i => nth (off + i) w zero) (seq 0 len).
    Definition wat (w : list F) (i : nat) : F := nth i w zero.

    (** [pow2F t = 2^t] in [F]; [vbits X k = Σ_(t<L) 2^t · X(t·K + k)] is
        the value encoded by the bits of cell [k] (the bit vectors
        [X^(t)] are stored consecutively, [X^(t)_k] at [t·K + k]). *)
    Definition pow2F (t : nat) : F := natF (Nat.pow 2 t).
    Definition vbits (X : list F) (k : nat) : F := fsum (fun t => pow2F t * nth (t * K + k) X zero) L.

    (** The linear map of the linear proof, as a function of the witness
        [w], parametrised by the challenge coefficients [β], [γ₁], [γ₂]:
[[
      ( com(s; ρ_s), com(δ; ρ_δ), com(b; ρ_b), com(p; ρ_p), com_gs2(X; ρ_X),
        g ^ R,  g ^ ⟨β, b⟩ · h ^ R ;
        Σ_k γ₁_k (δ_k - (s_(k mod m) - s_(k / m))),
        Σ_k γ₂_k (vbits X k + δ_k - 2 p_k + b_k) )
]]
        Cell [k] is the pair [(k / m, k mod m)]. *)
    Definition phi (beta g1 g2 : list F) (w : list F) : St :=
      (vec7 (com h1 gs1 (wslice w oS m) (wat w oR))
            (com h1 gs1 (wslice w oD K) (wat w (oR + 1)))
            (com h1 gs1 (wslice w oB K) (wat w (oR + 2)))
            (com h1 gs1 (wslice w oP K) (wat w (oR + 3)))
            (com h1 gs2 (wslice w oX NX) (wat w (oR + 4)))
            (g ^ wat w (oR + 5))
            (gop (g ^ dot beta (wslice w oB K) K) (h ^ wat w (oR + 5))),
       vec2 (fsum (fun k => nth k g1 zero *
                (wat w (oD + k) - (wat w (oS + k mod m) - wat w (oS + k / m)))) K)
            (fsum (fun k => nth k g2 zero *
                (vbits (wslice w oX NX) k + wat w (oD + k) - (one + one) * wat w (oP + k) + wat w (oB + k))) K)).

    (** [cbeta β cs = ∏_k cs_k ^ β_k], the random linear combination of
        the ciphertexts. *)
    Definition cbeta (beta : list F) (cs : list (G * G)) : G * G :=
      lmexp (vid := cid) (vadd := cmul) (smul := cpow) cs beta.

    (** [cneg gs len = com_gs(-1, …, -1; 0)], used to commit to the
        constant vectors [-1] in the zero arguments. *)
    Definition cneg (gs : list G) (len : nat) : G := com h1 gs (repeat (opp one) len) zero.

    (** A batched ballot: the [K] ciphertexts, the five commitments, the
        linear proof and three zero arguments. *)
    Record ballot2 : Type := mk_ballot2 {
      b2_cs : list (G * G);
      b2_Cs : G; b2_Cd : G; b2_Cb : G; b2_Cp : G; b2_CX : G;
      b2_lin : lin_proof;
      b2_z1 : zero_argument;
      b2_z2 : zero_argument;
      b2_z3 : zero_argument }.

    (** The challenges: coefficient vectors [β], [γ₁], [γ₂] (length [K]
        each), the linear-proof challenge [c], and the pair [(y, x)] for
        each zero argument. *)
    Record chal2 : Type := mk_chal2 {
      ch_beta : list F; ch_g1 : list F; ch_g2 : list F; ch_c : F;
      ch_y1 : F; ch_x1 : F; ch_y2 : F; ch_x2 : F; ch_y3 : F; ch_x3 : F }.

    (** The statement of the linear proof read off the ballot: the five
        commitments, the combined ciphertext [cbeta β cs], and zeros for
        the two scalar rows. *)
    Definition target (beta : list F) (bt : ballot2) : St :=
      let cb := cbeta beta (b2_cs bt) in
      (vec7 (b2_Cs bt) (b2_Cd bt) (b2_Cb bt) (b2_Cp bt) (b2_CX bt) (fst cb) (snd cb), vec2 zero zero).

    (** The interactive verifier: [K] ciphertexts, the linear proof
        accepts [target] under [phi], and the three zero arguments accept
        ([C_b, C_p] against [C_δ, com(-1)]; [C_X] against [C_X · com(-1)];
        [C_b] against [C_b · com(-1)]). *)
    Definition verify_ballot2 (ch : chal2) (bt : ballot2) : bool :=
      (Nat.eqb (length (b2_cs bt)) K) &&
      lin_verify W (phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch)) (target (ch_beta ch) bt) (ch_c ch) (b2_lin bt) &&
      zero_verify h1 gs1 [b2_Cb bt; b2_Cp bt] [b2_Cd bt; cneg gs1 K] (ch_y1 ch) (ch_x1 ch) (b2_z1 bt) &&
      zero_verify h1 gs2 [b2_CX bt] [gop (b2_CX bt) (cneg gs2 NX)] (ch_y2 ch) (ch_x2 ch) (b2_z2 bt) &&
      zero_verify h1 gs1 [b2_Cb bt] [gop (b2_Cb bt) (cneg gs1 K)] (ch_y3 ch) (ch_x3 ch) (b2_z3 bt).

    (** The ciphertexts as the [m × m] matrix of [Frontend/Schulze.v], for
        aggregation by [aggregate_margins]. *)
    Definition ballot2_bits (bt : ballot2) : Vector.t (Vector.t (G * G) m) m :=
      Vector.map (fun i => Vector.map (fun j =>
        nth (fin_idx i * m + fin_idx j) (b2_cs bt) cid) (fin_enum m)) (fin_enum m).

    (** *** The honest voter

        Positions are given as a list [sn] of [m] natural numbers. *)

    (** [pos_bit sn k = [s_(k/m) < s_(k mod m)] ]; [pos_v sn k] is the
        natural number [v_k] ([s_j - s_i - 1] or [s_i - s_j]); [bit v t] is
        bit [t] of [v]. *)
    Definition pos_bit (sn : list nat) (k : nat) : nat :=
      if Nat.ltb (nth (k / m) sn 0) (nth (k mod m) sn 0) then 1 else 0.
    Definition pos_v (sn : list nat) (k : nat) : nat :=
      let si := nth (k / m) sn 0 in let sj := nth (k mod m) sn 0 in
      if Nat.ltb si sj then (sj - si - 1)%nat else (si - sj)%nat.
    Definition bit (v t : nat) : nat := ((v / Nat.pow 2 t) mod 2)%nat.

    (** The honest witness vectors [s], [δ], [b], [p = b ∘ δ] and [X]
        (with [X^(t)_k] at [t·K + k]) as field elements. *)
    Definition hon_s (sn : list nat) : list F := map natF sn.
    Definition hon_d (sn : list nat) : list F :=
      map (fun k => natF (nth (k mod m) sn 0) - natF (nth (k / m) sn 0)) (seq 0 K).
    Definition hon_b (sn : list nat) : list F := map (fun k => natF (pos_bit sn k)) (seq 0 K).
    Definition hon_p (sn : list nat) : list F := hmul (hon_b sn) (hon_d sn).
    Definition hon_X (sn : list nat) : list F :=
      map (fun u => natF (bit (pos_v sn (u mod K)) (u / K))) (seq 0 NX).

    (** The voter's randomness: encryption randomness [rd_r] ([K] values),
        commitment randomness [rd_rs … rd_rX], the announcement randomness
        [rd_a] of the linear proof, and the prover randomness of the three
        zero arguments ([rd_a1 … rd_u3], in the layout of [zero_prove]). *)
    Record rand2 : Type := mk_rand2 {
      rd_r : list F;
      rd_rs : F; rd_rd : F; rd_rb : F; rd_rp : F; rd_rX : F;
      rd_a : list F;
      rd_a1 : list F; rd_b1 : list F; rd_r1 : F; rd_s1 : F; rd_t1 : list F; rd_u1 : list F;
      rd_a2 : list F; rd_b2 : list F; rd_r2 : F; rd_s2 : F; rd_t2 : list F; rd_u2 : list F;
      rd_a3 : list F; rd_b3 : list F; rd_r3 : F; rd_s3 : F; rd_t3 : list F; rd_u3 : list F }.

    (** The honest ciphertexts [Enc(pos_bit sn k; r_k)]. *)
    Definition hon_cs (sn : list nat) (rd : rand2) : list (G * G) :=
      map (fun k => enc g h (natF (pos_bit sn k)) (nth k (rd_r rd) zero)) (seq 0 K).

    (** The honest witness of the linear proof, in the layout above, with
        [R = ⟨β, r⟩]. *)
    Definition hon_w (beta : list F) (sn : list nat) (rd : rand2) : list F :=
      hon_s sn ++ hon_d sn ++ hon_b sn ++ hon_p sn ++ hon_X sn ++
      [rd_rs rd; rd_rd rd; rd_rb rd; rd_rp rd; rd_rX rd; dot beta (rd_r rd) K].

    (** [encrypt_ballot2 ch sn rd] computes the ballot for positions [sn]
        under challenges [ch] (interactive form). *)
    Definition encrypt_ballot2 (ch : chal2) (sn : list nat) (rd : rand2) : ballot2 :=
      let beta := ch_beta ch in
      mk_ballot2 (hon_cs sn rd)
        (com h1 gs1 (hon_s sn) (rd_rs rd)) (com h1 gs1 (hon_d sn) (rd_rd rd))
        (com h1 gs1 (hon_b sn) (rd_rb rd)) (com h1 gs1 (hon_p sn) (rd_rp rd))
        (com h1 gs2 (hon_X sn) (rd_rX rd))
        (lin_prove (phi beta (ch_g1 ch) (ch_g2 ch)) (hon_w beta sn rd) (rd_a rd) (ch_c ch))
        (zero_prove h1 gs1 [hon_b sn; hon_p sn] [hon_d sn; repeat (opp one) K]
          [rd_rb rd; rd_rp rd] [rd_rd rd; zero] (ch_y1 ch)
          (rd_a1 rd) (rd_b1 rd) (rd_r1 rd) (rd_s1 rd) (rd_t1 rd) (rd_u1 rd) (ch_x1 ch))
        (zero_prove h1 gs2 [hon_X sn] [ladd (hon_X sn) (repeat (opp one) NX)]
          [rd_rX rd] [rd_rX rd] (ch_y2 ch)
          (rd_a2 rd) (rd_b2 rd) (rd_r2 rd) (rd_s2 rd) (rd_t2 rd) (rd_u2 rd) (ch_x2 ch))
        (zero_prove h1 gs1 [hon_b sn] [ladd (hon_b sn) (repeat (opp one) K)]
          [rd_rb rd] [rd_rb rd] (ch_y3 ch)
          (rd_a3 rd) (rd_b3 rd) (rd_r3 rd) (rd_s3 rd) (rd_t3 rd) (rd_u3 rd) (ch_x3 ch)).

    (** *** Linearity of [phi]

        [lin_completeness] and [lin_soundness] require [phi] to be a
        homomorphism on witnesses of length [W]. The lemmas below
        distribute slicing, inner products and [vbits] over [ladd] and
        [lscale]. *)

    (** Length and entries of [wslice]. *)
    Lemma wslice_length : forall w off len, length (wslice w off len) = len.
    Proof. intros; unfold wslice; rewrite map_length, seq_length; reflexivity. Qed.

    Lemma nth_wslice : forall w off len i, (i < len)%nat -> nth i (wslice w off len) zero = nth (off + i) w zero.
    Proof. intros; unfold wslice; rewrite nth_map_seq by assumption; reflexivity. Qed.

    (** Slicing distributes over addition and scaling of witnesses. *)
    Lemma wslice_ladd : forall w w' off len, length w = W -> length w' = W -> (off + len <= W)%nat ->
      wslice (ladd w w') off len = ladd (wslice w off len) (wslice w' off len).
    Proof.
      intros * hw hw' hl; unfold wslice.
      rewrite ladd_map; apply map_ext_in; intros i hi; apply in_seq in hi.
      apply nth_ladd; [lia | lia].
    Qed.

    Lemma wslice_lscale : forall c w off len, length w = W -> (off + len <= W)%nat ->
      wslice (lscale c w) off len = lscale c (wslice w off len).
    Proof.
      intros * hw hl; unfold wslice.
      rewrite lscale_map; apply map_ext_in; intros i hi; apply in_seq in hi.
      apply nth_lscale; lia.
    Qed.

    (** Entries distribute over addition and scaling of witnesses. *)
    Lemma wat_ladd : forall w w' i, length w = W -> length w' = W -> (i < W)%nat ->
      wat (ladd w w') i = wat w i + wat w' i.
    Proof. intros; unfold wat; apply nth_ladd; lia. Qed.

    Lemma wat_lscale : forall c w i, length w = W -> (i < W)%nat -> wat (lscale c w) i = c * wat w i.
    Proof. intros; unfold wat; apply nth_lscale; lia. Qed.

    (** [dot β] is linear. *)
    Lemma dot_ladd : forall beta u v k, length u = k -> length v = k ->
      dot beta (ladd u v) k = dot beta u k + dot beta v k.
    Proof.
      intros * hu hv; unfold dot; rewrite <-fsum_add; apply fsum_ext; intros i hi.
      rewrite nth_ladd by lia; field.
    Qed.

    Lemma dot_lscale : forall beta c u k, length u = k -> dot beta (lscale c u) k = c * dot beta u k.
    Proof.
      intros * hu; unfold dot; rewrite <-fsum_scale; apply fsum_ext; intros i hi.
      rewrite nth_lscale by lia; field.
    Qed.

    (** [vbits] is linear. *)
    Lemma vbits_ladd : forall X X' k, length X = NX -> length X' = NX ->
      vbits (ladd X X') k = vbits X k + vbits X' k.
    Proof.
      intros * hX hX'; unfold vbits; rewrite <-fsum_add; apply fsum_ext; intros t ht.
      destruct (Nat.lt_ge_cases (t * K + k) NX) as [hlt | hge].
      + rewrite nth_ladd by lia; field.
      + rewrite !nth_overflow_F by (try rewrite ladd_length; lia); field.
    Qed.

    Lemma vbits_lscale : forall c X k, length X = NX -> vbits (lscale c X) k = c * vbits X k.
    Proof.
      intros * hX; unfold vbits; rewrite <-fsum_scale; apply fsum_ext; intros t ht.
      destruct (Nat.lt_ge_cases (t * K + k) NX) as [hlt | hge].
      + rewrite nth_lscale by lia; field.
      + rewrite !nth_overflow_F by (try rewrite lscale_length; lia); field.
    Qed.

    (** All slices of the layout fit in [W]. *)
    Lemma W_offsets : (oS + m <= W /\ oD + K <= W /\ oB + K <= W /\ oP + K <= W /\ oX + NX <= W /\ oR + 5 < W)%nat.
    Proof. unfold W, oR, oX, oP, oB, oD, oS; lia. Qed.

    (** For [k < K], [k / m] and [k mod m] are candidate indices. *)
    Lemma kdm_lt : forall k, (k < K)%nat -> (k / m < m)%nat /\ (k mod m < m)%nat.
    Proof.
      intros k hk; unfold K in hk; split.
      + apply Nat.Div0.div_lt_upper_bound; lia.
      + apply Nat.mod_upper_bound; lia.
    Qed.

    (** Componentwise addition and scaling of [vec7] and [vec2]. *)
    Lemma vec_add7 : forall a b c d e f k a' b' c' d' e' f' k',
      vec_add (vadd := gop) (vec7 a b c d e f k) (vec7 a' b' c' d' e' f' k') =
      vec7 (gop a a') (gop b b') (gop c c') (gop d d') (gop e e') (gop f f') (gop k k').
    Proof. reflexivity. Qed.
    Lemma vec_add2 : forall a b a' b', vec_add (vadd := add) (vec2 a b) (vec2 a' b') = vec2 (a + a') (b + b').
    Proof. reflexivity. Qed.
    Lemma vec_smul7 : forall a b c d e f k x,
      vec_smul (smul := gpow) (vec7 a b c d e f k) x = vec7 (a ^ x) (b ^ x) (c ^ x) (d ^ x) (e ^ x) (f ^ x) (k ^ x).
    Proof. reflexivity. Qed.
    Lemma vec_smul2 : forall a b x, vec_smul (smul := mul) (vec2 a b) x = vec2 (a * x) (b * x).
    Proof. reflexivity. Qed.
    (** Commutativity of [mul] and [u ^ (c a) = (u ^ a) ^ c]. *)
    Lemma Fmul_comm : forall a b : F, a * b = b * a. Proof. intros; field. Qed.
    Lemma pow_cmul : forall (u : G) (a c : F), u ^ (c * a) = (u ^ a) ^ c.
    Proof. intros; replace (c * a) with (a * c) by field; apply pow_mul. Qed.

    (** [phi] is additive on witnesses of length [W]. *)
    Lemma phi_add : forall beta g1 g2 w w', length w = W -> length w' = W ->
      phi beta g1 g2 (ladd w w') = st_add (phi beta g1 g2 w) (phi beta g1 g2 w').
    Proof.
      intros * hw hw'; destruct W_offsets as (ho1 & ho2 & ho3 & ho4 & ho5 & ho6).
      unfold phi, st_add, Product_space.padd; cbn [fst snd]; rewrite vec_add7, vec_add2.
      rewrite !wslice_ladd by lia. rewrite !wat_ladd by lia. rewrite !dot_ladd by apply wslice_length.
      rewrite !com_add by (rewrite !wslice_length; reflexivity). rewrite !pow_add.
      f_equal.
      + f_equal. apply gop_rearrange.
      + f_equal.
        * rewrite <-fsum_add; apply fsum_ext; intros k hk; pose proof (kdm_lt k hk).
          rewrite !wat_ladd by lia; field.
        * rewrite <-fsum_add; apply fsum_ext; intros k hk; pose proof (kdm_lt k hk).
          rewrite vbits_ladd by apply wslice_length; rewrite !wat_ladd by lia; field.
    Qed.

    (** [phi] commutes with scaling on witnesses of length [W]. *)
    Lemma phi_scale : forall beta g1 g2 c w, length w = W ->
      phi beta g1 g2 (lscale c w) = st_smul (phi beta g1 g2 w) c.
    Proof.
      intros * hw; destruct W_offsets as (ho1 & ho2 & ho3 & ho4 & ho5 & ho6).
      unfold phi, st_smul, Product_space.psmul; cbn [fst snd]; rewrite vec_smul7, vec_smul2.
      rewrite !wslice_lscale by lia. rewrite !wat_lscale by lia. rewrite !dot_lscale by apply wslice_length.
      rewrite !com_scale, !pow_cmul.
      f_equal.
      + f_equal. rewrite gop_pow; reflexivity.
      + f_equal.
        * rewrite (Fmul_comm (fsum _ _) c), <-fsum_scale; apply fsum_ext; intros k hk; pose proof (kdm_lt k hk).
          rewrite !wat_lscale by lia; field.
        * rewrite (Fmul_comm (fsum _ _) c), <-fsum_scale; apply fsum_ext; intros k hk; pose proof (kdm_lt k hk).
          rewrite vbits_lscale by apply wslice_length; rewrite !wat_lscale by lia; field.
    Qed.

    (** *** Completeness *)

    (** [K > 0]. *)
    Lemma K_pos : (0 < K)%nat.
    Proof. unfold K; lia. Qed.

    (** [fsum] peeled at the front. *)
    Lemma fsum_shift : forall (f : nat -> F) k, fsum f (S k) = f 0%nat + fsum (fun i => f (S i)) k.
    Proof.
      intros f k; revert f; induction k as [| k ih]; intros f; [cbn [SigmaK.fsum]; field |].
      change (fsum f (S (S k))) with (fsum f (S k) + f (S k)). rewrite ih.
      change (fsum (fun i => f (S i)) (S k)) with (fsum (fun i => f (S i)) k + f (S k)). field.
    Qed.

    (** [cid] is the encryption of [0] with randomness [0]. *)
    Lemma cid_enc : cid = enc g h zero zero.
    Proof. unfold Schulze.cid, Elgamal.enc; rewrite !pow_zero, gop_gid_l; reflexivity. Qed.

    (** Homomorphic multi-exponentiation:
        [∏_i Enc(m_i; r_i) ^ β_i = Enc(Σ β_i m_i; Σ β_i r_i)]. *)
    Lemma lmexp_enc : forall (mf rf : nat -> F) (k st : nat) (beta : list F), length beta = k ->
      lmexp (vid := cid) (vadd := cmul) (smul := cpow)
        (map (fun i => enc g h (mf i) (rf i)) (seq st k)) beta =
      enc g h (fsum (fun i => nth i beta zero * mf (st + i)%nat) k)
              (fsum (fun i => nth i beta zero * rf (st + i)%nat) k).
    Proof.
      intros mf rf k; induction k as [| k ih]; intros st beta hb.
      + destruct beta; [| discriminate]. cbn [seq map]. simpl. rewrite cid_enc. reflexivity.
      + destruct beta as [| b0 beta]; [discriminate |].
        cbn [seq map]. rewrite lmexp_cons. rewrite ih by (cbn in hb; lia).
        rewrite enc_pow, enc_mul.
        assert (e1 : forall (f : nat -> F), fsum (fun i => nth i (b0 :: beta) zero * f (st + i)%nat) (S k) =
          b0 * f st + fsum (fun i => nth i beta zero * f (S st + i)%nat) k).
        { intros f; rewrite fsum_shift; cbn [nth]; rewrite Nat.add_0_r; f_equal.
          apply fsum_ext; intros i hi; f_equal; f_equal; lia. }
        rewrite !e1. apply enc_ext; field.
    Qed.

    (** Entries of the honest witness vectors. *)
    Lemma nth_hon_b : forall sn k, (k < K)%nat -> nth k (hon_b sn) zero = natF (pos_bit sn k).
    Proof. intros; unfold hon_b; rewrite nth_map_seq by assumption; reflexivity. Qed.
    Lemma nth_hon_d : forall sn k, (k < K)%nat ->
      nth k (hon_d sn) zero = natF (nth (k mod m) sn 0) - natF (nth (k / m) sn 0).
    Proof. intros; unfold hon_d; rewrite nth_map_seq by assumption; reflexivity. Qed.
    Lemma nth_hon_s : forall sn i, (i < length sn)%nat -> nth i (hon_s sn) zero = natF (nth i sn 0).
    Proof.
      intros; unfold hon_s; change (nth i (map natF sn) zero) with (nth i (map natF sn) (natF 0)); apply map_nth.
    Qed.
    Lemma nth_hmul : forall (a b : list F) k, length a = length b -> (k < length a)%nat ->
      nth k (hmul a b) zero = nth k a zero * nth k b zero.
    Proof.
      induction a as [| a0 a ih]; intros b k hl hk; [cbn in hk; lia |].
      destruct b as [| b0 b]; [discriminate |].
      destruct k as [| k]; [reflexivity | cbn [BayerGroth.hmul combine map fst snd nth]; fold (hmul a b); apply ih; cbn in *; lia].
    Qed.
    Lemma nth_hon_p : forall sn k, (k < K)%nat -> nth k (hon_p sn) zero = nth k (hon_b sn) zero * nth k (hon_d sn) zero.
    Proof.
      intros sn k hk; unfold hon_p; apply nth_hmul; unfold hon_b, hon_d; rewrite !map_length, !seq_length; lia.
    Qed.

    (** The combined honest ciphertext encrypts [⟨β, b⟩] with randomness
        [⟨β, r⟩]. *)
    Lemma cbeta_hon : forall beta sn rd, length beta = K ->
      cbeta beta (hon_cs sn rd) = enc g h (dot beta (hon_b sn) K) (dot beta (rd_r rd) K).
    Proof.
      intros beta sn rd hb; unfold cbeta, hon_cs.
      rewrite (lmexp_enc (fun k => natF (pos_bit sn k)) (fun k => nth k (rd_r rd) zero) K 0 beta hb).
      apply enc_ext; apply fsum_ext; intros i hi; rewrite Nat.add_0_l; [rewrite nth_hon_b by exact hi |]; reflexivity.
    Qed.

    (** Slicing of concatenations. *)
    Lemma wslice_app_shift : forall (a b : list F) la off len, length a = la ->
      wslice (a ++ b) (la + off) len = wslice b off len.
    Proof.
      intros * ha; unfold wslice; apply map_ext_in; intros i hi.
      rewrite app_nth2 by lia; f_equal; lia.
    Qed.
    Lemma wslice_prefix : forall (a b : list F) len, length a = len -> wslice (a ++ b) 0 len = a.
    Proof.
      intros * ha; apply (nth_ext _ _ zero zero); [rewrite wslice_length; lia |].
      intros i hi; rewrite wslice_length in hi; rewrite nth_wslice by exact hi.
      rewrite app_nth1 by lia; f_equal.
    Qed.
    Lemma wat_app_shift : forall (a b : list F) la i, length a = la -> wat (a ++ b) (la + i) = wat b i.
    Proof. intros * ha; unfold wat; rewrite app_nth2 by lia; f_equal; lia. Qed.

    (** Lengths of the honest witness vectors. *)
    Lemma hon_s_length : forall sn, length sn = m -> length (hon_s sn) = m.
    Proof. intros; unfold hon_s; rewrite map_length; assumption. Qed.
    Lemma hon_d_length : forall sn, length (hon_d sn) = K.
    Proof. intros; unfold hon_d; rewrite map_length, seq_length; reflexivity. Qed.
    Lemma hon_b_length : forall sn, length (hon_b sn) = K.
    Proof. intros; unfold hon_b; rewrite map_length, seq_length; reflexivity. Qed.
    Lemma hon_X_length : forall sn, length (hon_X sn) = NX.
    Proof. intros; unfold hon_X; rewrite map_length, seq_length; reflexivity. Qed.
    Lemma hon_p_length : forall sn, length (hon_p sn) = K.
    Proof.
      intros; unfold hon_p; rewrite hmul_length, hon_b_length, hon_d_length; apply Nat.min_id.
    Qed.
    Lemma hon_lengths : forall sn, length sn = m ->
      length (hon_s sn) = m /\ length (hon_d sn) = K /\ length (hon_b sn) = K /\
      length (hon_p sn) = K /\ length (hon_X sn) = NX.
    Proof.
      intros sn hsn; repeat split;
        [apply hon_s_length; exact hsn | apply hon_d_length | apply hon_b_length | apply hon_p_length | apply hon_X_length].
    Qed.

    (** The honest witness has length [W]. *)
    Lemma hon_w_length : forall beta sn rd, length sn = m -> length (hon_w beta sn rd) = W.
    Proof.
      intros * hsn; destruct (hon_lengths sn hsn) as (l1 & l2 & l3 & l4 & l5).
      unfold hon_w, W, oR, oX; rewrite !app_length; cbn [length]; lia.
    Qed.

    (** The slices of the honest witness are the honest vectors and
        randomness. *)
    Lemma hon_w_slices : forall beta sn rd, length sn = m ->
      wslice (hon_w beta sn rd) oS m = hon_s sn /\ wslice (hon_w beta sn rd) oD K = hon_d sn /\
      wslice (hon_w beta sn rd) oB K = hon_b sn /\ wslice (hon_w beta sn rd) oP K = hon_p sn /\
      wslice (hon_w beta sn rd) oX NX = hon_X sn /\
      wat (hon_w beta sn rd) oR = rd_rs rd /\ wat (hon_w beta sn rd) (oR + 1) = rd_rd rd /\
      wat (hon_w beta sn rd) (oR + 2) = rd_rb rd /\ wat (hon_w beta sn rd) (oR + 3) = rd_rp rd /\
      wat (hon_w beta sn rd) (oR + 4) = rd_rX rd /\ wat (hon_w beta sn rd) (oR + 5) = dot beta (rd_r rd) K.
    Proof.
      intros * hsn; destruct (hon_lengths sn hsn) as (l1 & l2 & l3 & l4 & l5); unfold hon_w.
      repeat split.
      + unfold oS; apply wslice_prefix; exact l1.
      + replace oD with (length (hon_s sn) + 0)%nat by (unfold oD; lia).
        rewrite wslice_app_shift by reflexivity; apply wslice_prefix; exact l2.
      + replace oB with (length (hon_s sn) + (length (hon_d sn) + 0))%nat by (unfold oB; lia).
        rewrite !wslice_app_shift by reflexivity; apply wslice_prefix; exact l3.
      + replace oP with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + 0)))%nat by (unfold oP; lia).
        rewrite !wslice_app_shift by reflexivity; apply wslice_prefix; exact l4.
      + replace oX with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + 0))))%nat
          by (unfold oX; lia).
        rewrite !wslice_app_shift by reflexivity; apply wslice_prefix; exact l5.
      + replace oR with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + (length (hon_X sn) + 0)))))%nat
          by (unfold oR, oX; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR + 1)%nat with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + (length (hon_X sn) + 1)))))%nat
          by (unfold oR, oX; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR + 2)%nat with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + (length (hon_X sn) + 2)))))%nat
          by (unfold oR, oX; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR + 3)%nat with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + (length (hon_X sn) + 3)))))%nat
          by (unfold oR, oX; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR + 4)%nat with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + (length (hon_X sn) + 4)))))%nat
          by (unfold oR, oX; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
      + replace (oR + 5)%nat with (length (hon_s sn) + (length (hon_d sn) + (length (hon_b sn) + (length (hon_p sn) + (length (hon_X sn) + 5)))))%nat
          by (unfold oR, oX; lia).
        rewrite !wat_app_shift by reflexivity; reflexivity.
    Qed.

    (** Entries of the honest witness at the offsets used by [phi]. *)
    Lemma hon_w_at : forall beta sn rd k, length sn = m -> (k < K)%nat ->
      wat (hon_w beta sn rd) (oD + k) = nth k (hon_d sn) zero /\
      wat (hon_w beta sn rd) (oB + k) = nth k (hon_b sn) zero /\
      wat (hon_w beta sn rd) (oP + k) = nth k (hon_p sn) zero /\
      wat (hon_w beta sn rd) (oS + k mod m) = natF (nth (k mod m) sn 0) /\
      wat (hon_w beta sn rd) (oS + k / m) = natF (nth (k / m) sn 0).
    Proof.
      intros * hsn hk; destruct (hon_w_slices beta sn rd hsn) as (e1 & e2 & e3 & e4 & _).
      destruct (kdm_lt k hk) as (hd & hm).
      repeat split.
      + rewrite <-e2, nth_wslice by exact hk; reflexivity.
      + rewrite <-e3, nth_wslice by exact hk; reflexivity.
      + rewrite <-e4, nth_wslice by exact hk; reflexivity.
      + change (wat (hon_w beta sn rd) (oS + k mod m)) with (nth (oS + k mod m) (hon_w beta sn rd) zero).
        rewrite <-(nth_wslice (hon_w beta sn rd) oS m (k mod m)) by exact hm; rewrite e1; apply nth_hon_s; lia.
      + change (wat (hon_w beta sn rd) (oS + k / m)) with (nth (oS + k / m) (hon_w beta sn rd) zero).
        rewrite <-(nth_wslice (hon_w beta sn rd) oS m (k / m)) by exact hd; rewrite e1; apply nth_hon_s; lia.
    Qed.

    (** [natF 1 = 1]. *)
    Lemma natF_one : natF 1 = one.
    Proof. cbn [nat_to_F]; field. Qed.

    (** Binary expansion: [v mod 2^(L+1) = v mod 2^L + 2^L · bit v L]. *)
    Lemma mod_pow2_S : forall (Lb v : nat), (v mod Nat.pow 2 (S Lb) = v mod Nat.pow 2 Lb + Nat.pow 2 Lb * ((v / Nat.pow 2 Lb) mod 2))%nat.
    Proof.
      intros Lb v. set (P := Nat.pow 2 Lb).
      assert (hP : (0 < P)%nat) by (unfold P; pose proof (Nat.pow_nonzero 2 Lb ltac:(lia)); lia).
      rewrite Nat.pow_succ_r'; fold P.
      pose proof (Nat.div_mod v P ltac:(lia)) as hq1.
      pose proof (Nat.div_mod (v / P) 2 ltac:(lia)) as hq2.
      pose proof (Nat.mod_upper_bound v P ltac:(lia)) as hq3.
      pose proof (Nat.mod_upper_bound (v / P) 2 ltac:(lia)) as hq4.
      symmetry; apply (Nat.mod_unique v (2 * P) ((v / P) / 2)); nia.
    Qed.

    (** [Σ_(t<L) 2^t · bit v t = v mod 2^L] in [F]. *)
    Lemma bits_sum : forall (Lb v : nat),
      fsum (fun t => pow2F t * natF (bit v t)) Lb = natF (v mod Nat.pow 2 Lb).
    Proof.
      intros Lb v; induction Lb as [| Lb ih].
      + cbn [SigmaK.fsum Nat.pow]; rewrite Nat.mod_1_r; reflexivity.
      + change (fsum (fun t => pow2F t * natF (bit v t)) (S Lb)) with
          (fsum (fun t => pow2F t * natF (bit v t)) Lb + pow2F Lb * natF (bit v Lb)).
        rewrite ih, mod_pow2_S; unfold pow2F, bit.
        rewrite (natF_add (Hvec := Hvec)), (natF_mul (Hvec := Hvec)); reflexivity.
    Qed.

    (** Bits are 0 or 1. *)
    Lemma bit_01 : forall v t, bit v t = 0%nat \/ bit v t = 1%nat.
    Proof. intros; unfold bit; pose proof (Nat.mod_upper_bound (v / Nat.pow 2 t) 2 ltac:(lia)); lia. Qed.

    (** Entries of the honest [X]. *)
    Lemma nth_hon_X : forall sn t k, (t < L)%nat -> (k < K)%nat ->
      nth (t * K + k) (hon_X sn) zero = natF (bit (pos_v sn k) t).
    Proof.
      intros sn t k ht hk; pose proof K_pos.
      unfold hon_X; rewrite nth_map_seq by (unfold NX; nia).
      rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.div_add by lia.
      rewrite Nat.mod_small, Nat.div_small by lia; reflexivity.
    Qed.

    (** If [v_k < 2^L], the honest bits of cell [k] encode [v_k]. *)
    Lemma vbits_hon : forall sn k, (k < K)%nat -> (pos_v sn k < Nat.pow 2 L)%nat ->
      vbits (hon_X sn) k = natF (pos_v sn k).
    Proof.
      intros sn k hk hv; unfold vbits.
      rewrite (fsum_ext _ (fun t => pow2F t * natF (bit (pos_v sn k) t)))
        by (intros t ht; rewrite nth_hon_X by assumption; reflexivity).
      rewrite bits_sum, Nat.mod_small by exact hv; reflexivity.
    Qed.

    (** For positions in [ [0, m] ], [v_k ≤ m]. *)
    Lemma pos_v_bound : forall sn k, (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (k < K)%nat ->
      (pos_v sn k <= m)%nat.
    Proof.
      intros sn k hs hk; destruct (kdm_lt k hk) as (hd & hm).
      pose proof (hs _ hd); pose proof (hs _ hm); unfold pos_v.
      destruct (Nat.ltb _ _); lia.
    Qed.

    (** The first scalar row vanishes on the honest witness
        ([δ = M s]). *)
    Lemma hon_row1 : forall beta g1 sn rd, length sn = m ->
      fsum (fun k => nth k g1 zero * (wat (hon_w beta sn rd) (oD + k) -
        (wat (hon_w beta sn rd) (oS + k mod m) - wat (hon_w beta sn rd) (oS + k / m)))) K = zero.
    Proof.
      intros * hsn; transitivity (fsum (fun _ => zero) K); [| apply fsum_zero].
      apply fsum_ext; intros k hk.
      destruct (hon_w_at beta sn rd k hsn hk) as (e1 & _ & _ & e4 & e5).
      rewrite e1, e4, e5, nth_hon_d by exact hk; field.
    Qed.

    (** The second scalar row vanishes on the honest witness, provided
        positions are at most [m < 2^L]: case [b = 1] gives
        [(s_j - s_i - 1) + δ - 2δ + 1 = 0], case [b = 0] gives
        [(s_i - s_j) + δ = 0]. *)
    Lemma hon_row2 : forall beta g2 sn rd, length sn = m ->
      (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
      fsum (fun k => nth k g2 zero * (vbits (hon_X sn) k + wat (hon_w beta sn rd) (oD + k) -
        (one + one) * wat (hon_w beta sn rd) (oP + k) + wat (hon_w beta sn rd) (oB + k))) K = zero.
    Proof.
      intros * hsn hs hL; transitivity (fsum (fun _ => zero) K); [| apply fsum_zero].
      apply fsum_ext; intros k hk.
      destruct (hon_w_at beta sn rd k hsn hk) as (e1 & e2 & e3 & _ & _).
      rewrite e1, e2, e3, nth_hon_p, nth_hon_b, nth_hon_d by exact hk.
      rewrite vbits_hon by (try exact hk; pose proof (pos_v_bound sn k hs hk); lia).
      destruct (kdm_lt k hk) as (hd & hm); pose proof (hs _ hd); pose proof (hs _ hm).
      unfold pos_v, pos_bit; destruct (Nat.ltb (nth (k / m) sn 0) (nth (k mod m) sn 0)) eqn:hlt.
      + apply Nat.ltb_lt in hlt.
        rewrite (natF_sub (Hvec := Hvec)) by lia; rewrite (natF_sub (Hvec := Hvec)) by lia.
        rewrite natF_one; field.
      + apply Nat.ltb_ge in hlt.
        rewrite (natF_sub (Hvec := Hvec)) by lia; cbn [nat_to_F]; field.
    Qed.

    (** The honest ballot's [target] is [phi] of the honest witness. *)
    Lemma target_phi : forall ch sn rd, length sn = m -> length (ch_beta ch) = K ->
      (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
      target (ch_beta ch) (encrypt_ballot2 ch sn rd) =
      phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch) (hon_w (ch_beta ch) sn rd).
    Proof.
      intros * hsn hb hs hL; unfold target, encrypt_ballot2, phi; cbn [b2_cs b2_Cs b2_Cd b2_Cb b2_Cp b2_CX].
      destruct (hon_w_slices (ch_beta ch) sn rd hsn) as (e1 & e2 & e3 & e4 & e5 & e6 & e7 & e8 & e9 & e10 & e11).
      rewrite e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, cbeta_hon by exact hb.
      unfold Elgamal.enc; cbn [fst snd]. f_equal.
      unfold vec2; f_equal; [symmetry; apply hon_row1; exact hsn |].
      f_equal; symmetry; apply hon_row2; assumption.
    Qed.

    (** [star(a, b) + star(a ∘ b, -1) = 0]: the honest first zero
        argument has a zero sum. *)
    Lemma star_w_prod : forall w y (a b : list F) len, length a = len -> length b = len ->
      star_w w y a b + star_w w y (hmul a b) (repeat (opp one) len) = zero.
    Proof.
      intros w y a; revert w; induction a as [| a0 a ih]; intros w b len hla hlb.
      + destruct b; [| cbn in *; lia]. destruct len; [| discriminate]. cbn; field.
      + destruct b as [| b0 b]; [cbn in *; lia |]. destruct len as [| len]; [discriminate |].
        cbn [BayerGroth.hmul combine map fst snd repeat star_w].
        fold (hmul a b).
        specialize (ih (w * y) b len ltac:(cbn in hla; lia) ltac:(cbn in hlb; lia)).
        etransitivity; [| exact ih]. field.
    Qed.

    (** [star(X, X - 1) = 0] for a bit vector [X]. *)
    Lemma star_w_bits : forall w y (X : list F) len, length X = len -> (forall x, In x X -> x = zero \/ x = one) ->
      star_w w y X (ladd X (repeat (opp one) len)) = zero.
    Proof.
      intros w y X; revert w; induction X as [| x X ih]; intros w len hl hb.
      + destruct len; cbn; reflexivity.
      + destruct len as [| len]; [discriminate |].
        cbn [SigmaK.ladd combine map fst snd repeat star_w].
        rewrite ih with (len := len) by (first [cbn in hl; lia | intros x' hx'; apply hb; right; exact hx']).
        destruct (hb x (or_introl eq_refl)) as [-> | ->]; field.
    Qed.

    (** The honest [b] and [X] are bit vectors. *)
    Lemma hon_b_bits : forall sn x, In x (hon_b sn) -> x = zero \/ x = one.
    Proof.
      intros sn x hx; unfold hon_b in hx; apply in_map_iff in hx; destruct hx as (k & <- & _).
      unfold pos_bit; destruct (Nat.ltb _ _); [right; apply natF_one | left; reflexivity].
    Qed.

    Lemma hon_X_bits : forall sn x, In x (hon_X sn) -> x = zero \/ x = one.
    Proof.
      intros sn x hx; unfold hon_X in hx; apply in_map_iff in hx; destruct hx as (u & <- & _).
      destruct (bit_01 (pos_v sn (u mod K)) (u / K)) as [e | e]; rewrite e; [left; reflexivity | right; apply natF_one].
    Qed.

    (** Completeness of the batched ballot. For [m] positions in [ [0, m] ]
        with [m < 2^L], keys of lengths [K] and [NX], and voter randomness
        of the right lengths, the honest ballot is accepted under any
        challenges [ch] with [|β| = K]. Each conjunct follows from
        [lin_completeness] (via [target_phi]) or [zero_completeness] (via
        [star_w_prod], [star_w_bits]). *)
    Theorem ballot2_valid : forall (ch : chal2) (sn : list nat) (rd : rand2),
      length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
      length gs1 = K -> length gs2 = NX -> length (ch_beta ch) = K ->
      length (rd_r rd) = K -> length (rd_a rd) = W ->
      length (rd_a1 rd) = K -> length (rd_b1 rd) = K -> length (rd_t1 rd) = 3%nat -> length (rd_u1 rd) = 1%nat ->
      length (rd_a2 rd) = NX -> length (rd_b2 rd) = NX -> length (rd_t2 rd) = 2%nat -> length (rd_u2 rd) = 0%nat ->
      length (rd_a3 rd) = K -> length (rd_b3 rd) = K -> length (rd_t3 rd) = 2%nat -> length (rd_u3 rd) = 0%nat ->
      verify_ballot2 ch (encrypt_ballot2 ch sn rd) = true.
    Proof.
      intros * hsn hs hL hg1 hg2 hb hr ha ha1 hb1 ht1 hu1 ha2 hb2 ht2 hu2 ha3 hb3 ht3 hu3.
      destruct (hon_lengths sn hsn) as (l1 & l2 & l3 & l4 & l5).
      unfold verify_ballot2.
      apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split; [apply andb_true_iff; split |] |] |].
      +
        (* K ciphertexts. *)
        cbn [b2_cs encrypt_ballot2]; unfold hon_cs; apply Nat.eqb_eq; rewrite map_length, seq_length; reflexivity.
      +
        (* The linear proof: target is phi of the honest witness. *)
        rewrite target_phi by assumption. cbn [b2_lin encrypt_ballot2].
        apply (lin_completeness W (phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch))
          (phi_add (ch_beta ch) (ch_g1 ch) (ch_g2 ch)) (phi_scale (ch_beta ch) (ch_g1 ch) (ch_g2 ch)));
          [apply hon_w_length; exact hsn | exact ha].
      +
        (* Zero argument 1: p = b ∘ δ. *)
        cbn [b2_Cb b2_Cp b2_Cd b2_z1 encrypt_ballot2].
        change [com h1 gs1 (hon_b sn) (rd_rb rd); com h1 gs1 (hon_p sn) (rd_rp rd)]
          with (com_list h1 gs1 [hon_b sn; hon_p sn] [rd_rb rd; rd_rp rd]).
        change [com h1 gs1 (hon_d sn) (rd_rd rd); cneg gs1 K]
          with (com_list h1 gs1 [hon_d sn; repeat (opp one) K] [rd_rd rd; zero]).
        apply (zero_completeness (Hvec := Hvec) (Gdec := Gdec)); try (cbn; lia).
        * constructor; [rewrite ha1; exact (eq_sym hg1) |].
          constructor; [rewrite l3; exact (eq_sym hg1) |].
          constructor; [rewrite l4; exact (eq_sym hg1) | constructor].
        * constructor; [rewrite hb1; exact (eq_sym hg1) |].
          constructor; [rewrite l2; exact (eq_sym hg1) |].
          constructor; [rewrite repeat_length; exact (eq_sym hg1) | constructor].
        * cbn [combine map fold_right fst snd].
          pose proof (star_w_prod (ch_y1 ch) (ch_y1 ch) (hon_b sn) (hon_d sn) K l3 l2) as hp.
          unfold BayerGroth.star, hon_p; etransitivity; [| exact hp]; field.
      +
        (* Zero argument 2: X is a bit vector. *)
        cbn [b2_CX b2_z2 encrypt_ballot2].
        replace (gop (com h1 gs2 (hon_X sn) (rd_rX rd)) (cneg gs2 NX))
          with (com h1 gs2 (ladd (hon_X sn) (repeat (opp one) NX)) (rd_rX rd)).
        2: { unfold cneg; transitivity (com h1 gs2 (ladd (hon_X sn) (repeat (opp one) NX)) (rd_rX rd + zero));
             [f_equal; field | apply com_add; rewrite repeat_length; exact l5]. }
        change [com h1 gs2 (hon_X sn) (rd_rX rd)] with (com_list h1 gs2 [hon_X sn] [rd_rX rd]).
        change [com h1 gs2 (ladd (hon_X sn) (repeat (opp one) NX)) (rd_rX rd)]
          with (com_list h1 gs2 [ladd (hon_X sn) (repeat (opp one) NX)] [rd_rX rd]).
        apply (zero_completeness (Hvec := Hvec) (Gdec := Gdec)); try (cbn; lia).
        * constructor; [rewrite ha2; exact (eq_sym hg2) |].
          constructor; [rewrite l5; exact (eq_sym hg2) | constructor].
        * constructor; [rewrite hb2; exact (eq_sym hg2) |].
          constructor; [rewrite ladd_length, l5; [exact (eq_sym hg2) | rewrite repeat_length; exact l5] | constructor].
        * cbn [combine map fold_right fst snd].
          pose proof (star_w_bits (ch_y2 ch) (ch_y2 ch) (hon_X sn) NX l5 (hon_X_bits sn)) as hb0.
          unfold BayerGroth.star; etransitivity; [| exact hb0]; field.
      +
        (* Zero argument 3: b is a bit vector. *)
        cbn [b2_Cb b2_z3 encrypt_ballot2].
        replace (gop (com h1 gs1 (hon_b sn) (rd_rb rd)) (cneg gs1 K))
          with (com h1 gs1 (ladd (hon_b sn) (repeat (opp one) K)) (rd_rb rd)).
        2: { unfold cneg; transitivity (com h1 gs1 (ladd (hon_b sn) (repeat (opp one) K)) (rd_rb rd + zero));
             [f_equal; field | apply com_add; rewrite repeat_length; exact l3]. }
        change [com h1 gs1 (hon_b sn) (rd_rb rd)] with (com_list h1 gs1 [hon_b sn] [rd_rb rd]).
        change [com h1 gs1 (ladd (hon_b sn) (repeat (opp one) K)) (rd_rb rd)]
          with (com_list h1 gs1 [ladd (hon_b sn) (repeat (opp one) K)] [rd_rb rd]).
        apply (zero_completeness (Hvec := Hvec) (Gdec := Gdec)); try (cbn; lia).
        * constructor; [rewrite ha3; exact (eq_sym hg1) |].
          constructor; [rewrite l3; exact (eq_sym hg1) | constructor].
        * constructor; [rewrite hb3; exact (eq_sym hg1) |].
          constructor; [rewrite ladd_length, l3; [exact (eq_sym hg1) | rewrite repeat_length; exact l3] | constructor].
        * cbn [combine map fold_right fst snd].
          pose proof (star_w_bits (ch_y3 ch) (ch_y3 ch) (hon_b sn) K l3 (hon_b_bits sn)) as hb0.
          unfold BayerGroth.star; etransitivity; [| exact hb0]; field.
    Qed.

    (** *** Fiat–Shamir

        The hash input is a list of tagged items (group elements, field
        elements and natural-number tags). *)
    Inductive b2_item : Type := B2G (x : G) | B2F (x : F) | B2N (k : nat).

    (** The Fiat–Shamir section, parametric in the hash [H]. *)
    Section NIZK2.

    (** [H] is an abstract function into [F]. *)
      Context (H : list b2_item -> F).

    (** Item lists for the ciphertexts, the base statement (ciphertexts and
        commitments), a [St] value, and the announcement of a zero
        argument. *)
      Definition items_cs (cs : list (G * G)) : list b2_item :=
        concat (map (fun c => [B2G (fst c); B2G (snd c)]) cs).
      Definition items_base (bt : ballot2) : list b2_item :=
        items_cs (b2_cs bt) ++ [B2G (b2_Cs bt); B2G (b2_Cd bt); B2G (b2_Cb bt); B2G (b2_Cp bt); B2G (b2_CX bt)].
      Definition items_st (st : St) : list b2_item :=
        map B2G (Vector.to_list (fst st)) ++ map B2F (Vector.to_list (snd st)).
      Definition items_zero (z : zero_argument) : list b2_item :=
        B2G (za_cA0 z) :: B2G (za_cBm z) :: map B2G (za_cd z).

    (** The challenges of a ballot: tag 1 for [β], 2 and 3 for [γ₁], [γ₂]
        ([K] values each, indexed by [k]); tags 4, 5, 9 for [y₁], [y₂],
        [y₃]; tag 6 for [c] (from the base and the linear announcement);
        tags 7, 8, 10 for [x₁], [x₂], [x₃] (from the base and the
        respective zero-argument announcement). The election key is not
        hashed. *)
      Definition vec_chal (tag : nat) (bt : ballot2) : list F :=
        map (fun k => H (B2N tag :: B2N k :: items_base bt)) (seq 0 K).
      Definition challenges_of (bt : ballot2) : chal2 :=
        mk_chal2 (vec_chal 1 bt) (vec_chal 2 bt) (vec_chal 3 bt)
          (H (B2N 6 :: items_base bt ++ items_st (lin_a (b2_lin bt))))
          (H (B2N 4 :: items_base bt)) (H (B2N 7 :: items_base bt ++ items_zero (b2_z1 bt)))
          (H (B2N 5 :: items_base bt)) (H (B2N 8 :: items_base bt ++ items_zero (b2_z2 bt)))
          (H (B2N 9 :: items_base bt)) (H (B2N 10 :: items_base bt ++ items_zero (b2_z3 bt))).

    (** The non-interactive verifier. *)
      Definition nizk_verify_ballot2 (bt : ballot2) : bool :=
        verify_ballot2 (challenges_of bt) bt.

    (** The honest non-interactive voter in three passes: [chal0] is an
        arbitrary first guess; pass one fixes [β], [γ], [y] (from the
        ciphertexts and commitments, which do not depend on the
        challenges) and pass two fixes [c] and [x] (the linear
        announcement depends on [β], [γ]; the zero announcements on [y]);
        pass three is the ballot. *)
      Definition chal0 : chal2 :=
        mk_chal2 (repeat zero K) (repeat zero K) (repeat zero K) zero zero zero zero zero zero zero.
      Definition nizk_encrypt_ballot2 (sn : list nat) (rd : rand2) : ballot2 :=
        let b0 := encrypt_ballot2 chal0 sn rd in
        let b1 := encrypt_ballot2 (challenges_of b0) sn rd in
        encrypt_ballot2 (challenges_of b1) sn rd.

    (** The derived challenges depend only on [β], [γ₁], [γ₂], [y₁], [y₂],
        [y₃], not on [c] or the [x]'s. *)
      Lemma challenges_announcements : forall ch ch' sn rd,
        ch_beta ch = ch_beta ch' -> ch_g1 ch = ch_g1 ch' -> ch_g2 ch = ch_g2 ch' ->
        ch_y1 ch = ch_y1 ch' -> ch_y2 ch = ch_y2 ch' -> ch_y3 ch = ch_y3 ch' ->
        challenges_of (encrypt_ballot2 ch sn rd) = challenges_of (encrypt_ballot2 ch' sn rd).
      Proof.
        intros [] [] sn rd e1 e2 e3 e4 e5 e6; cbn in e1, e2, e3, e4, e5, e6; subst; reflexivity.
      Qed.

    (** The coefficient vectors have length [K]. *)
      Lemma vec_chal_length : forall tag bt, length (vec_chal tag bt) = K.
      Proof. intros; unfold vec_chal; rewrite map_length, seq_length; reflexivity. Qed.

    (** Completeness of the non-interactive ballot, for every hash [H]. *)
      Theorem nizk_ballot2_valid : forall (sn : list nat) (rd : rand2),
        length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
        length gs1 = K -> length gs2 = NX ->
        length (rd_r rd) = K -> length (rd_a rd) = W ->
        length (rd_a1 rd) = K -> length (rd_b1 rd) = K -> length (rd_t1 rd) = 3%nat -> length (rd_u1 rd) = 1%nat ->
        length (rd_a2 rd) = NX -> length (rd_b2 rd) = NX -> length (rd_t2 rd) = 2%nat -> length (rd_u2 rd) = 0%nat ->
        length (rd_a3 rd) = K -> length (rd_b3 rd) = K -> length (rd_t3 rd) = 2%nat -> length (rd_u3 rd) = 0%nat ->
        nizk_verify_ballot2 (nizk_encrypt_ballot2 sn rd) = true.
      Proof.
        intros; unfold nizk_verify_ballot2, nizk_encrypt_ballot2.
        set (b0 := encrypt_ballot2 chal0 sn rd).
        set (ch1 := challenges_of b0).
        set (b1 := encrypt_ballot2 ch1 sn rd).
        set (ch2 := challenges_of b1).
        assert (e : challenges_of (encrypt_ballot2 ch2 sn rd) = ch2).
        { transitivity (challenges_of (encrypt_ballot2 ch1 sn rd)); [| reflexivity].
          apply challenges_announcements; reflexivity. }
        rewrite e. apply ballot2_valid; try assumption. apply vec_chal_length.
      Qed.

    End NIZK2.

    (** *** Soundness: algebraic helpers *)

    (** [cmexp] is [cbeta] without the fixed coefficient order. *)
    Local Notation cmexp := (lmexp (vid := cid) (vadd := cmul) (smul := cpow)).

    (** Laws of the ciphertext algebra. *)
    Lemma cmul_cid_l : forall a : G * G, cmul cid a = a.
    Proof. intros [a1 a2]; unfold Schulze.cmul, Schulze.cid; cbn [fst snd]; rewrite !gop_gid_l; reflexivity. Qed.
    Lemma cmul_rearrange : forall a b c d : G * G, cmul (cmul a b) (cmul c d) = cmul (cmul a c) (cmul b d).
    Proof. intros [] [] [] []; unfold Schulze.cmul; cbn [fst snd]; f_equal; apply gop_rearrange. Qed.
    Lemma cpow_zero : forall a : G * G, cpow a zero = cid.
    Proof. intros []; unfold Schulze.cpow, Schulze.cid; cbn [fst snd]; rewrite !pow_zero; reflexivity. Qed.
    Lemma cpow_add : forall (a : G * G) (u v : F), cpow a (u + v) = cmul (cpow a u) (cpow a v).
    Proof. intros [] u v; unfold Schulze.cpow, Schulze.cmul; cbn [fst snd]; rewrite !pow_add; reflexivity. Qed.

    (** Multi-exponentiation of ciphertexts is linear in the exponents. *)
    Lemma cmexp_ladd : forall (cs : list (G * G)) (u v : list F), length u = length cs -> length v = length cs ->
      cmexp cs (ladd u v) = cmul (cmexp cs u) (cmexp cs v).
    Proof.
      induction cs as [| c cs ih]; intros u v hu hv.
      + destruct u; [| discriminate]; destruct v; [| discriminate]; cbn; rewrite cmul_cid_l; reflexivity.
      + destruct u as [| u0 u]; [discriminate |]; destruct v as [| v0 v]; [discriminate |].
        cbn [SigmaK.ladd combine map fst snd]; fold (ladd u v).
        rewrite !lmexp_cons, ih by (cbn in *; lia). rewrite cpow_add. apply cmul_rearrange.
    Qed.

    (** Multi-exponentiation with all-zero exponents is [cid]. *)
    Lemma cmexp_zeros : forall (cs : list (G * G)) (k : nat), cmexp cs (repeat zero k) = cid.
    Proof.
      induction cs as [| c cs ih]; intros k; [destruct k; reflexivity |].
      destruct k as [| k]; [reflexivity |].
      cbn [repeat]; rewrite lmexp_cons, cpow_zero, cmul_cid_l; apply ih.
    Qed.

    (** [unit_vec k d] is the exponent vector with [d] at [k] and zero
        elsewhere. *)
    Definition unit_vec (k : nat) (d : F) : list F := repeat zero k ++ d :: repeat zero (K - k - 1).

    (** Length and entries of [unit_vec]. *)
    Lemma unit_vec_length : forall k d, (k < K)%nat -> length (unit_vec k d) = K.
    Proof. intros; unfold unit_vec; rewrite app_length; cbn [length]; rewrite !repeat_length; lia. Qed.

    Lemma nth_unit_vec : forall k d j, (k < K)%nat -> (j < K)%nat ->
      nth j (unit_vec k d) zero = if Nat.eqb j k then d else zero.
    Proof.
      intros k d j hk hj; unfold unit_vec.
      destruct (Nat.lt_ge_cases j k) as [hlt | hge].
      + rewrite app_nth1 by (rewrite repeat_length; exact hlt).
        rewrite (proj2 (Nat.eqb_neq j k)) by lia; apply nth_repeat.
      + rewrite app_nth2 by (rewrite repeat_length; exact hge); rewrite repeat_length.
        destruct (Nat.eq_dec j k) as [-> | hne].
        * rewrite Nat.sub_diag, (proj2 (Nat.eqb_eq k k) eq_refl); reflexivity.
        * rewrite (proj2 (Nat.eqb_neq j k) hne).
          replace (j - k)%nat with (S (j - k - 1)) by lia; cbn [nth]; apply nth_repeat.
    Qed.

    (** [cmexp cs (unit_vec k d) = cs_k ^ d]. *)
    Lemma cmexp_unit : forall (cs : list (G * G)) (k : nat) (d : F), length cs = K -> (k < K)%nat ->
      cmexp cs (unit_vec k d) = cpow (nth k cs cid) d.
    Proof.
      intros cs k d hcs hk.
      set (a := nth k cs cid).
      destruct (nth_split cs cid (n := k) ltac:(lia)) as (l1 & l2 & e & hl1).
      change (nth k cs cid) with a in e.
      rewrite e. unfold unit_vec.
      rewrite (lmexp_app (HV := _)) with (gs1 := l1) (xs1 := repeat zero k)
        by (rewrite repeat_length; exact hl1).
      rewrite cmexp_zeros, cmul_cid_l, lmexp_cons, cmexp_zeros.
      unfold Schulze.cmul, Schulze.cid; destruct (cpow a d); cbn [fst snd]; rewrite !gop_gid_r; reflexivity.
    Qed.

    (** [differ_at k u v]: two coefficient vectors of length [K] that
        differ exactly at index [k]. *)
    Definition differ_at (k : nat) (u v : list F) : Prop :=
      length u = K /\ length v = K /\ (forall j, (j < K)%nat -> j <> k -> nth j u zero = nth j v zero) /\
      nth k u zero <> nth k v zero.

    (** [u = v + unit_vec k (u_k - v_k)] when they differ only at [k]. *)
    Lemma differ_at_ladd : forall k u v, (k < K)%nat -> differ_at k u v ->
      u = ladd v (unit_vec k (nth k u zero - nth k v zero)).
    Proof.
      intros k u v hk (hu & hv & hagree & hne).
      apply (nth_ext _ _ zero zero).
      + rewrite ladd_length; [lia | rewrite unit_vec_length; lia].
      + intros j hj; rewrite hu in hj.
        rewrite nth_ladd by (rewrite ?unit_vec_length; lia).
        rewrite nth_unit_vec by assumption.
        destruct (Nat.eqb j k) eqn:e; [apply Nat.eqb_eq in e; subst j; field |].
        apply Nat.eqb_neq in e; rewrite hagree by assumption; field.
    Qed.

    (** [cbeta u cs = cbeta v cs · cs_k ^ (u_k - v_k)] when [u], [v]
        differ only at [k]. *)
    Lemma cbeta_differ : forall (cs : list (G * G)) (k : nat) (u v : list F), length cs = K -> (k < K)%nat ->
      differ_at k u v -> cbeta u cs = cmul (cbeta v cs) (cpow (nth k cs cid) (nth k u zero - nth k v zero)).
    Proof.
      intros cs k u v hcs hk hd; unfold cbeta.
      transitivity (cmexp cs (ladd v (unit_vec k (nth k u zero - nth k v zero))));
        [f_equal; apply differ_at_ladd; assumption |].
      rewrite cmexp_ladd by (rewrite ?unit_vec_length; destruct hd; lia).
      rewrite cmexp_unit by assumption; reflexivity.
    Qed.

    (** [d]-th roots are unique for [d ≠ 0]. *)
    Lemma root_unique : forall (u v : G) (d : F), d <> zero -> u ^ d = v ^ d -> u = v.
    Proof.
      intros u v d hd he.
      rewrite <-(pow_one u), <-(pow_one v).
      replace one with (d * inv d) by (field; exact hd).
      rewrite !pow_mul, he; reflexivity.
    Qed.

    (** A sum that vanishes outside [k] equals its [k]-th term. *)
    Lemma fsum_single : forall (f : nat -> F) (k len : nat), (k < len)%nat ->
      (forall j, (j < len)%nat -> j <> k -> f j = zero) -> fsum f len = f k.
    Proof.
      intros f k len; induction len as [| len ih]; intros hk hz; [lia |].
      change (fsum f (S len)) with (fsum f len + f len).
      destruct (Nat.eq_dec k len) as [-> | hne].
      + rewrite (fsum_ext f (fun _ => zero)) by (intros j hj; apply hz; lia). rewrite fsum_zero; field.
      + rewrite ih by (try lia; intros j hj hjk; apply hz; lia). rewrite (hz len) by lia; field.
    Qed.

    (** If two coefficient vectors differing only at [k] both annihilate
        [e], then [e_k = 0]. *)
    Lemma rlc_coord : forall (e : nat -> F) (u v : list F) (k : nat), (k < K)%nat -> differ_at k u v ->
      fsum (fun j => nth j u zero * e j) K = zero -> fsum (fun j => nth j v zero * e j) K = zero -> e k = zero.
    Proof.
      intros e u v k hk (hu & hv & hagree & hne) hs1 hs2.
      assert (hs3 : fsum (fun j => (nth j u zero - nth j v zero) * e j) K = zero).
      { rewrite (fsum_ext _ (fun j => nth j u zero * e j + opp one * (nth j v zero * e j)))
          by (intros; field).
        rewrite fsum_add, fsum_scale, hs1, hs2; field. }
      rewrite (fsum_single _ k K hk) in hs3 by (intros j hj hjk; rewrite hagree by assumption; field).
      destruct (mul_eq_zero (Fdec := Fdec) (Hf := vector_space_field) _ _ hs3) as [h0 | h0];
        [exfalso; apply hne; apply (sub_eq_zero (Hf := vector_space_field)); exact h0 | exact h0].
    Qed.

    (** *** Zero arguments as polynomial identities *)

    (** [eval q y] evaluates the polynomial with coefficients [q]. *)
    Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).

    (** [star y a b = y · eval (a ∘ b) y]. *)
    Lemma star_hmul_eval : forall y (a b : list F), length a = length b -> star y a b = y * eval (hmul a b) y.
    Proof.
      intros y a b hl.
      transitivity (star y (hmul (repeat one (length a)) a) b); [rewrite hmul_ones by reflexivity; reflexivity |].
      transitivity (star y (repeat one (length a)) (hmul a b)); [unfold BayerGroth.star; symmetry; apply star_w_hmul |].
      rewrite (star_ones_feval (Hvec := Hvec) (length a)) by (rewrite hmul_length; lia).
      rewrite (feval_eval (Hvec := Hvec)); reflexivity.
    Qed.

    (** [star y c (-1, …, -1) = -(y · eval c y)]. *)
    Lemma star_neg_eval : forall y (c : list F) len, length c = len -> star y c (repeat (opp one) len) = opp (y * eval c y).
    Proof.
      intros y c len hl; subst len.
      rewrite neg_ones, star_lscale_r.
      transitivity (opp one * star y (repeat one (length c)) c); [unfold BayerGroth.star; rewrite star_w_comm; reflexivity |].
      rewrite (star_ones_feval (Hvec := Hvec) (length c)) by lia.
      rewrite (feval_eval (Hvec := Hvec)); field.
    Qed.

    (** A polynomial of degree below [|Y|] vanishing on all of [Y] (no
        duplicates) is zero. *)
    Lemma poly_vanish : forall (q Y : list F), NoDup Y -> (length q <= length Y)%nat ->
      (forall y, In y Y -> eval q y = zero) -> forall j, nth j q zero = zero.
    Proof.
      intros q Y hnd hl hz j.
      pose proof (agree_nth (Fdec := Fdec) (Hf := vector_space_field) Y q [] hnd hl ltac:(cbn; lia)
        (fun y hy => hz y hy) j) as e.
      rewrite e; destruct j; reflexivity.
    Qed.

    (** Same with [y · eval q y = 0] on non-zero [y]. *)
    Lemma poly_vanish_mul : forall (q Y : list F), NoDup Y -> (length q <= length Y)%nat ->
      (forall y, In y Y -> y <> zero) -> (forall y, In y Y -> y * eval q y = zero) ->
      forall j, nth j q zero = zero.
    Proof.
      intros q Y hnd hl hy0 hz; apply (poly_vanish q Y hnd hl).
      intros y hy; destruct (mul_eq_zero (Fdec := Fdec) (Hf := vector_space_field) _ _ (hz y hy)) as [e | e];
        [exfalso; exact (hy0 y hy e) | exact e].
    Qed.

    (** Injectivity of [vec7] and [vec2]. *)
    Lemma vec7_inj : forall a b c d e f k a' b' c' d' e' f' k',
      vec7 a b c d e f k = vec7 a' b' c' d' e' f' k' ->
      a = a' /\ b = b' /\ c = c' /\ d = d' /\ e = e' /\ f = f' /\ k = k'.
    Proof.
      intros * H.
      repeat split.
      + exact (f_equal Vector.hd H).
      + exact (f_equal (fun v => Vector.hd (Vector.tl v)) H).
      + exact (f_equal (fun v => Vector.hd (Vector.tl (Vector.tl v))) H).
      + exact (f_equal (fun v => Vector.hd (Vector.tl (Vector.tl (Vector.tl v)))) H).
      + exact (f_equal (fun v => Vector.hd (Vector.tl (Vector.tl (Vector.tl (Vector.tl v))))) H).
      + exact (f_equal (fun v => Vector.hd (Vector.tl (Vector.tl (Vector.tl (Vector.tl (Vector.tl v)))))) H).
      + exact (f_equal (fun v => Vector.hd (Vector.tl (Vector.tl (Vector.tl (Vector.tl (Vector.tl (Vector.tl v))))))) H).
    Qed.

    Lemma vec2_inj : forall a b a' b', vec2 a b = vec2 a' b' -> a = a' /\ b = b'.
    Proof.
      intros * H; split; [exact (f_equal Vector.hd H) | exact (f_equal (fun v => Vector.hd (Vector.tl v)) H)].
    Qed.

    (** *** Soundness: extraction *)

    (** [binding_break h1 gs]: two distinct openings of one commitment
        under [(h1, gs)], i.e. the binding property of the key is broken.
        [natF_injective] and [cdec] are from [Frontend/Schulze.v]. *)
    Local Notation binding_break := (binding_break (gid := gid) (gop := gop) (gpow := gpow)).
    Local Notation natF_injective := (Schulze.natF_injective (zero := zero) (one := one) (add := add)).
    Local Notation cdec := (Schulze.cdec (ginv := ginv) (gop := gop) (gpow := gpow)).

    (** [lin_accepts β γ₁ γ₂ bt c₀ c₁]: the linear proof of [bt] is accepted
        for the same announcement at challenges [c₀] and [c₁]. *)
    Definition lin_accepts (beta g1 g2 : list F) (bt : ballot2) (c0 c1 : F) : Prop :=
      exists (A : St) (z0 z1 : list F),
        lin_verify W (phi beta g1 g2) (target beta bt) c0 (mk_lin A z0) = true /\
        lin_verify W (phi beta g1 g2) (target beta bt) c1 (mk_lin A z1) = true.

    (** [zero_accepts gs cA cB y]: the zero argument for rows [cA], [cB] at
        [y] is accepted for one announcement at [2r + 1] distinct
        challenges [x] ([r] = number of rows). *)
    Definition zero_accepts (gs : list G) (cA cB : list G) (y : F) : Prop :=
      exists (cA0 cBm : G) (cd : list G) (xs : list F) (a b : nat -> list F) (r s t : nat -> F),
        NoDup xs /\ length xs = (2 * length cA + 1)%nat /\
        forall j, (j < length xs)%nat ->
          zero_verify h1 gs cA cB y (nth j xs zero) (mk_zero cA0 cBm cd (a j) (b j) (r j) (s j) (t j)) = true.

    (** Special soundness of the linear proof yields a witness [w] with
        [phi w = target]. *)
    Lemma lin_open : forall beta g1 g2 bt c0 c1, c0 <> c1 -> lin_accepts beta g1 g2 bt c0 c1 ->
      exists w, length w = W /\ phi beta g1 g2 w = target beta bt.
    Proof.
      intros * hc (A & z0 & z1 & h0 & hz1).
      destruct (lin_soundness (HV := st_vspace) W (phi beta g1 g2) (phi_add beta g1 g2) (phi_scale beta g1 g2)
        (target beta bt) A c0 c1 z0 z1 hc h0 hz1) as (hl & he).
      exists (lin_extract (sub := sub) (mul := mul) (inv := inv) (add := add) (opp := opp) (one := one) c0 c1 z0 z1); split; assumption.
    Qed.

    (** Reading the openings off [phi w = target]. *)
    Lemma phi_target_open : forall beta g1 g2 bt w, phi beta g1 g2 w = target beta bt ->
      b2_Cs bt = com h1 gs1 (wslice w oS m) (wat w oR) /\
      b2_Cd bt = com h1 gs1 (wslice w oD K) (wat w (oR + 1)) /\
      b2_Cb bt = com h1 gs1 (wslice w oB K) (wat w (oR + 2)) /\
      b2_Cp bt = com h1 gs1 (wslice w oP K) (wat w (oR + 3)) /\
      b2_CX bt = com h1 gs2 (wslice w oX NX) (wat w (oR + 4)) /\
      cbeta beta (b2_cs bt) = enc g h (dot beta (wslice w oB K) K) (wat w (oR + 5)) /\
      fsum (fun k => nth k g1 zero * (wat w (oD + k) - (wat w (oS + k mod m) - wat w (oS + k / m)))) K = zero /\
      fsum (fun k => nth k g2 zero * (vbits (wslice w oX NX) k + wat w (oD + k) -
        (one + one) * wat w (oP + k) + wat w (oB + k))) K = zero.
    Proof.
      intros * H; unfold phi, target in H.
      pose proof (f_equal fst H) as H1; pose proof (f_equal snd H) as H2; cbn [fst snd] in H1, H2.
      apply vec7_inj in H1; destruct H1 as (e1 & e2 & e3 & e4 & e5 & e6 & e7).
      apply vec2_inj in H2; destruct H2 as (e8 & e9).
      repeat split; try assumption; try (symmetry; assumption).
      rewrite (surjective_pairing (cbeta beta (b2_cs bt))); unfold Elgamal.enc.
      rewrite <-e6, <-e7; reflexivity.
    Qed.

    (** [m ≤ K]. *)
    Lemma m_le_K : (m <= K)%nat.
    Proof. unfold K; nia. Qed.

    (** Two witnesses opening the same five commitments agree on all five
        vectors, or a key is broken. *)
    Lemma open_agree : forall (w w' : list F), length gs1 = K -> length gs2 = NX ->
      com h1 gs1 (wslice w oS m) (wat w oR) = com h1 gs1 (wslice w' oS m) (wat w' oR) ->
      com h1 gs1 (wslice w oD K) (wat w (oR + 1)) = com h1 gs1 (wslice w' oD K) (wat w' (oR + 1)) ->
      com h1 gs1 (wslice w oB K) (wat w (oR + 2)) = com h1 gs1 (wslice w' oB K) (wat w' (oR + 2)) ->
      com h1 gs1 (wslice w oP K) (wat w (oR + 3)) = com h1 gs1 (wslice w' oP K) (wat w' (oR + 3)) ->
      com h1 gs2 (wslice w oX NX) (wat w (oR + 4)) = com h1 gs2 (wslice w' oX NX) (wat w' (oR + 4)) ->
      binding_break h1 gs1 \/ binding_break h1 gs2 \/
      (wslice w oS m = wslice w' oS m /\ wslice w oD K = wslice w' oD K /\ wslice w oB K = wslice w' oB K /\
       wslice w oP K = wslice w' oP K /\ wslice w oX NX = wslice w' oX NX).
    Proof.
      intros w w' hg1 hg2 es ed eb ep ex; pose proof m_le_K as hmK.
      destruct (open_eq_or_break (Hvec := Hvec) (Fdec := Fdec) h1 gs1 _ _ _ _ es) as [(_ & hs) | hb]; [| left; exact hb].
      destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 (wslice w oD K) (wat w (oR + 1))
        (wslice w' oD K) (wat w' (oR + 1)) ltac:(rewrite wslice_length; lia) ltac:(rewrite wslice_length; lia) ed)
        as [(hd & _) | hb]; [| left; exact hb].
      destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 (wslice w oB K) (wat w (oR + 2))
        (wslice w' oB K) (wat w' (oR + 2)) ltac:(rewrite wslice_length; lia) ltac:(rewrite wslice_length; lia) eb)
        as [(hb' & _) | hb]; [| left; exact hb].
      destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 (wslice w oP K) (wat w (oR + 3))
        (wslice w' oP K) (wat w' (oR + 3)) ltac:(rewrite wslice_length; lia) ltac:(rewrite wslice_length; lia) ep)
        as [(hp & _) | hb]; [| left; exact hb].
      destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs2 (wslice w oX NX) (wat w (oR + 4))
        (wslice w' oX NX) (wat w' (oR + 4)) ltac:(rewrite wslice_length; lia) ltac:(rewrite wslice_length; lia) ex)
        as [(hx & _) | hb]; [| right; left; exact hb].
      right; right; repeat split; try assumption.
      apply (nth_ext _ _ zero zero); [rewrite !wslice_length; reflexivity |].
      intros i hi; rewrite wslice_length in hi; apply hs; lia.
    Qed.

    (** Bit extraction from zero arguments: if [C = com(v; ρ)] and the
        argument with rows [C] against [C · com(-1)] is accepted at
        [|v|] distinct non-zero [y], then every [v_j] is a bit, or the key
        is broken. Proof: each accepted [y] gives
        [y · eval (v ∘ (v - 1)) y = 0] after opening (via
        [zero_soundness]); [poly_vanish_mul] then makes all coefficients
        [v_j (v_j - 1)] zero. *)
    Lemma zero_bits_open : forall (gs : list G) (len : nat) (C : G) (v : list F) (rho : F) (Y : list F),
      (1 <= len)%nat -> length gs = len -> length v = len -> C = com h1 gs v rho ->
      NoDup Y -> length Y = len -> (forall y, In y Y -> y <> zero) ->
      (forall y, In y Y -> zero_accepts gs [C] [gop C (cneg gs len)] y) ->
      binding_break h1 gs \/ forall j, (j < len)%nat -> nth j v zero = zero \/ nth j v zero = one.
    Proof.
      intros gs len C v rho Y hlen hgs hv hC hnd hY hy0 hacc.
      set (q := hmul v (ladd v (repeat (opp one) len))).
      assert (hq : length q = len) by (unfold q; rewrite hmul_length, ladd_length; [lia | rewrite repeat_length; lia]).
      (* At every accepted y, open the commitments and obtain
         y · eval (v ∘ (v - 1)) y = 0, or a binding break. *)
      assert (hall : forall j, (j < length Y)%nat -> nth j Y zero * eval q (nth j Y zero) = zero \/ binding_break h1 gs).
      { intros j hj; set (y := nth j Y zero); assert (hy : In y Y) by (apply nth_In; exact hj).
        destruct (hacc y hy) as (cA0 & cBm & cd & xs & a & b & r & s' & t & hnd' & hlen' & htr).
        destruct (zero_soundness (Hvec := Hvec) (Fdec := Fdec) h1 gs [C] [gop C (cneg gs len)] y cA0 cBm cd xs a b r s' t
          ltac:(lia) hnd' hlen' htr) as [(A & B & ra & sb & eA & eB & lA & lB & lra & lsb & hAn & hBn & hsum) | hb];
          [| right; exact hb].
        cbn [length] in lA, lB, lra, lsb.
        destruct A as [| a0 A]; [discriminate |]; destruct A; [| discriminate].
        destruct B as [| b0 B]; [discriminate |]; destruct B; [| discriminate].
        destruct ra as [| ra0 ra]; [discriminate |]; destruct ra; [| discriminate].
        destruct sb as [| sb0 sb]; [discriminate |]; destruct sb; [| discriminate].
        unfold BayerGroth.com_list in eA, eB; cbn [combine map fst snd] in eA, eB.
        injection eA as eA; injection eB as eB.
        rewrite hC in eA.
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs v rho a0 ra0 ltac:(lia)
          (hAn a0 (or_introl eq_refl)) eA) as [(ea & _) | hb]; [| right; exact hb].
        assert (eB' : com h1 gs (ladd v (repeat (opp one) len)) (rho + zero) = com h1 gs b0 sb0).
        { rewrite com_add by (rewrite repeat_length; exact hv). rewrite <-hC. unfold cneg in eB. exact eB. }
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs (ladd v (repeat (opp one) len)) (rho + zero) b0 sb0
          ltac:(rewrite ladd_length; [lia | rewrite repeat_length; lia]) (hBn b0 (or_introl eq_refl)) eB')
          as [(eb & _) | hb]; [| right; exact hb].
        left. cbn [combine map fold_right fst snd] in hsum. subst a0 b0. unfold q.
        rewrite <-(star_hmul_eval y v (ladd v (repeat (opp one) len)))
          by (rewrite ladd_length; [reflexivity | rewrite repeat_length; lia]).
        etransitivity; [| exact hsum]; field. }
      (* The polynomial vanishes on |v| distinct non-zero points, so every
         coefficient v_j (v_j - 1) is zero. *)
      destruct (forall_or _ _ (length Y) hall) as [hz | hb]; [| left; exact hb].
      right; intros j hj.
      pose proof (poly_vanish_mul q Y hnd ltac:(lia) hy0
        (fun y hy => match In_nth Y y zero hy with ex_intro _ i (conj hi e) => eq_ind _ (fun y' => y' * eval q y' = zero) (hz i hi) y e end) j) as e.
      unfold q in e.
      rewrite nth_hmul in e by (try rewrite ladd_length; try rewrite repeat_length; lia).
      rewrite nth_ladd in e by (rewrite ?repeat_length; lia).
      rewrite nth_repeat' in e by lia.
      destruct (mul_eq_zero (Fdec := Fdec) (Hf := vector_space_field) _ _ e) as [e0 | e0]; [left; exact e0 |].
      right. apply (sub_eq_zero (Hf := vector_space_field)). etransitivity; [| exact e0]; field.
    Qed.

    (** Product extraction: if the argument with rows [(C_b, C_p)] against
        [(C_δ, com(-1))] is accepted at [K] distinct non-zero [y], then
        [p = b ∘ d] for the openings, or [gs1] is broken. *)
    Lemma zero_prod_open : forall (Cb Cp Cd : G) (b p d : list F) (rb rp rd : F) (Y : list F),
      length gs1 = K -> length b = K -> length p = K -> length d = K ->
      Cb = com h1 gs1 b rb -> Cp = com h1 gs1 p rp -> Cd = com h1 gs1 d rd ->
      NoDup Y -> length Y = K -> (forall y, In y Y -> y <> zero) ->
      (forall y, In y Y -> zero_accepts gs1 [Cb; Cp] [Cd; cneg gs1 K] y) ->
      binding_break h1 gs1 \/ forall j, (j < K)%nat -> nth j p zero = nth j b zero * nth j d zero.
    Proof.
      intros Cb Cp Cd b p d rb rp rd Y hg1 hb hp hd eCb eCp eCd hnd hY hy0 hacc; pose proof K_pos as hK.
      set (q := SigmaK.padd (add := add) (hmul b d) (lscale (opp one) p)).
      assert (hq : length q = K) by (unfold q; rewrite SigmaK.padd_length, hmul_length, lscale_length; lia).
      (* At every accepted y, open the four commitments and obtain
         y · eval (b ∘ d - p) y = 0, or a binding break. *)
      assert (hall : forall j, (j < length Y)%nat -> nth j Y zero * eval q (nth j Y zero) = zero \/ binding_break h1 gs1).
      { intros j hj; set (y := nth j Y zero); assert (hy : In y Y) by (apply nth_In; exact hj).
        destruct (hacc y hy) as (cA0 & cBm & cd & xs & a & bb & r & s' & t & hnd' & hlen' & htr).
        destruct (zero_soundness (Hvec := Hvec) (Fdec := Fdec) h1 gs1 [Cb; Cp] [Cd; cneg gs1 K] y cA0 cBm cd xs a bb r s' t
          ltac:(lia) hnd' hlen' htr) as [(A & B & ra & sb & eA & eB & lA & lB & lra & lsb & hAn & hBn & hsum) | hbk];
          [| right; exact hbk].
        cbn [length] in lA, lB, lra, lsb.
        destruct A as [| a0 A]; [discriminate |]; destruct A as [| a1 A]; [discriminate |]; destruct A; [| discriminate].
        destruct B as [| b0 B]; [discriminate |]; destruct B as [| b1 B]; [discriminate |]; destruct B; [| discriminate].
        destruct ra as [| ra0 ra]; [discriminate |]; destruct ra as [| ra1 ra]; [discriminate |]; destruct ra; [| discriminate].
        destruct sb as [| sb0 sb]; [discriminate |]; destruct sb as [| sb1 sb]; [discriminate |]; destruct sb; [| discriminate].
        unfold BayerGroth.com_list in eA, eB; cbn [combine map fst snd] in eA, eB.
        injection eA as eA0 eA1; injection eB as eB0 eB1.
        rewrite eCb in eA0; rewrite eCp in eA1; rewrite eCd in eB0; unfold cneg in eB1.
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 b rb a0 ra0 ltac:(lia)
          (hAn a0 (or_introl eq_refl)) eA0) as [(ea0 & _) | hbk]; [| right; exact hbk].
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 p rp a1 ra1 ltac:(lia)
          (hAn a1 (or_intror (or_introl eq_refl))) eA1) as [(ea1 & _) | hbk]; [| right; exact hbk].
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 d rd b0 sb0 ltac:(lia)
          (hBn b0 (or_introl eq_refl)) eB0) as [(eb0 & _) | hbk]; [| right; exact hbk].
        destruct (open_eq_or_break_len (Hvec := Hvec) (Fdec := Fdec) h1 gs1 (repeat (opp one) K) zero b1 sb1
          ltac:(rewrite repeat_length; lia) (hBn b1 (or_intror (or_introl eq_refl))) eB1) as [(eb1 & _) | hbk]; [| right; exact hbk].
        left. cbn [combine map fold_right fst snd] in hsum. subst a0 a1 b0 b1.
        rewrite star_hmul_eval in hsum by lia.
        rewrite (star_neg_eval y p K hp) in hsum.
        unfold q; rewrite (eval_padd (Hf := vector_space_field)), (eval_lscale (Hf := vector_space_field)).
        etransitivity; [| exact hsum]; field. }
      (* All coefficients of b ∘ d - p vanish. *)
      destruct (forall_or _ _ (length Y) hall) as [hz | hbk]; [| left; exact hbk].
      right; intros j hj.
      pose proof (poly_vanish_mul q Y hnd ltac:(lia) hy0
        (fun y hy => match In_nth Y y zero hy with ex_intro _ i (conj hi e) => eq_ind _ (fun y' => y' * eval q y' = zero) (hz i hi) y e end) j) as e.
      unfold q in e.
      rewrite (nth_padd (Hf := vector_space_field)), (SigmaK.nth_lscale (Hf := vector_space_field)) in e.
      rewrite nth_hmul in e by lia.
      apply (sub_eq_zero (Hf := vector_space_field)).
      transitivity (opp (nth j b zero * nth j d zero + opp one * nth j p zero)); [field | rewrite e; field].
    Qed.

    (** [⟨u, b⟩ - ⟨v, b⟩ = (u_k - v_k) b_k] for [u], [v] differing only at
        [k]. *)
    Lemma dot_differ : forall (u v b : list F) (k : nat), (k < K)%nat -> differ_at k u v -> length b = K ->
      dot u b K - dot v b K = (nth k u zero - nth k v zero) * nth k b zero.
    Proof.
      intros u v b k hk (hu & hv & hagree & hne) hb; unfold dot.
      transitivity (fsum (fun j => (nth j u zero - nth j v zero) * nth j b zero) K).
      + rewrite (fsum_ext (fun j => (nth j u zero - nth j v zero) * nth j b zero)
          (fun j => nth j u zero * nth j b zero + opp one * (nth j v zero * nth j b zero))) by (intros; field).
        rewrite fsum_add, fsum_scale; field.
      + apply (fsum_single (fun j => (nth j u zero - nth j v zero) * nth j b zero) k K hk).
        intros j hj hjk; rewrite hagree by assumption; field.
    Qed.

    (** Bit extraction from the ciphertexts: if [cbeta β₀ cs] decrypts to
        [g ^ ⟨β₀, b₀⟩] and, for every [k], some [β'] differing from [β₀]
        only at [k] has [cbeta β' cs] decrypt to [g ^ ⟨β', b₀⟩], then every
        [c_k] decrypts to [g ^ b₀_k] (dividing the two and taking the
        [(β'_k - β₀_k)]-th root). *)
    Lemma beta_bits : forall (x : F) (cs : list (G * G)) (beta0 b0 : list F),
      h = g ^ x -> length cs = K -> length b0 = K ->
      cdec x (cbeta beta0 cs) = g ^ dot beta0 b0 K ->
      (forall k, (k < K)%nat -> exists beta', differ_at k beta' beta0 /\ cdec x (cbeta beta' cs) = g ^ dot beta' b0 K) ->
      forall k, (k < K)%nat -> cdec x (nth k cs cid) = g ^ nth k b0 zero.
    Proof.
      intros x cs beta0 b0 hh hcs hb0 hdec0 hfam k hk.
      destruct (hfam k hk) as (beta' & hd & hdec').
      pose proof hd as (hu & hv & _ & hne).
      rewrite (cbeta_differ cs k beta' beta0 hcs hk hd) in hdec'.
      rewrite (cdec_cmul (Hvec := Hvec)), (cdec_cpow (Hvec := Hvec)), hdec0 in hdec'.
      assert (e : (cdec x (nth k cs cid)) ^ (nth k beta' zero - nth k beta0 zero) =
        g ^ ((nth k beta' zero - nth k beta0 zero) * nth k b0 zero)).
      { rewrite <-(dot_differ beta' beta0 b0 k hk hd hb0).
        rewrite <-(gop_cancel (Hvec := Hvec) (g ^ dot beta0 b0 K) (cdec x (nth k cs cid) ^ (nth k beta' zero - nth k beta0 zero))).
        rewrite hdec'.
        replace (dot beta' b0 K - dot beta0 b0 K) with (dot beta' b0 K + opp (dot beta0 b0 K)) by field.
        rewrite pow_add, (pow_opp (Hvec := Hvec)); reflexivity. }
      rewrite pow_cmul in e.
      apply (root_unique _ _ (nth k beta' zero - nth k beta0 zero)); [apply sub_neq_zero; exact hne | exact e].
    Qed.

    (** Coefficient extraction for the scalar rows: one base [γ] and one
        variant per coordinate annihilating [e] force [e = 0]. *)
    Lemma gamma_rows : forall (e : nat -> F) (g0 : list F), length g0 = K ->
      fsum (fun j => nth j g0 zero * e j) K = zero ->
      (forall k, (k < K)%nat -> exists g', differ_at k g' g0 /\ fsum (fun j => nth j g' zero * e j) K = zero) ->
      forall k, (k < K)%nat -> e k = zero.
    Proof.
      intros e g0 hg0 h0 hfam k hk; destruct (hfam k hk) as (g' & hd & h').
      exact (rlc_coord e g' g0 k hk hd h' h0).
    Qed.

    (** *** Soundness: decoding to positions *)

    (** Natural-number sum [Σ_(t<k) f t]. *)
    Fixpoint nsum (f : nat -> nat) (k : nat) : nat :=
      match k with 0 => 0 | S k' => (nsum f k' + f k')%nat end.

    (** [natF] commutes with sums. *)
    Lemma fsum_natF : forall (f : nat -> nat) (k : nat), fsum (fun t => natF (f t)) k = natF (nsum f k).
    Proof.
      intros f k; induction k as [| k ih]; [reflexivity |].
      change (fsum (fun t => natF (f t)) (S k)) with (fsum (fun t => natF (f t)) k + natF (f k)).
      cbn [nsum]; rewrite ih, (natF_add (Hvec := Hvec)); reflexivity.
    Qed.

    (** Monotonicity of [nsum]. *)
    Lemma nsum_le : forall (f1 f2 : nat -> nat) (k : nat), (forall t, (t < k)%nat -> (f1 t <= f2 t)%nat) ->
      (nsum f1 k <= nsum f2 k)%nat.
    Proof.
      intros f1 f2 k; induction k as [| k ih]; intros hle; [reflexivity |].
      cbn [nsum]; pose proof (ih (fun t ht => hle t ltac:(lia))); pose proof (hle k ltac:(lia)); lia.
    Qed.

    (** [Σ_(t<k) 2^t = 2^k - 1]. *)
    Lemma nsum_pow2 : forall k, nsum (fun t => Nat.pow 2 t) k = (Nat.pow 2 k - 1)%nat.
    Proof.
      induction k as [| k ih]; [reflexivity |].
      cbn [nsum]; rewrite ih, Nat.pow_succ_r'; pose proof (Nat.pow_nonzero 2 k ltac:(lia)); lia.
    Qed.

    (** [1 ≠ 0] in [F]. *)
    Lemma Fone_neq_zero : one <> zero.
    Proof. exact (@one_neq_zero F (@eq F) zero one (@field_is_zero_neq_one _ _ _ _ _ _ _ _ _ _ vector_space_field) eq_equivalence). Qed.

    (** [bitF a] reads a field bit as a natural number. *)
    Definition bitF (a : F) : nat := if Fdec a one then 1 else 0.

    (** [natF (bitF a) = a] for a bit [a]. *)
    Lemma bitF_natF : forall a, a = zero \/ a = one -> natF (bitF a) = a.
    Proof.
      intros a [-> | ->]; unfold bitF.
      + destruct (Fdec zero one) as [e | _]; [exfalso; apply Fone_neq_zero; symmetry; exact e | reflexivity].
      + destruct (Fdec one one) as [_ | ne]; [apply natF_one | exfalso; apply ne; reflexivity].
    Qed.

    (** [bitF a] is 0 or 1. *)
    Lemma bitF_01 : forall a, bitF a = 0%nat \/ bitF a = 1%nat.
    Proof. intros a; unfold bitF; destruct (Fdec a one); [right | left]; reflexivity. Qed.

    (** [xbit X t k] is bit [t] of cell [k]; [nv X k] the natural number
        they encode. *)
    Definition xbit (X : list F) (t k : nat) : nat := bitF (nth (t * K + k)%nat X zero).
    Definition nv (X : list F) (k : nat) : nat := nsum (fun t => (Nat.pow 2 t * xbit X t k)%nat) L.

    (** For bit vectors, [vbits X k = natF (nv X k)]. *)
    Lemma vbits_nv : forall (X : list F) (k : nat), (k < K)%nat ->
      (forall j, (j < NX)%nat -> nth j X zero = zero \/ nth j X zero = one) ->
      vbits X k = natF (nv X k).
    Proof.
      intros X k hk hX; unfold vbits, nv; rewrite <-fsum_natF; apply fsum_ext; intros t ht.
      unfold pow2F; rewrite (natF_mul (Hvec := Hvec)); f_equal; symmetry; apply bitF_natF; apply hX.
      pose proof K_pos; unfold NX; nia.
    Qed.

    (** [nv X k < 2^L]. *)
    Lemma nv_lt : forall (X : list F) (k : nat), (nv X k < Nat.pow 2 L)%nat.
    Proof.
      intros X k; unfold nv.
      pose proof (nsum_le (fun t => (Nat.pow 2 t * xbit X t k)%nat) (fun t => Nat.pow 2 t) L
        (fun t _ => ltac:(destruct (bitF_01 (nth (t * K + k)%nat X zero)) as [e | e]; unfold xbit; rewrite e; lia))) as hle.
      rewrite nsum_pow2 in hle; pose proof (Nat.pow_nonzero 2 L ltac:(lia)); lia.
    Qed.

    (** [posn b X i] decodes a position for candidate [i] from the pair
        [(0, i)] (cell [i]): it is [2^L + δ_(0,i)], i.e.
        [2^L + nv + 1] if [b_(0,i) = 1] and [2^L - nv] otherwise. Positions
        are only determined up to the common offset [s_0]; the shift [2^L]
        makes them natural numbers. *)
    Definition posn (b X : list F) (i : nat) : nat :=
      if Nat.eqb (bitF (nth i b zero)) 1 then (nv X i + 1 + Nat.pow 2 L)%nat else (Nat.pow 2 L - nv X i)%nat.

    (** [posn ≤ 2 · 2^L]. *)
    Lemma posn_le : forall b X i, (posn b X i <= 2 * Nat.pow 2 L)%nat.
    Proof. intros; unfold posn; pose proof (nv_lt X i); destruct (Nat.eqb _ _); lia. Qed.

    (** Row-major cell indices. *)
    Lemma idx_div_mod : forall i j, (i < m)%nat -> (j < m)%nat ->
      ((i * m + j) / m = i)%nat /\ ((i * m + j) mod m = j)%nat.
    Proof.
      intros i j hi hj; split.
      + rewrite Nat.div_add_l by lia; rewrite Nat.div_small by lia; lia.
      + rewrite Nat.add_comm, Nat.Div0.mod_add; apply Nat.mod_small; exact hj.
    Qed.

    (** Decoding. Given openings [s, d, b, p, X] with [d = M s], [b] and [X]
        bit vectors, [p = b ∘ d] and the second scalar row
        [vbits X + d - 2p + b = 0], and characteristic above [3 · 2^L + 2]:
        for all candidates [i], [j], [b_(i,j) = [posn i < posn j] ].

        Proof idea: the row equation determines [d_(0,i)] from the bits,
        hence [natF (posn i) = d_(0,i) + 2^L]; then
        [d_(i,j) = posn j - posn i] in [F]; finally the row equation for
        [(i, j)] becomes an equation between naturals below
        [3 · 2^L + 2], which [natF_injective] turns into [nv + posn j =
        posn i] (if [b = 0]) or [nv + 1 + posn i = posn j] (if [b = 1]). *)
    Lemma decode_positions : forall (s d b p X : list F),
      length s = m -> length d = K -> length b = K -> length p = K -> length X = NX ->
      natF_injective (3 * Nat.pow 2 L + 2) ->
      (forall k, (k < K)%nat -> nth k d zero = nth (k mod m) s zero - nth (k / m) s zero) ->
      (forall j, (j < K)%nat -> nth j b zero = zero \/ nth j b zero = one) ->
      (forall j, (j < NX)%nat -> nth j X zero = zero \/ nth j X zero = one) ->
      (forall k, (k < K)%nat -> nth k p zero = nth k b zero * nth k d zero) ->
      (forall k, (k < K)%nat -> vbits X k + nth k d zero - (one + one) * nth k p zero + nth k b zero = zero) ->
      forall i j, (i < m)%nat -> (j < m)%nat ->
        nth (i * m + j)%nat b zero = natF (if Nat.ltb (posn b X i) (posn b X j) then 1 else 0).
    Proof.
      intros s d b p X hs hd hb hp hX hinj hdm hbb hXb hpp hrow.
      pose proof K_pos as hK; pose proof m_le_K as hmle.
      assert (hmK : forall i j, (i < m)%nat -> (j < m)%nat -> (i * m + j < K)%nat) by (intros; unfold K; nia).
      (* The second scalar row, with the bits read as naturals. *)
      assert (hv : forall k, (k < K)%nat ->
        natF (nv X k) + nth k d zero - (one + one) * (natF (bitF (nth k b zero)) * nth k d zero) + natF (bitF (nth k b zero)) = zero).
      { intros k hk; rewrite bitF_natF by (apply hbb; exact hk); rewrite <-hpp by exact hk; rewrite <-vbits_nv by assumption.
        apply hrow; exact hk. }
      (* Positions from the cells (0, i): posn i = 2^L + d_(0,i) in F. *)
      assert (hpos : forall i, (i < m)%nat -> natF (posn b X i) = nth i d zero + natF (Nat.pow 2 L)).
      { intros i hi.
        assert (hki : (i < K)%nat) by lia.
        pose proof (hv i hki) as e; pose proof (nv_lt X i) as hlt.
        unfold posn; destruct (bitF_01 (nth i b zero)) as [e0 | e1].
        + rewrite e0 in e |- *; cbn [Nat.eqb]; cbn [nat_to_F] in e.
          rewrite (natF_sub (Hvec := Hvec)) by lia.
          transitivity (natF (Nat.pow 2 L) - (natF (nv X i) + nth i d zero - (one + one) * (zero * nth i d zero) + zero) + nth i d zero);
            [field | rewrite e; field].
        + rewrite e1 in e |- *; cbn [Nat.eqb]; rewrite natF_one in e.
          rewrite !(natF_add (Hvec := Hvec)), natF_one.
          assert (hd1 : nth i d zero = natF (nv X i) + one).
          { transitivity (natF (nv X i) + one -
              (natF (nv X i) + nth i d zero - (one + one) * (one * nth i d zero) + one)); [field | rewrite e; field]. }
          rewrite hd1; field. }
      (* d_(i,j) = posn j - posn i, using d = M s twice. *)
      assert (hdij : forall i j, (i < m)%nat -> (j < m)%nat ->
        nth (i * m + j)%nat d zero = natF (posn b X j) - natF (posn b X i)).
      { intros i j hi hj.
        rewrite hdm by (apply hmK; assumption).
        destruct (idx_div_mod i j hi hj) as (e1 & e2); rewrite e1, e2.
        rewrite hpos, hpos by assumption.
        rewrite hdm with (k := i) by lia; rewrite hdm with (k := j) by lia.
        destruct (idx_div_mod 0 i ltac:(lia) hi) as (e3 & e4); destruct (idx_div_mod 0 j ltac:(lia) hj) as (e5 & e6).
        cbn [Nat.mul Nat.add] in e3, e4, e5, e6; rewrite e3, e4, e5, e6; field. }
      intros i j hi hj.
      pose proof (hv (i * m + j)%nat (hmK i j hi hj)) as e; rewrite hdij in e by assumption.
      pose proof (nv_lt X (i * m + j)) as hlt; pose proof (posn_le b X i) as hpi; pose proof (posn_le b X j) as hpj.
      (* Decide b_(i,j) by moving the row equation into bounded naturals. *)
      destruct (bitF_01 (nth (i * m + j)%nat b zero)) as [e0 | e1].
      +
        rewrite <-(bitF_natF (nth (i * m + j)%nat b zero) (hbb _ (hmK i j hi hj))), e0.
        rewrite e0 in e; cbn [nat_to_F] in e.
        assert (he : natF (nv X (i * m + j)%nat + posn b X j) = natF (posn b X i)).
        { rewrite (natF_add (Hvec := Hvec)). transitivity (natF (nv X (i * m + j)%nat) + (natF (posn b X j) - natF (posn b X i)) -
            (one + one) * (zero * (natF (posn b X j) - natF (posn b X i))) + zero + natF (posn b X i)); [field | rewrite e; field]. }
        apply hinj in he; [| lia | lia].
        destruct (Nat.ltb (posn b X i) (posn b X j)) eqn:hltb; [apply Nat.ltb_lt in hltb; lia | reflexivity].
      +
        rewrite <-(bitF_natF (nth (i * m + j)%nat b zero) (hbb _ (hmK i j hi hj))), e1.
        rewrite e1 in e; rewrite natF_one in e.
        assert (he : natF (nv X (i * m + j)%nat + 1 + posn b X i) = natF (posn b X j)).
        { rewrite !(natF_add (Hvec := Hvec)), natF_one.
          transitivity (natF (nv X (i * m + j)%nat) + (natF (posn b X j) - natF (posn b X i)) -
            (one + one) * (one * (natF (posn b X j) - natF (posn b X i))) + one + natF (posn b X j)); [field | rewrite e; field]. }
        apply hinj in he; [| lia | lia].
        destruct (Nat.ltb (posn b X i) (posn b X j)) eqn:hltb; [reflexivity | apply Nat.ltb_ge in hltb; lia].
    Qed.

    (** *** Special soundness *)

    (** Special soundness of the batched ballot, in rewinding form. Given:

        - [h = g ^ x], [L ≥ 1], keys of lengths [K], [NX], and
          characteristic above [3 · 2^L + 2];
        - the linear proof accepted (one announcement, two challenges
          [c₀ ≠ c₁]) on base coefficients [β₀, γ₁₀, γ₂₀] and on, for each
          [k], a variant of each of them differing only at [k];
        - the three zero arguments accepted at [K], [NX], [K] distinct
          non-zero [y] respectively;

        then [gs1] or [gs2] admits two openings of one commitment, or there
        are positions [pos_i ≤ 2 · 2^L] such that every ciphertext
        [c_(i·m+j)] decrypts to [g ^ [pos_i < pos_j] ].

        Proof outline: extract a base witness [w₀] ([lin_open]); every
        other accepted tuple opens the same vectors ([open_agree]); the
        [β] family makes each ciphertext decrypt to its committed bit
        ([beta_bits]); the [γ] families make both scalar rows vanish
        coordinatewise ([gamma_rows]); the zero arguments give [p = b ∘ d]
        and bit vectors ([zero_prod_open], [zero_bits_open]); finally
        [decode_positions]. *)
    Theorem ballot2_sound : forall (x : F) (bt : ballot2) (beta0 g10 g20 : list F) (c0 c1 : F) (Y1 Y2 Y3 : list F),
      h = g ^ x -> (1 <= L)%nat -> length gs1 = K -> length gs2 = NX -> natF_injective (3 * Nat.pow 2 L + 2) ->
      length (b2_cs bt) = K -> length beta0 = K -> length g10 = K -> length g20 = K -> c0 <> c1 ->
      lin_accepts beta0 g10 g20 bt c0 c1 ->
      (forall k, (k < K)%nat -> exists beta', differ_at k beta' beta0 /\ lin_accepts beta' g10 g20 bt c0 c1) ->
      (forall k, (k < K)%nat -> exists g1', differ_at k g1' g10 /\ lin_accepts beta0 g1' g20 bt c0 c1) ->
      (forall k, (k < K)%nat -> exists g2', differ_at k g2' g20 /\ lin_accepts beta0 g10 g2' bt c0 c1) ->
      NoDup Y1 -> length Y1 = K -> (forall y, In y Y1 -> y <> zero) ->
      (forall y, In y Y1 -> zero_accepts gs1 [b2_Cb bt; b2_Cp bt] [b2_Cd bt; cneg gs1 K] y) ->
      NoDup Y2 -> length Y2 = NX -> (forall y, In y Y2 -> y <> zero) ->
      (forall y, In y Y2 -> zero_accepts gs2 [b2_CX bt] [gop (b2_CX bt) (cneg gs2 NX)] y) ->
      NoDup Y3 -> length Y3 = K -> (forall y, In y Y3 -> y <> zero) ->
      (forall y, In y Y3 -> zero_accepts gs1 [b2_Cb bt] [gop (b2_Cb bt) (cneg gs1 K)] y) ->
      binding_break h1 gs1 \/ binding_break h1 gs2 \/
      exists (pos : Vector.t nat m),
        (forall i, (Vector.nth pos i <= 2 * Nat.pow 2 L)%nat) /\
        forall i j : Fin.t m,
          cdec x (nth (fin_idx i * m + fin_idx j) (b2_cs bt) cid) =
          g ^ (if Nat.ltb (Vector.nth pos i) (Vector.nth pos j) then one else zero).
    Proof.
      intros x bt beta0 g10 g20 c0 c1 Y1 Y2 Y3 hh hL hg1 hg2 hinj hcs hb0l hg10 hg20 hc hacc0 hfamb hfam1 hfam2
        hnd1 hY1 hy01 hz1 hnd2 hY2 hy02 hz2 hnd3 hY3 hy03 hz3.
      pose proof K_pos as hK; pose proof m_le_K as hmle.
      assert (hNX : (1 <= NX)%nat) by (unfold NX; nia).
      (* The base witness w0 and its openings. *)
      destruct (lin_open beta0 g10 g20 bt c0 c1 hc hacc0) as (w0 & hw0 & hphi0).
      destruct (phi_target_open beta0 g10 g20 bt w0 hphi0) as (eCs & eCd & eCb & eCp & eCX & ecb0 & erow1 & erow2).
      set (s0 := wslice w0 oS m) in *; set (d0 := wslice w0 oD K) in *; set (b0 := wslice w0 oB K) in *;
      set (p0 := wslice w0 oP K) in *; set (X0 := wslice w0 oX NX) in *.
      assert (hs0 : length s0 = m) by apply wslice_length.
      assert (hd0 : length d0 = K) by apply wslice_length.
      assert (hb0 : length b0 = K) by apply wslice_length.
      assert (hp0 : length p0 = K) by apply wslice_length.
      assert (hX0 : length X0 = NX) by apply wslice_length.
      assert (hwat : forall w k, (k < K)%nat ->
        wat w (oD + k) = nth k (wslice w oD K) zero /\ wat w (oB + k) = nth k (wslice w oB K) zero /\
        wat w (oP + k) = nth k (wslice w oP K) zero /\
        wat w (oS + k mod m) = nth (k mod m) (wslice w oS m) zero /\ wat w (oS + k / m) = nth (k / m) (wslice w oS m) zero).
      { intros w k hk; destruct (kdm_lt k hk) as (hd & hm); unfold wat; repeat split; symmetry; apply nth_wslice; assumption. }
      (* Any other accepted coefficient tuple opens the same vectors, or a
         key is broken. *)
      assert (hagree : forall beta g1 g2, length beta = K -> lin_accepts beta g1 g2 bt c0 c1 ->
        binding_break h1 gs1 \/ binding_break h1 gs2 \/
        exists w, length w = W /\ wslice w oS m = s0 /\ wslice w oD K = d0 /\ wslice w oB K = b0 /\
          wslice w oP K = p0 /\ wslice w oX NX = X0 /\
          cbeta beta (b2_cs bt) = enc g h (dot beta b0 K) (wat w (oR + 5)) /\
          fsum (fun k => nth k g1 zero * (wat w (oD + k) - (wat w (oS + k mod m) - wat w (oS + k / m)))) K = zero /\
          fsum (fun k => nth k g2 zero * (vbits (wslice w oX NX) k + wat w (oD + k) - (one + one) * wat w (oP + k) + wat w (oB + k))) K = zero).
      { intros beta g1 g2 hbl hacc.
        destruct (lin_open beta g1 g2 bt c0 c1 hc hacc) as (w & hw & hphi).
        destruct (phi_target_open beta g1 g2 bt w hphi) as (eCs' & eCd' & eCb' & eCp' & eCX' & ecb & er1 & er2).
        destruct (open_agree w w0 hg1 hg2 (eq_trans (eq_sym eCs') eCs) (eq_trans (eq_sym eCd') eCd)
          (eq_trans (eq_sym eCb') eCb) (eq_trans (eq_sym eCp') eCp) (eq_trans (eq_sym eCX') eCX))
          as [hb | [hb | (es & ed & eb & ep & ex)]]; [left; exact hb | right; left; exact hb |].
        right; right; exists w; repeat split; try assumption.
        rewrite ecb, eb; reflexivity. }
      (* The beta family: every ciphertext decrypts to its committed bit. *)
      assert (hbits : binding_break h1 gs1 \/ binding_break h1 gs2 \/
        forall k, (k < K)%nat -> cdec x (nth k (b2_cs bt) cid) = g ^ nth k b0 zero).
      { destruct (forall_or (fun k => exists beta', differ_at k beta' beta0 /\ cdec x (cbeta beta' (b2_cs bt)) = g ^ dot beta' b0 K)
          (binding_break h1 gs1 \/ binding_break h1 gs2) K) as [hfam | [hb | hb]];
          [| right; right | left; exact hb | right; left; exact hb].
        - intros k hk; destruct (hfamb k hk) as (beta' & hd & hacc).
          destruct (hagree beta' g10 g20 (proj1 hd) hacc) as [hb | [hb | (w & _ & _ & _ & _ & _ & _ & ecb & _ & _)]];
            [right; left; exact hb | right; right; exact hb |].
          left; exists beta'; split; [exact hd |]. rewrite ecb; apply (cdec_enc (Hvec := Hvec)); exact hh.
        - apply (beta_bits x (b2_cs bt) beta0 b0 hh hcs hb0); [| exact hfam].
          rewrite ecb0; apply (cdec_enc (Hvec := Hvec)); exact hh. }
      set (e1 := fun k => nth k d0 zero - (nth (k mod m) s0 zero - nth (k / m) s0 zero)).
      set (e2 := fun k => vbits X0 k + nth k d0 zero - (one + one) * nth k p0 zero + nth k b0 zero).
      assert (hrow_w : forall w g1 g2, wslice w oS m = s0 -> wslice w oD K = d0 -> wslice w oB K = b0 -> wslice w oP K = p0 ->
        wslice w oX NX = X0 ->
        (fsum (fun k => nth k g1 zero * (wat w (oD + k) - (wat w (oS + k mod m) - wat w (oS + k / m)))) K = zero ->
          fsum (fun k => nth k g1 zero * e1 k) K = zero) /\
        (fsum (fun k => nth k g2 zero * (vbits (wslice w oX NX) k + wat w (oD + k) - (one + one) * wat w (oP + k) + wat w (oB + k))) K = zero ->
          fsum (fun k => nth k g2 zero * e2 k) K = zero)).
      { intros w g1 g2 es ed eb ep ex; split; (intros hr; etransitivity; [| exact hr]; apply fsum_ext; intros k hk;
          destruct (hwat w k hk) as (a1 & a2 & a3 & a4 & a5); unfold e1, e2;
          rewrite ?a1, ?a2, ?a3, ?a4, ?a5, ?es, ?ed, ?eb, ?ep, ?ex; reflexivity). }
      (* The gamma families: both scalar rows vanish coordinatewise. *)
      assert (hrows : binding_break h1 gs1 \/ binding_break h1 gs2 \/
        ((forall k, (k < K)%nat -> e1 k = zero) /\ (forall k, (k < K)%nat -> e2 k = zero))).
      { destruct (hrow_w w0 g10 g20 eq_refl eq_refl eq_refl eq_refl eq_refl) as (hc1 & hc2).
        specialize (hc1 erow1); specialize (hc2 erow2).
        destruct (forall_or (fun k => exists g', differ_at k g' g10 /\ fsum (fun j => nth j g' zero * e1 j) K = zero)
          (binding_break h1 gs1 \/ binding_break h1 gs2) K) as [hf1 | [hb | hb]];
          [| | left; exact hb | right; left; exact hb].
        - intros k hk; destruct (hfam1 k hk) as (g1' & hd & hacc).
          destruct (hagree beta0 g1' g20 hb0l hacc) as [hb | [hb | (w & _ & es & ed & eb & ep & ex & _ & er1 & _)]];
            [right; left; exact hb | right; right; exact hb |].
          left; exists g1'; split; [exact hd | exact (proj1 (hrow_w w g1' g20 es ed eb ep ex) er1)].
        - destruct (forall_or (fun k => exists g', differ_at k g' g20 /\ fsum (fun j => nth j g' zero * e2 j) K = zero)
            (binding_break h1 gs1 \/ binding_break h1 gs2) K) as [hf2 | [hb | hb]];
            [| | left; exact hb | right; left; exact hb].
          + intros k hk; destruct (hfam2 k hk) as (g2' & hd & hacc).
            destruct (hagree beta0 g10 g2' hb0l hacc) as [hb | [hb | (w & _ & es & ed & eb & ep & ex & _ & _ & er2)]];
              [right; left; exact hb | right; right; exact hb |].
            left; exists g2'; split; [exact hd | exact (proj2 (hrow_w w g10 g2' es ed eb ep ex) er2)].
          + right; right; split.
            * exact (gamma_rows e1 g10 hg10 hc1 hf1).
            * exact (gamma_rows e2 g20 hg20 hc2 hf2). }
      (* The zero arguments: p = b ∘ d, X and b are bit vectors. *)
      destruct (zero_prod_open (b2_Cb bt) (b2_Cp bt) (b2_Cd bt) b0 p0 d0 _ _ _ Y1 hg1 hb0 hp0 hd0 eCb eCp eCd hnd1 hY1 hy01 hz1)
        as [hb | hprod]; [left; exact hb |].
      destruct (zero_bits_open gs2 NX (b2_CX bt) X0 _ Y2 hNX hg2 hX0 eCX hnd2 hY2 hy02 hz2) as [hb | hXbits]; [right; left; exact hb |].
      destruct (zero_bits_open gs1 K (b2_Cb bt) b0 _ Y3 hK hg1 hb0 eCb hnd3 hY3 hy03 hz3) as [hb | hbbits]; [left; exact hb |].
      destruct hbits as [hb | [hb | hbits]]; [left; exact hb | right; left; exact hb |].
      destruct hrows as [hb | [hb | (he1 & he2)]]; [left; exact hb | right; left; exact hb |].
      assert (hdm : forall k, (k < K)%nat -> nth k d0 zero = nth (k mod m) s0 zero - nth (k / m) s0 zero).
      { intros k hk; apply (sub_eq_zero (Hf := vector_space_field)); exact (he1 k hk). }
      (* Decode positions from the openings. *)
      pose proof (decode_positions s0 d0 b0 p0 X0 hs0 hd0 hb0 hp0 hX0 hinj hdm hbbits hXbits hprod he2) as hdec.
      right; right.
      exists (Vector.map (fun i => posn b0 X0 (fin_idx i)) (fin_enum m)); split.
      + intro i; rewrite (Vector.nth_map _ _ i i eq_refl), fin_enum_nth; apply posn_le.
      + intros i j; rewrite (Vector.nth_map _ _ i i eq_refl), (Vector.nth_map _ _ j j eq_refl), !fin_enum_nth.
        pose proof (fin_idx_lt m i) as hi; pose proof (fin_idx_lt m j) as hj.
        rewrite hbits by (unfold K; nia).
        rewrite hdec by assumption.
        destruct (Nat.ltb (posn b0 X0 (fin_idx i)) (posn b0 X0 (fin_idx j))); [rewrite natF_one | cbn [nat_to_F]]; reflexivity.
    Qed.

    (** The rewinding hypotheses of [ballot2_sound] packaged as one
        predicate on a ballot (used by [Backend/SchulzeBatchedTally.v]). *)
    Definition ballot2_rewound (bt : ballot2) : Prop :=
      length (b2_cs bt) = K /\
      exists (beta0 g10 g20 : list F) (c0 c1 : F) (Y1 Y2 Y3 : list F),
        length beta0 = K /\ length g10 = K /\ length g20 = K /\ c0 <> c1 /\
        lin_accepts beta0 g10 g20 bt c0 c1 /\
        (forall k, (k < K)%nat -> exists beta', differ_at k beta' beta0 /\ lin_accepts beta' g10 g20 bt c0 c1) /\
        (forall k, (k < K)%nat -> exists g1', differ_at k g1' g10 /\ lin_accepts beta0 g1' g20 bt c0 c1) /\
        (forall k, (k < K)%nat -> exists g2', differ_at k g2' g20 /\ lin_accepts beta0 g10 g2' bt c0 c1) /\
        NoDup Y1 /\ length Y1 = K /\ (forall y, In y Y1 -> y <> zero) /\
        (forall y, In y Y1 -> zero_accepts gs1 [b2_Cb bt; b2_Cp bt] [b2_Cd bt; cneg gs1 K] y) /\
        NoDup Y2 /\ length Y2 = NX /\ (forall y, In y Y2 -> y <> zero) /\
        (forall y, In y Y2 -> zero_accepts gs2 [b2_CX bt] [gop (b2_CX bt) (cneg gs2 NX)] y) /\
        NoDup Y3 /\ length Y3 = K /\ (forall y, In y Y3 -> y <> zero) /\
        (forall y, In y Y3 -> zero_accepts gs1 [b2_Cb bt] [gop (b2_Cb bt) (cneg gs1 K)] y).

    (** [ballot2_sound] restated on the matrix [ballot2_bits]. *)
    Corollary ballot2_sound_bits : forall (x : F) (bt : ballot2),
      h = g ^ x -> (1 <= L)%nat -> length gs1 = K -> length gs2 = NX -> natF_injective (3 * Nat.pow 2 L + 2) ->
      ballot2_rewound bt ->
      binding_break h1 gs1 \/ binding_break h1 gs2 \/
      exists (pos : Vector.t nat m),
        (forall i, (Vector.nth pos i <= 2 * Nat.pow 2 L)%nat) /\
        forall i j : Fin.t m, cdec x (Vector.nth (Vector.nth (ballot2_bits bt) i) j) =
          g ^ (if Nat.ltb (Vector.nth pos i) (Vector.nth pos j) then one else zero).
    Proof.
      intros x bt hh hL hg1 hg2 hinj (hcs & beta0 & g10 & g20 & c0 & c1 & Y1 & Y2 & Y3 & hb0 & hg10 & hg20 & hc & hacc &
        hf1 & hf2 & hf3 & hnd1 & hY1 & hy1 & hz1 & hnd2 & hY2 & hy2 & hz2 & hnd3 & hY3 & hy3 & hz3).
      destruct (ballot2_sound x bt beta0 g10 g20 c0 c1 Y1 Y2 Y3 hh hL hg1 hg2 hinj hcs hb0 hg10 hg20 hc hacc hf1 hf2 hf3
        hnd1 hY1 hy1 hz1 hnd2 hY2 hy2 hz2 hnd3 hY3 hy3 hz3) as [hb | [hb | (pos & hpos & hdec)]];
        [left; exact hb | right; left; exact hb | right; right].
      exists pos; split; [exact hpos |].
      intros i j; unfold ballot2_bits.
      rewrite (Vector.nth_map _ _ i i eq_refl), (Vector.nth_map _ _ j j eq_refl), !fin_enum_nth.
      apply hdec.
    Qed.

    (** *** Special honest-verifier zero knowledge

        Randomness is drawn uniformly from the list [lf] enumerating [F].
        The commitment keys are assumed to have known discrete logarithms
        [γ1], [γ2] in base [h1] (as in the library's zero-argument
        simulator); this is a property of the analysis, not something the
        simulator needs to know in deployment. *)
    Import Distr.
    Section ZK2.
      (** The enumeration [lf] of [F] and the discrete logarithms [γ1],
          [γ2] of the keys in base [h1]. *)
      Context (lf : list F) (Hlfn : lf <> []).
      Context (γ1 γ2 : list F).
      Hypothesis hg1 : length gs1 = K.
      Hypothesis hg2 : length gs2 = NX.
      Hypothesis hγ1l : length γ1 = K.
      Hypothesis hγ2l : length γ2 = NX.
      Hypothesis hγ1 : forall j, (j < K)%nat -> nth j gs1 gid = h1 ^ (nth j γ1 zero).
      Hypothesis hγ2 : forall j, (j < NX)%nat -> nth j gs2 gid = h1 ^ (nth j γ2 zero).

      (** The real and simulated distributions of the linear proof and of
          the zero argument, with implicit arguments fixed. *)
      Local Notation lin_real_distribution := (lin_real_distribution (add := add) (mul := mul)).
      Local Notation lin_sim_distribution := (lin_sim_distribution (vopp := st_opp) (vadd := st_add) (smul := st_smul)).
      Local Notation zero_real_distribution := (BayerGrothZK.zero_real_distribution (zero := zero) (one := one)
        (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)).
      Local Notation zero_sim_distribution := (zero_sim_distribution (zero := zero) (one := one) (add := add) (mul := mul)
        (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow)).
      Local Notation zdot := (BayerGrothZK.dot (zero := zero) (add := add) (mul := mul)).

      (** [Bind] respects pointwise equality of the continuation. *)
      Lemma bind_ext : forall {A B : Type} (d : dist A) (f f' : A -> dist B),
        (forall a, f a = f' a) -> Bind d f = Bind d f'.
      Proof. intros A B d f f' e; induction d as [| (a & p) d ih]; [reflexivity | cbn; rewrite e, ih; reflexivity]. Qed.

      (** [rand2_of r t a l1 l2 l3] assembles the voter randomness from six
          independent uniform draws: the [K] encryption randomnesses [r],
          the five commitment randomnesses [t], the linear announcement
          randomness [a], and the zero-argument randomness [l1], [l2], [l3]
          in the library's layout. *)
      Definition rand2_of (r t a l1 l2 l3 : list F) : rand2 :=
        mk_rand2 r (nth 0 t zero) (nth 1 t zero) (nth 2 t zero) (nth 3 t zero) (nth 4 t zero) a
          (slice l1 0 (length gs1)) (slice l1 (length gs1) (length gs1)) (nth (2 * length gs1) l1 zero) (nth (2 * length gs1 + 1) l1 zero)
          (slice l1 (2 * length gs1 + 2) 3) (slice l1 (2 * length gs1 + 3 + 2) 1)
          (slice l2 0 (length gs2)) (slice l2 (length gs2) (length gs2)) (nth (2 * length gs2) l2 zero) (nth (2 * length gs2 + 1) l2 zero)
          (slice l2 (2 * length gs2 + 2) 2) (slice l2 (2 * length gs2 + 3 + 1) 0)
          (slice l3 0 (length gs1)) (slice l3 (length gs1) (length gs1)) (nth (2 * length gs1) l3 zero) (nth (2 * length gs1 + 1) l3 zero)
          (slice l3 (2 * length gs1 + 2) 2) (slice l3 (2 * length gs1 + 3 + 1) 0).

      (** The honest ciphertexts for randomness [r]. *)
      Definition honest_cs (sn : list nat) (r : list F) : list (G * G) :=
        map (fun k => enc g h (natF (pos_bit sn k)) (nth k r zero)) (seq 0 K).

      (** The honest ballot as a distribution over the voter's randomness. *)
      Definition ballot2_real_dist (ch : chal2) (sn : list nat) : dist ballot2 :=
        Bind (rand lf Hlfn K) (fun r => Bind (rand lf Hlfn 5) (fun t => Bind (rand lf Hlfn W) (fun a =>
        Bind (rand lf Hlfn (zR gs1 2)) (fun l1 => Bind (rand lf Hlfn (zR gs2 1)) (fun l2 => Bind (rand lf Hlfn (zR gs1 1)) (fun l3 =>
          Ret (encrypt_ballot2 ch sn (rand2_of r t a l1 l2 l3)))))))).

      (** The linear-proof statement from the ciphertexts and a list [C] of
          five commitments. *)
      Definition target_of (beta : list F) (cs : list (G * G)) (C : list G) : St :=
        let cb := cbeta beta cs in
        (vec7 (nth 0 C gid) (nth 1 C gid) (nth 2 C gid) (nth 3 C gid) (nth 4 C gid) (fst cb) (snd cb), vec2 zero zero).

      (** The simulator of the proofs, from the ciphertexts, the five
          commitments and the challenges: the library simulators for the
          linear proof and the three zero arguments. *)
      Definition sim_proofs (ch : chal2) (cs : list (G * G)) (C : list G) : dist ballot2 :=
        let cS := nth 0 C gid in let cD := nth 1 C gid in let cB := nth 2 C gid in
        let cP := nth 3 C gid in let cX := nth 4 C gid in
        Bind (lin_sim_distribution W (phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch)) lf Hlfn (target_of (ch_beta ch) cs C) (ch_c ch)) (fun lp =>
        Bind (zero_sim_distribution h1 gs1 (ch_y1 ch) (ch_x1 ch) 2 lf Hlfn [cB; cP] [cD; cneg gs1 K]) (fun z1 =>
        Bind (zero_sim_distribution h1 gs2 (ch_y2 ch) (ch_x2 ch) 1 lf Hlfn [cX] [gop cX (cneg gs2 NX)]) (fun z2 =>
        Bind (zero_sim_distribution h1 gs1 (ch_y3 ch) (ch_x3 ch) 1 lf Hlfn [cB] [gop cB (cneg gs1 K)]) (fun z3 =>
          Ret (mk_ballot2 cs cS cD cB cP cX lp z1 z2 z3))))).

      (** The ballot simulator: five uniform group elements [h1 ^ u] as
          commitments, then [sim_proofs]. *)
      Definition ballot2_sim_dist (ch : chal2) (cs : list (G * G)) : dist ballot2 :=
        Bind (rand lf Hlfn 5) (fun u => sim_proofs ch cs (map (fun e => h1 ^ e) u)).

      (** The honest commitments for commitment randomness [t]. *)
      Definition com_vals (sn : list nat) (t : list F) : list G :=
        [com h1 gs1 (hon_s sn) (nth 0 t zero); com h1 gs1 (hon_d sn) (nth 1 t zero);
         com h1 gs1 (hon_b sn) (nth 2 t zero); com h1 gs1 (hon_p sn) (nth 3 t zero);
         com h1 gs2 (hon_X sn) (nth 4 t zero)].

      (** The honest proofs, given the ciphertext randomness [r] and the
          commitment randomness [t], as a distribution over the remaining
          prover randomness. *)
      Definition real_proofs (ch : chal2) (sn : list nat) (r t : list F) : dist ballot2 :=
        let w := hon_w (ch_beta ch) sn (rand2_of r t [] [] [] []) in
        Bind (lin_real_distribution W (phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch)) lf Hlfn w (ch_c ch)) (fun lp =>
        Bind (zero_real_distribution h1 gs1 [hon_b sn; hon_p sn] [hon_d sn; repeat (opp one) K]
                [nth 2 t zero; nth 3 t zero] [nth 1 t zero; zero] (ch_y1 ch) (ch_x1 ch) 2 lf Hlfn) (fun z1 =>
        Bind (zero_real_distribution h1 gs2 [hon_X sn] [ladd (hon_X sn) (repeat (opp one) NX)]
                [nth 4 t zero] [nth 4 t zero] (ch_y2 ch) (ch_x2 ch) 1 lf Hlfn) (fun z2 =>
        Bind (zero_real_distribution h1 gs1 [hon_b sn] [ladd (hon_b sn) (repeat (opp one) K)]
                [nth 2 t zero] [nth 2 t zero] (ch_y3 ch) (ch_x3 ch) 1 lf Hlfn) (fun z3 =>
          Ret (mk_ballot2 (honest_cs sn r) (nth 0 (com_vals sn t) gid) (nth 1 (com_vals sn t) gid)
                 (nth 2 (com_vals sn t) gid) (nth 3 (com_vals sn t) gid) (nth 4 (com_vals sn t) gid) lp z1 z2 z3))))).

      (** The real distribution factors as ciphertext randomness, then
          commitment randomness, then [real_proofs] (monad laws). *)
      Lemma real_dist_proofs : forall ch sn,
        ballot2_real_dist ch sn = Bind (rand lf Hlfn K) (fun r => Bind (rand lf Hlfn 5) (fun t => real_proofs ch sn r t)).
      Proof.
        intros ch sn; unfold ballot2_real_dist, real_proofs, lin_real_distribution, BayerGrothZK.zero_real_distribution.
        apply bind_ext; intro r; apply bind_ext; intro t.
        rewrite !bind_assoc; apply bind_ext; intro a. rewrite bind_ret_left.
        rewrite !bind_assoc; apply bind_ext; intro l1. rewrite bind_ret_left.
        rewrite !bind_assoc; apply bind_ext; intro l2. rewrite bind_ret_left.
        rewrite !bind_assoc; apply bind_ext; intro l3. rewrite bind_ret_left.
        reflexivity.
      Qed.

      (** Given the ciphertexts and commitments, the real proofs are a
          permutation of the simulated ones: [lin_shvzk], then [zero_shvzk]
          three times, layer by layer. *)
      Lemma real_proofs_perm : forall (ch : chal2) (sn : list nat) (r t : list F),
        NoDup lf -> (forall v : F, In v lf) ->
        length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
        length (ch_beta ch) = K -> length t = 5%nat ->
        Permutation (real_proofs ch sn r t) (sim_proofs ch (honest_cs sn r) (com_vals sn t)).
      Proof.
        intros ch sn r t hnd hall hsn hs hL hb ht.
        destruct (hon_lengths sn hsn) as (l1 & l2 & l3 & l4 & l5).
        unfold real_proofs, sim_proofs.
        (* The simulated target coincides with phi of the honest witness. *)
        replace (target_of (ch_beta ch) (honest_cs sn r) (com_vals sn t))
          with (phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch) (hon_w (ch_beta ch) sn (rand2_of r t [] [] [] [])))
          by (rewrite <-(target_phi ch sn (rand2_of r t [] [] [] [])); [reflexivity | assumption ..]).
        eapply Permutation_trans; [apply bind_perm_left; apply (lin_shvzk (HV := st_vspace) W (phi (ch_beta ch) (ch_g1 ch) (ch_g2 ch))
          (phi_add (ch_beta ch) (ch_g1 ch) (ch_g2 ch)) (phi_scale (ch_beta ch) (ch_g1 ch) (ch_g2 ch))); [apply hon_w_length; exact hsn | exact hnd | exact hall] |].
        (* Zero argument 1. *)
        apply bind_perm_right; intros lp _ _.
        change [nth 2 (com_vals sn t) gid; nth 3 (com_vals sn t) gid]
          with (com_list h1 gs1 [hon_b sn; hon_p sn] [nth 2 t zero; nth 3 t zero]).
        change [nth 1 (com_vals sn t) gid; cneg gs1 K]
          with (com_list h1 gs1 [hon_d sn; repeat (opp one) K] [nth 1 t zero; zero]).
        eapply Permutation_trans; [apply bind_perm_left; apply (zero_shvzk (Hvec := Hvec) (Gdec := Gdec) h1 gs1 γ1); try (cbn; lia); try assumption |].
        + rewrite hg1; unfold K; cbn; lia.
        + constructor; [rewrite l3; exact (eq_sym hg1) |].
          constructor; [rewrite l4; exact (eq_sym hg1) | constructor].
        + constructor; [rewrite l2; exact (eq_sym hg1) |].
          constructor; [rewrite repeat_length; exact (eq_sym hg1) | constructor].
        + rewrite hg1; exact hγ1.
        + cbn [combine map fold_right fst snd].
          pose proof (star_w_prod (ch_y1 ch) (ch_y1 ch) (hon_b sn) (hon_d sn) K l3 l2) as hp.
          unfold BayerGroth.star, hon_p; etransitivity; [| exact hp]; field.
          (* Zero argument 2. *)
        + apply bind_perm_right; intros z1 _ _.
          replace [gop (nth 4 (com_vals sn t) gid) (cneg gs2 NX)]
            with (com_list h1 gs2 [ladd (hon_X sn) (repeat (opp one) NX)] [nth 4 t zero]).
          2: { cbn [com_vals nth com_list combine map fst snd]. unfold cneg.
               transitivity [com h1 gs2 (ladd (hon_X sn) (repeat (opp one) NX)) (nth 4 t zero + zero)];
               [f_equal; f_equal; field | f_equal; apply com_add; rewrite repeat_length; exact l5]. }
          change [nth 4 (com_vals sn t) gid] with (com_list h1 gs2 [hon_X sn] [nth 4 t zero]).
          eapply Permutation_trans; [apply bind_perm_left; apply (zero_shvzk (Hvec := Hvec) (Gdec := Gdec) h1 gs2 γ2); try (cbn; lia); try assumption |].
          * rewrite hg2; unfold NX, K; destruct L as [| L']; [cbn in hL; lia | cbn; nia].
          * constructor; [rewrite l5; exact (eq_sym hg2) | constructor].
          * constructor; [rewrite ladd_length, l5; [exact (eq_sym hg2) | rewrite repeat_length; exact l5] | constructor].
          * rewrite hg2; exact hγ2.
          * cbn [combine map fold_right fst snd].
            pose proof (star_w_bits (ch_y2 ch) (ch_y2 ch) (hon_X sn) NX l5 (hon_X_bits sn)) as hb0.
            unfold BayerGroth.star; etransitivity; [| exact hb0]; field.
            (* Zero argument 3. *)
          * apply bind_perm_right; intros z2 _ _.
            replace [gop (nth 2 (com_vals sn t) gid) (cneg gs1 K)]
              with (com_list h1 gs1 [ladd (hon_b sn) (repeat (opp one) K)] [nth 2 t zero]).
            2: { cbn [com_vals nth com_list combine map fst snd]. unfold cneg.
                 transitivity [com h1 gs1 (ladd (hon_b sn) (repeat (opp one) K)) (nth 2 t zero + zero)];
                 [f_equal; f_equal; field | f_equal; apply com_add; rewrite repeat_length; exact l3]. }
            change [nth 2 (com_vals sn t) gid] with (com_list h1 gs1 [hon_b sn] [nth 2 t zero]).
            eapply Permutation_trans; [apply bind_perm_left; apply (zero_shvzk (Hvec := Hvec) (Gdec := Gdec) h1 gs1 γ1); try (cbn; lia); try assumption |].
            -- rewrite hg1; unfold K; cbn; lia.
            -- constructor; [rewrite l3; exact (eq_sym hg1) | constructor].
            -- constructor; [rewrite ladd_length, l3; [exact (eq_sym hg1) | rewrite repeat_length; exact l3] | constructor].
            -- rewrite hg1; exact hγ1.
            -- cbn [combine map fold_right fst snd].
               pose proof (star_w_bits (ch_y3 ch) (ch_y3 ch) (hon_b sn) K l3 (hon_b_bits sn)) as hb0.
               unfold BayerGroth.star; etransitivity; [| exact hb0]; field.
            -- apply bind_perm_right; intros z3 _ _. apply Permutation_refl.
      Qed.

      (** The bijection [t ↦ t + ⟨γ, v⟩] (and its inverse) on the five
          commitment randomnesses, where [v] are the honest committed
          vectors. *)
      Definition com_phi (sn : list nat) (t : list F) : list F :=
        [nth 0 t zero + zdot γ1 (hon_s sn); nth 1 t zero + zdot γ1 (hon_d sn);
         nth 2 t zero + zdot γ1 (hon_b sn); nth 3 t zero + zdot γ1 (hon_p sn);
         nth 4 t zero + zdot γ2 (hon_X sn)].
      Definition com_psi (sn : list nat) (u : list F) : list F :=
        [nth 0 u zero - zdot γ1 (hon_s sn); nth 1 u zero - zdot γ1 (hon_d sn);
         nth 2 u zero - zdot γ1 (hon_b sn); nth 3 u zero - zdot γ1 (hon_p sn);
         nth 4 u zero - zdot γ2 (hon_X sn)].

      (** The honest commitments are uniform: by [zk_of_bijection] and
          [com_dlog], [com(v; t) = h1 ^ (t + ⟨γ, v⟩)]. *)
      Lemma com_vals_perm : forall (sn : list nat), NoDup lf -> (forall v : F, In v lf) ->
        Permutation (Bind (rand lf Hlfn 5) (fun t => Ret (com_vals sn t)))
                    (Bind (rand lf Hlfn 5) (fun u => Ret (map (fun e => h1 ^ e) u))).
      Proof.
        intros sn hnd hall.
        apply (zk_of_bijection (zero := zero) lf Hlfn 5 (com_vals sn) (map (fun e => h1 ^ e)) (com_phi sn) (com_psi sn) hnd hall).
        + intros l hl; reflexivity.
        + intros l hl; reflexivity.
        + intros l hl; do 5 (destruct l as [| ? l]; [discriminate hl |]); destruct l; [| discriminate hl].
          unfold com_psi, com_phi; cbn [nth].
          f_equal; [field | f_equal; [field | f_equal; [field | f_equal; [field | f_equal; field]]]].
        + intros l hl; do 5 (destruct l as [| ? l]; [discriminate hl |]); destruct l; [| discriminate hl].
          unfold com_psi, com_phi; cbn [nth].
          f_equal; [field | f_equal; [field | f_equal; [field | f_equal; [field | f_equal; field]]]].
        + intros l hl. unfold com_vals, com_phi; cbn [map].
          assert (e1 : length γ1 = length gs1) by congruence.
          assert (e2 : length γ2 = length gs2) by congruence.
          assert (k1 : forall j, (j < length gs1)%nat -> nth j gs1 gid = h1 ^ nth j γ1 zero) by (rewrite hg1; exact hγ1).
          assert (k2 : forall j, (j < length gs2)%nat -> nth j gs2 gid = h1 ^ nth j γ2 zero) by (rewrite hg2; exact hγ2).
          f_equal; [apply (com_dlog (Hvec := Hvec)); assumption |
          f_equal; [apply (com_dlog (Hvec := Hvec)); assumption |
          f_equal; [apply (com_dlog (Hvec := Hvec)); assumption |
          f_equal; [apply (com_dlog (Hvec := Hvec)); assumption |
          f_equal; apply (com_dlog (Hvec := Hvec)); assumption]]]].
      Qed.

      (** SHVZK of the batched ballot: for valid positions ([sn] of length
          [m], entries at most [m < 2^L]) and [|β| = K], the honest ballot
          is distributed as the simulator's output given only the
          ciphertexts (with the same encryption randomness) and the
          challenges. Hence the commitments and proofs reveal nothing about
          the ranking beyond the ciphertexts. *)
      Theorem ballot2_zk : forall (ch : chal2) (sn : list nat),
        NoDup lf -> (forall v : F, In v lf) ->
        length sn = m -> (forall i, (i < m)%nat -> (nth i sn 0 <= m)%nat) -> (m < Nat.pow 2 L)%nat ->
        length (ch_beta ch) = K ->
        Permutation (ballot2_real_dist ch sn)
                    (Bind (rand lf Hlfn K) (fun r => ballot2_sim_dist ch (honest_cs sn r))).
      Proof.
        intros ch sn hnd hall hsn hs hL hb.
        rewrite real_dist_proofs. apply bind_perm_right; intros r _ _.
        unfold ballot2_sim_dist.
        transitivity (Bind (Bind (rand lf Hlfn 5) (fun t => Ret (com_vals sn t))) (fun C => sim_proofs ch (honest_cs sn r) C)).
        { rewrite bind_assoc. apply bind_perm_right; intros t p hin. rewrite bind_ret_left.
          apply real_proofs_perm; try assumption. exact (in_rand_length lf Hlfn 5 t p hin). }
        eapply Permutation_trans; [apply bind_perm_left; apply com_vals_perm; assumption |].
        rewrite bind_assoc. apply bind_perm_right; intros u _ _. rewrite bind_ret_left. apply Permutation_refl.
      Qed.

    End ZK2.

  End Ballot2.

End SchulzeBatched.
