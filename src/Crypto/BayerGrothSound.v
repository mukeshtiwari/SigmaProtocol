(** * Soundness of the Bayer–Groth shuffle argument and its sub-arguments

    This file proves knowledge soundness, in the form of special soundness with
    respect to a tree of accepting transcripts, for the verifiers defined in
    [BayerGroth.v]: the zero argument, the Hadamard product argument, the
    single value product argument, the product argument, the
    multi-exponentiation argument and the full verifiable shuffle argument of
    Bayer and Groth (_Efficient Zero-Knowledge Argument for Correctness of a
    Shuffle_, EUROCRYPT 2012). The protocol messages and the honest prover are
    in [BayerGroth.v]; the zero-knowledge simulators are in [BayerGrothZK.v].

    All results are purely algebraic and deterministic. Nothing is said about
    probabilities, knowledge error or running time of an extractor; instead
    every theorem has the shape

[[
    (enough accepting transcripts with distinct challenges)  ->
    (a witness for the statement exists)  \/  binding_break h gs
]]

    where [binding_break h gs] says that two different full-length openings
    of the same Pedersen commitment under the key [(h, gs)] are known. The
    reduction from [binding_break] to the discrete-logarithm problem is not
    part of this file. The witness is constructed explicitly (as Lagrange
    combinations of the responses), so the proofs are constructive
    extractors, although they are stated with [exists].

    The Pedersen commitment is [com h gs a r = h^r · ∏ g_i^(a_i)]. It only
    reads the first [length gs] coordinates of [a], so [binding_break] is
    stated for openings of exact length [length gs], and openings of other
    lengths are normalised with [pad]. The verifiers in [BayerGroth.v] check
    the lengths of the response vectors and (for the Hadamard argument) that
    the challenges are non-zero, so the theorems assume nothing about the
    transcripts beyond acceptance, the number of challenges and their
    distinctness.

    The proof technique is the same throughout:

    - a committed polynomial [geval (c_0 :: … :: c_k) x = ∏ c_i^(x^i)] that
      is opened at [k+1] distinct challenges is opened coefficientwise by the
      inverse Vandermonde matrix ([geval_openings], built on
      [coeff_from_evals] of [PolyRoots.v]);
    - comparing these extracted openings with the responses gives, unless
      binding breaks, a polynomial identity at every challenge
      ([open_eq_or_break]);
    - a polynomial identity of degree below the number of challenges holds
      coefficientwise ([agree_nth] of [PolyRoots.v]), and the relevant
      coefficient is the claim of the statement.

    Summary of the main theorems (m is the number of committed rows, n the
    length of the commitment key [gs], N = m·n):

    - [zero_soundness] (and [zero_soundness_ext] with explicit openings):
      2m+1 distinct challenges x; the extracted openings [A], [B] of [cA],
      [cB] satisfy [Σ_i A_i ⋆_y B_i = 0] for the bilinear map [star] of
      [BayerGroth.v].
    - [hadamard_soundness]: m distinct x, n distinct y, and for every pair a
      full zero-argument tree of 2m+1 challenges; the extracted openings of
      [cA] and [cb] satisfy [b = A_1 ∘ … ∘ A_m] (entrywise product).
    - [svp_soundness]: n+1 distinct challenges; the opening [a] of [ca]
      satisfies [∏ a_i = b].
    - [product_soundness]: composition of the two previous ones; the openings
      [A] of [cA] satisfy [∏ (A_1 ∘ … ∘ A_m) = b].
    - [multiexp_soundness]: 2m distinct challenges; the openings [A] of [cA]
      satisfy [C = Enc(1; ρ) · ∏_i C_i^(A_i)] for ElGamal-style vector
      ciphertexts.
    - [shuffle_soundness]: N distinct x, more than 2N² distinct y, more than
      N distinct z and the above trees for the sub-arguments at each
      challenge tuple; then there are a permutation σ and randomisers ρ with
      [C'_i = Enc(1; ρ_i) · C_(σ(i))] for every i.

    The shuffle theorem additionally assumes that the map [i ↦ fnat i] is
    injective on [{0, …, N−1}], i.e. the characteristic of the field exceeds N. The
    permutation is obtained from the product identity by [perm_of_products]
    of [PolyPerm.v] (a Schwartz–Zippel style root-counting argument, hence
    the bounds on the numbers of y and z challenges). Other building blocks:
    [SigmaK.v] (list polynomial arithmetic), [MultiExp.v] ([lmexp], [veval]),
    [PolyRoots.v] (Lagrange coefficients [lam], [agree_nth]). *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool List Permutation setoid_ring.Field PeanoNat Arith.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Sigma Require Import Sigma MultiExp OkamotoRows PolyRoots SigmaK PolyPerm BayerGroth.
From Utility Require Import Util.
Import ListNotations.

(** ** Setting

    [F] is the scalar field and [G] a group seen as an [F]-vector space
    (written multiplicatively in the prose: [gop] is the group law and
    [gpow] exponentiation). Equality on both is decidable, since the
    verifiers compare group elements. The local notations instantiate the
    generic polynomial and commitment machinery of [BayerGroth.v],
    [MultiExp.v] and [SigmaK.v] at this field and group. *)
Section BayerGrothSound.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Local Notation Hf := (@vector_space_field F (@eq F) zero one add mul sub div opp inv
    G (@eq G) gid ginv gop gpow Hvec).

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  Local Infix "^" := gpow.
  Local Infix "+" := add.
  Local Infix "*" := mul.
  Local Infix "-" := sub.

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
  Local Notation gpow_zero := (gpow_zero (Hvec := Hvec)).

  Local Notation gmexp := (lmexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation geval := (veval (one := one) (mul := mul) (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation feval := (veval (one := one) (mul := mul) (vid := zero) (vadd := add) (smul := mul)).
  Local Notation fpmul := (pmul (vid := zero) (vadd := add)).
  Local Notation fconv := (conv_coeff (vid := zero) (vadd := add)).
  Local Notation gsum := (vsum (vid := gid) (vadd := gop)).
  Local Notation fsum := (fsum (zero := zero) (add := add)).
  Local Notation com := (com (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation com_list := (com_list (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation lscale := (lscale (mul := mul)).
  Local Notation ladd := (ladd (add := add)).
  Local Notation fpow := (fpow (one := one) (mul := mul)).
  Local Notation lpows := (lpows (one := one) (mul := mul)).
  Local Notation padd := (padd (add := add)).
  Local Notation fnat := (fnat (zero := zero) (one := one) (add := add)).
  Local Notation pmulF := (pmulF (zero := zero) (add := add) (mul := mul)).
  Local Notation eval := (eval (zero := zero) (add := add) (mul := mul)).
  Local Notation star := (star (zero := zero) (add := add) (mul := mul)).
  Local Notation lveval := (lveval (add := add) (mul := mul)).
  Local Notation lam := (lam (zero := zero) (one := one) (add := add) (mul := mul) (sub := sub)
    (opp := opp) (inv := inv)).
  Local Notation zero_verify := (zero_verify (zero := zero) (one := one) (add := add) (mul := mul)
    (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation zero_argument := (@zero_argument F G).

  (** ** Boolean reflection and finite choice *)

  (** [gdec_true], [fdec_true]: a successful equality test of the verifier
      yields a propositional equality in [G], respectively [F]. *)
  Lemma gdec_true : forall u v : G, (if Gdec u v then true else false) = true -> u = v.
  Proof. intros u v h; destruct (Gdec u v); [assumption | discriminate]. Qed.

  Lemma fdec_true : forall u v : F, (if Fdec u v then true else false) = true -> u = v.
  Proof. intros u v h; destruct (Fdec u v); [assumption | discriminate]. Qed.

  (** [forall_or]: a finite conjunction of disjunctions with a common right
      disjunct [Q] distributes. If every [j < k] satisfies [P j \/ Q], then
      either all of them satisfy [P] or [Q] holds. This is how a
      [binding_break] found at any single challenge is propagated out of a
      quantifier over all challenges. *)
  Lemma forall_or : forall (P : nat -> Prop) (Q : Prop) (k : nat),
    (forall j, (j < k)%nat -> P j \/ Q) -> (forall j, (j < k)%nat -> P j) \/ Q.
  Proof.
    intros P Q k; induction k as [| k ih]; intros h; [left; intros j hj; lia |].
    destruct ih as [hp | hq]; [intros j hj; apply h; lia | | right; exact hq].
    destruct (h k ltac:(lia)) as [hk | hq]; [| right; exact hq].
    left; intros j hj. destruct (Nat.eq_dec j k) as [-> | hne]; [exact hk | apply hp; lia].
  Qed.

  (** ** Pedersen commitments: padding and binding

      [com h gs a r] ignores the coordinates of [a] beyond [length gs] and
      treats missing ones as zero; this section turns any two openings of the
      same commitment into either equal openings or a [binding_break]. *)

  (** [pad n a] is [a] truncated or zero-extended to length exactly [n]. *)
  Definition pad (n : nat) (a : list F) : list F := map (fun i => nth i a zero) (seq 0 n).

  (** [pad_length], [nth_pad]: [pad n a] has length [n] and agrees with [a]
      (with default [zero]) on the first [n] positions. *)
  Lemma pad_length : forall n a, length (pad n a) = n.
  Proof. intros; unfold pad; rewrite length_map, length_seq; reflexivity. Qed.

  Lemma nth_pad : forall n a i, (i < n)%nat -> nth i (pad n a) zero = nth i a zero.
  Proof. intros n a i hi; unfold pad; exact (PolyPerm.nth_map_seq (fun j => nth j a zero) n i zero hi). Qed.

  (** The multi-exponentiation [∏ g_i^(a_i)] only depends on [pad (length
      gs) a]. *)
  Lemma gmexp_pad : forall (gs : list G) (a : list F), gmexp gs a = gmexp gs (pad (length gs) a).
  Proof.
    induction gs as [| g gs ih]; intros a; [rewrite !lmexp_nil_l; reflexivity |].
    unfold pad; cbn [length seq map]; rewrite <-seq_shift, map_map.
    destruct a as [| a0 a].
    + rewrite lmexp_nil_r, lmexp_cons, gpow_zero, gid_l.
      rewrite (map_ext (fun x => nth (S x) [] zero) (fun x => nth x [] zero)) by (intro x; destruct x; reflexivity).
      fold (pad (length gs) []); rewrite <-ih; rewrite lmexp_nil_r; reflexivity.
    + rewrite !lmexp_cons; cbn [nth]. f_equal. unfold pad in ih; apply ih.
  Qed.

  (** Consequently [com h gs a r = com h gs (pad (length gs) a) r]. *)
  Lemma com_pad : forall h gs a r, com h gs a r = com h gs (pad (length gs) a) r.
  Proof. intros; unfold BayerGroth.com; f_equal; apply gmexp_pad. Qed.

  (** [binding_break h gs]: there are two different openings [(a, r) ≠ (a',
      r')] with [length a = length a' = length gs] and [com h gs a r = com h
      gs a' r']. Under the discrete-logarithm assumption for the key [(h,
      gs)] such a pair is hard to find; every soundness theorem below has
      this as its escape clause. *)
  Definition binding_break (h : G) (gs : list G) : Prop :=
    exists a r a' r', length a = length gs /\ length a' = length gs /\
      com h gs a r = com h gs a' r' /\ (a <> a' \/ r <> r').

  (** If [com h gs a r = com h gs a' r'] (for arbitrary lengths of [a],
      [a']), then either [r = r'] and [a], [a'] agree on the first [length
      gs] positions, or binding breaks (witnessed by the padded openings). *)
  Lemma open_eq_or_break : forall h gs a r a' r', com h gs a r = com h gs a' r' ->
    (r = r' /\ forall i, (i < length gs)%nat -> nth i a zero = nth i a' zero) \/ binding_break h gs.
  Proof.
    intros * he.
    destruct (Fdec r r') as [hr | hr].
    + destruct (list_eq_dec Fdec (pad (length gs) a) (pad (length gs) a')) as [hp | hp].
      - left; split; [exact hr |]. intros i hi.
        rewrite <-(nth_pad (length gs) a i hi), <-(nth_pad (length gs) a' i hi), hp; reflexivity.
      - right. exists (pad (length gs) a), r, (pad (length gs) a'), r'.
        split; [apply pad_length | split; [apply pad_length | split]].
        * rewrite <-!com_pad; exact he.
        * left; exact hp.
    + right. exists (pad (length gs) a), r, (pad (length gs) a'), r'.
      split; [apply pad_length | split; [apply pad_length | split]].
      * rewrite <-!com_pad; exact he.
      * right; exact hr.
  Qed.

  (** Variant of [open_eq_or_break] for openings of full length [length gs]:
      either [a = a'] and [r = r'], or binding breaks. *)
  Lemma open_eq_or_break_len : forall h gs a r a' r', length a = length gs -> length a' = length gs ->
    com h gs a r = com h gs a' r' -> (a = a' /\ r = r') \/ binding_break h gs.
  Proof.
    intros * hl hl' he. destruct (open_eq_or_break h gs a r a' r' he) as [[hr hn] | hb]; [left | right; exact hb].
    split; [| exact hr]. apply (nth_ext _ _ zero zero); [lia |]. intros i hi; apply hn; lia.
  Qed.

  (** ** Opening a committed polynomial from its evaluations

      If [geval cs x_j = com h gs (A_j) (r_j)] for [k = length cs] distinct
      points [x_j], each coefficient commitment [c_i] is the commitment to the
      Lagrange combination [Σ_j λ_(i,j) · A_j]. This is the generic extraction
      step of every sub-argument. *)

  (** [lcomb c A k] is the vector [Σ_(j<k) c_j · A_j], computed with [padd]
      (so vectors of different lengths are zero-extended). *)
  Fixpoint lcomb (c : nat -> F) (A : nat -> list F) (k : nat) : list F :=
    match k with 0 => [] | S k' => padd (lcomb c A k') (lscale (c k') (A k')) end.

  (** If [k > 0] and every [A_j] (for [j < k]) has length [n], then [lcomb c
      A k] has length [n]. *)
  Lemma lcomb_length : forall c A k n, (0 < k)%nat -> (forall j, (j < k)%nat -> length (A j) = n) ->
    length (lcomb c A k) = n.
  Proof.
    intros c A k n hk hA; induction k as [| k ih]; [lia |].
    cbn [lcomb]; rewrite SigmaK.padd_length; unfold SigmaK.lscale; rewrite length_map, hA by lia.
    destruct k as [| k]; [reflexivity | rewrite ih by (lia || (intros; apply hA; lia)); lia].
  Qed.

  (** On one-element vectors [lcomb] is the scalar sum [Σ_(j<k) c_j · f_j]. *)
  Lemma lcomb_singletons : forall c (f : nat -> F) k, (0 < k)%nat ->
    lcomb c (fun j => [f j]) k = [fsum (fun j => c j * f j) k].
  Proof.
    intros c f k hk; induction k as [| k ih]; [lia |].
    cbn [lcomb fsum]. destruct k as [| k]; [cbn; f_equal; field |].
    rewrite ih by lia; cbn [SigmaK.padd SigmaK.lscale map]; reflexivity.
  Qed.

  (** Homomorphism of Pedersen commitments: [∏_(j<k) com(a_j; r_j)^(c_j) =
      com(Σ c_j a_j; Σ c_j r_j)]. *)
  Lemma gsum_com : forall h gs (a : nat -> list F) (r c : nat -> F) k,
    gsum (fun j => (com h gs (a j) (r j)) ^ (c j)) k = com h gs (lcomb c a k) (fsum (fun j => c j * r j) k).
  Proof.
    intros h gs a r c k; induction k as [| k ih]; cbn [vsum lcomb fsum].
    + unfold BayerGroth.com; rewrite gpow_zero, lmexp_nil_r, gid_l; reflexivity.
    + rewrite ih, (com_padd (Hvec := Hvec)), (com_scale (Hvec := Hvec)); reflexivity.
  Qed.

  (** Coefficient extraction by the inverse Vandermonde matrix. Let [xs] be
      distinct ([NoDup]) with [length cs = length xs], and suppose that for
      every [j] the committed polynomial [geval cs (x_j)] opens to [(A j, r
      j)]. Then the [i]-th coefficient [c_i] opens to [(Σ_j λ_(i,j) A_j, Σ_j
      λ_(i,j) r_j)], where [lam xs i j] are the coefficients of the inverse
      Vandermonde matrix ([PolyRoots.v]). Proof: [coeff_from_evals] writes
      [c_i] as [∏_j (geval cs x_j)^(λ_(i,j))], then [gsum_com]. *)
  Theorem geval_openings : forall h gs (xs : list F) (cs : list G) (A : nat -> list F) (r : nat -> F),
    NoDup xs -> length cs = length xs ->
    (forall j, (j < length xs)%nat -> geval cs (nth j xs zero) = com h gs (A j) (r j)) ->
    forall i, (i < length xs)%nat ->
    nth i cs gid = com h gs (lcomb (lam xs i) A (length xs)) (fsum (fun j => lam xs i j * r j) (length xs)).
  Proof.
    intros * hnd hlen hev i hi.
    rewrite (coeff_from_evals (Fdec := Fdec) (Hf := Hf) (HV := Hvec) (fun cs x => geval cs x)
      (fun x => veval_nil x) (fun c cs x => veval_cons (HV := Hvec) c cs x) xs cs hnd hlen i hi).
    rewrite (vsum_ext _ (fun j => (com h gs (A j) (r j)) ^ (lam xs i j))) by (intros j hj; rewrite hev by exact hj; reflexivity).
    apply gsum_com.
  Qed.

  (** A list [cs] of length [k] whose [i]-th entry opens to [(A i, r i)] is
      exactly [com_list] of the lists of openings. *)
  Lemma com_list_of_openings : forall h gs (cs : list G) (A : nat -> list F) (r : nat -> F) k,
    length cs = k -> (forall i, (i < k)%nat -> nth i cs gid = com h gs (A i) (r i)) ->
    cs = com_list h gs (map A (seq 0 k)) (map r (seq 0 k)).
  Proof.
    intros * hl hn. apply (nth_ext _ _ gid gid).
    + rewrite com_list_length, !length_map, !length_seq; lia.
    + intros i hi. rewrite hl in hi. rewrite (nth_com_list (zero := zero)) by (rewrite ?length_map, ?length_seq; lia).
      rewrite !PolyPerm.nth_map_seq by exact hi. apply hn; exact hi.
  Qed.

  (** A successful inequality test [x ≠ y] of the verifier. *)
  Lemma fdec_ne : forall u v : F, (if Fdec u v then false else true) = true -> u <> v.
  Proof. intros u v h e; destruct (Fdec u v) eqn:E; [discriminate | exact (n e)]. Qed.

  (** ** Zero argument: (2m+1)-special soundness

      Statement: two lists of [m] commitments [cA] and [cB] and a challenge
      [y]. Claim: the position-wise openings [A_1 … A_m] of [cA] and [B_1 …
      B_m] of [cB] satisfy [Σ_i A_i ⋆_y B_i = 0], where [a ⋆_y b = Σ_j a_j
      b_j y^(j+1)] ([star] of [BayerGroth.v]). The prover commits to random
      blinders [A_0] (as [cA0]) and [B_(m+1)] (as [cBm]) and to the [2m+1]
      coefficients [d_k] of the product of the polynomials [Σ_(i=0..m) x^i
      A_i] (coefficient list [cA0 :: cA]) and [x^0 B_(m+1) + Σ_(i=1..m)
      x^(m+1-i) B_i] (coefficient list [cBm :: rev cB]). Matching pairs [A_i
      ⋆ B_i] land on [x^(m+1)], so [d_(m+1)] is the claimed sum; the verifier
      checks [c_(d_(m+1)) = 1] and the three opened evaluations at [x]. *)

  (** The zero-argument verifier guarantees that both response vectors have
      the length of the commitment key. *)
  Lemma zero_verify_lengths {h gs cA cB y x cA0 cBm cd a b r s t} :
    zero_verify h gs cA cB y x (mk_zero cA0 cBm cd a b r s t) = true -> length a = length gs /\ length b = length gs.
  Proof.
    intros hv; unfold BayerGroth.zero_verify in hv; cbv zeta in hv; cbn [za_a za_b] in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    repeat match goal with h : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in h end.
    split; assumption.
  Qed.

  (** Unpacking of an accepting zero-argument transcript: the length
      conditions, [c_(d_(m+1)) = 1] (index [S m] of [cd]), and the three
      verification equations [geval (cA0 :: cA) x = com(a; r)],
      [geval (cBm :: rev cB) x = com(b; s)] and
      [geval cd x = com([a ⋆_y b]; t)]. *)
  Lemma zero_verify_true : forall h gs cA cB y x cA0 cBm cd a b r s t,
    zero_verify h gs cA cB y x (mk_zero cA0 cBm cd a b r s t) = true ->
    (1 <= length cA)%nat /\ length cB = length cA /\ length cd = (2 * length cA + 1)%nat /\
    nth (S (length cA)) cd gid = gid /\
    geval (cA0 :: cA) x = com h gs a r /\ geval (cBm :: rev cB) x = com h gs b s /\
    geval cd x = com h gs [star y a b] t.
  Proof.
    intros * hv; unfold BayerGroth.zero_verify in hv; cbv zeta in hv; cbn [za_cA0 za_cBm za_cd za_a za_b za_r za_s za_t] in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    repeat match goal with
      | h : (if Gdec ?u ?v then true else false) = true |- _ => apply gdec_true in h
      | h : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in h
      | h : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in h
      end.
    repeat split; assumption.
  Qed.

  (** The extracted statement openings. From the first [m+1] challenges,
      [zopenA m xs a] are the openings of [A_1 … A_m] (coefficients [1 … m]
      of [cA0 :: cA]) and [zopenr] their randomness; [zopenB] and [zopens]
      are the same for [cBm :: rev cB], reversed so that they open [cB] in
      its stated order [B_0 … B_(m-1)]. *)
  Definition zopenA (m : nat) (xs : list F) (a : nat -> list F) : list (list F) :=
    map (fun i => lcomb (lam (firstn (S m) xs) (S i)) a (S m)) (seq 0 m).
  Definition zopenr (m : nat) (xs : list F) (r : nat -> F) : list F :=
    map (fun i => fsum (fun j => lam (firstn (S m) xs) (S i) j * r j) (S m)) (seq 0 m).
  Definition zopenB (m : nat) (xs : list F) (b : nat -> list F) : list (list F) := rev (zopenA m xs b).
  Definition zopens (m : nat) (xs : list F) (s : nat -> F) : list F := rev (zopenr m xs s).

  (** The four extracted lists all have length [m]. *)
  Lemma zopenA_length : forall m xs a, length (zopenA m xs a) = m.
  Proof. intros; unfold zopenA; rewrite length_map, length_seq; reflexivity. Qed.
  Lemma zopenr_length : forall m xs r, length (zopenr m xs r) = m.
  Proof. intros; unfold zopenr; rewrite length_map, length_seq; reflexivity. Qed.
  Lemma zopenB_length : forall m xs b, length (zopenB m xs b) = m.
  Proof. intros; unfold zopenB; rewrite length_rev; apply zopenA_length. Qed.
  Lemma zopens_length : forall m xs s, length (zopens m xs s) = m.
  Proof. intros; unfold zopens; rewrite length_rev; apply zopenr_length. Qed.

  (** Special soundness of the zero argument, with explicit witnesses.
      Hypotheses: the key has [length gs ≥ 1]; [xs] is a list of [2m+1]
      distinct challenges ([m = length cA]); for every [j] the transcript
      with first message [(cA0, cBm, cd)] (fixed) and challenge [x_j] with
      responses [(a j, b j, r j, s j, t j)] is accepted for the same [y].
      Conclusion: either binding breaks, or [cA] and [cB] are the
      commitment lists of [zopenA]/[zopenr] and [zopenB]/[zopens], all
      opened vectors have length [length gs], and
      [Σ_i zopenA_i ⋆_y zopenB_i = 0].

      Proof idea: [geval_openings] on the first [m+1] challenges opens [cA0
      :: cA] and [cBm :: rev cB], and on all [2m+1] challenges opens [cd].
      Binding then shows that at every challenge the responses are the
      evaluations of the extracted polynomials, so the polynomial identity
      [(Σ x^i A_i) ⋆ (Σ x^i B'_i) = Σ x^i d_i] holds at [2m+1] points and,
      by degree [2m], coefficientwise ([agree_nth]). The coefficient of
      [x^(m+1)] is the claimed sum ([conv_middle]), and the middle
      commitment [c_(d_(m+1)) = 1 = com(0; 0)] forces [d_(m+1) = 0] unless
      binding breaks. *)
  Theorem zero_soundness_ext : forall (h : G) (gs : list G) (cA cB : list G) (y : F) (cA0 cBm : G) (cd : list G)
    (xs : list F) (a b : nat -> list F) (r s t : nat -> F),
    (1 <= length gs)%nat ->
    NoDup xs -> length xs = (2 * length cA + 1)%nat ->
    (forall j, (j < length xs)%nat ->
      zero_verify h gs cA cB y (nth j xs zero) (mk_zero cA0 cBm cd (a j) (b j) (r j) (s j) (t j)) = true) ->
    (cA = com_list h gs (zopenA (length cA) xs a) (zopenr (length cA) xs r) /\
     cB = com_list h gs (zopenB (length cA) xs b) (zopens (length cA) xs s) /\
     (forall v, In v (zopenA (length cA) xs a) -> length v = length gs) /\
     (forall v, In v (zopenB (length cA) xs b) -> length v = length gs) /\
     fold_right add zero (map (fun p => star y (fst p) (snd p))
       (combine (zopenA (length cA) xs a) (zopenB (length cA) xs b))) = zero)
    \/ binding_break h gs.
  Proof.
    intros h gs cA cB y cA0 cBm cd xs a b r s t hn hnd hk htr0.
    (* Record the length facts checked by the verifier at every challenge. *)
    assert (htr : forall j, (j < length xs)%nat -> length (a j) = length gs /\ length (b j) = length gs /\
      zero_verify h gs cA cB y (nth j xs zero) (mk_zero cA0 cBm cd (a j) (b j) (r j) (s j) (t j)) = true)
      by (intros j hj; destruct (zero_verify_lengths (htr0 j hj)); repeat split; auto).
    set (m := length cA) in *. set (n := length gs) in *. set (k := (2 * m + 1)%nat) in *.
    assert (hm_eq : length cA = m) by reflexivity. assert (hn_eq : length gs = n) by reflexivity.
    assert (hk_eq : (2 * m + 1)%nat = k) by reflexivity.
    assert (hm : (1 <= m)%nat).
    { destruct (htr 0%nat ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto. }
    assert (hcB : length cB = m) by (destruct (htr 0%nat ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto).
    assert (hcd : length cd = k) by (destruct (htr 0%nat ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto).
    assert (hmid : nth (S m) cd gid = gid) by (destruct (htr 0%nat ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto).
    assert (hevA : forall j, (j < k)%nat -> geval (cA0 :: cA) (nth j xs zero) = com h gs (a j) (r j))
      by (intros j hj; destruct (htr j ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto).
    assert (hevB : forall j, (j < k)%nat -> geval (cBm :: rev cB) (nth j xs zero) = com h gs (b j) (s j))
      by (intros j hj; destruct (htr j ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto).
    assert (hevD : forall j, (j < k)%nat -> geval cd (nth j xs zero) = com h gs [star y (a j) (b j)] (t j))
      by (intros j hj; destruct (htr j ltac:(lia)) as (_ & _ & hv); apply zero_verify_true in hv; tauto).
    assert (hla : forall j, (j < k)%nat -> length (a j) = n) by (intros j hj; destruct (htr j ltac:(lia)); tauto).
    assert (hlb : forall j, (j < k)%nat -> length (b j) = n) by (intros j hj; destruct (htr j ltac:(lia)); tauto).
    (* The first m + 1 challenges open the commitments cA0 :: cA and
       cBm :: rev cB coefficientwise by the inverse Vandermonde matrix. *)
    set (X1 := firstn (S m) xs).
    assert (hX1nd : NoDup X1) by (apply NoDup_firstn; exact hnd).
    assert (hX1l : length X1 = S m) by (unfold X1; rewrite length_firstn; lia).
    assert (hX1n : forall j, (j < S m)%nat -> nth j X1 zero = nth j xs zero) by (intros j hj; unfold X1; apply nth_firstn_lt; exact hj).
    set (A' := fun i => lcomb (lam X1 i) a (S m)).
    set (r' := fun i => fsum (fun j => lam X1 i j * r j) (S m)).
    set (B' := fun i => lcomb (lam X1 i) b (S m)).
    set (s' := fun i => fsum (fun j => lam X1 i j * s j) (S m)).
    assert (hopenA : forall i, (i < S m)%nat -> nth i (cA0 :: cA) gid = com h gs (A' i) (r' i)).
    { intros i hi. unfold A', r'. rewrite <-hX1l.
      apply (geval_openings h gs X1 (cA0 :: cA) a r hX1nd);
        [rewrite hX1l; cbn [length]; lia | | rewrite hX1l; lia].
      intros j hj; rewrite hX1l in hj; rewrite hX1n by lia; apply hevA; lia. }
    assert (hopenB : forall i, (i < S m)%nat -> nth i (cBm :: rev cB) gid = com h gs (B' i) (s' i)).
    { intros i hi. unfold B', s'. rewrite <-hX1l.
      apply (geval_openings h gs X1 (cBm :: rev cB) b s hX1nd);
        [rewrite hX1l; cbn [length]; rewrite length_rev; lia | | rewrite hX1l; lia].
      intros j hj; rewrite hX1l in hj; rewrite hX1n by lia; apply hevB; lia. }
    (* All 2m + 1 challenges open the coefficient commitments cd. *)
    set (dsum := fun i => fsum (fun j => lam xs i j * star y (a j) (b j)) k).
    set (t' := fun i => fsum (fun j => lam xs i j * t j) k).
    assert (hopenD : forall i, (i < k)%nat -> nth i cd gid = com h gs [dsum i] (t' i)).
    { intros i hi. unfold dsum, t'. rewrite <-lcomb_singletons by lia. rewrite <-hk.
      apply (geval_openings h gs xs cd (fun j => [star y (a j) (b j)]) t hnd); [rewrite hk; lia | | rewrite hk; lia].
      intros j hj; rewrite hk in hj; apply hevD; lia. }
    set (A'' := map A' (seq 0 (S m))). set (r'' := map r' (seq 0 (S m))).
    set (B'' := map B' (seq 0 (S m))). set (s'' := map s' (seq 0 (S m))).
    set (d := map dsum (seq 0 k)). set (t'' := map t' (seq 0 k)).
    assert (hcAl : cA0 :: cA = com_list h gs A'' r'') by (apply com_list_of_openings; [reflexivity | exact hopenA]).
    assert (hcBl : cBm :: rev cB = com_list h gs B'' s'') by (apply com_list_of_openings; [cbn; rewrite length_rev; lia | exact hopenB]).
    assert (hcdl : cd = com_list h gs (map (fun dk => [dk]) d) t'').
    { unfold d; rewrite map_map. apply com_list_of_openings; [exact hcd | exact hopenD]. }
    assert (hA'len : forall i, (i < S m)%nat -> length (A' i) = n) by (intros i hi; unfold A'; apply lcomb_length; [lia | intros j hj; apply hla; lia]).
    assert (hB'len : forall i, (i < S m)%nat -> length (B' i) = n) by (intros i hi; unfold B'; apply lcomb_length; [lia | intros j hj; apply hlb; lia]).
    assert (hA''len : forall v, In v A'' -> length v = n).
    { intros v hv; unfold A'' in hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hA'len; lia. }
    assert (hB''len : forall v, In v B'' -> length v = n).
    { intros v hv; unfold B'' in hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hB'len; lia. }
    assert (hA''ne : A'' <> []) by (unfold A''; cbn [seq map]; discriminate).
    assert (hB''ne : B'' <> []) by (unfold B''; cbn [seq map]; discriminate).
    assert (hlenAr : length A'' = length r'') by (unfold A'', r''; rewrite !length_map; reflexivity).
    assert (hlenBs : length B'' = length s'') by (unfold B'', s''; rewrite !length_map; reflexivity).
    assert (hlend : length d = k) by (unfold d; rewrite length_map, length_seq; reflexivity).
    assert (hlendt : length (map (fun dk => [dk]) d) = length t'') by (unfold t''; rewrite !length_map, length_seq; exact hlend).
    (* By binding, the responses at each challenge are the evaluations of
       the extracted openings. *)
    assert (hresp : (forall j, (j < k)%nat ->
        a j = lveval A'' (nth j xs zero) /\ b j = lveval B'' (nth j xs zero) /\
        star y (a j) (b j) = feval d (nth j xs zero)) \/ binding_break h gs).
    { apply forall_or. intros j hj.
      pose proof (hevA j hj) as ha; rewrite hcAl, (geval_com_list (Hvec := Hvec)) in ha by exact hlenAr.
      pose proof (hevB j hj) as hb; rewrite hcBl, (geval_com_list (Hvec := Hvec)) in hb by exact hlenBs.
      pose proof (hevD j hj) as hd; rewrite hcdl, (geval_com_list (Hvec := Hvec)) in hd by exact hlendt.
      rewrite (lveval_singletons (Hvec := Hvec)) in hd by (unfold d; destruct k; [lia | cbn [seq map]; discriminate]).
      destruct (open_eq_or_break_len h gs _ _ _ _ (lveval_length A'' _ n hA''ne hA''len) (hla j hj) ha) as [[ea _] | hbb];
        [| right; exact hbb].
      destruct (open_eq_or_break_len h gs _ _ _ _ (lveval_length B'' _ n hB''ne hB''len) (hlb j hj) hb) as [[eb _] | hbb];
        [| right; exact hbb].
      destruct (open_eq_or_break h gs _ _ _ _ hd) as [[_ ed] | hbb]; [| right; exact hbb].
      left; split; [symmetry; exact ea | split; [symmetry; exact eb |]].
      specialize (ed 0%nat ltac:(lia)); cbn [nth] in ed; symmetry; exact ed. }
    destruct hresp as [hresp | hbb]; [| right; exact hbb].
    (* The product-polynomial identity holds at 2m + 1 distinct points, hence
       coefficientwise; we keep the coefficient of x^(m+1). *)
    assert (hpoly : forall i, nth i (fpmul (star y) A'' B'') zero = nth i d zero).
    { intros i. apply (agree_nth (Fdec := Fdec) (Hf := Hf) xs).
      + exact hnd.
      + rewrite (pmul_length (vid := zero) (vadd := add)) by assumption.
        unfold A'', B''; rewrite !length_map, !length_seq; lia.
      + lia.
      + intros x hx. destruct (In_nth xs x zero hx) as (j & hj & <-).
        rewrite <-!(feval_eval (Hvec := Hvec)), (feval_pmul_star (Hvec := Hvec)).
        destruct (hresp j ltac:(lia)) as (ea & eb & ed). rewrite <-ea, <-eb; exact ed. }
    specialize (hpoly (S m)).
    rewrite (nth_pmul (HV := F_vspace (Hvec := Hvec)) _ []) in hpoly by (intro v; apply star_nil_r).
    unfold d in hpoly; rewrite PolyPerm.nth_map_seq in hpoly by lia.
    (* Split off the random blinders A_0 and B_m, leaving the statement
       openings, and identify the middle coefficient with the claimed sum. *)
    set (Astmt := map (fun i => A' (S i)) (seq 0 m)).
    set (Bstmt := rev (map (fun i => B' (S i)) (seq 0 m))).
    assert (hA''eq : A'' = A' 0%nat :: Astmt) by (unfold A'', Astmt; cbn [seq map]; rewrite <-seq_shift, map_map; reflexivity).
    assert (hB''eq : B'' = B' 0%nat :: rev Bstmt) by (unfold B'', Bstmt; rewrite rev_involutive; cbn [seq map]; rewrite <-seq_shift, map_map; reflexivity).
    assert (hlBstmt : length Bstmt = m) by (unfold Bstmt; rewrite length_rev, length_map, length_seq; reflexivity).
    assert (hlAstmt : length Astmt = m) by (unfold Astmt; rewrite length_map, length_seq; reflexivity).
    rewrite hA''eq, hB''eq in hpoly. cbn [conv_coeff] in hpoly.
    rewrite (nth_overflow (B' 0%nat :: rev Bstmt)) in hpoly by (cbn [length]; rewrite length_rev; lia).
    rewrite star_nil_r in hpoly.
    pose proof (conv_middle (zero := zero) (add := add) (mul := mul) y Astmt Bstmt (B' 0%nat) ltac:(lia)) as hcm.
    rewrite hlBstmt in hcm. rewrite hcm in hpoly.
    (* The middle commitment is the identity, i.e. com(0; 0), so the middle
       coefficient is zero unless binding breaks. *)
    assert (hzero : dsum (S m) = zero \/ binding_break h gs).
    { pose proof (hopenD (S m) ltac:(lia)) as h0.
      pose proof (eq_trans (com_zero_single (Hvec := Hvec) h gs) (eq_trans (eq_sym hmid) h0)) as h1.
      destruct (open_eq_or_break h gs _ _ _ _ h1) as [[_ e] | hbb]; [left | right; exact hbb].
      specialize (e 0%nat ltac:(lia)); cbn [nth] in e; symmetry; exact e. }
    destruct hzero as [hzero | hbb]; [| right; exact hbb].
    left.
    assert (hr''eq : r'' = r' 0%nat :: map (fun i => r' (S i)) (seq 0 m)) by (unfold r''; cbn [seq map]; rewrite <-seq_shift, map_map; reflexivity).
    assert (hs''eq : s'' = s' 0%nat :: map (fun i => s' (S i)) (seq 0 m)) by (unfold s''; cbn [seq map]; rewrite <-seq_shift, map_map; reflexivity).
    rewrite hA''eq, hr''eq, com_list_cons in hcAl. injection hcAl as _ hcAl.
    rewrite hB''eq, hs''eq, com_list_cons in hcBl. injection hcBl as _ hcBl.
    fold m. change (zopenA m xs a) with Astmt. change (zopenB m xs b) with Bstmt.
    change (zopenr m xs r) with (map (fun i => r' (S i)) (seq 0 m)).
    change (zopens m xs s) with (rev (map (fun i => s' (S i)) (seq 0 m))).
    split; [exact hcAl |].
    split.
    { rewrite <-(rev_involutive cB), hcBl, com_list_rev by (rewrite length_rev, hlBstmt, length_map, length_seq; reflexivity).
      unfold Bstmt; rewrite rev_involutive; reflexivity. }
    split; [intros v hv; apply hA''len; rewrite hA''eq; right; exact hv |].
    split; [intros v hv; apply hB''len; rewrite hB''eq; right; apply in_rev; rewrite rev_involutive; exact hv |].
    match goal with |- ?S0 = zero => transitivity (zero + S0); [field | rewrite hpoly; exact hzero] end.
  Qed.

  (** Special soundness of the zero argument with the witness existentially
      quantified: under the hypotheses of [zero_soundness_ext], either
      binding breaks or there are openings [A], [B] (with randomness [ra],
      [sb]) of [cA], [cB], all of length [m] with vectors of length
      [length gs], such that [Σ_i A_i ⋆_y B_i = 0]. Immediate from
      [zero_soundness_ext]. *)
  Theorem zero_soundness : forall (h : G) (gs : list G) (cA cB : list G) (y : F) (cA0 cBm : G) (cd : list G)
    (xs : list F) (a b : nat -> list F) (r s t : nat -> F),
    (1 <= length gs)%nat ->
    NoDup xs -> length xs = (2 * length cA + 1)%nat ->
    (forall j, (j < length xs)%nat ->
      zero_verify h gs cA cB y (nth j xs zero) (mk_zero cA0 cBm cd (a j) (b j) (r j) (s j) (t j)) = true) ->
    (exists (A B : list (list F)) (ra sb : list F),
      cA = com_list h gs A ra /\ cB = com_list h gs B sb /\
      length A = length cA /\ length B = length cA /\ length ra = length cA /\ length sb = length cA /\
      (forall v, In v A -> length v = length gs) /\ (forall v, In v B -> length v = length gs) /\
      fold_right add zero (map (fun p => star y (fst p) (snd p)) (combine A B)) = zero)
    \/ binding_break h gs.
  Proof.
    intros * hn hnd hk htr.
    destruct (zero_soundness_ext h gs cA cB y cA0 cBm cd xs a b r s t hn hnd hk htr) as [(h1 & h2 & h3 & h4 & h5) | hbb];
      [left | right; exact hbb].
    exists (zopenA (length cA) xs a), (zopenB (length cA) xs b), (zopenr (length cA) xs r), (zopens (length cA) xs s).
    repeat split; try assumption; (apply zopenA_length || apply zopenB_length || apply zopenr_length || apply zopens_length).
  Qed.

  (** ** Hadamard argument: soundness from the zero argument

      Statement: commitments [cA = (c_(A_0), …, c_(A_(m-1)))] with [m ≥ 2]
      and [cb]. Claim: [b = A_0 ∘ A_1 ∘ … ∘ A_(m-1)] (entrywise product,
      [hprefix A (m-1)]). The prover commits to the partial products [B_i =
      A_0 ∘ … ∘ A_i] as [cB], with [c_(B_0) = c_(A_0)] and [c_(B_(m-1)) =
      cb], and uses challenges [x], [y] to batch the [m-1] relations
      [B_(i+1) = A_(i+1) ∘ B_i] into one zero-argument statement
      ([hadamard_zero_stmt]): with [⋆_y] the bilinear map,
      [Σ_i x^(i+1) (A_(i+1) ⋆_y B_i) − (1,…,1) ⋆_y D = 0], where [D] is the
      committed [Σ_i x^(i+1) B_(i+1)]. *)
  Local Notation hadamard_verify := (hadamard_verify (zero := zero) (one := one) (add := add) (mul := mul)
    (opp := opp) (Fdec := Fdec) (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation mk_had := (@mk_had F G).
  Local Notation hmul := (hmul (mul := mul)).
  Local Notation hprefix := (hprefix (mul := mul)).
  Local Notation star_w := (star_w (zero := zero) (add := add) (mul := mul)).

  (** The Hadamard verifier rejects the challenges [x = 0] and [y = 0]. *)
  Lemma hadamard_verify_nonzero {h gs n cA cb x y xz arg} :
    hadamard_verify h gs n cA cb x y xz arg = true -> x <> zero /\ y <> zero.
  Proof.
    intros hv; unfold BayerGroth.hadamard_verify in hv; cbv zeta in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    split; apply fdec_ne; assumption.
  Qed.

  (** The Hadamard verifier checks (through the zero argument) that both
      zero-argument responses have length [length gs]. *)
  Lemma hadamard_verify_lengths {h gs n cA cb x y xz cB cA0 cBm cd a b r s t} :
    hadamard_verify h gs n cA cb x y xz (mk_had cB (mk_zero cA0 cBm cd a b r s t)) = true ->
    length a = length gs /\ length b = length gs.
  Proof.
    intros hv; unfold BayerGroth.hadamard_verify in hv; cbv zeta in hv; cbn [ha_zero] in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    match goal with h : zero_verify _ _ _ _ _ _ _ = true |- _ => exact (zero_verify_lengths h) end.
  Qed.

  (** Unpacking of an accepting Hadamard transcript: [m ≥ 2], [length cB =
      m], [c_(B_0) = c_(A_0)], [c_(B_(m-1)) = cb], and the zero argument
      accepts the statement [hadamard_zero_stmt], written out: first list
      [tl cA ++ [com((−1,…,−1); 0)]], second list [(c_(B_i)^(x^(i+1)))_(i<m-1)
      ++ [(geval (tl cB) x)^x]]. *)
  Lemma hadamard_verify_true : forall h gs n cA cb x y xz cB zarg,
    hadamard_verify h gs n cA cb x y xz (mk_had cB zarg) = true ->
    (2 <= length cA)%nat /\ length cB = length cA /\ nth 0 cB gid = nth 0 cA gid /\ nth (length cA - 1) cB gid = cb /\
    zero_verify h gs (tl cA ++ [com h gs (repeat (opp one) n) zero])
      (map (fun i => (nth i cB gid) ^ (fpow x (S i))) (seq 0 (length cA - 1)) ++ [(geval (tl cB) x) ^ x]) y xz zarg = true.
  Proof.
    intros * hv; unfold BayerGroth.hadamard_verify, BayerGroth.hadamard_zero_stmt in hv; cbv zeta in hv;
      cbn [ha_cB ha_zero fst snd] in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    repeat match goal with
      | h : (if Gdec ?u ?v then true else false) = true |- _ => apply gdec_true in h
      | h : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in h
      | h : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in h
      end.
    repeat split; assumption.
  Qed.

  (** Arithmetic helpers for the Hadamard proof.

      [fsum_shift]: [Σ_(i<k+1) f i = f 0 + Σ_(i<k) f (i+1)]. *)
  Lemma fsum_shift : forall (f : nat -> F) (k : nat), fsum f (S k) = f 0%nat + fsum (fun i => f (S i)) k.
  Proof.
    intros f k; induction k as [| k ih]; [cbn; field |].
    change (fsum f (S (S k))) with (fsum f (S k) + f (S k)). rewrite ih.
    change (fsum (fun i => f (S i)) (S k)) with (fsum (fun i => f (S i)) k + f (S k)). field.
  Qed.

  (** The zero-argument sum [Σ_i A_i ⋆_y B_i] written with [fold_right] over
      [combine A B] equals the indexed sum [fsum] when both lists have
      length [k]. *)
  Lemma fold_combine_fsum : forall (y : F) (A B : list (list F)) (k : nat), length A = k -> length B = k ->
    fold_right add zero (map (fun p => star y (fst p) (snd p)) (combine A B)) = fsum (fun i => star y (nth i A []) (nth i B [])) k.
  Proof.
    intros y A B k; revert A B; induction k as [| k ih]; intros A B hA hB.
    + destruct A; [| discriminate]; reflexivity.
    + destruct A as [| a A]; [discriminate |]. destruct B as [| b B]; [discriminate |].
      cbn [combine map fold_right length fst snd] in *. rewrite (ih A B) by lia.
      rewrite (fsum_ext _ (fun i => star y (nth (S i) (a :: A) []) (nth (S i) (b :: B) [])) k) by (intros; reflexivity).
      change (fsum (fun i => star y (nth (S i) (a :: A) []) (nth (S i) (b :: B) [])) k) with
        (fsum (fun i => (fun j => star y (nth j (a :: A) []) (nth j (b :: B) [])) (S i)) k).
      change (star y a b) with ((fun j => star y (nth j (a :: A) []) (nth j (b :: B) [])) 0%nat).
      generalize (fun j => star y (nth j (a :: A) []) (nth j (b :: B) [])); intros f.
      symmetry; apply fsum_shift.
  Qed.

  (** [star_w_ones], [star_ones_feval]: pairing with the all-ones vector
      evaluates the other vector as a polynomial, [(1,…,1) ⋆_y v = y ·
      v(y)], provided [length v ≤ n]. This turns the vector identities
      of the Hadamard argument into polynomial identities in [y]. *)
  Lemma star_w_ones : forall (n : nat) (v : list F) (w y : F), (length v <= n)%nat ->
    star_w w y (repeat one n) v = w * feval v y.
  Proof.
    intros n v; revert n; induction v as [| v0 v ih]; intros n w y hl.
    + rewrite star_w_nil_r, veval_nil; field.
    + destruct n as [| n]; [cbn in hl; lia |]. cbn [repeat star_w]. rewrite ih by (cbn in hl; lia).
      rewrite (veval_cons (HV := F_vspace (Hvec := Hvec))); field.
  Qed.

  Lemma star_ones_feval : forall (n : nat) (v : list F) (y : F), (length v <= n)%nat ->
    star y (repeat one n) v = y * feval v y.
  Proof. intros; unfold BayerGroth.star; apply star_w_ones; assumption. Qed.

  (** [⋆_y] is additive in its right argument. *)
  Lemma star_padd_r : forall y a u v, star y a (padd u v) = star y a u + star y a v.
  Proof. intros; unfold BayerGroth.star; apply (star_w_padd_r (Hvec := Hvec)). Qed.

  (** The entrywise product [hmul] is commutative. *)
  Lemma hmul_comm : forall a b : list F, hmul a b = hmul b a.
  Proof.
    induction a as [| a0 a ih]; intros b; destruct b as [| b0 b]; try reflexivity.
    unfold BayerGroth.hmul in *; cbn [combine map fst snd]; rewrite ih; f_equal; field.
  Qed.

  (** Adding the zero vector of the same length is the identity. *)
  Lemma padd_zeros : forall (n : nat) (v : list F), length v = n -> padd (repeat zero n) v = v.
  Proof.
    induction n as [| n ih]; intros v hl; destruct v as [| v0 v]; try discriminate; [reflexivity |].
    cbn [repeat SigmaK.padd]; rewrite ih by (cbn in hl; lia); f_equal; field.
  Qed.

  (** [com((0,…,0); 0)] is the group identity. *)
  Lemma com_zeros : forall h gs (n : nat), com h gs (repeat zero n) zero = gid.
  Proof. intros; unfold BayerGroth.com; rewrite gpow_zero, (lmexp_repeat_zero (HV := Hvec)), gid_l; reflexivity. Qed.

  (** If [c^x = com(v; t)] and [x ≠ 0], then [c = com(x⁻¹ v; x⁻¹ t)]. Used
      to open [c_(B_0)] from the commitment [c_(B_0)^x] that appears in the
      zero-argument statement. *)
  Lemma open_pow : forall h gs (c : G) (x : F) (v : list F) (t : F), x <> zero ->
    c ^ x = com h gs v t -> c = com h gs (lscale (inv x) v) (inv x * t).
  Proof.
    intros * hx he. rewrite (com_scale (Hvec := Hvec)), <-he, <-(gpow_mul (Hvec := Hvec)).
    replace (x * inv x) with one by (field; exact hx). rewrite (gpow_one (Hvec := Hvec)); reflexivity.
  Qed.

  (** Special soundness of the Hadamard argument. Hypotheses: [length gs =
      n ≥ 1], [length cA = m ≥ 2]; [X] is a list of [m] distinct challenges
      [x] and [Y] a list of [n] distinct challenges [y]; the Hadamard first
      message [cB] is fixed, and for every pair [(x_p, y_q)] there is a zero
      argument tree: [2m+1] distinct challenges [zs p q] with fixed first
      message [(cA0 p q, cBm p q, cd p q)], all accepted. (Non-zeroness of
      the challenges is checked by the verifier, so it is not assumed.)
      Conclusion: either binding breaks or there are openings [A] (with
      randomness [r]) of [cA] and [(b, sb)] of [cb], all vectors of length
      [n], with [b = hprefix A (m-1) = A_0 ∘ … ∘ A_(m-1)].

      Proof idea: [zero_soundness_ext] at every pair [(p, q)] opens the
      zero statement. Binding identifies the openings across pairs: the
      openings of [tl cA] do not depend on [(p, q)]; [c_(B_0)] is opened
      by [open_pow]; [c_(B_1) … c_(B_(m-1))] are opened by applying
      [geval_openings] to the last zero-statement commitment [geval (1 ::
      tl cB) x_p] at the [m] values [x_p]. The zero-argument conclusion then
      reads [x · Σ_i x^i c_(q,i) = 0] with [c_(q,i) = A_(i+1) ⋆_y B_i −
      (1,…,1) ⋆_y B_(i+1)]; since [x_p ≠ 0] and the [m] points exceed the
      degree [m-2], all [c_(q,i) = 0]. By [star_w_hmul] and [star_ones_feval],
      [c_(q,i) = y_q · D(y_q)] for the vector [D = A_(i+1) ∘ B_i − B_(i+1)]
      of length [n], and [n] non-zero roots [y_q] force [D = 0]. Hence
      [B_(i+1) = A_(i+1) ∘ B_i], and induction gives [B_(m-1) = hprefix A
      (m-1)]. *)
  Theorem hadamard_soundness : forall (h : G) (gs : list G) (cA : list G) (cb : G) (cB : list G) (X Y : list F)
    (cA0 cBm : nat -> nat -> G) (cd : nat -> nat -> list G) (zs : nat -> nat -> list F)
    (za zb : nat -> nat -> nat -> list F) (zr zt zu : nat -> nat -> nat -> F),
    (1 <= length gs)%nat -> (2 <= length cA)%nat ->
    NoDup X -> length X = length cA -> NoDup Y -> length Y = length gs ->
    (forall p q, (p < length cA)%nat -> (q < length gs)%nat ->
      NoDup (zs p q) /\ length (zs p q) = (2 * length cA + 1)%nat /\
      forall j, (j < 2 * length cA + 1)%nat ->
        hadamard_verify h gs (length gs) cA cb (nth p X zero) (nth q Y zero) (nth j (zs p q) zero)
          (mk_had cB (mk_zero (cA0 p q) (cBm p q) (cd p q) (za p q j) (zb p q j) (zr p q j) (zt p q j) (zu p q j))) = true) ->
    (exists (A : list (list F)) (r : list F) (b : list F) (sb : F),
      cA = com_list h gs A r /\ cb = com h gs b sb /\ length A = length cA /\ length r = length cA /\
      (forall v, In v A -> length v = length gs) /\ length b = length gs /\ b = hprefix A (length cA - 1))
    \/ binding_break h gs.
  Proof.
    intros h gs cA cb cB X Y cA0 cBm cd zs za zb zr zt zu hn hm hXnd hXl hYnd hYl htr0.
    assert (htr : forall p q, (p < length cA)%nat -> (q < length gs)%nat ->
      NoDup (zs p q) /\ length (zs p q) = (2 * length cA + 1)%nat /\
      forall j, (j < 2 * length cA + 1)%nat -> length (za p q j) = length gs /\ length (zb p q j) = length gs /\
        hadamard_verify h gs (length gs) cA cb (nth p X zero) (nth q Y zero) (nth j (zs p q) zero)
          (mk_had cB (mk_zero (cA0 p q) (cBm p q) (cd p q) (za p q j) (zb p q j) (zr p q j) (zt p q j) (zu p q j))) = true).
    { intros p q hp hq. destruct (htr0 p q hp hq) as (h1 & h2 & h3). split; [exact h1 | split; [exact h2 |]].
      intros j hj. pose proof (h3 j hj) as hv. destruct (hadamard_verify_lengths hv) as (l1 & l2). repeat split; assumption. }
    assert (hX0 : forall x, In x X -> x <> zero).
    { intros x0 hx. destruct (In_nth X x0 zero hx) as (p & hp & <-).
      destruct (htr0 p 0%nat ltac:(lia) ltac:(lia)) as (_ & _ & h3). exact (proj1 (hadamard_verify_nonzero (h3 0%nat ltac:(lia)))). }
    assert (hY0 : forall y, In y Y -> y <> zero).
    { intros y0 hy. destruct (In_nth Y y0 zero hy) as (q & hq & <-).
      destruct (htr0 0%nat q ltac:(lia) ltac:(lia)) as (_ & _ & h3). exact (proj2 (hadamard_verify_nonzero (h3 0%nat ltac:(lia)))). }
    set (m := length cA) in *. set (n := length gs) in *.
    assert (hm_eq : length cA = m) by reflexivity. assert (hn_eq : length gs = n) by reflexivity.
    set (x := fun p => nth p X zero). set (y := fun q => nth q Y zero).
    set (cneg := com h gs (repeat (opp one) n) zero).
    set (cDs := fun p => map (fun i => (nth i cB gid) ^ (fpow (x p) (S i))) (seq 0 (m - 1)%nat)).
    set (cD := fun p => (geval (tl cB) (x p)) ^ (x p)).
    assert (hcB : length cB = m).
    { destruct (htr 0%nat 0%nat ltac:(lia) ltac:(lia)) as (_ & hl & hj); destruct (hj 0%nat ltac:(lia)) as (_ & _ & hv).
      apply hadamard_verify_true in hv; tauto. }
    assert (hcB0 : nth 0 cB gid = nth 0 cA gid).
    { destruct (htr 0%nat 0%nat ltac:(lia) ltac:(lia)) as (_ & hl & hj); destruct (hj 0%nat ltac:(lia)) as (_ & _ & hv).
      apply hadamard_verify_true in hv; tauto. }
    assert (hcBm : nth (m - 1)%nat cB gid = cb).
    { destruct (htr 0%nat 0%nat ltac:(lia) ltac:(lia)) as (_ & hl & hj); destruct (hj 0%nat ltac:(lia)) as (_ & _ & hv).
      apply hadamard_verify_true in hv; tauto. }
    set (ZA := fun p q => zopenA m (zs p q) (za p q)). set (ZR := fun p q => zopenr m (zs p q) (zr p q)).
    set (ZB := fun p q => zopenB m (zs p q) (zb p q)). set (ZT := fun p q => zopens m (zs p q) (zt p q)).
    (* Zero-argument soundness at every pair of challenges (x_p, y_q). *)
    assert (hz : (forall p, (p < m)%nat -> forall q, (q < n)%nat ->
        tl cA ++ [cneg] = com_list h gs (ZA p q) (ZR p q) /\
        cDs p ++ [cD p] = com_list h gs (ZB p q) (ZT p q) /\
        (forall v, In v (ZA p q) -> length v = n) /\ (forall v, In v (ZB p q) -> length v = n) /\
        fold_right add zero (map (fun pr => star (y q) (fst pr) (snd pr)) (combine (ZA p q) (ZB p q))) = zero)
      \/ binding_break h gs).
    { apply forall_or; intros p hp. apply forall_or; intros q hq.
      destruct (htr p q hp hq) as (hnd & hl & hj).
      assert (hlen : length (tl cA ++ [cneg]) = m) by (rewrite length_app, tl_len; cbn [length]; lia).
      destruct (zero_soundness_ext h gs (tl cA ++ [cneg]) (cDs p ++ [cD p]) (y q) (cA0 p q) (cBm p q) (cd p q) (zs p q)
        (za p q) (zb p q) (zr p q) (zt p q) (zu p q) hn hnd) as [(h1 & h2 & h3 & h4 & h5) | hbb].
      + rewrite hlen; exact hl.
      + intros j hj'; rewrite hl in hj'. destruct (hj j hj') as (_ & _ & hv). apply hadamard_verify_true in hv.
        destruct hv as (_ & _ & _ & _ & hv). exact hv.
      + left. rewrite hlen in h1, h2, h3, h4, h5. exact (conj h1 (conj h2 (conj h3 (conj h4 h5)))).
      + right; exact hbb. }
    destruct hz as [hz | hbb]; [| right; exact hbb].
    assert (hZAl : forall p q, length (ZA p q) = m) by (intros; apply zopenA_length).
    assert (hZBl : forall p q, length (ZB p q) = m) by (intros; apply zopenB_length).
    assert (hZRl : forall p q, length (ZR p q) = m) by (intros; apply zopenr_length).
    assert (hZTl : forall p q, length (ZT p q) = m) by (intros; apply zopens_length).
    (* Read off the components: openings of tl cA, of com(−1; 0), of the
       scaled c_(B_i) and of the last commitment cD. *)
    assert (hA : forall p q i, (p < m)%nat -> (q < n)%nat -> (i < m - 1)%nat ->
      nth (S i) cA gid = com h gs (nth i (ZA p q) []) (nth i (ZR p q) zero)).
    { intros p q i hp hq hi. destruct (hz p hp q hq) as (h1 & _).
      rewrite <-(nth_tl cA i gid) by (destruct cA; [cbn in hm; lia | discriminate]).
      rewrite <-(app_nth1 (tl cA) [cneg] gid) by (rewrite tl_len; lia).
      rewrite h1, (nth_com_list (zero := zero)) by (rewrite ?hZAl, ?hZRl; lia). reflexivity. }
    assert (hneg : forall p q, (p < m)%nat -> (q < n)%nat ->
      cneg = com h gs (nth (m - 1)%nat (ZA p q) []) (nth (m - 1)%nat (ZR p q) zero)).
    { intros p q hp hq. destruct (hz p hp q hq) as (h1 & _).
      assert (e : cneg = nth (m - 1)%nat (tl cA ++ [cneg]) gid).
      { rewrite app_nth2 by (rewrite tl_len; lia). rewrite tl_len, hm_eq. replace (m - 1 - (m - 1)%nat)%nat with 0%nat by lia. reflexivity. }
      rewrite e, h1, (nth_com_list (zero := zero)) by (rewrite ?hZAl, ?hZRl; lia). reflexivity. }
    assert (hBi : forall p q i, (p < m)%nat -> (q < n)%nat -> (i < m - 1)%nat ->
      (nth i cB gid) ^ (fpow (x p) (S i)) = com h gs (nth i (ZB p q) []) (nth i (ZT p q) zero)).
    { intros p q i hp hq hi. destruct (hz p hp q hq) as (_ & h2 & _).
      assert (e : (nth i cB gid) ^ (fpow (x p) (S i)) = nth i (cDs p ++ [cD p]) gid).
      { rewrite app_nth1 by (unfold cDs; rewrite length_map, length_seq; lia). unfold cDs.
        rewrite (PolyPerm.nth_map_seq (fun i => (nth i cB gid) ^ (fpow (x p) (S i))) (m - 1)%nat i gid hi). reflexivity. }
      rewrite e, h2, (nth_com_list (zero := zero)) by (rewrite ?hZBl, ?hZTl; lia). reflexivity. }
    assert (hDp : forall p q, (p < m)%nat -> (q < n)%nat ->
      cD p = com h gs (nth (m - 1)%nat (ZB p q) []) (nth (m - 1)%nat (ZT p q) zero)).
    { intros p q hp hq. destruct (hz p hp q hq) as (_ & h2 & _).
      assert (e : cD p = nth (m - 1)%nat (cDs p ++ [cD p]) gid).
      { rewrite app_nth2 by (unfold cDs; rewrite length_map, length_seq; lia). unfold cDs; rewrite length_map, length_seq.
        replace (m - 1 - (m - 1)%nat)%nat with 0%nat by lia. reflexivity. }
      rewrite e, h2, (nth_com_list (zero := zero)) by (rewrite ?hZBl, ?hZTl; lia). reflexivity. }
    assert (hZAn : forall p q i, (p < m)%nat -> (q < n)%nat -> (i < m)%nat -> length (nth i (ZA p q) []) = n).
    { intros p q i hp hq hi. destruct (hz p hp q hq) as (_ & _ & h3 & _). apply h3, nth_In; rewrite hZAl; exact hi. }
    assert (hZBn : forall p q i, (p < m)%nat -> (q < n)%nat -> (i < m)%nat -> length (nth i (ZB p q) []) = n).
    { intros p q i hp hq hi. destruct (hz p hp q hq) as (_ & _ & _ & h4 & _). apply h4, nth_In; rewrite hZBl; exact hi. }
    assert (hx0 : x 0%nat <> zero) by (apply hX0; unfold x; apply nth_In; lia).
    (* Reference openings of tl cA from the pair (0, 0); c_(B_0) from
       c_(B_0)^(x_0); c_(B_1) … c_(B_(m-1)) from cD(x_p) = geval (1 :: tl cB)
       x_p at the m values x_p by the inverse Vandermonde matrix. *)
    set (Aop := fun i => nth i (ZA 0 0) []). set (rop := fun i => nth i (ZR 0 0) zero).
    assert (hcDgeval : forall p, cD p = geval (gid :: tl cB) (x p)).
    { intros p; unfold cD; rewrite (veval_cons_vid (HV := Hvec)); reflexivity. }
    set (Bz := fun i => lcomb (lam X i) (fun p => nth (m - 1)%nat (ZB p 0) []) m).
    set (sz := fun i => fsum (fun p => lam X i p * nth (m - 1)%nat (ZT p 0) zero) m).
    assert (hopenB : forall i, (i < m)%nat -> nth i (gid :: tl cB) gid = com h gs (Bz i) (sz i)).
    { intros i hi. unfold Bz, sz.
      pose proof (geval_openings h gs X (gid :: tl cB) (fun p => nth (m - 1)%nat (ZB p 0) []) (fun p => nth (m - 1)%nat (ZT p 0) zero) hXnd
        ltac:(cbn [length]; rewrite tl_len, hXl; lia)
        ltac:(intros p hp; rewrite hXl in hp; fold (x p); rewrite <-hcDgeval; apply hDp; lia) i ltac:(rewrite hXl; lia)) as h1.
      rewrite hXl in h1. exact h1. }
    set (Bop := fun i => match i with 0 => lscale (inv (x 0%nat)) (nth 0 (ZB 0 0) []) | S _ => Bz i end).
    set (sop := fun i => match i with 0 => inv (x 0%nat) * nth 0 (ZT 0 0) zero | S _ => sz i end).
    assert (hB : forall i, (i < m)%nat -> nth i cB gid = com h gs (Bop i) (sop i)).
    { intros i hi. destruct i as [| i].
      + unfold Bop, sop. apply open_pow; [exact hx0 |].
        pose proof (hBi 0%nat 0%nat 0%nat ltac:(lia) ltac:(lia) ltac:(lia)) as h1. cbn [fpow] in h1.
        replace (x 0%nat * one) with (x 0%nat) in h1 by field. exact h1.
      + pose proof (hopenB (S i) hi) as h1. cbn [nth] in h1. rewrite nth_tl in h1 by (destruct cB; [cbn in hcB; lia | discriminate]).
        exact h1. }
    assert (hBn : forall i, (i < m)%nat -> length (Bop i) = n).
    { intros i hi. destruct i as [| i].
      + unfold Bop, SigmaK.lscale; rewrite length_map; apply hZBn; lia.
      + unfold Bop, Bz; apply lcomb_length; [lia |]. intros p hp; apply hZBn; lia. }
    assert (hAn : forall i, (i < m - 1)%nat -> length (Aop i) = n) by (intros i hi; unfold Aop; apply hZAn; lia).
    assert (hcBl : cB = com_list h gs (map Bop (seq 0 m)) (map sop (seq 0 m))) by (apply com_list_of_openings; [exact hcB | exact hB]).
    assert (htl : gid :: tl cB = com_list h gs (repeat zero n :: map (fun i => Bop (S i)) (seq 0 (m - 1)%nat)) (zero :: map (fun i => sop (S i)) (seq 0 (m - 1)%nat))).
    { rewrite com_list_cons, com_zeros. f_equal.
      assert (hseq : seq 0 m = 0%nat :: map S (seq 0 (m - 1)%nat)).
      { transitivity (seq 0 (S (m - 1)%nat)); [f_equal; lia |]. cbn [seq]. rewrite seq_shift; reflexivity. }
      rewrite hcBl, hseq. cbn [map BayerGroth.com_list combine tl]. rewrite !map_map. reflexivity. }
    (* By binding, at every (p, q) the zero-argument openings are expressed
       in terms of the reference openings Aop and Bop. *)
    assert (hbind : (forall p, (p < m)%nat -> forall q, (q < n)%nat ->
        (forall i, (i < m - 1)%nat -> nth i (ZA p q) [] = Aop i) /\
        nth (m - 1)%nat (ZA p q) [] = repeat (opp one) n /\
        (forall i, (i < m - 1)%nat -> nth i (ZB p q) [] = lscale (fpow (x p) (S i)) (Bop i)) /\
        nth (m - 1)%nat (ZB p q) [] = lveval (repeat zero n :: map (fun i => Bop (S i)) (seq 0 (m - 1)%nat)) (x p))
      \/ binding_break h gs).
    { apply forall_or; intros p hp. apply forall_or; intros q hq.
      assert (hA' : (forall i, (i < m - 1)%nat -> nth i (ZA p q) [] = Aop i) \/ binding_break h gs).
      { apply forall_or; intros i hi.
        pose proof (hA p q i hp hq hi) as e1. rewrite (hA 0%nat 0%nat i ltac:(lia) ltac:(lia) hi) in e1.
        destruct (open_eq_or_break_len h gs _ _ _ _ (hZAn 0 0 i ltac:(lia) ltac:(lia) ltac:(lia)) (hZAn p q i hp hq ltac:(lia)) e1)
          as [[e _] | hbb]; [left; symmetry; exact e | right; exact hbb]. }
      destruct hA' as [hA' | hbb]; [| right; exact hbb].
      assert (hneg' : nth (m - 1)%nat (ZA p q) [] = repeat (opp one) n \/ binding_break h gs).
      { pose proof (hneg p q hp hq) as e1. unfold cneg in e1.
        destruct (open_eq_or_break_len h gs _ _ _ _ (repeat_length (opp one) n) (hZAn p q (m - 1)%nat hp hq ltac:(lia)) e1)
          as [[e _] | hbb]; [left; symmetry; exact e | right; exact hbb]. }
      destruct hneg' as [hneg' | hbb]; [| right; exact hbb].
      assert (hB' : (forall i, (i < m - 1)%nat -> nth i (ZB p q) [] = lscale (fpow (x p) (S i)) (Bop i)) \/ binding_break h gs).
      { apply forall_or; intros i hi.
        pose proof (hBi p q i hp hq hi) as e1. rewrite (hB i ltac:(lia)), <-(com_scale (Hvec := Hvec)) in e1.
        assert (hl1 : length (lscale (fpow (x p) (S i)) (Bop i)) = length gs)
          by (unfold SigmaK.lscale; rewrite length_map; apply hBn; lia).
        destruct (open_eq_or_break_len h gs _ _ _ _ hl1 (hZBn p q i hp hq ltac:(lia)) e1)
          as [[e _] | hbb]; [left; symmetry; exact e | right; exact hbb]. }
      destruct hB' as [hB' | hbb]; [| right; exact hbb].
      assert (hD' : nth (m - 1)%nat (ZB p q) [] = lveval (repeat zero n :: map (fun i => Bop (S i)) (seq 0 (m - 1)%nat)) (x p) \/ binding_break h gs).
      { pose proof (hDp p q hp hq) as e1. rewrite hcDgeval, htl, (geval_com_list (Hvec := Hvec)) in e1
          by (cbn [length]; rewrite !length_map; reflexivity).
        assert (hl1 : length (lveval (repeat zero n :: map (fun i => Bop (S i)) (seq 0 (m - 1)%nat)) (x p)) = length gs).
        { apply lveval_length; [discriminate |].
          intros v hv; destruct hv as [<- | hv]; [apply repeat_length |].
          apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hBn; lia. }
        destruct (open_eq_or_break_len h gs _ _ _ _ hl1 (hZBn p q (m - 1)%nat hp hq ltac:(lia)) e1)
          as [[e _] | hbb]; [left; symmetry; exact e | right; exact hbb]. }
      destruct hD' as [hD' | hbb]; [| right; exact hbb].
      left; repeat split; assumption. }
    destruct hbind as [hbind | hbb]; [| right; exact hbb].
    assert (hfm : forall (g : nat -> F) (x0 : F) k, x0 * feval (map g (seq 0 k)) x0 = fsum (fun i => fpow x0 (S i) * g i) k).
    { intros g x0 k. rewrite <-sum_pow_feval_w, <-fsum_fold. apply fsum_ext; intros i _; cbn [fpow]; field. }
    assert (hfs : forall (f g : nat -> F) k, fsum (fun i => f i - g i) k = fsum f k - fsum g k).
    { intros f g k; induction k as [| k ihk]; cbn [fsum]; [field | rewrite ihk; field]. }
    (* The relation x · Σ_i x^i (A_(i+1) ⋆ B_i − 1 ⋆ B_(i+1)) = 0 at every
       (x_p, y_q). *)
    set (c := fun q i => star (y q) (Aop i) (Bop i) - star (y q) (repeat one n) (Bop (S i))).
    assert (hrel : forall p q, (p < m)%nat -> (q < n)%nat -> x p * feval (map (c q) (seq 0 (m - 1)%nat)) (x p) = zero).
    { intros p q hp hq. destruct (hz p hp q hq) as (_ & _ & _ & _ & h5). destruct (hbind p hp q hq) as (eA & eneg & eB & eD).
      rewrite (fold_combine_fsum _ _ _ m (hZAl p q) (hZBl p q)) in h5.
      replace m with (S (m - 1)%nat) in h5 by lia. cbn [fsum] in h5. rewrite eneg, eD in h5.
      rewrite (fsum_ext _ (fun i => fpow (x p) (S i) * star (y q) (Aop i) (Bop i)) (m - 1)%nat) in h5.
      2: { intros i hi. rewrite eA, eB by lia. apply (star_lscale_r (Hvec := Hvec)). }
      rewrite lveval_cons, padd_zeros in h5.
      2: { unfold SigmaK.lscale; rewrite length_map. apply lveval_length; [destruct m as [| [| m']]; try lia; cbn [seq map]; discriminate |].
           intros v hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hBn; lia. }
      rewrite (neg_ones (Hvec := Hvec)), (star_lscale_l (Hvec := Hvec)), (star_lscale_r (Hvec := Hvec)) in h5.
      rewrite <-(star_lveval_r (Hvec := Hvec)), map_map, hfm in h5.
      rewrite hfm. unfold c.
      rewrite (fsum_ext _ (fun i => fpow (x p) (S i) * star (y q) (Aop i) (Bop i) - fpow (x p) (S i) * star (y q) (repeat one n) (Bop (S i))) (m - 1)%nat)
        by (intros; field).
      rewrite hfs.
      match goal with |- ?a - ?b = zero => transitivity (a + opp one * b); [field | exact h5] end. }
    (* Dividing by x_p ≠ 0, a polynomial of degree below m vanishes at the
       m distinct x_p, so each coefficient c q i is zero. *)
    assert (hc : forall q i, (q < n)%nat -> (i < m - 1)%nat -> c q i = zero).
    { intros q i hq hi.
      assert (hev : forall p, (p < m)%nat -> feval (map (c q) (seq 0 (m - 1)%nat)) (x p) = zero).
      { intros p hp. pose proof (hrel p q hp hq) as h1.
        assert (hxp : x p <> zero) by (apply hX0; unfold x; apply nth_In; lia).
        destruct (mul_eq_zero (Fdec := Fdec) (Hf := Hf) _ _ h1) as [h2 | h2]; [contradiction | exact h2]. }
      pose proof (agree_nth (Fdec := Fdec) (Hf := Hf) X (map (c q) (seq 0 (m - 1)%nat)) [] hXnd) as hag.
      rewrite length_map, length_seq, hXl in hag. specialize (hag ltac:(lia) ltac:(cbn; lia)).
      assert (hag' : forall x0, In x0 X -> eval (map (c q) (seq 0 (m - 1)%nat)) x0 = eval [] x0).
      { intros x0 hx. destruct (In_nth X x0 zero hx) as (p & hp & <-). rewrite <-(feval_eval (Hvec := Hvec)). cbn [eval]. apply hev; lia. }
      specialize (hag hag' i). rewrite (PolyPerm.nth_map_seq (c q) (m - 1)%nat i zero hi) in hag. destruct i; exact hag. }
    (* The vector D = A_(i+1) ∘ B_i − B_(i+1) has n entries and its
       polynomial vanishes at the n non-zero y_q; hence the Hadamard step
       B_(i+1) = A_(i+1) ∘ B_i. *)
    assert (hstep : forall i, (i < m - 1)%nat -> Bop (S i) = hmul (Aop i) (Bop i)).
    { intros i hi.
      set (D := padd (hmul (Aop i) (Bop i)) (lscale (opp one) (Bop (S i)))).
      assert (hDl : length D = n).
      { unfold D; rewrite SigmaK.padd_length, hmul_length; unfold SigmaK.lscale; rewrite length_map, hAn, !hBn by lia; lia. }
      assert (hDev : forall q, (q < n)%nat -> feval D (y q) = zero).
      { intros q hq. pose proof (hc q i hq hi) as h1. unfold c in h1.
        assert (hyq : y q <> zero) by (apply hY0; unfold y; apply nth_In; lia).
        assert (h2 : star (y q) (repeat one n) D = zero).
        { unfold D. rewrite star_padd_r, (star_lscale_r (Hvec := Hvec)).
          unfold BayerGroth.star at 1. rewrite (star_w_hmul (Hvec := Hvec)), (hmul_ones (Hvec := Hvec) n) by (apply hAn; exact hi).
          fold (star (y q) (Aop i) (Bop i)).
          transitivity (star (y q) (Aop i) (Bop i) - star (y q) (repeat one n) (Bop (S i))); [field | exact h1]. }
        rewrite star_ones_feval in h2 by lia.
        destruct (mul_eq_zero (Fdec := Fdec) (Hf := Hf) _ _ h2) as [h3 | h3]; [contradiction | exact h3]. }
      pose proof (agree_nth (Fdec := Fdec) (Hf := Hf) Y D [] hYnd) as hag.
      rewrite hDl, hYl in hag. specialize (hag (le_n _) ltac:(cbn; lia)).
      assert (hag' : forall y0, In y0 Y -> eval D y0 = eval [] y0).
      { intros y0 hy. destruct (In_nth Y y0 zero hy) as (q & hq & <-). rewrite <-(feval_eval (Hvec := Hvec)). cbn [eval]. apply hDev; lia. }
      specialize (hag hag').
      apply (nth_ext _ _ zero zero); [rewrite hmul_length, hAn, !hBn by lia; lia |].
      intros j hj. rewrite hBn in hj by lia. specialize (hag j). unfold D in hag.
      rewrite (SigmaK.nth_padd (Hf := Hf)), (SigmaK.nth_lscale (Hf := Hf)) in hag.
      assert (hz0 : nth j [] zero = zero) by (destruct j; reflexivity). rewrite hz0 in hag.
      symmetry; apply sub_eq_zero. match goal with |- ?a - ?b = zero => transitivity (a + opp one * b); [field | exact hag] end. }
    (* Assemble the openings of cA and conclude b = hprefix A (m − 1) by
       induction on the prefix. *)
    set (A := Bop 0%nat :: map Aop (seq 0 (m - 1)%nat)). set (r := sop 0%nat :: map rop (seq 0 (m - 1)%nat)).
    assert (hcAl : cA = com_list h gs A r).
    { apply (nth_ext _ _ gid gid).
      + rewrite com_list_length; unfold A, r; cbn [length]; rewrite !length_map, !length_seq; lia.
      + intros i hi. rewrite (nth_com_list (zero := zero)) by (unfold A, r; cbn [length]; rewrite ?length_map, ?length_seq; lia).
        destruct i as [| i].
        - unfold A, r; cbn [nth]. rewrite <-hcB0. apply hB; lia.
        - unfold A, r; cbn [nth]. rewrite !(PolyPerm.nth_map_seq) by lia. apply hA; lia. }
    assert (hAl : length A = m) by (unfold A; cbn [length]; rewrite length_map, length_seq; lia).
    assert (hAall : forall v, In v A -> length v = n).
    { intros v hv. destruct hv as [<- | hv]; [apply hBn; lia |]. apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hAn; lia. }
    assert (hpref : forall j, (j < m)%nat -> hprefix A j = Bop j).
    { intros j; induction j as [| j ih]; intros hj.
      + rewrite hprefix_0 by (unfold A; discriminate). reflexivity.
      + rewrite hprefix_S by lia. rewrite ih by lia. rewrite hstep by lia. rewrite hmul_comm. f_equal.
        unfold A; cbn [nth]. rewrite PolyPerm.nth_map_seq by lia. reflexivity. }
    left. exists A, r, (Bop (m - 1)%nat), (sop (m - 1)%nat).
    split; [exact hcAl |].
    split; [rewrite <-hcBm; apply hB; lia |].
    split; [exact hAl |].
    split; [unfold r; cbn [length]; rewrite length_map, length_seq; lia |].
    split; [exact hAall |].
    split; [apply hBn; lia |].
    symmetry; apply hpref; lia.
  Qed.

  (** ** Single value product argument: (n+1)-special soundness

      Statement: a commitment [ca] and a scalar [b]. Claim: [ca] opens to a
      vector [a] of length [n] with [∏_i a_i = b]. The prover commits to
      a blinder [d] ([cd]), and to [δ], [Δ] ([cδ], [cΔ]) for the running
      products [b_i = a_0 ⋯ a_i]; the responses are [ã = x a + d], [b̃]
      with [b̃_0 = ã_0], [b̃_(n-1) = x b], and the verifier checks
      [x b̃_(i+1) − b̃_i ã_(i+1)] against [x Δ + δ]. *)
  Local Notation svp_verify := (svp_verify (zero := zero) (mul := mul) (sub := sub) (Fdec := Fdec)
    (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation mk_svp := (@mk_svp F G).

  (** The single value product verifier checks [length ã = length gs]. *)
  Lemma svp_verify_length {h gs ca b x cd cδ cΔ ta tb rt st} :
    svp_verify h gs ca b x (mk_svp cd cδ cΔ ta tb rt st) = true -> length ta = length gs.
  Proof.
    intros hv; unfold BayerGroth.svp_verify in hv; cbv zeta in hv; cbn [svp_a] in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    match goal with h : (length ta =? length gs)%nat = true |- _ => apply Nat.eqb_eq in h; exact h end.
  Qed.

  (** Unpacking of an accepting single value product transcript: [n ≥ 2],
      [length b̃ = n], [ca^x · cd = com(ã; r̃)], [cΔ^x · cδ = com(e; s̃)]
      with [e_i = x b̃_(i+1) − b̃_i ã_(i+1)], [b̃_0 = ã_0] and [b̃_(n-1) = x
      b]. *)
  Lemma svp_verify_true : forall h gs ca b x cd cδ cΔ ta tb rt st,
    svp_verify h gs ca b x (mk_svp cd cδ cΔ ta tb rt st) = true ->
    (2 <= length ta)%nat /\ length tb = length ta /\
    gop (ca ^ x) cd = com h gs ta rt /\
    gop (cΔ ^ x) cδ = com h gs (map (fun i => x * nth (S i) tb zero - nth i tb zero * nth (S i) ta zero) (seq 0 (length ta - 1))) st /\
    nth 0 tb zero = nth 0 ta zero /\ nth (length ta - 1) tb zero = x * b.
  Proof.
    intros * hv; unfold BayerGroth.svp_verify in hv; cbv zeta in hv;
      cbn [svp_cd svp_cdelta svp_cDelta svp_a svp_b svp_r svp_s] in hv.
    repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
    repeat match goal with
      | h : (if Gdec ?u ?v then true else false) = true |- _ => apply gdec_true in h
      | h : (if Fdec ?u ?v then true else false) = true |- _ => apply fdec_true in h
      | h : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in h
      | h : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in h
      end.
    repeat split; assumption.
  Qed.

  (** Helpers: [geval_pair] evaluates a committed linear polynomial,
      [geval [c0; c1] x = c0 · c1^x]. *)
  Lemma geval_pair : forall (c0 c1 : G) (x : F), geval [c0; c1] x = gop c0 (c1 ^ x).
  Proof.
    intros; rewrite !(veval_cons (HV := Hvec)), veval_nil, (smul_vid (HV := Hvec)), gid_r; reflexivity.
  Qed.

  (** Prepending [i] zero coefficients multiplies the polynomial by [x^i]. *)
  Lemma eval_shift : forall (i : nat) (p : list F) (x : F), eval (repeat zero i ++ p) x = fpow x i * eval p x.
  Proof.
    induction i as [| i ih]; intros p x; cbn [repeat app fpow eval]; [field | rewrite ih; field].
  Qed.

  (** The coefficient of [X^(k+1)] in [p · (c0 + c1 X)] for [deg p = k] is
      [p_k · c1]. *)
  Lemma pmulF_lead : forall (p : list F) (k : nat) (c0 c1 : F), length p = S k ->
    nth (S k) (pmulF p [c0; c1]) zero = nth k p zero * c1.
  Proof.
    induction p as [| c p ih]; intros k c0 c1 hl; [discriminate |].
    cbn [pmulF]; rewrite (SigmaK.nth_padd (Hf := Hf)); cbn [length] in hl.
    destruct k as [| k].
    + destruct p; [| discriminate]. cbn; field.
    + cbn [nth]. rewrite (nth_overflow (lscale c [c0; c1])) by (cbn; lia).
      rewrite ih by lia; field.
  Qed.

  (** [x^n = x · x^(n-1)] for [n > 0]. *)
  Lemma fpow_pred : forall (x : F) (n : nat), (0 < n)%nat -> fpow x n = x * fpow x (n - 1).
  Proof. intros x n hn; destruct n; [lia | replace (S n - 1)%nat with n by lia; reflexivity]. Qed.

  (** The product of a concatenation is the product of the products. *)
  Lemma fold_mul_app : forall l1 l2 : list F,
    fold_right mul one (l1 ++ l2) = fold_right mul one l1 * fold_right mul one l2.
  Proof. induction l1 as [| a l1 ih]; intros l2; cbn [app fold_right]; [field | rewrite ih; field]. Qed.

  (** The polynomials [T_i] of the single value product argument: with
      [ã = d + X a] and [e = δ + X Δ] as polynomials in the challenge [X],
      [T_0 = d_0 + a_0 X] and [T_(i+1) = T_i · (d_(i+1) + a_(i+1) X) +
      X^i (δ_i + Δ_i X)]. The verification equations give [x^i b̃_i =
      T_i(x)] ([svpT_eval]). *)
  Fixpoint svpT (a d δ Δ : list F) (i : nat) : list F :=
    match i with
    | 0 => [nth 0 d zero; nth 0 a zero]
    | S i' => padd (pmulF (svpT a d δ Δ i') [nth (S i') d zero; nth (S i') a zero])
                (repeat zero i' ++ [nth i' δ zero; nth i' Δ zero])
    end.

  (** [T_i] has [i+2] coefficients, i.e. degree at most [i+1]. *)
  Lemma svpT_length : forall a d δ Δ i, length (svpT a d δ Δ i) = S (S i).
  Proof.
    intros a d δ Δ i; induction i as [| i ih]; [reflexivity |].
    cbn [svpT]; rewrite SigmaK.padd_length, (SigmaK.length_pmulF) by (discriminate || (rewrite <-length_zero_iff_nil, ih; lia)).
    rewrite ih, length_app, repeat_length; cbn [length]; lia.
  Qed.

  (** The leading coefficient of [T_i] (that of [X^(i+1)]) is [a_0 ⋯ a_i].
      *)
  Lemma svpT_lead : forall a d δ Δ i,
    nth (S i) (svpT a d δ Δ i) zero = fold_right mul one (map (fun k => nth k a zero) (seq 0 (S i))).
  Proof.
    intros a d δ Δ i; induction i as [| i ih]; [cbn; field |].
    cbn [svpT]; rewrite (SigmaK.nth_padd (Hf := Hf)), pmulF_lead by apply svpT_length.
    rewrite (nth_overflow (repeat zero i ++ _)) by (rewrite length_app, repeat_length; cbn; lia).
    rewrite ih, (seq_S (S i)), Nat.add_0_l, map_app, fold_mul_app; cbn [map fold_right]; field.
  Qed.

  (** If [ã_i = d_i + x a_i] for [i < n], [b̃_0 = ã_0] and [x b̃_(i+1) −
      b̃_i ã_(i+1) = δ_i + x Δ_i] for [i < n-1], then [x^i b̃_i = T_i(x)]
      for [i < n]. Induction on [i]. *)
  Lemma svpT_eval : forall (a d δ Δ ta tb : list F) (x : F) (n : nat),
    (forall i, (i < n)%nat -> nth i ta zero = nth i d zero + x * nth i a zero) ->
    nth 0 tb zero = nth 0 ta zero ->
    (forall i, (i < n - 1)%nat -> x * nth (S i) tb zero - nth i tb zero * nth (S i) ta zero = nth i δ zero + x * nth i Δ zero) ->
    forall i, (i < n)%nat -> fpow x i * nth i tb zero = eval (svpT a d δ Δ i) x.
  Proof.
    intros a d δ Δ ta tb x n hta hb0 he i; induction i as [| i ih]; intros hi.
    + cbn [fpow svpT eval]. rewrite hb0, hta by exact hi. field.
    + assert (hx : x * nth (S i) tb zero = nth i tb zero * nth (S i) ta zero + (nth i δ zero + x * nth i Δ zero))
        by (rewrite <-(he i ltac:(lia)); field).
      cbn [fpow svpT]. rewrite (eval_padd (Hf := Hf)), (eval_pmulF (Hf := Hf)), eval_shift, <-(ih ltac:(lia)); cbn [eval].
      transitivity (fpow x i * (x * nth (S i) tb zero)); [field |].
      rewrite hx, (hta (S i) ltac:(lia)). field.
  Qed.

  (** Special soundness of the single value product argument. Hypotheses:
      [length gs = n ≥ 2]; [xs] is a list of [n+1] distinct challenges; the
      first message [(cd, cδ, cΔ)] is fixed and all [n+1] transcripts are
      accepted. Conclusion: either binding breaks or [ca = com(a; ra)] with
      [length a = n] and [∏_i a_i = b].

      Proof idea: two challenges suffice to open [cd], [ca] and [cδ],
      [cΔ] ([geval_openings] on [[cd; ca]] and [[cδ; cΔ]]). By binding,
      [ã = d + x a] and [e = δ + x Δ] at every challenge, so by
      [svpT_eval] together with [b̃_(n-1) = x b] the polynomial identity [X^n b =
      T_(n-1)(X)] holds at the [n+1] challenges; both sides have degree at
      most [n], so the coefficients of [X^n] agree, giving [b = a_0 ⋯
      a_(n-1)] by [svpT_lead]. *)
  Theorem svp_soundness : forall (h : G) (gs : list G) (ca : G) (b : F) (cd cδ cΔ : G) (xs : list F)
    (ta tb : nat -> list F) (rt st : nat -> F),
    (2 <= length gs)%nat -> NoDup xs -> length xs = S (length gs) ->
    (forall j, (j < length xs)%nat ->
      svp_verify h gs ca b (nth j xs zero) (mk_svp cd cδ cΔ (ta j) (tb j) (rt j) (st j)) = true) ->
    (exists (a : list F) (ra : F), ca = com h gs a ra /\ length a = length gs /\ fold_right mul one a = b)
    \/ binding_break h gs.
  Proof.
    intros h gs ca b cd cδ cΔ xs ta tb rt st hn hnd hk htr0.
    assert (htr : forall j, (j < length xs)%nat -> length (ta j) = length gs /\
      svp_verify h gs ca b (nth j xs zero) (mk_svp cd cδ cΔ (ta j) (tb j) (rt j) (st j)) = true)
      by (intros j hj; split; [exact (svp_verify_length (htr0 j hj)) | exact (htr0 j hj)]).
    set (n := length gs) in *. assert (hn_eq : length gs = n) by reflexivity.
    assert (hlta : forall j, (j < S n)%nat -> length (ta j) = n) by (intros j hj; destruct (htr j ltac:(lia)); assumption).
    assert (hV : forall j, (j < S n)%nat ->
      gop (ca ^ (nth j xs zero)) cd = com h gs (ta j) (rt j) /\
      gop (cΔ ^ (nth j xs zero)) cδ = com h gs (map (fun i => nth j xs zero * nth (S i) (tb j) zero - nth i (tb j) zero * nth (S i) (ta j) zero) (seq 0 (n - 1))) (st j) /\
      nth 0 (tb j) zero = nth 0 (ta j) zero /\ nth (n - 1) (tb j) zero = nth j xs zero * b).
    { intros j hj; destruct (htr j ltac:(lia)) as (hl & hv); apply svp_verify_true in hv.
      rewrite hl in hv; tauto. }
    (* Open cd, ca and cδ, cΔ from the first two challenges. *)
    set (X2 := firstn 2 xs).
    assert (hX2nd : NoDup X2) by (apply NoDup_firstn; exact hnd).
    assert (hX2l : length X2 = 2) by (unfold X2; rewrite length_firstn; lia).
    assert (hX2n : forall j, (j < 2)%nat -> nth j X2 zero = nth j xs zero) by (intros j hj; unfold X2; apply nth_firstn_lt; exact hj).
    set (e := fun j => map (fun i => nth j xs zero * nth (S i) (tb j) zero - nth i (tb j) zero * nth (S i) (ta j) zero) (seq 0 (n - 1))).
    assert (hle : forall j, length (e j) = (n - 1)%nat) by (intros j; unfold e; rewrite length_map, length_seq; reflexivity).
    set (d := lcomb (lam X2 0) ta 2). set (a := lcomb (lam X2 1) ta 2).
    set (rd := fsum (fun j => lam X2 0 j * rt j) 2). set (ra := fsum (fun j => lam X2 1 j * rt j) 2).
    set (δ := lcomb (lam X2 0) e 2). set (Δ := lcomb (lam X2 1) e 2).
    set (sδ := fsum (fun j => lam X2 0 j * st j) 2). set (sΔ := fsum (fun j => lam X2 1 j * st j) 2).
    assert (hopen1 : forall i, (i < 2)%nat -> nth i [cd; ca] gid = com h gs (lcomb (lam X2 i) ta 2) (fsum (fun j => lam X2 i j * rt j) 2)).
    { intros i hi. rewrite <-hX2l.
      apply (geval_openings h gs X2 [cd; ca] ta rt hX2nd); [rewrite hX2l; reflexivity | | rewrite hX2l; lia].
      intros j hj; rewrite hX2l in hj; rewrite hX2n by lia; rewrite geval_pair, gcomm.
      destruct (hV j ltac:(lia)) as (h1 & _); exact h1. }
    assert (hopen2 : forall i, (i < 2)%nat -> nth i [cδ; cΔ] gid = com h gs (lcomb (lam X2 i) e 2) (fsum (fun j => lam X2 i j * st j) 2)).
    { intros i hi. rewrite <-hX2l.
      apply (geval_openings h gs X2 [cδ; cΔ] e st hX2nd); [rewrite hX2l; reflexivity | | rewrite hX2l; lia].
      intros j hj; rewrite hX2l in hj; rewrite hX2n by lia; rewrite geval_pair, gcomm.
      destruct (hV j ltac:(lia)) as (_ & h2 & _); exact h2. }
    pose proof (hopen1 0%nat ltac:(lia)) as hcd; pose proof (hopen1 1%nat ltac:(lia)) as hca; cbn [nth] in hcd, hca.
    pose proof (hopen2 0%nat ltac:(lia)) as hcδ; pose proof (hopen2 1%nat ltac:(lia)) as hcΔ; cbn [nth] in hcδ, hcΔ.
    fold d rd in hcd. fold a ra in hca. fold δ sδ in hcδ. fold Δ sΔ in hcΔ.
    assert (hla : length a = n) by (unfold a; apply lcomb_length; [lia | intros j hj; apply hlta; lia]).
    assert (hld : length d = n) by (unfold d; apply lcomb_length; [lia | intros j hj; apply hlta; lia]).
    assert (hlδ : length δ = (n - 1)%nat) by (unfold δ; apply lcomb_length; [lia | intros j hj; apply hle]).
    assert (hlΔ : length Δ = (n - 1)%nat) by (unfold Δ; apply lcomb_length; [lia | intros j hj; apply hle]).
    (* By binding, the responses are the evaluations of the extracted
       openings at every challenge. *)
    assert (hresp : (forall j, (j < S n)%nat ->
        (forall i, (i < n)%nat -> nth i (ta j) zero = nth i d zero + nth j xs zero * nth i a zero) /\
        (forall i, (i < n - 1)%nat -> nth i (e j) zero = nth i δ zero + nth j xs zero * nth i Δ zero)) \/ binding_break h gs).
    { apply forall_or. intros j hj. destruct (hV j hj) as (h1 & h2 & _).
      rewrite hca, hcd, <-(com_scale (Hvec := Hvec)), <-(com_padd (Hvec := Hvec)) in h1.
      rewrite hcΔ, hcδ, <-(com_scale (Hvec := Hvec)), <-(com_padd (Hvec := Hvec)) in h2.
      fold (e j) in h2.
      destruct (open_eq_or_break h gs _ _ _ _ h1) as [[_ e1] | hbb]; [| right; exact hbb].
      destruct (open_eq_or_break h gs _ _ _ _ h2) as [[_ e2] | hbb]; [| right; exact hbb].
      left; split.
      + intros i hi. rewrite <-(e1 i ltac:(lia)), (SigmaK.nth_padd (Hf := Hf)), (SigmaK.nth_lscale (Hf := Hf)); field.
      + intros i hi. rewrite <-(e2 i ltac:(lia)), (SigmaK.nth_padd (Hf := Hf)), (SigmaK.nth_lscale (Hf := Hf)); field. }
    destruct hresp as [hresp | hbb]; [| right; exact hbb].
    (* The polynomial identity X^n b = T_(n-1)(X) at all n + 1 challenges,
       hence agreement of the coefficient of X^n. *)
    assert (hid : forall j, (j < S n)%nat ->
      eval (repeat zero n ++ [b]) (nth j xs zero) = eval (svpT a d δ Δ (n - 1)) (nth j xs zero)).
    { intros j hj. destruct (hV j hj) as (_ & _ & hb0 & hbn). destruct (hresp j hj) as (hta' & he').
      assert (he'' : forall i, (i < n - 1)%nat ->
        nth j xs zero * nth (S i) (tb j) zero - nth i (tb j) zero * nth (S i) (ta j) zero = nth i δ zero + nth j xs zero * nth i Δ zero).
      { intros i hi. rewrite <-(he' i hi). unfold e. rewrite (PolyPerm.nth_map_seq _ _ _ zero hi). reflexivity. }
      rewrite eval_shift; cbn [eval].
      rewrite <-(svpT_eval a d δ Δ (ta j) (tb j) (nth j xs zero) n hta' hb0 he'' (n - 1) ltac:(lia)).
      rewrite hbn, fpow_pred by lia. field. }
    assert (hcoef : nth n (repeat zero n ++ [b]) zero = nth n (svpT a d δ Δ (n - 1)) zero).
    { apply (agree_nth (Fdec := Fdec) (Hf := Hf) xs).
      + exact hnd.
      + rewrite length_app, repeat_length; cbn [length]; lia.
      + rewrite svpT_length; lia.
      + intros x hx. destruct (In_nth xs x zero hx) as (j & hj & <-). apply hid; lia. }
    rewrite app_nth2, repeat_length, Nat.sub_diag in hcoef by (rewrite repeat_length; lia); cbn [nth] in hcoef.
    assert (hlead : nth n (svpT a d δ Δ (n - 1)) zero = fold_right mul one (map (fun k => nth k a zero) (seq 0 n))).
    { pose proof (svpT_lead a d δ Δ (n - 1)) as h0; replace (S (n - 1)) with n in h0 by lia; exact h0. }
    rewrite hlead in hcoef.
    left. exists a, ra. split; [exact hca | split; [exact hla |]].
    rewrite hcoef, <-hla.
    transitivity (fold_right mul one (map id a)); [rewrite map_id; reflexivity |].
    f_equal. rewrite <-(map_nth_seq id zero a). apply map_ext; intro k; reflexivity.
  Qed.

  (** ** Product argument: composition

      Statement: [cA] (with [m ≥ 1] commitments) and a scalar [b]. Claim:
      [∏_j (A_0 ∘ … ∘ A_(m-1))_j = b]. For [m > 1] the prover sends a
      commitment [cb] to [A_0 ∘ … ∘ A_(m-1)], a Hadamard argument for
      [(cA, cb)] and a single value product argument for [(cb, b)]; for
      [m = 1] only a single value product argument for [(c_(A_0), b)]. *)
  Local Notation product_verify := (product_verify (zero := zero) (one := one) (add := add) (mul := mul)
    (sub := sub) (opp := opp) (Fdec := Fdec) (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation mk_prod := (@mk_prod F G).

  (** Unpacking of an accepting product transcript whose Hadamard part is
      present: either [m > 1] and both the Hadamard and the single value
      product verifiers accept, or [m = 1] and the single value product
      verifier accepts on [c_(A_0)]. *)
  Lemma product_verify_true : forall h gs n cA b xh yh xz xs cb had svp,
    (1 <= length cA)%nat ->
    product_verify h gs n cA b xh yh xz xs (mk_prod cb (Some had) svp) = true ->
    ((1 < length cA)%nat /\ hadamard_verify h gs n cA cb xh yh xz had = true /\ svp_verify h gs cb b xs svp = true) \/
    (length cA = 1%nat /\ svp_verify h gs (nth 0 cA gid) b xs svp = true).
  Proof.
    intros * hm hv; unfold BayerGroth.product_verify in hv; cbv zeta in hv; cbn [pa_cb pa_had pa_svp] in hv.
    destruct (1 <? length cA)%nat eqn:e.
    + apply Nat.ltb_lt in e. apply andb_prop in hv. left; split; [exact e | exact hv].
    + apply Nat.ltb_ge in e. right; split; [lia | exact hv].
  Qed.

  (** Special soundness of the product argument. Hypotheses: [length gs =
      n ≥ 2], [length cA = m ≥ 1]; [X] ([m] distinct), [Y] ([n] distinct)
      and the zero-argument challenge lists [zs p q] ([2m+1] distinct each)
      as in [hadamard_soundness]; [XS] a list of [n+1] distinct challenges
      for the single value product argument; [cb], [cB] and the single
      value product first message are fixed; and every combination of a
      Hadamard leaf [(p, q, j)] with a single value product challenge [j']
      is accepted. Conclusion: either binding breaks or [cA = com_list A r]
      with vectors of length [n] and [∏ (hprefix A (m-1)) = b].

      Proof: for [m > 1], [hadamard_soundness] gives [cb = com(A_0 ∘ … ∘
      A_(m-1))] and [svp_soundness] gives [cb = com(a)] with [∏ a = b];
      binding identifies the two openings. For [m = 1],
      [svp_soundness] directly. *)
  Theorem product_soundness : forall (h : G) (gs : list G) (cA : list G) (b : F) (cb : G) (cB : list G) (X Y : list F)
    (cA0 cBm : nat -> nat -> G) (cd : nat -> nat -> list G) (zs : nat -> nat -> list F)
    (za zb : nat -> nat -> nat -> list F) (zr zt zu : nat -> nat -> nat -> F)
    (scd scδ scΔ : G) (XS : list F) (ta tb : nat -> list F) (rt st : nat -> F),
    (2 <= length gs)%nat -> (1 <= length cA)%nat ->
    NoDup X -> length X = length cA -> NoDup Y -> length Y = length gs ->
    NoDup XS -> length XS = S (length gs) ->
    (forall p q, (p < length cA)%nat -> (q < length gs)%nat ->
      NoDup (zs p q) /\ length (zs p q) = (2 * length cA + 1)%nat /\
      forall j, (j < 2 * length cA + 1)%nat ->
        forall j', (j' < S (length gs))%nat ->
          product_verify h gs (length gs) cA b (nth p X zero) (nth q Y zero) (nth j (zs p q) zero) (nth j' XS zero)
            (mk_prod cb (Some (mk_had cB (mk_zero (cA0 p q) (cBm p q) (cd p q) (za p q j) (zb p q j) (zr p q j) (zt p q j) (zu p q j))))
              (mk_svp scd scδ scΔ (ta j') (tb j') (rt j') (st j'))) = true) ->
    (exists (A : list (list F)) (r : list F),
      cA = com_list h gs A r /\ length A = length cA /\ length r = length cA /\
      (forall v, In v A -> length v = length gs) /\
      fold_right mul one (hprefix A (length cA - 1)) = b)
    \/ binding_break h gs.
  Proof.
    intros h gs cA b cb cB X Y cA0 cBm cd zs za zb zr zt zu scd scδ scΔ XS ta tb rt st hn hm hXnd hXl hYnd hYl hSnd hSl htr.
    set (m := length cA) in *. set (n := length gs) in *.
    assert (hm_eq : length cA = m) by reflexivity. assert (hn_eq : length gs = n) by reflexivity.
    destruct (htr 0%nat 0%nat ltac:(lia) ltac:(lia)) as (_ & _ & hj0).
    pose proof (hj0 0%nat ltac:(lia)) as hj'0.
    pose proof (hj'0 0%nat ltac:(lia)) as hv0.
    destruct (product_verify_true _ _ _ _ _ _ _ _ _ _ _ _ hm hv0) as [(hm1 & _ & _) | (hm1 & _)].
    +
      assert (hhad : (exists (A : list (list F)) (r : list F) (b' : list F) (sb : F),
          cA = com_list h gs A r /\ cb = com h gs b' sb /\ length A = m /\ length r = m /\
          (forall v, In v A -> length v = n) /\ length b' = n /\ b' = hprefix A (m - 1)) \/ binding_break h gs).
      { apply (hadamard_soundness h gs cA cb cB X Y cA0 cBm cd zs za zb zr zt zu);
          [lia | lia | exact hXnd | exact hXl | exact hYnd | exact hYl |].
        intros p q hp hq. destruct (htr p q hp hq) as (h1 & h2 & h3). split; [exact h1 | split; [exact h2 |]].
        intros j hj. pose proof (h3 j hj 0%nat ltac:(lia)) as hv.
        destruct (product_verify_true _ _ _ _ _ _ _ _ _ _ _ _ hm hv) as [(_ & hh & _) | (e & _)]; [exact hh | lia]. }
      destruct hhad as [(A & r & b' & sb & hcA & hcb & hA & hr & hAn & hb'n & hpref) | hbb]; [| right; exact hbb].
      assert (hsvp : (exists (a : list F) (ra : F), cb = com h gs a ra /\ length a = n /\ fold_right mul one a = b) \/ binding_break h gs).
      { apply (svp_soundness h gs cb b scd scδ scΔ XS ta tb rt st hn hSnd hSl).
        intros j' hj'. rewrite hSl in hj'. pose proof (hj'0 j' hj') as hv.
        destruct (product_verify_true _ _ _ _ _ _ _ _ _ _ _ _ hm hv) as [(_ & _ & hs) | (e & _)]; [exact hs | lia]. }
      destruct hsvp as [(a & ra & hcb' & han & hprod) | hbb]; [| right; exact hbb].
      rewrite hcb in hcb'.
      destruct (open_eq_or_break_len h gs _ _ _ _ hb'n han hcb') as [[e _] | hbb]; [| right; exact hbb].
      left. exists A, r. repeat split; try assumption. rewrite <-hpref, e; exact hprod.
    +
      assert (hsvp : (exists (a : list F) (ra : F), nth 0 cA gid = com h gs a ra /\ length a = n /\ fold_right mul one a = b) \/ binding_break h gs).
      { apply (svp_soundness h gs (nth 0 cA gid) b scd scδ scΔ XS ta tb rt st hn hSnd hSl).
        intros j' hj'. rewrite hSl in hj'. pose proof (hj'0 j' hj') as hv.
        destruct (product_verify_true _ _ _ _ _ _ _ _ _ _ _ _ hm hv) as [(e & _) | (_ & hs)]; [lia | exact hs]. }
      destruct hsvp as [(a & ra & hca & han & hprod) | hbb]; [| right; exact hbb].
      left. exists [a], [ra].
      assert (hcA1 : cA = [nth 0 cA gid]) by (destruct cA as [| c0 [| c1 cA']]; [discriminate | reflexivity | discriminate]).
      split; [rewrite hcA1, com_list_cons, hca; reflexivity |].
      split; [cbn; lia | split; [cbn; lia |]].
      split; [intros v [<- | []]; exact han |].
      replace (m - 1)%nat with 0%nat by lia. rewrite hprefix_0 by discriminate. exact hprod.
  Qed.

  (** ** Multi-exponentiation argument: 2m-special soundness

      Ciphertexts are vectors [CT] of [l+1] group elements, the ElGamal-style
      encryptions [enc g pk M τ = (g^τ, pk_1^τ M_1, …, pk_l^τ M_l)] of
      [BayerGroth.v], with componentwise group law [cmul] and power
      [cpow]; [encg g pk β τ] encrypts [g^β] in every slot.

      Statement: rows of ciphertexts [Cs = (C_0, …, C_(m-1))] (each a list
      of [n] ciphertexts), a target ciphertext [C], and commitments [cA] to
      exponent vectors [A_0 … A_(m-1)]. Claim: [C = Enc(1; ρ) · ∏_i
      C_i^(A_i)] for some [ρ], where [C_i^(A_i) = ∏_j C_(i,j)^(A_(i,j))]
      ([cmexp]). The prover commits to a blinder [A_(-1)] ([cA0]), to the
      [2m] diagonal products [E_k] together with commitments [cB] to scalars
      [β_k] (with [β_m = 0] enforced by [c_(B_m) = 1]), and [E_m = C]. *)
  Section MultiExpSound.

    Context {l : nat}.
    Local Notation CT := (Vector.t G (S l)).
    Local Notation cone := (vec_id (V := G) (vid := gid) (S l)).
    Local Notation cmul := (vec_add (vadd := gop) (n := S l)).
    Local Notation cpow := (vec_smul (smul := gpow) (n := S l)).
    Local Notation CTvs := (vec_vspace (HV := Hvec) (S l)).
    Local Notation cmexp := (lmexp (vid := cone) (vadd := cmul) (smul := cpow)).
    Local Notation ceval := (veval (one := one) (mul := mul) (vid := cone) (vadd := cmul) (smul := cpow)).
    Local Notation cpadd := (vpadd (vadd := cmul)).
    Local Notation cprod := (fold_right cmul cone).
    Local Notation csum := (vsum (vid := cone) (vadd := cmul)).
    Local Notation encg := (encg (gop := gop) (gpow := gpow) (l := l)).
    Local Notation diagonals := (diagonals (gid := gid) (gop := gop) (gpow := gpow) (l := l)).
    Local Notation diag_row := (diag_row (gid := gid) (gop := gop) (gpow := gpow) (l := l)).
    Local Notation multiexp_verify := (multiexp_verify (one := one) (mul := mul) (gid := gid) (gop := gop)
      (gpow := gpow) (Gdec := Gdec) (l := l)).
    Local Notation mk_mexp := (@mk_mexp F G l).

    (** Equality test on ciphertexts. *)
    Lemma vdec_true : forall u v : CT, (if vec_dec Gdec u v then true else false) = true -> u = v.
    Proof. intros u v h; destruct (vec_dec Gdec u v); [assumption | discriminate]. Qed.

    (** Group identities in the ciphertext space: [cmul_cancel] is [(X ·
        Y) · Y⁻¹ = X]; [cmul_inv_l] is [Y⁻¹ · Y = 1]; [cancel_inv2] solves
        [X · Y⁻¹ · Z⁻¹ = W] for [X = W · Z · Y]. *)
    Lemma cmul_cancel : forall X Y : CT, cmul (cmul X Y) (cpow Y (opp one)) = X.
    Proof.
      intros X Y. rewrite <-(vadd_assoc (HV := CTvs)).
      transitivity (cmul X (cmul (cpow Y one) (cpow Y (opp one)))).
      { rewrite (vsmul_one (HV := CTvs)); reflexivity. }
      rewrite <-(vsmul_add (HV := CTvs)).
      replace (one + opp one) with zero by field.
      rewrite (vsmul_zero (HV := CTvs)), (vadd_vid_r (HV := CTvs)); reflexivity.
    Qed.

    Lemma cmul_inv_l : forall Y : CT, cmul (cpow Y (opp one)) Y = cone.
    Proof.
      intros Y. rewrite (vadd_comm (HV := CTvs)). pose proof (cmul_cancel cone Y) as h.
      rewrite (vadd_vid_l (HV := CTvs)) in h. exact h.
    Qed.

    Lemma cancel_inv2 : forall X Y Z W : CT,
      cmul X (cmul (cpow Y (opp one)) (cpow Z (opp one))) = W -> X = cmul W (cmul Z Y).
    Proof.
      intros X Y Z W h. rewrite <-h.
      rewrite <-(vadd_assoc (HV := CTvs) X), <-(vadd_assoc (HV := CTvs) (cpow Y (opp one))),
        (vadd_assoc (HV := CTvs) (cpow Z (opp one)) Z Y), cmul_inv_l, (vadd_vid_l (HV := CTvs) Y), cmul_inv_l,
        (vadd_vid_r (HV := CTvs)); reflexivity.
    Qed.

    (** Indexing commutes with raising every element of a list to [c]
        (out-of-range indices give [1]). *)
    Lemma nth_map_cpow : forall (D : list CT) (c : F) k, nth k (map (fun d => cpow d c) D) cone = cpow (nth k D cone) c.
    Proof.
      induction D as [| d D ih]; intros c k.
      + destruct k; cbn [map nth]; rewrite (vsmul_vid (HV := CTvs)); reflexivity.
      + destruct k; cbn [map nth]; [reflexivity | apply ih].
    Qed.

    (** Evaluating the polynomial with coefficients [encg β_k 0] gives
        [encg (Σ β_k x^k) 0]. *)
    Lemma ceval_encg_zero : forall g pk (bs : list F) x,
      ceval (map (fun β => encg g pk β zero) bs) x = encg g pk (feval bs x) zero.
    Proof.
      intros g pk bs x; induction bs as [| β bs ih].
      + cbn [map]; rewrite veval_nil, veval_nil; symmetry; apply (encg_zero_zero (Hvec := Hvec)).
      + cbn [map]; rewrite (veval_cons (HV := CTvs)), (veval_cons (HV := F_vspace (Hvec := Hvec))), ih.
        rewrite (encg_pow (Hvec := Hvec)), (encg_mul (Hvec := Hvec)). f_equal; field.
    Qed.

    (** [∏_j Enc(1; t_j)^(c_j) = Enc(1; Σ_j c_j t_j)]. *)
    Lemma csum_encg : forall g pk (t c : nat -> F) k,
      csum (fun j => cpow (encg g pk zero (t j)) (c j)) k = encg g pk zero (fsum (fun j => c j * t j) k).
    Proof.
      intros g pk t c k; induction k as [| k ih]; cbn [vsum fsum].
      + symmetry; apply (encg_zero_zero (Hvec := Hvec)).
      + rewrite ih, (encg_pow (Hvec := Hvec)), (encg_mul (Hvec := Hvec)). f_equal; field.
    Qed.

    (** The multi-exponentiation verifier checks [length a = length gs]. *)
    Lemma multiexp_verify_length {h gs g pk} {Cs : list (list CT)} {C : CT} {cA x cA0 cB E a r b s τ} :
      multiexp_verify h gs g pk Cs C cA x (mk_mexp cA0 cB E a r b s τ) = true -> length a = length gs.
    Proof.
      intros hv; unfold BayerGroth.multiexp_verify in hv; cbv zeta in hv; cbn [me_a] in hv.
      repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
      match goal with h : (length a =? length gs)%nat = true |- _ => apply Nat.eqb_eq in h; exact h end.
    Qed.

    (** Unpacking of an accepting multi-exponentiation transcript: [m ≥ 1],
        [length Cs = m], [length cB = length E = 2m], [c_(B_m) = 1], [E_m =
        C], [geval (cA0 :: cA) x = com(a; r)], [geval cB x = com([b]; s)],
        and [∏_k E_k^(x^k) = encg b τ · ∏_i C_i^(x^(m-i-1) a)]. *)
    Lemma multiexp_verify_true : forall h gs g pk (Cs : list (list CT)) (C : CT) cA x cA0 cB E a r b s τ,
      multiexp_verify h gs g pk Cs C cA x (mk_mexp cA0 cB E a r b s τ) = true ->
      (1 <= length cA)%nat /\ length Cs = length cA /\ length cB = (2 * length cA)%nat /\ length E = (2 * length cA)%nat /\
      nth (length cA) cB gid = gid /\ nth (length cA) E cone = C /\
      geval (cA0 :: cA) x = com h gs a r /\ geval cB x = com h gs [b] s /\
      ceval E x = cmul (encg g pk b τ)
        (cprod (map (fun p => cmexp (snd p) (lscale (fpow x (length cA - fst p - 1)) a)) (combine (seq 0 (length cA)) Cs))).
    Proof.
      intros * hv; unfold BayerGroth.multiexp_verify in hv; cbv zeta in hv;
        cbn [me_cA0 me_cB me_E me_a me_r me_b me_s me_tau] in hv.
      repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
      repeat match goal with
        | h : (if Gdec ?u ?v then true else false) = true |- _ => apply gdec_true in h
        | h : (if vec_dec Gdec ?u ?v then true else false) = true |- _ => apply vdec_true in h
        | h : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in h
        | h : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in h
        end.
      repeat split; assumption.
    Qed.

    (** Special soundness of the multi-exponentiation argument. Hypotheses:
        [length gs ≥ 1], [length cA = m ≥ 1]; [xs] is a list of [2m]
        distinct challenges; the first message [(cA0, cB, E)] is fixed and
        all [2m] transcripts are accepted. Conclusion: either binding breaks
        or [cA = com_list A ra] with vectors of length [length gs] and [C =
        Enc(1; ρ) · ∏_i C_i^(A_i)] for some [ρ].

        Proof idea: the first [m+1] challenges open [cA0 :: cA] to [A'_0 …
        A'_m]; all [2m] challenges open [cB] to scalars [β_k]. By binding the
        responses are [a = Σ x^i A'_i] and [b = Σ x^k β_k]. The ciphertext
        polynomial [Q = E · D⁻¹ · Enc(g^β; 0)⁻¹], where [D] is the
        polynomial of diagonal products ([diagonals]), evaluates to an
        encryption of 1 at each of the [2m] challenges; [coeff_from_evals]
        in the ciphertext vector space shows each coefficient is an
        encryption of 1 as well. Its coefficient [m] gives [C = E_m =
        Enc(1; ρ_m) · D_m · Enc(g^(β_m); 0)], with [β_m = 0] from [c_(B_m) =
        1] by binding and [D_m = ∏_i C_i^(A'_(i+1))]. *)
    Theorem multiexp_soundness : forall (h g : G) (gs : list G) (pk : Vector.t G l) (Cs : list (list CT)) (C : CT)
      (cA : list G) (cA0 : G) (cB : list G) (E : list CT) (xs : list F) (a : nat -> list F) (r b s τ : nat -> F),
      (1 <= length gs)%nat -> (1 <= length cA)%nat -> NoDup xs -> length xs = (2 * length cA)%nat ->
      (forall j, (j < length xs)%nat ->
        multiexp_verify h gs g pk Cs C cA (nth j xs zero) (mk_mexp cA0 cB E (a j) (r j) (b j) (s j) (τ j)) = true) ->
      (exists (A : list (list F)) (ra : list F) (ρ : F),
        cA = com_list h gs A ra /\ length A = length cA /\ length ra = length cA /\
        (forall v, In v A -> length v = length gs) /\
        C = cmul (encg g pk zero ρ) (cprod (map (fun p => cmexp (snd p) (nth (fst p) A [])) (combine (seq 0 (length cA)) Cs))))
      \/ binding_break h gs.
    Proof.
      intros h g gs pk Cs C cA cA0 cB E xs a r b s τ hn hm hnd hk htr0.
      assert (htr : forall j, (j < length xs)%nat -> length (a j) = length gs /\
        multiexp_verify h gs g pk Cs C cA (nth j xs zero) (mk_mexp cA0 cB E (a j) (r j) (b j) (s j) (τ j)) = true)
        by (intros j hj; split; [exact (multiexp_verify_length (htr0 j hj)) | exact (htr0 j hj)]).
      set (m := length cA) in *. set (n := length gs) in *. set (k := (2 * m)%nat) in *.
      assert (hm_eq : length cA = m) by reflexivity. assert (hn_eq : length gs = n) by reflexivity.
      assert (hk_eq : (2 * m)%nat = k) by reflexivity.
      assert (hCs : length Cs = m) by (destruct (htr 0%nat ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hcB : length cB = k) by (destruct (htr 0%nat ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hE : length E = k) by (destruct (htr 0%nat ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hcBm : nth m cB gid = gid) by (destruct (htr 0%nat ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hEm : nth m E cone = C) by (destruct (htr 0%nat ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hevA : forall j, (j < k)%nat -> geval (cA0 :: cA) (nth j xs zero) = com h gs (a j) (r j))
        by (intros j hj; destruct (htr j ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hevB : forall j, (j < k)%nat -> geval cB (nth j xs zero) = com h gs [b j] (s j))
        by (intros j hj; destruct (htr j ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hevE : forall j, (j < k)%nat -> ceval E (nth j xs zero) = cmul (encg g pk (b j) (τ j))
        (cprod (map (fun p => cmexp (snd p) (lscale (fpow (nth j xs zero) (m - fst p - 1)) (a j))) (combine (seq 0 m) Cs))))
        by (intros j hj; destruct (htr j ltac:(lia)) as (_ & hv); apply multiexp_verify_true in hv; tauto).
      assert (hla : forall j, (j < k)%nat -> length (a j) = n) by (intros j hj; destruct (htr j ltac:(lia)); tauto).
      (* The first m + 1 challenges open cA0 :: cA; all 2m challenges open
         the scalar commitments cB. *)
      set (X1 := firstn (S m) xs).
      assert (hX1nd : NoDup X1) by (apply NoDup_firstn; exact hnd).
      assert (hX1l : length X1 = S m) by (unfold X1; rewrite length_firstn; lia).
      assert (hX1n : forall j, (j < S m)%nat -> nth j X1 zero = nth j xs zero) by (intros j hj; unfold X1; apply nth_firstn_lt; exact hj).
      set (A' := fun i => lcomb (lam X1 i) a (S m)).
      set (r' := fun i => fsum (fun j => lam X1 i j * r j) (S m)).
      assert (hopenA : forall i, (i < S m)%nat -> nth i (cA0 :: cA) gid = com h gs (A' i) (r' i)).
      { intros i hi. unfold A', r'. rewrite <-hX1l.
        apply (geval_openings h gs X1 (cA0 :: cA) a r hX1nd);
          [rewrite hX1l; cbn [length]; lia | | rewrite hX1l; lia].
        intros j hj; rewrite hX1l in hj; rewrite hX1n by lia; apply hevA; lia. }
      set (β := fun i => fsum (fun j => lam xs i j * b j) k).
      set (s' := fun i => fsum (fun j => lam xs i j * s j) k).
      assert (hopenB : forall i, (i < k)%nat -> nth i cB gid = com h gs [β i] (s' i)).
      { intros i hi. unfold β, s'. rewrite <-lcomb_singletons by lia. rewrite <-hk.
        apply (geval_openings h gs xs cB (fun j => [b j]) s hnd); [rewrite hk; lia | | rewrite hk; lia].
        intros j hj; rewrite hk in hj; apply hevB; lia. }
      set (A'' := map A' (seq 0 (S m))). set (r'' := map r' (seq 0 (S m))).
      set (βl := map β (seq 0 k)). set (s'' := map s' (seq 0 k)).
      assert (hcAl : cA0 :: cA = com_list h gs A'' r'') by (apply com_list_of_openings; [reflexivity | exact hopenA]).
      assert (hcBl : cB = com_list h gs (map (fun bk => [bk]) βl) s'').
      { unfold βl; rewrite map_map. apply com_list_of_openings; [exact hcB | exact hopenB]. }
      assert (hA'len : forall i, (i < S m)%nat -> length (A' i) = n) by (intros i hi; unfold A'; apply lcomb_length; [lia | intros j hj; apply hla; lia]).
      assert (hA''len : forall v, In v A'' -> length v = n).
      { intros v hv; unfold A'' in hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hA'len; lia. }
      assert (hA''ne : A'' <> []) by (unfold A''; cbn [seq map]; discriminate).
      assert (hA''l : length A'' = S m) by (unfold A''; rewrite length_map, length_seq; reflexivity).
      assert (hlenAr : length A'' = length r'') by (unfold A'', r''; rewrite !length_map; reflexivity).
      assert (hlenβ : length βl = k) by (unfold βl; rewrite length_map, length_seq; reflexivity).
      assert (hlenβs : length (map (fun bk => [bk]) βl) = length s'') by (unfold s''; rewrite !length_map, length_seq; exact hlenβ).
      (* By binding, the responses are evaluations of the extracted
         openings. *)
      assert (hresp : (forall j, (j < k)%nat -> a j = lveval A'' (nth j xs zero) /\ b j = feval βl (nth j xs zero)) \/ binding_break h gs).
      { apply forall_or. intros j hj.
        pose proof (hevA j hj) as ha; rewrite hcAl, (geval_com_list (Hvec := Hvec)) in ha by exact hlenAr.
        pose proof (hevB j hj) as hb; rewrite hcBl, (geval_com_list (Hvec := Hvec)) in hb by exact hlenβs.
        rewrite (lveval_singletons (Hvec := Hvec)) in hb by (unfold βl; destruct k; [lia | cbn [seq map]; discriminate]).
        destruct (open_eq_or_break_len h gs _ _ _ _ (lveval_length A'' _ n hA''ne hA''len) (hla j hj) ha) as [[ea _] | hbb];
          [| right; exact hbb].
        destruct (open_eq_or_break h gs _ _ _ _ hb) as [[_ eb] | hbb]; [| right; exact hbb].
        left; split; [symmetry; exact ea |].
        specialize (eb 0%nat ltac:(lia)); cbn [nth] in eb; symmetry; exact eb. }
      destruct hresp as [hresp | hbb]; [| right; exact hbb].
      (* The diagonal polynomial D and Q = E · D⁻¹ · Enc(g^β; 0)⁻¹, an
         encryption of 1 at every challenge. *)
      set (D := diagonals m Cs A'').
      assert (hlenD : (length D <= k)%nat).
      { unfold D, BayerGroth.diagonals; apply fold_cpadd_length_le.
        rewrite Forall_forall; intros row hrow; apply in_map_iff in hrow; destruct hrow as ((i & Ci) & <- & hp).
        apply in_combine_l in hp; apply in_seq in hp.
        unfold BayerGroth.diag_row; cbn [fst snd]; rewrite length_app, repeat_length, length_map, hA''l; lia. }
      assert (hDev : forall j, (j < k)%nat -> ceval D (nth j xs zero) =
        cprod (map (fun p => cmexp (snd p) (lscale (fpow (nth j xs zero) (m - fst p - 1)) (a j))) (combine (seq 0 m) Cs))).
      { intros j hj. unfold D, BayerGroth.diagonals; rewrite (ceval_fold_cpadd (Hvec := Hvec)), map_map.
        f_equal; apply map_ext_in; intros (i & Ci) hp; rewrite (ceval_diag_row (Hvec := Hvec)); cbn [fst snd].
        destruct (hresp j hj) as (ea & _); rewrite <-ea; reflexivity. }
      set (Bp := map (fun β0 => encg g pk β0 zero) βl).
      set (Q := cpadd E (cpadd (map (fun d => cpow d (opp one)) D) (map (fun d => cpow d (opp one)) Bp))).
      assert (hQlen : length Q = k).
      { unfold Q, Bp; rewrite !(vpadd_length (vadd := cmul)), !length_map, hE, hlenβ; lia. }
      assert (hQev : forall j, (j < k)%nat -> ceval Q (nth j xs zero) = encg g pk zero (τ j)).
      { intros j hj. unfold Q; rewrite !(veval_vpadd (HV := CTvs)), !(veval_scale_coeffs (HV := CTvs)).
        unfold Bp; rewrite ceval_encg_zero, hevE by exact hj. rewrite <-hDev by exact hj.
        destruct (hresp j hj) as (_ & eb); rewrite eb.
        rewrite (vadd_assoc (HV := CTvs)), cmul_cancel, (encg_pow (Hvec := Hvec)), (encg_mul (Hvec := Hvec)).
        f_equal; field. }
      (* The inverse Vandermonde matrix in the ciphertext space: every
         coefficient of Q is an encryption of 1; take coefficient m. *)
      set (ρ := fun i => fsum (fun j => lam xs i j * τ j) k).
      assert (hQi : forall i, (i < k)%nat -> nth i Q cone = encg g pk zero (ρ i)).
      { intros i hi. unfold ρ. rewrite <-hk.
        rewrite (coeff_from_evals (Fdec := Fdec) (Hf := Hf) (HV := CTvs) (fun cs x => ceval cs x)
          (fun x => veval_nil x) (fun c cs x => veval_cons (HV := CTvs) c cs x) xs Q hnd ltac:(lia) i ltac:(lia)).
        rewrite (vsum_ext _ (fun j => cpow (encg g pk zero (τ j)) (lam xs i j)))
          by (intros j hj; rewrite hQev by lia; reflexivity).
        rewrite hk; apply csum_encg. }
      specialize (hQi m ltac:(lia)).
      unfold Q in hQi; rewrite !(nth_vpadd (HV := CTvs)), hEm, !nth_map_cpow in hQi.
      unfold Bp, βl in hQi; rewrite map_map in hQi.
      rewrite (PolyPerm.nth_map_seq (fun i => encg g pk (β i) zero)) in hQi by lia.
      apply cancel_inv2 in hQi.
      (* β_m = 0 since c_(B_m) is the identity, unless binding breaks. *)
      assert (hβm : β m = zero \/ binding_break h gs).
      { pose proof (hopenB m ltac:(lia)) as h0.
        pose proof (eq_trans (com_zero_single (Hvec := Hvec) h gs) (eq_trans (eq_sym hcBm) h0)) as h1.
        destruct (open_eq_or_break h gs _ _ _ _ h1) as [[_ e] | hbb]; [left | right; exact hbb].
        specialize (e 0%nat ltac:(lia)); cbn [nth] in e; symmetry; exact e. }
      destruct hβm as [hβm | hbb]; [| right; exact hbb].
      rewrite hβm, (encg_zero_zero (Hvec := Hvec)), (vadd_vid_l (HV := CTvs)) in hQi.
      set (Astmt := map (fun i => A' (S i)) (seq 0 m)).
      assert (hA''eq : A'' = A' 0%nat :: Astmt) by (unfold A'', Astmt; cbn [seq map]; rewrite <-seq_shift, map_map; reflexivity).
      (* The middle diagonal is D_m = ∏_i C_i^(A_(i+1)). *)
      assert (hDm : nth m D cone = cprod (map (fun p => cmexp (snd p) (nth (fst p) Astmt [])) (combine (seq 0 m) Cs))).
      { unfold D, BayerGroth.diagonals; rewrite (nth_fold_cpadd (Hvec := Hvec)), map_map.
        f_equal; apply map_ext_in; intros (i & Ci) hp; apply in_combine_l in hp; apply in_seq in hp; cbn [fst snd].
        rewrite (nth_diag_row_m m A'' i Ci) by (lia || exact hA''l).
        rewrite hA''eq; cbn [nth]; reflexivity. }
      rewrite hDm in hQi.
      left. exists Astmt, (map (fun i => r' (S i)) (seq 0 m)), (ρ m).
      assert (hr''eq : r'' = r' 0%nat :: map (fun i => r' (S i)) (seq 0 m)) by (unfold r''; cbn [seq map]; rewrite <-seq_shift, map_map; reflexivity).
      rewrite hA''eq, hr''eq, com_list_cons in hcAl. injection hcAl as _ hcAl.
      split; [exact hcAl |].
      split; [unfold Astmt; rewrite length_map, length_seq; reflexivity |].
      split; [rewrite length_map, length_seq; reflexivity |].
      split; [intros v hv; apply hA''len; rewrite hA''eq; right; exact hv |].
      exact hQi.
    Qed.

    (** ** Shuffle argument

        Statement: input ciphertexts [Cs] and output ciphertexts [Cs'], both
        of length [N = m·n]. The prover commits to [a = (π(0), …, π(N-1))]
        (as [cA], [m] rows of [n]) and, after the challenge [x], to [b =
        (x^π(0), …, x^π(N-1))] (as [cB]). After [y], [z] it gives a product
        argument for [∏_i (y a_i + b_i − z) = ∏_i (y i + x^i − z)] on the
        commitments [c_A^y · c_B · com(−z, …, −z)], and a
        multi-exponentiation argument for [∏_i C_i^(x^i) = Enc(1; ρ) ·
        ∏_i C'_i^(b_i)]. *)

    (** *** Helpers *)

    Local Notation shuffle_verify := (shuffle_verify (zero := zero) (one := one) (add := add) (mul := mul)
      (sub := sub) (opp := opp) (Fdec := Fdec) (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) (l := l)).
    Local Notation mk_shuffle := (@mk_shuffle F G l).

    (** Unpacking of an accepting shuffle transcript: the size conditions
        [m ≥ 1], [n ≥ 2], [length Cs = length Cs' = N], [length cA = length
        cB = m], acceptance of the product argument on [shuffle_product_stmt]
        and of the multi-exponentiation argument on [(chunk n m Cs', ∏_i
        C_i^(x^i), cB)]. *)
    Lemma shuffle_verify_true : forall h gs g pk m n (Cs Cs' : list CT) x y z xh yh xz xs xm cA cB prod mexp,
      shuffle_verify h gs g pk m n Cs Cs' x y z xh yh xz xs xm (mk_shuffle cA cB prod mexp) = true ->
      (1 <= m)%nat /\ (2 <= n)%nat /\ length Cs = (m * n)%nat /\ length Cs' = (m * n)%nat /\ length cA = m /\ length cB = m /\
      product_verify h gs n
        (map (fun c => gop c (com h gs (repeat (opp z) n) zero)) (map (fun p => gop ((fst p) ^ y) (snd p)) (combine cA cB)))
        (fold_right mul one (map (fun i => y * fnat i + fpow x i - z) (seq 0 (m * n)))) xh yh xz xs prod = true /\
      multiexp_verify h gs g pk (chunk n m Cs') (cmexp Cs (lpows x (m * n))) cB xm mexp = true.
    Proof.
      intros * hv; unfold BayerGroth.shuffle_verify, BayerGroth.shuffle_product_stmt, BayerGroth.shuffle_mexp_C in hv;
        cbv zeta in hv; cbn [sh_cA sh_cB sh_prod sh_mexp fst snd] in hv.
      repeat match goal with h : (_ && _)%bool = true |- _ => apply andb_prop in h; destruct h end.
      repeat match goal with
        | h : (_ <=? _)%nat = true |- _ => apply Nat.leb_le in h
        | h : (_ =? _)%nat = true |- _ => apply Nat.eqb_eq in h
        end.
      repeat split; assumption.
    Qed.

    (** [chunk n] inverts [concat] on a list of rows of length [n]. *)
    Lemma chunk_concat : forall (L : list (list F)) (n : nat), Forall (fun v => length v = n) L ->
      chunk n (length L) (concat L) = L.
    Proof.
      induction L as [| a L ih]; intros n hL; [reflexivity |].
      inversion hL as [| ? ? ha hL']; subst. cbn [length concat chunk].
      rewrite firstn_app, skipn_app, firstn_all2, skipn_all2 by lia.
      rewrite Nat.sub_diag; cbn [firstn skipn app]. rewrite app_nil_r, (ih _ hL'). reflexivity.
    Qed.

    (** A concatenation of [k] rows of length [n] has length [k·n]. *)
    Lemma concat_length_rows : forall (L : list (list F)) (n : nat), Forall (fun v => length v = n) L ->
      length (concat L) = (length L * n)%nat.
    Proof.
      induction L as [| v L ih]; intros n hL; [reflexivity |].
      apply Forall_cons_iff in hL; destruct hL as [hv hL]. cbn [concat length]; rewrite length_app, hv, (ih n hL); lia.
    Qed.

    (** [combine] distributes over [++] when the first parts have equal
        lengths. *)
    Lemma combine_app' : forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B), length l1 = length l1' ->
      combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
    Proof.
      intros A B l1; induction l1 as [| a l1 ih]; intros l2 l1' l2' hl; destruct l1' as [| a' l1']; try discriminate; [reflexivity |].
      cbn [app combine]; rewrite ih by (cbn in hl; lia); reflexivity.
    Qed.

    (** Rowwise application of a binary map followed by [concat] equals the
        same map applied to the concatenations. *)
    Lemma concat_map_combine : forall (f : F -> F -> F) (A B : list (list F)) (n : nat),
      length A = length B -> Forall (fun v => length v = n) A -> Forall (fun v => length v = n) B ->
      concat (map (fun p => map (fun q => f (fst q) (snd q)) (combine (fst p) (snd p))) (combine A B)) =
      map (fun q => f (fst q) (snd q)) (combine (concat A) (concat B)).
    Proof.
      intros f A; induction A as [| a A ih]; intros B n hl hA hB; destruct B as [| b B]; try discriminate; [reflexivity |].
      apply Forall_cons_iff in hA; destruct hA as [ha hA]. apply Forall_cons_iff in hB; destruct hB as [hb hB].
      cbn [combine map concat fst snd].
      rewrite (ih B n ltac:(cbn in hl; lia) hA hB).
      rewrite combine_app' by congruence. rewrite map_app. reflexivity.
    Qed.

    (** [y a + b − (z, …, z)] as vector arithmetic equals the entrywise map
        [(a_i, b_i) ↦ y a_i + b_i − z]. *)
    Lemma padd_lscale_combine : forall (y z : F) (a b : list F) (n : nat), length a = n -> length b = n ->
      padd (padd (lscale y a) b) (repeat (opp z) n) = map (fun q => y * fst q + snd q - z) (combine a b).
    Proof.
      intros y z a; induction a as [| a0 a ih]; intros b n ha hb; destruct b as [| b0 b]; destruct n as [| n]; try discriminate;
        [reflexivity |].
      cbn [SigmaK.lscale map repeat SigmaK.padd combine fst snd]. rewrite <-(ih b n) by (cbn in *; lia).
      f_equal; field.
    Qed.

    (** An entrywise map over [combine a b] written by indices. *)
    Lemma map_combine_nth : forall (f : F -> F -> F) (a b : list F) (N : nat), length a = N -> length b = N ->
      map (fun q => f (fst q) (snd q)) (combine a b) = map (fun k => f (nth k a zero) (nth k b zero)) (seq 0 N).
    Proof.
      intros f a b N ha hb. apply (nth_ext _ _ zero zero).
      + rewrite !length_map, length_combine, length_seq; lia.
      + intros k hk. rewrite length_map, length_combine in hk.
        rewrite PolyPerm.nth_map_seq by lia.
        rewrite (nth_indep _ zero ((fun q => f (fst q) (snd q)) (zero, zero))) by (rewrite length_map, length_combine; lia).
        rewrite (map_nth (fun q => f (fst q) (snd q))), combine_nth by lia. reflexivity.
    Qed.

    (** Finite choice: from [∀ k < N, ∃ r, P k r] build a list [rs] of length
        [N] with [P k (rs_k)]. Used to collect the randomisers [ρ_i]. *)
    Lemma forall_exists_list : forall (P : nat -> F -> Prop) (N : nat),
      (forall k, (k < N)%nat -> exists r, P k r) -> exists rs : list F, length rs = N /\ forall k, (k < N)%nat -> P k (nth k rs zero).
    Proof.
      intros P N; induction N as [| N ih]; intros h.
      + exists []; split; [reflexivity | intros k hk; lia].
      + destruct ih as (rs & hl & hrs); [intros k hk; apply h; lia |].
        destruct (h N ltac:(lia)) as (r & hr).
        exists (rs ++ [r]); split; [rewrite length_app; cbn; lia |].
        intros k hk. destruct (Nat.eq_dec k N) as [-> | hne].
        - rewrite app_nth2, hl, Nat.sub_diag by lia; exact hr.
        - rewrite app_nth1 by lia; apply hrs; lia.
    Qed.

    (** A product of powers of encryptions of 1 is an encryption of 1. *)
    Lemma csum_in_enc : forall g pk (f : nat -> CT) (c : nat -> F) (k : nat),
      (forall j, (j < k)%nat -> exists ρ, f j = encg g pk zero ρ) ->
      exists ρ, csum (fun j => cpow (f j) (c j)) k = encg g pk zero ρ.
    Proof.
      intros g pk f c k; induction k as [| k ih]; intros h.
      + exists zero; cbn [vsum]; symmetry; apply (encg_zero_zero (Hvec := Hvec)).
      + destruct ih as (ρ & hρ); [intros j hj; apply h; lia |].
        destruct (h k ltac:(lia)) as (ρk & hk).
        exists (ρ + ρk * c k). cbn [vsum]. rewrite hρ, hk, (encg_pow (Hvec := Hvec)), (encg_mul (Hvec := Hvec)).
        f_equal; field.
    Qed.

    (** [perm_inv σ N j]: the index [k < N] with [σ_k = j], found by search
        (returns 0 if there is none). For a permutation given as the list of
        its values this is the inverse permutation. *)
    Definition perm_inv (σ : list nat) (N : nat) (j : nat) : nat :=
      match find (fun k => Nat.eqb (nth k σ 0%nat) j) (seq 0 N) with Some k => k | None => 0%nat end.

    (** For [σ] a permutation of [0 … N-1] and [j < N]: [perm_inv σ N j < N]
        and [σ (perm_inv σ N j) = j]. *)
    Lemma perm_inv_spec : forall (σ : list nat) (N j : nat), Permutation σ (seq 0 N) -> (j < N)%nat ->
      (perm_inv σ N j < N)%nat /\ nth (perm_inv σ N j) σ 0%nat = j.
    Proof.
      intros σ N j hp hj. unfold perm_inv.
      destruct (find (fun k => Nat.eqb (nth k σ 0%nat) j) (seq 0 N)) as [k |] eqn:hf.
      + apply find_some in hf; destruct hf as [hk he]; apply in_seq in hk; apply Nat.eqb_eq in he. split; [lia | exact he].
      + exfalso.
        assert (hin : In j σ) by (eapply Permutation_in; [apply Permutation_sym; exact hp | apply in_seq; lia]).
        destruct (In_nth σ j 0%nat hin) as (k & hk & hnk).
        pose proof (find_none _ _ hf k) as h. rewrite (Permutation_length hp), length_seq in hk.
        specialize (h ltac:(apply in_seq; lia)). cbv beta in h. rewrite hnk, Nat.eqb_refl in h; discriminate.
    Qed.

    (** [perm_inv σ N (σ k) = k] for [k < N]. *)
    Lemma perm_inv_nth : forall (σ : list nat) (N k : nat), Permutation σ (seq 0 N) -> (k < N)%nat ->
      perm_inv σ N (nth k σ 0%nat) = k.
    Proof.
      intros σ N k hp hk.
      assert (hnd : NoDup σ) by (eapply Permutation_NoDup; [apply Permutation_sym; exact hp | apply seq_NoDup]).
      assert (hlen : length σ = N) by (rewrite (Permutation_length hp), length_seq; reflexivity).
      assert (hj : (nth k σ 0 < N)%nat).
      { assert (hin : In (nth k σ 0%nat) (seq 0 N)) by (eapply Permutation_in; [exact hp | apply nth_In; lia]).
        apply in_seq in hin; lia. }
      destruct (perm_inv_spec σ N (nth k σ 0%nat) hp hj) as (h1 & h2).
      apply (proj1 (NoDup_nth σ 0%nat) hnd); [lia | lia | exact h2].
    Qed.

    (** [perm_inv σ N] is itself a permutation of [0 … N-1]. *)
    Lemma perm_inv_perm : forall (σ : list nat) (N : nat), Permutation σ (seq 0 N) ->
      Permutation (map (perm_inv σ N) (seq 0 N)) (seq 0 N).
    Proof.
      intros σ N hp. apply NoDup_Permutation_bis.
      + apply (proj2 (NoDup_nth _ 0%nat)). rewrite length_map, length_seq. intros i i' hi hi' e.
        rewrite !PolyPerm.nth_map_seq in e by assumption.
        destruct (perm_inv_spec σ N i hp hi) as (_ & e1). destruct (perm_inv_spec σ N i' hp hi') as (_ & e2).
        rewrite <-e1, <-e2, e; reflexivity.
      + rewrite length_map, !length_seq; lia.
      + intros j hj. apply in_map_iff in hj; destruct hj as (i & <- & hi); apply in_seq in hi.
        apply in_seq. destruct (perm_inv_spec σ N i hp ltac:(lia)) as (h & _); lia.
    Qed.

    (** [combine] with an indexed list, written by indices. *)
    Lemma combine_nth_seq : forall (L : list CT) (f : nat -> F) (N : nat), length L = N ->
      combine L (map f (seq 0 N)) = map (fun k => (nth k L cone, f k)) (seq 0 N).
    Proof.
      intros L f N hl. apply (nth_ext _ _ (cone, zero) (cone, zero)).
      + rewrite length_combine, !length_map, !length_seq; lia.
      + intros k hk. rewrite length_combine, length_map, length_seq in hk.
        rewrite combine_nth by (rewrite length_map, length_seq; lia).
        rewrite !PolyPerm.nth_map_seq by lia. reflexivity.
    Qed.

    (** Reindexing of a multi-exponentiation along a permutation:
        [∏_k C'_k^(x^(σ(k))) = Σ_j x^j C'_(σ⁻¹(j))], i.e. the ciphertext
        polynomial whose [j]-th coefficient is [C'_(σ⁻¹(j))]. *)
    Lemma cmexp_perm : forall (Cs' : list CT) (σ : list nat) (N : nat) (x : F),
      length Cs' = N -> Permutation σ (seq 0 N) ->
      cmexp Cs' (map (fun k => fpow x (nth k σ 0%nat)) (seq 0 N)) =
      ceval (map (fun j => nth (perm_inv σ N j) Cs' cone) (seq 0 N)) x.
    Proof.
      intros Cs' σ N x hl hp.
      unfold veval. rewrite length_map, length_seq, lpows_map, !lmexp_as_fold.
      rewrite (combine_nth_seq Cs' (fun k => fpow x (nth k σ 0%nat)) N hl), combine_map_same, !map_map. cbn [fst snd].
      apply (fold_vadd_perm (HV := CTvs)).
      rewrite (map_ext_in (fun j => cpow (nth (perm_inv σ N j) Cs' cone) (fpow x j))
        (fun j => (fun k => cpow (nth k Cs' cone) (fpow x (nth k σ 0%nat))) (perm_inv σ N j))).
      2: { intros j hj; apply in_seq in hj. cbv beta. destruct (perm_inv_spec σ N j hp ltac:(lia)) as (_ & e). rewrite e; reflexivity. }
      rewrite <-(map_map (perm_inv σ N) (fun k => cpow (nth k Cs' cone) (fpow x (nth k σ 0%nat)))).
      apply Permutation_map. apply Permutation_sym. apply perm_inv_perm; exact hp.
    Qed.

    (** [sh_pst] and [sh_bprod] are the two components of the product
        statement of the shuffle ([shuffle_product_stmt]): the commitment
        list [c_(A_i)^y · c_(B_i) · com((−z, …, −z); 0)] and the public value
        [∏_(i<N) (y i + x^i − z)]. *)
    Definition sh_pst (h : G) (gs : list G) (n : nat) (cA cB : list G) (y z : F) : list G :=
      map (fun c => gop c (com h gs (repeat (opp z) n) zero)) (map (fun p => gop ((fst p) ^ y) (snd p)) (combine cA cB)).
    Definition sh_bprod (N : nat) (x y z : F) : F :=
      fold_right mul one (map (fun i => y * fnat i + fpow x i - z) (seq 0 N)).

    (** [sh_pst] has [length cA] entries when [length cB = length cA]. *)
    Lemma sh_pst_length : forall h gs n cA cB y z, length cB = length cA -> length (sh_pst h gs n cA cB y z) = length cA.
    Proof. intros; unfold sh_pst; rewrite !length_map, length_combine; lia. Qed.

    (** Rotation [(a · b) · c = (c · a) · b] in the commutative group. *)
    Lemma gop_rot : forall a b c : G, gop (gop a b) c = gop (gop c a) b.
    Proof. intros; rewrite (gcomm (gop a b) c), gassoc; reflexivity. Qed.

    (** The [i]-th entry of [sh_pst]. *)
    Lemma nth_sh_pst : forall h gs n cA cB y z i, length cB = length cA -> (i < length cA)%nat ->
      nth i (sh_pst h gs n cA cB y z) gid = gop (gop ((nth i cA gid) ^ y) (nth i cB gid)) (com h gs (repeat (opp z) n) zero).
    Proof.
      intros * hl hi; unfold sh_pst.
      rewrite (nth_indep _ gid ((fun c => gop c (com h gs (repeat (opp z) n) zero)) gid))
        by (rewrite !length_map, length_combine; lia).
      rewrite (map_nth (fun c => gop c (com h gs (repeat (opp z) n) zero))).
      rewrite (nth_indep _ gid ((fun p : G * G => gop ((fst p) ^ y) (snd p)) (gid, gid)))
        by (rewrite length_map, length_combine; lia).
      rewrite (map_nth (fun p : G * G => gop ((fst p) ^ y) (snd p))), combine_nth by lia. reflexivity.
    Qed.

    (** [X · Y⁻¹ = W] gives [X = W · Y] in the ciphertext space. *)
    Lemma cancel_inv1' : forall X Y W : CT, cmul X (cpow Y (opp one)) = W -> X = cmul W Y.
    Proof. intros X Y W h. rewrite <-h, <-(vadd_assoc (HV := CTvs)), cmul_inv_l, (vadd_vid_r (HV := CTvs)); reflexivity. Qed.

    (** Distinct positions of a duplicate-free list hold distinct values. *)
    Lemma nth_NoDup_neq : forall (Y : list F) (i j : nat), NoDup Y -> (i < length Y)%nat -> (j < length Y)%nat -> i <> j ->
      nth i Y zero <> nth j Y zero.
    Proof. intros Y i j hnd hi hj hne e; apply hne; apply (proj1 (NoDup_nth Y zero) hnd); assumption. Qed.

    (** *** Soundness of the shuffle

        Special soundness of the Bayer–Groth shuffle argument. Let [n =
        length gs ≥ 2], [m ≥ 1], [N = m·n]. Hypotheses:

        - [fnat] is injective on [0 … N-1] (field characteristic above N);
        - [X]: [N] distinct challenges [x]; [Y]: more than [2N²] distinct
          challenges [y]; [Z]: more than [N] distinct challenges [z];
        - for the product argument: [Xh] ([m] distinct), [Yh] ([n]
          distinct), zero-argument lists [Zs p q] ([2m+1] distinct each) and
          [XS] ([n+1] distinct), as in [product_soundness];
        - [XM]: [2m] distinct multi-exponentiation challenges;
        - [cA] is fixed; [cB] depends only on [x]; the product-argument
          first messages depend on [(x, y, z)] (and the zero-argument ones
          also on [(p, q)]); the multi-exponentiation first message depends
          only on [x]; and every transcript in this tree is accepted.

        Conclusion: either binding breaks or there are a permutation [σ] of
        [0 … N-1] and [ρs] of length [N] with
        [C'_i = Enc(1; ρ_i) · C_(σ(i))] for every [i < N], which is the
        shuffle relation (re-encryption and permutation).

        Proof idea: [product_soundness] at every [(x, y, z)] and
        [multiexp_soundness] at every [x]. Two values of [y] open [cA] to
        [a] (from [c_A^y c_B]). For each [x] the multi-exponentiation
        opens [cB] to [b], and binding turns the product argument into the
        identity [∏_i (y a_i + b_i − z) = ∏_i (y i + x^i − z)] at all [y ∈
        Y], [z ∈ Z]; [perm_of_products] then gives a permutation [σ] with
        [a_k = σ(k)] and [b_k = x^(σ(k))]; [σ] is the same for every [x]
        because [a] is. Hence [∏ C_i^(x^i) = Enc(1; ρ_x) · ∏_k
        C'_k^(x^(σ(k)))], so the ciphertext polynomial [Q] with coefficients
        [C_j / C'_(σ⁻¹(j))] is an encryption of 1 at [N] distinct points,
        and by [coeff_from_evals] each coefficient is an encryption of 1. *)
    Theorem shuffle_soundness : forall (h g : G) (gs : list G) (pk : Vector.t G l) (m : nat) (Cs Cs' : list CT) (cA : list G)
      (X Y Z Xh Yh XS XM : list F) (Zs : nat -> nat -> list F)
      (cB : nat -> list G) (pcb : nat -> nat -> nat -> G) (pcB : nat -> nat -> nat -> list G)
      (zA0 zBm : nat -> nat -> nat -> nat -> nat -> G) (zcd : nat -> nat -> nat -> nat -> nat -> list G)
      (za zb : nat -> nat -> nat -> nat -> nat -> nat -> list F) (zr zt zu : nat -> nat -> nat -> nat -> nat -> nat -> F)
      (scd scδ scΔ : nat -> nat -> nat -> G) (ta tb : nat -> nat -> nat -> nat -> list F) (rt st : nat -> nat -> nat -> nat -> F)
      (mA0 : nat -> G) (mcB : nat -> list G) (mE : nat -> list CT) (ma : nat -> nat -> list F) (mr mb ms mτ : nat -> nat -> F),
      let n := length gs in let N := (m * n)%nat in
      (1 <= m)%nat -> (2 <= n)%nat ->
      (forall i j, (i < N)%nat -> (j < N)%nat -> fnat i = fnat j -> i = j) ->
      NoDup X -> length X = N -> NoDup Y -> (2 * (N * N) < length Y)%nat -> NoDup Z -> (N < length Z)%nat ->
      NoDup Xh -> length Xh = m -> NoDup Yh -> length Yh = n ->
      (forall p q, (p < m)%nat -> (q < n)%nat -> NoDup (Zs p q) /\ length (Zs p q) = (2 * m + 1)%nat) ->
      NoDup XS -> length XS = S n -> NoDup XM -> length XM = (2 * m)%nat ->
      (forall jx jy jz p q j j' jm, (jx < N)%nat -> (jy < length Y)%nat -> (jz < length Z)%nat -> (p < m)%nat -> (q < n)%nat ->
        (j < 2 * m + 1)%nat -> (j' < S n)%nat -> (jm < 2 * m)%nat ->
        shuffle_verify h gs g pk m n Cs Cs' (nth jx X zero) (nth jy Y zero) (nth jz Z zero) (nth p Xh zero) (nth q Yh zero)
          (nth j (Zs p q) zero) (nth j' XS zero) (nth jm XM zero)
          (mk_shuffle cA (cB jx)
            (mk_prod (pcb jx jy jz)
              (Some (mk_had (pcB jx jy jz) (mk_zero (zA0 jx jy jz p q) (zBm jx jy jz p q) (zcd jx jy jz p q)
                (za jx jy jz p q j) (zb jx jy jz p q j) (zr jx jy jz p q j) (zt jx jy jz p q j) (zu jx jy jz p q j))))
              (mk_svp (scd jx jy jz) (scδ jx jy jz) (scΔ jx jy jz) (ta jx jy jz j') (tb jx jy jz j') (rt jx jy jz j') (st jx jy jz j')))
            (mk_mexp (mA0 jx) (mcB jx) (mE jx) (ma jx jm) (mr jx jm) (mb jx jm) (ms jx jm) (mτ jx jm))) = true) ->
      (exists (σ : list nat) (ρs : list F), Permutation σ (seq 0 N) /\ length ρs = N /\
        forall i, (i < N)%nat -> nth i Cs' cone = cmul (encg g pk zero (nth i ρs zero)) (nth (nth i σ 0%nat) Cs cone))
      \/ binding_break h gs.
    Proof.
      intros h g gs pk m Cs Cs' cA X Y Z Xh Yh XS XM Zs cB pcb pcB zA0 zBm zcd za zb zr zt zu scd scδ scΔ ta tb rt st
        mA0 mcB mE ma mr mb ms mτ n N hm hn hinj hXnd hXl hYnd hYl hZnd hZl hXhnd hXhl hYhnd hYhl hZs hSnd hSl hMnd hMl htr.
      assert (hn_eq : length gs = n) by reflexivity. assert (hN_eq : (m * n)%nat = N) by reflexivity.
      assert (hN : (1 <= N)%nat) by (unfold N; nia).
      set (x := fun jx => nth jx X zero). set (y := fun jy => nth jy Y zero). set (z := fun jz => nth jz Z zero).
      assert (hbase : (1 <= m)%nat /\ (2 <= n)%nat /\ length Cs = N /\ length Cs' = N /\ length cA = m).
      { pose proof (htr 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as hv.
        apply shuffle_verify_true in hv. tauto. }
      destruct hbase as (_ & _ & hCs & hCs' & hcA).
      assert (hcB : forall jx, (jx < N)%nat -> length (cB jx) = m).
      { intros jx hjx. pose proof (htr jx 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat hjx ltac:(lia) ltac:(lia) ltac:(lia)
          ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as hv.
        apply shuffle_verify_true in hv. tauto. }
      (* The product and multi-exponentiation sub-transcripts at every
         challenge tuple. *)
      assert (hprod : forall jx jy jz p q j j', (jx < N)%nat -> (jy < length Y)%nat -> (jz < length Z)%nat -> (p < m)%nat -> (q < n)%nat ->
        (j < 2 * m + 1)%nat -> (j' < S n)%nat ->
        product_verify h gs n (sh_pst h gs n cA (cB jx) (y jy) (z jz)) (sh_bprod N (x jx) (y jy) (z jz))
          (nth p Xh zero) (nth q Yh zero) (nth j (Zs p q) zero) (nth j' XS zero)
          (mk_prod (pcb jx jy jz)
            (Some (mk_had (pcB jx jy jz) (mk_zero (zA0 jx jy jz p q) (zBm jx jy jz p q) (zcd jx jy jz p q)
              (za jx jy jz p q j) (zb jx jy jz p q j) (zr jx jy jz p q j) (zt jx jy jz p q j) (zu jx jy jz p q j))))
            (mk_svp (scd jx jy jz) (scδ jx jy jz) (scΔ jx jy jz) (ta jx jy jz j') (tb jx jy jz j') (rt jx jy jz j') (st jx jy jz j'))) = true).
      { intros jx jy jz p q j j' hjx hjy hjz hp hq hj hj'.
        pose proof (htr jx jy jz p q j j' 0%nat hjx hjy hjz hp hq hj hj' ltac:(lia)) as hv.
        apply shuffle_verify_true in hv. destruct hv as (_ & _ & _ & _ & _ & _ & hpv & _). exact hpv. }
      assert (hmexp : forall jx jm, (jx < N)%nat -> (jm < 2 * m)%nat ->
        multiexp_verify h gs g pk (chunk n m Cs') (cmexp Cs (lpows (x jx) N)) (cB jx) (nth jm XM zero)
          (mk_mexp (mA0 jx) (mcB jx) (mE jx) (ma jx jm) (mr jx jm) (mb jx jm) (ms jx jm) (mτ jx jm)) = true).
      { intros jx jm hjx hjm.
        pose proof (htr jx 0%nat 0%nat 0%nat 0%nat 0%nat 0%nat jm hjx ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) hjm) as hv.
        apply shuffle_verify_true in hv. destruct hv as (_ & _ & _ & _ & _ & _ & _ & hmx). exact hmx. }
      (* Product-argument soundness at every (x, y, z). *)
      assert (hP : forall jx jy jz, (jx < N)%nat -> (jy < length Y)%nat -> (jz < length Z)%nat ->
        (exists (D : list (list F)) (t : list F),
          sh_pst h gs n cA (cB jx) (y jy) (z jz) = com_list h gs D t /\ length D = m /\ length t = m /\
          (forall v, In v D -> length v = n) /\ fold_right mul one (hprefix D (m - 1)) = sh_bprod N (x jx) (y jy) (z jz))
        \/ binding_break h gs).
      { intros jx jy jz hjx hjy hjz.
        assert (hl : length (sh_pst h gs n cA (cB jx) (y jy) (z jz)) = m) by (rewrite sh_pst_length, hcA by (rewrite hcB, hcA; lia); reflexivity).
        destruct (product_soundness h gs (sh_pst h gs n cA (cB jx) (y jy) (z jz)) (sh_bprod N (x jx) (y jy) (z jz))
          (pcb jx jy jz) (pcB jx jy jz) Xh Yh (zA0 jx jy jz) (zBm jx jy jz) (zcd jx jy jz) Zs
          (za jx jy jz) (zb jx jy jz) (zr jx jy jz) (zt jx jy jz) (zu jx jy jz)
          (scd jx jy jz) (scδ jx jy jz) (scΔ jx jy jz) XS (ta jx jy jz) (tb jx jy jz) (rt jx jy jz) (st jx jy jz))
          as [(D & t & h1 & h2 & h3 & h4 & h5) | hbb]; [lia | rewrite hl; lia | exact hXhnd | rewrite hl; exact hXhl
            | exact hYhnd | exact hYhl | exact hSnd | exact hSl | | | right; exact hbb].
        + intros p q hp hq. rewrite hl in hp. destruct (hZs p q hp hq) as (hz1 & hz2). split; [exact hz1 | split; [rewrite hl; exact hz2 |]].
          intros j hj. rewrite hl in hj. intros j' hj'. exact (hprod jx jy jz p q j j' hjx hjy hjz hp hq hj hj').
        + left. exists D, t. rewrite hl in h2, h3, h5. repeat split; assumption. }
      (* Multi-exponentiation soundness at every x. *)
      assert (hM : forall jx, (jx < N)%nat ->
        (exists (B : list (list F)) (sB : list F) (ρ : F),
          cB jx = com_list h gs B sB /\ length B = m /\ length sB = m /\ (forall v, In v B -> length v = n) /\
          cmexp Cs (lpows (x jx) N) = cmul (encg g pk zero ρ)
            (cprod (map (fun p => cmexp (snd p) (nth (fst p) B [])) (combine (seq 0 m) (chunk n m Cs')))))
        \/ binding_break h gs).
      { intros jx hjx.
        destruct (multiexp_soundness h g gs pk (chunk n m Cs') (cmexp Cs (lpows (x jx) N)) (cB jx) (mA0 jx) (mcB jx) (mE jx) XM
          (ma jx) (mr jx) (mb jx) (ms jx) (mτ jx)) as [(B & sB & ρ & h1 & h2 & h3 & h4 & h5) | hbb];
          [lia | rewrite hcB by exact hjx; exact hm | exact hMnd | rewrite hcB by exact hjx; exact hMl | | | right; exact hbb].
        + intros jm hjm. rewrite hMl in hjm. exact (hmexp jx jm hjx hjm).
        + left. exists B, sB, ρ. rewrite hcB in h2, h3, h5 by exact hjx. repeat split; assumption. }
      (* Open cA from two distinct values of y: the i-th product-statement
         commitment is the linear polynomial c_(B_i) com(−z) · c_(A_i)^y. *)
      assert (hY2 : (2 <= length Y)%nat) by nia.
      assert (hy01 : y 0%nat <> y 1%nat) by (apply nth_NoDup_neq; [exact hYnd | lia | lia | lia]).
      destruct (hP 0%nat 0%nat 0%nat hN ltac:(lia) ltac:(lia)) as [(D0 & t0 & hD0 & hD0l & ht0l & hD0n & _) | hbb]; [| right; exact hbb].
      destruct (hP 0%nat 1%nat 0%nat hN ltac:(lia) ltac:(lia)) as [(D1 & t1 & hD1 & hD1l & ht1l & hD1n & _) | hbb]; [| right; exact hbb].
      set (Dsel := fun jy => match jy with 0 => D0 | _ => D1 end).
      set (tsel := fun jy => match jy with 0 => t0 | _ => t1 end).
      set (Y2 := [y 0%nat; y 1%nat]).
      assert (hY2nd : NoDup Y2) by (unfold Y2; constructor; [intros [e | []]; apply hy01; symmetry; exact e | constructor; [intros [] | constructor]]).
      set (Aop := fun i => lcomb (lam Y2 1) (fun jy => nth i (Dsel jy) []) 2).
      set (rop := fun i => fsum (fun jy => lam Y2 1 jy * nth i (tsel jy) zero) 2).
      assert (hcB0 : length (cB 0%nat) = length cA) by (rewrite hcB, hcA by exact hN; reflexivity).
      assert (hcAi : forall i, (i < m)%nat -> nth i cA gid = com h gs (Aop i) (rop i)).
      { intros i hi.
        pose proof (geval_openings h gs Y2 [gop (nth i (cB 0%nat) gid) (com h gs (repeat (opp (z 0%nat)) n) zero); nth i cA gid]
          (fun jy => nth i (Dsel jy) []) (fun jy => nth i (tsel jy) zero) hY2nd eq_refl) as hg.
        cbn [length] in hg.
        assert (hev : forall jy, (jy < 2)%nat -> geval [gop (nth i (cB 0%nat) gid) (com h gs (repeat (opp (z 0%nat)) n) zero); nth i cA gid]
          (nth jy Y2 zero) = com h gs (nth i (Dsel jy) []) (nth i (tsel jy) zero)).
        { intros jy hjy. destruct jy as [| [| jy]]; try lia; unfold Y2, Dsel, tsel; cbn [nth]; rewrite geval_pair, gop_rot.
          + rewrite <-(nth_sh_pst h gs n cA (cB 0%nat) (y 0%nat) (z 0%nat) i hcB0 ltac:(lia)), hD0.
            rewrite (nth_com_list (zero := zero)) by lia; reflexivity.
          + rewrite <-(nth_sh_pst h gs n cA (cB 0%nat) (y 1%nat) (z 0%nat) i hcB0 ltac:(lia)), hD1.
            rewrite (nth_com_list (zero := zero)) by lia; reflexivity. }
        specialize (hg hev 1%nat ltac:(unfold Y2; cbn; lia)). cbn [nth] in hg. exact hg. }
      assert (hAn : forall i, (i < m)%nat -> length (Aop i) = n).
      { intros i hi. unfold Aop. apply lcomb_length; [lia |]. intros jy hjy. destruct jy as [| [| jy]]; try lia; cbn [Dsel].
        + apply hD0n, nth_In; lia.
        + apply hD1n, nth_In; lia. }
      set (Amat := map Aop (seq 0 m)). set (a := concat Amat).
      assert (hAmat : cA = com_list h gs Amat (map rop (seq 0 m))) by (apply com_list_of_openings; [exact hcA | exact hcAi]).
      assert (hAmatl : length Amat = m) by (unfold Amat; rewrite length_map, length_seq; reflexivity).
      assert (hAmatn : Forall (fun v => length v = n) Amat).
      { unfold Amat; rewrite Forall_forall; intros v hv; apply in_map_iff in hv; destruct hv as (i & <- & hi); apply in_seq in hi; apply hAn; lia. }
      assert (hal : length a = N) by (unfold a; rewrite (concat_length_rows Amat n hAmatn), hAmatl; exact hN_eq).
      (* For each x: the openings of cB are x^σ(k) along a permutation σ of
         the entries of a, via binding and perm_of_products. *)
      assert (hjx : forall jx, (jx < N)%nat ->
        (exists (B : list (list F)) (ρ : F) (σ' : list nat), Permutation σ' (seq 0 N) /\
          (forall k, (k < N)%nat -> nth k a zero = fnat (nth k σ' 0%nat)) /\
          (forall k, (k < N)%nat -> nth k (concat B) zero = fpow (x jx) (nth k σ' 0%nat)) /\
          length B = m /\ Forall (fun v => length v = n) B /\
          cmexp Cs (lpows (x jx) N) = cmul (encg g pk zero ρ) (cmexp Cs' (concat B)))
        \/ binding_break h gs).
      { intros jx hjx.
        destruct (hM jx hjx) as [(B & sB & ρ & hcBl & hBl & hsBl & hBn & hC) | hbb]; [| right; exact hbb].
        assert (hBf : Forall (fun v => length v = n) B) by (rewrite Forall_forall; exact hBn).
        set (b := concat B).
        assert (hbl : length b = N) by (unfold b; rewrite (concat_length_rows B n hBf), hBl; exact hN_eq).
        (* The product identity at every (y, z), by binding. *)
        assert (hid : (forall jy, (jy < length Y)%nat -> forall jz, (jz < length Z)%nat ->
            fold_right mul one (map (fun k => y jy * nth k a zero + nth k b zero - z jz) (seq 0 N)) =
            fold_right mul one (map (fun k => y jy * fnat k + fpow (x jx) k - z jz) (seq 0 N))) \/ binding_break h gs).
        { apply forall_or; intros jy hjy. apply forall_or; intros jz hjz.
          destruct (hP jx jy jz hjx hjy hjz) as [(D & t & hD & hDl & htl & hDn & hDp) | hbb]; [| right; exact hbb].
          assert (hDi : (forall i, (i < m)%nat -> nth i D [] = padd (padd (lscale (y jy) (Aop i)) (nth i B [])) (repeat (opp (z jz)) n))
            \/ binding_break h gs).
          { apply forall_or; intros i hi.
            pose proof (nth_sh_pst h gs n cA (cB jx) (y jy) (z jz) i ltac:(rewrite hcB, hcA; lia) ltac:(lia)) as e1.
            rewrite hD, (nth_com_list (zero := zero)) in e1 by lia.
            rewrite hcAi, hcBl, (nth_com_list (zero := zero)) in e1 by (lia || (rewrite hBl, hsBl; lia)).
            rewrite <-(com_scale (Hvec := Hvec)), <-!(com_padd (Hvec := Hvec)) in e1.
            assert (hl1 : length (padd (padd (lscale (y jy) (Aop i)) (nth i B [])) (repeat (opp (z jz)) n)) = length gs).
            { rewrite !SigmaK.padd_length, repeat_length; unfold SigmaK.lscale; rewrite length_map, hAn by exact hi.
              rewrite hBn by (apply nth_In; lia). lia. }
            assert (hl2 : length (nth i D []) = length gs) by (apply hDn, nth_In; lia).
            destruct (open_eq_or_break_len h gs _ _ _ _ hl2 hl1 e1) as [[e _] | hbb]; [left; exact e | right; exact hbb]. }
          destruct hDi as [hDi | hbb]; [| right; exact hbb].
          left.
          assert (hDeq : D = map (fun p => map (fun q => y jy * fst q + snd q - z jz) (combine (fst p) (snd p))) (combine Amat B)).
          { apply (nth_ext _ _ [] []); [rewrite length_map, length_combine; lia |].
            intros i hi. rewrite hDl in hi. rewrite hDi by exact hi.
            rewrite (nth_indep (map (fun p => map (fun q => y jy * fst q + snd q - z jz) (combine (fst p) (snd p))) (combine Amat B)) []
              ((fun p => map (fun q => y jy * fst q + snd q - z jz) (combine (fst p) (snd p))) ([], [])))
              by (rewrite length_map, length_combine; lia).
            rewrite (map_nth (fun p => map (fun q => y jy * fst q + snd q - z jz) (combine (fst p) (snd p)))), combine_nth by lia.
            cbn [fst snd]. unfold Amat; rewrite PolyPerm.nth_map_seq by exact hi.
            apply padd_lscale_combine; [apply hAn; exact hi | apply hBn, nth_In; lia]. }
          rewrite <-(map_combine_nth (fun u v => y jy * u + v - z jz) a b N hal hbl).
          unfold a, b. rewrite <-(concat_map_combine (fun u v => y jy * u + v - z jz) Amat B n) by (lia || assumption).
          rewrite <-hDeq. fold (sh_bprod N (x jx) (y jy) (z jz)). rewrite <-hDp.
          pose proof (prod_hprefix_concat (Hvec := Hvec) n D ltac:(destruct D; [cbn in hDl; lia | discriminate])
            ltac:(rewrite Forall_forall; exact hDn)) as hpc.
          rewrite hDl in hpc. rewrite hpc. reflexivity. }
        destruct hid as [hid | hbb]; [| right; exact hbb].
        destruct (perm_of_products (Fdec := Fdec) (Hf := Hf) N a b (x jx) Y Z hal hbl hinj hYnd hZnd hZl hYl) as (σ' & hσ' & hab).
        { intros y0 z0 hy0 hz0. destruct (In_nth Y y0 zero hy0) as (jy & hjy & <-). destruct (In_nth Z z0 zero hz0) as (jz & hjz & <-).
          apply hid; assumption. }
        left. exists B, ρ, σ'. split; [exact hσ' |].
        split; [intros k hk; apply (hab k hk) |].
        split; [intros k hk; apply (hab k hk) |].
        split; [exact hBl | split; [exact hBf |]].
        rewrite hC. f_equal. rewrite <-(cmexp_chunks (Hvec := Hvec) n m Cs' (concat B) hCs' hbl).
        rewrite <-hBl, chunk_concat by exact hBf. reflexivity. }
      (* Fix the permutation obtained at the first x. *)
      destruct (hjx 0%nat hN) as [(B0 & ρ0 & σ & hσ & haσ & _) | hbb]; [| right; exact hbb].
      assert (hσl : length σ = N) by (rewrite (Permutation_length hσ), length_seq; reflexivity).
      assert (hσk : forall k, (k < N)%nat -> (nth k σ 0 < N)%nat).
      { intros k hk. assert (hin : In (nth k σ 0%nat) (seq 0 N)) by (eapply Permutation_in; [exact hσ | apply nth_In; lia]).
        apply in_seq in hin; lia. }
      (* Q(X) = C(X) · C''(X)⁻¹ with C''_j = C'_(σ⁻¹(j)) is an encryption
         of 1 at every x; the permutation is the same for every x since it
         is determined by a. *)
      set (Cs'' := map (fun j => nth (perm_inv σ N j) Cs' cone) (seq 0 N)).
      set (Q := cpadd Cs (map (fun c => cpow c (opp one)) Cs'')).
      assert (hQ : (forall jx, (jx < N)%nat -> exists ρ, ceval Q (x jx) = encg g pk zero ρ) \/ binding_break h gs).
      { apply forall_or; intros jx hjx'.
        destruct (hjx jx hjx') as [(B & ρ & σ' & hσ'' & haσ' & hbσ' & hBl & hBf & hC) | hbb]; [| right; exact hbb].
        left. exists ρ.
        assert (hσeq : σ' = σ).
        { assert (hσ'l : length σ' = N) by (rewrite (Permutation_length hσ''), length_seq; reflexivity).
          apply (nth_ext _ _ 0%nat 0%nat); [lia |].
          intros k hk. rewrite hσ'l in hk.
          assert (hk' : (nth k σ' 0 < N)%nat).
          { assert (hin : In (nth k σ' 0%nat) (seq 0 N)) by (eapply Permutation_in; [exact hσ'' | apply nth_In; lia]). apply in_seq in hin; lia. }
          apply hinj; [exact hk' | apply hσk; exact hk | rewrite <-haσ', <-haσ by exact hk; reflexivity]. }
        subst σ'.
        assert (hbeq : concat B = map (fun k => fpow (x jx) (nth k σ 0%nat)) (seq 0 N)).
        { apply (nth_ext _ _ zero zero).
          + rewrite length_map, length_seq, (concat_length_rows B n hBf), hBl; exact hN_eq.
          + intros k hk. rewrite (concat_length_rows B n hBf), hBl, hN_eq in hk.
            rewrite PolyPerm.nth_map_seq by exact hk. apply hbσ'; exact hk. }
        rewrite hbeq, (cmexp_perm Cs' σ N (x jx) hCs' hσ) in hC.
        unfold Q; rewrite (veval_vpadd (HV := CTvs)), (veval_scale_coeffs (HV := CTvs)).
        fold Cs''. unfold veval at 1. rewrite hCs. rewrite hC. apply cmul_cancel. }
      destruct hQ as [hQ | hbb]; [| right; exact hbb].
      assert (hCs''l : length Cs'' = N) by (unfold Cs''; rewrite length_map, length_seq; reflexivity).
      assert (hQl : length Q = N) by (unfold Q; rewrite (vpadd_length (vadd := cmul)), length_map, hCs, hCs''l; lia).
      (* Coefficients of Q, by the inverse Vandermonde matrix in the
         ciphertext space, are encryptions of 1. *)
      assert (hQk : forall k, (k < N)%nat -> exists ρ, nth k Cs cone = cmul (encg g pk zero ρ) (nth (perm_inv σ N k) Cs' cone)).
      { intros k hk.
        pose proof (coeff_from_evals (Fdec := Fdec) (Hf := Hf) (HV := CTvs) (fun cs x => ceval cs x)
          (fun x => veval_nil x) (fun c cs x => veval_cons (HV := CTvs) c cs x) X Q hXnd ltac:(rewrite hQl, hXl; reflexivity) k ltac:(lia)) as hc.
        destruct (csum_in_enc g pk (fun j => ceval Q (nth j X zero)) (lam X k) (length X)) as (ρ & hρ).
        { intros j hj; apply hQ; lia. }
        exists ρ. cbv beta in hc. rewrite hρ in hc. unfold Q in hc. rewrite (nth_vpadd (HV := CTvs)), nth_map_cpow in hc.
        unfold Cs'' in hc; rewrite PolyPerm.nth_map_seq in hc by exact hk.
        apply cancel_inv1' in hc. exact hc. }
      (* Re-index to C'_i = Enc(1; −ρ) · C_(σ(i)) and collect the
         randomisers into a list. *)
      assert (hfin : forall i, (i < N)%nat -> exists ρ, nth i Cs' cone = cmul (encg g pk zero ρ) (nth (nth i σ 0%nat) Cs cone)).
      { intros i hi. destruct (hQk (nth i σ 0%nat) (hσk i hi)) as (ρ & hρ).
        rewrite perm_inv_nth in hρ by (exact hσ || exact hi).
        exists (opp ρ). rewrite hρ, (vadd_assoc (HV := CTvs)), (encg_mul (Hvec := Hvec)).
        replace (zero + zero) with zero by field. replace (opp ρ + ρ) with zero by field.
        rewrite (encg_zero_zero (Hvec := Hvec)), (vadd_vid_l (HV := CTvs)); reflexivity. }
      destruct (forall_exists_list (fun i ρ => nth i Cs' cone = cmul (encg g pk zero ρ) (nth (nth i σ 0%nat) Cs cone)) N hfin)
        as (ρs & hρsl & hρs).
      left. exists σ, ρs. split; [exact hσ | split; [exact hρsl | exact hρs]].
    Qed.

  End MultiExpSound.

End BayerGrothSound.
