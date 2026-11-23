(** * Fiat–Shamir verifier for Bayer–Groth shuffle arguments *)

(** This file makes the interactive Bayer–Groth shuffle argument of
    [Sigma.BayerGroth] (S. Bayer and J. Groth, ‘Efficient zero-knowledge
    argument for correctness of a shuffle’, EUROCRYPT 2012) non-interactive,
    in the format of the Swiss Post e-voting system (crypto-primitives
    specification 1.6.0: Algorithm 9.12 VerifyShuffleArgument and
    Algorithms 9.16, 9.19, 9.21, 9.23, 9.26 for the sub-arguments). The
    extracted verifier ([Examples.BayerGrothIns]) is driven by
    src/Executable/Bgverifier on the Swiss Post test vectors (3072-bit group
    [p = 2q + 1], [g = 2]) and in differential testing
    (bench/swisspost-diff).

    The argument is a tree of sub-arguments: the shuffle argument consists
    of a product argument and a multi-exponentiation argument; the product
    argument consists (for [m > 1]) of a Hadamard argument and a single
    value product (SVP) argument; the Hadamard argument ends in a zero
    argument. Each interactive verifier in [Sigma.BayerGroth] takes its
    challenges as arguments.

    How the challenges are derived. Swiss Post computes every challenge with
    RecursiveHash (SHA3-256) over the group parameters [p, q], the public key,
    the commitment key, the statement and the announcements, in a fixed
    order. Here the hash functions are a record [oracles] of closures over
    the group parameters and statement, supplied by the OCaml driver; each
    field takes the announcements in the order the specification hashes
    them:

    - [o_x c_A] for [x = H(p, q, pk, ck, C, C', c_A)];
    - [o_y c_A c_B] and [o_z c_A c_B] for [y] and [z] (the latter with
      prefix ‘1’);
    - [o_xh] and [o_yh] for the Hadamard challenges over [(c_A, c_b, c_B)];
    - [o_xz] for the zero argument over [(c_A0, c_Bm, c_d, c_B, c_A)];
    - [o_xs] for the SVP argument over [(c_Δ, c_δ, c_d, b, c_a)];
    - [o_xm] for the multi-exponentiation argument over
      [(C_matrix, C, c_A, c_A0, c_B, E)].

    The verifier recomputes the statements of the inner sub-arguments exactly
    as the interactive verifiers do, so each [*_verify_fs] is, by definition,
    the interactive verifier at the oracle's challenges ([*_verify_fs_spec],
    proved by [reflexivity]).

    Main results:

    - Completeness: [svp_fs_completeness], [zero_fs_completeness],
      [hadamard_fs_completeness], [multiexp_fs_completeness],
      [product_fs_completeness], [shuffle_fs_completeness]. The honest
      provers ([*_prove_fs]) query the oracle on their announcements stage
      by stage; since announcements never depend on later challenges
      (the [*_indep] lemmas), the challenges the prover used are the ones
      the verifier recomputes ([shuffle_challenges_prove]). The Hadamard
      completeness needs oracles whose Hadamard challenges are never zero.
    - Soundness in rewinding form, [shuffle_fs_soundness]: if the
      Fiat–Shamir verifier accepts the proofs of a whole tree of
      reprogrammed oracles (one per index of challenge choices, each
      returning prescribed distinct challenges on the announcements of its
      proof), then either the output ciphertexts are a re-encryption and
      permutation of the inputs or the commitment key is broken
      ([binding_break]). It is a direct consequence of [shuffle_soundness]
      in [Sigma.BayerGrothSound].
    - One-query soundness error for single-challenge arguments:
      [zero_fs_soundness_error], [svp_fs_soundness_error],
      [multiexp_fs_soundness_error], via [k_special_soundness_error] from
      [Sigma.SigmaK]: for a prover with fixed announcements answering the
      challenge [c] with responses [resp c], either a witness exists, or the
      binding is broken, or the acceptance probability over a uniform [c] is
      at most [(k − 1)/|lf|].

    What is NOT verified. The probabilistic analysis of the forking
    (rewinding) argument, i.e. the loss in the number of oracle queries, is
    not formalised; [shuffle_fs_soundness] is its deterministic core. The
    hash encoding (RecursiveHash, SHA3-256), the parsing of the input files,
    the subgroup-membership and range checks of the inputs, and the
    derivation of the commitment key are done by the unverified OCaml
    driver. Hardness of breaking commitment binding is not
    formalised; it appears only as the disjunct [binding_break]. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool List Permutation PArith setoid_ring.Field.
From Stdlib Require Import PeanoNat.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Sigma Require Import Sigma MultiExp OkamotoRows SigmaK BayerGroth BayerGrothSound.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import ListNotations.

(** ** Setting *)

(** The field [F] and prime-order group [G] (an [F]-vector space). [l] is
    the number of message components of a ciphertext; a ciphertext [CT] is
    a vector of [l + 1] group elements (randomness component and message
    components), with componentwise product [cmul], power [cpow], identity
    [cone], multi-exponentiation [cmexp] and product of a list [cprod]. *)
Section BayerGrothVerifier.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  Context {l : nat}.
  Local Notation CT := (Vector.t G (S l)).
  Local Notation cone := (vec_id (V := G) (vid := gid) (S l)).
  Local Notation cmul := (vec_add (vadd := gop) (n := S l)).
  Local Notation cpow := (vec_smul (smul := gpow) (n := S l)).
  Local Notation cmexp := (lmexp (vid := cone) (vadd := cmul) (smul := cpow)).
  Local Notation cprod := (fold_right cmul cone).

  (** Short names for the argument records of [Sigma.BayerGroth], and
      versions of its commitment, encryption, prover and verifier functions
      specialised to the operations of this section. *)
  Local Notation svp_argument := (@svp_argument F G).
  Local Notation zero_argument := (@zero_argument F G).
  Local Notation hadamard_argument := (@hadamard_argument F G).
  Local Notation multiexp_argument := (@multiexp_argument F G l).
  Local Notation product_argument := (@product_argument F G).
  Local Notation shuffle_argument := (@shuffle_argument F G l).

  Local Notation com := (com (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation com_list := (com_list (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation hprefix := (hprefix (mul := mul)).
  Local Notation enc := (enc (gop := gop) (gpow := gpow) (l := l)).
  Local Notation svp_verify := (svp_verify (zero := zero) (mul := mul) (sub := sub) (Fdec := Fdec)
    (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation svp_prove := (svp_prove (zero := zero) (one := one) (add := add) (mul := mul)
    (sub := sub) (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation zero_verify := (zero_verify (zero := zero) (one := one) (add := add) (mul := mul)
    (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation zero_prove := (zero_prove (zero := zero) (one := one) (add := add) (mul := mul)
    (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation hadamard_zero_stmt := (hadamard_zero_stmt (zero := zero) (one := one) (mul := mul)
    (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation hadamard_verify := (hadamard_verify (zero := zero) (one := one) (add := add)
    (mul := mul) (opp := opp) (Fdec := Fdec) (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)).
  Local Notation hadamard_prove := (hadamard_prove (zero := zero) (one := one) (add := add)
    (mul := mul) (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation multiexp_verify := (multiexp_verify (one := one) (mul := mul) (gid := gid)
    (gop := gop) (gpow := gpow) (Gdec := Gdec) (l := l)).
  Local Notation multiexp_prove := (multiexp_prove (zero := zero) (one := one) (add := add)
    (mul := mul) (gid := gid) (gop := gop) (gpow := gpow) (l := l)).
  Local Notation product_verify := (product_verify (zero := zero) (one := one) (add := add)
    (mul := mul) (sub := sub) (opp := opp) (Fdec := Fdec) (gid := gid) (gop := gop) (gpow := gpow)
    (Gdec := Gdec)).
  Local Notation product_prove := (product_prove (zero := zero) (one := one) (add := add)
    (mul := mul) (sub := sub) (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation shuffle_product_stmt := (shuffle_product_stmt (zero := zero) (one := one)
    (add := add) (mul := mul) (sub := sub) (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation shuffle_mexp_C := (shuffle_mexp_C (one := one) (mul := mul) (gid := gid)
    (gop := gop) (gpow := gpow) (l := l)).
  Local Notation shuffle_verify := (shuffle_verify (zero := zero) (one := one) (add := add)
    (mul := mul) (sub := sub) (opp := opp) (Fdec := Fdec) (gid := gid) (gop := gop) (gpow := gpow)
    (Gdec := Gdec) (l := l)).
  Local Notation shuffle_prove := (shuffle_prove (zero := zero) (one := one) (add := add)
    (mul := mul) (sub := sub) (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (l := l)).

  (** ** The random oracles *)

  (** The eight hash functions used by the Swiss Post verifier, as functions
      of the announcements (statement and group parameters fixed in the
      closures); see the file header for the exact inputs. *)
  Record oracles : Type := mk_oracles {
    o_x : list G -> F;
    o_y : list G -> list G -> F;
    o_z : list G -> list G -> F;
    o_xh : list G -> G -> list G -> F;
    o_yh : list G -> G -> list G -> F;
    o_xz : G -> G -> list G -> list G -> list G -> F;
    o_xs : G -> G -> G -> F -> G -> F;
    o_xm : list (list CT) -> CT -> list G -> G -> list G -> list CT -> F }.

  (** ** Single value product argument (Algorithms 9.25, 9.26) *)

  (** The SVP challenge [x = o_xs(c_Δ, c_δ, c_d, b, c_a)] for the claim that
      [c_a] commits to a vector whose product is [b]. *)
  Definition svp_challenge (O : oracles) (ca : G) (b : F) (arg : svp_argument) : F :=
    o_xs O (svp_cDelta arg) (svp_cdelta arg) (svp_cd arg) b ca.

  (** Fiat–Shamir SVP verifier: the interactive [svp_verify] at the oracle
      challenge. *)
  Definition svp_verify_fs (O : oracles) (h : G) (gs : list G) (ca : G) (b : F) (arg : svp_argument) : bool :=
    svp_verify h gs ca b (svp_challenge O ca b arg) arg.

  (** [svp_verify_fs] unfolds to the interactive verifier at
      [svp_challenge]. *)
  Theorem svp_verify_fs_spec : forall O h gs ca b arg,
    svp_verify_fs O h gs ca b arg = svp_verify h gs ca b (svp_challenge O ca b arg) arg.
  Proof. reflexivity. Qed.

  (** If the interactive verifier accepts at the oracle challenge, so does
      [svp_verify_fs]. Used to transfer completeness. *)
  Lemma svp_verify_fs_of : forall O h gs ca b arg x,
    svp_challenge O ca b arg = x -> svp_verify h gs ca b x arg = true -> svp_verify_fs O h gs ca b arg = true.
  Proof. intros * <- hv; exact hv. Qed.

  (** Honest non-interactive SVP prover: the announcements [c_d, c_δ, c_Δ]
      do not depend on the challenge, so the prover runs once with
      challenge [0] to obtain them, hashes them and reruns with the
      resulting challenge. *)
  Definition svp_prove_fs (O : oracles) (h : G) (gs : list G) (a : list F) (r : F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F) : svp_argument :=
    let ca := com h gs a r in
    let b := fold_right mul one a in
    let arg0 := svp_prove h gs a r d rd dmid s0 sx zero in
    svp_prove h gs a r d rd dmid s0 sx (svp_challenge O ca b arg0).

  (** FS completeness of the SVP argument: for [a] of length at least two
      matching the commitment key, with correctly sized randomness, the
      verifier accepts the honest proof for [c_a = com h gs a r] and
      [b = ∏ a_i]. From [svp_completeness]. *)
  Theorem svp_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (a : list F) (r : F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F),
    (2 <= length a)%nat -> length d = length a -> length dmid = (length a - 2)%nat -> length a = length gs ->
    svp_verify_fs O h gs (com h gs a r) (fold_right mul one a) (svp_prove_fs O h gs a r d rd dmid s0 sx) = true.
  Proof.
    intros; unfold svp_prove_fs; cbv zeta.
    eapply svp_verify_fs_of; [| apply (svp_completeness (Hvec := Hvec)); assumption].
    reflexivity.
  Qed.

  (** ** Zero argument (Algorithms 9.22, 9.23) *)

  (** The zero-argument challenge [o_xz(c_A0, c_Bm, c_d, c_B, c_A)]. *)
  Definition zero_challenge (O : oracles) (cA cB : list G) (arg : zero_argument) : F :=
    o_xz O (za_cA0 arg) (za_cBm arg) (za_cd arg) cB cA.

  (** Fiat–Shamir zero-argument verifier: [zero_verify] at the oracle
      challenge, for commitments [cA], [cB] and bilinear-map parameter
      [y]. *)
  Definition zero_verify_fs (O : oracles) (h : G) (gs : list G) (cA cB : list G) (y : F)
    (arg : zero_argument) : bool :=
    zero_verify h gs cA cB y (zero_challenge O cA cB arg) arg.

  (** [zero_verify_fs] unfolds to the interactive verifier. *)
  Theorem zero_verify_fs_spec : forall O h gs cA cB y arg,
    zero_verify_fs O h gs cA cB y arg = zero_verify h gs cA cB y (zero_challenge O cA cB arg) arg.
  Proof. reflexivity. Qed.

  (** Transfer of acceptance from the interactive verifier at the oracle
      challenge. *)
  Lemma zero_verify_fs_of : forall O h gs cA cB y arg x,
    zero_challenge O cA cB arg = x -> zero_verify h gs cA cB y x arg = true -> zero_verify_fs O h gs cA cB y arg = true.
  Proof. intros * <- hv; exact hv. Qed.

  (** Honest non-interactive zero-argument prover: announcements computed
      with challenge [0], hashed, then the prover reruns at that
      challenge. *)
  Definition zero_prove_fs (O : oracles) (h : G) (gs : list G) (A B : list (list F)) (r s : list F) (y : F)
    (a0 bm : list F) (r0 sm : F) (t1 t2 : list F) : zero_argument :=
    let cA := com_list h gs A r in
    let cB := com_list h gs B s in
    let arg0 := zero_prove h gs A B r s y a0 bm r0 sm t1 t2 zero in
    zero_prove h gs A B r s y a0 bm r0 sm t1 t2 (zero_challenge O cA cB arg0).

  (** FS completeness of the zero argument: if
      [Σ_i A_i ⋆_y B_i = 0] (the bilinear map [star]) and the dimensions
      match, the honest proof is accepted. From [zero_completeness]. *)
  Theorem zero_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (A B : list (list F))
    (r s : list F) (y : F) (a0 bm : list F) (r0 sm : F) (t1 t2 : list F),
    (1 <= length A)%nat -> length B = length A -> length r = length A -> length s = length A ->
    length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
    Forall (fun v => length v = length gs) (a0 :: A) -> Forall (fun v => length v = length gs) (bm :: B) ->
    fold_right add zero (map (fun p => star (zero := zero) (add := add) (mul := mul) y (fst p) (snd p)) (combine A B)) = zero ->
    zero_verify_fs O h gs (com_list h gs A r) (com_list h gs B s) y
      (zero_prove_fs O h gs A B r s y a0 bm r0 sm t1 t2) = true.
  Proof.
    intros; unfold zero_prove_fs; cbv zeta.
    eapply zero_verify_fs_of; [| apply (zero_completeness (Hvec := Hvec)); assumption].
    reflexivity.
  Qed.

  (** ** Hadamard argument (Algorithms 9.20, 9.21) *)

  (** The three Hadamard-level challenges. *)
  Record hchal : Type := mk_hchal { hc_x : F; hc_y : F; hc_xz : F }.

  (** Computes [x = o_xh(c_A, c_b, c_B)], [y = o_yh(c_A, c_b, c_B)] and the
      challenge of the inner zero argument on the zero statement that the
      verifier derives from [(c_A, c_B, x)] ([hadamard_zero_stmt]). *)
  Definition hadamard_challenges (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (cb : G)
    (arg : hadamard_argument) : hchal :=
    let cB := ha_cB arg in
    let x := o_xh O cA cb cB in
    let y := o_yh O cA cb cB in
    let st := hadamard_zero_stmt h gs n cA cB x in
    mk_hchal x y (zero_challenge O (fst st) (snd st) (ha_zero arg)).

  (** Fiat–Shamir Hadamard verifier: [hadamard_verify] at the oracle
      challenges. *)
  Definition hadamard_verify_fs (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (cb : G)
    (arg : hadamard_argument) : bool :=
    let c := hadamard_challenges O h gs n cA cb arg in
    hadamard_verify h gs n cA cb (hc_x c) (hc_y c) (hc_xz c) arg.

  (** [hadamard_verify_fs] unfolds to the interactive verifier. *)
  Theorem hadamard_verify_fs_spec : forall O h gs n cA cb arg,
    hadamard_verify_fs O h gs n cA cb arg =
    hadamard_verify h gs n cA cb (hc_x (hadamard_challenges O h gs n cA cb arg))
      (hc_y (hadamard_challenges O h gs n cA cb arg)) (hc_xz (hadamard_challenges O h gs n cA cb arg)) arg.
  Proof. reflexivity. Qed.

  (** Transfer of acceptance from the interactive Hadamard verifier. *)
  Lemma hadamard_verify_fs_of : forall O h gs n cA cb arg x y xz,
    hadamard_challenges O h gs n cA cb arg = mk_hchal x y xz ->
    hadamard_verify h gs n cA cb x y xz arg = true -> hadamard_verify_fs O h gs n cA cb arg = true.
  Proof. intros * hc hv; unfold hadamard_verify_fs; rewrite hc; exact hv. Qed.

  (** Honest non-interactive Hadamard prover. Stage 1: [c_B] does not depend
      on the challenges, so [x] and [y] are read off a run with all
      challenges zero. Stage 2: the zero-argument announcements depend on
      [x] and [y], so the zero challenge is read off a run with those values.
      The final argument uses all three. *)
  Definition hadamard_prove_fs (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F))
    (r : list F) (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F) : hadamard_argument :=
    let cA := com_list h gs A r in
    let cb := com h gs (hprefix A (length A - 1)) s in
    let P := fun x y xz => hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 xz in
    let c0 := hadamard_challenges O h gs n cA cb (P zero zero zero) in
    let c1 := hadamard_challenges O h gs n cA cb (P (hc_x c0) (hc_y c0) zero) in
    P (hc_x c0) (hc_y c0) (hc_xz c1).

  (** The challenges recomputed from the honest Hadamard argument are the
      ones used to produce it, given the staged definitions. *)
  Lemma hadamard_challenges_prove : forall O h gs n A r s smid a0z bmz r0z smz t1 t2 cA cb x y xz,
    hc_x (hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid zero zero a0z bmz r0z smz t1 t2 zero)) = x ->
    hc_y (hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid zero zero a0z bmz r0z smz t1 t2 zero)) = y ->
    hc_xz (hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 zero)) = xz ->
    hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 xz) = mk_hchal x y xz.
  Proof. intros; subst; reflexivity. Qed.

  (** FS completeness of the Hadamard argument: for at least two rows of
      equal length [n] matching the key, the verifier accepts the honest
      proof for [c_A = com_list A r] and [c_b] the commitment to their
      Hadamard product. Requires an oracle whose [x] and [y] are never
      zero (the interactive completeness needs non-zero challenges). *)
  Theorem hadamard_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F))
    (r : list F) (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F),
    (2 <= length A)%nat -> Forall (fun a => length a = n) A -> length r = length A ->
    length smid = (length A - 2)%nat -> length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
    n = length gs -> length a0z = length gs -> length bmz = length gs ->
    (forall cA cb cB, o_xh O cA cb cB <> zero) -> (forall cA cb cB, o_yh O cA cb cB <> zero) ->
    hadamard_verify_fs O h gs n (com_list h gs A r) (com h gs (hprefix A (length A - 1)) s)
      (hadamard_prove_fs O h gs n A r s smid a0z bmz r0z smz t1 t2) = true.
  Proof.
    intros O h gs n A r s smid a0z bmz r0z smz t1 t2 hm hA hr hsmid ht1 ht2 hng ha0z hbmz hx hy; unfold hadamard_prove_fs; cbv beta zeta.
    eapply hadamard_verify_fs_of; [| apply (hadamard_completeness (Hvec := Hvec)); try assumption;
      unfold hadamard_challenges; cbn [hc_x hc_y]; first [apply hx | apply hy]].
    apply hadamard_challenges_prove; reflexivity.
  Qed.

  (** ** Multi-exponentiation argument (Algorithms 9.15, 9.16) *)

  (** The challenge [o_xm(C_matrix, C, c_A, c_A0, c_B, E)]. *)
  Definition multiexp_challenge (O : oracles) (Cs : list (list CT)) (C : CT) (cA : list G)
    (arg : multiexp_argument) : F :=
    o_xm O Cs C cA (me_cA0 arg) (me_cB arg) (me_E arg).

  (** Fiat–Shamir multi-exponentiation verifier: [multiexp_verify] at the
      oracle challenge, for ciphertext matrix [Cs], target ciphertext [C]
      and commitments [cA]. *)
  Definition multiexp_verify_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
    (Cs : list (list CT)) (C : CT) (cA : list G) (arg : multiexp_argument) : bool :=
    multiexp_verify h gs g pk Cs C cA (multiexp_challenge O Cs C cA arg) arg.

  (** [multiexp_verify_fs] unfolds to the interactive verifier. *)
  Theorem multiexp_verify_fs_spec : forall O h gs g pk Cs C cA arg,
    multiexp_verify_fs O h gs g pk Cs C cA arg = multiexp_verify h gs g pk Cs C cA (multiexp_challenge O Cs C cA arg) arg.
  Proof. reflexivity. Qed.

  (** Transfer of acceptance from the interactive verifier. *)
  Lemma multiexp_verify_fs_of : forall O h gs g pk Cs C cA arg x,
    multiexp_challenge O Cs C cA arg = x -> multiexp_verify h gs g pk Cs C cA x arg = true ->
    multiexp_verify_fs O h gs g pk Cs C cA arg = true.
  Proof. intros * <- hv; exact hv. Qed.

  (** The ciphertext [C = Enc(1; ρ) · ∏_i C_i^{a_i}] of an honest
      multi-exponentiation statement, with [C_i] the [i]-th row of [Cs]
      and [a_i] the [i]-th row of [A]. *)
  Definition multiexp_C (g : G) (pk : Vector.t G l) (Cs : list (list CT)) (A : list (list F)) (ρ : F) : CT :=
    cmul (enc g pk (Vector.const gid l) ρ)
      (cprod (map (fun p => cmexp (snd p) (nth (fst p) A [])) (combine (seq 0 (length A)) Cs))).

  (** Honest non-interactive multi-exponentiation prover (announcements
      at challenge [0], then the real run). *)
  Definition multiexp_prove_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
    (Cs : list (list CT)) (A : list (list F)) (r : list F) (ρ : F) (a0 : list F) (r0 : F)
    (bs ss τs : list F) : multiexp_argument :=
    let cA := com_list h gs A r in
    let C := multiexp_C g pk Cs A ρ in
    let arg0 := multiexp_prove h gs g pk Cs A r ρ a0 r0 bs ss τs zero in
    multiexp_prove h gs g pk Cs A r ρ a0 r0 bs ss τs (multiexp_challenge O Cs C cA arg0).

  (** FS completeness of the multi-exponentiation argument for the honest
      statement [multiexp_C]. From [multiexp_completeness]. *)
  Theorem multiexp_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
    (Cs : list (list CT)) (A : list (list F)) (r : list F) (ρ : F) (a0 : list F) (r0 : F) (bs ss τs : list F),
    (1 <= length A)%nat -> length Cs = length A -> length r = length A ->
    length bs = (2 * length A)%nat -> length ss = (2 * length A)%nat -> length τs = (2 * length A)%nat ->
    Forall (fun v => length v = length gs) (a0 :: A) ->
    multiexp_verify_fs O h gs g pk Cs (multiexp_C g pk Cs A ρ) (com_list h gs A r)
      (multiexp_prove_fs O h gs g pk Cs A r ρ a0 r0 bs ss τs) = true.
  Proof.
    intros; unfold multiexp_prove_fs; cbv zeta.
    eapply multiexp_verify_fs_of; [| unfold multiexp_C; apply (multiexp_completeness (Hvec := Hvec)); assumption].
    reflexivity.
  Qed.

  (** ** Product argument (Algorithms 9.18, 9.19) *)

  (** The four product-level challenges: three Hadamard challenges and the
      SVP challenge. *)
  Record pchal : Type := mk_pchal { pc_xh : F; pc_yh : F; pc_xz : F; pc_xs : F }.

  (** For [m = |c_A| > 1] the product argument consists of a Hadamard
      argument on [(c_A, c_b)] and an SVP argument on [(c_b, b)]; for [m = 1]
      only the SVP argument on [(c_{A,1}, b)], and the Hadamard challenges
      are set to zero. *)
  Definition product_challenges (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (b : F)
    (arg : product_argument) : pchal :=
    let m := length cA in
    let hc := match pa_had arg with
      | Some had => hadamard_challenges O h gs n cA (pa_cb arg) had
      | None => mk_hchal zero zero zero
      end in
    let ca := if Nat.ltb 1 m then pa_cb arg else nth 0 cA gid in
    mk_pchal (hc_x hc) (hc_y hc) (hc_xz hc) (svp_challenge O ca b (pa_svp arg)).

  (** Fiat–Shamir product verifier: [product_verify] at the oracle
      challenges. *)
  Definition product_verify_fs (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (b : F)
    (arg : product_argument) : bool :=
    let c := product_challenges O h gs n cA b arg in
    product_verify h gs n cA b (pc_xh c) (pc_yh c) (pc_xz c) (pc_xs c) arg.

  (** [product_verify_fs] unfolds to the interactive verifier. *)
  Theorem product_verify_fs_spec : forall O h gs n cA b arg,
    product_verify_fs O h gs n cA b arg =
    product_verify h gs n cA b (pc_xh (product_challenges O h gs n cA b arg)) (pc_yh (product_challenges O h gs n cA b arg))
      (pc_xz (product_challenges O h gs n cA b arg)) (pc_xs (product_challenges O h gs n cA b arg)) arg.
  Proof. reflexivity. Qed.

  (** Transfer of acceptance from the interactive product verifier. *)
  Lemma product_verify_fs_of : forall O h gs n cA b arg xh yh xz xs,
    product_challenges O h gs n cA b arg = mk_pchal xh yh xz xs ->
    product_verify h gs n cA b xh yh xz xs arg = true -> product_verify_fs O h gs n cA b arg = true.
  Proof. intros * hc hv; unfold product_verify_fs; rewrite hc; exact hv. Qed.

  (** Honest non-interactive product prover, staged as for the Hadamard
      argument: [x_h], [y_h] and the SVP challenge from a run with all
      challenges zero, then the zero-argument challenge from a run with
      [x_h], [y_h]. *)
  Definition product_prove_fs (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F)
    (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F) : product_argument :=
    let cA := com_list h gs A r in
    let b := fold_right mul one (hprefix A (length A - 1)) in
    let P := fun xh yh xz xs => product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs in
    let c0 := product_challenges O h gs n cA b (P zero zero zero zero) in
    let c1 := product_challenges O h gs n cA b (P (pc_xh c0) (pc_yh c0) zero zero) in
    P (pc_xh c0) (pc_yh c0) (pc_xz c1) (pc_xs c0).

  (** The challenges recomputed from the honest product argument are the
      staged ones (case split on [m > 1]). *)
  Lemma product_challenges_prove : forall O h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx cA b xh yh xz xs,
    pc_xh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx zero zero zero zero)) = xh ->
    pc_yh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx zero zero zero zero)) = yh ->
    pc_xz (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh zero zero)) = xz ->
    pc_xs (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx zero zero zero zero)) = xs ->
    product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs) = mk_pchal xh yh xz xs.
  Proof.
    intros; subst; unfold product_challenges, product_prove; cbv zeta.
    destruct (Nat.ltb 1 (length A)); reflexivity.
  Qed.

  (** For [m > 1], the Hadamard challenges [x_h] and [y_h] of an honest
      product argument are oracle values and hence non-zero if the oracle
      never returns zero there. *)
  Lemma product_challenges_xh_nz : forall O h gs n cA b A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs,
    (forall cA cb cB, o_xh O cA cb cB <> zero) -> (1 < length A)%nat ->
    pc_xh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)) <> zero.
  Proof.
    intros * hx hlt. unfold product_challenges, BayerGroth.product_prove, hadamard_challenges; cbv zeta.
    rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) hlt). cbn [pa_had pa_cb pc_xh hc_x]. apply hx.
  Qed.

  Lemma product_challenges_yh_nz : forall O h gs n cA b A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs,
    (forall cA cb cB, o_yh O cA cb cB <> zero) -> (1 < length A)%nat ->
    pc_yh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)) <> zero.
  Proof.
    intros * hy hlt. unfold product_challenges, BayerGroth.product_prove, hadamard_challenges; cbv zeta.
    rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) hlt). cbn [pa_had pa_cb pc_yh hc_y]. apply hy.
  Qed.

  (** FS completeness of the product argument for [b = ∏] of all entries
      of [A] (via [hprefix]) and [c_A = com_list A r]. From
      [product_completeness], with the non-zero Hadamard challenges
      supplied by [product_challenges_xh_nz] and
      [product_challenges_yh_nz]. *)
  Theorem product_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F)
    (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F),
    (1 <= length A)%nat -> (2 <= n)%nat -> Forall (fun a => length a = n) A -> length r = length A ->
    length smid = (length A - 2)%nat -> length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
    length d = n -> length dmid = (n - 2)%nat ->
    n = length gs -> length a0z = length gs -> length bmz = length gs ->
    (forall cA cb cB, o_xh O cA cb cB <> zero) -> (forall cA cb cB, o_yh O cA cb cB <> zero) ->
    product_verify_fs O h gs n (com_list h gs A r) (fold_right mul one (hprefix A (length A - 1)))
      (product_prove_fs O h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx) = true.
  Proof.
    intros O h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx hm hn hA hr hsmid ht1 ht2 hd hdmid hng ha0z hbmz hx hy;
      unfold product_prove_fs; cbv beta zeta.
    eapply product_verify_fs_of; [| apply (product_completeness (Hvec := Hvec)); try assumption; intros hlt;
      first [eapply product_challenges_xh_nz; [exact hx | exact hlt] | eapply product_challenges_yh_nz; [exact hy | exact hlt]]].
    apply product_challenges_prove; reflexivity.
  Qed.

  (** ** Shuffle argument (Algorithms 9.11, 9.12) *)

  (** The eight challenges of a shuffle argument. *)
  Record schal : Type := mk_schal {
    sc_x : F; sc_y : F; sc_z : F; sc_xh : F; sc_yh : F; sc_xz : F; sc_xs : F; sc_xm : F }.

  (** All challenges of a shuffle argument for [N = m·n] ciphertexts
      arranged as an [m × n] matrix: [x] from [c_A], [y] and [z] from
      [(c_A, c_B)], the product-argument challenges on the statement
      [shuffle_product_stmt] (commitment [c_D · c_{−z}] and product
      [∏ (y·i + x^i − z)]), and the multi-exponentiation challenge on
      [(C' as an m × n matrix, ∏ C_i^{x^i}, c_B)]. *)
  Definition shuffle_challenges (O : oracles) (h : G) (gs : list G) (m n : nat) (Cs Cs' : list CT)
    (arg : shuffle_argument) : schal :=
    let N := (m * n)%nat in
    let cA := sh_cA arg in
    let cB := sh_cB arg in
    let x := o_x O cA in
    let y := o_y O cA cB in
    let z := o_z O cA cB in
    let st := shuffle_product_stmt h gs n N cA cB x y z in
    let pc := product_challenges O h gs n (fst st) (snd st) (sh_prod arg) in
    let xm := multiexp_challenge O (chunk n m Cs') (shuffle_mexp_C Cs x N) cB (sh_mexp arg) in
    mk_schal x y z (pc_xh pc) (pc_yh pc) (pc_xz pc) (pc_xs pc) xm.

  (** Fiat–Shamir shuffle verifier (Algorithm 9.12): [shuffle_verify] at the
      oracle challenges for input ciphertexts [Cs], output ciphertexts [Cs'],
      commitment key [(h, gs)], generator [g] and public key [pk]. *)
  Definition shuffle_verify_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
    (Cs Cs' : list CT) (arg : shuffle_argument) : bool :=
    let c := shuffle_challenges O h gs m n Cs Cs' arg in
    shuffle_verify h gs g pk m n Cs Cs' (sc_x c) (sc_y c) (sc_z c) (sc_xh c) (sc_yh c) (sc_xz c) (sc_xs c) (sc_xm c) arg.

  (** [shuffle_verify_fs] unfolds to the interactive verifier. *)
  Theorem shuffle_verify_fs_spec : forall O h gs g pk m n Cs Cs' arg,
    shuffle_verify_fs O h gs g pk m n Cs Cs' arg =
    let c := shuffle_challenges O h gs m n Cs Cs' arg in
    shuffle_verify h gs g pk m n Cs Cs' (sc_x c) (sc_y c) (sc_z c) (sc_xh c) (sc_yh c) (sc_xz c) (sc_xs c) (sc_xm c) arg.
  Proof. reflexivity. Qed.

  (** Transfer of acceptance from the interactive shuffle verifier. *)
  Lemma shuffle_verify_fs_of : forall O h gs g pk m n Cs Cs' arg x y z xh yh xz xs xm,
    shuffle_challenges O h gs m n Cs Cs' arg = mk_schal x y z xh yh xz xs xm ->
    shuffle_verify h gs g pk m n Cs Cs' x y z xh yh xz xs xm arg = true ->
    shuffle_verify_fs O h gs g pk m n Cs Cs' arg = true.
  Proof. intros * hc hv; unfold shuffle_verify_fs; rewrite hc; exact hv. Qed.

  (** Honest non-interactive shuffle prover, stage by stage: [c_A] gives
      [x]; [c_B] (which depends on [x]) gives [y] and [z]; the product
      statement and the Hadamard announcements give [x_h], [y_h], the SVP
      and multi-exponentiation announcements give [x_s] and [x_m]; finally
      the zero-argument announcements (which depend on [x_h], [y_h]) give
      [x_z]. [perm] is the permutation and [ρs] the re-encryption
      randomness. *)
  Definition shuffle_prove_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
    (Cs Cs' : list CT) (perm : list nat) (ρs : list F) (r s : list F)
    (sp : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F)
    (a0 : list F) (r0 : F) (bs ss τs : list F) : shuffle_argument :=
    let P := fun x y z xh yh xz xs xm =>
      shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
        x y z xh yh xz xs xm in
    let Q := shuffle_challenges O h gs m n Cs Cs' in
    let c0 := Q (P zero zero zero zero zero zero zero zero) in
    let x := sc_x c0 in
    let c1 := Q (P x zero zero zero zero zero zero zero) in
    let y := sc_y c1 in
    let z := sc_z c1 in
    let c2 := Q (P x y z zero zero zero zero zero) in
    let xh := sc_xh c2 in
    let yh := sc_yh c2 in
    let xs := sc_xs c2 in
    let xm := sc_xm c2 in
    let c3 := Q (P x y z xh yh zero xs xm) in
    P x y z xh yh (sc_xz c3) xs xm.

  (** *** Challenge independence *)

  (** The announcements of an honest prover do not depend on later
      challenges. [svp_challenge_indep] and [multiexp_challenge_indep]: the
      challenge computed from an honest SVP or multi-exponentiation argument
      does not depend on the challenge the argument was produced with. *)
  Lemma svp_challenge_indep : forall O ca b h gs a r d rd dmid s0 sx x x',
    svp_challenge O ca b (svp_prove h gs a r d rd dmid s0 sx x) = svp_challenge O ca b (svp_prove h gs a r d rd dmid s0 sx x').
  Proof. reflexivity. Qed.

  Lemma multiexp_challenge_indep : forall O Cs C cA h gs g pk Ms A r ρ a0 r0 bs ss τs x x',
    multiexp_challenge O Cs C cA (multiexp_prove h gs g pk Ms A r ρ a0 r0 bs ss τs x) =
    multiexp_challenge O Cs C cA (multiexp_prove h gs g pk Ms A r ρ a0 r0 bs ss τs x').
  Proof. reflexivity. Qed.

  (** The same for the product argument: [x_h], [y_h] and [x_s] do not
      depend on any product challenge, and [x_z] does not depend on [x_z]
      and [x_s] ([product_challenges_indep_xh], [_yh], [_xs], [_xz]). *)
  Lemma product_challenges_indep_xh : forall O h gs n cA b A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs xh' yh' xz' xs',
    pc_xh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)) =
    pc_xh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh' yh' xz' xs')).
  Proof. intros; unfold product_challenges, product_prove; cbv zeta; destruct (Nat.ltb 1 (length A)); reflexivity. Qed.

  Lemma product_challenges_indep_yh : forall O h gs n cA b A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs xh' yh' xz' xs',
    pc_yh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)) =
    pc_yh (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh' yh' xz' xs')).
  Proof. intros; unfold product_challenges, product_prove; cbv zeta; destruct (Nat.ltb 1 (length A)); reflexivity. Qed.

  Lemma product_challenges_indep_xs : forall O h gs n cA b A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs xh' yh' xz' xs',
    pc_xs (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)) =
    pc_xs (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh' yh' xz' xs')).
  Proof. intros; unfold product_challenges, product_prove; cbv zeta; destruct (Nat.ltb 1 (length A)); reflexivity. Qed.

  Lemma product_challenges_indep_xz : forall O h gs n cA b A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs xz' xs',
    pc_xz (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs)) =
    pc_xz (product_challenges O h gs n cA b (product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz' xs')).
  Proof. intros; unfold product_challenges, product_prove; cbv zeta; destruct (Nat.ltb 1 (length A)); reflexivity. Qed.

  (** Components of an honest shuffle argument, by computation: [c_A]
      commits to the permutation (as field elements), [c_B] to the
      permuted powers [x^{π(i)}], the product argument is on
      [y·π(i) + x^{π(i)} − z], and the multi-exponentiation argument is on
      the output ciphertexts with exponents [x^{π(i)}] and randomness
      [−Σ ρ_i x^{π(i)}]. *)
  Lemma sh_cA_prove : forall h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm,
    sh_cA (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm) =
    com_list h gs (chunk n m (map (fnat (zero := zero) (one := one) (add := add)) perm)) r.
  Proof. reflexivity. Qed.

  Lemma sh_cB_prove : forall h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm,
    sh_cB (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm) =
    com_list h gs (chunk n m (map (fun i => fpow (one := one) (mul := mul) x i) perm)) s.
  Proof. reflexivity. Qed.

  Lemma sh_prod_prove : forall h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm,
    sh_prod (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm) =
    product_prove h gs n
      (chunk n m (map (fun p => sub (add (mul y (fst p)) (snd p)) z)
        (combine (map (fnat (zero := zero) (one := one) (add := add)) perm) (map (fun i => fpow (one := one) (mul := mul) x i) perm))))
      (ladd (add := add) (lscale (mul := mul) y r) s) sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs.
  Proof. reflexivity. Qed.

  Lemma sh_mexp_prove : forall h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm,
    sh_mexp (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm) =
    multiexp_prove h gs g pk (chunk n m Cs') (chunk n m (map (fun i => fpow (one := one) (mul := mul) x i) perm)) s
      (opp (fold_right add zero (map (fun p => mul (fst p) (snd p)) (combine ρs (map (fun i => fpow (one := one) (mul := mul) x i) perm)))))
      a0 r0 bs ss τs xm.
  Proof. reflexivity. Qed.

  (** Unfolds [shuffle_challenges] and rewrites with the component lemmas
      above. *)
  Local Ltac sh_components :=
    unfold shuffle_challenges; cbv zeta; cbn [sc_x sc_y sc_z sc_xh sc_yh sc_xz sc_xs sc_xm];
    repeat rewrite sh_cA_prove; repeat rewrite sh_cB_prove; repeat rewrite sh_prod_prove; repeat rewrite sh_mexp_prove.

  (** Each challenge of an honest shuffle argument depends only on the
      earlier ones: [x] on nothing, [y] and [z] on [x], [x_h], [y_h], [x_s]
      and [x_m] on [x, y, z], and [x_z] on all but itself and [x_s], [x_m].
      Lemmas [sc_x_indep], [sc_y_indep], [sc_z_indep], [sc_xh_indep],
      [sc_yh_indep], [sc_xs_indep], [sc_xm_indep], [sc_xz_indep]. *)
  Lemma sc_x_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm x' y' z' xh' yh' xz' xs' xm',
    sc_x (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_x (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x' y' z' xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; reflexivity. Qed.

  Lemma sc_y_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm y' z' xh' yh' xz' xs' xm',
    sc_y (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_y (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y' z' xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; reflexivity. Qed.

  Lemma sc_z_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm y' z' xh' yh' xz' xs' xm',
    sc_z (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_z (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y' z' xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; reflexivity. Qed.

  Lemma sc_xh_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm xh' yh' xz' xs' xm',
    sc_xh (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_xh (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; apply product_challenges_indep_xh. Qed.

  Lemma sc_yh_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm xh' yh' xz' xs' xm',
    sc_yh (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_yh (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; apply product_challenges_indep_yh. Qed.

  Lemma sc_xs_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm xh' yh' xz' xs' xm',
    sc_xs (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_xs (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; apply product_challenges_indep_xs. Qed.

  Lemma sc_xm_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm y' z' xh' yh' xz' xs' xm',
    sc_xm (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_xm (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y' z' xh' yh' xz' xs' xm')).
  Proof. intros; sh_components; apply multiexp_challenge_indep. Qed.

  Lemma sc_xz_indep : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm xz' xs' xm',
    sc_xz (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm)) =
    sc_xz (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz' xs' xm')).
  Proof. intros; sh_components; apply product_challenges_indep_xz. Qed.

  (** Eta law for the challenge record. *)
  Lemma schal_eta : forall c : schal, c = mk_schal (sc_x c) (sc_y c) (sc_z c) (sc_xh c) (sc_yh c) (sc_xz c) (sc_xs c) (sc_xm c).
  Proof. destruct c; reflexivity. Qed.

  (** The challenges recomputed by the verifier from an honest shuffle
      argument equal the staged challenges used to produce it. Proof:
      eta-expand the record, substitute the challenges by their definitions
      latest first, and close each field with the corresponding
      independence lemma. *)
  Lemma shuffle_challenges_prove : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2
    d rd dmid s0 sx a0 r0 bs ss τs x y z xh yh xz xs xm,
    let P := fun x y z xh yh xz xs xm =>
      shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
        x y z xh yh xz xs xm in
    let Q := shuffle_challenges O h gs m n Cs Cs' in
    sc_x (Q (P zero zero zero zero zero zero zero zero)) = x ->
    sc_y (Q (P x zero zero zero zero zero zero zero)) = y ->
    sc_z (Q (P x zero zero zero zero zero zero zero)) = z ->
    sc_xh (Q (P x y z zero zero zero zero zero)) = xh ->
    sc_yh (Q (P x y z zero zero zero zero zero)) = yh ->
    sc_xs (Q (P x y z zero zero zero zero zero)) = xs ->
    sc_xm (Q (P x y z zero zero zero zero zero)) = xm ->
    sc_xz (Q (P x y z xh yh zero xs xm)) = xz ->
    Q (P x y z xh yh xz xs xm) = mk_schal x y z xh yh xz xs xm.
  Proof.
    intros O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
      x y z xh yh xz xs xm; cbv zeta; intros h1 h2 h3 h4 h5 h6 h7 h8.
    rewrite (schal_eta (shuffle_challenges _ _ _ _ _ _ _ _)).
    rewrite <- h8, <- h7, <- h6, <- h5, <- h4, <- h3, <- h2, <- h1; cbv beta.
    f_equal; solve [ apply sc_x_indep | apply sc_y_indep | apply sc_z_indep | apply sc_xh_indep
                   | apply sc_yh_indep | apply sc_xz_indep | apply sc_xs_indep | apply sc_xm_indep ].
  Qed.

  (** For [m > 1] the Hadamard challenges of an honest shuffle argument are
      oracle values, hence non-zero under the corresponding oracle
      hypothesis ([shuffle_challenges_xh_nz], [shuffle_challenges_yh_nz]). *)
  Lemma shuffle_challenges_xh_nz : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm,
    (forall cA cb cB, o_xh O cA cb cB <> zero) -> (1 < m)%nat ->
    sc_xh (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx
      a0 r0 bs ss τs x y z xh yh xz xs xm)) <> zero.
  Proof.
    intros * hx hlt. unfold shuffle_challenges, product_challenges, hadamard_challenges, BayerGroth.shuffle_prove, BayerGroth.product_prove;
      cbv zeta. cbn [sh_prod sh_cA sh_cB sc_xh pc_xh]. rewrite chunk_length, (proj2 (PeanoNat.Nat.ltb_lt _ _) hlt).
    cbn [pa_had pa_cb hc_x]. apply hx.
  Qed.

  Lemma shuffle_challenges_yh_nz : forall O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
    x y z xh yh xz xs xm,
    (forall cA cb cB, o_yh O cA cb cB <> zero) -> (1 < m)%nat ->
    sc_yh (shuffle_challenges O h gs m n Cs Cs' (shuffle_prove h gs g pk m n Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx
      a0 r0 bs ss τs x y z xh yh xz xs xm)) <> zero.
  Proof.
    intros * hy hlt. unfold shuffle_challenges, product_challenges, hadamard_challenges, BayerGroth.shuffle_prove, BayerGroth.product_prove;
      cbv zeta. cbn [sh_prod sh_cA sh_cB sc_yh pc_yh]. rewrite chunk_length, (proj2 (PeanoNat.Nat.ltb_lt _ _) hlt).
    cbn [pa_had pa_cb hc_y]. apply hy.
  Qed.

  (** FS completeness of the shuffle argument. Hypotheses: [m ≥ 1],
      [n ≥ 2] equal to the key length, [N = m·n] input and output
      ciphertexts with [C'_i = Enc(1; ρ_i) · C_{π(i)}] for a permutation
      [perm] of [0..N−1], correctly sized prover randomness, and an oracle
      whose Hadamard challenges are never zero. Conclusion: the
      Fiat–Shamir verifier accepts the honest proof. Proof: interactive
      [shuffle_completeness] plus [shuffle_challenges_prove]. *)
  Theorem shuffle_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
    (Cs Cs' : list CT) (perm : list nat) (ρs : list F) (r s : list F)
    (sp : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F) (a0 : list F) (r0 : F) (bs ss τs : list F),
    (1 <= m)%nat -> (2 <= n)%nat -> length Cs = (m * n)%nat -> length Cs' = (m * n)%nat ->
    Permutation perm (seq 0 (m * n)) -> length ρs = (m * n)%nat ->
    (forall i, (i < m * n)%nat ->
      nth i Cs' cone = cmul (encg (gop := gop) (gpow := gpow) (l := l) g pk zero (nth i ρs zero)) (nth (nth i perm 0%nat) Cs cone)) ->
    length r = m -> length s = m -> length smid = (m - 2)%nat -> length t1 = S m -> length t2 = (m - 1)%nat ->
    length d = n -> length dmid = (n - 2)%nat ->
    length bs = (2 * m)%nat -> length ss = (2 * m)%nat -> length τs = (2 * m)%nat ->
    n = length gs -> length a0z = n -> length bmz = n -> length a0 = n ->
    (forall cA cb cB, o_xh O cA cb cB <> zero) -> (forall cA cb cB, o_yh O cA cb cB <> zero) ->
    shuffle_verify_fs O h gs g pk m n Cs Cs'
      (shuffle_prove_fs O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs) = true.
  Proof.
    intros O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx a0 r0 bs ss τs
      hm hn hC hC' hperm hρ hrel hr hs hsmid ht1 ht2 hd hdmid hb hss hτ hng ha0z hbmz ha0 hx hy; unfold shuffle_prove_fs; cbv beta zeta.
    pose proof (shuffle_completeness (Hvec := Hvec) (Fdec := Fdec) (Gdec := Gdec) h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2
      d rd dmid s0 sx a0 r0 bs ss τs) as hsc; cbv zeta in hsc.
    eapply shuffle_verify_fs_of; [| apply hsc; try assumption; intros hlt;
      first [eapply shuffle_challenges_xh_nz; [exact hx | exact hlt] | eapply shuffle_challenges_yh_nz; [exact hy | exact hlt]]].
    apply (shuffle_challenges_prove O h gs g pk m n Cs Cs' perm ρs r s sp smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx
      a0 r0 bs ss τs); reflexivity.
  Qed.

  (** ** The random-oracle step *)

  (** The soundness theorems of [Sigma.BayerGrothSound] are about the
      interactive verifiers; the theorems below carry them to the
      Fiat–Shamir verifiers. *)
  Local Notation binding_break := (binding_break (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation encg := (encg (gop := gop) (gpow := gpow) (l := l)).
  Local Notation fnat := (fnat (zero := zero) (one := one) (add := add)).

  (** Soundness in rewinding form. The prover's proofs form a tree indexed
      by [(jx, jy, jz, p, q, j, j', jm)], one index per choice of each
      challenge from the distinct lists [X, Y, Z, Xh, Yh, Zs p q, XS, XM]
      of the sizes required by the extractor ([|X| = N], [|Y| > 2N²],
      [|Z| > N], [|Xh| = m], [|Yh| = n], [|Zs p q| = 2m+1], [|XS| = n+1],
      [|XM| = 2m]). The announcements of each proof only depend on the
      earlier indices (encoded by the arguments of the functions [cB],
      [pcb], …). If the reprogrammed oracle [O idx] returns the challenges
      of [idx] on the announcements of that proof, and every proof is
      accepted by [shuffle_verify_fs], then either there exist a
      permutation [σ] and randomness [ρs] with
      [C'_i = Enc(1; ρ_i) · C_{σ(i)}], or [binding_break h gs]. Also
      requires that [fnat] be injective on [0..N−1] (characteristic larger
      than [N]). This is the deterministic content of the forking lemma;
      the query-loss analysis is not formalised. Proof: rewrite each
      acceptance with the oracle hypothesis and apply
      [shuffle_soundness]. *)
  Theorem shuffle_fs_soundness : forall (h g : G) (gs : list G) (pk : Vector.t G l) (m : nat) (Cs Cs' : list CT) (cA : list G)
    (X Y Z Xh Yh XS XM : list F) (Zs : nat -> nat -> list F)
    (O : nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> oracles)
    (cB : nat -> list G) (pcb : nat -> nat -> nat -> G) (pcB : nat -> nat -> nat -> list G)
    (zA0 zBm : nat -> nat -> nat -> nat -> nat -> G) (zcd : nat -> nat -> nat -> nat -> nat -> list G)
    (za zb : nat -> nat -> nat -> nat -> nat -> nat -> list F) (zr zt zu : nat -> nat -> nat -> nat -> nat -> nat -> F)
    (scd scδ scΔ : nat -> nat -> nat -> G) (ta tb : nat -> nat -> nat -> nat -> list F) (rt st : nat -> nat -> nat -> nat -> F)
    (mA0 : nat -> G) (mcB : nat -> list G) (mE : nat -> list CT) (ma : nat -> nat -> list F) (mr mb ms mτ : nat -> nat -> F),
    let n := length gs in let N := (m * n)%nat in
    let arg := fun jx jy jz p q j j' jm =>
      mk_shuffle cA (cB jx)
        (mk_prod (pcb jx jy jz)
          (Some (mk_had (pcB jx jy jz) (mk_zero (zA0 jx jy jz p q) (zBm jx jy jz p q) (zcd jx jy jz p q)
            (za jx jy jz p q j) (zb jx jy jz p q j) (zr jx jy jz p q j) (zt jx jy jz p q j) (zu jx jy jz p q j))))
          (mk_svp (scd jx jy jz) (scδ jx jy jz) (scΔ jx jy jz) (ta jx jy jz j') (tb jx jy jz j') (rt jx jy jz j') (st jx jy jz j')))
        (mk_mexp (mA0 jx) (mcB jx) (mE jx) (ma jx jm) (mr jx jm) (mb jx jm) (ms jx jm) (mτ jx jm)) in
    (1 <= m)%nat -> (2 <= n)%nat ->
    (forall i j, (i < N)%nat -> (j < N)%nat -> fnat i = fnat j -> i = j) ->
    NoDup X -> length X = N -> NoDup Y -> (2 * (N * N) < length Y)%nat -> NoDup Z -> (N < length Z)%nat ->
    NoDup Xh -> length Xh = m -> NoDup Yh -> length Yh = n ->
    (forall p q, (p < m)%nat -> (q < n)%nat -> NoDup (Zs p q) /\ length (Zs p q) = (2 * m + 1)%nat) ->
    NoDup XS -> length XS = S n -> NoDup XM -> length XM = (2 * m)%nat ->
    (forall jx jy jz p q j j' jm, (jx < N)%nat -> (jy < length Y)%nat -> (jz < length Z)%nat -> (p < m)%nat -> (q < n)%nat ->
      (j < 2 * m + 1)%nat -> (j' < S n)%nat -> (jm < 2 * m)%nat ->
      shuffle_challenges (O jx jy jz p q j j' jm) h gs m n Cs Cs' (arg jx jy jz p q j j' jm) =
      mk_schal (nth jx X zero) (nth jy Y zero) (nth jz Z zero) (nth p Xh zero) (nth q Yh zero)
        (nth j (Zs p q) zero) (nth j' XS zero) (nth jm XM zero)) ->
    (forall jx jy jz p q j j' jm, (jx < N)%nat -> (jy < length Y)%nat -> (jz < length Z)%nat -> (p < m)%nat -> (q < n)%nat ->
      (j < 2 * m + 1)%nat -> (j' < S n)%nat -> (jm < 2 * m)%nat ->
      shuffle_verify_fs (O jx jy jz p q j j' jm) h gs g pk m n Cs Cs' (arg jx jy jz p q j j' jm) = true) ->
    (exists (σ : list nat) (ρs : list F), Permutation σ (seq 0 N) /\ length ρs = N /\
      forall i, (i < N)%nat -> nth i Cs' cone = cmul (encg g pk zero (nth i ρs zero)) (nth (nth i σ 0%nat) Cs cone))
    \/ binding_break h gs.
  Proof.
    intros * hm hn hinj hXnd hXl hYnd hYl hZnd hZl hXhnd hXhl hYhnd hYhl hZs hSnd hSl hMnd hMl horacle htr.
    apply (shuffle_soundness (Hvec := Hvec) (Fdec := Fdec) (Gdec := Gdec) h g gs pk m Cs Cs' cA X Y Z Xh Yh XS XM Zs cB pcb pcB
      zA0 zBm zcd za zb zr zt zu scd scδ scΔ ta tb rt st mA0 mcB mE ma mr mb ms mτ); try assumption.
    intros jx jy jz p q j j' jm hjx hjy hjz hp hq hj hj' hjm.
    pose proof (htr jx jy jz p q j j' jm hjx hjy hjz hp hq hj hj' hjm) as hv.
    unfold shuffle_verify_fs in hv. rewrite (horacle jx jy jz p q j j' jm hjx hjy hjz hp hq hj hj' hjm) in hv.
    exact hv.
  Qed.

  (** One-query soundness error of the zero argument. Fix the
      announcements and let the responses be any function of the challenge
      [c]. Then either [c_A], [c_B] open to matrices [A], [B] with
      [Σ A_i ⋆_y B_i = 0], or the commitment binding is broken, or the
      probability that the interactive verifier accepts at a uniform
      challenge from [lf] is at most [2·|c_A| / |lf|]. Proof:
      [k_special_soundness_error] with [k = 2|c_A| + 1], then
      [zero_soundness] on the [k] accepting challenges. *)
  Theorem zero_fs_soundness_error : forall (h : G) (gs : list G) (cA cB : list G) (y : F) (cA0 cBm : G) (cd : list G)
    (ra rb : F -> list F) (rr rs rt : F -> F) (lf : list F) (Hlfn : lf <> []),
    (1 <= length gs)%nat -> NoDup lf ->
    (exists (A B : list (list F)) (r s : list F),
      cA = com_list h gs A r /\ cB = com_list h gs B s /\
      length A = length cA /\ length B = length cA /\ length r = length cA /\ length s = length cA /\
      (forall v, In v A -> length v = length gs) /\ (forall v, In v B -> length v = length gs) /\
      fold_right add zero (map (fun p => star (zero := zero) (add := add) (mul := mul) y (fst p) (snd p)) (combine A B)) = zero)
    \/ binding_break h gs
    \/ leq (@prob_of_an_event F (fun c => zero_verify h gs cA cB y c (mk_zero cA0 cBm cd (ra c) (rb c) (rr c) (rs c) (rt c)))
          (uniform_with_replacement lf Hlfn)) (mk_prob (2 * length cA) (Pos.of_nat (length lf))) = true.
  Proof.
    intros * hn hnd.
    (* Either k distinct accepting challenges exist, or the acceptance
       probability is already small. *)
    destruct (k_special_soundness_error
      (fun c => zero_verify h gs cA cB y c (mk_zero cA0 cBm cd (ra c) (rb c) (rr c) (rs c) (rt c))) lf Hlfn (2 * length cA + 1)
      hnd ltac:(lia)) as [(cs & hcl & hcnd & hcs) | hp].
    (* Extract the witness from the k accepting transcripts. *)
    + destruct (zero_soundness (Hvec := Hvec) (Fdec := Fdec) (Gdec := Gdec) h gs cA cB y cA0 cBm cd cs
        (fun j => ra (nth j cs zero)) (fun j => rb (nth j cs zero)) (fun j => rr (nth j cs zero)) (fun j => rs (nth j cs zero))
        (fun j => rt (nth j cs zero)) hn hcnd hcl) as [hw | hbb].
      - intros j hj. destruct (hcs (nth j cs zero) (nth_In cs zero hj)) as (_ & hv). exact hv.
      - left; exact hw.
      - right; left; exact hbb.
    + right; right. replace (2 * length cA)%nat with (2 * length cA + 1 - 1)%nat by lia. exact hp.
  Qed.

  (** One-query soundness error of the SVP argument, with
      [k = |gs| + 1]: either [c_a] opens to [a] with [∏ a_i = b], or the
      binding is broken, or the acceptance probability is at most
      [|gs| / |lf|]. From [svp_soundness]. *)
  Theorem svp_fs_soundness_error : forall (h : G) (gs : list G) (ca : G) (b : F) (cd cδ cΔ : G)
    (ra rb : F -> list F) (rr rs : F -> F) (lf : list F) (Hlfn : lf <> []),
    (2 <= length gs)%nat -> NoDup lf ->
    (exists (a : list F) (r : F), ca = com h gs a r /\ length a = length gs /\ fold_right mul one a = b)
    \/ binding_break h gs
    \/ leq (@prob_of_an_event F (fun c => svp_verify h gs ca b c (mk_svp cd cδ cΔ (ra c) (rb c) (rr c) (rs c)))
          (uniform_with_replacement lf Hlfn)) (mk_prob (length gs) (Pos.of_nat (length lf))) = true.
  Proof.
    intros * hn hnd.
    destruct (k_special_soundness_error
      (fun c => svp_verify h gs ca b c (mk_svp cd cδ cΔ (ra c) (rb c) (rr c) (rs c))) lf Hlfn (S (length gs))
      hnd ltac:(lia)) as [(cs & hcl & hcnd & hcs) | hp].
    + destruct (svp_soundness (Hvec := Hvec) (Fdec := Fdec) (Gdec := Gdec) h gs ca b cd cδ cΔ cs
        (fun j => ra (nth j cs zero)) (fun j => rb (nth j cs zero)) (fun j => rr (nth j cs zero)) (fun j => rs (nth j cs zero))
        hn hcnd hcl) as [hw | hbb].
      - intros j hj. destruct (hcs (nth j cs zero) (nth_In cs zero hj)) as (_ & hv). exact hv.
      - left; exact hw.
      - right; left; exact hbb.
    + right; right. replace (length gs) with (S (length gs) - 1)%nat by lia. exact hp.
  Qed.

  (** One-query soundness error of the multi-exponentiation argument, with
      [k = 2|c_A|]: either [c_A] opens to [A] and [C] is
      [Enc(1; ρ) · ∏ C_i^{a_i}] for some [ρ], or the binding is broken, or
      the acceptance probability is at most [(2|c_A| − 1) / |lf|]. From
      [multiexp_soundness]. *)
  Theorem multiexp_fs_soundness_error : forall (h g : G) (gs : list G) (pk : Vector.t G l) (Cs : list (list CT)) (C : CT)
    (cA : list G) (cA0 : G) (cB : list G) (E : list CT) (ra : F -> list F) (rr rb rs rτ : F -> F) (lf : list F) (Hlfn : lf <> []),
    (1 <= length gs)%nat -> (1 <= length cA)%nat -> NoDup lf ->
    (exists (A : list (list F)) (r : list F) (ρ : F),
      cA = com_list h gs A r /\ length A = length cA /\ length r = length cA /\
      (forall v, In v A -> length v = length gs) /\
      C = cmul (encg g pk zero ρ) (cprod (map (fun p => cmexp (snd p) (nth (fst p) A [])) (combine (seq 0 (length cA)) Cs))))
    \/ binding_break h gs
    \/ leq (@prob_of_an_event F (fun c => multiexp_verify h gs g pk Cs C cA c (mk_mexp cA0 cB E (ra c) (rr c) (rb c) (rs c) (rτ c)))
          (uniform_with_replacement lf Hlfn)) (mk_prob (2 * length cA - 1) (Pos.of_nat (length lf))) = true.
  Proof.
    intros * hn hm hnd.
    destruct (k_special_soundness_error
      (fun c => multiexp_verify h gs g pk Cs C cA c (mk_mexp cA0 cB E (ra c) (rr c) (rb c) (rs c) (rτ c))) lf Hlfn (2 * length cA)
      hnd ltac:(lia)) as [(cs & hcl & hcnd & hcs) | hp].
    + destruct (multiexp_soundness (Hvec := Hvec) (Fdec := Fdec) (Gdec := Gdec) h g gs pk Cs C cA cA0 cB E cs
        (fun j => ra (nth j cs zero)) (fun j => rr (nth j cs zero)) (fun j => rb (nth j cs zero)) (fun j => rs (nth j cs zero))
        (fun j => rτ (nth j cs zero)) hn hm hcnd hcl) as [hw | hbb].
      - intros j hj. destruct (hcs (nth j cs zero) (nth_In cs zero hj)) as (_ & hv). exact hv.
      - left; exact hw.
      - right; left; exact hbb.
    + right; right. exact hp.
  Qed.

End BayerGrothVerifier.
