(* Fiat–Shamir verification of Bayer–Groth shuffle arguments in the format of
   the Swiss Post e-voting system (crypto-primitives specification 1.6.0:
   Algorithms 9.12 VerifyShuffleArgument, 9.16, 9.19, 9.21, 9.23, 9.26 for
   the sub-arguments), linked to the interactive verifiers of
   Crypto/BayerGroth.v.

   The interactive verifiers take the challenges as arguments. The Swiss Post
   verifier computes them with RecursiveHash (SHA3-256, Section 3) over the
   group parameters p, q, the public key pk, the commitment key ck, the
   statement and the announcements of the argument, in a fixed order. This
   file receives these hash functions as an oracle record whose fields are
   closures over the group parameters and the statement, supplied by the
   driver (Executable/Bgverifier); each field takes the announcements in the
   order in which the specification hashes them:

     x  = H(p, q, pk, ck, C, C', c_A)                          o_x c_A
     y  = H(c_B, p, q, pk, ck, C, C', c_A)                     o_y c_A c_B
     z  = H("1", c_B, p, q, pk, ck, C, C', c_A)                o_z c_A c_B
     Hadamard:   x = H(p, q, pk, ck, c_A, c_b, c_B)            o_xh c_A c_b c_B
                 y = H("1", p, q, pk, ck, c_A, c_b, c_B)       o_yh c_A c_b c_B
     zero:       x = H(p, q, pk, ck, c_A0, c_Bm, c_d, c_B, c_A)  o_xz c_A0 c_Bm c_d c_B c_A
     single value product:
                 x = H(p, q, pk, ck, c_Δ, c_δ, c_d, b, c_a)    o_xs c_Δ c_δ c_d b c_a
     multi-exponentiation:
                 x = H(p, q, pk, ck, C_matrix, C, c_A, c_A0, c_B, E)
                                                               o_xm C_matrix C c_A c_A0 c_B E

   The statements of the sub-arguments (the product argument inside the
   shuffle argument, the zero argument inside the Hadamard argument, the
   single value product argument for m = 1 and m > 1) are recomputed here
   exactly as the interactive verifiers compute them, so that each
   Fiat–Shamir verifier is by definition the interactive verifier at the
   oracle's challenges (the *_verify_fs_spec theorems). The honest provers
   are made non-interactive the same way (the *_prove_fs functions): they query the
   oracle on their announcements stage by stage, and *_fs_completeness
   states that the Fiat–Shamir verifier accepts their arguments, from the
   completeness theorems of the interactive arguments. As everywhere in this
   development the security theorems are about the interactive protocols. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool List Permutation PArith setoid_ring.Field.
From Stdlib Require Import PeanoNat.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma MultiExp OkamotoRows SigmaK BayerGroth BayerGrothSound.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import ListNotations.

Section BayerGrothVerifier.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}.

  (* ciphertexts with l message components *)
  Context {l : nat}.
  Local Notation CT := (Vector.t G (S l)).
  Local Notation cone := (vec_id (V := G) (vid := gid) (S l)).
  Local Notation cmul := (vec_add (vadd := gop) (n := S l)).
  Local Notation cpow := (vec_smul (smul := gpow) (n := S l)).
  Local Notation cmexp := (lmexp (vid := cone) (vadd := cmul) (smul := cpow)).
  Local Notation cprod := (fold_right cmul cone).

  (* the argument records *)
  Local Notation svp_argument := (@svp_argument F G).
  Local Notation zero_argument := (@zero_argument F G).
  Local Notation hadamard_argument := (@hadamard_argument F G).
  Local Notation multiexp_argument := (@multiexp_argument F G l).
  Local Notation product_argument := (@product_argument F G).
  Local Notation shuffle_argument := (@shuffle_argument F G l).

  (* the definitions of Crypto/BayerGroth.v at the operations of the context *)
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

  (* ---- the random oracles ---- *)

  Record oracles : Type := mk_oracles {
    o_x : list G -> F;
    o_y : list G -> list G -> F;
    o_z : list G -> list G -> F;
    o_xh : list G -> G -> list G -> F;
    o_yh : list G -> G -> list G -> F;
    o_xz : G -> G -> list G -> list G -> list G -> F;
    o_xs : G -> G -> G -> F -> G -> F;
    o_xm : list (list CT) -> CT -> list G -> G -> list G -> list CT -> F }.

  (* ---- single value product argument (Algorithms 9.25, 9.26) ---- *)

  Definition svp_challenge (O : oracles) (ca : G) (b : F) (arg : svp_argument) : F :=
    o_xs O (svp_cDelta arg) (svp_cdelta arg) (svp_cd arg) b ca.

  Definition svp_verify_fs (O : oracles) (h : G) (gs : list G) (ca : G) (b : F) (arg : svp_argument) : bool :=
    svp_verify h gs ca b (svp_challenge O ca b arg) arg.

  Theorem svp_verify_fs_spec : forall O h gs ca b arg,
    svp_verify_fs O h gs ca b arg = svp_verify h gs ca b (svp_challenge O ca b arg) arg.
  Proof. reflexivity. Qed.

  Lemma svp_verify_fs_of : forall O h gs ca b arg x,
    svp_challenge O ca b arg = x -> svp_verify h gs ca b x arg = true -> svp_verify_fs O h gs ca b arg = true.
  Proof. intros * <- hv; exact hv. Qed.

  (* the honest prover: the announcements c_d, c_δ, c_Δ do not depend on the
    challenge, so they are computed once (with challenge 0) and hashed *)
  Definition svp_prove_fs (O : oracles) (h : G) (gs : list G) (a : list F) (r : F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F) : svp_argument :=
    let ca := com h gs a r in
    let b := fold_right mul one a in
    let arg0 := svp_prove h gs a r d rd dmid s0 sx zero in
    svp_prove h gs a r d rd dmid s0 sx (svp_challenge O ca b arg0).

  Theorem svp_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (a : list F) (r : F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F),
    (2 <= length a)%nat -> length d = length a -> length dmid = (length a - 2)%nat -> length a = length gs ->
    svp_verify_fs O h gs (com h gs a r) (fold_right mul one a) (svp_prove_fs O h gs a r d rd dmid s0 sx) = true.
  Proof.
    intros; unfold svp_prove_fs; cbv zeta.
    eapply svp_verify_fs_of; [| apply (svp_completeness (Hvec := Hvec)); assumption].
    reflexivity.
  Qed.

  (* ---- zero argument (Algorithms 9.22, 9.23) ---- *)

  Definition zero_challenge (O : oracles) (cA cB : list G) (arg : zero_argument) : F :=
    o_xz O (za_cA0 arg) (za_cBm arg) (za_cd arg) cB cA.

  Definition zero_verify_fs (O : oracles) (h : G) (gs : list G) (cA cB : list G) (y : F)
    (arg : zero_argument) : bool :=
    zero_verify h gs cA cB y (zero_challenge O cA cB arg) arg.

  Theorem zero_verify_fs_spec : forall O h gs cA cB y arg,
    zero_verify_fs O h gs cA cB y arg = zero_verify h gs cA cB y (zero_challenge O cA cB arg) arg.
  Proof. reflexivity. Qed.

  Lemma zero_verify_fs_of : forall O h gs cA cB y arg x,
    zero_challenge O cA cB arg = x -> zero_verify h gs cA cB y x arg = true -> zero_verify_fs O h gs cA cB y arg = true.
  Proof. intros * <- hv; exact hv. Qed.

  Definition zero_prove_fs (O : oracles) (h : G) (gs : list G) (A B : list (list F)) (r s : list F) (y : F)
    (a0 bm : list F) (r0 sm : F) (t1 t2 : list F) : zero_argument :=
    let cA := com_list h gs A r in
    let cB := com_list h gs B s in
    let arg0 := zero_prove h gs A B r s y a0 bm r0 sm t1 t2 zero in
    zero_prove h gs A B r s y a0 bm r0 sm t1 t2 (zero_challenge O cA cB arg0).

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

  (* ---- Hadamard argument (Algorithms 9.20, 9.21) ---- *)

  Record hchal : Type := mk_hchal { hc_x : F; hc_y : F; hc_xz : F }.

  (* x and y from the statement and c_B; the zero argument's challenge from
    the zero statement that the verifier derives from them *)
  Definition hadamard_challenges (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (cb : G)
    (arg : hadamard_argument) : hchal :=
    let cB := ha_cB arg in
    let x := o_xh O cA cb cB in
    let y := o_yh O cA cb cB in
    let st := hadamard_zero_stmt h gs n cA cB x in
    mk_hchal x y (zero_challenge O (fst st) (snd st) (ha_zero arg)).

  Definition hadamard_verify_fs (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (cb : G)
    (arg : hadamard_argument) : bool :=
    let c := hadamard_challenges O h gs n cA cb arg in
    hadamard_verify h gs n cA cb (hc_x c) (hc_y c) (hc_xz c) arg.

  Theorem hadamard_verify_fs_spec : forall O h gs n cA cb arg,
    hadamard_verify_fs O h gs n cA cb arg =
    hadamard_verify h gs n cA cb (hc_x (hadamard_challenges O h gs n cA cb arg))
      (hc_y (hadamard_challenges O h gs n cA cb arg)) (hc_xz (hadamard_challenges O h gs n cA cb arg)) arg.
  Proof. reflexivity. Qed.

  Lemma hadamard_verify_fs_of : forall O h gs n cA cb arg x y xz,
    hadamard_challenges O h gs n cA cb arg = mk_hchal x y xz ->
    hadamard_verify h gs n cA cb x y xz arg = true -> hadamard_verify_fs O h gs n cA cb arg = true.
  Proof. intros * hc hv; unfold hadamard_verify_fs; rewrite hc; exact hv. Qed.

  (* the honest prover: c_B first (independent of the challenges), then the
    zero argument's announcements (they depend on x and y) *)
  Definition hadamard_prove_fs (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F))
    (r : list F) (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F) : hadamard_argument :=
    let cA := com_list h gs A r in
    let cb := com h gs (hprefix A (length A - 1)) s in
    let P := fun x y xz => hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 xz in
    let c0 := hadamard_challenges O h gs n cA cb (P zero zero zero) in
    let c1 := hadamard_challenges O h gs n cA cb (P (hc_x c0) (hc_y c0) zero) in
    P (hc_x c0) (hc_y c0) (hc_xz c1).

  Lemma hadamard_challenges_prove : forall O h gs n A r s smid a0z bmz r0z smz t1 t2 cA cb x y xz,
    hc_x (hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid zero zero a0z bmz r0z smz t1 t2 zero)) = x ->
    hc_y (hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid zero zero a0z bmz r0z smz t1 t2 zero)) = y ->
    hc_xz (hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 zero)) = xz ->
    hadamard_challenges O h gs n cA cb (hadamard_prove h gs n A r s smid x y a0z bmz r0z smz t1 t2 xz) = mk_hchal x y xz.
  Proof. intros; subst; reflexivity. Qed.

  Theorem hadamard_fs_completeness : forall (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F))
    (r : list F) (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F),
    (2 <= length A)%nat -> Forall (fun a => length a = n) A -> length r = length A ->
    length smid = (length A - 2)%nat -> length t1 = S (length A) -> length t2 = (length A - 1)%nat ->
    n = length gs -> length a0z = length gs -> length bmz = length gs ->
    (* an oracle whose Hadamard challenges are never zero *)
    (forall cA cb cB, o_xh O cA cb cB <> zero) -> (forall cA cb cB, o_yh O cA cb cB <> zero) ->
    hadamard_verify_fs O h gs n (com_list h gs A r) (com h gs (hprefix A (length A - 1)) s)
      (hadamard_prove_fs O h gs n A r s smid a0z bmz r0z smz t1 t2) = true.
  Proof.
    intros O h gs n A r s smid a0z bmz r0z smz t1 t2 hm hA hr hsmid ht1 ht2 hng ha0z hbmz hx hy; unfold hadamard_prove_fs; cbv beta zeta.
    eapply hadamard_verify_fs_of; [| apply (hadamard_completeness (Hvec := Hvec)); try assumption;
      unfold hadamard_challenges; cbn [hc_x hc_y]; first [apply hx | apply hy]].
    apply hadamard_challenges_prove; reflexivity.
  Qed.

  (* ---- multi-exponentiation argument (Algorithms 9.15, 9.16) ---- *)

  Definition multiexp_challenge (O : oracles) (Cs : list (list CT)) (C : CT) (cA : list G)
    (arg : multiexp_argument) : F :=
    o_xm O Cs C cA (me_cA0 arg) (me_cB arg) (me_E arg).

  Definition multiexp_verify_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
    (Cs : list (list CT)) (C : CT) (cA : list G) (arg : multiexp_argument) : bool :=
    multiexp_verify h gs g pk Cs C cA (multiexp_challenge O Cs C cA arg) arg.

  Theorem multiexp_verify_fs_spec : forall O h gs g pk Cs C cA arg,
    multiexp_verify_fs O h gs g pk Cs C cA arg = multiexp_verify h gs g pk Cs C cA (multiexp_challenge O Cs C cA arg) arg.
  Proof. reflexivity. Qed.

  Lemma multiexp_verify_fs_of : forall O h gs g pk Cs C cA arg x,
    multiexp_challenge O Cs C cA arg = x -> multiexp_verify h gs g pk Cs C cA x arg = true ->
    multiexp_verify_fs O h gs g pk Cs C cA arg = true.
  Proof. intros * <- hv; exact hv. Qed.

  (* the ciphertext C = Enc(1; ρ) ∏_i C_i^{a_i} of the honest statement *)
  Definition multiexp_C (g : G) (pk : Vector.t G l) (Cs : list (list CT)) (A : list (list F)) (ρ : F) : CT :=
    cmul (enc g pk (Vector.const gid l) ρ)
      (cprod (map (fun p => cmexp (snd p) (nth (fst p) A [])) (combine (seq 0 (length A)) Cs))).

  Definition multiexp_prove_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l)
    (Cs : list (list CT)) (A : list (list F)) (r : list F) (ρ : F) (a0 : list F) (r0 : F)
    (bs ss τs : list F) : multiexp_argument :=
    let cA := com_list h gs A r in
    let C := multiexp_C g pk Cs A ρ in
    let arg0 := multiexp_prove h gs g pk Cs A r ρ a0 r0 bs ss τs zero in
    multiexp_prove h gs g pk Cs A r ρ a0 r0 bs ss τs (multiexp_challenge O Cs C cA arg0).

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

  (* ---- product argument (Algorithms 9.18, 9.19) ---- *)

  Record pchal : Type := mk_pchal { pc_xh : F; pc_yh : F; pc_xz : F; pc_xs : F }.

  (* for m > 1 the Hadamard argument on (c_A, c_b) and the single value
    product argument on (c_b, b); for m = 1 only the latter, on (c_{A1}, b) *)
  Definition product_challenges (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (b : F)
    (arg : product_argument) : pchal :=
    let m := length cA in
    let hc := match pa_had arg with
      | Some had => hadamard_challenges O h gs n cA (pa_cb arg) had
      | None => mk_hchal zero zero zero
      end in
    let ca := if Nat.ltb 1 m then pa_cb arg else nth 0 cA gid in
    mk_pchal (hc_x hc) (hc_y hc) (hc_xz hc) (svp_challenge O ca b (pa_svp arg)).

  Definition product_verify_fs (O : oracles) (h : G) (gs : list G) (n : nat) (cA : list G) (b : F)
    (arg : product_argument) : bool :=
    let c := product_challenges O h gs n cA b arg in
    product_verify h gs n cA b (pc_xh c) (pc_yh c) (pc_xz c) (pc_xs c) arg.

  Theorem product_verify_fs_spec : forall O h gs n cA b arg,
    product_verify_fs O h gs n cA b arg =
    product_verify h gs n cA b (pc_xh (product_challenges O h gs n cA b arg)) (pc_yh (product_challenges O h gs n cA b arg))
      (pc_xz (product_challenges O h gs n cA b arg)) (pc_xs (product_challenges O h gs n cA b arg)) arg.
  Proof. reflexivity. Qed.

  Lemma product_verify_fs_of : forall O h gs n cA b arg xh yh xz xs,
    product_challenges O h gs n cA b arg = mk_pchal xh yh xz xs ->
    product_verify h gs n cA b xh yh xz xs arg = true -> product_verify_fs O h gs n cA b arg = true.
  Proof. intros * hc hv; unfold product_verify_fs; rewrite hc; exact hv. Qed.

  Definition product_prove_fs (O : oracles) (h : G) (gs : list G) (n : nat) (A : list (list F)) (r : list F)
    (s : F) (smid : list F) (a0z bmz : list F) (r0z smz : F) (t1 t2 : list F)
    (d : list F) (rd : F) (dmid : list F) (s0 sx : F) : product_argument :=
    let cA := com_list h gs A r in
    let b := fold_right mul one (hprefix A (length A - 1)) in
    let P := fun xh yh xz xs => product_prove h gs n A r s smid a0z bmz r0z smz t1 t2 d rd dmid s0 sx xh yh xz xs in
    let c0 := product_challenges O h gs n cA b (P zero zero zero zero) in
    let c1 := product_challenges O h gs n cA b (P (pc_xh c0) (pc_yh c0) zero zero) in
    P (pc_xh c0) (pc_yh c0) (pc_xz c1) (pc_xs c0).

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

  (* for m > 1 the Hadamard challenges of the product argument are oracle values *)
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

  (* ---- shuffle argument (Algorithms 9.11, 9.12) ---- *)

  Record schal : Type := mk_schal {
    sc_x : F; sc_y : F; sc_z : F; sc_xh : F; sc_yh : F; sc_xz : F; sc_xs : F; sc_xm : F }.

  (* x from c_A; y, z from c_A and c_B; the product argument's challenges on
    the statement (c_D c_{−z}, ∏(y i + x^i − z)); the multi-exponentiation
    argument's challenge on (C' as an m × n matrix, ∏ C_i^{x^i}, c_B) *)
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

  Definition shuffle_verify_fs (O : oracles) (h : G) (gs : list G) (g : G) (pk : Vector.t G l) (m n : nat)
    (Cs Cs' : list CT) (arg : shuffle_argument) : bool :=
    let c := shuffle_challenges O h gs m n Cs Cs' arg in
    shuffle_verify h gs g pk m n Cs Cs' (sc_x c) (sc_y c) (sc_z c) (sc_xh c) (sc_yh c) (sc_xz c) (sc_xs c) (sc_xm c) arg.

  Theorem shuffle_verify_fs_spec : forall O h gs g pk m n Cs Cs' arg,
    shuffle_verify_fs O h gs g pk m n Cs Cs' arg =
    let c := shuffle_challenges O h gs m n Cs Cs' arg in
    shuffle_verify h gs g pk m n Cs Cs' (sc_x c) (sc_y c) (sc_z c) (sc_xh c) (sc_yh c) (sc_xz c) (sc_xs c) (sc_xm c) arg.
  Proof. reflexivity. Qed.

  Lemma shuffle_verify_fs_of : forall O h gs g pk m n Cs Cs' arg x y z xh yh xz xs xm,
    shuffle_challenges O h gs m n Cs Cs' arg = mk_schal x y z xh yh xz xs xm ->
    shuffle_verify h gs g pk m n Cs Cs' x y z xh yh xz xs xm arg = true ->
    shuffle_verify_fs O h gs g pk m n Cs Cs' arg = true.
  Proof. intros * hc hv; unfold shuffle_verify_fs; rewrite hc; exact hv. Qed.

  (* the honest prover, stage by stage: c_A gives x; c_B (which depends on x)
    gives y and z; the product statement and the announcements c_b, c_B of
    the Hadamard argument give its challenges, the single value product and
    multi-exponentiation announcements theirs; finally the zero argument's
    announcements (which depend on the Hadamard challenges) give xz *)
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

  (* the announcements of the honest provers do not depend on the challenges
    that come after them *)
  Lemma svp_challenge_indep : forall O ca b h gs a r d rd dmid s0 sx x x',
    svp_challenge O ca b (svp_prove h gs a r d rd dmid s0 sx x) = svp_challenge O ca b (svp_prove h gs a r d rd dmid s0 sx x').
  Proof. reflexivity. Qed.

  Lemma multiexp_challenge_indep : forall O Cs C cA h gs g pk Ms A r ρ a0 r0 bs ss τs x x',
    multiexp_challenge O Cs C cA (multiexp_prove h gs g pk Ms A r ρ a0 r0 bs ss τs x) =
    multiexp_challenge O Cs C cA (multiexp_prove h gs g pk Ms A r ρ a0 r0 bs ss τs x').
  Proof. reflexivity. Qed.

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

  (* the components of the honest shuffle argument *)
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

  Local Ltac sh_components :=
    unfold shuffle_challenges; cbv zeta; cbn [sc_x sc_y sc_z sc_xh sc_yh sc_xz sc_xs sc_xm];
    repeat rewrite sh_cA_prove; repeat rewrite sh_cB_prove; repeat rewrite sh_prod_prove; repeat rewrite sh_mexp_prove.

  (* each challenge of the shuffle argument depends only on the earlier ones *)
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

  Lemma schal_eta : forall c : schal, c = mk_schal (sc_x c) (sc_y c) (sc_z c) (sc_xh c) (sc_yh c) (sc_xz c) (sc_xs c) (sc_xm c).
  Proof. destruct c; reflexivity. Qed.

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
    (* substitute the challenges by their definitions, latest first *)
    rewrite <- h8, <- h7, <- h6, <- h5, <- h4, <- h3, <- h2, <- h1; cbv beta.
    f_equal; solve [ apply sc_x_indep | apply sc_y_indep | apply sc_z_indep | apply sc_xh_indep
                   | apply sc_yh_indep | apply sc_xz_indep | apply sc_xs_indep | apply sc_xm_indep ].
  Qed.

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

  (* ---------------------------------------------------------------- *)
  (* the random-oracle step                                           *)
  (* ---------------------------------------------------------------- *)

  (* The soundness theorems of Crypto/BayerGrothSound.v are about the
     interactive verifiers. Two statements carry them to the Fiat–Shamir
     verifier. The rewinding form: a prover whose proofs are accepted by the
     Fiat–Shamir verifier under every reprogramming of the oracle tree (the
     oracle at index (jx, jy, jz, p, q, j, j', jm), evaluated on the
     announcements of that proof, returns the challenges of that index;
     announcements depend only on the earlier answers) either breaks the
     binding of the commitment key or knows the shuffle witness — the
     deterministic content of the forking argument, whose probabilistic
     analysis (the loss in the number of oracle queries) is not formalised.
     The one-query form, for the single-challenge arguments: a prover who
     fixes announcements and answers the oracle's value c with resp c is
     accepted with probability at most (k − 1)/|lf| over a uniform oracle
     value, unless the k-special-soundness extractor applies. *)

  Local Notation binding_break := (binding_break (gid := gid) (gop := gop) (gpow := gpow)).
  Local Notation encg := (encg (gop := gop) (gpow := gpow) (l := l)).
  Local Notation fnat := (fnat (zero := zero) (one := one) (add := add)).

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
    (* the reprogrammed oracles return the challenges of the index on the announcements of its proof *)
    (forall jx jy jz p q j j' jm, (jx < N)%nat -> (jy < length Y)%nat -> (jz < length Z)%nat -> (p < m)%nat -> (q < n)%nat ->
      (j < 2 * m + 1)%nat -> (j' < S n)%nat -> (jm < 2 * m)%nat ->
      shuffle_challenges (O jx jy jz p q j j' jm) h gs m n Cs Cs' (arg jx jy jz p q j j' jm) =
      mk_schal (nth jx X zero) (nth jy Y zero) (nth jz Z zero) (nth p Xh zero) (nth q Yh zero)
        (nth j (Zs p q) zero) (nth j' XS zero) (nth jm XM zero)) ->
    (* every proof of the tree is accepted by the Fiat–Shamir verifier *)
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

  (* one-query bounds for the single-challenge arguments: a prover strategy
     (announcements fixed, responses resp c to the oracle's value c) *)
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
    destruct (k_special_soundness_error
      (fun c => zero_verify h gs cA cB y c (mk_zero cA0 cBm cd (ra c) (rb c) (rr c) (rs c) (rt c))) lf Hlfn (2 * length cA + 1)
      hnd ltac:(lia)) as [(cs & hcl & hcnd & hcs) | hp].
    + destruct (zero_soundness (Hvec := Hvec) (Fdec := Fdec) (Gdec := Gdec) h gs cA cB y cA0 cBm cd cs
        (fun j => ra (nth j cs zero)) (fun j => rb (nth j cs zero)) (fun j => rr (nth j cs zero)) (fun j => rs (nth j cs zero))
        (fun j => rt (nth j cs zero)) hn hcnd hcl) as [hw | hbb].
      - intros j hj. destruct (hcs (nth j cs zero) (nth_In cs zero hj)) as (_ & hv). exact hv.
      - left; exact hw.
      - right; left; exact hbb.
    + right; right. replace (2 * length cA)%nat with (2 * length cA + 1 - 1)%nat by lia. exact hp.
  Qed.

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
