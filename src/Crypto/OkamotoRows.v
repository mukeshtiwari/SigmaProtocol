(* Multi-base statements in product spaces: several linear equations
   T_j = ∏_i B_j[i]^{w_i} over one witness vector w, verified with one
   challenge and one response vector, are a single instance of the
   generalised Okamoto protocol (Crypto/Okamoto.v) in the product space G^m
   (Algebra/Vector_product_space.v), one component per equation. This is
   the shape of the presentation proofs of anonymous credentials: U-Prove
   with a pseudonym and attribute commitments (Crypto/UProve.v), and the
   validity proof of BBS# (Crypto/BBSSharp.v). The file has the transpose
   from rows to Okamoto bases, the componentwise reconstruction of the
   announcement as a Fiat–Shamir verifier computes it, the completeness,
   special soundness and honest-verifier zero-knowledge instances, rows
   with a single base, the Chaum–Pedersen reconstruction used by the
   discrete-logarithm-equality proofs, and the group facts the credential
   files share. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

Section OkamotoRows.

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
  Local Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).
  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).

  (* the group and vector-space laws of G as explicit terms *)
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
  Local Notation gfadd := (@vector_space_smul_distributive_fadd F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation gfmul := (@vector_space_smul_associative_fmul F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation gvadd := (@vector_space_smul_distributive_vadd F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation gone := (@vector_space_field_one F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation gzero := (@vector_space_field_zero F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).


  (* the vector-space laws as plain lemmas (rewriting with the unapplied class
    projections does not terminate) *)
  Lemma gpow_add : forall (g : G) (r s : F), g ^ (add r s) = gop (g ^ r) (g ^ s).
  Proof. intros; apply gfadd. Qed.
  Lemma gpow_mul : forall (g : G) (r s : F), g ^ (mul r s) = (g ^ r) ^ s.
  Proof. intros; apply gfmul. Qed.
  Lemma gop_pow : forall (a b : G) (r : F), (gop a b) ^ r = gop (a ^ r) (b ^ r).
  Proof. intros; apply gvadd. Qed.
  Lemma gpow_one : forall g : G, g ^ one = g.
  Proof. intros; apply gone. Qed.
  Lemma gpow_zero : forall g : G, g ^ zero = gid.
  Proof. intros; apply gzero. Qed.

  (* ---------------------------------------------------------------- *)
  (* Group facts                                                       *)
  (* ---------------------------------------------------------------- *)

  Lemma inv_unique : forall x y : G, gop x y = gid -> ginv x = y.
  Proof.
    intros x y h.
    rewrite <-(gid_r (ginv x)), <-h, gassoc, ginv_l, gid_l; reflexivity.
  Qed.

  Lemma ginv_gop : forall a b : G, ginv (gop a b) = gop (ginv a) (ginv b).
  Proof.
    intros a b; apply inv_unique.
    rewrite (gcomm (ginv a) (ginv b)), gassoc, <-(gassoc a b (ginv b)), (ginv_r b),
      (gid_r a), (ginv_r a); reflexivity.
  Qed.

  Lemma ginv_gid : ginv gid = gid.
  Proof. apply inv_unique; apply gid_l. Qed.

  Lemma pow_opp : forall (g : G) (r : F), g ^ (opp r) = ginv (g ^ r).
  Proof.
    intros g r; symmetry; apply inv_unique.
    rewrite <-(gpow_add g r (opp r)).
    assert (h : add r (opp r) = zero) by field.
    rewrite h; apply gpow_zero.
  Qed.

  Lemma gop4 : forall a b c d : G, gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
  Proof.
    intros a b c d.
    rewrite <-(gassoc a b (gop c d)), (gassoc b c d), (gcomm b c), <-(gassoc c b d),
      (gassoc a c (gop b d)); reflexivity.
  Qed.

  Lemma mexp_map_opp : forall (k : nat) (gs : Vector.t G k) (xs : Vector.t F k),
    gexp gs (Vector.map opp xs) = ginv (gexp gs xs).
  Proof.
    induction k as [| k ih]; intros gs xs.
    + rewrite (vector_inv_0 gs), (vector_inv_0 xs); cbn [Vector.map].
      rewrite !mexp_nil, ginv_gid; reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      cbn [Vector.map]; rewrite !mexp_cons, ih, pow_opp, ginv_gop; reflexivity.
  Qed.

  Lemma mexp_map2_gop : forall (k : nat) (v w : Vector.t G k) (xs : Vector.t F k),
    gexp (Vector.map2 gop v w) xs = gop (gexp v xs) (gexp w xs).
  Proof.
    induction k as [| k ih]; intros v w xs.
    + rewrite (vector_inv_0 v), (vector_inv_0 w), (vector_inv_0 xs).
      rewrite !mexp_nil, gid_l; reflexivity.
    + destruct (vector_inv_S v) as (a & v' & ->).
      destruct (vector_inv_S w) as (b & w' & ->).
      destruct (vector_inv_S xs) as (x & xs' & ->).
      rewrite map2_cons, !mexp_cons, ih, gop_pow, gop4; reflexivity.
  Qed.


  (* ---------------------------------------------------------------- *)
  (* Chaum–Pedersen reconstruction                                      *)
  (* ---------------------------------------------------------------- *)

  (* The statement c₁ = g^y ∧ c₂ = h^y with the published response ρ and
    challenge c (response convention ρ = ω + c·y): the verifier
    reconstructs the announcement (g^ρ c₁^{−c}, h^ρ c₂^{−c}), which with
    challenge c is an accepting Chaum–Pedersen transcript. Used for the
    Issuer's signature of U-Prove (Figure 4 of its spec) and for the
    discrete-logarithm-equality proof of BBS#. *)
  Definition cp_reconstruct (g c1 h c2 : G) (c ρ : F) : Vector.t G 2 :=
    [gop (g ^ ρ) (c1 ^ (opp c)); gop (h ^ ρ) (c2 ^ (opp c))].

  Definition cp_transcript (g c1 h c2 : G) (c ρ : F) : @sigma_proto F G 2 1 1 :=
    (cp_reconstruct g c1 h c2 c ρ; [c]; [ρ]).

  Definition cp_verify (g c1 h c2 : G) (t : @sigma_proto F G 2 1 1) : bool :=
    generalised_cp_accepting_conversations (gop := gop) (gpow := gpow) (Gdec := Gdec) g h c1 c2 t.

  Theorem cp_reconstruct_accepting : forall (g c1 h c2 : G) (c ρ : F),
    cp_verify g c1 h c2 (cp_transcript g c1 h c2 c ρ) = true.
  Proof.
    intros *; unfold cp_verify, cp_transcript, cp_reconstruct.
    apply generalised_cp_accepting_conversations_accept_backward;
    rewrite <-gassoc, pow_opp, ginv_l, gid_r; reflexivity.
  Qed.

  Theorem cp_special_soundness : forall (g c1 h c2 : G) (a : Vector.t G 2) (ca ra cb rb : F),
    ca <> cb ->
    cp_verify g c1 h c2 (a; [ca]; [ra]) = true ->
    cp_verify g c1 h c2 (a; [cb]; [rb]) = true ->
    exists y : F, g ^ y = c1 /\ h ^ y = c2.
  Proof.
    intros * hc h1 h2.
    destruct (generalise_cp_sigma_soundness g h c1 c2 a ca cb ra rb h1 h2 hc) as (y & hy).
    exists y; split; [exact (hy Fin.F1) | exact (hy (Fin.FS Fin.F1))].
  Qed.

  Theorem cp_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (g c1 h c2 : G) (y c : F),
    g ^ y = c1 -> h ^ y = c2 ->
    List.NoDup lf -> (forall z : F, List.In z lf) ->
    Permutation
      (generalised_cp_schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn y g h c)
      (generalised_cp_simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn g h c1 c2 c).
  Proof.
    intros * h1 h2 hnd hall.
    exact (generalised_cp_special_honest_verifier_zkp_enum y g h c1 c2 (conj h1 h2) lf Hlfn c hnd hall).
  Qed.

  Section Rows.

    Local Notation VG m := (Vector.t G m).
    Local Notation vexp m := (mexp (vid := vec_id (V := G) (vid := gid) m)
      (vadd := vec_add (vadd := gop)) (smul := vec_smul (smul := gpow))).

    (* A presentation with m components is given by one base row per
      component (over the K witness coordinates) and one target per
      component. The Okamoto bases in G^m are the columns. *)
    Fixpoint transpose {m : nat} (K : nat) : Vector.t (VG K) m -> Vector.t (VG m) K :=
      match K return Vector.t (VG K) m -> Vector.t (VG m) K with
      | 0 => fun _ => []
      | S K' => fun Bs => Vector.map Vector.hd Bs :: transpose K' (Vector.map Vector.tl Bs)
      end.

    Lemma map_fun_const : forall {A B : Type} (c : B) (m : nat) (v : Vector.t A m),
      Vector.map (fun _ => c) v = Vector.const c m.
    Proof.
      intros A B c m v; induction v as [| a m v ih]; [reflexivity |].
      cbn [Vector.map]; rewrite ih; reflexivity.
    Qed.

    Lemma map2_map : forall {A B C D : Type} (f : B -> C -> D) (g : A -> B) (h : A -> C) (m : nat)
      (v : Vector.t A m),
      Vector.map2 f (Vector.map g v) (Vector.map h v) = Vector.map (fun a => f (g a) (h a)) v.
    Proof.
      intros A B C D f g h m v; induction v as [| a m v ih]; [reflexivity |].
      cbn [Vector.map]; rewrite map2_cons, ih; reflexivity.
    Qed.

    (* the product-space multi-exponentiation is componentwise *)
    Lemma vexp_transpose : forall (m K : nat) (Bs : Vector.t (VG K) m) (ws : Vector.t F K),
      vexp m (transpose K Bs) ws = Vector.map (fun row => gexp row ws) Bs.
    Proof.
      intros m K; induction K as [| K ih]; intros Bs ws.
      + rewrite (vector_inv_0 ws); cbn [transpose]; rewrite mexp_nil.
        symmetry; etransitivity.
        - apply (Vector.map_ext _ _ (fun row : Vector.t G 0 => gexp row []) (fun _ => gid)).
          intro row; apply mexp_nil.
        - apply map_fun_const.
      + destruct (vector_inv_S ws) as (w & ws' & ->).
        cbn [transpose]; rewrite mexp_cons, ih.
        unfold vec_add, vec_smul; rewrite !Vector.map_map, map2_map.
        apply Vector.map_ext; intro row.
        destruct (vector_inv_S row) as (r0 & row' & ->).
        rewrite mexp_cons; reflexivity.
    Qed.

    (* the component reconstructions, as the U-Prove verifier computes them:
      T_j^{−c} · ∏_i B_j[i]^{r_i} *)
    Definition ext_reconstruct {K m : nat} (c : F) (Bs : Vector.t (VG K) m) (Ts : VG m)
      (rs : Vector.t F K) : VG m :=
      Vector.map2 (fun row T => gop (T ^ (opp c)) (gexp row rs)) Bs Ts.

    Lemma ext_reconstruct_eq : forall (K m : nat) (c : F) (Bs : Vector.t (VG K) m) (Ts : VG m)
      (rs : Vector.t F K),
      vec_add (vadd := gop) (ext_reconstruct c Bs Ts rs) (vec_smul (smul := gpow) Ts c) =
      Vector.map (fun row => gexp row rs) Bs.
    Proof.
      intros K m c; induction m as [| m ih]; intros Bs Ts rs.
      + rewrite (vector_inv_0 Bs), (vector_inv_0 Ts); reflexivity.
      + destruct (vector_inv_S Bs) as (row & Bs' & ->).
        destruct (vector_inv_S Ts) as (T & Ts' & ->).
        unfold ext_reconstruct, vec_add, vec_smul in *.
        rewrite map2_cons; cbn [Vector.map]; rewrite map2_cons.
        f_equal; [| apply ih].
        rewrite (gcomm (T ^ (opp c)) (gexp row rs)), <-gassoc, pow_opp, ginv_l, gid_r; reflexivity.
    Qed.

    Definition ext_verify {n m : nat} (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m)
      (t : @sigma_proto F (VG m) 1 1 (S (S n))) : bool :=
      generalised_okamoto_accepting_conversation (gid := vec_id (V := G) (vid := gid) m)
        (gop := vec_add (vadd := gop)) (gpow := vec_smul (smul := gpow)) (Gdec := vec_dec Gdec)
        (n := n) (transpose (S (S n)) Bs) Ts t.

    Definition ext_real {n m : nat} (ws : Vector.t F (S (S n))) (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m)
      (us : Vector.t F (S (S n))) (c : F) : @sigma_proto F (VG m) 1 1 (S (S n)) :=
      generalised_okamoto_real_protocol (add := add) (mul := mul) (gid := vec_id (V := G) (vid := gid) m)
        (gop := vec_add (vadd := gop)) (gpow := vec_smul (smul := gpow)) (n := n)
        ws (transpose (S (S n)) Bs) Ts us c.

    Definition ext_simulator {n m : nat} (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m)
      (us : Vector.t F (S (S n))) (c : F) : @sigma_proto F (VG m) 1 1 (S (S n)) :=
      generalised_okamoto_simulator_protocol (opp := opp) (gid := vec_id (V := G) (vid := gid) m)
        (gop := vec_add (vadd := gop)) (gpow := vec_smul (smul := gpow)) (n := n)
        (transpose (S (S n)) Bs) Ts us c.

    Definition ext_real_distribution {n m : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (ws : Vector.t F (S (S n))) (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m) (c : F) :
      dist (@sigma_proto F (VG m) 1 1 (S (S n))) :=
      generalised_okamoto_real_distribution (add := add) (mul := mul) (gid := vec_id (V := G) (vid := gid) m)
        (gop := vec_add (vadd := gop)) (gpow := vec_smul (smul := gpow)) (n := n)
        lf Hlfn ws (transpose (S (S n)) Bs) Ts c.

    Definition ext_simulator_distribution {n m : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m) (c : F) : dist (@sigma_proto F (VG m) 1 1 (S (S n))) :=
      generalised_okamoto_simulator_distribution (opp := opp) (gid := vec_id (V := G) (vid := gid) m)
        (gop := vec_add (vadd := gop)) (gpow := vec_smul (smul := gpow)) (n := n)
        lf Hlfn (transpose (S (S n)) Bs) Ts c.

    (* the componentwise reconstructions and the challenge form an accepting
      transcript of the product-space statement *)
    Theorem ext_reconstruct_accepting : forall (n m : nat) (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m)
      (c : F) (rs : Vector.t F (S (S n))),
      ext_verify Bs Ts ([ext_reconstruct c Bs Ts rs]; [c]; rs) = true.
    Proof.
      intros *; unfold ext_verify.
      apply generalised_okamoto_accepting_conversation_true.
      cbv beta iota; rewrite mexp_okamoto, vexp_transpose.
      cbn [Vector.hd Vector.caseS].
      symmetry; apply ext_reconstruct_eq.
    Qed.

    Theorem ext_completeness : forall (n m : nat) (ws : Vector.t F (S (S n))) (Bs : Vector.t (VG (S (S n))) m)
      (Ts : VG m) (us : Vector.t F (S (S n))) (c : F),
      (forall j : Fin.t m, gexp Bs[@j] ws = Ts[@j]) ->
      ext_verify Bs Ts (ext_real ws Bs Ts us c) = true.
    Proof.
      intros * hrel; unfold ext_verify, ext_real.
      apply generalised_okamoto_real_accepting_conversation.
      change (Ts = vexp m (transpose (S (S n)) Bs) ws).
      rewrite vexp_transpose.
      apply Vector.eq_nth_iff; intros j ? <-.
      rewrite (Vector.nth_map _ _ j j eq_refl); symmetry; apply hrel.
    Qed.

    Theorem ext_simulator_completeness : forall (n m : nat) (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m)
      (us : Vector.t F (S (S n))) (c : F),
      ext_verify Bs Ts (ext_simulator Bs Ts us c) = true.
    Proof. intros *; apply generalised_okamoto_simulator_accepting_conversation. Qed.

    (* special soundness: one witness satisfying every component equation, so
      the pseudonym and the commitments are bound to the token's attributes *)
    Theorem ext_special_soundness : forall (n m : nat) (Bs : Vector.t (VG (S (S n))) m) (Ts A : VG m)
      (c1 c2 : F) (rs1 rs2 : Vector.t F (S (S n))),
      c1 <> c2 ->
      ext_verify Bs Ts ([A]; [c1]; rs1) = true ->
      ext_verify Bs Ts ([A]; [c2]; rs2) = true ->
      exists ws : Vector.t F (S (S n)), forall j : Fin.t m, gexp Bs[@j] ws = Ts[@j].
    Proof.
      intros * hc h1 h2; unfold ext_verify in h1, h2.
      destruct (generalised_okamoto_real_special_soundness n (transpose (S (S n)) Bs) Ts A c1 c2 rs1 rs2
        hc h1 h2) as (xi & hxi & _).
      exists xi; intro j.
      assert (hv : Ts = vexp m (transpose (S (S n)) Bs) xi) by exact hxi.
      rewrite vexp_transpose in hv; rewrite hv.
      rewrite (Vector.nth_map _ _ j j eq_refl); reflexivity.
    Qed.

    Theorem ext_shvzk : forall (n m : nat) (lf : list F) (Hlfn : lf <> List.nil) (ws : Vector.t F (S (S n)))
      (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m) (c : F),
      (forall j : Fin.t m, gexp Bs[@j] ws = Ts[@j]) ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation (ext_real_distribution lf Hlfn ws Bs Ts c) (ext_simulator_distribution lf Hlfn Bs Ts c).
    Proof.
      intros * hrel hnd hall; unfold ext_real_distribution, ext_simulator_distribution.
      apply generalised_okamoto_special_honest_verifier_zkp_enum; [| exact hnd | exact hall].
      change (Ts = vexp m (transpose (S (S n)) Bs) ws).
      rewrite vexp_transpose.
      apply Vector.eq_nth_iff; intros j ? <-.
      rewrite (Vector.nth_map _ _ j j eq_refl); symmetry; apply hrel.
    Qed.

    (* a row with the single base b at coordinate p *)
    Definition unit_row {K : nat} (p : Fin.t K) (b : G) : VG K :=
      Vector.replace (Vector.const gid K) p b.

    Lemma replace_F1 : forall {A : Type} (k : nat) (a : A) (v : Vector.t A k) (b : A),
      Vector.replace (a :: v) Fin.F1 b = b :: v.
    Proof. reflexivity. Qed.

    Lemma replace_FS : forall {A : Type} (k : nat) (a : A) (v : Vector.t A k) (p : Fin.t k) (b : A),
      Vector.replace (a :: v) (Fin.FS p) b = a :: Vector.replace v p b.
    Proof. reflexivity. Qed.

    Lemma mexp_unit_row : forall (K : nat) (p : Fin.t K) (b : G) (ws : Vector.t F K),
      gexp (unit_row p b) ws = b ^ ws[@p].
    Proof.
      induction K as [| K ih]; intros p b ws; [refine (match fin_inv_0 p with end) |].
      destruct (vector_inv_S ws) as (w & ws' & ->).
      destruct (fin_inv_S _ p) as [-> | (p' & ->)]; unfold unit_row in *; rewrite const_S.
      + rewrite replace_F1, mexp_cons, mexp_const_vid, gid_r; reflexivity.
      + rewrite replace_FS, mexp_cons, ih, (smul_vid (HV := Hvec)), gid_l; reflexivity.
    Qed.

  End Rows.

End OkamotoRows.
