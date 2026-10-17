(* Fiat–Shamir verification of U-Prove tokens and presentation proofs
   (Microsoft, U-Prove Cryptographic Specification V1.1 Revision 3, Figures 4
   and 10; unchanged in Revisions 4 and 5 of March 2023), linked to the
   protocol instances of Crypto/UProve.v.

   The verifier receives the published values only: the token
   (h, σ_z', σ_c', σ_r'), the digest a, the responses r_0, r_i, [r_d], and for
   the extensions the pseudonym (a_p, P_s) and the commitments (c̃_i, ã_i, r̃_i).
   It reconstructs the announcements from the responses and the challenge and
   checks them against the published digests. The hash formatting of the
   spec (section 2.2) is done by the driver, which passes three oracles:

     Ha : G -> Digest        a = H(A), a_p = H(A_p), ã_i = H(Ã_i)  (Figures 9, 10)
     C  : digests -> F       c = H(⟨c_p, m_d⟩) with
                             c_p = H(UID_T, a, ⟨D⟩, ⟨x_i⟩_D, ⟨C⟩, ⟨c̃_i⟩, ⟨ã_i⟩, p', a_p, P_s, m)
                             as a function of the announcement digests, the
                             token and message data being fixed in the closure
     Hs : G -> G -> F        σ_c' = H(h, PI, σ_z', σ_a', σ_b') as a function of
                             the reconstructed (σ_a', σ_b')

   The link theorems say that a verified proof yields an accepting transcript
   of the corresponding library protocol (Okamoto for the presentation, in G
   or, with pseudonym and commitments, in G^m; Schnorr when every attribute
   is disclosed; Chaum–Pedersen for the Issuer's signature), whose challenge
   is the oracle's value on the reconstructed announcement. As everywhere in
   this development, the theorems are about the interactive protocols; the
   random-oracle step from a hash-consistent accepting transcript to
   soundness of the non-interactive proof is not formalised. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool List setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows UProve.
From Utility Require Import Util.
Import VectorNotations.

Section UProveVerifier.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}
    {Digest : Type} {Ddec : forall x y : Digest, {x = y} + {x <> y}}.

  Local Infix "^" := gpow.
  Local Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).
  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).
  Local Notation VG m := (Vector.t G m).

  Local Notation gcg := (@vector_space_commutative_group F (@eq F) zero one add mul sub div
    opp inv G (@eq G) gid ginv gop gpow Hvec).
  Local Notation ggroup := (@commutative_group_group G (@eq G) gop gid ginv gcg).
  Local Notation gmonoid := (@group_monoid G (@eq G) gop gid ginv ggroup).
  Local Notation gassoc := (@associative G (@eq G) gop
    (@monoid_is_associative G (@eq G) gop gid gmonoid)).
  Local Notation gid_r := (@right_identity G (@eq G) gop gid
    (@monoid_is_right_identity G (@eq G) gop gid gmonoid)).
  Local Notation gcomm := (@commutative G (@eq G) gop
    (@commutative_group_is_commutative G (@eq G) gop gid ginv gcg)).
  Local Notation ginv_l := (@left_inverse G (@eq G) gop gid ginv
    (@group_is_left_inverse G (@eq G) gop gid ginv ggroup)).

  Definition bool_of_dec {P Q : Prop} (d : {P} + {Q}) : bool :=
    match d with left _ => true | right _ => false end.

  Lemma bool_of_dec_true : forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (x y : A),
    bool_of_dec (dec x y) = true -> x = y.
  Proof. intros * h; destruct (dec x y); [assumption | discriminate]. Qed.

  (* T^{−c} · M · T^c = M *)
  Lemma cancel_pow : forall (T M : G) (c : F), gop (gop (T ^ (opp c)) M) (T ^ c) = M.
  Proof.
    intros; rewrite (gcomm (T ^ (opp c)) M), <-gassoc, (pow_opp (Hvec := Hvec)), ginv_l, gid_r;
    reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The Issuer's signature (Figure 4)                                 *)
  (* ---------------------------------------------------------------- *)

  Definition verify_signature (Hs : G -> G -> F) (g g0 h σz : G) (σc σr : F) : bool :=
    match Gdec h gid with
    | left _ => false
    | right _ =>
      bool_of_dec (Fdec σc (Hs (gop (g ^ σr) (g0 ^ (opp σc))) (gop (h ^ σr) (σz ^ (opp σc)))))
    end.

  Theorem verify_signature_accepting : forall (Hs : G -> G -> F) (g g0 h σz : G) (σc σr : F),
    verify_signature Hs g g0 h σz σc σr = true ->
    h <> gid /\
    σc = Hs (gop (g ^ σr) (g0 ^ (opp σc))) (gop (h ^ σr) (σz ^ (opp σc))) /\
    sig_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) g g0 h σz
      (sig_transcript (opp := opp) (gop := gop) (gpow := gpow) g g0 h σz σc σr) = true.
  Proof.
    intros * hv; unfold verify_signature in hv.
    destruct (Gdec h gid) as [_ | hne]; [discriminate |].
    split; [exact hne | split; [apply bool_of_dec_true in hv; exact hv |]].
    apply sig_reconstruct_accepting.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* The presentation proof, core statement (Figure 10)               *)
  (* ---------------------------------------------------------------- *)

  (* the reconstructed announcement
     (g_0 g_t^{x_t} ∏_{D} g_i^{x_i})^{−c} · h^{r_0} · ∏_{U} g_i^{r_i} · [g_d^{r_d}] *)
  Definition pres_announcement {k : nat} (c : F) (h : G) (rest : Vector.t G k) (target : G)
    (rs : Vector.t F (S k)) : G :=
    gop (target ^ (opp c)) (gexp (pres_bases h rest) rs).

  Definition verify_presentation {k : nat} (Ha : G -> Digest) (C : Digest -> F) (h : G)
    (rest : Vector.t G k) (target : G) (a : Digest) (rs : Vector.t F (S k)) : bool :=
    bool_of_dec (Ddec a (Ha (pres_announcement (C a) h rest target rs))).

  (* at least one undisclosed attribute or a Device: Okamoto *)
  Theorem verify_presentation_okamoto : forall (n : nat) (Ha : G -> Digest) (C : Digest -> F) (h : G)
    (rest : Vector.t G (S n)) (target : G) (a : Digest) (rs : Vector.t F (S (S n))),
    verify_presentation Ha C h rest target a rs = true ->
    a = Ha (pres_announcement (C a) h rest target rs) /\
    pres_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) h rest target ([pres_announcement (C a) h rest target rs]; [C a]; rs) = true.
  Proof.
    intros * hv; unfold verify_presentation in hv; apply bool_of_dec_true in hv.
    split; [exact hv |].
    unfold pres_verify; apply generalised_okamoto_accepting_conversation_true.
    cbv beta iota; rewrite mexp_okamoto; cbn [Vector.hd Vector.caseS].
    unfold pres_announcement; rewrite cancel_pow; reflexivity.
  Qed.

  (* every attribute disclosed, no Device: Schnorr *)
  Theorem verify_presentation_schnorr : forall (Ha : G -> Digest) (C : Digest -> F) (h target : G)
    (a : Digest) (rs : Vector.t F 1),
    verify_presentation Ha C h [] target a rs = true ->
    a = Ha (pres_announcement (C a) h [] target rs) /\
    pres0_verify (gop := gop) (gpow := gpow) (Gdec := Gdec) h target ([pres_announcement (C a) h [] target rs]; [C a]; rs) = true.
  Proof.
    intros * hv; unfold verify_presentation in hv; apply bool_of_dec_true in hv.
    split; [exact hv |].
    destruct (vector_inv_S rs) as (r & rs' & ->); rewrite (vector_inv_0 rs').
    unfold pres0_verify, accepting_conversation; cbn [Vector.hd Vector.caseS].
    rewrite dec_true.
    unfold pres_announcement, pres_bases; rewrite mexp_single, cancel_pow; reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* With pseudonym and commitments: the statement in G^m              *)
  (* ---------------------------------------------------------------- *)

  (* every published digest is the hash of the corresponding reconstructed
    announcement *)
  Definition digests_ok (Ha : G -> Digest) {m : nat} (ds : Vector.t Digest m) (A : VG m) : bool :=
    Vector.fold_right andb (Vector.map2 (fun d x => bool_of_dec (Ddec d (Ha x))) ds A) true.

  Lemma digests_ok_true : forall (Ha : G -> Digest) (m : nat) (ds : Vector.t Digest m) (A : VG m),
    digests_ok Ha ds A = true -> ds = Vector.map Ha A.
  Proof.
    intros Ha m; induction m as [| m ih]; intros ds A h.
    + rewrite (vector_inv_0 ds), (vector_inv_0 A); reflexivity.
    + destruct (vector_inv_S ds) as (d & ds' & ->).
      destruct (vector_inv_S A) as (x & A' & ->).
      unfold digests_ok in *; rewrite map2_cons in h; cbn [Vector.fold_right] in h.
      apply andb_true_iff in h; destruct h as (h1 & h2).
      apply bool_of_dec_true in h1; cbn [Vector.map]; rewrite h1, (ih _ _ h2); reflexivity.
  Qed.

  Definition verify_ext {K m : nat} (Ha : G -> Digest) (C : Vector.t Digest m -> F)
    (Bs : Vector.t (VG K) m) (Ts : VG m) (ds : Vector.t Digest m) (rs : Vector.t F K) : bool :=
    digests_ok Ha ds (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (C ds) Bs Ts rs).

  Theorem verify_ext_accepting : forall (n m : nat) (Ha : G -> Digest) (C : Vector.t Digest m -> F)
    (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m) (ds : Vector.t Digest m) (rs : Vector.t F (S (S n))),
    verify_ext Ha C Bs Ts ds rs = true ->
    ds = Vector.map Ha (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (C ds) Bs Ts rs) /\
    ext_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) Bs Ts ([ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (C ds) Bs Ts rs]; [C ds]; rs) = true.
  Proof.
    intros * hv; unfold verify_ext in hv.
    split; [apply digests_ok_true; exact hv | apply ext_reconstruct_accepting].
  Qed.

  (* ---- the rows of a U-Prove presentation ---- *)

  (* Witness coordinates: 0 is α⁻¹, then the hidden bases in order (the
    undisclosed attributes by increasing index, then the Device key), then
    one opening per committed attribute. A component is (base row, target,
    published digest). *)
  Definition component (K : nat) : Type := (VG K * G * Digest)%type.

  Definition core_component {k e : nat} (h : G) (rest : Vector.t G k) (target : G) (a : Digest) :
    component (S k + e) :=
    (core_row (e := e) (gid := gid) h rest, target, a).

  Definition nym_component {K : nat} (p : Fin.t K) (gs Ps : G) (ap : Digest) : component K :=
    (nym_row (gid := gid) p gs, ginv Ps, ap).

  Definition commit_component {K : nat} (i o : Fin.t K) (g g1 ct : G) (at_ : Digest) : component K :=
    (commit_row (gid := gid) (gop := gop) i o g g1, ginv ct, at_).

  Definition uprove_components {k e : nat} (h : G) (rest : Vector.t G k) (target : G) (a : Digest)
    (nym : option (Fin.t (S k + e) * G * G * Digest))
    (coms : list (Fin.t (S k + e) * Fin.t (S k + e) * G * Digest)) (g g1 : G) : list (component (S k + e)) :=
    core_component h rest target a ::
    (match nym with
     | Some (p, gs, Ps, ap) => nym_component p gs Ps ap :: nil
     | None => nil
     end ++
     List.map (fun '(i, o, ct, at_) => commit_component i o g g1 ct at_) coms).

  (* index of a hidden coordinate, from the spec's positions *)
  Definition coord (K p : nat) : option (Fin.t K) :=
    match Fin.of_nat p K with inleft f => Some f | inright _ => None end.

  Definition verify_uprove {K : nat} (Ha : G -> Digest) (C : list Digest -> F)
    (cs : list (component K)) (rs : Vector.t F K) : bool :=
    let v := Vector.of_list cs in
    verify_ext Ha (fun ds => C (Vector.to_list ds))
      (Vector.map (fun c => fst (fst c)) v) (Vector.map (fun c => snd (fst c)) v)
      (Vector.map snd v) rs.

  Theorem verify_uprove_accepting : forall (n : nat) (Ha : G -> Digest) (C : list Digest -> F)
    (cs : list (component (S (S n)))) (rs : Vector.t F (S (S n))),
    verify_uprove Ha C cs rs = true ->
    let v := Vector.of_list cs in
    let Bs := Vector.map (fun c => fst (fst c)) v in
    let Ts := Vector.map (fun c => snd (fst c)) v in
    let ds := Vector.map snd v in
    let c := C (Vector.to_list ds) in
    ds = Vector.map Ha (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c Bs Ts rs) /\
    ext_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) Bs Ts ([ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) c Bs Ts rs]; [c]; rs) = true.
  Proof. intros * hv; cbv zeta; exact (verify_ext_accepting _ _ _ _ _ _ _ _ hv). Qed.

End UProveVerifier.
