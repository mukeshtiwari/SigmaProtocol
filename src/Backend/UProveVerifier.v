(** * Fiat–Shamir verifier for U-Prove tokens and presentation proofs *)

(** This file defines the executable verifier for Microsoft U-Prove
    (U-Prove Cryptographic Specification V1.1 Revision 3, Figures 4 and 10;
    the verification equations are unchanged in Revisions 4 and 5 of March
    2023) and links each check to an interactive Sigma protocol proved
    correct in [Crypto.UProve].

    The verifier sees only published values: the token
    [(h, σ_z', σ_c', σ_r')], the presentation digest [a], the responses
    [r_0, r_i] (and [r_d] for Device-protected tokens), and for the
    extensions the pseudonym data [(a_p, P_s)] and the attribute commitments
    [(c̃_i, ã_i, r̃_i)]. It reconstructs every announcement from the responses
    and the challenge and compares its hash with the published digest.

    - Token signature (Figure 4): a Chaum–Pedersen proof that
      [log_g g_0 = log_h σ_z']; the verifier rebuilds
      [(g^{σ_r} g_0^{−σ_c}, h^{σ_r} σ_z^{−σ_c})] and checks
      [σ_c = Hs(…)] ([verify_signature]).
    - Presentation (Figure 10): an Okamoto proof for
      [target = h^{α⁻¹} · ∏ rest_i^{−x_i}], where the bases are [h] followed
      by the bases of the undisclosed attributes; the announcement is
      [target^{−c} · ∏ b_i^{r_i}] ([verify_presentation]). With all
      attributes disclosed this degenerates to a Schnorr proof.
    - Extensions: pseudonym and commitments add rows sharing the same
      response vector, giving the multi-row Okamoto protocol of
      [Crypto.OkamotoRows] ([verify_uprove]).

    How the challenges are derived. The hash formatting of the
    specification (Section 2.2) is not formalised. The verifier takes three
    oracles from the caller: [Ha : G -> Digest] for the announcement digests
    [a = H(A)], [a_p = H(A_p)], [ã_i = H(Ã_i)]; [C] mapping the digests to
    the challenge [c = H(⟨c_p, m_d⟩)] (all token and message data fixed in
    the closure); and [Hs : G -> G -> F] for the signature challenge
    [σ_c' = H(h, PI, σ_z', σ_a', σ_b')]. In the extracted driver
    (src/Executable/Uproveverifier/main.ml with [Examples.UProveIns], P-256
    and SHA-256) these are OCaml functions; the group arithmetic,
    reconstruction and comparisons are extracted from this file. The driver
    runs it on the test vectors of the U-Prove [C#] SDK.

    What is proved. Each [*_accepting] / [*_okamoto] / [*_schnorr] theorem
    states that an accepted proof gives (i) the hash equation for the
    published digest or challenge and (ii) an accepting transcript of the
    corresponding interactive protocol ([sig_verify], [pres_verify],
    [pres0_verify], [ext_verify]) whose challenge is the oracle value.
    Special soundness and SHVZK of those protocols are proved in
    [Crypto.UProve] and [Crypto.OkamotoRows].

    What is NOT verified. The step from a hash-consistent accepting
    transcript to soundness of the non-interactive proof (random oracle,
    rewinding) is not formalised; neither is the hash formatting, the
    parsing of the test vectors, nor group membership of received points.
    The accepting-transcript part (ii) holds for all responses by
    construction; only (i) depends on the check. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool List setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows UProve.
From Utility Require Import Util.
Import VectorNotations.

(** ** Verifier over an abstract prime-order group *)

(** [F] is the scalar field, [G] the group as an [F]-vector space
    (multiplicative notation via [^]), and [Digest] the type of hash
    outputs with decidable equality [Ddec]; U-Prove compares digests, not
    field elements, for the presentation announcements. *)
Section UProveVerifier.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}
    {Digest : Type} {Ddec : forall x y : Digest, {x = y} + {x <> y}}.

  (** Local notations: [^] for exponentiation, [(a; c; r)] for transcripts,
      [gexp] for multi-exponentiation, [VG m] for group vectors, and names
      for the group laws used in the proofs. *)
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

  (** Boolean view of a decision procedure. *)
  Definition bool_of_dec {P Q : Prop} (d : {P} + {Q}) : bool :=
    match d with left _ => true | right _ => false end.

  (** [bool_of_dec (dec x y) = true] implies [x = y]. *)
  Lemma bool_of_dec_true : forall (A : Type) (dec : forall x y : A, {x = y} + {x <> y}) (x y : A),
    bool_of_dec (dec x y) = true -> x = y.
  Proof. intros * h; destruct (dec x y); [assumption | discriminate]. Qed.

  (** Group identity [(T^{−c} · M) · T^c = M], used to cancel the target
      factor of a reconstructed announcement. *)
  Lemma cancel_pow : forall (T M : G) (c : F), gop (gop (T ^ (opp c)) M) (T ^ c) = M.
  Proof.
    intros; rewrite (gcomm (T ^ (opp c)) M), <-gassoc, (pow_opp (Hvec := Hvec)), ginv_l, gid_r;
    reflexivity.
  Qed.

  (** *** Token signature *)

  (** Verifies the Issuer's signature [(σ_z, σ_c, σ_r)] on a token with
      public key [h]: rejects [h = 1] (as the specification requires), and
      otherwise accepts iff
      [σ_c = Hs(g^{σ_r} g_0^{−σ_c}, h^{σ_r} σ_z^{−σ_c})]. Here [g_0] is the
      Issuer public key and [g] the group generator. *)
  Definition verify_signature (Hs : G -> G -> F) (g g0 h σz : G) (σc σr : F) : bool :=
    match Gdec h gid with
    | left _ => false
    | right _ =>
      bool_of_dec (Fdec σc (Hs (gop (g ^ σr) (g0 ^ (opp σc))) (gop (h ^ σr) (σz ^ (opp σc)))))
    end.

  (** If [verify_signature] accepts, then [h ≠ 1], [σ_c] is the oracle value
      on the reconstruction, and [sig_transcript] is an accepting
      Chaum–Pedersen transcript ([sig_reconstruct_accepting]). Combined with
      [sig_special_soundness] two such transcripts would extract [y_0] with
      [g_0 = g^{y_0}] and [σ_z = h^{y_0}]. *)
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

  (** *** Presentation proof *)

  (** [pres_announcement c h rest target rs = target^{−c} · ∏ b_i^{r_i}]
      with bases [b = h :: rest] ([pres_bases]): the announcement implied by
      challenge [c] and responses [rs]. [target] is the public part of the
      token value ([pres_target] in [Crypto.UProve]). *)
  Definition pres_announcement {k : nat} (c : F) (h : G) (rest : Vector.t G k) (target : G)
    (rs : Vector.t F (S k)) : G :=
    gop (target ^ (opp c)) (gexp (pres_bases h rest) rs).

  (** Verifies a presentation proof: the challenge is [C a], computed from
      the published digest [a], and the check is
      [a = Ha(pres_announcement (C a) …)]. *)
  Definition verify_presentation {k : nat} (Ha : G -> Digest) (C : Digest -> F) (h : G)
    (rest : Vector.t G k) (target : G) (a : Digest) (rs : Vector.t F (S k)) : bool :=
    bool_of_dec (Ddec a (Ha (pres_announcement (C a) h rest target rs))).

  (** If [verify_presentation] accepts with at least one undisclosed base
      ([rest] of length [S n], so at least two Okamoto bases), then [a] is
      the digest of the reconstruction and the reconstructed transcript is
      accepted by the Okamoto verifier [pres_verify]. Proof: rewrite the
      multi-exponentiation into the Okamoto fold ([mexp_okamoto]) and cancel
      [target^{−c} · target^c] with [cancel_pow]. *)
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

  (** Variant for the case where every attribute is disclosed and the token
      has no Device: only the base [h] remains and the proof is a Schnorr
      proof, accepted by [pres0_verify]. *)
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

  (** *** Multi-row proofs (pseudonym and commitments) *)

  (** [digests_ok Ha ds A] checks componentwise that [ds_j = Ha(A_j)]. *)
  Definition digests_ok (Ha : G -> Digest) {m : nat} (ds : Vector.t Digest m) (A : VG m) : bool :=
    Vector.fold_right andb (Vector.map2 (fun d x => bool_of_dec (Ddec d (Ha x))) ds A) true.

  (** Correctness of [digests_ok]: it returns [true] only if
      [ds = map Ha A]. Proof by induction on the length. *)
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

  (** Generic multi-row check: the challenge is [C ds] computed from all
      published digests, the announcements are reconstructed row by row with
      [ext_reconstruct] (from [Crypto.OkamotoRows]), and each digest must be
      the hash of its row's announcement. *)
  Definition verify_ext {K m : nat} (Ha : G -> Digest) (C : Vector.t Digest m -> F)
    (Bs : Vector.t (VG K) m) (Ts : VG m) (ds : Vector.t Digest m) (rs : Vector.t F K) : bool :=
    digests_ok Ha ds (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (C ds) Bs Ts rs).

  (** If [verify_ext] accepts, the digests are the hashes of the
      reconstructed announcements and the reconstructed transcript is
      accepted by [ext_verify] (multi-row Okamoto with a common response
      vector of length at least two). *)
  Theorem verify_ext_accepting : forall (n m : nat) (Ha : G -> Digest) (C : Vector.t Digest m -> F)
    (Bs : Vector.t (VG (S (S n))) m) (Ts : VG m) (ds : Vector.t Digest m) (rs : Vector.t F (S (S n))),
    verify_ext Ha C Bs Ts ds rs = true ->
    ds = Vector.map Ha (ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (C ds) Bs Ts rs) /\
    ext_verify (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec) Bs Ts ([ext_reconstruct (opp := opp) (gid := gid) (gop := gop) (gpow := gpow) (C ds) Bs Ts rs]; [C ds]; rs) = true.
  Proof.
    intros * hv; unfold verify_ext in hv.
    split; [apply digests_ok_true; exact hv | apply ext_reconstruct_accepting].
  Qed.

  (** A row of the multi-row statement: the bases, the target and the
      published digest of that row's announcement. *)
  Definition component (K : nat) : Type := (VG K * G * Digest)%type.

  (** The core presentation row ([core_row]: [h], the hidden bases, then
      [e] identity bases for the commitment openings) with its target and
      digest [a]. *)
  Definition core_component {k e : nat} (h : G) (rest : Vector.t G k) (target : G) (a : Digest) :
    component (S k + e) :=
    (core_row (e := e) (gid := gid) h rest, target, a).

  (** The pseudonym row: base [g_s] at coordinate [p], target [P_s⁻¹]
      (the witness holds [−x_p]), digest [a_p]. *)
  Definition nym_component {K : nat} (p : Fin.t K) (gs Ps : G) (ap : Digest) : component K :=
    (nym_row (gid := gid) p gs, ginv Ps, ap).

  (** The row of an attribute commitment [c̃ = g^{x_i} g_1^{õ}]: bases [g]
      and [g_1] at coordinates [i] and [o], target [c̃⁻¹], digest [ã]. *)
  Definition commit_component {K : nat} (i o : Fin.t K) (g g1 ct : G) (at_ : Digest) : component K :=
    (commit_row (gid := gid) (gop := gop) i o g g1, ginv ct, at_).

  (** Assembles all rows of a U-Prove presentation: the core row, an
      optional pseudonym row and one row per committed attribute. Each
      commitment entry carries its attribute and opening coordinates, the
      commitment [c̃] and its digest. *)
  Definition uprove_components {k e : nat} (h : G) (rest : Vector.t G k) (target : G) (a : Digest)
    (nym : option (Fin.t (S k + e) * G * G * Digest))
    (coms : list (Fin.t (S k + e) * Fin.t (S k + e) * G * Digest)) (g g1 : G) : list (component (S k + e)) :=
    core_component h rest target a ::
    (match nym with
     | Some (p, gs, Ps, ap) => nym_component p gs Ps ap :: nil
     | None => nil
     end ++
     List.map (fun '(i, o, ct, at_) => commit_component i o g g1 ct at_) coms).

  (** [coord K p] converts a natural-number index into a coordinate
      [Fin.t K], or [None] if out of range; used by the driver to build
      rows from parsed indices. *)
  Definition coord (K p : nat) : option (Fin.t K) :=
    match Fin.of_nat p K with inleft f => Some f | inright _ => None end.

  (** The full U-Prove check with extensions: [verify_ext] on the list of
      rows (converted to a vector), with the challenge oracle [C] taking the
      list of row digests. *)
  Definition verify_uprove {K : nat} (Ha : G -> Digest) (C : list Digest -> F)
    (cs : list (component K)) (rs : Vector.t F K) : bool :=
    let v := Vector.of_list cs in
    verify_ext Ha (fun ds => C (Vector.to_list ds))
      (Vector.map (fun c => fst (fst c)) v) (Vector.map (fun c => snd (fst c)) v)
      (Vector.map snd v) rs.

  (** If [verify_uprove] accepts, then the published digests are the hashes
      of the reconstructed row announcements and the reconstruction is an
      accepting [ext_verify] transcript for the assembled rows. Immediate
      from [verify_ext_accepting]. *)
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
