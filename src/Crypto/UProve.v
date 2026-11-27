(** * U-Prove: token presentation and issuer signature as Sigma protocols *)

(** This file models the zero-knowledge parts of Microsoft's U-Prove
    anonymous-credential system (U-Prove Cryptographic Specification V1.1
    Revision 3, based on S. Brands, Rethinking Public Key Infrastructures
    and Digital Certificates, MIT Press 2000).

    A U-Prove token has public key [h = γ^α], where

    [[
      γ = g_0 · g_t^(x_t) · ∏_(i ∈ D) g_i^(x_i) · ∏_(i ∉ D) g_i^(x_i) · [g_d^(x_d)]
    ]]

    collects the Issuer's generators [g_i] raised to the encoded attributes
    [x_i], the token-information hash [x_t] and optionally a Device key
    [x_d]; [α] is the Prover's blinding factor and [α⁻¹] is the token private
    key. When the token is presented with disclosed attribute set [D], the
    Prover shows knowledge of [α⁻¹] and of the undisclosed values such that

    [[
      g_0 · g_t^(x_t) · ∏_(i ∈ D) g_i^(x_i) = h^(α⁻¹) · ∏_(i ∉ D) g_i^(−x_i) · [g_d^(−x_d)].
    ]]

    The left-hand side is public ([pres_target]); the right-hand side is a
    multi-exponentiation with bases [h :: rest] and witness
    [α⁻¹ :: −xrest] ([pres_bases], [pres_witness]). This is one instance of
    the generalised Okamoto protocol of [Okamoto]; the U-Prove responses
    [r_0 = c·α⁻¹ + w_0] and [r_i = −c·x_i + w_i] are exactly the library's
    responses [u + c·x] for this witness. When nothing is hidden (only [h]
    remains), the statement degenerates to a Schnorr proof ([pres0_]...).

    The Issuer's signature [(σ_z', σ_c', σ_r')] on a token is a
    Chaum–Pedersen proof that [g_0 = g^(y_0)] and [σ_z' = h^(y_0)] for the
    Issuer's private key [y_0] (section [Signature]). The file also models
    the blind issuance protocol [issue] and proves the issued token passes
    the signature check.

    Scope-exclusive pseudonyms [P_s = g_s^(x_p)] and attribute commitments
    [c̃ = g^(x_i) · g_1^(õ)] are further linear equations over the same
    witness, proved with the same challenge and responses. Section
    [Extensions] provides the corresponding rows for the product-space
    encoding of [OkamotoRows].

    All security properties (completeness, special soundness, special
    honest-verifier zero knowledge) are inherited from [Okamoto] and
    [ChaumPedersen]. The Fiat–Shamir verifier is in
    [Backend/UProveVerifier.v] and a P-256 instantiation in
    [Examples/UProveIns.v]. *)
From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Sigma Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

(** ** Setting *)
Section UProve.

  (** A field [F] of exponents and a group [G] forming a vector space, each
      with decidable equality. The local notations below expose the group and
      vector-space laws, and the shared lemmas of [OkamotoRows] at this
      instance. *)
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

  Local Notation pow_opp := (pow_opp (Hvec := Hvec)).
  Local Notation ginv_gop := (ginv_gop (Hvec := Hvec)).
  Local Notation gpow_add := (gpow_add (Hvec := Hvec)).
  Local Notation gpow_mul := (gpow_mul (Hvec := Hvec)).
  Local Notation gpow_one := (gpow_one (Hvec := Hvec)).
  Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
  Local Notation mexp_map_opp := (mexp_map_opp (Hvec := Hvec)).
  Local Notation mexp_map2_gop := (mexp_map2_gop (Hvec := Hvec)).
  Local Notation mexp_unit_row := (mexp_unit_row (Hvec := Hvec)).

  (** ** The token and the presentation proof *)
  Section Presentation.

    (** The public side of the presentation equation:
        [g_0 · g_t^(x_t) · ∏_(i ∈ D) g_i^(x_i)], with disclosed bases [gD] and
        values [xD]. *)
    Definition pres_target {d : nat} (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d) : G :=
      gop g0 (gop (gt ^ xt) (gexp gD xD)).

    (** The token value [γ]: the public part [pres_target] times the hidden
        part [∏ rest^xrest] (undisclosed attributes and, if present, the Device
        key). *)
    Definition gamma {d k : nat} (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d)
      (rest : Vector.t G k) (xrest : Vector.t F k) : G :=
      gop (pres_target g0 gt xt gD xD) (gexp rest xrest).

    (** The token public key [h = γ^α]. *)
    Definition token_pub (γ : G) (α : F) : G := γ ^ α.

    (** Okamoto bases of the presentation: [h] followed by the hidden bases
        [rest]. *)
    Definition pres_bases {k : nat} (h : G) (rest : Vector.t G k) : Vector.t G (S k) := h :: rest.
    (** Okamoto witness of the presentation: [α⁻¹] followed by the negated hidden
        values [−xrest]. *)
    Definition pres_witness {k : nat} (αinv : F) (xrest : Vector.t F k) : Vector.t F (S k) :=
      αinv :: Vector.map opp xrest.

    (** The token relation: if [α · αinv = 1], then
        [h^(αinv) · ∏ rest^(−xrest) = pres_target], where [h = γ^α]. Indeed
        [h^(α⁻¹) = γ] and the hidden factor of [γ] cancels against its
        inverse. *)
    Lemma pres_relation : forall (d k : nat) (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d)
      (rest : Vector.t G k) (xrest : Vector.t F k) (α αinv : F),
      mul α αinv = one ->
      gexp (pres_bases (token_pub (gamma g0 gt xt gD xD rest xrest) α) rest) (pres_witness αinv xrest) =
      pres_target g0 gt xt gD xD.
    Proof.
      intros * hα; unfold pres_bases, pres_witness, token_pub, gamma.
      rewrite mexp_cons, mexp_map_opp, <-gpow_mul, hα, gpow_one, <-gassoc, ginv_r, gid_r; reflexivity.
    Qed.

    (** *** At least one hidden coordinate: generalised Okamoto

        The honest presentation transcript (with [S (S n) ≥ 2] coordinates:
        [α⁻¹] and at least one hidden value). *)
    Definition pres_real {n : nat} (αinv : F) (xrest : Vector.t F (S n)) (h : G) (rest : Vector.t G (S n))
      (target : G) (us : Vector.t F (S (S n))) (c : F) : @sigma_proto F G 1 1 (S (S n)) :=
      generalised_okamoto_real_protocol (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) (pres_witness αinv xrest) (pres_bases h rest) target us c.

    (** Simulated presentation transcript. *)
    Definition pres_simulator {n : nat} (h : G) (rest : Vector.t G (S n)) (target : G)
      (us : Vector.t F (S (S n))) (c : F) : @sigma_proto F G 1 1 (S (S n)) :=
      generalised_okamoto_simulator_protocol (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) (pres_bases h rest) target us c.

    (** Presentation verifier: the Okamoto check
        [h^(r_0) · ∏ rest^(r_i) = a · target^c]. *)
    Definition pres_verify {n : nat} (h : G) (rest : Vector.t G (S n)) (target : G)
      (t : @sigma_proto F G 1 1 (S (S n))) : bool :=
      generalised_okamoto_accepting_conversation (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)
        (n := n) (pres_bases h rest) target t.

    (** Distribution of honest presentation transcripts for a fixed
        challenge. *)
    Definition pres_real_distribution {n : nat} (lf : list F) (Hlfn : lf <> List.nil) (αinv : F)
      (xrest : Vector.t F (S n)) (h : G) (rest : Vector.t G (S n)) (target : G) (c : F) :
      dist (@sigma_proto F G 1 1 (S (S n))) :=
      generalised_okamoto_real_distribution (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) lf Hlfn (pres_witness αinv xrest) (pres_bases h rest) target c.

    (** Distribution of simulated presentation transcripts. *)
    Definition pres_simulator_distribution {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (h : G) (rest : Vector.t G (S n)) (target : G) (c : F) : dist (@sigma_proto F G 1 1 (S (S n))) :=
      generalised_okamoto_simulator_distribution (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) lf Hlfn (pres_bases h rest) target c.

    (** Completeness: for a correctly formed token ([h = γ^α], [α·αinv = 1]),
        every honest presentation transcript is accepted. *)
    Theorem pres_completeness : forall (n d : nat) (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d)
      (rest : Vector.t G (S n)) (xrest : Vector.t F (S n)) (α αinv : F) (us : Vector.t F (S (S n))) (c : F),
      mul α αinv = one ->
      pres_verify (token_pub (gamma g0 gt xt gD xD rest xrest) α) rest (pres_target g0 gt xt gD xD)
        (pres_real αinv xrest (token_pub (gamma g0 gt xt gD xD rest xrest) α) rest
          (pres_target g0 gt xt gD xD) us c) = true.
    Proof.
      intros * hα; unfold pres_verify, pres_real.
      apply generalised_okamoto_real_accepting_conversation.
      symmetry; exact (pres_relation d (S n) g0 gt xt gD xD rest xrest α αinv hα).
    Qed.

    (** Simulated presentation transcripts are always accepted. *)
    Theorem pres_simulator_completeness : forall (n : nat) (h : G) (rest : Vector.t G (S n)) (target : G)
      (us : Vector.t F (S (S n))) (c : F),
      pres_verify h rest target (pres_simulator h rest target us c) = true.
    Proof. intros *; apply generalised_okamoto_simulator_accepting_conversation. Qed.

    (** Special soundness: two accepting transcripts with the same announcement
        and different challenges yield a token private key [αinv] and hidden
        values [xrest] satisfying the presentation equation. The Okamoto
        extractor gives [−xrest] in the tail coordinates, which is negated
        back. *)
    Theorem pres_special_soundness : forall (n : nat) (h : G) (rest : Vector.t G (S n)) (target a : G)
      (c1 c2 : F) (rs1 rs2 : Vector.t F (S (S n))),
      c1 <> c2 ->
      pres_verify h rest target ([a]; [c1]; rs1) = true ->
      pres_verify h rest target ([a]; [c2]; rs2) = true ->
      exists (αinv : F) (xrest : Vector.t F (S n)),
        gexp (pres_bases h rest) (pres_witness αinv xrest) = target.
    Proof.
      intros * hc h1 h2; unfold pres_verify in h1, h2.
      destruct (generalised_okamoto_real_special_soundness n (pres_bases h rest) target a c1 c2 rs1 rs2
        hc h1 h2) as (xi & hxi & _).
      destruct (vector_inv_S xi) as (x0 & xs & ->).
      assert (hm : Vector.map opp (Vector.map opp xs) = xs).
      { rewrite Vector.map_map; erewrite Vector.map_ext; [apply Vector.map_id |].
        intro x; cbv beta; field. }
      exists x0, (Vector.map opp xs); unfold pres_witness; rewrite hm.
      symmetry; exact hxi.
    Qed.

    (** Special honest-verifier zero knowledge: if the presentation equation
        holds and [lf] enumerates the field without duplicates, the honest
        transcript distribution is a permutation of the simulator's, which
        uses only public data. In particular, transcripts reveal nothing about
        the undisclosed attributes. *)
    Theorem pres_shvzk : forall (n : nat) (lf : list F) (Hlfn : lf <> List.nil) (αinv : F)
      (xrest : Vector.t F (S n)) (h : G) (rest : Vector.t G (S n)) (target : G) (c : F),
      gexp (pres_bases h rest) (pres_witness αinv xrest) = target ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation (pres_real_distribution lf Hlfn αinv xrest h rest target c)
        (pres_simulator_distribution lf Hlfn h rest target c).
    Proof.
      intros * hrel hnd hall; unfold pres_real_distribution, pres_simulator_distribution.
      exact (generalised_okamoto_special_honest_verifier_zkp_enum lf Hlfn _ _ _ c (eq_sym hrel) hnd hall).
    Qed.

    (** *** No hidden coordinate: Schnorr

        When every attribute is disclosed and there is no Device key, the
        statement is [h^(α⁻¹) = target], proved with the Schnorr protocol of
        [Sigma]. This is the honest transcript. *)
    Definition pres0_real (αinv : F) (h : G) (u c : F) : @sigma_proto F G 1 1 1 :=
      schnorr_protocol (add := add) (mul := mul) (gpow := gpow) αinv h u c.

    (** Schnorr verifier for [h^(αinv) = target]. *)
    Definition pres0_verify (h target : G) (t : @sigma_proto F G 1 1 1) : bool :=
      accepting_conversation (gop := gop) (gpow := gpow) (Gdec := Gdec) h target t.

    (** Completeness of the fully disclosed presentation, from [pres_relation]
        with empty [rest]. *)
    Theorem pres0_completeness : forall (d : nat) (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d)
      (α αinv u c : F),
      mul α αinv = one ->
      pres0_verify (token_pub (gamma g0 gt xt gD xD [] []) α) (pres_target g0 gt xt gD xD)
        (pres0_real αinv (token_pub (gamma g0 gt xt gD xD [] []) α) u c) = true.
    Proof.
      intros * hα; unfold pres0_verify, pres0_real.
      apply schnorr_completeness.
      pose proof (pres_relation d 0 g0 gt xt gD xD [] [] α αinv hα) as hr.
      unfold pres_bases, pres_witness in hr; cbn [Vector.map] in hr.
      rewrite mexp_single in hr; symmetry; exact hr.
    Qed.

    (** Special soundness of the fully disclosed presentation: two transcripts
        yield [αinv] with [h^(αinv) = target]. *)
    Theorem pres0_special_soundness : forall (h target a : G) (c1 r1 c2 r2 : F),
      c1 <> c2 ->
      pres0_verify h target ([a]; [c1]; [r1]) = true ->
      pres0_verify h target ([a]; [c2]; [r2]) = true ->
      exists αinv : F, h ^ αinv = target.
    Proof. intros * hc h1 h2; exact (special_soundness h target a c1 r1 c2 r2 hc h1 h2). Qed.

    (** Special HVZK of the fully disclosed presentation, as a permutation of
        distributions when [lf] enumerates the field. *)
    Theorem pres0_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (αinv : F) (h target : G) (c : F),
      h ^ αinv = target ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation (schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn αinv h c)
        (simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn h target c).
    Proof.
      intros * hr hnd hall.
      exact (special_honest_verifier_zkp_enum αinv h target (eq_sym hr) lf Hlfn c hnd hall).
    Qed.

  End Presentation.

  (** ** The Issuer's signature: Chaum–Pedersen *)
  Section Signature.

    (** The verifier's reconstruction of the signature announcement:
        [(g^(σ_r) · g_0^(−σ_c), h^(σ_r) · σ_z^(−σ_c))]. The token is valid when
        [σ_c] equals the hash of [h], the prover information, [σ_z] and these
        two values; the hash is outside this file. *)
    Definition sig_reconstruct (g g0 h σz : G) (σc σr : F) : Vector.t G 2 :=
      [gop (g ^ σr) (g0 ^ (opp σc)); gop (h ^ σr) (σz ^ (opp σc))].

    (** The Chaum–Pedersen transcript of a signature [(σ_z, σ_c, σ_r)]. *)
    Definition sig_transcript (g g0 h σz : G) (σc σr : F) : @sigma_proto F G 2 1 1 :=
      (sig_reconstruct g g0 h σz σc σr; [σc]; [σr]).

    (** The Chaum–Pedersen verifier for [g_0 = g^(y_0)] and [σ_z = h^(y_0)]. *)
    Definition sig_verify (g g0 h σz : G) (t : @sigma_proto F G 2 1 1) : bool :=
      generalised_cp_accepting_conversations (gop := gop) (gpow := gpow) (Gdec := Gdec) g h g0 σz t.

    (** A reconstructed signature transcript always verifies. *)
    Theorem sig_reconstruct_accepting : forall (g g0 h σz : G) (σc σr : F),
      sig_verify g g0 h σz (sig_transcript g g0 h σz σc σr) = true.
    Proof.
      intros *; unfold sig_verify, sig_transcript, sig_reconstruct.
      apply generalised_cp_accepting_conversations_accept_backward;
      rewrite <-gassoc, pow_opp, ginv_l, gid_r; reflexivity.
    Qed.

    (** A U-Prove token as stored by the Prover: public key [tok_h] and the
        signature components [tok_sz], [tok_sc], [tok_sr] (the primed values
        of the specification). *)
    Record token := mk_token { tok_h : G; tok_sz : G; tok_sc : F; tok_sr : F }.

    (** The blind issuance protocol (specification Figure 8), with the Prover's
        hash value [σc'] supplied as a parameter. Inputs: generators [g], [g0],
        [γ], Issuer key [y0], Issuer nonce [w], Prover blinding [α] and [β1],
        [β2]. Output: the token [(h, σ_z', σ_c', σ_r')] together with the
        Prover's blinded announcement [(σ_a', σ_b')], which the Prover hashes
        to obtain [σc'] in the real protocol. *)
    Definition issue (g g0 γ : G) (y0 w α β1 β2 σc' : F) : token * (G * G) :=
      let h := γ ^ α in
      let σz := γ ^ y0 in
      let σa := g ^ w in
      let σb := γ ^ w in
      let t1 := gop (g0 ^ β1) (g ^ β2) in
      let t2 := h ^ β2 in
      let σz' := σz ^ α in
      let σa' := gop t1 σa in
      let σb' := gop (gop (σz' ^ β1) t2) (σb ^ α) in
      let σc := add σc' β1 in
      let σr := add (mul σc y0) w in
      let σr' := add σr β2 in
      (mk_token h σz' σc' σr', (σa', σb')).

    (** Normalise group expressions [g^a] by collecting exponents and close the
        exponent equation with [field]. *)
    Local Ltac gnorm := repeat rewrite <-gpow_mul; repeat rewrite <-gpow_add; f_equal; field.

    (** Issuance completeness: if [g0 = g^(y0)], the verifier's reconstruction
        of the issued token's signature announcement equals the Prover's
        blinded announcement [(σ_a', σ_b')]. Hence, if [σc'] is the hash of
        [(h, ..., σ_z', σ_a', σ_b')], the token passes signature
        verification. *)
    Theorem issuance_reconstruct : forall (g g0 γ : G) (y0 w α β1 β2 σc' : F),
      g0 = g ^ y0 ->
      let t := fst (issue g g0 γ y0 w α β1 β2 σc') in
      sig_reconstruct g g0 (tok_h t) (tok_sz t) (tok_sc t) (tok_sr t) =
      [fst (snd (issue g g0 γ y0 w α β1 β2 σc')); snd (snd (issue g g0 γ y0 w α β1 β2 σc'))].
    Proof.
      intros * hg; subst g0; unfold issue, sig_reconstruct; cbn [fst snd tok_h tok_sz tok_sc tok_sr].
      apply (f_equal2 (fun a b : G => [a; b])); gnorm.
    Qed.

    (** The issued token satisfies the signature statement:
        [g^(y0) = g0] and [h^(y0) = σ_z']. *)
    Theorem issuance_statement : forall (g g0 γ : G) (y0 w α β1 β2 σc' : F),
      g0 = g ^ y0 ->
      let t := fst (issue g g0 γ y0 w α β1 β2 σc') in
      g ^ y0 = g0 /\ tok_h t ^ y0 = tok_sz t.
    Proof.
      intros * hg; subst g0; unfold issue; cbn [fst tok_h tok_sz]; split; [reflexivity |].
      rewrite <-!gpow_mul; f_equal; field.
    Qed.

    (** Special soundness of the signature proof: two accepting transcripts
        with the same announcement give [y0] with [g^(y0) = g0] and
        [h^(y0) = σz]. *)
    Theorem sig_special_soundness : forall (g g0 h σz : G) (a : Vector.t G 2) (c1 r1 c2 r2 : F),
      c1 <> c2 ->
      sig_verify g g0 h σz (a; [c1]; [r1]) = true ->
      sig_verify g g0 h σz (a; [c2]; [r2]) = true ->
      exists y0 : F, g ^ y0 = g0 /\ h ^ y0 = σz.
    Proof.
      intros * hc h1 h2.
      destruct (generalise_cp_sigma_soundness g h g0 σz a c1 c2 r1 r2 h1 h2 hc) as (y & hy).
      exists y; split; [exact (hy Fin.F1) | exact (hy (Fin.FS Fin.F1))].
    Qed.

    (** Special HVZK of the signature proof, as a permutation of
        distributions when [lf] enumerates the field. *)
    Theorem sig_shvzk : forall (lf : list F) (Hlfn : lf <> List.nil) (g g0 h σz : G) (y0 c : F),
      g ^ y0 = g0 -> h ^ y0 = σz ->
      List.NoDup lf -> (forall y : F, List.In y lf) ->
      Permutation
        (generalised_cp_schnorr_distribution (add := add) (mul := mul) (gpow := gpow) lf Hlfn y0 g h c)
        (generalised_cp_simulator_distribution (opp := opp) (gop := gop) (gpow := gpow) lf Hlfn g h g0 σz c).
    Proof.
      intros * h1 h2 hnd hall.
      exact (generalised_cp_special_honest_verifier_zkp_enum y0 g h g0 σz (conj h1 h2) lf Hlfn c hnd hall).
    Qed.

  End Signature.

  (** ** Pseudonyms and attribute commitments as extra rows

      These definitions express the extra equations of a presentation as rows
      for the product-space encoding of [OkamotoRows], all over one witness
      vector of length [K]. *)
  Section Extensions.

    Local Notation VG m := (Vector.t G m).

    (** The core row: the presentation bases followed by [e] identity bases,
        one per commitment opening. *)
    Definition core_row {k e : nat} (h : G) (rest : Vector.t G k) : VG (S k + e) :=
      pres_bases h rest ++ Vector.const gid e.

    (** The full witness: the presentation witness followed by the negated
        commitment openings [−os]. *)
    Definition core_witness {k e : nat} (αinv : F) (xrest : Vector.t F k) (os : Vector.t F e) :
      Vector.t F (S k + e) :=
      pres_witness αinv xrest ++ Vector.map opp os.

    (** The core row satisfies the presentation equation with the full witness,
        since the identity bases contribute nothing. *)
    Lemma core_relation : forall (k e : nat) (h : G) (rest : Vector.t G k) (αinv : F) (xrest : Vector.t F k)
      (os : Vector.t F e) (target : G),
      gexp (pres_bases h rest) (pres_witness αinv xrest) = target ->
      gexp (core_row h rest) (core_witness αinv xrest os) = target.
    Proof.
      intros * hr; unfold core_row, core_witness.
      rewrite mexp_app, mexp_const_vid, gid_r; exact hr.
    Qed.

    (** The row of the scope-exclusive pseudonym [P_s = g_s^(x_p)]: base [g_s]
        at the position [p] of [x_p], identity elsewhere. *)
    Definition nym_row {K : nat} (p : Fin.t K) (gs : G) : VG K := unit_row (gid := gid) p gs.

    (** If coordinate [p] of the witness is [−x], the pseudonym row evaluates
        to [(g_s^x)⁻¹]: the row's target is [P_s⁻¹]. *)
    Lemma nym_relation : forall (K : nat) (p : Fin.t K) (gs : G) (x : F) (ws : Vector.t F K),
      ws[@p] = opp x ->
      gexp (nym_row p gs) ws = ginv (gs ^ x).
    Proof. intros * hp; unfold nym_row; rewrite mexp_unit_row, hp, pow_opp; reflexivity. Qed.

    (** The row of an attribute commitment [c̃ = g^(x_i) · g_1^(õ)]: base [g]
        at position [i], base [g_1] at position [o] of the opening. *)
    Definition commit_row {K : nat} (i o : Fin.t K) (g g1 : G) : VG K :=
      Vector.map2 gop (unit_row (gid := gid) i g) (unit_row (gid := gid) o g1).

    (** If coordinates [i] and [o] hold [−x] and [−õ], the commitment row
        evaluates to [(g^x · g_1^(õ))⁻¹]: the row's target is [c̃⁻¹]. *)
    Lemma commit_relation : forall (K : nat) (i o : Fin.t K) (g g1 : G) (x od : F) (ws : Vector.t F K),
      ws[@i] = opp x -> ws[@o] = opp od ->
      gexp (commit_row i o g g1) ws = ginv (gop (g ^ x) (g1 ^ od)).
    Proof.
      intros * hi ho; unfold commit_row.
      rewrite mexp_map2_gop, !mexp_unit_row, hi, ho, !pow_opp, ginv_gop; reflexivity.
    Qed.

  End Extensions.

End UProve.
