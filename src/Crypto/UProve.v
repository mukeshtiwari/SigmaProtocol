(* U-Prove (Brands' credentials; Microsoft, "U-Prove Cryptographic
   Specification V1.1 Revision 3".

  https://www.microsoft.com/en-us/research/publication/u-prove-cryptographic-specification-v1-1-revision-3/

   A U-Prove token has public key h = γ^α with

     γ = g_0 · g_1^{x_1} ⋯ g_n^{x_n} · g_t^{x_t} · [g_d^{x_d}]

   where g_0..g_n, g_t are the Issuer's public generators, x_i the encoded
   attribute values, x_t the hash of the token information, g_d^{x_d} the
   optional Device key and α the Prover's blinding factor; the token private
   key is α⁻¹. Presenting the token with a disclosed set D (spec section 2.6,
   Figures 9 and 10) proves knowledge of α⁻¹ and of the undisclosed x_i with

     g_0 · g_t^{x_t} · ∏_{i∈D} g_i^{x_i} = h^{α⁻¹} · ∏_{i∉D} g_i^{−x_i} · [g_d^{−x_d}]

   which is one instance of the generalised Okamoto protocol (Crypto/Okamoto.v)
   with bases (h, g_i for i ∉ D, [g_d]) and witness (α⁻¹, −x_i, [−x_d]). The
   spec's responses r_0 = c·α⁻¹ + w_0 and r_i = −c·x_i + w_i are exactly the
   library's response u + c·x for this witness, and the verifier's
   reconstruction

     A = (g_0 g_t^{x_t} ∏_{i∈D} g_i^{x_i})^{−c} · h^{r_0} · ∏_{i∉D} g_i^{r_i} · [g_d^{r_d}]

   is the Okamoto announcement (Backend/UProveVerifier.v links the published
   proof to the accepting transcript). The Issuer's signature (σ_z', σ_c', σ_r')
   on the token (section 2.3.6, Figure 4) is a Chaum–Pedersen proof that
   g_0 = g^{y_0} and σ_z' = h^{y_0} for the Issuer's private key y_0, with the
   spec's reconstruction g^{σ_r'} g_0^{−σ_c'}, h^{σ_r'} σ_z'^{−σ_c'} its
   announcement (Crypto/ChaumPedersen.v). The scope-exclusive pseudonym
   P_s = g_s^{x_p} and the attribute commitments c̃_i = g^{x_i} g_1^{õ_i}
   (Figure 9) are further linear equations over the same witness (plus the
   fresh openings õ_i), verified with the same challenge and the same
   responses: the whole presentation is a single Okamoto statement in the
   product space G^m (Algebra/Vector_product_space.v), one component per
   equation.

   This file has the statements and the protocol instances: completeness,
   special soundness (extraction of α⁻¹ and the hidden attributes, and for the
   signature of y_0) and special honest-verifier zero knowledge, all
   inherited from Okamoto and Chaum–Pedersen. The Fiat–Shamir verifier is in
   Backend/UProveVerifier.v and the P-256 instantiation in
   Examples/UProveIns.v. *)

From Stdlib Require Import Utf8 Vector Fin Lia Bool setoid_ring.Field Permutation List.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring
  Vector_space Vector_product_space.
From Crypto Require Import Sigma Okamoto ChaumPedersen EqSigma MultiExp OkamotoRows.
From Probability Require Import Prob Distr.
From Utility Require Import Util.
Import VectorNotations.

Section UProve.

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




  (* the shared lemmas of Crypto/OkamotoRows.v at this instance *)
  Local Notation pow_opp := (pow_opp (Hvec := Hvec)).
  Local Notation ginv_gop := (ginv_gop (Hvec := Hvec)).
  Local Notation gpow_add := (gpow_add (Hvec := Hvec)).
  Local Notation gpow_mul := (gpow_mul (Hvec := Hvec)).
  Local Notation gpow_one := (gpow_one (Hvec := Hvec)).
  Local Notation gop_pow := (gop_pow (Hvec := Hvec)).
  Local Notation mexp_map_opp := (mexp_map_opp (Hvec := Hvec)).
  Local Notation mexp_map2_gop := (mexp_map2_gop (Hvec := Hvec)).
  Local Notation mexp_unit_row := (mexp_unit_row (Hvec := Hvec)).

  (* ---------------------------------------------------------------- *)
  (* The token and the presentation statement                         *)
  (* ---------------------------------------------------------------- *)

  Section Presentation.

    (* the verifier's side: g_0 · g_t^{x_t} · ∏_{i∈D} g_i^{x_i} *)
    Definition pres_target {d : nat} (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d) : G :=
      gop g0 (gop (gt ^ xt) (gexp gD xD)).

    (* γ with the hidden part separated: rest are the bases of the undisclosed
      attributes, and of the Device key when the token is Device-protected *)
    Definition gamma {d k : nat} (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d)
      (rest : Vector.t G k) (xrest : Vector.t F k) : G :=
      gop (pres_target g0 gt xt gD xD) (gexp rest xrest).

    (* the token public key h = γ^α *)
    Definition token_pub (γ : G) (α : F) : G := γ ^ α.

    Definition pres_bases {k : nat} (h : G) (rest : Vector.t G k) : Vector.t G (S k) := h :: rest.
    Definition pres_witness {k : nat} (αinv : F) (xrest : Vector.t F k) : Vector.t F (S k) :=
      αinv :: Vector.map opp xrest.

    (* the token relation: h^{α⁻¹} · ∏ rest^{−xrest} = g_0 g_t^{x_t} ∏_{D} g_i^{x_i} *)
    Lemma pres_relation : forall (d k : nat) (g0 gt : G) (xt : F) (gD : Vector.t G d) (xD : Vector.t F d)
      (rest : Vector.t G k) (xrest : Vector.t F k) (α αinv : F),
      mul α αinv = one ->
      gexp (pres_bases (token_pub (gamma g0 gt xt gD xD rest xrest) α) rest) (pres_witness αinv xrest) =
      pres_target g0 gt xt gD xD.
    Proof.
      intros * hα; unfold pres_bases, pres_witness, token_pub, gamma.
      rewrite mexp_cons, mexp_map_opp, <-gpow_mul, hα, gpow_one, <-gassoc, ginv_r, gid_r; reflexivity.
    Qed.

    (* ---- at least one hidden coordinate: the generalised Okamoto protocol ---- *)

    Definition pres_real {n : nat} (αinv : F) (xrest : Vector.t F (S n)) (h : G) (rest : Vector.t G (S n))
      (target : G) (us : Vector.t F (S (S n))) (c : F) : @sigma_proto F G 1 1 (S (S n)) :=
      generalised_okamoto_real_protocol (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) (pres_witness αinv xrest) (pres_bases h rest) target us c.

    Definition pres_simulator {n : nat} (h : G) (rest : Vector.t G (S n)) (target : G)
      (us : Vector.t F (S (S n))) (c : F) : @sigma_proto F G 1 1 (S (S n)) :=
      generalised_okamoto_simulator_protocol (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) (pres_bases h rest) target us c.

    Definition pres_verify {n : nat} (h : G) (rest : Vector.t G (S n)) (target : G)
      (t : @sigma_proto F G 1 1 (S (S n))) : bool :=
      generalised_okamoto_accepting_conversation (gid := gid) (gop := gop) (gpow := gpow) (Gdec := Gdec)
        (n := n) (pres_bases h rest) target t.

    Definition pres_real_distribution {n : nat} (lf : list F) (Hlfn : lf <> List.nil) (αinv : F)
      (xrest : Vector.t F (S n)) (h : G) (rest : Vector.t G (S n)) (target : G) (c : F) :
      dist (@sigma_proto F G 1 1 (S (S n))) :=
      generalised_okamoto_real_distribution (add := add) (mul := mul) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) lf Hlfn (pres_witness αinv xrest) (pres_bases h rest) target c.

    Definition pres_simulator_distribution {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
      (h : G) (rest : Vector.t G (S n)) (target : G) (c : F) : dist (@sigma_proto F G 1 1 (S (S n))) :=
      generalised_okamoto_simulator_distribution (opp := opp) (gid := gid) (gop := gop) (gpow := gpow)
        (n := n) lf Hlfn (pres_bases h rest) target c.

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

    Theorem pres_simulator_completeness : forall (n : nat) (h : G) (rest : Vector.t G (S n)) (target : G)
      (us : Vector.t F (S (S n))) (c : F),
      pres_verify h rest target (pres_simulator h rest target us c) = true.
    Proof. intros *; apply generalised_okamoto_simulator_accepting_conversation. Qed.

    (* special soundness: two accepting transcripts with the same announcement
      give the token private key and the hidden attributes *)
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

    (* special honest-verifier zero knowledge: the transcripts of an honest
      presentation are distributed as the simulator's, which sees only the
      public data; in particular they carry no information about the
      undisclosed attributes *)
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

    (* ---- no hidden coordinate (every attribute disclosed, no Device): Schnorr ---- *)

    Definition pres0_real (αinv : F) (h : G) (u c : F) : @sigma_proto F G 1 1 1 :=
      schnorr_protocol (add := add) (mul := mul) (gpow := gpow) αinv h u c.

    Definition pres0_verify (h target : G) (t : @sigma_proto F G 1 1 1) : bool :=
      accepting_conversation (gop := gop) (gpow := gpow) (Gdec := Gdec) h target t.

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

    Theorem pres0_special_soundness : forall (h target a : G) (c1 r1 c2 r2 : F),
      c1 <> c2 ->
      pres0_verify h target ([a]; [c1]; [r1]) = true ->
      pres0_verify h target ([a]; [c2]; [r2]) = true ->
      exists αinv : F, h ^ αinv = target.
    Proof. intros * hc h1 h2; exact (special_soundness_berry h target a c1 r1 c2 r2 hc h1 h2). Qed.

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

  (* ---------------------------------------------------------------- *)
  (* The Issuer's signature: Chaum–Pedersen                            *)
  (* ---------------------------------------------------------------- *)

  Section Signature.

    (* the verifier's reconstruction of the announcement (Figure 4) *)
    Definition sig_reconstruct (g g0 h σz : G) (σc σr : F) : Vector.t G 2 :=
      [gop (g ^ σr) (g0 ^ (opp σc)); gop (h ^ σr) (σz ^ (opp σc))].

    Definition sig_transcript (g g0 h σz : G) (σc σr : F) : @sigma_proto F G 2 1 1 :=
      (sig_reconstruct g g0 h σz σc σr; [σc]; [σr]).

    (* the statement: g_0 = g^{y_0} ∧ σ_z' = h^{y_0} *)
    Definition sig_verify (g g0 h σz : G) (t : @sigma_proto F G 2 1 1) : bool :=
      generalised_cp_accepting_conversations (gop := gop) (gpow := gpow) (Gdec := Gdec) g h g0 σz t.

    Theorem sig_reconstruct_accepting : forall (g g0 h σz : G) (σc σr : F),
      sig_verify g g0 h σz (sig_transcript g g0 h σz σc σr) = true.
    Proof.
      intros *; unfold sig_verify, sig_transcript, sig_reconstruct.
      apply generalised_cp_accepting_conversations_accept_backward;
      rewrite <-gassoc, pow_opp, ginv_l, gid_r; reflexivity.
    Qed.

    (* The issuance protocol (Figure 8), with the Prover's hash value σ_c' as a
      parameter: the token and the Prover's announcement (σ_a', σ_b'). *)
    Record token := mk_token { tok_h : G; tok_sz : G; tok_sc : F; tok_sr : F }.

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

    Local Ltac gnorm := repeat rewrite <-gpow_mul; repeat rewrite <-gpow_add; f_equal; field.

    (* issuance completeness: the verifier's reconstruction of the issued token
      is the Prover's announcement, so the token passes Figure 4 whenever
      σ_c' = H(h, PI, σ_z', σ_a', σ_b') *)
    Theorem issuance_reconstruct : forall (g g0 γ : G) (y0 w α β1 β2 σc' : F),
      g0 = g ^ y0 ->
      let t := fst (issue g g0 γ y0 w α β1 β2 σc') in
      sig_reconstruct g g0 (tok_h t) (tok_sz t) (tok_sc t) (tok_sr t) =
      [fst (snd (issue g g0 γ y0 w α β1 β2 σc')); snd (snd (issue g g0 γ y0 w α β1 β2 σc'))].
    Proof.
      intros * hg; subst g0; unfold issue, sig_reconstruct; cbn [fst snd tok_h tok_sz tok_sc tok_sr].
      apply (f_equal2 (fun a b : G => [a; b])); gnorm.
    Qed.

    (* the issued token's signature statement holds *)
    Theorem issuance_statement : forall (g g0 γ : G) (y0 w α β1 β2 σc' : F),
      g0 = g ^ y0 ->
      let t := fst (issue g g0 γ y0 w α β1 β2 σc') in
      g ^ y0 = g0 /\ tok_h t ^ y0 = tok_sz t.
    Proof.
      intros * hg; subst g0; unfold issue; cbn [fst tok_h tok_sz]; split; [reflexivity |].
      rewrite <-!gpow_mul; f_equal; field.
    Qed.

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

  (* ---------------------------------------------------------------- *)
  (* Pseudonyms and commitments: the presentation in G^m               *)
  (* ---------------------------------------------------------------- *)

  Section Extensions.

    Local Notation VG m := (Vector.t G m).

    (* ---- the U-Prove rows ---- *)

    (* the core row: the presentation bases, then identity bases for the e
      commitment openings; the core witness is the presentation witness
      followed by the negated openings *)
    Definition core_row {k e : nat} (h : G) (rest : Vector.t G k) : VG (S k + e) :=
      pres_bases h rest ++ Vector.const gid e.

    Definition core_witness {k e : nat} (αinv : F) (xrest : Vector.t F k) (os : Vector.t F e) :
      Vector.t F (S k + e) :=
      pres_witness αinv xrest ++ Vector.map opp os.

    Lemma core_relation : forall (k e : nat) (h : G) (rest : Vector.t G k) (αinv : F) (xrest : Vector.t F k)
      (os : Vector.t F e) (target : G),
      gexp (pres_bases h rest) (pres_witness αinv xrest) = target ->
      gexp (core_row h rest) (core_witness αinv xrest os) = target.
    Proof.
      intros * hr; unfold core_row, core_witness.
      rewrite mexp_app, mexp_const_vid, gid_r; exact hr.
    Qed.

    (* the scope-exclusive pseudonym P_s = g_s^{x_p}: coordinate p of the
      witness holds −x_p, and the target is P_s^{−1} *)
    Definition nym_row {K : nat} (p : Fin.t K) (gs : G) : VG K := unit_row (gid := gid) p gs.

    Lemma nym_relation : forall (K : nat) (p : Fin.t K) (gs : G) (x : F) (ws : Vector.t F K),
      ws[@p] = opp x ->
      gexp (nym_row p gs) ws = ginv (gs ^ x).
    Proof. intros * hp; unfold nym_row; rewrite mexp_unit_row, hp, pow_opp; reflexivity. Qed.

    (* the attribute commitment c̃ = g^{x_i} g_1^{õ}: coordinates i and o hold
      −x_i and −õ, and the target is c̃^{−1} *)
    Definition commit_row {K : nat} (i o : Fin.t K) (g g1 : G) : VG K :=
      Vector.map2 gop (unit_row (gid := gid) i g) (unit_row (gid := gid) o g1).

    Lemma commit_relation : forall (K : nat) (i o : Fin.t K) (g g1 : G) (x od : F) (ws : Vector.t F K),
      ws[@i] = opp x -> ws[@o] = opp od ->
      gexp (commit_row i o g g1) ws = ginv (gop (g ^ x) (g1 ^ od)).
    Proof.
      intros * hi ho; unfold commit_row.
      rewrite mexp_map2_gop, !mexp_unit_row, hi, ho, !pow_opp, ginv_gop; reflexivity.
    Qed.

  End Extensions.

End UProve.
