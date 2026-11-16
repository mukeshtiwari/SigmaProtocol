(* A certified verifier for the proofs of a shuffle of the Verificatum
   mix-net (VMN 3.1.0; D. Wikström, "How to Implement a Stand-alone
   Verifier for the Verificatum Mix-Net", the vmnv manual), for key width
   1 and ciphertext width 1 over a group of prime order, without
   pre-computation.

   Algorithm 19 of the manual verifies the proof of a shuffle of one
   mix-server: it derives the batching vector e from a seed (a random
   oracle applied to g, h, u, pk, w, w'), the challenge v from a random
   oracle applied to the seed and the proof commitment τ, and accepts if
   and only if the five equations

     A^v A' = g^{k_A} ∏ h_i^{k_E,i}      C^v C' = g^{k_C}     D^v D' = g^{k_D}
     B_i^v B'_i = g^{k_B,i} B_{i-1}^{k_E,i}      F^v F' = Enc_pk(1, −k_F) ∏ w'_i^{k_E,i}

   hold. These are the Okamoto acceptance test at the statement space V of
   Crypto/ShuffleTW.v for the transcript (τ; v; σ): the announcement is
   (A', C', D', B', F'), the challenge is v itself (Verificatum writes the
   response as ω + v·x) and the response is (k_A, k_C, k_D, k_F, k_B, k_E).
   So verify_pos is tw_verify, and the theorem verify_pos_accepting states
   that a verified proof of a shuffle is an accepting transcript of the
   generalised Okamoto protocol for the multi-base statement whose
   conjunction of equations is tw_relation_iff.

   The random oracles are parameters, as everywhere in this development:
   the driver (Executable/Vmnverifier) implements Verificatum's byte trees,
   SHA-256 random oracles and PRG, derives the independent generators h,
   and passes the two oracles as functions of the data they hash.
   Algorithm 25 (the loop over the mix-servers, accepting a rejected proof
   only if the server left the list unchanged, and requiring at least one
   valid proof) is verify_shuffling.

   Algorithm 22 verifies the joint decryption. Party l publishes decryption
   factors f_l,i = u_i^{−x_l/α} (α = lcm(1..k)², so that the combining
   exponents α·c_l with the Lagrange coefficients c_l are integers), a
   commitment (y'_l, B'_l) = (g^{r_l}, U^{r_l}) with U = ∏ u_i^{e_i}, and the
   reply k_l = r_l − (x_l/α)·v. The verifier combines the proofs of the
   parties in Δ with the exponents α·c_l: y' = ∏ y'_l^{α c_l},
   B' = ∏ B'_l^{α c_l}, k = Σ α c_l k_l, f_i = ∏ f_l,i^{α c_l}, B = ∏ f_i^{e_i},
   and accepts if and only if y^{−v} y' = g^k and B^v B' = U^k (this is what
   VMN's DistrElGamalSessionBasic.verifyCombined computes; the manual's
   PDec notation means the same). These two equations are the acceptance
   test of the library's Chaum–Pedersen protocol (Crypto/ChaumPedersen.v)
   for the statement (y, B^{−1}) = (g, U)^x with announcement (y', B'),
   challenge −v and response k. The exponents α·c_l are computed in the
   field, which changes nothing since the group has order q. Finally the
   plaintexts are m_i = v_i · f_i. *)

From Stdlib Require Import Utf8 Vector List Bool Lia PeanoNat ZArith.
From Algebra Require Import Hierarchy.
From Crypto Require Import Sigma Okamoto MultiExp ShuffleTW ChaumPedersen EqSigma.
From Utility Require Import Util.
Import VectorNotations.

Section Verificatum.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}
    {N : nat}.

  Local Notation M := (S N).                 (* number of ciphertexts *)
  Local Notation ciphertext := (G * G)%type. (* (u, v) = (g^s, y^s m) *)
  Local Notation nwit := (Nat.add 4 (Nat.add M M)).
  Local Notation V := (@ShuffleTW.V G N).

  (* ---------------------------------------------------------------- *)
  (* The published proof of a shuffle of one mix-server (Algorithm 19) *)
  (* ---------------------------------------------------------------- *)

  Record pos_proof : Type := mk_pos_proof {
    pu : Vector.t G M;          (* μ: the permutation commitment u *)
    pB : Vector.t G M;          (* τ = node(B, A', B', C', D', F') *)
    pA' : G;
    pB' : Vector.t G M;
    pC' : G;
    pD' : G;
    pF' : ciphertext;
    kA : F;                     (* σ = node(k_A, k_B, k_C, k_D, k_E, k_F) *)
    kB : Vector.t F M;
    kC : F;
    kD : F;
    kE : Vector.t F M;
    kF : F
  }.

  (* The two random oracles of Algorithm 19, as functions of the data they
    hash: e = PRG(RO_seed(ρ | node(g, h, u, pk, w, w'))) and
    v = RO_challenge(ρ | node(leaf(s), τ)), where the seed s is itself a
    function of (u, w, w'). The driver supplies them with ρ, g, h and pk
    fixed. *)
  Record pos_oracles : Type := mk_pos_oracles {
    oracle_es : Vector.t G M -> Vector.t ciphertext M -> Vector.t ciphertext M -> Vector.t F M;
    oracle_v : Vector.t G M -> Vector.t ciphertext M -> Vector.t ciphertext M -> pos_proof -> F
  }.

  (* the public data of the round-2 statement, in the form of ShuffleTW *)
  Definition pos_public (g : G) (hs : Vector.t G M) (pk : ciphertext)
    (w w' : Vector.t ciphertext M) (es : Vector.t F M) (pf : pos_proof) : @public F G N :=
    @ShuffleTW.mk_public F G N g (Vector.hd hs) hs (snd pk) (pu pf) es (pB pf) w w'.

  Definition pos_announcement (pf : pos_proof) : V :=
    (pA' pf, (pC' pf, (pD' pf, (pB' pf, pF' pf)))).

  Definition pos_response (pf : pos_proof) : Vector.t F nwit :=
    [kA pf; kC pf; kD pf; kF pf] ++ kB pf ++ kE pf.

  Definition pos_transcript (v : F) (pf : pos_proof) : @sigma_proto F V 1 1 nwit :=
    mk_sigma _ _ _ [pos_announcement pf] [v] (pos_response pf).

  (* Algorithm 19 *)
  Definition verify_pos (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (w w' : Vector.t ciphertext M) (pf : pos_proof) : bool :=
    let es := oracle_es O (pu pf) w w' in
    let v := oracle_v O (pu pf) w w' pf in
    tw_verify (one := one) (mul := mul)
      (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)
      (pos_public g hs pk w w' es pf) (pos_transcript v pf).

  (* A verified proof of a shuffle is an accepting transcript of the
    generalised Okamoto protocol for the statement of ShuffleTW. *)
  Theorem verify_pos_accepting : forall (g : G) (hs : Vector.t G M) (pk : ciphertext)
    (O : pos_oracles) (w w' : Vector.t ciphertext M) (pf : pos_proof),
    verify_pos g hs pk O w w' pf = true ->
    let P := pos_public g hs pk w w' (oracle_es O (pu pf) w w') pf in
    generalised_okamoto_accepting_conversation (gid := ShuffleTW.Vid (gid := gid))
      (gop := ShuffleTW.Vadd (gop := gop)) (gpow := ShuffleTW.Vsmul (gpow := gpow))
      (Gdec := ShuffleTW.Vdec (Gdec := Gdec))
      (bases (gid := gid) (ginv := ginv) P)
      (target (one := one) (mul := mul) (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow) P)
      (pos_transcript (oracle_v O (pu pf) w w' pf) pf) = true.
  Proof. intros * h; exact h. Qed.

  (* ---------------------------------------------------------------- *)
  (* Algorithm 25: the shuffling of all mix-servers                    *)
  (* ---------------------------------------------------------------- *)

  Definition ciphertext_eqb (c d : ciphertext) : bool :=
    match Gdec (fst c) (fst d), Gdec (snd c) (snd d) with
    | left _, left _ => true | _, _ => false
    end.

  Definition list_eqb (L L' : Vector.t ciphertext M) : bool :=
    Vector.fold_right andb (Vector.map2 ciphertext_eqb L L') true.

  Lemma ciphertext_eqb_eq : forall c d, ciphertext_eqb c d = true <-> c = d.
  Proof.
    intros [a b] [c d]; unfold ciphertext_eqb; cbn [fst snd].
    destruct (Gdec a c) as [-> | h]; [destruct (Gdec b d) as [-> | h'] |].
    + split; reflexivity.
    + split; [discriminate | intro e; exfalso; apply h'; congruence].
    + split; [discriminate | intro e; exfalso; apply h; congruence].
  Qed.

  Lemma list_eqb_eq : forall (m : nat) (L L' : Vector.t ciphertext m),
    Vector.fold_right andb (Vector.map2 ciphertext_eqb L L') true = true <-> L = L'.
  Proof.
    induction m as [| m ih]; intros L L'.
    + rewrite (vector_inv_0 L), (vector_inv_0 L'); split; reflexivity.
    + destruct (vector_inv_S L) as (c & L1 & ->).
      destruct (vector_inv_S L') as (d & L1' & ->).
      cbn; rewrite andb_true_iff, ciphertext_eqb_eq, ih.
      split; [intros [-> ->]; reflexivity | intro h; injection h as -> h; split; [reflexivity |]].
      apply Eqdep_dec.inj_pair2_eq_dec in h; [exact h | exact Nat.eq_dec].
  Qed.

  (* one step per mix-server: its output list and its proof *)
  Definition step : Type := (Vector.t ciphertext M * pos_proof)%type.

  (* the number of valid proofs, and whether every rejected proof left the
    list unchanged *)
  Fixpoint check_steps (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (L : Vector.t ciphertext M) (steps : list step) : nat * bool :=
    match steps with
    | List.nil => (0, true)
    | List.cons (L', pf) rest =>
        let ok := verify_pos g hs pk O L L' pf in
        let '(n, b) := check_steps g hs pk O L' rest in
        ((if ok then S n else n), b && (ok || list_eqb L L'))
    end.

  (* Algorithm 25: accept if at least one proof is valid and every
    rejected proof left the list unchanged; L0 is the input list, the last
    step's list is the output of the shuffling *)
  Definition verify_shuffling (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (L0 : Vector.t ciphertext M) (steps : list step) : bool :=
    let '(n, b) := check_steps g hs pk O L0 steps in
    b && (1 <=? n).

  (* the lists L_0, L_1, …, L_λa *)
  Definition lists (L0 : Vector.t ciphertext M) (steps : list step) : list (Vector.t ciphertext M) :=
    List.cons L0 (List.map fst steps).

  (* Each server either produced a verified proof of a shuffle from its
    input list to its output list, or left the list unchanged; and at least
    one server produced a verified proof. *)
  Lemma check_steps_spec : forall g hs pk O L steps n b,
    check_steps g hs pk O L steps = (n, b) ->
    b = true ->
    (forall i L1 L2 pf, List.nth_error (lists L steps) i = Some L1 ->
      List.nth_error steps i = Some (L2, pf) ->
      verify_pos g hs pk O L1 L2 pf = true \/ L1 = L2) /\
    (1 <= n -> exists i L1 L2 pf, List.nth_error (lists L steps) i = Some L1 /\
      List.nth_error steps i = Some (L2, pf) /\ verify_pos g hs pk O L1 L2 pf = true).
  Proof.
    intros g hs pk O L steps; revert L.
    induction steps as [| [L' pf] rest ih]; intros L n b hc hb.
    + cbn in hc; injection hc as <- <-. split.
      - intros i L1 L2 pf h1 h2; destruct i; cbn in h2; discriminate.
      - intro h; lia.
    + cbn [check_steps] in hc.
      destruct (check_steps g hs pk O L' rest) as [n' b'] eqn:hrest.
      injection hc as <- <-.
      apply andb_true_iff in hb; destruct hb as [hb' hok].
      destruct (ih L' n' b' hrest hb') as [hall hex].
      split.
      - intros i L1 L2 pf' h1 h2.
        destruct i as [| i]; cbn in h1, h2.
        * injection h1 as <-; injection h2 as <- <-.
          apply orb_true_iff in hok; destruct hok as [hok | hok]; [left; exact hok |].
          right; apply (list_eqb_eq M); exact hok.
        * exact (hall i L1 L2 pf' h1 h2).
      - intro hn; revert hn.
        destruct (verify_pos g hs pk O L L' pf) eqn:hv; intro hn.
        * exists 0, L, L', pf; cbn; repeat split; assumption.
        * destruct (hex hn) as (i & L1 & L2 & pf' & h1 & h2 & h3).
          exists (S i), L1, L2, pf'; cbn; repeat split; assumption.
  Qed.

  Theorem verify_shuffling_spec : forall g hs pk O L0 steps,
    verify_shuffling g hs pk O L0 steps = true ->
    (forall i L1 L2 pf, List.nth_error (lists L0 steps) i = Some L1 ->
      List.nth_error steps i = Some (L2, pf) ->
      verify_pos g hs pk O L1 L2 pf = true \/ L1 = L2) /\
    (exists i L1 L2 pf, List.nth_error (lists L0 steps) i = Some L1 /\
      List.nth_error steps i = Some (L2, pf) /\ verify_pos g hs pk O L1 L2 pf = true).
  Proof.
    intros * h; unfold verify_shuffling in h.
    destruct (check_steps g hs pk O L0 steps) as [n b] eqn:hc.
    apply andb_true_iff in h; destruct h as [hb hn].
    apply Nat.leb_le in hn.
    destruct (check_steps_spec g hs pk O L0 steps n b hc hb) as [h1 h2].
    split; [exact h1 | exact (h2 hn)].
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Algorithm 22: the joint decryption                                *)
  (* ---------------------------------------------------------------- *)

  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).

  (* small integers in the field *)
  Fixpoint nat_to_F (n : nat) : F :=
    match n with 0 => zero | S n' => add one (nat_to_F n') end.

  Fixpoint F_of_pos (x : positive) : F :=
    match x with
    | xH => one
    | xO x' => let y := F_of_pos x' in add y y
    | xI x' => let y := F_of_pos x' in add (add y y) one
    end.

  Definition F_of_Z (z : Z) : F :=
    match z with Z0 => zero | Zpos x => F_of_pos x | Zneg x => opp (F_of_pos x) end.

  (* α = lcm(1, …, k)² *)
  Definition alpha_Z (k : nat) : Z :=
    let l := List.fold_right (fun i acc => Z.lcm (Z.of_nat i) acc) 1%Z (List.seq 1 k) in
    (l * l)%Z.

  (* the Lagrange coefficient c_l = ∏_{i ∈ Δ, i ≠ l} i / (i − l), in the field *)
  Definition lagrange (delta : list nat) (l : nat) : F :=
    List.fold_right (fun i acc =>
      if Nat.eqb i l then acc
      else mul acc (mul (nat_to_F i) (inv (sub (nat_to_F i) (nat_to_F l)))))
      one delta.

  (* the published proof of party l: its decryption factors, the
    commitment (y'_l, B'_l) and the reply k_l *)
  Record dec_proof : Type := mk_dec_proof {
    dfs : Vector.t G M;
    dy' : G;
    dB' : G;
    dk : F
  }.

  (* The random oracles of Algorithm 22, as functions of the data they
    hash: e from RO_seed(ρ | node(node(g, w), node(Γ, (f_1, …, f_k)))) and
    v from RO_challenge(ρ | node(leaf(s), node(τ_1, …, τ_k))). *)
  Record dec_oracles : Type := mk_dec_oracles {
    oracle_dec_es : Vector.t ciphertext M -> list G -> list dec_proof -> Vector.t F M;
    oracle_dec_v : Vector.t ciphertext M -> list G -> list dec_proof -> F
  }.

  Definition gprod_list (xs : list G) : G := List.fold_right gop gid xs.
  Definition fsum_list (xs : list F) : F := List.fold_right add zero xs.

  (* the parties in Δ, with their combining exponents α·c_l *)
  Definition selected (k : nat) (delta : list nat) (parties : list (nat * dec_proof)) :
    list (F * dec_proof) :=
    let alpha := F_of_Z (alpha_Z k) in
    List.map (fun '(l, pf) => (mul alpha (lagrange delta l), pf))
      (List.filter (fun '(l, _) => List.existsb (Nat.eqb l) delta) parties).

  (* the combined decryption factors f_i = ∏_{l ∈ Δ} f_l,i^{α c_l} *)
  Definition combined_factors (sel : list (F * dec_proof)) : Vector.t G M :=
    List.fold_right (fun '(c, pf) acc => Vector.map2 gop (Vector.map (fun x => gpow x c) (dfs pf)) acc)
      (Vector.const gid M) sel.

  (* Algorithm 22 with Algorithm 27's plaintext check: g the generator,
    y = Γ_0 the joint public key, L the ciphertexts to decrypt, parties
    the proofs of all k parties (indices from 1), Δ the selected parties,
    m the published plaintexts *)
  Definition verify_decryption (g y : G) (O : dec_oracles) (L : Vector.t ciphertext M)
    (Gamma : list G) (parties : list (nat * dec_proof)) (delta : list nat)
    (m : Vector.t G M) : bool :=
    let k := length parties in
    let all := List.map snd parties in
    let es := oracle_dec_es O L Gamma all in
    let v := oracle_dec_v O L Gamma all in
    let sel := selected k delta parties in
    let y' := gprod_list (List.map (fun '(c, pf) => gpow (dy' pf) c) sel) in
    let B' := gprod_list (List.map (fun '(c, pf) => gpow (dB' pf) c) sel) in
    let kx := fsum_list (List.map (fun '(c, pf) => mul c (dk pf)) sel) in
    let f := combined_factors sel in
    let U := gexp (Vector.map fst L) es in
    let B := gexp f es in
    generalised_cp_accepting_conversations (gop := gop) (gpow := gpow) (Gdec := Gdec) g U y (ginv B)
      (mk_sigma _ _ _ [y'; B'] [opp v] [kx]) &&
    (* m_i = v_i · f_i *)
    Vector.fold_right andb (Vector.map2 (fun mi vf => if Gdec mi vf then true else false)
      m (Vector.map2 (fun c fi => gop (snd c) fi) L f)) true.

  (* A verified joint decryption is an accepting Chaum–Pedersen transcript
    for (y, B^{−1}) = (g, U)^x with the combined announcement, challenge −v
    and combined response. *)
  Theorem verify_decryption_accepting : forall g y O L Gamma parties delta m,
    verify_decryption g y O L Gamma parties delta m = true ->
    let k := length parties in
    let all := List.map snd parties in
    let es := oracle_dec_es O L Gamma all in
    let v := oracle_dec_v O L Gamma all in
    let sel := selected k delta parties in
    let f := combined_factors sel in
    generalised_cp_accepting_conversations (gop := gop) (gpow := gpow) (Gdec := Gdec) g (gexp (Vector.map fst L) es) y
      (ginv (gexp f es))
      (mk_sigma _ _ _
        [gprod_list (List.map (fun '(c, pf) => gpow (dy' pf) c) sel);
         gprod_list (List.map (fun '(c, pf) => gpow (dB' pf) c) sel)]
        [opp v] [fsum_list (List.map (fun '(c, pf) => mul c (dk pf)) sel)]) = true.
  Proof.
    intros * h; unfold verify_decryption in h.
    apply andb_true_iff in h; destruct h as [h _]. exact h.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Algorithm 28 for a mixing session                                 *)
  (* ---------------------------------------------------------------- *)

  Definition verify_mixing (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (OD : dec_oracles) (L0 : Vector.t ciphertext M) (steps : list step)
    (Gamma : list G) (parties : list (nat * dec_proof)) (delta : list nat)
    (m : Vector.t G M) : bool :=
    verify_shuffling g hs pk O L0 steps &&
    (match Gamma with
     | List.cons y _ => (if Gdec y (snd pk) then true else false) &&
        verify_decryption g y OD (List.last (List.map fst steps) L0) Gamma parties delta m
     | List.nil => false
     end).

End Verificatum.
