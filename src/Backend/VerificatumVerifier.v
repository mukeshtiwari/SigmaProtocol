(** * Verifier for Verificatum mix-net proofs of shuffle and decryption *)

(** This file is an executable verifier for the zero-knowledge proofs
    produced by the Verificatum mix-net (VMN 3.1.0), following
    D. Wikström, ‘How to Implement a Stand-alone Verifier for the
    Verificatum Mix-Net’ (the vmnv manual). It covers key width 1 and
    ciphertext width 1 over a prime-order group, without pre-computation.
    The extracted verifier is driven by src/Executable/Vmnverifier and run
    on real Verificatum output (bench/verificatum-diff).

    Proof of a shuffle (Algorithm 19). For one mix-server with input list
    [w] and output list [w'], the proof is the Terelius–Wikström protocol
    (AFRICACRYPT 2010). The verifier derives a batching vector [e] and a
    challenge [v] by random oracles and accepts iff

    [[
      A^v A' = g^{k_A} ∏ h_i^{k_E,i}          C^v C' = g^{k_C}
      D^v D' = g^{k_D}                         B_i^v B'_i = g^{k_B,i} B_{i-1}^{k_E,i}
      F^v F' = Enc_pk(1, −k_F) ∏ w'_i^{k_E,i}
    ]]

    These five equations are precisely the generalised Okamoto acceptance
    test in the product space [V] of [Sigma.ShuffleTW] for the transcript
    with announcement [(A', C', D', B', F')], challenge [v] and response
    [(k_A, k_C, k_D, k_F, k_B, k_E)]: Verificatum writes responses as
    [ω + v·x], which matches the library convention. So [verify_pos] is
    literally [tw_verify], and [verify_pos_accepting] holds by
    definition. The soundness properties used are [tw_special_soundness]
    and [tw_relation_iff] ([Sigma.ShuffleTW]) and the idealised
    extraction theorem [tw_soundness] ([Sigma.ShuffleTWSound2]).

    Shuffling session (Algorithm 25). [verify_shuffling] runs over all
    mix-servers: each server must either give a valid proof or leave the
    list unchanged, and at least one proof must be valid
    ([verify_shuffling_spec]).

    Joint decryption (Algorithm 22, with the plaintext check of
    Algorithm 27). Party [l] publishes decryption factors
    [f_{l,i} = u_i^{−x_l/α}] with [α = lcm(1..k)²] (so that [α·c_l] is an
    integer for every Lagrange coefficient [c_l]), a commitment
    [(y'_l, B'_l)] and a reply [k_l]. The verifier combines the parties in
    [Δ] with exponents [α·c_l] and checks one Chaum–Pedersen equation pair
    for the combined values, as in VMN's
    [DistrElGamalSessionBasic.verifyCombined]; the plaintexts must be
    [m_i = v_i · f_i]. [verify_decryption_accepting] states that an accepted
    decryption is an accepting Chaum–Pedersen transcript with challenge
    [−v] for [(y, B⁻¹) = (g, U)^x]. The combining exponents are computed in
    the field [F], which is harmless because the group has order [|F|].

    How the challenges are derived. The random oracles are parameters
    ([pos_oracles], [dec_oracles]). The OCaml driver implements
    Verificatum's byte-tree encoding, SHA-256 based random oracles and PRG,
    derives the independent generators [h], and passes the oracles as
    functions of the data they hash. Unlike the credential verifiers there
    is no hash comparison here: the challenge is recomputed and plugged into
    the verification equations, exactly as in the manual.

    What is NOT verified. The Fiat–Shamir step (random oracle model) and
    the oracle implementations, byte-tree parsing, derivation of the
    generators and the group-membership and field-range checks of the
    inputs are done by the unverified OCaml driver and are outside the
    formal statements. Only the first element of [Gamma] (the joint public key) is
    compared with the shuffle public key; the per-party public keys in the
    tail of [Gamma] only enter through the oracles, so a party's individual
    decryption proof is not checked separately (only the combined one,
    as VMN does). Each theorem here is a link to an interactive protocol;
    soundness of the non-interactive proof is not formalised. *)
From Stdlib Require Import Utf8 Vector List Bool Lia PeanoNat ZArith.
From Algebra Require Import Hierarchy.
From Sigma Require Import Sigma Okamoto MultiExp ShuffleTW ChaumPedersen EqSigma.
From Utility Require Import Util.
Import VectorNotations.

(** ** Proof of a shuffle of one mix-server *)

(** Parameters: the field [F] and prime-order group [G] (as an
    [F]-vector space), and [N] with [M = N + 1] ciphertexts. *)
Section Verificatum.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {G : Type} {gid : G} {ginv : G -> G} {gop : G -> G -> G} {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}
    {Hvec : @vector_space F (@eq F) zero one add mul sub div opp inv
      G (@eq G) gid ginv gop gpow}
    {N : nat}.

  (** [M = N + 1] is the number of ciphertexts, a ciphertext is an
      ElGamal pair [(u, v) = (g^s, y^s·m)], [nwit = 4 + 2M] is the length
      of the response vector, and [V] is the statement space of
      [Sigma.ShuffleTW]. *)
  Local Notation M := (S N).
  Local Notation ciphertext := (G * G)%type.
  Local Notation nwit := (Nat.add 4 (Nat.add M M)).
  Local Notation V := (@ShuffleTW.V G N).

  (** The published proof of a shuffle of one mix-server: the
      permutation commitment [pu] (μ in the manual); the proof commitment
      τ, consisting of the bridging commitments [pB] and the announcement
      [(pA', pB', pC', pD', pF')]; and the reply σ, the responses
      [(kA, kB, kC, kD, kE, kF)]. *)
  Record pos_proof : Type := mk_pos_proof {
    pu : Vector.t G M;
    pB : Vector.t G M;
    pA' : G;
    pB' : Vector.t G M;
    pC' : G;
    pD' : G;
    pF' : ciphertext;
    kA : F;
    kB : Vector.t F M;
    kC : F;
    kD : F;
    kE : Vector.t F M;
    kF : F
  }.

  (** The two random oracles of Algorithm 19 as functions of the data they
      hash. [oracle_es] returns the batching vector
      [e = PRG(RO_seed(ρ | node(g, h, u, pk, w, w')))] from the permutation
      commitment and the two lists; [oracle_v] returns the challenge
      [v = RO_challenge(ρ | node(leaf(s), τ))]. The driver fixes [ρ], [g],
      [h] and [pk] in the closures. *)
  Record pos_oracles : Type := mk_pos_oracles {
    oracle_es : Vector.t G M -> Vector.t ciphertext M -> Vector.t ciphertext M -> Vector.t F M;
    oracle_v : Vector.t G M -> Vector.t ciphertext M -> Vector.t ciphertext M -> pos_proof -> F
  }.

  (** The public data of the Terelius–Wikström statement assembled from
      the proof: generator [g], [h_0 = hd hs], the generators [hs], the
      second component of the public key [pk], the commitment, the batching
      vector [es], the bridging commitments, and the input and output
      lists. *)
  Definition pos_public (g : G) (hs : Vector.t G M) (pk : ciphertext)
    (w w' : Vector.t ciphertext M) (es : Vector.t F M) (pf : pos_proof) : @public F G N :=
    @ShuffleTW.mk_public F G N g (Vector.hd hs) hs (snd pk) (pu pf) es (pB pf) w w'.

  (** The announcement [(A', C', D', B', F')] as an element of [V]. *)
  Definition pos_announcement (pf : pos_proof) : V :=
    (pA' pf, (pC' pf, (pD' pf, (pB' pf, pF' pf)))).

  (** The response vector in the coordinate order of [Sigma.ShuffleTW]:
      [(k_A, k_C, k_D, k_F) ++ k_B ++ k_E]. *)
  Definition pos_response (pf : pos_proof) : Vector.t F nwit :=
    [kA pf; kC pf; kD pf; kF pf] ++ kB pf ++ kE pf.

  (** The full transcript [(announcement; v; responses)]. *)
  Definition pos_transcript (v : F) (pf : pos_proof) : @sigma_proto F V 1 1 nwit :=
    mk_sigma _ _ _ [pos_announcement pf] [v] (pos_response pf).

  (** Algorithm 19: computes [e] and [v] with the oracles and runs
      [tw_verify] (the generalised Okamoto verifier at [V]) on the
      resulting statement and transcript. *)
  Definition verify_pos (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (w w' : Vector.t ciphertext M) (pf : pos_proof) : bool :=
    let es := oracle_es O (pu pf) w w' in
    let v := oracle_v O (pu pf) w w' pf in
    tw_verify (one := one) (mul := mul)
      (gid := gid) (ginv := ginv) (gop := gop) (gpow := gpow) (Gdec := Gdec)
      (pos_public g hs pk w w' es pf) (pos_transcript v pf).

  (** A verified proof of a shuffle is an accepting transcript of the
      generalised Okamoto protocol for [bases P] and [target P]; by
      [tw_relation_iff] this is the conjunction of the five verification
      equations. Holds by unfolding: [verify_pos] is [tw_verify]. *)
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

  (** ** Shuffling by all mix-servers (Algorithm 25) *)

  (** Boolean equality of ciphertexts. *)
  Definition ciphertext_eqb (c d : ciphertext) : bool :=
    match Gdec (fst c) (fst d), Gdec (snd c) (snd d) with
    | left _, left _ => true | _, _ => false
    end.

  (** Boolean equality of ciphertext lists of length [M]. *)
  Definition list_eqb (L L' : Vector.t ciphertext M) : bool :=
    Vector.fold_right andb (Vector.map2 ciphertext_eqb L L') true.

  (** [ciphertext_eqb] reflects equality. *)
  Lemma ciphertext_eqb_eq : forall c d, ciphertext_eqb c d = true <-> c = d.
  Proof.
    intros [a b] [c d]; unfold ciphertext_eqb; cbn [fst snd].
    destruct (Gdec a c) as [-> | h]; [destruct (Gdec b d) as [-> | h'] |].
    + split; reflexivity.
    + split; [discriminate | intro e; exfalso; apply h'; congruence].
    + split; [discriminate | intro e; exfalso; apply h; congruence].
  Qed.

  (** The fold of [ciphertext_eqb] over two lists reflects equality of the
      lists. Proof by induction on the length; the cons case uses
      [inj_pair2_eq_dec] to invert vector equality. *)
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

  (** One step per mix-server: its output list and its proof. *)
  Definition step : Type := (Vector.t ciphertext M * pos_proof)%type.

  (** [check_steps g hs pk O L steps] walks the mix-servers starting from
      input [L] and returns the number of valid proofs and whether every
      rejected proof left the list unchanged. *)
  Fixpoint check_steps (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (L : Vector.t ciphertext M) (steps : list step) : nat * bool :=
    match steps with
    | List.nil => (0, true)
    | List.cons (L', pf) rest =>
        let ok := verify_pos g hs pk O L L' pf in
        let '(n, b) := check_steps g hs pk O L' rest in
        ((if ok then S n else n), b && (ok || list_eqb L L'))
    end.

  (** Algorithm 25: accept iff every rejected proof left the list unchanged
      and at least one proof is valid. [L0] is the input list; the last
      step's list is the output. *)
  Definition verify_shuffling (g : G) (hs : Vector.t G M) (pk : ciphertext) (O : pos_oracles)
    (L0 : Vector.t ciphertext M) (steps : list step) : bool :=
    let '(n, b) := check_steps g hs pk O L0 steps in
    b && (1 <=? n).

  (** The sequence of lists [L_0, L_1, …, L_λ]. *)
  Definition lists (L0 : Vector.t ciphertext M) (steps : list step) : list (Vector.t ciphertext M) :=
    List.cons L0 (List.map fst steps).

  (** Invariant of [check_steps]: if the boolean is [true], every step [i]
      either has a verified proof from list [i] to list [i+1] or leaves the
      list unchanged; and if the counter is positive, some step has a
      verified proof. Proof by induction on [steps]. *)
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

  (** Specification of [verify_shuffling]: if it accepts, each server
      either produced a verified proof of a shuffle from its input to its
      output list or left the list unchanged, and at least one server
      produced a verified proof. Combined with [tw_soundness], the final
      list is a re-encryption and permutation of [L0] unless a discrete
      logarithm relation among the generators is known (in the idealised
      extraction setting of that theorem). *)
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

  (** ** Joint decryption (Algorithm 22) *)

  (** [gexp] is multi-exponentiation [∏ g_i^{x_i}]. *)
  Local Notation gexp := (mexp (vid := gid) (vadd := gop) (smul := gpow)).

  (** The natural number [n] as a field element. *)
  Fixpoint nat_to_F (n : nat) : F :=
    match n with 0 => zero | S n' => add one (nat_to_F n') end.

  (** Binary conversion of a positive integer into the field by doubling,
      and its extension [F_of_Z] to all integers. *)
  Fixpoint F_of_pos (x : positive) : F :=
    match x with
    | xH => one
    | xO x' => let y := F_of_pos x' in add y y
    | xI x' => let y := F_of_pos x' in add (add y y) one
    end.

  Definition F_of_Z (z : Z) : F :=
    match z with Z0 => zero | Zpos x => F_of_pos x | Zneg x => opp (F_of_pos x) end.

  (** [alpha_Z k = lcm(1, …, k)²], the integer that makes all Lagrange
      combining exponents integral in VMN. *)
  Definition alpha_Z (k : nat) : Z :=
    let l := List.fold_right (fun i acc => Z.lcm (Z.of_nat i) acc) 1%Z (List.seq 1 k) in
    (l * l)%Z.

  (** The Lagrange coefficient [c_l = ∏_{i ∈ Δ, i ≠ l} i / (i − l)] computed
      in the field. *)
  Definition lagrange (delta : list nat) (l : nat) : F :=
    List.fold_right (fun i acc =>
      if Nat.eqb i l then acc
      else mul acc (mul (nat_to_F i) (inv (sub (nat_to_F i) (nat_to_F l)))))
      one delta.

  (** The published decryption proof of one party: decryption factors
      [dfs], commitment [(dy', dB')] and reply [dk]. *)
  Record dec_proof : Type := mk_dec_proof {
    dfs : Vector.t G M;
    dy' : G;
    dB' : G;
    dk : F
  }.

  (** The random oracles of Algorithm 22: [oracle_dec_es] gives the
      batching vector from [RO_seed(ρ | node(node(g, w), node(Γ, f)))],
      [oracle_dec_v] the challenge from
      [RO_challenge(ρ | node(leaf(s), node(τ_1, …, τ_k)))]. *)
  Record dec_oracles : Type := mk_dec_oracles {
    oracle_dec_es : Vector.t ciphertext M -> list G -> list dec_proof -> Vector.t F M;
    oracle_dec_v : Vector.t ciphertext M -> list G -> list dec_proof -> F
  }.

  (** Product of a list of group elements and sum of a list of field
      elements. *)
  Definition gprod_list (xs : list G) : G := List.fold_right gop gid xs.
  Definition fsum_list (xs : list F) : F := List.fold_right add zero xs.

  (** The parties in [Δ] (indices from 1) with their combining exponents
      [α·c_l], where [k] is the total number of parties. *)
  Definition selected (k : nat) (delta : list nat) (parties : list (nat * dec_proof)) :
    list (F * dec_proof) :=
    let alpha := F_of_Z (alpha_Z k) in
    List.map (fun '(l, pf) => (mul alpha (lagrange delta l), pf))
      (List.filter (fun '(l, _) => List.existsb (Nat.eqb l) delta) parties).

  (** The combined decryption factors [f_i = ∏_{l ∈ Δ} f_{l,i}^{α c_l}]. *)
  Definition combined_factors (sel : list (F * dec_proof)) : Vector.t G M :=
    List.fold_right (fun '(c, pf) acc => Vector.map2 gop (Vector.map (fun x => gpow x c) (dfs pf)) acc)
      (Vector.const gid M) sel.

  (** Algorithm 22 with the plaintext check of Algorithm 27. Inputs: the
      generator [g], the joint public key [y], the oracles, the ciphertexts
      [L], the public keys [Gamma], the proofs of all parties, the selected
      set [Δ] and the claimed plaintexts [m]. It combines
      [y' = ∏ y'_l^{α c_l}], [B' = ∏ B'_l^{α c_l}], [k = Σ α c_l k_l] and
      [f], sets [U = ∏ u_i^{e_i}] and [B = ∏ f_i^{e_i}], and accepts iff the
      Chaum–Pedersen check [g^k = y' · y^{−v}], [U^k = B' · B^{v}]
      passes (i.e. challenge [−v] for [(y, B⁻¹)]) and [m_i = v_i · f_i] for
      every [i]. *)
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
    Vector.fold_right andb (Vector.map2 (fun mi vf => if Gdec mi vf then true else false)
      m (Vector.map2 (fun c fi => gop (snd c) fi) L f)) true.

  (** A verified joint decryption gives an accepting Chaum–Pedersen
      transcript for the statement [(y, B⁻¹) = (g, U)^x] with the combined
      announcement, challenge [−v] and combined response. Special soundness
      of [Sigma.ChaumPedersen] then yields [x] with [y = g^x] and
      [B = U^{−x}] from two such transcripts. The plaintext equations are
      not restated. *)
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

  (** ** Mixing session (Algorithm 28) *)

  (** Accepts iff the shuffling verifies, [Gamma] is non-empty, its first
      element (the joint public key) equals the second component of the
      shuffle public key [pk], and the decryption of the final list (the
      last step's output, or [L0] if there are no steps) to [m]
      verifies. *)
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
