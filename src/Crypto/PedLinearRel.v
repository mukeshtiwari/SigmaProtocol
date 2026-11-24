(** * A linear relation on values hidden in Pedersen commitments *)

(** This file formalises a Sigma protocol proving that the values hidden in
    a vector of Pedersen commitments satisfy a public linear equation. The
    public input is two generators [g], [h], a coefficient vector
    [αs = (α_1, ..., α_m)] with [m = 2 + n ≥ 2], commitments
    [cs = (C_1, ..., C_m)] and a value [z]; the prover knows openings
    [(v_i, r_i)] with

    [[
      C_i = g^(v_i) · h^(r_i)  for all i,     and     Σ_i α_i · v_i = z.
    ]]

    One run of the protocol:

    - the prover picks random [u_i], [w_i] and sends
      [A_i = g^(u_i) · h^(w_i)] for each [i] and [A_0 = g^(Σ_i α_i·u_i)];
    - the verifier sends a challenge [c];
    - the prover answers [s_i = u_i + c·v_i] and [t_i = w_i + c·r_i];
    - the verifier checks [g^(s_i) · h^(t_i) = A_i · C_i^c] for all [i] and
      [g^(Σ_i α_i·s_i) = A_0 · g^(c·z)].

    The transcript uses the generic [sigma_proto] record of [Sigma] with
    [m + 1] commitments, one challenge and [2m] responses ([s] followed by
    [t]).

    Main results:

    - completeness: [pedersen_linear_relation_completeness];
    - special soundness: [pedersen_linear_relation_special_soundness]
      extracts openings [(v_i, r_i)] of all commitments, together with the
      linear relation [Σ α_i·v_i = z], unless [g] is the identity (a
      degenerate case that the statement makes explicit as a disjunct);
    - special honest-verifier zero knowledge: the weak form
      [generalised_pedersen_special_honest_verifier_zkp] (acceptance bits
      and probabilities agree) and the strong forms
      [generalised_pedersen_special_honest_verifier_zkp_perm] and
      [generalised_pedersen_special_honest_verifier_zkp_enum] (the real and
      simulated transcript distributions are permutations of each other).

    The protocol is instantiated in [Examples/PedLinearRelIns.v] and
    extracted to OCaml through [Extraction/PedLinearRellib]. *)
From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef
  BinPos Permutation.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import
  Prob Distr.
From Utility Require Import Util.
From ExtLib Require Import Monad.
From Sigma Require Import Sigma.

Import MonadNotation
  VectorNotations.

#[local] Open Scope monad_scope.

(** ** Setting

    A field [F] of exponents and a group [G] with exponentiation [gpow]
    (written [^]); the vector-space axioms are assumed later, in section
    [Proofs]. *)
Section DL.
  (** The field of exponents with decidable equality [Fdec]. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}.

  (** The group with identity [gid], inverse [ginv], operation [gop],
      exponentiation [gpow] and decidable equality [Gdec]. *)
  Context
    {G : Type}
    {gid : G}
    {ginv : G -> G}
    {gop : G -> G -> G}
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}.

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  (** [(a; c; r)] builds a transcript from commitment, challenge and
      response vectors. *)
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  (** ** Prover, simulator and verifier *)
  Section PedLinearRelation.

    Section Def.

      (** Coordinate-wise Pedersen commitments [C_i = g^(v_i) · h^(r_i)] to the
          values [vs] with randomness [rs]. *)
      Definition pedersen_commitment_vector {n : nat}
        (g h : G) (vs rs : Vector.t F (2 + n)) : Vector.t G (2 + n).
      Proof.
        refine(zip_with (fun v r => gop (g^v) (h^r)) vs rs).
      Defined.

      (** The prover's first message. The randomness vector [usws] is split into
          [us] and [ws]; the result is the [m] commitments
          [g^(u_i) · h^(w_i)] followed by [g^(Σ_i α_i·u_i)]. *)
      Definition construct_pedersen_linear_relation_commitment {n : nat}
        (g h : G) (αs : Vector.t F (2 + n))
        (usws : Vector.t F ((2 + n) + (2 + n))) : Vector.t G ((2 + n) + 1).
      Proof.
        destruct (splitat (2 + n) usws) as (us & ws).
        set (comm₁ := pedersen_commitment_vector g h us ws).
        set (comm₂ := g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc)
        (zip_with pair αs us) zero)).
        exact (comm₁ ++ [comm₂]).
      Defined.

      (** An honest transcript with witness [(vs, rs)], randomness [usws] and
          challenge [c]: the commitment above, challenge [c], and responses
          [u_i + c·v_i] followed by [w_i + c·r_i]. *)
      Definition construct_pedersen_linear_relation_generalised_real_proof
        {n : nat} (g h : G) (αs : Vector.t F (2 + n))
        (usws : Vector.t F ((2 + n) + (2 + n)))
        (vs rs : Vector.t F (2 + n)) (c : F) :
        @sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n)).
      Proof.
        destruct (splitat (2 + n) usws) as (us & ws).
        set (comm := construct_pedersen_linear_relation_commitment g h αs usws).
        set (res₁ := zip_with (fun u v => u + c * v) us vs).
        set (res₂ := zip_with (fun w r => w + c * r) ws rs).
        exact (comm; [c]; res₁ ++ res₂).
      Defined.

      (** The simulator. It uses [usws] directly as the responses [(s, t)] and
          solves the verification equations for the commitments:
          [A_i = g^(s_i) · h^(t_i) · C_i^(−c)] and
          [A_0 = g^(Σ_i α_i·s_i) · (g^(−z))^c]. No witness is needed. *)
      Definition construct_pedersen_linear_relation_generalised_simulator_proof
        {n : nat} (g h : G) (αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (z : F)
        (usws : Vector.t F ((2 + n) + (2 + n))) (c : F) :
        @sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n)).
      Proof.
        destruct (splitat (2 + n) usws) as (us & ws).
        set (comm₁ :=
          zip_with (fun '(u, w) com => gop (gop (g^u) (h^w)) (com^(opp c)))
          (zip_with pair us ws) cs).
        set (comm₂ := gop (g^((Vector.fold_right (fun '(α, u) acc => α * u + acc)
        (zip_with pair αs us) zero))) ((g^(opp z))^c)).
        exact (comm₁ ++ [comm₂]; [c]; usws).
      Defined.

      (** The verifier, given [z], [αs] and [cs]: split the commitment into the
          [m] values [A_i] and [A_0], split the responses into [s] and [t], and
          accept iff

          - [g^(s_i) · h^(t_i) = A_i · C_i^c] for every [i] (checked with
            [vector_forallb]), and
          - [g^(Σ_i α_i·s_i) = A_0 · g^(c·z)]. *)
      Definition verify_pedersen_linear_relation_generalised_proof {n : nat}
        (g h : G) : F -> Vector.t F (2 + n) -> Vector.t G (2 + n) ->
        @sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n)) -> bool.
      Proof.
        intros z αs cs pf.
        refine
        (match pf as pf' in sigma_proto
          return pf = pf' -> bool
        with
        |(comm; cha; res) => fun ha => _
        end eq_refl).
        destruct (splitat (2 + n) comm) as (comm₁ & comm₂).
        destruct (splitat (2 + n) res) as (res₁ & res₂).
        set (ret₁ := vector_forallb (fun '((vi, ri), (comi, csi)) =>
          match
            Gdec (gop (g^vi) (h^ri)) (gop comi (csi^(hd cha)))
          with
          | left _ => true
          | right _ => false
          end)
        (zip_with pair
          (zip_with pair res₁ res₂)
          (zip_with pair comm₁ cs))).
        set (ret₂ :=
          match Gdec (g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc)
          (zip_with pair αs res₁) zero)) (gop (hd comm₂) (g ^ (hd cha * z)))
          with
          | left _ => true
          | right _ => false
          end).
        exact (ret₁ && ret₂).
      Defined.

      (** Distribution of honest transcripts for a fixed challenge [c]: draw the
          [2m] random values uniformly with replacement from [lf] and run the
          honest prover. *)
      Definition generalised_pedersen_linear_relation_distribution
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
        (αs : Vector.t F (2 + n))
        (vs rs : Vector.t F (2 + n)) (g h : G)
        (c : F) : dist (@sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n))) :=
        usws <- repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) ((2 + n) + (2 + n)) ;;
        Ret (construct_pedersen_linear_relation_generalised_real_proof
          g h αs usws vs rs c).

      (** Distribution of simulated transcripts: draw the [2m] responses
          uniformly from [lf] and run the simulator. *)
      Definition generalised_pedersen_linear_relation_simulator_distribution
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
        (g h : G) (αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (z : F)
        (c : F) : dist (@sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n))) :=
        usws <- repeat_dist_ntimes_vector
          (uniform_with_replacement lf Hlfn) ((2 + n) + (2 + n)) ;;
        Ret (construct_pedersen_linear_relation_generalised_simulator_proof
          g h αs cs z usws c).

    End Def.

    (** ** Security properties *)
    Section Proofs.

      (** Specification of the verifier (soundness direction): if a transcript
          of shape [(A ++ [A_0]; [c]; s ++ t)] is accepted, then
          [g^(s_i) · h^(t_i) = A_i · C_i^c] for every [i] and
          [g^(Σ α_i·s_i) = A_0 · g^(c·z)]. *)
      Theorem pedersen_linear_relation_verification_function_correctness_forward :
        ∀ (n : nat) (g h : G) (z : F) (αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (comm₁ : Vector.t G (2 + n))
        (comm₂ : G) (c : F) (res₁ res₂ : Vector.t F (2 + n)),
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
        (comm₁ ++ [comm₂]; [c]; res₁ ++ res₂) = true ->
        (∀ (i : Fin.t (2 + n)),
          gop (g ^ (nth res₁ i)) (h ^ (nth res₂ i)) =
          gop (nth comm₁ i) ((nth cs i) ^ c)) ∧
        g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc)
          (zip_with pair αs res₁) zero) =
        gop (comm₂) (g ^ (c * z)).
      Proof.
        intros * ha.
        unfold  verify_pedersen_linear_relation_generalised_proof in ha.
        rewrite !VectorSpec.splitat_append in ha.
        eapply andb_true_iff in ha.
        destruct ha as (hal & har).
        rewrite dec_true in har.
        split. intro i.
        rewrite vector_forallb_correct in hal.
        specialize (hal i).
        rewrite !nth_zip_with, dec_true in hal.
        exact hal. exact har.
      Qed.

      (** Specification of the verifier (completeness direction): if both
          verification equations hold, the transcript is accepted. *)
      Theorem pedersen_linear_relation_verification_function_correctness_backward :
        ∀ (n : nat) (g h : G) (z : F) (αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (comm₁ : Vector.t G (2 + n))
        (comm₂ : G) (c : F) (res₁ res₂ : Vector.t F (2 + n)),
        (∀ (i : Fin.t (2 + n)),
          gop (g ^ (nth res₁ i)) (h ^ (nth res₂ i)) =
          gop (nth comm₁ i) ((nth cs i) ^ c)) ->
        g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc)
          (zip_with pair αs res₁) zero) =
        gop (comm₂) (g ^ (c * z)) ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
        (comm₁ ++ [comm₂]; [c]; res₁ ++ res₂) = true.
      Proof.
        intros * ha hb.
        unfold  verify_pedersen_linear_relation_generalised_proof.
        rewrite !VectorSpec.splitat_append.
        eapply andb_true_iff.
        split.
        eapply vector_forallb_correct.
        intro i. rewrite !nth_zip_with, dec_true.
        eapply ha.
        rewrite dec_true.
        exact hb.
      Qed.

      (** From here on [F] and [G] form a vector space. *)
      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (** Rearrangement in the abelian group: [(a·b)·(c·d) = (a·c)·(b·d)]. *)
      Theorem gop_simp : ∀ (a b c d : G),
        gop (gop a b) (gop c d) = gop (gop a c) (gop b d).
      Proof.
        intros *.
        rewrite <-!associative.
        setoid_rewrite commutative at 2.
        rewrite <-!associative.
        setoid_rewrite commutative at 3.
        reflexivity.
      Qed.

      (** Linearity of the weighted sum in its second argument:
          [Σ α_i·(u_i + c·v_i) = Σ α_i·u_i + c·Σ α_i·v_i]. *)
      Theorem fold_right_zip :
        ∀ (n : nat) (αs us vs : Vector.t F n) (c : F),
        fold_right (λ '(α, u) (acc : F), α * u + acc)
          (zip_with pair αs (zip_with (λ u v : F, u + c * v) us vs)) zero =
        (fold_right (λ '(α, u) (acc : F), α * u + acc) (zip_with pair αs us) zero +
        c * fold_right (λ '(α, v) (acc : F), α * v + acc) (zip_with pair αs vs)
        zero).
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          pose proof (vector_inv_0 αs) as ha.
          pose proof (vector_inv_0 us) as hb.
          pose proof (vector_inv_0 vs) as hc.
          subst; cbn. field.
        +
          intros *.
          destruct (vector_inv_S αs) as (αsh & αst & ha).
          destruct (vector_inv_S us) as (ush & ust & hb).
          destruct (vector_inv_S vs) as (vsh & vst & hc).
          subst. cbn.
          set (ca := fold_right (λ '(α, u) (acc : F), α * u + acc) (zip_with pair αst ust) zero).
          set (cb := fold_right (λ '(α, v) (acc : F), α * v + acc) (zip_with pair αst vst) zero).
          assert (ha : c * (αsh * vsh + cb) = c * αsh * vsh + c * cb). field.
          rewrite ha; clear ha.
          assert (ha : αsh * ush + ca + (c * αsh * vsh + c * cb) =
            αsh * ush + c * αsh * vsh + (ca + c * cb)). field.
          rewrite ha. clear ha.
          f_equal. field. unfold ca, cb.
          now rewrite ihn.
      Qed.

      (** *** Completeness

          If [cs] are Pedersen commitments to [vs] with randomness [rs] and
          [z = Σ α_i·v_i], every honest transcript is accepted, for any randomness
          and challenge. Each per-commitment check reduces to
          [g^(u + c·v) · h^(w + c·r) = g^u · h^w · (g^v · h^r)^c] and the linear
          check to [fold_right_zip]. *)
      Theorem pedersen_linear_relation_completeness :
        ∀ (n : nat) (g h : G) (αs : Vector.t F (2 + n))
          (vs rs : Vector.t F ((2 + n))) (cs : Vector.t G (2 + n))
          (usws : Vector.t F ((2 + n) + (2 + n))) (c z : F),
        cs = pedersen_commitment_vector g h vs rs ->
        z = Vector.fold_right (fun '(α, v) acc => α * v + acc)
          (zip_with pair αs vs) zero ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
          (construct_pedersen_linear_relation_generalised_real_proof
            g h αs usws vs rs c) = true.
      Proof.
        intros * ha hb.
        unfold construct_pedersen_linear_relation_generalised_real_proof.
        destruct (splitat (2 + n) usws) as (us & ws) eqn:hc.
        unfold construct_pedersen_linear_relation_commitment.
        rewrite hc.
        set (comm₁ := pedersen_commitment_vector g h us ws).
        set (comm₂ := g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc)
                      (zip_with pair αs us) zero)).
        set (res₁ := zip_with (fun u v => u + c * v) us vs).
        set (res₂ := zip_with (fun w r => w + c * r) ws rs).
        eapply pedersen_linear_relation_verification_function_correctness_backward.
        -
          intro i.
          subst res₁ res₂ comm₁ cs.
          unfold pedersen_commitment_vector.
          rewrite !nth_zip_with.
          rewrite !smul_distributive_vadd, gop_simp,
          <-!smul_associative_fmul,
          <-!smul_distributive_fadd.
          assert (hd : c * vs[@i] = vs[@i] * c). field.
          rewrite !hd; clear hd.
          assert(hd : c * rs[@i] = rs[@i] * c). field.
          rewrite !hd. reflexivity.
        -
          subst res₁ z comm₂.
          rewrite <-!smul_distributive_fadd.
          rewrite fold_right_zip. reflexivity.
      Qed.

      (** Simulated transcripts are always accepted, for any [cs], [z], [αs]: the
          commitments were solved from the verification equations. *)
      Theorem pedersen_linear_relation_simulator_completeness :
        ∀ (n : nat) (g h : G) (αs : Vector.t F (2 + n))
          (cs : Vector.t G (2 + n)) (z c : F)
          (usws : Vector.t F ((2 + n) + (2 + n))),
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
          (construct_pedersen_linear_relation_generalised_simulator_proof
            g h αs cs z usws c) = true.
      Proof.
        intros n g h αs cs z c usws.
        unfold construct_pedersen_linear_relation_generalised_simulator_proof.
        destruct (splitat (2 + n) usws) as (us & ws) eqn:ha.
        eapply VectorSpec.append_splitat in ha.
        set (comm₁ := zip_with (fun '(u, w) com => gop (gop (g ^ u) (h ^ w)) (com ^ (opp c)))
          (zip_with pair us ws) cs).
        set (comm₂ := gop (g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc)
          (zip_with pair αs us) zero)) ((g ^ (opp z)) ^ c)).
        rewrite ha.
        eapply pedersen_linear_relation_verification_function_correctness_backward.
        -
          intro i. subst comm₁.
          rewrite !nth_zip_with.
          rewrite <-associative.
          rewrite <-smul_distributive_fadd.
          assert (hb : opp c + c = zero). field.
          rewrite hb; clear hb.
          rewrite field_zero, right_identity.
          reflexivity.
        -
          subst comm₂.
          rewrite <-associative, <-smul_associative_fmul,
           <-smul_distributive_fadd.
          assert (hb : (opp z * c + c * z) = zero). field.
          rewrite hb; clear hb.
          rewrite field_zero, right_identity.
          reflexivity.
      Qed.

      (** *** Special soundness

          Pulling a common factor out of the weighted sum:
          [Σ α_i·((u_i − v_i)·c) = c · Σ α_i·(u_i − v_i)]. *)
      Theorem fold_right_pull_out_inv :
        ∀ (n : nat) (αs us vs : Vector.t F n) (c : F),
        fold_right (λ '(α, v) (acc : F), α * v + acc)
          (zip_with pair αs (zip_with (λ r₁ r₂ : F, (r₁ - r₂) * c ) us vs)) zero =
        c * fold_right (λ '(α, v) (acc : F), α * v + acc)
          (zip_with pair αs (zip_with (λ r₁ r₂ : F, (r₁ - r₂)) us vs)) zero.
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          pose proof (vector_inv_0 αs) as ha.
          pose proof (vector_inv_0 us) as hb.
          pose proof (vector_inv_0 vs) as hc.
          subst; cbn. field.

        +
          intros *.
          destruct (vector_inv_S αs) as (αsh & αst & ha).
          destruct (vector_inv_S us) as (ush & ust & hb).
          destruct (vector_inv_S vs) as (vsh & vst & hc).
          subst. cbn.
          rewrite ihn.
          field.
      Qed.

      (** Linearity of the weighted sum with respect to subtraction:
          [Σ α_i·u_i − Σ α_i·v_i = Σ α_i·(u_i − v_i)]. *)
      Theorem fold_right_sub_distributive :
        ∀ (n : nat) (αs us vs : Vector.t F n),
        fold_right (λ '(α, u) (acc : F), α * u + acc) (zip_with pair αs us) zero -
        fold_right (λ '(α, u) (acc : F), α * u + acc) (zip_with pair αs vs) zero =
        fold_right (λ '(α, v) (acc : F), α * v + acc)
          (zip_with pair αs (zip_with (λ r₁ r₂ : F, r₁ - r₂) us vs)) zero.
      Proof.
        induction n as [|n ihn].
        +
          intros *.
          pose proof (vector_inv_0 αs) as ha.
          pose proof (vector_inv_0 us) as hb.
          pose proof (vector_inv_0 vs) as hc.
          subst; cbn. field.
        +
          intros *.
          destruct (vector_inv_S αs) as (αsh & αst & ha).
          destruct (vector_inv_S us) as (ush & ust & hb).
          destruct (vector_inv_S vs) as (vsh & vst & hc).
          subst. cbn.
          rewrite <-ihn.
          field.
      Qed.

      (** Special soundness: from two accepting transcripts with the same
          commitment and challenges [c₁ ≠ c₂], with responses [(s, t)] and
          [(s', t')], the vectors

          [[
            v_i = (s_i − s'_i) / (c₁ − c₂),     r_i = (t_i − t'_i) / (c₁ − c₂)
          ]]

          open every commitment, [C_i = g^(v_i) · h^(r_i)], and moreover either
          [z = Σ α_i·v_i] or [g = gid].

          Proof idea: dividing the per-commitment checks of the two transcripts
          gives [g^(s_i − s'_i) · h^(t_i − t'_i) = C_i^(c₁ − c₂)]; raising to
          [(c₁ − c₂)⁻¹] gives the openings. Dividing the linear checks gives
          [g^(Σ α_i·(s_i − s'_i) − z·(c₁ − c₂)) = gid], so either [g = gid] or the
          exponent is zero ([gid_power_zero]), which is the linear relation. *)
      Theorem pedersen_linear_relation_special_soundness :
        ∀ (n : nat) (g h : G) (αs : Vector.t F (2 + n))
          (cs : Vector.t G (2 + n)) (z : F)
          (comm : Vector.t G ((2 + n) + 1))
          (c₁ c₂ : F) (res₁ res₂ : Vector.t F ((2 + n) + (2 + n))),
        c₁ <> c₂ ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
          (comm; [c₁]; res₁) = true ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
          (comm; [c₂]; res₂) = true ->
        ∃ (vs rs : Vector.t F (2 + n)),
          (∀ (i : Fin.t (2 + n)),
            nth cs i = gop (g ^ (nth vs i)) (h ^ (nth rs i))) ∧
          (z = Vector.fold_right (fun '(α, v) acc => α * v + acc)
            (zip_with pair αs vs) zero ∨ g = gid).
      Proof.
        intros * ha hb hc.
        (* Split both response vectors and the commitment into their two parts. *)
        destruct (splitat (2 + n) res₁) as (res₁_a & res₁_b) eqn:hd.
        destruct (splitat (2 + n) res₂) as (res₂_a & res₂_b) eqn:he.
        destruct (splitat (2 + n) comm) as (comm_a & comm_b) eqn:hf.
        eapply VectorSpec.append_splitat in hd, he, hf.
        subst. destruct (vector_inv_S comm_b) as (comm_bh & comm_bt & hd).
        pose proof (vector_inv_0 comm_bt) as he.
        subst.
        eapply pedersen_linear_relation_verification_function_correctness_forward in
        hb, hc.
        destruct hb as (hbl & hbr).
        destruct hc as (hcl & hcr).
        (* The extracted openings: differences of responses divided by c₁ − c₂. *)
        exists (zip_with (fun r₁ r₂ => (r₁ - r₂) * inv (c₁ - c₂)) res₁_a res₂_a),
        (zip_with (fun r₁ r₂ => (r₁ - r₂) * inv (c₁ - c₂)) res₁_b res₂_b).
        split.
        -
          (* Openings: combine the i-th checks and cancel the common commitment A_i. *)
          intro i.
          rewrite !nth_zip_with.
          specialize (hbl i).
          specialize (hcl i).
          eapply f_equal with (f := ginv) in hcl.
          rewrite !group_inv_flip,
          !connection_between_vopp_and_fopp in hcl.
          rewrite commutative in hcl.
          pose proof (@rewrite_gop G gop _ _ _ _ hbl hcl) as hcom.
          rewrite gop_simp in hcom.
          rewrite <-!(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in hcom; try assumption.
          rewrite <-!ring_sub_definition in hcom.
          setoid_rewrite commutative in hcom at 3.
          rewrite gop_simp in hcom.
          rewrite <-!(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in hcom; try assumption.
          rewrite <-!ring_sub_definition in hcom.
          assert (hd : (gop comm_a[@i] (ginv comm_a[@i])) = gid).
          rewrite right_inverse; reflexivity.
          rewrite hd in hcom; clear hd.
          rewrite right_identity in hcom.
          apply f_equal with (f := fun x => x^(inv (c₁ - c₂))) in hcom.
          rewrite <-!smul_associative_fmul in hcom.
          assert (hd : ((c₁ - c₂) * inv (c₁ - c₂)) = one). field.
          intro hd. eapply ha.
          eapply f_equal with (f := fun x => x + c₂) in hd.
          rewrite left_identity in hd.
          rewrite <-hd. field.
          rewrite hd in hcom; clear hd.
          rewrite field_one in hcom.
          rewrite !smul_distributive_vadd, <-!smul_associative_fmul
          in hcom.
          rewrite <-hcom. reflexivity.
        -
          (* Linear relation: combine the two linear checks; A_0 cancels. *)
          clear hbl hcl.
          eapply f_equal with (f := ginv) in hcr.
          rewrite !group_inv_flip,
          !connection_between_vopp_and_fopp in hcr.
          rewrite commutative in hcr.
          pose proof (@rewrite_gop G gop _ _ _ _ hbr hcr) as hcom.
          rewrite gop_simp in hcom.
          rewrite <-!(@vector_space_smul_distributive_fadd
            F (@eq F) zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow) in hcom; try assumption.
          rewrite <-!ring_sub_definition in hcom.
          setoid_rewrite commutative in hcom at 3.
          rewrite right_inverse, left_identity in hcom.
          eapply f_equal with (f := fun x => gop x (g ^ (opp (z * c₁ - c₂ * z))))
          in hcom.
          rewrite <-!smul_distributive_fadd in hcom.
          assert (hd : (z * c₁ - c₂ * z + opp (z * c₁ - c₂ * z)) = zero).
          field. rewrite hd, field_zero in hcom.
          clear hd.
          assert (hd : opp (z * c₁ - c₂ * z) = z * (c₂ - c₁)). field.
          rewrite hd in hcom; clear hd.
          (* Either g = gid, or the exponent Σ α_i·(s_i − s'_i) − z·(c₁ − c₂) is 0. *)
          eapply gid_power_zero in hcom.
          destruct hcom as [hcom | hcom].
          ++
            right. exact hcom.
          ++
            left.
            eapply f_equal with (f := fun x => x + opp (z * (c₂ - c₁))) in hcom.
            rewrite left_identity in hcom.
            assert (hd : z * (c₂ - c₁) + opp (z * (c₂ - c₁)) = zero).
            field. rewrite <-associative, hd, right_identity in hcom.
            clear hd.
            assert (hd : opp (z * (c₂ - c₁)) = z * (c₁ - c₂)). field.
            rewrite hd in hcom; clear hd.
            rewrite fold_right_pull_out_inv.
            rewrite fold_right_sub_distributive in hcom.
            rewrite hcom.
            field.
            intros hb. eapply ha.
            eapply f_equal with (f := fun x => x + c₂) in hb.
            rewrite left_identity in hb.
            assert (hc : c₁ - c₂ + c₂ = c₁). field.
            rewrite hc in hb; clear hc.
            exact hb.
            Unshelve.
            eapply Fdec.
      Qed.

      (** *** Special honest-verifier zero knowledge

          Within this part, [p / q] denotes the probability [p/q] built with
          [mk_prob]. *)
      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

      (** Every transcript in the support of [Bind l (honest prover)] is accepted,
          for any randomness distribution [l], when the statement holds. *)
      Lemma generalised_pedersen_real_distribution_transcript_accepting_generic {n : nat} :
        ∀ (l : dist (Vector.t F (2 + n + (2 + n)))) (g h : G) (vs rs αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (z : F) (trans : sigma_proto) (pr : prob) (c : F),
        cs = pedersen_commitment_vector g h vs rs ->
        z = fold_right (λ '(α, v) (acc : F), α * v + acc) (zip_with pair αs vs) zero ->
        List.In (trans, pr) (Bind l (λ usws : Vector.t F ((2 + n) + (2 + n)),
            Ret (construct_pedersen_linear_relation_generalised_real_proof g h αs usws vs rs c))) →
        verify_pedersen_linear_relation_generalised_proof g h z αs cs trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Hu Hv Ha.
          cbn in Ha;
          inversion Ha.
        +
          destruct l as [|(la, lp) l].
          ++
            intros * Hu Hv Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply  pedersen_linear_relation_completeness;
            assumption.
          ++
            intros * Hu Hv Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply pedersen_linear_relation_completeness;
              assumption.
            +++
              eapply IHl; try assumption.
              exact Hu. exact Hv.
              exact Ha.
      Qed.

      (** If every element of [l] has probability [1/m], so does every transcript
          of [Bind l (honest prover)]. *)
      Lemma generalised_pedersen_real_distribution_transcript_probability_generic {n : nat} :
      ∀ (l : dist (Vector.t F (2 + n + (2 + n)))) (g h : G) (vs rs αs : Vector.t F (2 + n))
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n + (2 + n))) (prx : prob),
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ usws : Vector.t F (2 + n + (2 + n)),
         Ret (construct_pedersen_linear_relation_generalised_real_proof g h αs usws vs rs c))) →
        pr = 1 / m.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst;
          clear Hwa.
          unfold mul_prob,
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.

      (** Each support element of the honest distribution is accepting and has
          probability [1 / |lf|^(2m)]. *)
      Lemma generalised_pedersen_real_distribution_transcript_generic {n : nat} :
        ∀ (lf : list F) (Hlf : lf <> List.nil) (g h : G) (vs rs αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (z : F) (a : sigma_proto) (b : prob) (c : F),
        cs = pedersen_commitment_vector g h vs rs ->
        z = fold_right (λ '(α, v) (acc : F), α * v + acc) (zip_with pair αs vs) zero ->
        List.In (a, b) (generalised_pedersen_linear_relation_distribution lf Hlf αs vs rs g h c) ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n + (2 + n)))).
      Proof.
        intros * Hrel Hr Ha.
        refine(conj _ _).
        +
          eapply generalised_pedersen_real_distribution_transcript_accepting_generic.
          exact Hrel. exact Hr. exact Ha.
        +
          eapply generalised_pedersen_real_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.

       (** Every transcript in the support of [Bind l (simulator)] is accepted. *)
       Lemma generalised_pedersen_simulator_distribution_transcript_accepting_generic {n : nat} :
        forall (l : dist (Vector.t F (2 + n + (2 + n))))
        (g h : G) (αs : Vector.t F (2 + n)) (cs : Vector.t G (2 + n)) (z : F)
        (trans : sigma_proto) (pr : prob) (c : F),
        List.In (trans, pr) (Bind l (λ usws : Vector.t F (2 + n + (2 + n)),
            Ret (construct_pedersen_linear_relation_generalised_simulator_proof g h αs cs z usws c))) →
        verify_pedersen_linear_relation_generalised_proof g h z αs cs trans = true.
      Proof.
        induction l as [|(a, p) l IHl].
        +
          intros * Ha.
          cbn in Ha;
          inversion Ha.
        +
          destruct l as [|(la, lp) l].
          ++
            intros * Ha.
            cbn in Ha.
            destruct Ha as [Ha | Ha];
            inversion Ha.
            eapply pedersen_linear_relation_simulator_completeness.
          ++
            intros * Ha.
            remember (((la, lp) :: l)%list) as ls.
            cbn in Ha.
            destruct Ha as [Ha | Ha].
            +++
              inversion Ha.
              eapply pedersen_linear_relation_simulator_completeness.
            +++
              eapply IHl; exact Ha.
      Qed.

      (** If every element of [l] has probability [1/m], so does every transcript
          of [Bind l (simulator)]. *)
      Lemma generalised_pedersen_simulator_distribution_transcript_probability_generic {n : nat} :
        forall (l : dist (Vector.t F (2 + n + (2 + n))))
        (g h : G) (αs : Vector.t F (2 + n)) (cs : Vector.t G (2 + n)) (z : F)
        (trans : sigma_proto) (pr : prob) (c : F) (m : nat),
        (∀ (trx : Vector.t F (2 + n + (2 + n))) (prx : prob),
          List.In (trx, prx) l → prx = 1 / m) ->
        List.In (trans, pr) (Bind l (λ usws : Vector.t F (2 + n + (2 + n)),
          Ret (construct_pedersen_linear_relation_generalised_simulator_proof g h αs cs z usws c))) →
        pr = 1 / m.
      Proof.
        induction l as [|(a, p) l IHl].
        + intros * Ha Hin.
          simpl in Hin.
          inversion Hin.
        + intros * Ha Hin.
          pose proof (Ha a p (or_introl eq_refl)).
          destruct Hin as [Hwa | Hwb].
          inversion Hwa; subst;
          clear Hwa.
          unfold mul_prob,
          Prob.one; simpl.
          f_equal.
          nia.
          simpl in Hwb.
          eapply IHl.
          intros ? ? Hinn.
          exact (Ha trx prx (or_intror Hinn)).
          exact Hwb.
      Qed.

       (** Each support element of the simulated distribution is accepting and has
           probability [1 / |lf|^(2m)]. *)
       Lemma generalised_pedersen_simulator_distribution_transcript_generic {n : nat} :
        forall (lf : list F) (Hlf : lf <> List.nil)
        (g h : G) (αs : Vector.t F (2 + n)) (cs : Vector.t G (2 + n)) (z : F)
        (a : sigma_proto) (b : prob) (c : F),
        List.In (a, b) (generalised_pedersen_linear_relation_simulator_distribution lf Hlf g h αs cs z c) ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs a = true ∧
        b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) (2 + n + (2 + n)))).
      Proof.
        intros * Ha.
        refine(conj _ _).
        +
          eapply generalised_pedersen_simulator_distribution_transcript_accepting_generic.
          exact Ha.
        +
          eapply generalised_pedersen_simulator_distribution_transcript_probability_generic.
          intros * Hb.
          eapply  uniform_probability_multidraw_prob.
          exact Hb.
          exact Ha.
      Qed.

      (** Special HVZK in the weak form used across the library: after replacing
          each transcript by its acceptance bit, the real and simulated
          distributions are equal. Transcripts themselves are compared in
          [generalised_pedersen_special_honest_verifier_zkp_perm]. *)
      Lemma generalised_pedersen_special_honest_verifier_zkp {n : nat} :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (g h : G) (vs rs αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (c z : F),
        cs = pedersen_commitment_vector g h vs rs ->
        z = fold_right (λ '(α, v) (acc : F), α * v + acc) (zip_with pair αs vs) zero ->
        List.map (fun '(a, p) =>
          (verify_pedersen_linear_relation_generalised_proof g h z αs cs a, p))
          (generalised_pedersen_linear_relation_distribution lf Hlfn αs vs rs g h c) =
        List.map (fun '(a, p) =>
          (verify_pedersen_linear_relation_generalised_proof g h z αs cs a, p))
          (generalised_pedersen_linear_relation_simulator_distribution lf Hlfn g h αs cs z c).
      Proof.
        intros * Hrel Hr.
        eapply map_ext_eq.
        +
          unfold generalised_pedersen_linear_relation_distribution,
          generalised_pedersen_linear_relation_simulator_distribution; cbn.
          repeat rewrite distribution_length.
          reflexivity.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_pedersen_real_distribution_transcript_generic.
          exact Hrel. exact Hr. exact Ha.
        +
          intros (aa, cc, rr) y Ha.
          eapply generalised_pedersen_simulator_distribution_transcript_generic.
          exact Ha.
      Qed.

      (** Shift identity for the commitments: the honest commitment
          [g^(u_i) · h^(w_i)] equals the simulator's commitment computed from the
          shifted responses [u_i + c·v_i], [w_i + c·r_i] and
          [C_i = g^(v_i) · h^(r_i)]. *)
      Lemma pedersen_commitment_shift (g h : G) (c : F) :
        forall (m : nat) (us ws vs rs : Vector.t F m),
        zip_with (fun v r => gop (g^v) (h^r)) us ws =
        zip_with (fun '(u, w) com => gop (gop (g^u) (h^w)) (com^(opp c)))
          (zip_with pair (zip_with (fun u v => u + c * v) us vs)
            (zip_with (fun w r => w + c * r) ws rs))
          (zip_with (fun v r => gop (g^v) (h^r)) vs rs).
      Proof.
        induction m as [| m ih]; intros us ws vs rs.
        + rewrite (vector_inv_0 us), (vector_inv_0 ws), (vector_inv_0 vs),
            (vector_inv_0 rs); reflexivity.
        + destruct (vector_inv_S us) as (u & us' & hu).
          destruct (vector_inv_S ws) as (w & ws' & hw).
          destruct (vector_inv_S vs) as (v & vs' & hv).
          destruct (vector_inv_S rs) as (r & rs' & hr).
          subst; cbn.
          f_equal; [| apply ih].
          pose proof (schnorr_commitment_shift v g (g ^ v) eq_refl u c) as ha.
          pose proof (schnorr_commitment_shift r h (h ^ r) eq_refl w c) as hb.
          rewrite smul_distributive_vadd, gop_simp, <-ha, <-hb.
          reflexivity.
      Qed.

      (** If the statement holds, the honest transcript with randomness
          [(us, ws)] is the simulated transcript with responses
          [(us + c·vs, ws + c·rs)]. *)
      Lemma pedersen_linear_shift {n : nat} (g h : G) (αs vs rs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (c z : F)
        (hcs : cs = pedersen_commitment_vector g h vs rs)
        (hz : z = fold_right (λ '(α, v) acc, α * v + acc) (zip_with pair αs vs) zero) :
        forall (us ws : Vector.t F (2 + n)),
        construct_pedersen_linear_relation_generalised_real_proof g h αs
          (Vector.append us ws) vs rs c =
        construct_pedersen_linear_relation_generalised_simulator_proof g h αs cs z
          (Vector.append (zip_with (fun u v => u + c * v) us vs)
            (zip_with (fun w r => w + c * r) ws rs)) c.
      Proof.
        intros us ws.
        unfold construct_pedersen_linear_relation_generalised_real_proof,
          construct_pedersen_linear_relation_generalised_simulator_proof,
          construct_pedersen_linear_relation_commitment.
        rewrite !VectorSpec.splitat_append.
        cbv beta iota zeta.
        subst; unfold pedersen_commitment_vector.
        f_equal; f_equal.
        + apply pedersen_commitment_shift.
        + f_equal.
          rewrite fold_right_zip, smul_pow_up, <-smul_distributive_fadd.
          f_equal; field.
      Qed.

      (** The response vector [us + c·vs] as a coordinate-wise function
          application [vec_apply]. *)
      Lemma pedersen_response_vec_apply (c : F) :
        forall (m : nat) (vs us : Vector.t F m),
        vec_apply (Vector.map (fun v u => u + c * v) vs) us =
        zip_with (fun u v => u + c * v) us vs.
      Proof.
        induction m as [|m ih]; intros vs us.
        + rewrite (vector_inv_0 vs), (vector_inv_0 us); reflexivity.
        + destruct (vector_inv_S vs) as (v & vs' & hv).
          destruct (vector_inv_S us) as (u & us' & hu).
          subst; cbn; f_equal; apply ih.
      Qed.

      (** Strong special HVZK: if the statement holds and every shift
          [u ↦ u + c·x] permutes [lf], the real transcript distribution is a
          permutation of the simulated one. Proof: [bind_ret_perm] with the
          shift of [pedersen_linear_shift], which permutes the product
          distribution ([repeat_uniform_perm]). *)
      Theorem generalised_pedersen_special_honest_verifier_zkp_perm {n : nat} :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (g h : G) (vs rs αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (c z : F),
        cs = pedersen_commitment_vector g h vs rs ->
        z = fold_right (λ '(α, v) acc, α * v + acc) (zip_with pair αs vs) zero ->
        (forall x : F, Permutation (List.map (fun u => u + c * x) lf) lf) ->
        Permutation
          (generalised_pedersen_linear_relation_distribution lf Hlfn αs vs rs g h c)
          (generalised_pedersen_linear_relation_simulator_distribution lf Hlfn g h αs cs z c).
      Proof.
        intros * hcs hz hp.
        change (Permutation
          (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
              ((2 + n) + (2 + n)))
            (fun usws => Ret (construct_pedersen_linear_relation_generalised_real_proof
              g h αs usws vs rs c)))
          (Bind (repeat_dist_ntimes_vector (uniform_with_replacement lf Hlfn)
              ((2 + n) + (2 + n)))
            (fun usws => Ret (construct_pedersen_linear_relation_generalised_simulator_proof
              g h αs cs z usws c)))).
        eapply bind_ret_perm with
          (phi := vec_apply (Vector.append
            (Vector.map (fun v u => u + c * v) vs)
            (Vector.map (fun r w => w + c * r) rs))).
        + apply repeat_uniform_perm.
          apply (nth_append_forall (fun phi => Permutation (List.map phi lf) lf)).
          * intros i; rewrite (nth_map _ _ i i eq_refl); apply hp.
          * intros j; rewrite (nth_map _ _ j j eq_refl); apply hp.
        + intros usws p _.
          destruct (splitat (2 + n) usws) as (us & ws) eqn:hsplit.
          apply VectorSpec.append_splitat in hsplit.
          subst usws.
          rewrite vec_apply_append, !pedersen_response_vec_apply.
          apply pedersen_linear_shift; assumption.
      Qed.

      (** Strong special HVZK when [lf] enumerates the field without duplicates
          (every shift is then a permutation, [enumerates_perm_map]). *)
      Theorem generalised_pedersen_special_honest_verifier_zkp_enum {n : nat} :
        forall (lf : list F) (Hlfn : lf <> List.nil)
        (g h : G) (vs rs αs : Vector.t F (2 + n))
        (cs : Vector.t G (2 + n)) (c z : F),
        cs = pedersen_commitment_vector g h vs rs ->
        z = fold_right (λ '(α, v) acc, α * v + acc) (zip_with pair αs vs) zero ->
        List.NoDup lf -> (forall y : F, List.In y lf) ->
        Permutation
          (generalised_pedersen_linear_relation_distribution lf Hlfn αs vs rs g h c)
          (generalised_pedersen_linear_relation_simulator_distribution lf Hlfn g h αs cs z c).
      Proof.
        intros * hcs hz hnd hall.
        eapply generalised_pedersen_special_honest_verifier_zkp_perm;
        [exact hcs | exact hz |].
        intro x.
        eapply enumerates_perm_map with (psi := fun u => u - c * x);
        [exact hnd | exact hall | intros u; field | intros u; field].
      Qed.

    End Proofs.
  End PedLinearRelation.
End DL.
