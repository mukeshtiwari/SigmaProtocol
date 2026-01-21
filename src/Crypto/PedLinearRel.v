From Stdlib Require Import Setoid
  setoid_ring.Field Lia Vector Utf8
  Psatz Bool Pnat BinNatDef 
  BinPos. 
From Algebra Require Import 
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Probability Require Import 
  Prob Distr. 
From Utility Require Import Util. 
From ExtLib Require Import Monad. 
From Crypto Require Import Sigma.
  

Import MonadNotation 
  VectorNotations.

#[local] Open Scope monad_scope.

(* Discrete Logarithm Zero Knowlege Proof *) 
Section DL. 
  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}
    {Fdec: forall x y : F, {x = y} + {x <> y}}. 
    (* decidable equality on Field *)

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Gdec : forall x y : G, {x = y} + {x <> y}}. 
    (* decidable equality on G *)
    

  #[local] Infix "^" := gpow.
  #[local] Infix "*" := mul.
  #[local] Infix "/" := div.
  #[local] Infix "+" := add.
  #[local] Infix "-" := sub.

  
  #[local] Notation "( a ; c ; r )" := (mk_sigma _ _ _ a c r).

  Section PedLinearRelation.

    Section Def.
      (*
      
      vs : Vector.t F n 
      rs : Vector.t F n 
      g h : G 
      as : Vector.t F n 
      cs : zip_with (fun v r => gop g^u h^r) vs rs
      z  = Σ_i a_i ∙ v_i 

      ∃ (v_i, r_i) : ∀ i, C_i = G^{v_i}·H^{r_i} ∧ Σ a_i·v_i = Z
      This forces that the lenghth of as should be 2 + n 
      
      *)

      Definition pedersen_commitment_vector {n : nat}
        (g h : G) (vs rs : Vector.t F (2 + n)) : Vector.t G (2 + n).
      Proof.
        refine(zip_with (fun v r => gop (g^v) (h^r)) vs rs).
      Defined.

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


      (* 
      
      g, h ∈ G: Two group generators
      αs = (α₁, α₂, ..., α_{2+n}) ∈ F^{2+n}: Coefficient vector
      vs = (v₁, v₂, ..., v_{2+n}) ∈ F^{2+n}: Secret witness values
      rs = (r₁, r₂, ..., r_{2+n}) ∈ F^{2+n}: Secret randomness values
      usws ∈ F^{2(2+n)}: Fresh randomness for commitment phase
      c ∈ F: Challenge value
      comm₁[i] = g^{u_i} · h^{w_i}  for each i
      comm₂ = g^{Σᵢ αᵢ·uᵢ}
      res₁[i] = u_i + c·v_i  for each i
      res₂[i] = w_i + c·r_i  for each i

      This proves knowledge of (vs, rs) satisfying:

      C_i = g^{v_i} · h^{r_i} (Pedersen commitments) for all i
      Σᵢ αᵢ·vᵢ = z (linear constraint on the committed values)


      *)
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


      (*
      
      g, h ∈ G: Two group generators
      αs = (α₁, α₂, ..., α_{2+n}) ∈ F^{2+n}: Coefficient vector
      cs = (C₁, C₂, ..., C_{2+n}) ∈ G^{2+n}: Public Pedersen commitments (where C_i = g^{v_i} · h^{r_i} for unknown v_i, r_i)
      z ∈ F: Public value (where z = Σᵢ αᵢ·vᵢ for unknown v_i)
      usws ∈ F^{2(2+n)}: Random values to use as responses
      c ∈ F: Challenge value (chosen by simulator)

      Construction Steps
      Split randomness: usws → (us, ws) where both have length (2+n)
      First commitment comm₁ ∈ G^{2+n} (computed backwards):
      comm₁[i] = g^{u_i} · h^{w_i} · C_i^{-c}
      Second commitment comm₂ ∈ G:
      comm₂ = g^{Σᵢ αᵢ·uᵢ} · g^{-z·c}
      Response: Just usws (i.e., us ++ ws)
        
      *)
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
        


      (* 
      
        Inputs
        g, h ∈ G: Two group generators
        z ∈ F: Public value (claimed to equal Σᵢ αᵢ·vᵢ)
        αs = (α₁, α₂, ..., α_{2+n}) ∈ F^{2+n}: Public coefficient vector
        cs = (C₁, C₂, ..., C_{2+n}) ∈ G^{2+n}: Public Pedersen commitments
        pf = (comm; cha; res): The proof transcript to verify
      
        Verification step:
        Split comm into comm₁ (first 2+n elements) and comm₂ (last element)
        Extract challenge c from cha
        Split res into res₁ and res₂ (each has 2+n elements)

        First check (ret₁): Verify each Pedersen commitment relation:
        For all i: g^{res₁[i]} · h^{res₂[i]} ?= comm₁[i] · C_i^c
        Second check (ret₂): Verify the linear constraint:
        g^{Σᵢ αᵢ·res₁[i]} ?= comm₂ · g^{c·z}

        Why This Works
        If the prover is honest with secrets (vs, rs) where C_i = g^{v_i}·h^{r_i} and z = Σᵢ αᵢ·vᵢ:

        Check 1 expands to: g^{u_i + c·v_i}·h^{w_i + c·r_i} = g^{u_i}·h^{w_i}·(g^{v_i}·h^{r_i})^c ✓
        Check 2 expands to: g^{Σᵢ αᵢ·(u_i + c·v_i)} = g^{Σᵢ αᵢ·u_i}·g^{c·Σᵢ αᵢ·v_i} ✓
        Both equations hold by the group homomorphism properties.

      *)
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

      (* 
      
        lf: Non-empty list of field elements (the randomness space)
        αs ∈ F^{2+n}: Coefficient vector
        vs, rs ∈ F^{2+n}: Secret witness (values and randomness satisfying the relation)
        g, h ∈ G: Group generators
        c ∈ F: Challenge value

        Sample randomness: usws ← Uniform(lf)^{2(2+n)}
        Construct real proof: 
        Return: construct_pedersen_linear_relation_generalised_real_proof
        (g, h, αs, usws, vs, rs, c)

      *)
      (* Generalised pedersen linear relation distribution *)
      Definition generalised_pedersen_linear_relation_distribution  
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil)
        (αs : Vector.t F (2 + n)) 
        (vs rs : Vector.t F (2 + n)) (g h : G) 
        (c : F) : dist (@sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n))) :=
        (* draw n random elements *)
        usws <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) ((2 + n) + (2 + n)) ;;
        Ret (construct_pedersen_linear_relation_generalised_real_proof 
          g h αs usws vs rs c).
      
      (* 
        lf: Non-empty list of field elements (randomness space)
        g, h ∈ G: Group generators
        αs ∈ F^{2+n}: Coefficient vector (public)
        cs ∈ G^{2+n}: Pedersen commitments C_i = g^{v_i}·h^{r_i} (public, but v_i, r_i are unknown)
        z ∈ F: Public value where z = Σᵢ αᵢ·vᵢ (but individual v_i are unknown)
        c ∈ F: Challenge value

        Sample random responses:
        usws ← Uniform(lf)^{2(2+n)}
        Construct simulated proof (working backwards):
        Return: construct_pedersen_linear_relation_generalised_simulator_proof
        (g, h, αs, cs, z, usws, c)

        The simulator can produce valid-looking transcripts without any witness
        These simulated transcripts should be indistinguishable from real proofs
        This proves: transcripts reveal nothing beyond statement validity (zero-knowledge!)
      *)
      
      (* Generalised simulator distribution (without secret) *)
      Definition generalised_pedersen_linear_relation_simulator_distribution 
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
        (g h : G) (αs : Vector.t F (2 + n)) 
        (cs : Vector.t G (2 + n)) (z : F)
        (c : F) : dist (@sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n))) :=
        (* draw n random elements *)
        usws <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) ((2 + n) + (2 + n)) ;;
        Ret (construct_pedersen_linear_relation_generalised_simulator_proof 
          g h αs cs z usws c).

    End Def. 

    Section Proofs.

      Theorem pedersen_linear_relation_verification_function_correctness_forward :
        ∀ (n : nat) (g h : G) (z : F) (αs : Vector.t F (2 + n)) 
        (cs : Vector.t G (2 + n)) (comm₁ : Vector.t G (2 + n))
        (comm₂ : G) (c : F) (res₁ res₂ : Vector.t F (2 + n)),
        (* If verification succeeds *)
        verify_pedersen_linear_relation_generalised_proof g h z αs cs 
        (comm₁ ++ [comm₂]; [c]; res₁ ++ res₂) = true ->
        (* Then the verification equations hold *)
        (* Equation 1: Pedersen commitment relations *)
        (∀ (i : Fin.t (2 + n)), 
          gop (g ^ (nth res₁ i)) (h ^ (nth res₂ i)) = 
          gop (nth comm₁ i) ((nth cs i) ^ c)) ∧
        (* Equation 2: Linear constraint *)
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


      
      Theorem pedersen_linear_relation_verification_function_correctness_backward :
        ∀ (n : nat) (g h : G) (z : F) (αs : Vector.t F (2 + n)) 
        (cs : Vector.t G (2 + n)) (comm₁ : Vector.t G (2 + n))
        (comm₂ : G) (c : F) (res₁ res₂ : Vector.t F (2 + n)),
        (* Then the verification equations hold *)
        (* Equation 1: Pedersen commitment relations *)
        (∀ (i : Fin.t (2 + n)), 
          gop (g ^ (nth res₁ i)) (h ^ (nth res₂ i)) = 
          gop (nth comm₁ i) ((nth cs i) ^ c)) ->
        (* Equation 2: Linear constraint *)
        g ^ (Vector.fold_right (fun '(α, u) acc => α * u + acc) 
          (zip_with pair αs res₁) zero) = 
        gop (comm₂) (g ^ (c * z)) ->
         (* If verification succeeds *)
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

      Context
        {Hvec: @vector_space F (@eq F) zero one add mul sub 
          div opp inv G (@eq G) gid ginv gop gpow}.
      Add Field field : (@field_theory_for_stdlib_tactic F
        eq zero one opp add mul sub inv div vector_space_field).

      (* move this to Util.v and remove it from Okamoto *)
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

      (* move to util.v? It needs field assumption *)
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
      

      Theorem pedersen_linear_relation_completeness :
        ∀ (n : nat) (g h : G) (αs : Vector.t F (2 + n)) 
          (vs rs : Vector.t F ((2 + n))) (cs : Vector.t G (2 + n)) 
          (usws : Vector.t F ((2 + n) + (2 + n))) (c z : F),
        (* Define the public commitments from witnesses *)
        cs = pedersen_commitment_vector g h vs rs ->
        (* Define the public linear combination *)
        z = Vector.fold_right (fun '(α, v) acc => α * v + acc)
          (zip_with pair αs vs) zero ->
        (* Then the real proof verifies *)
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
        - (* Prove equation 1: Pedersen commitment relations *)
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
        - (* Prove equation 2: Linear constraint *)
          subst res₁ z comm₂.
          rewrite <-!smul_distributive_fadd.
          rewrite fold_right_zip. reflexivity.
      Qed.

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
        (* res₁ = us, res₂ = ws in the simulator transcript *)
        eapply pedersen_linear_relation_verification_function_correctness_backward.
        - (* Check 1: g^{u_i} h^{w_i} = comm₁[i] · cs[i]^c *)
          intro i. subst comm₁.
          rewrite !nth_zip_with.
          rewrite <-associative.
          rewrite <-smul_distributive_fadd.
          assert (hb : opp c + c = zero). field.
          rewrite hb; clear hb.
          rewrite field_zero, right_identity.
          reflexivity.
        - (* Check 2: g^{Σ α_i·u_i} = comm₂ · g^{c·z} *)
          subst comm₂.
          rewrite <-associative, <-smul_associative_fmul,
           <-smul_distributive_fadd.
          assert (hb : (opp z * c + c * z) = zero). field.
          rewrite hb; clear hb.
          rewrite field_zero, right_identity.
          reflexivity.
      Qed.

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

      Theorem pedersen_linear_relation_special_soundness :
        ∀ (n : nat) (g h : G) (αs : Vector.t F (2 + n))
          (cs : Vector.t G (2 + n)) (z : F)
          (comm : Vector.t G ((2 + n) + 1))
          (c₁ c₂ : F) (res₁ res₂ : Vector.t F ((2 + n) + (2 + n))),
        (* Two accepting transcripts with same commitment, different challenges *)
        c₁ <> c₂ ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
          (comm; [c₁]; res₁) = true ->
        verify_pedersen_linear_relation_generalised_proof g h z αs cs
          (comm; [c₂]; res₂) = true ->
        (* Then we can extract valid witnesses *)
        ∃ (vs rs : Vector.t F (2 + n)),
          (* Commitments are well-formed *)
          (∀ (i : Fin.t (2 + n)),
            nth cs i = gop (g ^ (nth vs i)) (h ^ (nth rs i))) ∧
          (* Linear relation holds or the group generator is an idenity *)
          (z = Vector.fold_right (fun '(α, v) acc => α * v + acc) 
            (zip_with pair αs vs) zero ∨ g = gid).
      Proof.
        intros * ha hb hc.
        (* Extract responses from both transcripts *)
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
        exists (zip_with (fun r₁ r₂ => (r₁ - r₂) * inv (c₁ - c₂)) res₁_a res₂_a),
        (zip_with (fun r₁ r₂ => (r₁ - r₂) * inv (c₁ - c₂)) res₁_b res₂_b).
        split.
        - (* Prove commitment relation: C_i = g^{v_i} · h^{r_i} *)
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
          (* rewrite and setoid_rewrite both fails! *)
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
        - (* Prove linear constraint: z = Σ α_i · v_i *)
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
          eapply gid_power_zero in hcom.
          destruct hcom as [hcom | hcom].
          ++
            right. exact hcom.
          ++
            left.
            (* multiply both sides inv (c₂ - c₁) in Hcom *)
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

      (* special honest-verifier zero-knowledge proof *)
      (* honest verifier zero knowledge proof *)
      (* 
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

      Definition verify_pedersen_linear_relation_generalised_proof {n : nat} 
        (g h : G) : F -> Vector.t F (2 + n) -> Vector.t G (2 + n) -> 
        @sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n)) -> bool.

         intros z αs cs pf.
      *)

      #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

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
          (* destruct l *)
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

      (*  Definition construct_pedersen_linear_relation_generalised_simulator_proof 
        {n : nat} (g h : G) (αs : Vector.t F (2 + n)) 
        (cs : Vector.t G (2 + n)) (z : F)
        (usws : Vector.t F ((2 + n) + (2 + n))) (c : F) : 
        @sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n)). 
      *)

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
          (* destruct l *)
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


      (*  (* Generalised simulator distribution (without secret) *)
      Definition generalised_and_simulator_distribution 
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
        (g h : G) (αs : Vector.t F (2 + n)) 
        (cs : Vector.t G (2 + n)) (z : F)
        (c : F) : dist (@sigma_proto F G ((2 + n) + 1) 1  ((2 + n) + (2 + n))) :=
        (* draw n random elements *)
        usws <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) ((2 + n) + (2 + n)) ;;
        Ret (construct_pedersen_linear_relation_generalised_simulator_proof 
          g h αs cs z usws c).*)

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


      (* Two distributions are identical (information theoretic security)*)
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
    
    End Proofs.
  End PedLinearRelation.
End DL. 
  