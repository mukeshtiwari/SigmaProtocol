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
  VectorNotations EqNotations.

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


  Section Or.
    (* Proof Friendly Definitions *)
    Section Defs.

      (* Generalised Or composition where you know 1 out of n statements
        g^x₁ = h₁ ∨ g^x₂ = h₂ ∨ g^x₃ = h₃ ... 
              
        One witness out of n statements but if you want to prove 
        that you know k out of n statements then 
        use the following paper https://www.win.tue.nl/~berry/papers/crypto94.pdf
      
      *)
      (* Prover knows the ith relation *)
      (* The way out is that the verifier may let the prover “cheat” a 
        little bit by allowing the prover to use the simulator of the 
        Σ-protocol for the relation Ri for which the prover does not 
        know witness wi (i = 1 or i = 2). The verifier will do so by 
        providing a single challenge c which the prover is allowed to 
        split into two challenges c1, c2 provided c1, c2 satisfy a 
        linear constraint in terms of c. For example, the constraint 
        may be c = c1 ⊕ c2 if the challenges happen to be bit strings. 
        Essentially, the prover gets one degree of freedom to cheat. 
      *)
        (* 
          prover knowns ith relation 
          x is the secret 
          us is random scalors for commitment 
          cs is random scalors for prover to cheat
          us = usl ++ [u] ++ usr
          cs = csl ++ [_] ++ csr 
          Prover recomputes: 
          cb := c - Σ rsl + rsr 

          Uses simulator on (usl ++ usr) (csl ++ csr)
          Uses Schnorr protocol u cb
          Package them together.

          Verifier check the if all the individual 
          sigma protocols are valid and 
          challenges sum up to c.
        *)

        (* 
        1. **Commitment**:
          - Let k be the index for which the prover knows the witness x_k (so y_k = g^{x_k}).
          - For statement k (real):
            - Choose random r_k, compute t_k = g^{r_k}.
          - For each statement i ≠ k (simulated):
            - Choose random s_i and c_i.
            - Compute t_i = g^{s_i} * y_i^{-c_i}.
        2. **Send commitments**: The prover sends (t_1, t_2, ..., t_n) to the verifier.
        3. **Challenge**: The verifier sends a random challenge c.
        4. **Response**:
          - The prover sets c_k = c - (sum of c_i for i≠k) mod q.
          - For the real statement k: compute s_k = r_k + c_k * x_k mod q.
          - The responses for the simulated statements are already known (s_i for i≠k).
          - The prover sends (s_1, s_2, ..., s_n) and (c_1, c_2, ..., c_n).
        
        *)

        (* 
          x g hs us cs c. 
          x is secret  
          g and hs are public group elements 
          and prover knows the (m + 1)-th relation.
          us and cs -- verifier let prover cheat -- are randomness 
          c is challenge.
        *)

        (*  {(x₁, x₂ … xₙ) : h₁ = g^x₁ ∨ h₂ = g^x₂ ∨ … hₙ = g^xₙ} *)
        (* Prover knows (m + 1)-th relation g^x = hₘ *)
        #[local]
        Definition construct_or_conversations_schnorr {m n : nat} 
          (x : F) (g : G) (hs : Vector.t G (m + (1 + n)))
          (uscs : Vector.t F ((m + (1 + n)) + (m + n))) (c : F) : 
          @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          (* commitment *)
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          (* us is the randomness for commitment and cs is the degree of freedom *)
          (* split us for simulation  *)
          destruct (splitat m us) as (usl & usrh).
          destruct (vector_inv_S usrh) as (u & usr & _).
          (* split cs for simulation *)
          destruct (splitat m cs) as (csl & csr).
          destruct (splitat m hs) as (hsl & hsrh).
          destruct (vector_inv_S hsrh) as (_ & hsr & _).
          (* left simulate commitments *)
          set (comml := zip_with (fun ui ci => (ui, ci)) usl csl).
          set (commitl := zip_with (fun hi '(ui, ci) => gop (g^ui) (hi^(opp ci))) hsl comml).
          (* real commitment *)
          set (com := g^u). 
          (* right simulate commitment *)
          set (commr := zip_with (fun ui ci => (ui, ci)) usr csr).
          set (commitr := zip_with (fun hi '(ui, ci) => gop (g^ui) (hi^(opp ci))) hsr commr).
          (* put c at front of challenges *)
          remember (c - (Vector.fold_right add (csl ++ csr) zero)) as cb.
          (* response *)
          remember (u + cb * x) as res.
          refine((commitl ++ [com] ++ commitr); c :: csl ++ [cb] ++ csr ; usl ++ [res] ++ usr).
        Defined.

        (*  {(x₁, x₂ … xₙ) : h₁ = g^x₁ ∨ h₂ = g^x₂ ∨ … hₙ = g^xₙ} *)
        (* Prover knows rindex such that relation g^x = hₘ *)
        Definition generalised_construct_or_conversations_schnorr {n : nat} 
          (rindex : Fin.t (2 + n)) (x : F) (g : G) (hs : Vector.t G (2 + n))
          (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) : 
          @sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n).
        Proof.
          destruct (splitat (2 + n) uscs) as (us & cs).
          destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as 
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfa & pfb & ha & hb & hc).
          pose proof (@construct_or_conversations_schnorr m₁ m₂ x g 
          (rew pfa in hs) ((rew pfa in us) ++ (rew pfb in cs)) c) as hd.
          rewrite <-pfa in hd.
          exact hd.
        Defined.
        

        (* simulator *)
        (* does not involve secret x *)
        Definition generalised_construct_or_conversations_simulator {n : nat} 
          (g : G) (hs : Vector.t G (2 + n)) (uscs : Vector.t F ((2 + n) + (1 + n)))  
          (c : F) :  @sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n).
        Proof.
          destruct (splitat (2 + n)uscs) as (us & cs).
          (* (c - Σcs) :: cs *)
          set (cm := (c - (Vector.fold_right add cs zero) :: cs)).
          set (comm := zip_with (fun ui ci => (ui, ci)) us cm).
          set(commitment := zip_with (fun hi '(ui, ci) => 
            gop (g^ui) (hi^(opp ci))) hs comm).
          refine(commitment; c :: cm; us).
        Defined.


        #[local]
        Definition or_accepting_conversations_supplement : 
          forall {n : nat}, G -> Vector.t G n -> @sigma_proto F G n n n -> bool.
        Proof.
          refine
            (fix Fn n := 
            match n with 
            | 0 => fun g hs Ha => true
            | S n' => fun g hs Ha => 
              match Ha with 
              | (a₁; c₁; r₁) => _ 
              end 
            end).
          destruct (vector_inv_S hs) as (h & hsr & _).
          destruct (vector_inv_S a₁) as (a & asr & _).
          destruct (vector_inv_S c₁) as (c & csr & _).
          destruct (vector_inv_S r₁) as (r & rsr & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([a]; [c]; [r])) && 
            (Fn _ g hsr (asr; csr; rsr))).
        Defined.

        (* verify OR sigma protocol *)
        (* Check that 
          - the sum of c_i (from i=1 to n) equals c mod q.
          - For each i from 1 to n: check that g^{s_i} = t_i * y_i^{c_i}. *)
        Definition generalised_or_accepting_conversations {n : nat} 
          (g : G) (hs : Vector.t G n)
          (pf : @sigma_proto F G n (1 + n) n) : bool.
        Proof.
          refine 
            match pf with 
            |(a; css; r) => _ 
            end.
          (* Verifier first checks if challenge c is equal 
            to the rest of challenges *)
          destruct (vector_inv_S css) as (c & cs & _).
          refine
            match Fdec c (Vector.fold_right add cs zero) with 
            | left _ => 
                (* now check sigma *)
                or_accepting_conversations_supplement g hs (a; cs; r)
            | right _ => false (* if it's false, there is 
              no point for checking further *)
            end.
        Defined.

        (* schnorr OR distribution *)
        Definition generalised_or_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (rindex : Fin.t (2 + n)) (x : F) (g : G) (hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n)) := 
          uscs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + (1 + n)) ;;
          Ret (generalised_construct_or_conversations_schnorr rindex x g hs uscs c).


        (* simulator distribution *)
        Definition generalised_or_simulator_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (g : G) (hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto F G (2 + n) (1 + (2 + n)) (2 + n)) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + (1 + n)) ;;
          Ret (generalised_construct_or_conversations_simulator g hs usrs c).

    End Defs.

    Section Proofs.


        (* properties about accepting funciton *)
        (* 
          when or_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations and 
          hd c = sum of rest of c 
        *)
        Lemma or_accepting_conversations_correctness_supplement_forward : 
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          or_accepting_conversations_supplement g hs s = true ->
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n, 
            @accepting_conversation F G gop gpow Gdec g (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end).
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl).
            intros f;
            inversion f.
          +
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl); intro f. 
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (fin_inv_S _ f) as [Hi | (fs & Hi)];
            subst; simpl. 
            ++
              cbn in Ha.
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              exact Hal.
            ++
              simpl in Ha;
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              exact (IHn _ _ _ Har fs).
        Qed.


         Lemma or_accepting_conversations_correctness_supplement_backward : 
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n,
            @accepting_conversation  F G gop gpow Gdec g (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end) -> or_accepting_conversations_supplement g hs s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 hs);
            cbn; reflexivity.
          + 
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl).
            destruct (vector_inv_S hs) as (hsh & hstl & Hd).
            destruct (vector_inv_S a₁) as (ah₁ & atl₁ & He).
            destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            subst; cbn. 
            eapply andb_true_iff.
            split.
            ++ 
              pose proof (Ha Fin.F1) as Hi.
              cbn in Hi.
              exact Hi.
            ++
              specialize (IHn g hstl (atl₁; ctl₁; rtl₁)).
              assert (Hb : (∀ f : Fin.t n,
              match (atl₁; ctl₁; rtl₁) with
              | (a; c; r) =>
                  @accepting_conversation  F G gop gpow Gdec g hstl[@f]
                    ([a[@f]]; [c[@f]]; [r[@f]]) = true
              end)).
              intros *; exact (Ha (Fin.FS f)).
              exact (IHn Hb).
        Qed.


        Lemma or_accepting_conversations_correctness_supplement : 
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          or_accepting_conversations_supplement g hs s = true <-> 
          match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n,
            @accepting_conversation F G gop gpow Gdec g (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end.
        Proof.
          intros *.
          split; intros Ha.
          +
            eapply or_accepting_conversations_correctness_supplement_forward;
            exact Ha.
          +
            eapply or_accepting_conversations_correctness_supplement_backward;
            exact Ha.
        Qed.

        Lemma or_accepting_conversations_supplement_app :
          forall (n m : nat) (g : G)
          (hsl al : Vector.t G n) (hsr ar : Vector.t G m)
          (cl rl : Vector.t F n) (cr rr : Vector.t F m),
          or_accepting_conversations_supplement
            g (hsl ++ hsr) 
            ((al ++ ar); (cl ++ cr); (rl ++ rr)) = 
          or_accepting_conversations_supplement g hsl (al; cl; rl)  && 
          or_accepting_conversations_supplement g hsr (ar; cr; rr).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 hsl).
            rewrite (vector_inv_0 al).
            rewrite (vector_inv_0 cl).
            rewrite (vector_inv_0 rl).
            cbn; reflexivity.
          +
            intros *.
            destruct (vector_inv_S hsl) as (hslh & hsltl & Hb).
            destruct (vector_inv_S al) as (alh & altl & Hc).
            destruct (vector_inv_S cl) as (clh & cltl & Hd).
            destruct (vector_inv_S rl) as (rlh & rltl & He).
            subst; cbn.
            destruct (Gdec (g ^ rlh) (gop alh (hslh ^ clh))).
            ++
              cbn; eapply IHn.
            ++
              cbn; reflexivity.
        Qed.

        Lemma generalised_or_accepting_conversations_correctness_forward : 
          forall {n : nat} (g : G) (hs : Vector.t G n )
          (s :  @sigma_proto F G n (1 + n) n),
          generalised_or_accepting_conversations g hs s = true -> 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end.
        Proof.
          intros * Ha. 
          unfold generalised_or_accepting_conversations in Ha.
          refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl).
          rewrite Hb in Ha.
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          destruct (Fdec ch₁ (fold_right add ctl₁ zero)) eqn:Hd;
          [|inversion Ha].
          split.
          +
            rewrite Hc; cbn;
            exact e.
          +
            rewrite Hc; cbn.
            eapply or_accepting_conversations_correctness_supplement_forward in
            Ha; exact Ha.
        Qed.


        Lemma generalised_or_accepting_conversations_correctness_backward : 
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n (1 + n) n), 
          (match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) -> 
          generalised_or_accepting_conversations g hs s = true.
        Proof.
          intros * Ha.
          unfold generalised_or_accepting_conversations.
          refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl).
          destruct (vector_inv_S c₁) as (ch₁ & ctl₁ & Hc).
          assert (Hd : ch₁ = (fold_right add ctl₁ zero)).
          rewrite Hb in Ha.
          +
            destruct Ha as [Hal Har].
            rewrite Hc in Hal; cbn 
            in Hal. exact Hal.
          +
            rewrite <-Hd.
            destruct (Fdec ch₁ ch₁) eqn:He.
            eapply or_accepting_conversations_correctness_supplement;
            intros f.
            rewrite Hb in Ha.
            destruct Ha as [Hal Har].
            rewrite Hc in Har.
            specialize (Har f).
            cbn in Har; cbn.
            exact Har.
            congruence.
        Qed.


        Lemma generalised_or_accepting_conversations_correctness: 
          forall {n : nat} (g : G) (hs : Vector.t G n)
          (s :  @sigma_proto F G n (1 + n) n),
          (match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t n),
            @accepting_conversation F G gop gpow Gdec g (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) <-> 
          generalised_or_accepting_conversations g hs s = true.
        Proof.
          intros *; 
          split; intro Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_backward; 
            try assumption.
          +
            eapply generalised_or_accepting_conversations_correctness_forward;
            try assumption.
        Qed.

        (* end of properties *)

         Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).
        
        (* completeness *)
        Lemma fold_right_app :
          forall (n m : nat) (ul : Vector.t F n)
          (ur : Vector.t F m),
          fold_right add (ul ++ ur) zero = 
          (fold_right add ul zero) + (fold_right add ur zero).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 ul);
            cbn. field.
          +
            intros *.
            destruct (vector_inv_S ul) as (ulh & ultl & Ha).
            subst; cbn. 
            rewrite IHn; cbn.
            field.
        Qed.

        Theorem construct_or_conversations_schnorr_completeness_base : 
          forall (n : nat) (f : Fin.t n) (usr csr : Vector.t F n)
          (hsr : Vector.t G n) (g : G),
          g ^ usr[@f] = gop 
          (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsr
          (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f]
          (hsr[@f] ^ csr[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *.
            refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S csr) as (csrh & csrt & hb).
            destruct (vector_inv_S hsr) as (hsrh & hsrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihn.
        Qed.
      


        Theorem construct_or_conversations_schnorr_completeness_generic : 
          forall (m n : nat) (f : Fin.t (m + S n)) (g : G) (usl : Vector.t F m)
          (c : F) (csl : Vector.t F m) (csr : Vector.t F n) (x : F) (u : F)
          (usr : Vector.t F n) (hsl : Vector.t G m) (h : G) (hsr : Vector.t G n),
          g^x = h -> 
          g ^ (usl ++ u + (c - fold_right add (csl ++ csr) zero) * x :: usr)[@f] =
          gop (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsl
          (zip_with (λ ui ci : F, (ui, ci)) usl csl) ++ g ^ u
          :: zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsr
            (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f]
          ((hsl ++ h :: hsr)[@f] ^ (csl ++ c - fold_right add (csl ++ csr) zero :: csr)[@f]).
        Proof.
          induction m as [|m ihm].
          +
            cbn; intros * hr.
            rewrite (vector_inv_0 csl), (vector_inv_0 usl),
            (vector_inv_0 hsl).
            assert (ha : (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) []
            (zip_with (λ ui ci : F, (ui, ci)) [] []) = [])). reflexivity.
            rewrite ha; clear ha. 
            destruct (fin_inv_S _ f) as [f' | (f' & hf)].
            ++
              subst; cbn.
              remember ((c - fold_right add csr zero)) as ct.
              assert (Hg : (g ^ x) ^ ct = (g ^ (x * ct))).
              rewrite smul_pow_up. 
              reflexivity.
              rewrite Hg; clear Hg.
              assert (Hxc : x * ct = ct * x) by field.
              rewrite Hxc; clear Hxc.
              rewrite <- (@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div
                opp inv G (@eq G) gid ginv gop gpow);
              subst; [exact eq_refl 
              | assumption].
            ++
              subst; cbn.
              eapply construct_or_conversations_schnorr_completeness_base.
          +
            (* inductive case *)
            intros *.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            destruct (vector_inv_S csl) as (cslh & cslt & hb).
            destruct (vector_inv_S hsl) as (hslh & hslt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & hd)]. 
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              rewrite hd. cbn.
              specialize (ihm _ f' g uslt (c - cslh) cslt csr x u usr hslt h hsr).
              remember (fold_right add (cslt ++ csr) zero) as ct.
              assert (ha : c - (cslh + ct) = c - cslh - ct). field.
              rewrite ha; clear ha. 
              exact ihm.
        Qed.
        

        Theorem fold_right_rew_gen : 
          forall (m n : nat) (cs : Vector.t F m) (pf : m = n),
          fold_right add (rew [t F] pf in cs) zero =
          fold_right add cs zero.
        Proof.
          intros m n cs.
          refine(match cs as cs' in Vector.t _ m' 
            return ∀ (pf : m' = n), fold_right add (rew [t F] pf in cs') zero =
              fold_right add cs' zero 
            with 
            | [] => _ 
            | csh :: cst => _ 
            end); intro pf; subst; reflexivity.
        Qed.

        Theorem construct_or_conversations_simulator_completeness_base : 
          ∀ (n : nat) (f : Fin.t n) (usr : Vector.t F n) (g : G)
          (hsr : Vector.t G n) (cstt : Vector.t F n),
          g ^ usr[@f] =
          gop
          (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci)) hsr
          (zip_with (λ ui ci : F, (ui, ci)) usr cstt))[@f]
          (hsr[@f] ^ cstt[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *.
            refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S cstt) as (cstth & csttt & hb).
            destruct (vector_inv_S hsr) as (hsrh & hsrt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihn.
        Qed.



        Theorem construct_or_conversations_simulator_completeness_generic : 
          ∀ (m n : nat) (f : Fin.t (m + S n)) 
          (usl : Vector.t F m) (u : F) (usr : Vector.t F n)
          (hsl : t G m) (g h : G) (hsr : t G n)
          (cst : t F (m + S n)),
          g ^ (usl ++ u :: usr)[@f] =
          gop
          (zip_with (λ (hi : G) '(ui, ci), gop (g ^ ui) (hi ^ opp ci))
          (hsl ++ h :: hsr)
          (zip_with (λ ui ci : F, (ui, ci)) (usl ++ u :: usr) cst))[@f]
          ((hsl ++ h :: hsr)[@f] ^ cst[@f]).
        Proof.
          induction m as [|m ihm].
          +
            cbn; intros *.
            rewrite (vector_inv_0 usl), (vector_inv_0 hsl).
            destruct (vector_inv_S cst) as (csth & cstt & ha).
            destruct (fin_inv_S _ f) as [f' | (f' & hf)].
            ++
              subst. cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply construct_or_conversations_simulator_completeness_base.
          +
            intros *.
            destruct (vector_inv_S usl) as (uslh & uslt & ha). 
            cbn in cst.
            destruct (vector_inv_S cst) as (csth & cstt & hb).
            destruct (vector_inv_S hsl) as (hslh & hslt & hc).
            subst.
            destruct (fin_inv_S _ f) as [f' | (f' & hf)].
            ++
              subst; cbn.
              rewrite <-associative.
              rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
                zero one add mul sub div 
                opp inv G (@eq G) gid ginv gop gpow).
              rewrite field_zero_iff_left,
              vector_space_field_zero,
              monoid_is_right_identity.
              reflexivity.
              typeclasses eauto.
            ++
              subst; cbn.
              eapply ihm.
        Qed.
                
          
      
         
        Lemma construct_or_conversations_schnorr_completeness {m n : nat}
          (x : F) (* secret witness *) (g : G) (* public values *)
          (hsl : Vector.t G m) (h : G) (hsr : Vector.t G n) (R : h = g ^ x) : 
          ∀ (uscs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          generalised_or_accepting_conversations g (hsl ++ [h] ++ hsr)
          (construct_or_conversations_schnorr x g (hsl ++ [h] ++ hsr) uscs c) = true.
        Proof.
          intros *. cbn.
          eapply generalised_or_accepting_conversations_correctness.
          unfold construct_or_conversations_schnorr.
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          (* us is the randomness for commitment and cs is the degree of freedom *)
          (* split us for simulation  *)
          destruct (splitat m us) as (usl & usrh).
          destruct (vector_inv_S usrh) as (u & usr & _).
          (* split cs for simulation *)
          destruct (splitat m cs) as (csl & csr).
          rewrite VectorSpec.splitat_append.
          cbn; split.
          + 
            rewrite !fold_right_app. 
            remember (fold_right add csl zero) as ca.
            remember (fold_right add csr zero) as cb.
            cbn. rewrite <-Heqcb. field.
          +
            intros f.
            rewrite dec_true.
            eapply construct_or_conversations_schnorr_completeness_generic.
            rewrite R; reflexivity.
        Qed.

       
       
        Theorem generalised_construct_or_conversations_schnorr_completeness_fin : 
          forall (m n : nat) (rindex : Fin.t (m + S n)) 
          (hsl : Vector.t G m) (h g : G) (hsr : Vector.t G n) (x : F),
          m = proj1_sig (Fin.to_nat rindex) ->
          (hsl ++ h :: hsr)[@rindex] = g ^ x -> h = g ^ x.
        Proof.
          intros * ha hb.
          assert (hc : rindex = Fin.R m (Fin.F1 : Fin.t (1 + n))).
          eapply fin_to_nat. exact ha.
          subst. rewrite VectorSpec.nth_append_R in hb.
          cbn in hb.
          exact hb.
        Qed.

        
        (* Main completeness *)
        (*  {(x₁, x₂ … xₙ) : h₁ = g^x₁ ∨ h₂ = g^x₂ ∨ … hₙ = g^xₙ} *)
        (* Prover knows rindex  relation g^x = hₘ  *)
        Lemma generalised_construct_or_conversations_schnorr_completeness {n : nat} 
          (rindex : Fin.t (2 + n)) (x : F) (g : G) (hs : Vector.t G (2 + n))
          (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) : 
          Vector.nth hs rindex = g^x -> 
          generalised_or_accepting_conversations g hs
          (generalised_construct_or_conversations_schnorr rindex x g hs uscs c) = true.
        Proof.
          intros * hu.
          unfold generalised_construct_or_conversations_schnorr.
          destruct (splitat (2 + n) uscs) as (us & cs) eqn:hv.
          eapply append_splitat in hv.
          destruct (vector_fin_app_pred (1 + n) rindex us cs) as 
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfa & pfb & ha & hb & hc & hd).
          revert hd.
          subst; cbn. intro hf. rewrite !rew_opp_r.
          destruct (splitat m₁ ((rew [t G] pfa in hs))) as (hsl & hsrr) eqn:ha.
          eapply append_splitat in ha.
          destruct (vector_inv_S hsrr) as (h & hsr & hc).
          rewrite hc in ha. revert hf.
          subst; cbn. intro hf.
          remember ((rew <- [λ n0 : nat, @sigma_proto F G n0 (S n0) n0] pfa in
          @construct_or_conversations_schnorr m₁ m₂ x g (rew [t G] pfa in hs)
          ((v₁ ++ vm :: v₂) ++ v₃ ++ v₄) c))  as sa.  cbn in sa.
          setoid_rewrite <-Heqsa.
          generalize dependent sa. revert hu. generalize dependent hs. 
          generalize dependent  rindex.
          cbn in * |- *. rewrite pfa. 
          intros * ha * hb hc * hd he * hf.
          cbn in * |- *; subst. 
          eapply construct_or_conversations_schnorr_completeness.
          eapply generalised_construct_or_conversations_schnorr_completeness_fin.
          exact hb. exact he.
        Qed.


        (* simulator completeness *)
        Lemma generalised_construct_or_conversations_simulator_completeness {n : nat}
          (g : G) (* public values *) (hs : Vector.t G (2 + n)) : 
          ∀ (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F),
          generalised_or_accepting_conversations g hs
          (generalised_construct_or_conversations_simulator g hs uscs c) = true.
        Proof.
          intros *.
          eapply generalised_or_accepting_conversations_correctness.
          unfold generalised_construct_or_conversations_simulator.
          destruct (splitat (2 + n) uscs) as (us & cs).
          split.
          + cbn; field.
          +

            intros *.
            assert (ha : ∃ (m₁ m₂ : nat), (2 + n = m₁ + (1 + m₂))%nat). 
            exists 1, n. nia.
            destruct ha as (m₁ & m₂ & ha).
            revert us. revert f. revert hs. 
            remember ((c - fold_right add cs zero :: cs)) as cst.
            clear Heqcst. revert cst.
            cbn in * |- *. rewrite !ha.
            intros *. rewrite dec_true.
            destruct (splitat m₁ us) as (usl & usrr) eqn:hb.
            eapply append_splitat in hb.
            destruct (vector_inv_S usrr) as (u & usr & hc).
            subst.
            destruct (splitat m₁ hs) as (hsl & hsrr) eqn:hb.
            eapply append_splitat in hb.
            destruct (vector_inv_S hsrr) as (h & hsr & hc).
            subst.
            eapply construct_or_conversations_simulator_completeness_generic.
        Qed.

        (* Special Soundenss Proof *)

         Lemma generalised_or_sigma_soundness_base_case :
          forall (n : nat) g hs 
          (a : Vector.t G (1 + n)) (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (1 + n))
          (r₁ r₂ : Vector.t F (1 + n)),
          generalised_or_accepting_conversations
            g hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations
            g hs (a; c₂ :: cs₂; r₂) = true ->
          (* c₁ and c₂ are verifier's challenges *)
          c₁ <> c₂ -> 
          (* There is an index where relation R is true and I can 
            extract a witness out of it *)
          ∃ (f : Fin.t (1 + n)) (y : F),
          g^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            g hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            g hs (a; c₂ :: cs₂; r₂) Hb as He.
          clear Ha; clear Hb.
          generalize dependent n.
          intros n hs a. revert c₂; revert c₁.
          generalize dependent n.          
          induction n as [|n IHn].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            exists Fin.F1.
            destruct (vector_inv_S hs) as (hsh & hstl & Hg).
            rewrite (vector_inv_0 hstl) in Hg.
            rewrite Hg; cbn.
            specialize (Har Fin.F1).
            specialize (Hbr Fin.F1).
            cbn in * |- *.
            rewrite dec_true, Hg in Har, Hbr.
            destruct (vector_inv_S a) as (ah & atl & Hh).
            rewrite (vector_inv_0 atl) in Hh.
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hi).
            rewrite (vector_inv_0 rtl₁) in Hi.
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hj).
            rewrite (vector_inv_0 cstl₁) in Hj.
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hk).
            rewrite (vector_inv_0 rtl₂) in Hk.
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hl).
            rewrite (vector_inv_0 cstl₂) in Hl.
            subst.
            assert (Hm : csh₁ <> csh₂).
            intros Hm; eapply Hc; 
            rewrite Hm; reflexivity.
            eapply special_soundness_berry; cbn;
            try (rewrite dec_true);
            [exact Hm | exact Har | exact Hbr].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            cbn in Hal, Har, Hbl, Hbr.
            destruct (vector_inv_S hs) as (hsh & hstl & He).
            destruct (vector_inv_S a) as (ah & atl & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hh).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hj).
            subst; cbn in Hc.
            remember (fold_right add cstl₁ zero) as hcl.
            remember (fold_right add cstl₂ zero) as hcr.
            (* case analysis on challenges *)
            assert (Hd : csh₁ <> csh₂ ∨ 
              (csh₁ = csh₂ ∧ (hcl <> hcr))).
            case_eq (Fdec csh₁ csh₂);
            intros Hd He.
            right.
            refine (conj Hd _).
            intros Hf; eapply Hc;
            rewrite Hd, Hf;
            exact eq_refl. 
            left; exact Hd.
            (* I know that 
            Hd: csh₁ ≠ csh₂ ∨ csh₁ = csh₂ ∧ hcl ≠ hcr*)
            destruct Hd as [Hd | Hd].
            ++
              pose proof (Hbr Fin.F1) as Hk.
              pose proof (Har Fin.F1) as Hj.
              exists (Fin.F1).
              cbn in Hj, Hk |- *.
              rewrite dec_true in Hk, Hj. 
              eapply special_soundness_berry; cbn;
              try (rewrite dec_true);
              [exact Hd | exact Hj | exact Hk].
            ++
              (* inductive case *)
              cbn in IHn.
              destruct Hd as (Hdl & Hdr).
              assert (He : (∀ f : Fin.t (S n),
              (if
                Gdec (g^rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf : 
              (∀ f : Fin.t (S n),
                (if
                  Gdec (g ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f; 
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHn hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as 
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
              Unshelve.
              eapply Gdec.
              eapply Gdec.
        Qed.


        Lemma generalised_or_sigma_soundness_generic :
          forall (m n : nat) 
          (g : G) (hs : Vector.t G (m + (1 + n)))
          (a : Vector.t G (m + (1 + n))) 
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (m + (1 + n)))
          (r₁ r₂ : Vector.t F (m + (1 + n))),
          generalised_or_accepting_conversations 
            g hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations 
            g hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ -> 
          (* I know an index where relation R is true and I can 
            extract a witness out of it *)
          ∃ (f : Fin.t (m + (1 + n))) (y : F),
          g^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            g hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            g hs (a; c₂ :: cs₂; r₂) Hb as He.
          cbn in Hd, He.
          clear Ha; clear Hb.
          generalize dependent n;
          intros n hs a; 
          revert c₂; revert c₁;
          generalize dependent n.
          induction m as [|m' IHm].
          +
            intros * Ha Hb Hc.
            eapply generalised_or_sigma_soundness_base_case;
            try assumption.
            eapply generalised_or_accepting_conversations_correctness_backward;
            exact Ha.
            eapply generalised_or_accepting_conversations_correctness_backward;
            exact Hb.
            exact Hc.
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            cbn in * |- .
            destruct (vector_inv_S hs) as (hsh & hstl & He).
            destruct (vector_inv_S a) as (ah & atl & Hf).
            destruct (vector_inv_S r₁) as (rh₁ & rtl₁ & Hg).
            destruct (vector_inv_S cs₁) as (csh₁ & cstl₁ & Hh).
            destruct (vector_inv_S r₂) as (rh₂ & rtl₂ & Hi).
            destruct (vector_inv_S cs₂) as (csh₂ & cstl₂ & Hj).
            subst; cbn in Hc.
            remember (fold_right add cstl₁ zero) as hcl.
            remember (fold_right add cstl₂ zero) as hcr.
            (* case analysis on challenges *)
            assert (Hd : csh₁ <> csh₂ ∨ 
              (csh₁ = csh₂ ∧ (hcl <> hcr))).
            case_eq (Fdec csh₁ csh₂);
            intros Hd He.
            right.
            refine (conj Hd _).
            intros Hf; eapply Hc;
            rewrite Hd, Hf;
            exact eq_refl. 
            left; exact Hd.
            (* I know that 
            Hd: csh₁ ≠ csh₂ ∨ csh₁ = csh₂ ∧ hcl ≠ hcr*)
            destruct Hd as [Hd | Hd].
            ++
              pose proof (Hbr Fin.F1) as Hk.
              pose proof (Har Fin.F1) as Hj.
              exists (Fin.F1).
              cbn in Hj, Hk |- *.
              rewrite dec_true in Hk, Hj.
              eapply special_soundness_berry; cbn;
              try (rewrite dec_true);
              [exact Hd | exact Hj | exact Hk].
            ++
              (* inductive case *)
              cbn in IHm.
              destruct Hd as (Hdl & Hdr).
              assert (He : (∀ f : Fin.t (m' + S n),
              (if
                Gdec (g ^ rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf : 
              (∀ f : Fin.t (m' + S n),
                (if
                  Gdec (g ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f; 
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHm _  hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as 
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
              Unshelve.
              eapply Gdec.
        Qed.


        (* special soundness *)
        Lemma generalised_or_sigma_soundness 
          {m n : nat}
          (g : G) (* public values *)
          (hsl : Vector.t G m) 
          (h : G)
          (hsr : Vector.t G n) :
          forall (a : Vector.t G (m + (1 + n))) 
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (m + (1 + n)))
          (r₁ r₂ : Vector.t F (m + (1 + n))),
          generalised_or_accepting_conversations 
            g (hsl ++ [h] ++ hsr) (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations 
            g (hsl ++ [h] ++ hsr) (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ ->
          ∃ (f : Fin.t (m + (1 + n))) (y : F),
          g^y = (nth (hsl ++ [h] ++ hsr) f).
        Proof.
          intros * Ha Hb Hc.
          eapply generalised_or_sigma_soundness_generic;
          [exact Ha | exact Hb | exact Hc].
        Qed.


        (* Main soundness proof *)
        Lemma generalised_or_sigma_soundness_main
          {n : nat}
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)):
          forall (a : Vector.t G (2 + n)) 
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (2 + n))
          (r₁ r₂ : Vector.t F (2 + n)),
          generalised_or_accepting_conversations 
            g hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations 
            g hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ -> 
          (* There is an index where relation R is true and can 
            extract a witness out of it *)
          ∃ (f : Fin.t (2 + n)) (y : F),
          g^y = (nth hs f).
        Proof.
          intros *.
          assert (ha : ∃ (m₁ m₂ : nat), (2 + n = m₁ + (1 + m₂))%nat). 
          exists 1, n. nia.
          destruct ha as (m₁ & m₂ & ha).
          revert hs a cs₁ cs₂ r₁ r₂.
          rewrite ha; clear ha.
          intros * ha hb hc.
          destruct (splitat m₁ hs) as (hsl & hsrr) eqn:hd.
          eapply append_splitat in hd.
          destruct (vector_inv_S hsrr) as (h & hsr & he).
          subst.
          eapply generalised_or_sigma_soundness.
          exact ha. exact hb. exact hc.
        Qed.


        (* zero-knowledge *)

        (* honest verifier zero knowledge proof *)

        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        Lemma or_schnorr_distribution_probability_generic 
          {m n : nat}
          (x : F) (* secret witness *)
          (g : G) (* public values *)
          (hsl : Vector.t G m) 
          (h : G)
          (hsr : Vector.t G n) : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_schnorr x 
              g (hsl ++ [h] ++ hsr) uscs c))) → pr = 1 / q.
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

        Lemma generalised_or_schnorr_distribution_probability_generic 
          {n : nat}
          (x : F) (* secret witness *)
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)): 
          forall (rindex : Fin.t (2 + n)) (l : dist (t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_schnorr rindex x 
              g hs uscs c))) → pr = 1 / q.
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

         Lemma generalised_or_schnorr_distribution_transcript_generic 
          {n : nat}
          (x : F) (* secret witness *)
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)) 
          (rindex : Fin.t (2 + n))
          (R : Vector.nth hs rindex = g ^ x) : 
          forall (l : dist (Vector.t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_schnorr rindex x 
              g hs uscs c))) → 
          generalised_or_accepting_conversations g hs trans = true.
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
              now eapply generalised_construct_or_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply generalised_construct_or_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.
        

       
        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n
        *)
        (* This proof is very nice. *)
        (* From Berry's notes : we have (n = 0), and the probability is 
          1 / |lf|^3 *)
        Lemma generalised_or_special_honest_verifier_schnorr_dist 
          {n : nat}
          (x : F) (* secret witness *)
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)) 
          (rindex : Fin.t (2 + n))
          (R : Vector.nth hs rindex = g ^ x) : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_or_schnorr_distribution lf Hlfn rindex x g hs c) ->
            (* it's an accepting conversation and probability is *)
          generalised_or_accepting_conversations g hs a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_or_schnorr_distribution_transcript_generic.
            exact R.
            exact Ha.
          +
            eapply generalised_or_schnorr_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.



         Lemma generalised_or_simulator_distribution_probability_generic 
          {n : nat}
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)) : 
          forall (l : dist (t F ((2 + n) + (1+ n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_simulator 
              g hs uscs c))) → pr = 1 / q.
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

        Lemma generalised_or_simulator_distribution_transcript_generic 
          {n : nat}
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)) : 
          forall (l : dist (Vector.t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_or_conversations_simulator
                g hs uscs c))) → 
          generalised_or_accepting_conversations g hs trans = true.
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
              eapply generalised_construct_or_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply generalised_construct_or_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (* Every element in generalised simulator distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        (* This proof is very nice. *)
        (* From Berry's notes : we have n = 0 and the probability is 
          1 / |lf|^3 *)
        Lemma generalised_or_special_honest_verifier_simulator_dist 
          {n : nat}
          (g : G) (* public values *)
          (hs : Vector.t G (2 + n)) :  
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_or_simulator_distribution lf Hlfn g hs c) ->
            (* it's an accepting conversation and probability is *)
          generalised_or_accepting_conversations g hs a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_or_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_or_simulator_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.


        (* Information theoretic proofs *)
        Lemma generalised_or_special_honest_verifier_zkp 
          {n : nat}
          (x : F) (* secret witness *)
          (g : G) (* public values *)
          (* Prover knows a relation *)
          (hs : Vector.t G (2 + n))
          (rindex : Fin.t (2 + n)) 
          (R : Vector.nth hs rindex = g ^ x) : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) => 
            (generalised_or_accepting_conversations g hs a, p))
            (generalised_or_schnorr_distribution lf Hlfn rindex x g hs c) = 
          List.map (fun '(a, p) => 
            (generalised_or_accepting_conversations g hs a, p))
            (generalised_or_simulator_distribution lf Hlfn g hs c).
        Proof.
          intros ? ? ?.
          eapply map_ext_eq.
          +
            unfold generalised_or_schnorr_distribution,
            generalised_or_simulator_distribution; cbn.
            repeat rewrite distribution_length.
            reflexivity.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_or_special_honest_verifier_schnorr_dist.
            exact R.
            exact Ha. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_or_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed.
        
    End Proofs.
  End Or. 
End DL.