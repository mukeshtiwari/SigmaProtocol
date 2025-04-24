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

  Section Parallel.

    Section Def. 

        
        Definition compose_two_parallel_sigma_protocols {n m r u v w : nat} 
          (s₁ : @sigma_proto F G n m r) (s₂ : @sigma_proto F G u v w) :
          @sigma_proto F G (n + u) (m + v) (r + w) :=
          match s₁, s₂ with 
          | (a₁; c₁; r₁), (a₂; c₂; r₂) =>
            (a₁ ++ a₂; c₁ ++ c₂; r₁ ++ r₂)
          end.


        (*
          Construct parallel Sigma protocol for a 
          the relation R : h = g^x
        *)
        (* input: x g us cs *)
        (* secret x, generator g, commitments us, challenges cs *)
        Definition construct_parallel_conversations_schnorr :
          forall {n : nat},  F -> G ->  Vector.t F n -> Vector.t F n ->
          @sigma_proto F G n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun x g us cs => _
          | S n' => fun x g us cs  => _
          end).
          + 
            (* base case. *)
            refine ([]; []; []).
          + 
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S cs) as (csh & cstl & _).
            exact (@compose_two_parallel_sigma_protocols _ _ _ _ _ _ 
              (@schnorr_protocol F add mul G gpow x g ush csh)
              (Fn _ x g ustl cstl)).
        Defined.

      
        (* Does not involve the secret x *)
        (* input: g h us cs *)
        (* group generator g and h, commitments us, challenges cs *)
        Definition construct_parallel_conversations_simulator :
          forall {n : nat}, 
          G ->  G -> Vector.t F n -> Vector.t F n -> @sigma_proto F G n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun g h us cs => _
          | S n' => fun g h us cs  => _
          end).
          + refine ([]; []; []).
          + 
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S cs) as (csh & cstl & _).
            exact (@compose_two_parallel_sigma_protocols _ _ _ _ _ _ 
              (@schnorr_simulator F opp G gop gpow g h ush csh)
              (Fn _ g h ustl cstl)).
        Defined.

        
        (* Function that takes group generators g, h, and 
        sigma protocol and returns a boolean value *)
        Definition generalised_parallel_accepting_conversations : 
          forall {n : nat}, 
          G -> G -> @sigma_proto F G n n n -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun _ _ p => true
            | S n' => fun g h p => 
              match p with 
              | (a; c ; r) => _ 
              end 
            end).
          destruct (vector_inv_S a) as (ah & atl & _).
          destruct (vector_inv_S c) as (ch & ctl & _).
          destruct (vector_inv_S r) as (rh & rtl & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([ah]; [ch]; [rh])) &&
            (Fn _ g h (atl; ctl; rtl))).
        Defined.


        (* Parallel Schnorr distribution (involves secret x)*)
        Definition generalised_parallel_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (x : F) (g : G) (cs : Vector.t F n) : dist (@sigma_proto F G n n n) :=
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_parallel_conversations_schnorr x g us cs).
        
        
        
        (* Parallel Simulator distribution (without secret x) *)
        Definition generalised_parallel_simulator_distribution 
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (g h : G) (cs : Vector.t F n) : dist (@sigma_proto F G n n n) := 
          (* draw n random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) n ;;
          Ret (construct_parallel_conversations_simulator g h us cs).

    End Def.
      
    Section Proofs.


        (* 
          when generalised_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations.
        *)
        Lemma generalised_parallel_accepting_conversations_correctness_forward : 
          forall (n : nat) g h (s : @sigma_proto F G n n n),
          @generalised_parallel_accepting_conversations n g h s = true ->
          ∀ (f : Fin.t n), 
          match s with 
          | (a; c; r) => 
            @accepting_conversation F G gop gpow Gdec g h 
              ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true
          end.
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +  
            intros * Ha f.
            refine (match f with end).
          +
            intros * Ha f.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hc => _  
            end eq_refl).
            rewrite Hc in Ha.
            destruct (vector_inv_S a) as (ha & ta & Hd).
            destruct (vector_inv_S c) as (hc & tc & He).
            destruct (vector_inv_S r) as (hr & tr & Hf).
            destruct (fin_inv_S _ f) as [hf | (hf & Hg)].
            subst; simpl.
            eapply andb_true_iff in Ha. 
            destruct Ha as (Ha & _).
            rewrite Ha; reflexivity.
            subst ; simpl.
            eapply andb_true_iff in Ha.
            destruct Ha as (_ & Ha).
            exact (IHn _ _ _ Ha hf).
        Qed.



          
        (* When we have accepting conversations, then 
        generalised_accepting accepts it.
        *)
        Lemma generalised_parallel_accepting_conversations_correctness_backward : 
          forall (n : nat) g h (s : @sigma_proto F G n n n), 
          (forall (f : Fin.t n),
            match s with 
            | (a; c; r) => 
              @accepting_conversation F G gop gpow Gdec g h 
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true 
            end) -> 
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof.
          unfold accepting_conversation.
          induction n as [|n IHn];
          simpl.
          +
            intros * Ha.
            reflexivity.
          +
            intros * Ha.
            refine
            (match s as s'
            return s = s' -> _ with 
            |(a; c; r) => fun Hb => _  
            end eq_refl).
            destruct (vector_inv_S a) as (ha & ta & Hc).
            destruct (vector_inv_S c) as (hc & tc & Hd).
            destruct (vector_inv_S r) as (hr & tr & He);
            subst.
            eapply andb_true_iff; split;
            [exact (Ha Fin.F1) |
            eapply IHn; 
            intros fz;
            exact (Ha (Fin.FS fz))].
        Qed.


        Lemma generalised_parallel_accepting_conversations_correctness : 
          forall (n : nat) g h (s : @sigma_proto F G n n n), 
          (forall (f : Fin.t n),
            match s with 
            | (a; c; r) => 
              @accepting_conversation F G gop gpow Gdec g h 
                ([(nth a f)]; [(nth c f)]; [(nth r f)]) = true 
            end) <-> 
          @generalised_parallel_accepting_conversations n g h s = true.
        Proof.
          split;
          [apply generalised_parallel_accepting_conversations_correctness_backward |
          apply generalised_parallel_accepting_conversations_correctness_forward].
        Qed.


        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow} (* vector space *)
          (x : F) (* secret witness *)
          (g h : G) (* public values *) 
          (R : h = g ^ x). (* relation that prover trying to establish, or convince a verifier*)



        (* completeness *)
        Lemma construct_parallel_conversations_schnorr_completeness : 
          forall (n : nat) (us cs : Vector.t F n),
          generalised_parallel_accepting_conversations g h
            (construct_parallel_conversations_schnorr x g us cs) = true.
        Proof.
          induction n as [|n IHn];
          [intros ? ?;
          reflexivity | intros ? ? ].
          destruct (vector_inv_S us) as (hus & tus & Ha).
          destruct (vector_inv_S cs) as (hcs & tcs & Hb).
          rewrite Ha, Hb.
          specialize (IHn tus tcs).
          pose proof 
          generalised_parallel_accepting_conversations_correctness_forward
          _ _ _ _ IHn as Hc.
          eapply 
          generalised_parallel_accepting_conversations_correctness_backward.
          intros ?; cbn.
          remember (construct_parallel_conversations_schnorr x g tus tcs) as s.
          refine
          (match s as s'
          return s = s' -> _ with 
          |(a; c; r) => fun Hb => _  
          end eq_refl).
          destruct (fin_inv_S _ f) as [hd | (hd & Hf)].
          +
            rewrite hd; cbn.
            (* by schnorr completeness *)
            now eapply schnorr_completeness.
          +
            rewrite Hf; cbn.
            specialize (Hc hd);
            rewrite Hb in Hc;
            exact Hc.
        Qed.


        (* simulator completeness *)
        Lemma construct_parallel_conversations_simulator_completeness : 
          forall (n : nat) (us cs : Vector.t F n),
          generalised_parallel_accepting_conversations g h
            (construct_parallel_conversations_simulator g h us cs) = true.
        Proof using -(x R).
          clear x R. (* clear the secret and relation. *)
          induction n as [|n IHn];
          [intros ? ?;
          reflexivity | intros ? ? ].
          destruct (vector_inv_S us) as (hus & tus & Ha).
          destruct (vector_inv_S cs) as (hcs & tcs & Hb).
          rewrite Ha, Hb.
          specialize (IHn tus tcs).
          pose proof 
          generalised_parallel_accepting_conversations_correctness_forward
          _ _ _ _ IHn as Hc.
          eapply 
          generalised_parallel_accepting_conversations_correctness_backward.
          intros ?; cbn.
          remember (construct_parallel_conversations_simulator g h tus tcs) as s.
          refine
          (match s as s'
          return s = s' -> _ with 
          |(a; c; r) => fun Hb => _  
          end eq_refl).
          destruct (fin_inv_S _ f) as [hd | (hd & Hf)].
          +
            rewrite hd; cbn.
            (* by simulator completeness *)
            eapply simulator_completeness.
            Unshelve.
            exact Fdec.
          +
            rewrite Hf; cbn.
            specialize (Hc hd);
            rewrite Hb in Hc;
            exact Hc.
        Qed.


        (* special soundness helper *)
        Lemma generalise_parallel_sigma_soundness_supplement : 
          ∀ (n : nat) (s₁ s₂ : @sigma_proto F G (S n) (S n) (S n)),
          (match s₁, s₂ with 
          | (a₁; c₁; _), (a₂; c₂; _) => 
            two_challenge_vectors_same_everyelem a₁ a₂ ->
            two_challenge_vectors_disjoint_someelem c₁ c₂ ->
            (* accepting conversatation*)
            generalised_parallel_accepting_conversations g h s₁ = true -> 
            (* accepting conversatation*)
            generalised_parallel_accepting_conversations g h s₂ = true ->
            ∃ y : F, g^y = h
          end).
        Proof using -(x R).
          clear x R. (* otherwise, it's trivial :) *)
          induction n as [|n IHn].
          +
            intros ? ?.
            refine 
            (match s₁ as s'
            return s₁ = s' -> _ with 
            |(a₁; c₁; r₁) => fun Ha => _  
            end eq_refl).
            refine 
            (match s₂ as s'
            return s₂ = s' -> _ with 
            |(a₂; c₂; r₂) => fun Hb => _  
            end eq_refl).
            intros Hc Hd He Hf.
            unfold two_challenge_vectors_same_everyelem in Hc.
            destruct Hd as [f Hd].
            destruct (vector_inv_S a₁) as (ha₁ & ta₁ & Hg).
            destruct (vector_inv_S c₁) as (hc₁ & tc₁ & Hh).
            destruct (vector_inv_S r₁) as (hr₁ & tr₁ & Hi).
            rewrite Hg, Hh, Hi in He;
            cbn in He.
            destruct (vector_inv_S a₂) as (ha₂ & ta₂ & Hj).
            destruct (vector_inv_S c₂) as (hc₂ & tc₂ & Hk).
            destruct (vector_inv_S r₂) as (hr₂ & tr₂ & Hl).
            rewrite Hj, Hk, Hl in Hf;
            cbn in Hf.
            (* using the special soundness 
              of Schonorr protocol as 
              base case 
            *)
            eapply special_soundness_berry with
            (a := ha₁) (c₁ := hc₁) (r₁ := hr₁)
            (c₂ := hc₂) (r₂ := hr₂).
            
            rewrite Hh, Hk in Hd.
            destruct (fin_inv_S _ f) as [hf | (hf & Hm)];
            [rewrite hf in Hd;
            cbn in Hd; exact Hd |
            inversion hf].
            apply andb_true_iff in He;
            cbn; exact (proj1 He).
            apply andb_true_iff in Hf;
            cbn.
            rewrite Hg, Hj in Hc.
            specialize (Hc f).
            destruct (fin_inv_S _ f) as [hf | (hf & Hm)].
            rewrite hf in Hc;
            cbn in Hc; rewrite Hc.
            exact (proj1 Hf).
            inversion hf.
          +
            intros ? ?.
            refine 
            (match s₁ as s'
            return s₁ = s' -> _ with 
            |(a₁; c₁; r₁) => fun Ha => _  
            end eq_refl).
            refine 
            (match s₂ as s'
            return s₂ = s' -> _ with 
            |(a₂; c₂; r₂) => fun Hb => _  
            end eq_refl).
            intros Hc Hd He Hf.
            (* interesting way to control the 
            normalisation! *)
            remember (S n) as sn.
            destruct (vector_inv_S a₁) as (ha₁ & ta₁ & Hg).
            destruct (vector_inv_S c₁) as (hc₁ & tc₁ & Hh).
            destruct (vector_inv_S r₁) as (hr₁ & tr₁ & Hi).
            destruct (vector_inv_S a₂) as (ha₂ & ta₂ & Hj).
            destruct (vector_inv_S c₂) as (hc₂ & tc₂ & Hk).
            destruct (vector_inv_S r₂) as (hr₂ & tr₂ & Hl).
            rewrite Hg, Hj in Hc.
            rewrite Hh, Hk in Hd.
            rewrite Hg, Hh, Hi in He.
            rewrite Hj, Hk, Hl in Hf.
            cbn in He, Hf.
            apply andb_true_iff in He, Hf.
            destruct He as [Hel Her].
            destruct Hf as [Hfl Hfr].
            destruct Hd as [f Hm].
            destruct (fin_inv_S _ f) as [hf | (hf & Hn)].
            rewrite hf in Hm;
            cbn in Hm.
            (* 
              using the special soundness 
              of Schonorr protocol as 
              base case 
            *)
            eapply special_soundness_berry with 
            (a := ha₁) (c₁ := hc₁) (r₁ := hr₁)
            (c₂ := hc₂) (r₂ := hr₂).
            exact Hm.
            exact Hel.
            cbn.
            pose proof (Hc f) as Hn;
            rewrite hf in Hn;
            cbn in Hn;
            rewrite Hn;
            exact Hfl.
            (* 
              induction case
            *)
            specialize (IHn (ta₁; tc₁; tr₁)
            (ta₂; tc₂; tr₂));
            cbn in IHn.
            assert (Ho : two_challenge_vectors_same_everyelem ta₁ ta₂).
            intro Ho;
            pose proof (Hc (Fin.FS Ho)) as Hp;
            cbn in Hp;
            exact Hp.
            assert (Hp : two_challenge_vectors_disjoint_someelem tc₁ tc₂).
            exists hf;
            rewrite Hn in Hm;
            cbn in Hm; exact Hm.
            eapply IHn; 
            try assumption.
            Unshelve.
            apply Fdec.
            apply Fdec.
        Qed.


        (* special soundness *)
        Lemma generalise_parallel_sigma_soundness : 
          ∀ (n : nat) (a : Vector.t G (1 + n)) 
          (c₁ r₁ c₂ r₂ : Vector.t F (1 + n)),
          c₁ <> c₂ -> 
          (* accepting conversatation*)
          generalised_parallel_accepting_conversations g h (a; c₁; r₁) = true -> 
          (* accepting conversatation*)
          generalised_parallel_accepting_conversations g h (a; c₂; r₂) = true ->
          ∃ y : F, g^y = h.
        Proof using -(x R).
          clear x R.
          intros * Ha Hb Hc.
          exact (generalise_parallel_sigma_soundness_supplement n
            (a; c₁; r₁) (a; c₂; r₂) 
            (vector_same_implies_same_everyelem _ a a eq_refl)
            (@vector_not_equal_implies_disjoint_someelem _ Fdec _ c₁ c₂ Ha) 
            Hb Hc).
        Qed.


        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        (* Honest Verifier zero-knowledge-proof *)
        Lemma generalised_parallel_schnorr_distribution_transcript_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (cs : Vector.t F n),
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_schnorr x g us cs))) → 
          generalised_parallel_accepting_conversations g h trans = true.
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
              eapply construct_parallel_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_parallel_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.




        Lemma generalised_parallel_schnorr_distribution_probability_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (cs : Vector.t F n) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_schnorr x g us cs))) → 
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


        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        Lemma generalised_parallel_special_honest_verifier_schnorr_dist {n : nat}: 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (cs : Vector.t F n) a b, 
          List.In (a, b) 
            (generalised_parallel_schnorr_distribution lf Hlfn x g cs) ->
            (* it's an accepting conversation and probability is *)
          generalised_parallel_accepting_conversations g h a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) n).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_parallel_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_parallel_schnorr_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.


        (* fact about simultor *)
        Lemma generalised_parallel_simulator_distribution_transcript_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) 
          (trans : sigma_proto) (pr : prob) (cs : Vector.t F n),
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_simulator g h us cs))) → 
          generalised_parallel_accepting_conversations g h trans = true.
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
              eapply construct_parallel_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_parallel_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.



        Lemma generalised_parallel_simulator_distribution_probability_generic {n : nat} : 
          forall (l : dist (Vector.t F n)) (trans : sigma_proto) 
          (pr : prob) (cs : Vector.t F n) (m : nat),
          (∀ (trx : Vector.t F n) (prx : prob), List.In (trx, prx) l → prx = 1 / m) -> 
          List.In (trans, pr) (Bind l (λ us : t F n,
            Ret (construct_parallel_conversations_simulator g h us cs))) → 
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


        (* *)
        Lemma generalised_parallel_special_honest_verifier_simulator_dist {n : nat}: 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (cs : Vector.t F n) (a : sigma_proto) (b : prob),
          List.In (a, b) 
            (generalised_parallel_simulator_distribution lf Hlfn g h cs) ->
            (* first component is true and probability is *)
          generalised_parallel_accepting_conversations g h a = true ∧ 
          b = mk_prob 1 (Pos.of_nat (Nat.pow (List.length lf) n)).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_parallel_simulator_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_parallel_simulator_distribution_probability_generic;
            [intros * Hc;
            eapply uniform_probability_multidraw_prob; exact Hc|
            exact Ha].
        Qed.




        (* distributions is identical (information theoretic soundenss because 
        the most powerful computer can't also distinguish between the two) *)
        Lemma generalised_parallel_special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (n : nat) 
          (cs : Vector.t F n),
          List.map (fun '(a, p) => 
            (generalised_parallel_accepting_conversations g h a, p))
            (@generalised_parallel_schnorr_distribution n lf Hlfn x g cs) = 
          List.map (fun '(a, p) => 
            (generalised_parallel_accepting_conversations g h a, p))
            (@generalised_parallel_simulator_distribution n lf Hlfn g h cs).
        Proof.
          intros ? ? ? ?.
          eapply map_ext_eq.
          + unfold generalised_parallel_schnorr_distribution, 
            generalised_parallel_simulator_distribution;
            cbn. repeat rewrite distribution_length. 
            reflexivity. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_parallel_special_honest_verifier_schnorr_dist.
            exact Ha.
          + 
            intros (aa, cc, rr) y Ha. 
            eapply generalised_parallel_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed.
        (* End of proofs *)
    End Proofs.
  End Parallel.
End DL.