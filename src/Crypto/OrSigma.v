From Coq Require Import Setoid
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


  Section Or. 


    (* Generalised Or composition where you know 1 out of n statements
      ∃ x : g₁^x = h₁ ∨ g₂^x = h₂ ∨ g₃^x= h₃ ... 
            
      One witness out of n statements but if you want to prove 
      that you know k out of n statements then 
      use the following paper https://www.win.tue.nl/~berry/papers/crypto94.pdf
    
    *)

    Section Def.


        Definition compose_two_or_sigma_protocols {n m r u v w : nat} 
          (s₁ : @sigma_proto F G n m r) (s₂ : @sigma_proto F G u v w) :
          @sigma_proto F G (n + u) (m + v) (r + w) :=
        match s₁, s₂ with 
        |(a₁; c₁; r₁), (a₂; c₂; r₂) =>
          (a₁ ++ a₂; c₁ ++ c₂; r₁ ++ r₂)
        end.

        (* Does not involve the secret x *)
        (* gs hs us rs *)
        #[local]
        Definition construct_or_conversations_simulator_supplement :
          forall {n : nat}, 
          Vector.t G n ->  Vector.t G n -> Vector.t F n -> 
          Vector.t F n -> @sigma_proto F G n n n.
        Proof.
          refine(fix Fn n {struct n} := 
          match n with 
          | 0 => fun gs hs us rs => _
          | S n' => fun gs hs us rs  => _
          end).
          + refine (mk_sigma _ _ _ [] [] []).
          + 
            destruct (vector_inv_S gs) as (gsh & gstl & _).
            destruct (vector_inv_S hs) as (hsh & hstl & _).
            destruct (vector_inv_S us) as (ush & ustl & _).
            destruct (vector_inv_S rs) as (rsh & rstl & _).
            exact (compose_two_or_sigma_protocols 
              (@schnorr_simulator F opp G gop gpow gsh hsh ush rsh)
              (Fn _ gstl hstl ustl rstl)).
        Defined.


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
          rs is randomly generated scalors 
          us = usl ++ [u_i] ++ usr
          rs = rsl ++ [_] ++ rsr 
          Prover recomputes: 
          r_i := c - Σ rsl + rsr 

          Uses simulator on (usl ++ usr) (rsl ++ rsr)
          Uses Schnorr protocol u_i r_i 
          Package them together.

          Verifier check the if all the individual 
          sigma protocols are valid and 
          challenges sum up to c.
        *)


        (* 
          x gs hs us rs c. 
          x is secret  
          gs and hs are public group elements 
          and prover knows the (m + 1)th relation.
          us and rs -- verifier let prover cheat -- are randomness 
          c is challenge

          Important: discuss this with Berry. 
        *)

         Definition construct_or_conversations_schnorr {m n : nat} :
          F -> Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros x gs hs usrs c.
          destruct (splitat (m + (1 + n)) usrs) as (us & rs).
          destruct (splitat m gs) as (gsl & gsrt).
          destruct (vector_inv_S gsrt) as (g & gsr & _).
          destruct (splitat m hs) as (hsl & hsrt).
          (* discard h because it is not needed in schnorr protocol *)
          destruct (vector_inv_S hsrt) as (_ & hsr & _).
          (* us := usl ++ [u_i] ++ usr *)
          destruct (splitat m us) as (usl & rurt).
          destruct (vector_inv_S rurt) as (u_i & usr & _).
          (* rs := rsl ++ [_] ++ rsr *)
          destruct (splitat m rs) as (rsl & rsr).
          (* compute r_i  *)
          remember (c - (Vector.fold_right add (rsl ++ rsr) zero)) 
          as r_i.
          (* we will return rsl ++ [r_i] ++ rsr in c field *)
          (* run simulator on gsl hsl usl rsl *)
          remember (construct_or_conversations_simulator_supplement 
            gsl hsl usl rsl) as Ha.
          (* run protocol for known relation *)
          remember (@schnorr_protocol F add mul G gpow x g u_i r_i) as Hb.
          (* run simulator on gsr hsr usr rsr *)
          remember (construct_or_conversations_simulator_supplement 
            gsr hsr usr rsr) as Hc.
          (* now combine all and put the 
            c at front of challenges *)
          refine 
            match Ha, Hb, Hc with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂), (a₃; c₃; r₃) => 
              ((a₁ ++ (a₂ ++ a₃)); c :: c₁ ++ (c₂ ++ c₃); (r₁ ++ (r₂ ++ r₃)))
            end.
        Defined.


        (* simulator *)
        (* does not involve secret x *)
        Definition construct_or_conversations_simulator {m n : nat} :
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros gs hs usrs c.
          destruct (splitat (m + (1 + n)) usrs) as (us & rs).
          destruct (splitat m gs) as (gsl & gsrt).
          destruct (vector_inv_S gsrt) as (g & gsr & _).
          destruct (splitat m hs) as (hsl & hsrt).
          destruct (vector_inv_S hsrt) as (h & hsr & _).
          (* us := usl ++ [u_i] ++ usr *)
          destruct (splitat m us) as (usl & rurt).
          destruct (vector_inv_S rurt) as (u_i & usr & _).
          (* rs := rsl ++ [_] ++ rsr *)
          destruct (splitat m rs) as (rsl & rsr).
          (* compute r_i  *)
          remember (c - (Vector.fold_right add (rsl ++ rsr) zero)) 
          as r_i.
          (* we will return rsl ++ [r_i] ++ rsr in c field *)
          (* run simulator on gsl hsl usl rsl *)
          remember (construct_or_conversations_simulator_supplement 
            gsl hsl usl rsl) as Ha.
          (* run protocol for known relation *)
          remember (@schnorr_simulator F opp G gop gpow g h u_i r_i) as Hb.
          (* run simulator on gsr hsr usr rsr *)
          remember (construct_or_conversations_simulator_supplement 
            gsr hsr usr rsr) as Hc.
          (* now combine all and put the 
            c at front of challenges *)
          refine 
            match Ha, Hb, Hc with 
            |(a₁; c₁; r₁), (a₂; c₂; r₂), (a₃; c₃; r₃) => 
              ((a₁ ++ (a₂ ++ a₃)); c :: c₁ ++ (c₂ ++ c₃); (r₁ ++ (r₂ ++ r₃)))
            end.
        Defined.


        (* Berry suggested to run the schnorr simulator for the first element *)
        Definition construct_or_conversations_simulator_gen {m n : nat} :
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          Vector.t F ((m + (1 + n)) + (m + n)) -> 
          F -> @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
        Proof.
          intros gs' hs' usrs' c.
          assert (Ha : (m + (1 + n) = 1 + (m + n))%nat) by nia.
          set (gs := subst_vector gs' Ha);
          clearbody gs.
          set (hs := subst_vector hs' Ha);
          clearbody hs; clear Ha.
          assert (Ha : (((m + (1 + n)) + (m + n)) = ((1 + (m + n)) + (m + n)))%nat) 
            by nia. 
          set (usrs := subst_vector usrs' Ha);
          clearbody usrs; clear Ha.
          clear gs' hs' usrs'.
          destruct (splitat (1 + (m + n)) usrs) as (us & rs).
          destruct (vector_inv_S gs) as (g & gsr & _).
          destruct (vector_inv_S hs) as (h & hsr & _).
          (* us := [u_i] ++ usr *)
          destruct (vector_inv_S us) as (u_i & usr & _).
          (* compute r_i  *)
          set (r_i := c - (Vector.fold_right add rs zero));
          clearbody r_i.
          set (Ha := @schnorr_simulator F opp G gop gpow g h u_i r_i);
          clearbody Ha.
          set (Hb := construct_or_conversations_simulator_supplement 
            gsr hsr usr rs);
          clearbody Hb.
          refine 
            match Ha, Hb with 
            | (a₁; c₁; r₁), (a₂; c₂; r₂) => _ 
            end. 
          destruct (splitat m a₂) as (al & ar).
          destruct (splitat m c₂) as (cl & cr).
          destruct (splitat m r₂) as (rl & rr).
          refine (al ++ a₁ ++ ar; _; _).
          refine (c :: (cl ++ c₁ ++ cr)).
          refine (rl ++ r₁ ++ rr).
        Defined.

        (* End of simulator *)



        #[local]
        Definition generalised_or_accepting_conversations_supplement : 
          forall {n : nat}, 
          Vector.t G n -> Vector.t G n ->
          @sigma_proto F G n n n -> bool.
        Proof.
          refine
            (fix Fn n := 
            match n with 
            | 0 => fun gs hs Ha => true
            | S n' => fun gs hs Ha => 
              match Ha with 
              | (a₁; c₁; r₁) => _ 
              end 
            end).
          destruct (vector_inv_S gs) as (g & gsr & _).
          destruct (vector_inv_S hs) as (h & hsr & _).
          destruct (vector_inv_S a₁) as (a & asr & _).
          destruct (vector_inv_S c₁) as (c & csr & _).
          destruct (vector_inv_S r₁) as (r & rsr & _).
          exact ((@accepting_conversation F G gop gpow Gdec g h ([a]; [c]; [r])) && 
            (Fn _ gsr hsr (asr; csr; rsr))).
        Defined.


        (* verify or sigma protocol *)
        Definition generalised_or_accepting_conversations : 
          forall {m n : nat}, 
          Vector.t G (m + (1 + n)) -> Vector.t G (m + (1 + n)) ->
          @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)) ->
          bool.
        Proof.
          intros ? ? gs hs Ha.
          refine 
            match Ha with 
            |(a; ct; r) => _ 
            end.
          (* Verifier first checks if challenge c is equal 
            to the rest of challenges *)
          destruct (vector_inv_S ct) as (c & cs & _).
          refine
            match Fdec c (Vector.fold_right add cs zero) with 
            | left _ => 
                (* now check sigma *)
                generalised_or_accepting_conversations_supplement gs hs (a; cs; r)
            | right _ => false (* if it's false, there is 
              no point for checking further *)
            end.
        Defined.


         (* schnorr distribution *)
        Definition generalised_or_schnorr_distribution  
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (x : F) (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_schnorr x gs hs usrs c).

        (* simulator distribution *)
        Definition generalised_or_simulator_distribution  
          {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (m + (1 + n))) (c : F) : 
          dist (@sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
          (* draw ((m + (1 + n)) + (m + n)) random elements *)
          usrs <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
          Ret (construct_or_conversations_simulator gs hs usrs c).


    End Def.

    Section Proofs.


        (* properties about accepting funciton *)
        (* 
          when generalised_or_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations and 
          hd c = sum of rest of c 
        *)
        Lemma generalised_or_accepting_conversations_correctness_supplement_forward : 
          forall {n : nat} (gs hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          generalised_or_accepting_conversations_supplement gs hs s = true ->
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n, 
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f) 
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
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
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


         Lemma generalised_or_accepting_conversations_correctness_supplement_backward : 
          forall {n : nat} (gs hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n,
            @accepting_conversation  F G gop gpow Gdec (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end) -> generalised_or_accepting_conversations_supplement gs hs s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 gs);
            rewrite (vector_inv_0 hs);
            cbn; reflexivity.
          + 
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (a₁; c₁; r₁) => fun Hb => _ 
              end eq_refl).
            destruct (vector_inv_S gs) as (gsh & gstl & Hc).
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
              specialize (IHn gstl hstl (atl₁; ctl₁; rtl₁)).
              assert (Hb : (∀ f : Fin.t n,
              match (atl₁; ctl₁; rtl₁) with
              | (a; c; r) =>
                  @accepting_conversation  F G gop gpow Gdec gstl[@f] hstl[@f]
                    ([a[@f]]; [c[@f]]; [r[@f]]) = true
              end)).
              intros *; exact (Ha (Fin.FS f)).
              exact (IHn Hb).
        Qed.


        Lemma generalised_or_accepting_conversations_correctness_supplement : 
          forall {n : nat} (gs hs : Vector.t G n)
          (s :  @sigma_proto F G n n n),
          generalised_or_accepting_conversations_supplement gs hs s = true <-> 
          match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n,
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c f]; [(nth r f)]) = true
          end.
        Proof.
          intros *.
          split; intros Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_supplement_forward;
            exact Ha.
          +
            eapply generalised_or_accepting_conversations_correctness_supplement_backward;
            exact Ha.
        Qed.



         
        Lemma generalised_or_accepting_conversations_supplement_app :
          forall (n m : nat) 
          (gsl hsl al : Vector.t G n) (gsr hsr ar : Vector.t G m)
          (cl rl : Vector.t F n) (cr rr : Vector.t F m),
          generalised_or_accepting_conversations_supplement
            (gsl ++ gsr) (hsl ++ hsr) 
            ((al ++ ar); (cl ++ cr); (rl ++ rr)) = 
          generalised_or_accepting_conversations_supplement gsl hsl (al; cl; rl)  && 
          generalised_or_accepting_conversations_supplement gsr hsr (ar; cr; rr).
        Proof.
          induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 gsl).
            rewrite (vector_inv_0 hsl).
            rewrite (vector_inv_0 al).
            rewrite (vector_inv_0 cl).
            rewrite (vector_inv_0 rl).
            cbn; reflexivity.
          +
            intros *.
            destruct (vector_inv_S gsl) as (gslh & gsltl & Ha).
            destruct (vector_inv_S hsl) as (hslh & hsltl & Hb).
            destruct (vector_inv_S al) as (alh & altl & Hc).
            destruct (vector_inv_S cl) as (clh & cltl & Hd).
            destruct (vector_inv_S rl) as (rlh & rltl & He).
            subst; cbn.
            destruct (Gdec (gslh ^ rlh) (gop alh (hslh ^ clh))).
            ++
              cbn; eapply IHn.
            ++
              cbn; reflexivity.
        Qed.


        Lemma generalised_or_accepting_conversations_correctness_forward : 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_or_accepting_conversations gs hs s = true -> 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f) 
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
            eapply generalised_or_accepting_conversations_correctness_supplement_forward in
            Ha; exact Ha.
        Qed.


        Lemma generalised_or_accepting_conversations_correctness_backward : 
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))), 
          (match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) -> 
          generalised_or_accepting_conversations gs hs s = true.
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
          destruct m as [|m].
          +
            destruct Ha as [Hal Har].
            specialize (Har Fin.F1).
            rewrite Hc in Hal; cbn 
            in Hal; exact Hal.
          +
            destruct Ha as [Hal Har].
            specialize (Har Fin.F1).
            rewrite Hc in Hal; cbn 
            in Hal; exact Hal.
          +
            rewrite <-Hd.
            destruct (Fdec ch₁ ch₁) eqn:He.
            eapply generalised_or_accepting_conversations_correctness_supplement;
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
          forall {m n : nat} (gs hs : Vector.t G (m + (1 + n)))
          (s :  @sigma_proto F G (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          (match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            @accepting_conversation F G gop gpow Gdec (nth gs f) (nth hs f) 
              ([(nth a f)]; [nth c (Fin.FS f)]; [(nth r f)]) = true)
          end) <-> 
          generalised_or_accepting_conversations gs hs s = true.
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


        Lemma construct_or_conversations_simulator_challenge : 
          forall (n : nat) (gs hs : Vector.t G n)(us cs : Vector.t F n) 
          (a : Vector.t G n) (c r : Vector.t F n),
          (a; c; r) = construct_or_conversations_simulator_supplement gs hs us cs ->
          cs = c.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 gs), 
            (vector_inv_0 hs),
            (vector_inv_0 us),
            (vector_inv_0 cs) in Ha.
            cbn in Ha; inversion Ha; subst.
            rewrite ((vector_inv_0 cs)); 
            reflexivity.
          +
            intros * Ha.
            destruct (vector_inv_S gs) as (gsh & gstl & Hb).
            destruct (vector_inv_S hs) as (hsh & hstl & Hc).
            destruct (vector_inv_S a) as (ah & atl & Hd).
            destruct (vector_inv_S c) as (ch & ctl & He).
            destruct (vector_inv_S r) as (rh & rtl & Hf).
            destruct (vector_inv_S us) as (ush & ustl & Hg).
            destruct (vector_inv_S cs) as (csh & cstl & Hi).
            subst; cbn in Ha.
            remember (construct_or_conversations_simulator_supplement gstl hstl ustl cstl)
            as s.
            refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl).
            rewrite Hb in Ha;
            inversion Ha; subst.
            f_equal.
            eapply Eqdep.EqdepTheory.inj_pair2 in H1, H3, H5.
            eapply IHn.
            apply eq_sym. 
            rewrite <-H3 in Hb.
            exact Hb.
        Qed.



        (* so in OR composition, we need simulator correctness first *)
        #[local]
        Lemma construct_or_conversations_simulator_completeness_supplement :
          forall (m : nat) (gsl hsl : Vector.t G m) (usa csa : Vector.t F m),
          generalised_or_accepting_conversations_supplement gsl hsl
            (construct_or_conversations_simulator_supplement gsl hsl usa csa) = true.
        Proof.
          induction m as [|m' IHm].
          +
            intros *.
            rewrite (vector_inv_0 gsl).
            rewrite (vector_inv_0 hsl).
            rewrite (vector_inv_0 usa).
            rewrite (vector_inv_0 csa).
            reflexivity.
          +
            intros *.
            destruct (vector_inv_S gsl) as (gslh & gsltl & Ha).
            destruct (vector_inv_S hsl) as (hslh & hsltl & Hb).
            destruct (vector_inv_S usa) as (usah & usatl & Hc).
            destruct (vector_inv_S csa) as (csah & csatl & Hd).
            subst; cbn.
            remember (construct_or_conversations_simulator_supplement gsltl hsltl usatl csatl)
            as s.
            refine 
            (match s as s' return s = s' -> _ 
            with 
            | (a₁; c₁; r₁) => fun Hb => _ 
            end eq_refl); cbn.
            eapply andb_true_iff; split.
            ++
              eapply simulator_completeness.
            ++
              rewrite <-Hb, Heqs.
              eapply IHm.
              Unshelve.
              apply Fdec.
        Qed.



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


         Lemma generalise_or_sigma_soundness_base_case :
          forall (n : nat) gs hs 
          (a : Vector.t G (1 + n)) (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (1 + n))
          (r₁ r₂ : Vector.t F (1 + n)),
          @generalised_or_accepting_conversations 0 n 
            gs hs (a; c₁ :: cs₁; r₁) = true ->
          @generalised_or_accepting_conversations _ _
            gs hs (a; c₂ :: cs₂; r₂) = true ->
          (* c₁ and c₂ are verifier's challenges *)
          c₁ <> c₂ -> 
          (* There is an index where relation R is true and I can 
            extract a witness out of it *)
          ∃ (f : Fin.t (1 + n)) (y : F),
          (nth gs f)^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₂ :: cs₂; r₂) Hb as He.
          clear Ha; clear Hb.
          generalize dependent n.
          intros n gs hs a. revert c₂; revert c₁.
          generalize dependent n.          
          induction n as [|n IHn].
          +
            intros * Ha Hb Hc.
            destruct Ha as (Hal & Har).
            destruct Hb as (Hbl & Hbr).
            exists Fin.F1.
            destruct (vector_inv_S gs) as (gsh & gstl & Hf).
            rewrite (vector_inv_0 gstl) in Hf. 
            destruct (vector_inv_S hs) as (hsh & hstl & Hg).
            rewrite (vector_inv_0 hstl) in Hg.
            rewrite Hf, Hg; cbn.
            specialize (Har Fin.F1).
            specialize (Hbr Fin.F1).
            cbn in * |- *.
            rewrite dec_true, Hf, Hg in Har, Hbr.
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
            destruct (vector_inv_S gs) as (gsh & gstl & Hd).
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
                Gdec (gstl[@f] ^ rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf : 
              (∀ f : Fin.t (S n),
                (if
                  Gdec (gstl[@f] ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f; 
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHn gstl hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as 
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
              Unshelve.
              eapply Fdec.
              eapply Gdec.
              eapply Fdec.
              eapply Gdec.
        Qed.



        Lemma generalise_or_sigma_soundness_generic :
          forall (m n : nat) 
          (gs hs : Vector.t G (m + (1 + n)))
          (a : Vector.t G (m + (1 + n))) 
          (c₁ c₂ : F)
          (cs₁ cs₂ : Vector.t F (m + (1 + n)))
          (r₁ r₂ : Vector.t F (m + (1 + n))),
          generalised_or_accepting_conversations 
            gs hs (a; c₁ :: cs₁; r₁) = true ->
          generalised_or_accepting_conversations 
            gs hs (a; c₂ :: cs₂; r₂) = true ->
          c₁ <> c₂ -> 
          (* I know an index where relation R is true and I can 
            extract a witness out of it *)
          ∃ (f : Fin.t (m + (1 + n))) (y : F),
          (nth gs f)^y = (nth hs f).
        Proof.
          intros * Ha Hb.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₁ :: cs₁; r₁) Ha as Hd.
          pose proof generalised_or_accepting_conversations_correctness_forward 
            gs hs (a; c₂ :: cs₂; r₂) Hb as He.
          cbn in Hd, He.
          clear Ha; clear Hb.
          generalize dependent n;
          intros n gs hs a; 
          revert c₂; revert c₁;
          generalize dependent n.
          induction m as [|m' IHm].
          +
            intros * Ha Hb Hc.
            eapply generalise_or_sigma_soundness_base_case;
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
            destruct (vector_inv_S gs) as (gsh & gstl & Hd).
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
                Gdec (gstl[@f] ^ rtl₁[@f])
                  (gop atl[@f] (hstl[@f] ^ cstl₁[@f]))
              then true
              else false) = true)).
              intro f;
              specialize (Har (Fin.FS f));
              exact Har.
              assert (Hf : 
              (∀ f : Fin.t (m' + S n),
                (if
                  Gdec (gstl[@f] ^ rtl₂[@f])
                    (gop atl[@f] (hstl[@f] ^ cstl₂[@f]))
                  then true
                  else false) = true)).
              intro f; 
              specialize (Hbr (Fin.FS f));
              exact Hbr.
              rewrite Heqhcl, Heqhcr in Hdr.
              destruct (IHm _ gstl hstl atl
                (fold_right add cstl₁ zero)
                (fold_right add cstl₂ zero) cstl₁ cstl₂ rtl₁ rtl₂
                (conj eq_refl He) (conj eq_refl Hf) Hdr) as 
              (f & y & IH).
              exists (Fin.FS f), y;
              exact IH.
              Unshelve.
              eapply Fdec.
              eapply Gdec.
        Qed.


         (* Let's prove completeness *)
        (* gs := gsl ++ [g] ++ gsr *)
        (* hs := hsl ++ [h] ++ hsr *)


        
        Context
          {m n : nat}
          (gsl : Vector.t G m) 
          (gsr : Vector.t G n)
          (x : F) (* secret witness *)
          (g h : G) (* public values *)
          (hsl : Vector.t G m) 
          (hsr : Vector.t G n) 
          (R : h = g ^ x).  (* Prover knows (m + 1)th relation *)
      
      
        
        (* completeness *)
        Lemma construct_or_conversations_schnorr_completeness : 
          ∀ (uscs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
            (construct_or_conversations_schnorr x
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
              uscs c) = true.
        Proof.
          intros *.
          unfold generalised_or_accepting_conversations,
          construct_or_conversations_schnorr.
          repeat rewrite VectorSpec.splitat_append.
          destruct (vector_inv_S ([g] ++ gsr)) as (ga & gt & Ha).
          destruct (vector_inv_S ([h] ++ hsr)) as (ha & ht & Hb).
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usa & usb) eqn:Hc.
          destruct (vector_inv_S usb) as (usba & usbb & Hd).
          destruct (splitat m cs) as (csa & csb) eqn:He.
          remember (construct_or_conversations_simulator_supplement gsl hsl usa csa)
          as sa.
          refine
          (match sa as s'
          return sa = s' -> _ with 
          |(a₁; c₁; r₁) => fun Hg => _  
          end eq_refl).
          unfold schnorr_protocol.
          remember (construct_or_conversations_simulator_supplement gt ht usbb csb)
          as sb. 
          refine
          (match sb as s'
          return sb = s' -> _ with 
          |(a₂; c₂; r₂) => fun Hi => _  
          end eq_refl); cbn.
          (*
          fold_right add (csa ++ csbb) zero = c₁ + c₂
          *)
          assert (Hj : c = (fold_right add
          (c₁ ++ c - fold_right add (csa ++ csb) zero :: c₂) zero)).
          remember (c - fold_right add (csa ++ csb) zero :: c₂) as ct.
          rewrite fold_right_app.
          rewrite Heqct; cbn.
          rewrite fold_right_app.
          rewrite Hg in Heqsa;
          eapply construct_or_conversations_simulator_challenge in Heqsa;
          rewrite Heqsa.
          rewrite Hi in Heqsb; 
          eapply construct_or_conversations_simulator_challenge in Heqsb;
          rewrite Heqsb.
          remember (fold_right add c₁ zero) as ca.
          remember (fold_right add c₂ zero) as cb.
          field.
          rewrite <-Hj.
          destruct (Fdec c c) as [Hk | Hk].
          rewrite generalised_or_accepting_conversations_supplement_app.
          eapply andb_true_iff.
          split.
          (* use simulator correctness *)
          rewrite <-Hg, Heqsa.
          eapply construct_or_conversations_simulator_completeness_supplement.
          cbn; eapply andb_true_iff.
          split.
          remember ((c - fold_right add (csa ++ csb) zero)) as ct.
          inversion Ha.
          rewrite <-H0.
          clear Hk; clear H0; clear H1.
          rewrite dec_true, R.
          assert (Hl : (g ^ x) ^ ct = (g ^ (x * ct))).
          rewrite smul_pow_up; 
          reflexivity.
          rewrite Hl; clear Hl.
          assert (Hxc : x * ct = ct * x).
          rewrite commutative; reflexivity.
          rewrite Hxc; clear Hxc.
          rewrite (@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div
            opp inv G (@eq G) gid ginv gop gpow).
          reflexivity.
          exact Hvec.
          (* simulator correctness *)
          rewrite <-Hi, Heqsb.
          inversion Ha; subst.
          inversion Hb; subst.
          eapply Eqdep.EqdepTheory.inj_pair2 in H1, H2.
          subst.
          eapply construct_or_conversations_simulator_completeness_supplement.
          congruence.
        Qed.


        (* This proof basically hinges on simulator_supplement proof. It's 
        here clear presentation *)
        (*simulator completeness*)
        Lemma construct_or_conversations_simulator_completeness : 
          ∀ (uscs : Vector.t F (m + (1 + n) + (m + n))) (c : F),
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
            (construct_or_conversations_simulator
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr)
              uscs c) = true.
        Proof using -(x R).
          clear x R. 
          intros *.
          unfold generalised_or_accepting_conversations,
          construct_or_conversations_simulator.
          repeat rewrite VectorSpec.splitat_append.
          destruct (vector_inv_S ([g] ++ gsr)) as (ga & gt & Ha).
          destruct (vector_inv_S ([h] ++ hsr)) as (ha & ht & Hb).
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          destruct (splitat m us) as (usa & usb) eqn:Hc.
          destruct (vector_inv_S usb) as (usba & usbb & Hd).
          destruct (splitat m cs) as (csa & csb) eqn:He.
          remember (construct_or_conversations_simulator_supplement gsl hsl usa csa)
          as sa.
          refine
          (match sa as s'
          return sa = s' -> _ with 
          |(a₁; c₁; r₁) => fun Hg => _  
          end eq_refl).
          unfold schnorr_simulator.
          remember (construct_or_conversations_simulator_supplement gt ht usbb csb)
          as sb. 
          refine
          (match sb as s'
          return sb = s' -> _ with 
          |(a₂; c₂; r₂) => fun Hi => _  
          end eq_refl); cbn.
          assert (Hj : c = (fold_right add
          (c₁ ++ c - fold_right add (csa ++ csb) zero :: c₂) zero)).
          remember (c - fold_right add (csa ++ csb) zero :: c₂) as ct.
          rewrite fold_right_app.
          rewrite Heqct; cbn.
          rewrite fold_right_app.
          rewrite Hg in Heqsa;
          eapply construct_or_conversations_simulator_challenge in Heqsa;
          rewrite Heqsa.
          rewrite Hi in Heqsb; 
          eapply construct_or_conversations_simulator_challenge in Heqsb;
          rewrite Heqsb.
          remember (fold_right add c₁ zero) as ca.
          remember (fold_right add c₂ zero) as cb.
          field.
          rewrite <-Hj.
          destruct (Fdec c c) as [Hk | Hk].
          rewrite generalised_or_accepting_conversations_supplement_app.
          eapply andb_true_iff.
          split.
          (* use simulator_supplement correctness *)
          rewrite <-Hg, Heqsa.
          eapply construct_or_conversations_simulator_completeness_supplement.
          cbn; eapply andb_true_iff.
          split.
          remember ((c - fold_right add (csa ++ csb) zero)) as ct.
          inversion Ha.
          rewrite <-H0.
          clear Hk; clear H0; clear H1.
          (* schnorr simulator correctness *)
          rewrite dec_true.
          rewrite <-associative.
          inversion Hb.
          rewrite <-(@vector_space_smul_distributive_fadd F (@eq F) 
            zero one add mul sub div 
            opp inv G (@eq G) gid ginv gop gpow).
          rewrite field_zero_iff_left,
          vector_space_field_zero,
          monoid_is_right_identity.
          reflexivity.
          typeclasses eauto.
          (* simulator_supplement correctness *)
          rewrite <-Hi, Heqsb.
          inversion Ha; subst.
          inversion Hb; subst.
          eapply Eqdep.EqdepTheory.inj_pair2 in H1, H2.
          subst.
          eapply construct_or_conversations_simulator_completeness_supplement.
          congruence.
        Qed.

        (* end of completeness *)

        (* special soundness *)
        Lemma generalise_or_sigma_soundness :
         forall (a : Vector.t G (m + (1 + n))) 
         (c₁ c₂ : F)
         (cs₁ cs₂ : Vector.t F (m + (1 + n)))
         (r₁ r₂ : Vector.t F (m + (1 + n))),
         generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) (a; c₁ :: cs₁; r₁) = true ->
         generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) (a; c₂ :: cs₂; r₂) = true ->
         c₁ <> c₂ -> 
         (* There is an index where relation R is true and can 
          extract a witness out of it *)
         ∃ (f : Fin.t (m + (1 + n))) (y : F),
         (nth (gsl ++ [g] ++ gsr) f)^y = (nth (hsl ++ [h] ++ hsr) f).
        Proof using -(x R).
          clear x R.
          intros * Ha Hb Hc.
          eapply generalise_or_sigma_soundness_generic;
          [exact Ha | exact Hb | exact Hc].
        Qed. 




          
        (* honest verifier zero knowledge proof *)

        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        Lemma generalised_or_schnorr_distribution_probability_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_schnorr x 
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          pr = 1 / q.
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



        Lemma generalised_or_schnorr_distribution_transcript_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_schnorr x 
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) trans = true.
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
              eapply construct_or_conversations_schnorr_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_or_conversations_schnorr_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.




        (* Every element in generalised schnorr distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        (* This proof is very nice. *)
        (* From Berry's notes : we have (m = 0 ∧ n = 1) ∨
          (m = 1 ∧ n = 0). In both cases, probability is 
          1 / |lf|^3 *)
        Lemma generalised_or_special_honest_verifier_schnorr_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_or_schnorr_distribution lf Hlfn 
            x (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) c) ->
            (* it's an accepting conversation and probability is *)
          generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) (m + (1 + n) + (m + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_or_schnorr_distribution_transcript_generic; 
            exact Ha.
          +
            eapply generalised_or_schnorr_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.




        Lemma generalised_or_simulator_distribution_probability_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_simulator 
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          pr = 1 / q.
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



        Lemma generalised_or_simulator_distribution_transcript_generic : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_or_conversations_simulator
              (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) uscs c))) → 
          generalised_or_accepting_conversations 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) trans = true.
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
              eapply construct_or_conversations_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply construct_or_conversations_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.



        (* Every element in generalised simulator distribution 
          is an accepting conversation and it's probability 1 / |lf|^n 
          Maybe probabilistic notations but this one is more intuitive.
        *)
        (* This proof is very nice. *)
        (* From Berry's notes : we have (m = 0 ∧ n = 1) ∨
          (m = 1 ∧ n = 0). In both cases, probability is 
          1 / |lf|^3 *)
        Lemma generalised_or_special_honest_verifier_simulator_dist : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_or_simulator_distribution lf Hlfn 
            (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) c) ->
            (* it's an accepting conversation and probability is *)
          generalised_or_accepting_conversations 
          (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) (m + (1 + n) + (m + n))).
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
        Lemma generalised_or_special_honest_verifier_zkp : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) => 
            (generalised_or_accepting_conversations (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) a, p))
            (generalised_or_schnorr_distribution lf Hlfn x (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) c) = 
          List.map (fun '(a, p) => 
            (generalised_or_accepting_conversations (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) a, p))
            (generalised_or_simulator_distribution lf Hlfn (gsl ++ [g] ++ gsr) (hsl ++ [h] ++ hsr) c).
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
            exact Ha. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_or_special_honest_verifier_simulator_dist.
            exact Ha.
        Qed.


    End Proofs.
  End Or.
End DL.