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
From Crypto Require Import Sigma 
  AndSigma.

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

  #[local] Notation "( a ; c ; r )" := 
    (mk_sigma _ _ _ a c r).

  Section Neq.

     (* 
          In this section, we prove that 
          ∃ x₁ x₂ x₃ : g^x₁ = h₁ ∧ g^x₂ = h₂ ∧ g^x₃ = h₃ .... 
          ∧ x₁ <> x₂ ∧ x₁ <> x₃ ∧ x₁ <> ..... ∧ 
          x₂ <> x₃ <> x₂ <> x₄ ...... 
          ...
          ..
          .
      *)
    Section Def. 


        (*
          g₁ h₁ x₁ gs hs xs us c
          Proves that x₁ is not equal to any element in xs, i.e.,
          ∀ x : F, In x xs -> x <> x₁
          using Okamoto protocol
        *)
        (* don't reuse the random numbers! *)
        (* can I use the same challenge? *)

        Definition generalised_construct_neq_conversations_okamoto :
          ∀ {n : nat}, F -> G -> G ->     
          Vector.t F (1 + n) ->
          Vector.t G (1 + n) -> Vector.t G (1 + n) -> 
          Vector.t F  (2 * (1 + n)) -> F -> 
          @sigma_proto F G (1 + n) 1 (2 * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun  x₁ g₁ h₁ xs gs hs  us c => _
            | S n' => fun  x₁ g₁ h₁  xs gs hs  us c => _ 
            end); cbn in * |- *.
          +
            (* base case *)
            destruct (vector_inv_S xs) as (x₂ & _).
            destruct (vector_inv_S gs) as (g₂ & _).
            destruct (vector_inv_S hs) as (h₂ & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & _).
            exact ([gop ((gop g₁ g₂)^u₁) ((gop h₁ h₂)^u₂)]; [c];
              [u₁ + c * x₁ * inv (x₁ - x₂); u₂ + c * inv (x₂ - x₁)]).
          +
            (* induction case *)
            destruct (vector_inv_S gs) as (g₂ & gstl & _).
            destruct (vector_inv_S hs) as (h₂ & hstl & _).
            destruct (vector_inv_S xs) as (x₂ & xstl & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & ustll & _).
            refine 
              match (Fn _ x₁ g₁ h₁  xstl gstl hstl  
                (@subst_vector F _ _ ustll (eq_sym (nat_succ_eq n' (n' + 0)))) c)
              with 
              | (a; _ ; r) => ([gop ((gop g₁ g₂)^u₁) ((gop h₁ h₂)^u₂)] ++ a; [c]; 
                [u₁ + c * x₁ * inv (x₁ - x₂); u₂ + c * inv (x₂ - x₁)] ++ 
                (@eq_rect nat (S (n' + S (n' + 0)))
                  (fun x => Vector.t F x) r _  (nat_succ_eq n' (n' + 0))))
              end.
        Defined.


        (* 
          xs : secrets 
          gs  hs : public values such h := g^x 
          us: randomness 
          c : challenge  

          O (n^2) proof terms! 
          Is there efficient way to model NEQ
        
          Key question: how much randomness I need? 
          We have (2 + n) gs and hs and for 
          (2 * (1 + n) + 2 * n + ...... + 2 = 
          (1 + n) (2 + n)

          The amount of randomenss I need is : (1 + n) * (2 + n)
        *)
        (* 
          This function is going to call 
          generalised_construct_neq_conversations_okamoto
          for each pair 
        *)
        
        #[local]
        Definition generalised_construct_neq_conversations_schnorr_supplement :
          ∀ {n : nat}, Vector.t F (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t G (2 + n) ->  
          Vector.t F ((2 + n) * (1 + n))-> F -> 
          @sigma_proto F G (Nat.div ((2 + n) * (1 + n)) 2) 1 ((2 + n) * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun xs gs hs us c => _
            | S n' => fun xs gs hs us c => _ 
            end); cbn in * |- *.
          +
            (* call Okamoto construction *)
            refine 
              (generalised_construct_neq_conversations_okamoto 
              (hd xs) (hd gs) (hd hs) (tl xs) (tl gs) (tl hs) us c).
          +
            (* requires some complicated reasoning about arithmatic *)
            (* inductive case *)
            (* massage the goal *)
            replace (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) 
            with ((2 * (2 + n')) + (S (n' + S (n' + n' * S n'))))%nat in us.
             (* Take 2 * (S (S n')) from us *)
            destruct (splitat (2 * (1 + S n')) us) as (usl & usr).
            refine
              match (generalised_construct_neq_conversations_okamoto 
              (hd xs) (hd gs) (hd hs) (tl xs) (tl gs) (tl hs) usl c)
              with
              |(a₁; _; r₁) => _ 
              end.
            refine 
              match Fn _ (tl xs) (tl gs) (tl hs)  usr c
              with 
              |(a₂; _; r₂) => _ 
              end.
            set (r := r₁ ++ r₂);
            clearbody r.
            set (a := a₁ ++ a₂);
            clearbody a.
            (* massage a *)
            replace ((1 + S n' + fst (Nat.divmod (n' + S (n' + n' * S n')) 1 0 0)))%nat
            with (fst (Nat.divmod (n' + S (S (n' + S (S (n' + n' * S (S n')))))) 1 1 1))
            in a.
            (* massage r *)
            replace (2 * (1 + S n') + S (n' + S (n' + n' * S n')))%nat with 
            (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) in r.
            refine (a; [c]; r).
            all:try nia.
            eapply nat_divmod.
        Defined.


        (* input xs, gs, hs, us, c *)
        (* size of proofs is O(n^2) for NEQ if 
          we have n statements.
        *) 
        Definition generalised_construct_neq_conversations_schnorr {n : nat} : 
          Vector.t F (2 + n) -> Vector.t G (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          (* first I compute AND protocol *)
          intros xs gs hs us c.
          (* split the randomness us at 2 + n *)
          destruct (splitat (2 + n) us) as (usl & usr).
          (* Now run AND protocol *)
          (refine 
            match @construct_and_conversations_schnorr F 
            add mul G gpow _ xs gs usl c with 
            | (a; _; r) => _ 
            end).
          (* Now call supplement protocol *)
          (refine 
            match generalised_construct_neq_conversations_schnorr_supplement 
              xs gs hs usr c with 
            | (a₁; _; r₁) => (a ++ a₁; [c]; r ++ r₁)
            end).
        Defined. 

        (* simulator *)
        (* Does not involve secret *)
        (* g₁ h₁ gh hs us c *)
        #[local]
        Definition generalised_construct_neq_conversations_simulator_okamoto :
          ∀ {n : nat}, G -> G ->
          Vector.t G (1 + n) -> 
          Vector.t G (1 + n) -> 
          Vector.t F  (2 * (1 + n)) -> F -> 
          @sigma_proto F G (1 + n) 1 (2 * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun g₁ h₁ gs hs us c => _
            | S n' => fun g₁ h₁ gs hs us c => _ 
            end); cbn in * |- *.
          +
            destruct (vector_inv_S gs) as (g₂ & _).
            destruct (vector_inv_S hs) as (h₂ & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & _).
            exact
            ([gop ((gop g₁ g₂)^u₁) (gop ((gop h₁ h₂)^u₂) g₂^(opp c))]; [c];
              [u₁; u₂]).
          +
            destruct (vector_inv_S gs) as (g₂ & gstl & _).
            destruct (vector_inv_S hs) as (h₂ & hstl & _).
            destruct (vector_inv_S us) as (u₁ & ustl & _).
            destruct (vector_inv_S ustl) as (u₂ & ustll & _).
            refine 
              match Fn _ g₁ h₁ gstl hstl 
                (@subst_vector F _ _ ustll (eq_sym (nat_succ_eq n' (n' + 0)))) c 
              with 
              | (a; _; r) => 
                ([gop ((gop g₁ g₂)^u₁) (gop ((gop h₁ h₂)^u₂) g₂^(opp c))] ++ a; [c]; _)
              end.
            replace (S (n' + S (n' + 0)))%nat with 
            (n' + S (S (n' + 0)))%nat in r.
            exact ([u₁; u₂] ++ r).
            nia.
        Defined.

        
        (* gs hs us c *)
        #[local]
        Definition generalised_construct_neq_conversations_simulator_supplement :
          ∀ {n : nat}, 
          Vector.t G (2 + n) -> 
          Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) * (1 + n)) -> F -> 
          @sigma_proto F G (Nat.div ((2 + n) * (1 + n)) 2) 1 ((2 + n) * (1 + n)).
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun gs hs us c => _
            | S n' => fun gs hs us c => _ 
            end); cbn in * |- *.
          +
            exact (generalised_construct_neq_conversations_simulator_okamoto
            (hd gs) (hd hs) (tl gs) (tl hs) us c).
          +
            replace (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) 
            with ((2 * (2 + n')) + (S (n' + S (n' + n' * S n'))))%nat in us.
             (* Take 2 * (S (S n')) from us *)
            destruct (splitat (2 * (1 + S n')) us) as (usl & usr).
            refine
              match (generalised_construct_neq_conversations_simulator_okamoto 
              (hd gs) (hd hs) (tl gs) (tl hs) usl c)
              with
              |(a₁; _; r₁) => _ 
              end.
            refine 
              match Fn _ (tl gs) (tl hs) usr c
              with 
              |(a₂; _; r₂) => _ 
              end.
            set (r := r₁ ++ r₂);
            clearbody r.
            set (a := a₁ ++ a₂);
            clearbody a.
            replace ((1 + S n' + fst (Nat.divmod (n' + S (n' + n' * S n')) 1 0 0)))%nat
            with (fst (Nat.divmod (n' + S (S (n' + S (S (n' + n' * S (S n')))))) 1 1 1))
            in a.
            (* massage r *)
            replace (2 * (1 + S n') + S (n' + S (n' + n' * S n')))%nat with 
            (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) in r.
            refine (a; [c]; r).
            all:try nia.
            eapply nat_divmod.
        Defined.


            
        (* input gs, hs, us, c *)
        (* does not involve secret *)
        Definition generalised_construct_neq_conversations_simulator {n : nat} : 
          Vector.t G (2 + n) -> Vector.t G (2 + n) -> 
          Vector.t F ((2 + n) + ((2 + n) * (1 + n))) -> F ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)).
        Proof.
          (* first I compute AND protocol simulator *)
          intros gs hs us c.
          (* split the randomness us at 2 + n *)
          destruct (splitat (2 + n) us) as (usl & usr).
          (* run AND protocol simulator *)
          refine 
            match @construct_and_conversations_simulator F 
            opp G gop gpow _ gs hs usl c with 
            | (a; _; r) => _ 
            end.
          refine 
            match generalised_construct_neq_conversations_simulator_supplement 
              gs hs usr c with 
            | (a₁; _; r₁) => (a ++ a₁; [c]; r ++ r₁)
            end.
        Defined.

        (* end simulator *)

        (* verification equation *)

        (* verification equation of Okamoto protocol *)
        (* g₁ h₁ gs hs sigma_proof *)
        #[local]
        Definition generalised_neq_accepting_conversations_okamoto :
          ∀ {n : nat}, G -> G ->    
          Vector.t G (1 + n) -> Vector.t G (1 + n) -> 
          @sigma_proto F G (1 + n) 1 (2 * (1 + n)) -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun  g₁ h₁ gs hs us => _
            | S n' => fun  g₁ h₁ gs hs us => _ 
            end); cbn in * |- *.
          +
            refine 
              match us with 
              |(a; c; r) => _ 
              end.
            (*
              Verifies the following equation
              (g₁ * g₂)^r₁ * (h₁ * h₂)^r₂ = a₁ * g₂^c₁
            *)
            destruct (vector_inv_S gs) as (g₂ & _).
            destruct (vector_inv_S hs) as (h₂ & _).
            destruct (vector_inv_S a) as (a₁ & _).
            destruct (vector_inv_S c) as (c₁ & _).
            destruct (vector_inv_S r) as (r₁ & rtl & _).
            destruct (vector_inv_S rtl) as (r₂ & _).
            refine 
              match Gdec 
                (gop ((gop g₁ g₂)^r₁) ((gop h₁ h₂)^r₂)) 
                (gop a₁ (g₂^c₁))
              with 
              | left _ => true 
              | right _ => false 
              end.
          +
            refine 
              match us with 
              |(a; c; r) => _ 
              end.
            destruct (vector_inv_S gs) as (g₂ & gstl & _).
            destruct (vector_inv_S hs) as (h₂ & hstl & _).
            destruct (vector_inv_S a) as (a₁ & atl & _).
            destruct (vector_inv_S c) as (c₁ & _).
            destruct (vector_inv_S r) as (r₁ & rtl & _).
            destruct (vector_inv_S rtl) as (r₂ & rtll & _).
            refine 
              match Gdec 
                (gop ((gop g₁ g₂)^r₁) ((gop h₁ h₂)^r₂)) 
                (gop a₁ (g₂^c₁))
              with
              | left _ => Fn _ g₁ h₁ gstl hstl (atl; c; _) (* check the rest *)
              | right _ => false (* no point of checking the rest *)
              end.
            (* 
              massage rtll to the goal
            *)
            refine 
              (@eq_rect nat (n' + S (S (n' + 0)))%nat 
                (fun x => Vector.t F x) rtll (S (n' + S (n' + 0)))
                (eq_sym (nat_succ_eq n' (n' + 0)))).
        Defined.

        
        Definition generalised_neq_accepting_conversations_supplement :
          forall {n : nat}, 
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          @sigma_proto F G (Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) * (1 + n)) -> bool.
        Proof.
          refine(fix Fn n {struct n} := 
            match n with 
            | 0 => fun gs hs sig => _
            | S n' => fun gs hs sig => _ 
            end); cbn in * |- *.
          +
            (* call Okamoto verification *)
            refine 
              (generalised_neq_accepting_conversations_okamoto 
                (hd gs) (hd hs) (tl gs) (tl hs) sig).
          +
            (* inductive case *)
            refine 
              match sig with 
              |(a; c; r) => _ 
              end.
            destruct (vector_inv_S gs) as (g₁ & gstl & _).
            destruct (vector_inv_S hs) as (h₁ & hstl & _).
            rewrite nat_divmod in a.
            destruct (splitat (2 + n') a) as (al & ar).
            replace (S (S (n' + S (S (n' + S (S (n' + n' * S (S n')))))))) 
            with ((2 * (2 + n')) + (S (n' + S (n' + n' * S n'))))%nat in r.
            destruct (splitat (2 * (2 + n')) r) as (rl & rr).
            (* 
              Call generalised_neq_conversations_okamoto and if it 
              returns true than continue checking else 
              break. 
            *)
            refine 
              match generalised_neq_accepting_conversations_okamoto 
                g₁ h₁ gstl hstl (al; c; rl)
              with 
              | true => Fn _ gstl hstl (ar ; c; rr)
              | _ => false
              end.
            nia.
        Defined.




        Definition generalised_neq_accepting_conversations {n : nat} :
          Vector.t G (2 + n) -> Vector.t G (2 + n) ->
          @sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
            ((2 + n) + (2 + n) * (1 + n)) -> bool.
        Proof.
          intros gs hs sig.
          (* split the sig at (2 + n) *)
          refine 
            match sig with 
            |(a; c; r) => _ 
            end.
          (* split commitments at (2 + n )*)
          destruct (splitat (2 + n) a) as (al & ar).
          (* split responses at (2 + n)*)
          destruct (splitat (2 + n) r) as (rl & rr).
          (* Run AND verifier on (al; c; rl) *)
          refine 
            match 
              @generalised_and_accepting_conversations F G gop gpow Gdec _ gs hs (al; c; rl)
            with 
            | true => _ 
            | _ => false (* No point of checking futher *) 
            end.
          (* run Okamoto verifier on (ar; c; rr) *)
          exact (generalised_neq_accepting_conversations_supplement gs hs (ar; c; rr)).
        Defined.
          
        (* end verification *)

        (* distribution (zero-knowledge) *)

        Definition generalised_neq_schnorr_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (xs : Vector.t F (2 + n)) (gs hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          (* draw ((2 + n) + ((1 + n) + (1 + n))) random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_schnorr xs gs hs us c).


        Definition generalised_neq_simulator_distribution  
          {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
          (gs hs : Vector.t G (2 + n)) (c : F) : 
          dist (@sigma_proto F G ((2 + n) + Nat.div ((2 + n) * (1 + n)) 2) 1
          ((2 + n) + (2 + n) * (1 + n))) :=
          (* draw ((2 + n) + ((1 + n) + (1 + n))) random elements *)
          us <- repeat_dist_ntimes_vector 
            (uniform_with_replacement lf Hlfn) ((2 + n) + ((2 + n) * (1 + n))) ;;
          Ret (generalised_construct_neq_conversations_simulator gs hs us c).
        
    End Def. 

    Section Proofs.


      



    End Proofs.
  End Neq.
End DL.