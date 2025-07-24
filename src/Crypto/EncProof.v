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

  Section EncProof.
    Section Def.

      (* Mostly taken and generalised from https://github.com/benadida/helios-server/blob/master/helios/crypto/elgamal.py#L225-L423 *)
      (* 
        c₁ := g^x, c₂ := m_{b} * h^x 
        Ciphertext c is an encryption of [m₀; m₁; ...;m\_{n-1}]. We assume that 
        all the messages are group elements. 
        We contruct a proof 
        log_{g} c₁ = log_{h} (c₂ * m_{b}^{-1})
        and run simulator for the rest 
      *)
      (* (c₁, c₂) = (g^r, m₀ ∙ h^r) ∨ 
         (c₁, c₂) = (g^r, m₁ ∙ h^r) ∨
         .
         .
         .
         (c₁, c₂) = (g^r, mₙ-1 ∙ h^r)
      *)
      (* ms : messages, h and g : group generator, c : ciphertext, x : randomess 
      used in c *)
      (* 
      1. For each index i in [0, n-1]:
      - If i is the true branch (i.e., the ciphertext encrypts m_i with randomness r, so c1 = g^r, c2 = m_i * h^r):
        * We generate a real Chaum-Pedersen commitment: pick a random u_i, and set:
            t1_i = g^{u_i}
            t2_i = h^{u_i}
      - Else (for false branches):
        * We simulate a Chaum-Pedersen proof: pick random u_i, c_i (from Z_q) and set:
            t1_i = g^{u_i} * c1^{-c_i}
            t2_i = h^{u_i} * (c2 / m_i)^{-c_i}
      2. The prover gets challenge c.
      3. For the true branch b, we set the challenge for that branch to be:
          c_b = c - sum_{i != b} c_i   (mod q)
        and then compute the response for the true branch:
          r_b = u_i + c_b * r   (note: here r_i is the randomness we used in the commitment for the true branch, and r is the encryption randomness)
        For the false branches, we already have s_i and c_i.
      4. The proof then consists of:
        (t1_0, t2_0, t1_1, t2_1, ..., t1_{n-1}, t2_{n-1}, c_0, c_1, ..., c_{n-1}, u_0, u_1, ..., r_b, u_{n-1})

      *)
      Definition construct_encryption_proof_elgamal_real {m n : nat} (x : F)
        (uscs : Vector.t F ((m + (1 + n)) + (m + n)))   
        (ms : Vector.t G (m + (1 + n))) (g h : G) (cp : G * G) (c : F) : 
         @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
      Proof.
        (* commitment *)
        destruct (splitat (m + (1 + n)) uscs) as (us & cs).
        (* us is the randomness for commitment and cs is the degree of freedom *)
        (* split us for simulation  *)
        destruct (splitat m us) as (usl & usrh).
        destruct (vector_inv_S usrh) as (u & usr & _).
        (* split cs for simulation *)
        destruct (splitat m cs) as (csl & csr).
        destruct cp as (c₁, c₂). (* ciphertext *)
        destruct (splitat m ms) as (msl & mslt).
        destruct (vector_inv_S mslt) as (_ & msr & _). 
        (* left simulate commitments *)
        set (comml := zip_with (fun ui ci => (ui, ci)) usl csl).
        set (commitl := zip_with (fun mi '(ui, ci) => 
          (gop (g^ui) (c₁^(opp ci)), 
          gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) msl comml).
        (* commitment for the message which prover knows (true branch) *)
        set (com := (g^u, h^u)).
        (* right simulate commitment *)
        set (commr := zip_with (fun ui ci => (ui, ci)) usr csr).
        set (commitr := zip_with (fun mi '(ui, ci) => 
          (gop (g^ui) (c₁^(opp ci)), 
          gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) msr commr).
        (* put c at front of challenges *)
        remember (c - (Vector.fold_right add (csl ++ csr) zero)) as cb.
        (* response *)
        remember (u + cb * x) as res.
        refine ((commitl ++ [com] ++ commitr); 
          c :: csl ++ [cb] ++ csr ; usl ++ [res] ++ usr).
      Defined.
    

      (* simulator *)
      (* does not involve secret x *)
      Definition construct_encryption_proof_elgamal_simulator {m n : nat} 
        (uscs : Vector.t F ((m + (1 + n)) + (m + n)))  
        (ms : Vector.t G (m + (1 + n))) (g h : G) (cp : G * G)
        (c : F) :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
      Proof.
        destruct (splitat (m + (1 + n)) uscs) as (us & cs).
        destruct cp as (c₁, c₂). (* ciphertext *)
        (* (c - Σcs) :: cs *)
        set (cm := rew [Vector.t F] (plus_n_Sm m n) in 
          (c - (Vector.fold_right add cs zero) :: cs)).
        set (comm := zip_with (fun ui ci => (ui, ci)) us cm).
        set (commit := zip_with (fun mi '(ui, ci) => 
          (gop (g^ui) (c₁^(opp ci)), 
          gop (h^ui) (((gop c₂ (ginv mi))^(opp ci))))) ms comm).
        refine(commit; c :: cm; us).
      Defined.


      #[local]
      Definition generalised_accepting_encryption_proof_elgamal_supplement {n : nat}
      (g h : G) (ms : Vector.t G n) (cp : G * G) 
      (pf : @sigma_proto F (G * G) n n n) : bool.
      Proof.
        revert n g h ms cp pf.
        refine
          (fix Fn n := 
          match n with 
          | 0 => fun g h ms cp pf => true
          | S n' => fun g h ms cp pf => 
            match pf with 
            | (a; c; r) => _ 
            end 
          end).
        destruct (vector_inv_S a) as ((ah₁, ah₂) & asr & _).
        destruct (vector_inv_S c) as (ch & csr & _).
        destruct (vector_inv_S r) as (rh & rsr & _).
        destruct (vector_inv_S ms) as (m & msr & _).
        destruct cp as (c₁, c₂).
        exact ((@accepting_conversation F G gop gpow Gdec g c₁ ([ah₁]; [ch]; [rh])) && 
          (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv m)) ([ah₂]; [ch]; [rh])) &&
          (Fn _ g h msr (c₁, c₂) (asr; csr; rsr))).
      Defined.


      (* verify EncProof sigma protocol *)
      (* Check that 
        - the sum of c_i (from i=1 to n) equals c.
        - For each i from 1 to n: check that g^{r_i} = t_1i * c₁^{c_i} and 
          h^{r_i} = t2i * (c₂ / m_i)^{c_i}.
        *)
      Definition generalised_accepting_encryption_proof_elgamal  {m n : nat} 
        (ms : Vector.t G (m + (1 + n)))  (g h : G) (cp : G * G)
        (pf : @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) : bool. 
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
              generalised_accepting_encryption_proof_elgamal_supplement g h ms cp (a; cs; r)
          | right _ => false (* if it's false, there is 
            no point for checking further *)
          end.
      Defined.


      
      (* elgamal distribution *)
      Definition generalised_encryption_proof_elgamal_real_distribution  
        {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
        (x : F) (cp : G * G) (g h : G) (ms : Vector.t G (m + (1 + n))) (c : F) : 
        dist (@sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
        (* draw ((m + (1 + n)) + (m + n)) random elements *)
        uscs <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
        Ret (construct_encryption_proof_elgamal_real x uscs ms g h cp c).

      (* simulator distribution *)
      Definition generalised_encryption_proof_elgamal_simulator_distribution  
        {n m : nat} (lf : list F) (Hlfn : lf <> List.nil) 
        (g h : G) (cp : G * G) (g h : G) (ms : Vector.t G (m + (1 + n))) (c : F) : 
        dist (@sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))) :=
        (* draw ((m + (1 + n)) + (m + n)) random elements *)
        uscs <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) ((m + (1 + n)) + (m + n)) ;;
        Ret (construct_encryption_proof_elgamal_simulator  uscs ms g h cp c).

    End Def.

    Section Proofs.

      (* properties about accepting funciton *)
        (* 
          when generalised_or_accepting_conversations return true 
          then every individual sigma protocol is an 
          accepting conversations and 
          hd c = sum of rest of c 
        *)
        Lemma generalised_accepting_encryption_proof_elgamal_supplement_forward : 
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = true ->
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n, 
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c f]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c f]; [nth r f])) = true
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
              | (au; cu; ru) => fun Hb => _ 
              end eq_refl); intro f. 
            destruct (vector_inv_S au) as ((ah₁, ah₂) & aut & He).
            destruct (vector_inv_S cu) as (cuh & cut & Hf).
            destruct (vector_inv_S ru) as (ruh & rut & Hg).
            destruct (vector_inv_S ms) as (msh & mst & Hi).
            destruct (fin_inv_S _ f) as [Hj | (fs & Hj)];
            subst; simpl. 
            ++
              cbn in Ha.
              eapply andb_true_iff in Ha.
              destruct Ha as (Hal  &  Har).
              split. eapply andb_true_iff in Hal. 
              destruct Hal as [Hall Halr]. exact Hall.
              eapply andb_true_iff in Hal. 
              destruct Hal as [Hall Halr]. exact Halr.
            ++
              simpl in Ha;
              eapply andb_true_iff in Ha.
              destruct Ha as [Hal Har].
              eapply andb_true_iff in Hal.
              destruct Hal as [Hall Halr].
              specialize (IHn g h mst c₁ c₂ (aut; cut; rut) Har).
              cbn in IHn. 
              eapply IHn.
        Qed.

        Lemma generalised_accepting_encryption_proof_elgamal_supplement_backward : 
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n, 
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c f]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c f]; [nth r f])) = true
          end) -> generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = true.
        Proof.
          induction n as [|n IHn].
          +
            intros * Ha.
            rewrite (vector_inv_0 ms);
            cbn; reflexivity.
          + 
            intros * Ha.
            refine 
              (match s as s' return s = s' -> _ 
              with 
              | (au; cu; ru) => fun Hb => _ 
              end eq_refl).
            destruct (vector_inv_S ms) as (msh & mstl & Hd).
            destruct (vector_inv_S au) as ((auh₁, auh₂) & autl & He).
            destruct (vector_inv_S cu) as (cuh & cutl & Hf).
            destruct (vector_inv_S ru) as (ruh & rutl & Hg).
            subst. simpl. 
            eapply andb_true_iff.
            split. 
            ++ 
              pose proof (Ha Fin.F1) as Hi.
              cbn in Hi.
              eapply andb_true_iff.
              exact Hi.
            ++
              eapply IHn.
              intro f. 
              specialize (Ha (Fin.FS f)).
              cbn in Ha. 
              exact Ha.
        Qed.

         Lemma generalised_accepting_encryption_proof_elgamal_supplement_correctness : 
          forall {n : nat} (g h : G) (ms : Vector.t G n) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) n n n),
          generalised_accepting_encryption_proof_elgamal_supplement g h ms (c₁, c₂) s = true <->
          (match s with 
          | (a; c; r) => 
            ∀ f : Fin.t n, 
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c f]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c f]; [nth r f])) = true
          end).
        Proof.
          intros *; split; intro ha;
          [eapply generalised_accepting_encryption_proof_elgamal_supplement_forward |
          eapply generalised_accepting_encryption_proof_elgamal_supplement_backward]; assumption.
        Qed.


        Lemma generalised_accepting_elgamal_accepting_conversations_supplement_app :
          forall (n m : nat) (g h : G) (cp : G * G)
          (msl : Vector.t G n) (msr : Vector.t G m)
          (al : Vector.t (G * G) n) (ar : Vector.t (G * G) m)
          (cl rl : Vector.t F n) (cr rr : Vector.t F m) ,
          generalised_accepting_encryption_proof_elgamal_supplement g h (msl ++ msr)
          cp  ((al ++ ar); (cl ++ cr); (rl ++ rr)) = 
          generalised_accepting_encryption_proof_elgamal_supplement g h msl cp (al; cl; rl) &&
          generalised_accepting_encryption_proof_elgamal_supplement g h msr cp (ar; cr; rr). 
        Proof.
           induction n as [|n IHn].
          +
            intros *.
            rewrite (vector_inv_0 msl).
            rewrite (vector_inv_0 al).
            rewrite (vector_inv_0 cl).
            rewrite (vector_inv_0 rl).
            simpl; reflexivity.
          +
            intros *.
            destruct (vector_inv_S msl) as (mslh & msltl & Hb).
            destruct (vector_inv_S al) as ((alhl, alhr) & altl & Hc).
            destruct (vector_inv_S cl) as (clh & cltl & Hd).
            destruct (vector_inv_S rl) as (rlh & rltl & He).
            destruct cp as (c₁, c₂).
            subst; simpl.
            destruct (Gdec (g ^ rlh) (gop alhl (c₁ ^ clh)));
            destruct (Gdec (h ^ rlh) (gop alhr (gop c₂ (ginv mslh) ^ clh))); 
            simpl; try reflexivity.
            ++
              simpl. eapply IHn.
        Qed.


         Lemma generalised_accepting_elgamal_conversations_correctness_forward : 
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true -> 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end.
        Proof.
          intros * Ha.
          unfold generalised_accepting_encryption_proof_elgamal in Ha.
          refine 
            (match s as s' return s = s' -> _ 
            with 
            | (au; cu; ru) => fun Hb => _ 
            end eq_refl).
          rewrite Hb in Ha.
          destruct (vector_inv_S cu) as (cuh & cut & hc).
          subst. split.
          + 
            destruct (Fdec cuh (fold_right add cut zero)); try congruence.
            exact e.
          +
          intro f.
          pose proof (@generalised_accepting_encryption_proof_elgamal_supplement_forward 
          _ g h ms c₁ c₂ (au; cut; ru)) as hb.
          destruct (Fdec cuh (fold_right add cut zero)); try congruence.
          specialize (hb Ha).
          cbn in hb |- *.
          exact (hb f).
        Qed.


        Lemma generalised_accepting_elgamal_conversations_correctness_backward : 
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end ->  generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true.
        Proof.
          intros * Ha.
          unfold generalised_accepting_encryption_proof_elgamal.
          refine 
            (match s as s' return s = s' -> _ 
            with 
            | (au; cu; ru) => fun Hb => _ 
            end eq_refl).
          destruct (vector_inv_S cu) as (cuh & cutl & Hc).
          assert (Hd : cuh = (fold_right add cutl zero)).
          {
            rewrite Hb in Ha.
            destruct Ha as [hal har].
            rewrite Hc in hal; cbn in hal.
            exact hal.
          }
          rewrite <-Hd.
          destruct (Fdec cuh cuh) as [e | e]; try congruence.
          rewrite Hb in Ha. destruct Ha as (hal & har).
          eapply generalised_accepting_encryption_proof_elgamal_supplement_backward.
          intro f. specialize (har f).
          rewrite Hc in har.
          cbn in har. cbn. exact har.
        Qed.



        Lemma generalised_accepting_elgamal_conversations_correctness: 
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true <-> 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t (m + (1 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end.
        Proof.
          intros *; split; intro ha;
          [eapply generalised_accepting_elgamal_conversations_correctness_forward |
          eapply generalised_accepting_elgamal_conversations_correctness_backward]; assumption.
        Qed.

        (* end of properties *)

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        

       
        (* special soundness *)
        Lemma generalised_accepting_elgamal_conversations_soundness :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (au₁ : t (G * G) (m + (1 + n))) (cu₁ : F) (cut₁ ru₁ : t F (m + (1 + n))) 
          (au₂ : t (G * G) (m + (1 + n))) (cu₂ : F) (cut₂ ru₂ : t F (m + (1 + n))), 
          generalised_accepting_encryption_proof_elgamal ms g h 
            (c₁, c₂) (au₁; cu₁ :: cut₁; ru₁) = true ->
          generalised_accepting_encryption_proof_elgamal ms g h 
            (c₁, c₂) (au₂; cu₂ :: cut₂; ru₂) = true ->
          cu₁ ≠ cu₂ -> ∃ (y : F), g^y = c₁ ∧ 
          ∃ (f : Fin.t (m + (1 + n))), h^y = gop c₂ (ginv (nth ms f)).
        Proof.

        Admitted.


        (* Move this to common utility file for F and G *)
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

        Lemma construct_encryption_proof_elgamal_real_completeness_generic_first_base : 
          forall (n : nat) (f : Fin.t n) (x : F) (g h c₂ : G) 
          (msr : Vector.t G n) (usr csr : Vector.t F n), 
          g ^ usr[@f] = gop (fst (zip_with (λ (mi : G) '(ui, ci), 
          (gop (g ^ ui) ((g ^ x) ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
          (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f]) ((g ^ x) ^ csr[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S csr) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
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

        Lemma construct_encryption_proof_elgamal_real_completeness_generic_second_base : 
          forall (n : nat) (f : Fin.t n) (g h c₁ c₂ : G) 
          (msr : Vector.t G n) (usr csr : Vector.t F n), 
          h ^ usr[@f] = gop (snd (zip_with (λ (mi : G) '(ui, ci),
          (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
            (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f])
          (gop c₂ (ginv msr[@f]) ^ csr[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S csr) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
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

        Lemma construct_encryption_proof_elgamal_real_completeness_generic_first : 
          forall (m n : nat) (f : Fin.t (m + S n)) (x : F) (g h c₁ c₂ : G) 
          (msl : Vector.t G m)
          (msr : Vector.t G n) (c : F) (usl csl : Vector.t F m)
          (u : F) (usr csr : Vector.t F n), c₁ = g^x -> 
          g ^ (usl ++ u + (c - fold_right add (csl ++ csr) zero) * x :: usr)[@f] =
          gop (fst (zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msl
              (zip_with (λ ui ci : F, (ui, ci)) usl csl) ++ (g ^ u, h ^ u)
              :: zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
                gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
                (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f])
          (c₁ ^ (csl ++ c - fold_right add (csl ++ csr) zero :: csr)[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros * hr.
            rewrite (vector_inv_0 usl), (vector_inv_0 csl),
            (vector_inv_0 msl). 
            assert (ha : (zip_with (λ (mi : G) '(ui, ci),
              (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) []
              (zip_with (λ ui ci : F, (ui, ci)) [] [])) = []). reflexivity.
              rewrite ha. clear ha.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
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
              eapply construct_encryption_proof_elgamal_real_completeness_generic_first_base.
          +
            intros * hr.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            destruct (vector_inv_S csl) as (cslh & cslt & hb).
            destruct (vector_inv_S msl) as (mslh & mslt & hc).
            rewrite ha, hb, hc. 
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
              specialize (ihm n f' x g h c₁ c₂ mslt msr (c - cslh) uslt cslt u usr csr
                hr).
              remember (fold_right add (cslt ++ csr) zero) as ct.
              assert (he : c - (cslh + ct) = c - cslh - ct). field.
              rewrite he. 
              eapply ihm.
        Qed.



        Lemma construct_encryption_proof_elgamal_real_completeness_generic_second : 
          forall (m n : nat) (f : Fin.t (m + S n)) (x : F) (g h c₁ c₂ : G) 
          (msl : Vector.t G m) (mc : G)
          (msr : Vector.t G n) (c : F) (usl csl : Vector.t F m)
          (u : F) (usr csr : Vector.t F n), h ^ x = gop c₂ (ginv mc) -> 
          h ^ (usl ++ u + (c - fold_right add (csl ++ csr) zero) * x :: usr)[@f] =
          gop (snd (zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msl 
            (zip_with (λ ui ci : F, (ui, ci)) usl csl) ++ (g ^ u, h ^ u):: zip_with
            (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci), 
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr 
            (zip_with (λ ui ci : F, (ui, ci)) usr csr))[@f])
            (gop c₂ (ginv (msl ++ mc :: msr)[@f]) 
            ^ (csl ++ c - fold_right add (csl ++ csr) zero :: csr)[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros * hr.
            rewrite (vector_inv_0 usl), (vector_inv_0 csl),
            (vector_inv_0 msl). 
            assert (ha : (zip_with (λ (mi : G) '(ui, ci),
              (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) []
              (zip_with (λ ui ci : F, (ui, ci)) [] [])) = []). reflexivity.
              rewrite ha. clear ha.
            destruct (fin_inv_S _ f) as [f' | (f' & ha)].
            ++
              subst; cbn.
              remember ((c - fold_right add csr zero)) as ct.
              rewrite <- hr.
              assert (Hg : (h ^ x) ^ ct = (h ^ (x * ct))).
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
              eapply construct_encryption_proof_elgamal_real_completeness_generic_second_base.
          +
            intros * hr.
            destruct (vector_inv_S usl) as (uslh & uslt & ha).
            destruct (vector_inv_S csl) as (cslh & cslt & hb).
            destruct (vector_inv_S msl) as (mslh & mslt & hc).
            rewrite ha, hb, hc. 
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
              specialize (ihm n f' x g h c₁ c₂ mslt mc msr (c - cslh) uslt cslt u usr csr
                hr).
              remember (fold_right add (cslt ++ csr) zero) as ct.
              assert (he : c - (cslh + ct) = c - cslh - ct). field.
              rewrite he. 
              eapply ihm.
        Qed.

        Lemma construct_encryption_proof_elgamal_simulator_completeness_generic_first_base : 
          forall (n : nat) (f : Fin.t n) (g h c₁ c₂ : G) 
          (msr : Vector.t G n) (usr cstt : Vector.t F n), 
          g ^ usr[@f] = gop (fst (zip_with (λ (mi : G) '(ui, ci), (gop (g ^ ui) (c₁ ^ opp ci),
            gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr 
            (zip_with (λ ui ci : F, (ui, ci)) usr cstt))[@f]) (c₁ ^ cstt[@f]).
        Proof.
           induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S cstt) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
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

        Lemma construct_encryption_proof_elgamal_simulator_completeness_generic_first :
          forall (m n : nat) (f : Fin.t (m + S n)) (msl : Vector.t G m)
            (mc g h c₁ c₂ : G) (msr : Vector.t G n) (usl : Vector.t F m) cst
            (usr : Vector.t F n) (u : F), 
            g ^ (usl ++ u :: usr)[@f] = gop (fst (zip_with (λ (mi : G) '(ui, ci),
            (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci)))
            (msl ++ mc :: msr) (zip_with (λ ui ci : F, (ui, ci)) (usl ++ u :: usr) cst))[@f]) 
            (c₁ ^ cst[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros *.
            rewrite (vector_inv_0 usl), (vector_inv_0 msl).
            destruct (vector_inv_S cst) as (csth & cstt & ha).
            destruct (fin_inv_S _ f) as [f' | (f' & hb)].
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
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_first_base.
        +
          intros *.
          destruct (vector_inv_S usl) as (uslh & uslt & ha). 
          cbn in cst.
          destruct (vector_inv_S cst) as (csth & cstt & hb).
          destruct (vector_inv_S msl) as (mslh & mslt & hc).
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

        Theorem construct_encryption_proof_elgamal_simulator_completeness_generic_second_base : 
          forall (n : nat) (f : Fin.t n) (g h c₁ c₂ : G) 
          (msr : Vector.t G n) (usr cstt : Vector.t F n), 
          h ^ usr[@f] = gop (snd (zip_with (λ (mi : G) '(ui, ci),
          (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci))) msr
          (zip_with (λ ui ci : F, (ui, ci)) usr cstt))[@f]) 
          (gop c₂ (ginv msr[@f]) ^ cstt[@f]).
        Proof.
          induction n as [|n ihn].
          +
            intros *. refine match f with end.
          +
            intros *.
            destruct (vector_inv_S usr) as (usrh & usrt & ha).
            destruct (vector_inv_S cstt) as (csrh & csrt & hb).
            destruct (vector_inv_S msr) as (msrh & msrt & hc).
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

        Theorem construct_encryption_proof_elgamal_simulator_completeness_generic_second : 
          forall (m n : nat) (f : Fin.t (m + S n)) (g h c₁ c₂ : G) 
          (msl : Vector.t G m) (mc : G)
          (msr : Vector.t G n)  (usl : Vector.t F m) cst
          (u : F) (usr : Vector.t F n), 
          h ^ (usl ++ u :: usr)[@f] = gop (snd (zip_with (λ (mi : G) '(ui, ci),
            (gop (g ^ ui) (c₁ ^ opp ci), gop (h ^ ui) (gop c₂ (ginv mi) ^ opp ci)))
            (msl ++ mc :: msr) (zip_with (λ ui ci : F, (ui, ci)) (usl ++ u :: usr) cst))[@f])
          (gop c₂ (ginv (msl ++ mc :: msr)[@f]) ^ cst[@f]).
        Proof.
          induction m as [|m ihm].
          +
            intros *.
            rewrite (vector_inv_0 usl), (vector_inv_0 msl).
            destruct (vector_inv_S cst) as (csth & cstt & ha).
            destruct (fin_inv_S _ f) as [f' | (f' & hb)].
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
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_second_base. 
        +
          intros *.
          destruct (vector_inv_S usl) as (uslh & uslt & ha). 
          cbn in cst.
          destruct (vector_inv_S cst) as (csth & cstt & hb).
          destruct (vector_inv_S msl) as (mslh & mslt & hc).
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


        (* completeness *)
         Context
          {m n : nat}
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (* Prover knows a relation *)
          (msl : Vector.t G m) 
          (mc : G)
          (msr : Vector.t G n) 
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv mc)).


        Lemma construct_encryption_proof_elgamal_real_completeness : 
          forall (c : F) (uscs : Vector.t F ((m + (1 + n)) + (m + n))), 
          generalised_accepting_encryption_proof_elgamal 
          (msl ++ [mc] ++ msr)  g h (c₁, c₂) 
            (construct_encryption_proof_elgamal_real (x : F)
            uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c) = true. 
        Proof.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness.
          unfold construct_encryption_proof_elgamal_real.
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
            rewrite !fold_right_app. cbn.
            field.
          +
            intro f.
            rewrite !dec_true.
            split.
            ++
              eapply construct_encryption_proof_elgamal_real_completeness_generic_first.
              destruct R as [Ra Rb].
              rewrite Ra; reflexivity.
            ++
              eapply construct_encryption_proof_elgamal_real_completeness_generic_second.
              destruct R as [Ra Rb].
              rewrite Rb; reflexivity.
        Qed.


        (* simulator completeness *)
        Lemma construct_encryption_proof_elgamal_simulator_completeness : 
          forall (c : F) (uscs : Vector.t F ((m + (1 + n)) + (m + n))), 
          generalised_accepting_encryption_proof_elgamal 
          (msl ++ [mc] ++ msr)  g h (c₁, c₂) 
            (construct_encryption_proof_elgamal_simulator uscs 
              (msl ++ [mc] ++ msr) g h (c₁, c₂) c) = true.
        Proof using -(x R).
          clear x R.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness.
          unfold construct_encryption_proof_elgamal_simulator.
          destruct (splitat (m + (1 + n)) uscs) as (us & cs).
          cbn; split.
          +

            rewrite fold_right_rew_gen. cbn. field. 
          + 
            intros *.
            rewrite !dec_true.
            split.
            ++
              remember (rew [t F] plus_n_Sm m n in (c - fold_right add cs zero :: cs))
              as cst. clear Heqcst.
              destruct (splitat m us) as (usl & usrh) eqn:ha.
              eapply append_splitat in ha.
              destruct (vector_inv_S usrh) as (u & usr & hb).
              (* split cs for simulation *)
              destruct (splitat m cs) as (csl & csr) eqn:hc.
              eapply append_splitat in hc.
              subst.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_first.
            ++
              remember (rew [t F] plus_n_Sm m n in (c - fold_right add cs zero :: cs))
              as cst. clear Heqcst.
              destruct (splitat m us) as (usl & usrh) eqn:ha.
              eapply append_splitat in ha.
              destruct (vector_inv_S usrh) as (u & usr & hb).
              (* split cs for simulation *)
              destruct (splitat m cs) as (csl & csr) eqn:hc.
              eapply append_splitat in hc.
              subst.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_second.
      Qed.
       

        

        (* zero-knowledge *)




          




    End Proofs.
  End EncProof.
End DL.

