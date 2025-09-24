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


      Definition construct_encryption_proof_elgamal_commitment {m n : nat}
        (uscs : Vector.t F ((m + (1 + n)) + (m + n)))   
        (ms : Vector.t G (m + (1 + n))) (g h : G) (cp : G * G) : 
        Vector.t (G * G) (m + (1 + n)).
      Proof.
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
        exact (commitl ++ [com] ++ commitr).
      Defined.

      Definition construct_encryption_proof_elgamal_real {m n : nat} (x : F)
        (uscs : Vector.t F ((m + (1 + n)) + (m + n)))   
        (ms : Vector.t G (m + (1 + n))) (g h : G) (cp : G * G) (c : F) : 
         @sigma_proto F (G * G) (m + (1 + n)) (1 + (m + (1 + n))) (m + (1 + n)).
      Proof.
        (* commitment *)
        set (comm := @construct_encryption_proof_elgamal_commitment m n 
          uscs ms g h cp).
        destruct (splitat (m + (1 + n)) uscs) as (us & cs).
        (* us is the randomness for commitment and cs is the degree of freedom *)
        (* split us for simulation  *)
        destruct (splitat m us) as (usl & usrh).
        destruct (vector_inv_S usrh) as (u & usr & _).
        (* split cs for simulation *)
        destruct (splitat m cs) as (csl & csr).
        (* put c at front of challenges *)
        remember (c - (Vector.fold_right add (csl ++ csr) zero)) as cb.
        (* response *)
        remember (u + cb * x) as res.
        refine (comm; 
          c :: csl ++ [cb] ++ csr ; usl ++ [res] ++ usr).
      Defined.

      Definition generalised_construct_encryption_proof_elgamal_real {n : nat}
          (rindex : Fin.t (2 + n)) (x : F) (uscs : Vector.t F ((2 + n) + (1 + n))) 
          (ms : Vector.t G (2 + n))
          (g h : G) (cp : G * G) (c : F) : 
          @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n).
      Proof.
        destruct (splitat (2 + n) uscs) as (us & cs).
        destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as 
        (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
        destruct pfaa as [pfa].
        destruct pfbb as [pfb].
        destruct haa as [ha].
        destruct ha as (ha & hb & hc & hd).
        generalize dependent ms. generalize dependent us. 
        generalize dependent cs. generalize dependent rindex. 
        cbn in * |- *. rewrite !pfa, !pfb. cbn.
        intros rindex ha cs hb us hc hd ms. 
        pose proof (@construct_encryption_proof_elgamal_real m₁ m₂ 
         x (us ++ cs) ms g h cp c) as he. exact he.
      Defined.

      (* simulator *)
      (* does not involve secret randomness x *)
      Definition generalised_construct_encryption_proof_elgamal_simulator {n : nat} 
        (uscs : Vector.t F ((2 + n) + (1 + n)))  
        (ms : Vector.t G ((2 + n))) (g h : G) (cp : G * G)
        (c : F) :  @sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n)).
      Proof.
        destruct (splitat ((2 + n)) uscs) as (us & cs).
        destruct cp as (c₁, c₂). (* ciphertext *)
        (* (c - Σcs) :: cs *)
        set (cm := (c - (Vector.fold_right add cs zero) :: cs)).
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
        (* g^rh = ah₁ * c₁^ch ∧ 
          g^rh = ah₂ * (c₂ * m^{-1})^ch 
        *)
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
      Definition generalised_accepting_encryption_proof_elgamal  {n : nat} 
        (ms : Vector.t G n)  (g h : G) (cp : G * G)
        (pf : @sigma_proto F (G * G) n (1 + n) n) : bool. 
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
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil) (rindex : Fin.t (2 + n))
        (x : F) (cp : G * G) (g h : G) (ms : Vector.t G ((2 + n))) (c : F) : 
        dist (@sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))) :=
        (* draw ((m + (1 + n)) + (m + n)) random elements *)
        uscs <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) (((2 + n)) + (1 + n)) ;;
        Ret (generalised_construct_encryption_proof_elgamal_real 
          rindex x uscs ms g h cp c).

      (* simulator distribution *)
      Definition generalised_encryption_proof_elgamal_simulator_distribution  
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil) 
        (g h : G) (cp : G * G) (ms : Vector.t G ((2 + n))) (c : F) : 
        dist (@sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))) :=
        (* draw ((m + (1 + n)) + (m + n)) random elements *)
        uscs <- repeat_dist_ntimes_vector 
          (uniform_with_replacement lf Hlfn) (((2 + n)) + (1 + n)) ;;
        Ret (generalised_construct_encryption_proof_elgamal_simulator  
          uscs ms g h cp c).



    End Def.

    Section Proofs.


      (* properties about accepting function *)
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

        Lemma generalised_accepting_elgamal_conversations_correctness_gen : 
          forall {n : nat} (g h : G) (ms : Vector.t G ((2 + n))) (c₁ c₂ : G)
          (s :  @sigma_proto F (G * G) ((2 + n)) (1 + ((2 + n))) ((2 + n))),
          generalised_accepting_encryption_proof_elgamal ms g h (c₁, c₂) s = true <-> 
          match s with 
          | (a; c; r) => 
            Vector.hd c = Vector.fold_right add (Vector.tl c) zero ∧
            (∀ (f : Fin.t ((2 + n))),
            (@accepting_conversation F G gop gpow Gdec g c₁ 
              ([fst (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true ∧ 
            (@accepting_conversation F G gop gpow Gdec h (gop c₂ (ginv (nth ms f))) 
              ([snd (nth a f)]; [nth c (Fin.FS f)]; [nth r f])) = true)
          end.
        Proof.
          intros n.
          assert (ha : (∃ (m₁ m₂ : nat), (2 + n) = (m₁ + (1 + m₂)))%nat).
          exists 1, n. reflexivity.
          destruct ha as (m₁ & m₂ & ha).
          rewrite !ha.
          intros *. 
          eapply generalised_accepting_elgamal_conversations_correctness.
        Qed.


        (* end of the properties about verification function *)

        Context
          {Hvec: @vector_space F (@eq F) zero one add mul sub 
            div opp inv G (@eq G) gid ginv gop gpow}.

        (* add field *)
        Add Field field : (@field_theory_for_stdlib_tactic F
          eq zero one opp add mul sub inv div vector_space_field).

        (* special soundness *)
        Lemma generalised_accepting_elgamal_soundness :
          forall {m n : nat} (g h : G) (ms : Vector.t G (m + (1 + n))) (c₁ c₂ : G)
          (a : t (G * G) (m + (1 + n))) (cu₁ : F) (cut₁ ru₁ : t F (m + (1 + n))) 
          (cu₂ : F) (cut₂ ru₂ : t F (m + (1 + n))), 
          generalised_accepting_encryption_proof_elgamal ms g h 
            (c₁, c₂) (a; cu₁ :: cut₁; ru₁) = true ->
          generalised_accepting_encryption_proof_elgamal ms g h 
            (c₁, c₂) (a; cu₂ :: cut₂; ru₂) = true -> 
          cu₁ ≠ cu₂ -> ∃ (y : F), g^y = c₁ ∧ 
          ∃ (f : Fin.t (m + (1 + n))), h^y = gop c₂ (ginv (nth ms f)).
        Proof.
          intros * ha hb hc.
          eapply generalised_accepting_elgamal_conversations_correctness in ha, hb.
          cbn in ha, hb.
          generalize dependent n.
          generalize dependent cu₂.
          revert cu₁.
          induction m as [|m ihm].
          +
            intros * hc * [ha hb] [hd he].
            destruct (vector_inv_S ms) as (msh & mstl & He).
            destruct (vector_inv_S a) as ((ahl, ahr) & alt & Hf).
            destruct (vector_inv_S ru₁) as (ruh₁ & rutl₁ & Hh).
            destruct (vector_inv_S ru₂) as (ruh₂ & rult₂ & Hi).
            destruct (vector_inv_S cut₁) as (cuth₁ & cutl₁ & Hj).
            destruct (vector_inv_S cut₂) as (cuth₂ & cutl₂ & Hk).
            subst. cbn in hc.
            remember (fold_right add cutl₁ zero) as hcl.
            remember (fold_right add cutl₂ zero) as hcr.
            (* case analysis on challenges *)
            assert (hcase : cuth₁ <> cuth₂ ∨ 
              (cuth₁ = cuth₂ ∧ (hcl <> hcr))).
            {
              case_eq (Fdec cuth₁ cuth₂);
              intros huu hv.
              right.
              refine (conj huu _). 
              intro hf. eapply hc.
              subst. rewrite hf.
              reflexivity.
              left. exact huu. 
            }
          
          (* I know that 
           hcase : cuth₁ ≠ cuth₂ ∨ cuth₁ = cuth₂ ∧ hcl ≠ hcr*)
            destruct hcase as [hcase | hcase].
            ++
              specialize (he Fin.F1).
              specialize (hb Fin.F1).
              rewrite dec_true in he, hb.
              cbn in he, hb.
              destruct he as [hel her].
              destruct hb as [hbl hbr].
              rewrite dec_true in her, hbr.
              (* witness *)
              exists ((ruh₁ - ruh₂) * inv (cuth₁ - cuth₂)).
              split.
              +++
                eapply f_equal with (f := ginv) in hel.
                rewrite connection_between_vopp_and_fopp in hel.
                rewrite group_inv_flip  in hel.
                rewrite commutative in hel.
                pose proof (@rewrite_gop G gop _ _ _ _ hbl hel) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahl (c₁ ^ cuth₁) = gop (c₁ ^ cuth₁) ahl).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
                in Hcom.
                assert (Hwt : (gop ahl (gop (ginv ahl) (ginv (c₁ ^ cuth₂)))) = 
                (ginv (c₁ ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) = 
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone c₁).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              +++ 
                exists Fin.F1. cbn.
                remember (gop c₂ (ginv msh)) as ct.
                eapply f_equal with (f := ginv) in her.
                rewrite connection_between_vopp_and_fopp in her.
                rewrite group_inv_flip  in her.
                rewrite commutative in her.
                pose proof (@rewrite_gop G gop _ _ _ _ hbr her) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahr (ct ^ cuth₁) = gop (ct ^ cuth₁) ahr).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
                in Hcom.
                assert (Hwt : (gop ahr (gop (ginv ahr) (ginv (ct ^ cuth₂)))) = 
                (ginv (ct ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) = 
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone ct).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
            ++
              destruct hcase as (hcasel & hcaser).
              assert (ht : cutl₁ <> cutl₂).
              {
                subst. intro ha. eapply hcaser.
                subst. reflexivity.
              }
              destruct (@vector_not_equal_implies_disjoint_someelem F Fdec _ 
                cutl₁ cutl₂ ht) as (f & ha).
              destruct (hb (Fin.FS f)) as (hbl & hbr); clear hb.
              destruct (he (Fin.FS f)) as (hel & her); clear he.
              rewrite dec_true in hbl, hbr, hel, her.
              cbn in * |- .
              remember (rutl₁[@f]) as rf₁.
              remember (cutl₁[@f]) as cf₁.
              remember (rult₂[@f]) as rf₂.
              remember (cutl₂[@f]) as cf₂.
              remember (fst alt[@f]) as a.
              exists ((rf₁ - rf₂) * inv (cf₁ - cf₂)).
              split.
              +++
                eapply f_equal with (f := ginv) in hel.
                rewrite connection_between_vopp_and_fopp in hel.
                rewrite group_inv_flip  in hel.
                rewrite commutative in hel.
                pose proof (@rewrite_gop G gop _ _ _ _ hbl hel) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop a (c₁ ^ cf₁) = gop (c₁ ^ cf₁) a).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
                in Hcom.
                assert (Hwt : (gop a (gop (ginv a) (ginv (c₁ ^ cf₂)))) = 
                (ginv (c₁ ^ cf₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cf₁ + opp cf₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cf₁ + opp cf₂) * inv (cf₁ + opp cf₂) = 
                (inv (cf₁ + opp cf₂) * (cf₁ + opp cf₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone c₁).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cf₁ cf₂ ha as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              +++
                exists (Fin.FS f).
                cbn.
                remember (snd alt[@f]) as sa.
                remember (gop c₂ (ginv mstl[@f])) as ct.
                eapply f_equal with (f := ginv) in her.
                rewrite connection_between_vopp_and_fopp in her.
                rewrite group_inv_flip  in her.
                rewrite commutative in her.
                pose proof (@rewrite_gop G gop _ _ _ _ hbr her) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop sa (ct ^ cf₁) = gop (ct ^ cf₁) sa).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
                in Hcom.
                assert (Hwt : (gop sa (gop (ginv sa) (ginv (ct ^ cf₂)))) = 
                (ginv (ct ^ cf₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cf₁ + opp cf₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cf₁ + opp cf₂) * inv (cf₁ + opp cf₂) = 
                (inv (cf₁ + opp cf₂) * (cf₁ + opp cf₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone ct).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cf₁ cf₂ ha as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
          +
            (* inductive case *)    
            intros * hc * [ha hb] [hd he].
            destruct (vector_inv_S ms) as (msh & mstl & He).
            destruct (vector_inv_S a) as ((ahl, ahr) & alt & Hf).
            destruct (vector_inv_S ru₁) as (ruh₁ & rutl₁ & Hh).
            destruct (vector_inv_S ru₂) as (ruh₂ & rutl₂ & Hi).
            destruct (vector_inv_S cut₁) as (cuth₁ & cutl₁ & Hj).
            destruct (vector_inv_S cut₂) as (cuth₂ & cutl₂ & Hk).
            cbn in hc.
            remember (fold_right add cutl₁ zero) as hcl.
            remember (fold_right add cutl₂ zero) as hcr.
            (* case analysis on challenges *)
            assert (hcase : cuth₁ <> cuth₂ ∨ 
              (cuth₁ = cuth₂ ∧ (hcl <> hcr))).
            {
              case_eq (Fdec cuth₁ cuth₂);
              intros hu hv.
              right.
              refine (conj hu _). 
              intro hf. eapply hc.
              subst. cbn. f_equal.
              exact hf.
              left. exact hu. 
            }
            destruct hcase as [hcase | hcase].
            ++
              specialize (he Fin.F1).
              specialize (hb Fin.F1).
              rewrite dec_true in he, hb.
              cbn in he, hb.
              destruct he as [hel her].
              destruct hb as [hbl hbr].
              rewrite dec_true in her, hbr.
              (* witness *)
              exists ((ruh₁ - ruh₂) * inv (cuth₁ - cuth₂)).
              split.
              +++
                subst; cbn in * |-.
                eapply f_equal with (f := ginv) in hel.
                rewrite connection_between_vopp_and_fopp in hel.
                rewrite group_inv_flip  in hel.
                rewrite commutative in hel.
                pose proof (@rewrite_gop G gop _ _ _ _ hbl hel) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahl (c₁ ^ cuth₁) = gop (c₁ ^ cuth₁) ahl).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
                in Hcom.
                assert (Hwt : (gop ahl (gop (ginv ahl) (ginv (c₁ ^ cuth₂)))) = 
                (ginv (c₁ ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) = 
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone c₁).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
              +++
                exists Fin.F1. subst; cbn in *|- *.
                remember (gop c₂ (ginv msh)) as ct.
                eapply f_equal with (f := ginv) in her.
                rewrite connection_between_vopp_and_fopp in her.
                rewrite group_inv_flip  in her.
                rewrite commutative in her.
                pose proof (@rewrite_gop G gop _ _ _ _ hbr her) as Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                assert (Hwt : gop ahr (ct ^ cuth₁) = gop (ct ^ cuth₁) ahr).
                rewrite commutative; reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                setoid_rewrite <-(@monoid_is_associative G (@eq G) gop gid) 
                in Hcom.
                assert (Hwt : (gop ahr (gop (ginv ahr) (ginv (ct ^ cuth₂)))) = 
                (ginv (ct ^ cuth₂))).
                rewrite associative.
                rewrite group_is_right_inverse,
                monoid_is_left_idenity;
                reflexivity.
                rewrite Hwt in Hcom; clear Hwt.
                rewrite connection_between_vopp_and_fopp in Hcom.
                rewrite <-(@vector_space_smul_distributive_fadd 
                  F (@eq F) zero one add mul sub div 
                  opp inv G (@eq G) gid ginv gop gpow) in Hcom.
                apply f_equal with (f := fun x => x^(inv (cuth₁ + opp cuth₂)))
                in Hcom.
                rewrite !smul_pow_up in Hcom.
                assert (Hw : (cuth₁ + opp cuth₂) * inv (cuth₁ + opp cuth₂) = 
                (inv (cuth₁ + opp cuth₂) * (cuth₁ + opp cuth₂))).
                rewrite commutative; reflexivity.
                rewrite Hw in Hcom; clear Hw.
                rewrite field_is_left_multiplicative_inverse in Hcom.
                pose proof vector_space_field_one as Hone.
                unfold is_field_one in Hone.
                specialize (Hone ct).
                rewrite Hone in Hcom.
                rewrite <-ring_sub_definition in Hcom.
                exact Hcom.
                intros Hf.
                pose proof ring_neq_sub_neq_zero cuth₁ cuth₂ hcase as Hw.
                apply Hw.
                rewrite ring_sub_definition.
                exact Hf.
                all:typeclasses eauto.
            ++
              (* apply induction hypothesis *)
              specialize (ihm (fold_right add cutl₁ zero) (fold_right add cutl₂ zero)).
              destruct hcase as (hcasel & hcaser).
              rewrite Heqhcl, Heqhcr in hcaser.
              specialize (ihm hcaser n mstl alt cutl₁ rutl₁ cutl₂ rutl₂).
              assert (hua : fold_right add cutl₁ zero = fold_right add cutl₁ zero
                ∧ (∀ f : Fin.t (m + S n),
                (if Gdec (g ^ rutl₁[@f]) (gop (fst alt[@f])
                (c₁ ^ cutl₁[@f]))
                then true
                else false) = true
                ∧ (if
                Gdec (h ^ rutl₁[@f])
                (gop (snd alt[@f]) (gop c₂ (ginv mstl[@f])
                ^ cutl₁[@f]))
                then true
                else false) = true)).
              {
                refine(conj eq_refl _).
                intro f. 
                specialize (hb (Fin.FS f)).
                subst; simpl in * |- *.
                exact hb.
              }
            assert (hub : fold_right add cutl₂ zero = fold_right add cutl₂ zero
              ∧ (∀ f : Fin.t (m + S n),
              (if Gdec (g ^ rutl₂[@f])
              (gop (fst alt[@f]) (c₁ ^ cutl₂[@f]))
              then true
              else false) = true
              ∧ (if
              Gdec (h ^ rutl₂[@f])
              (gop (snd alt[@f])
              (gop c₂ (ginv mstl[@f]) ^ cutl₂[@f]))
              then true
              else false) = true)).
              {
                refine(conj eq_refl _).
                intro f.
                specialize (he (Fin.FS f)).
                subst; simpl in * |- *.
                exact he.
              }
            destruct (ihm hua hub) as (y & hg & f' & hff).
            exists y. split. exact hg.
            exists (Fin.FS f'). subst; cbn. exact hff.
        Qed.

        (* what a challening proof! *)

        (* main special soundness *)
        Lemma generalised_accepting_elgamal_soundness_main :
          forall {n : nat} (g h : G) (ms : Vector.t G (2 + n)) (c₁ c₂ : G)
          (a : Vector.t (G * G) ((2 + n))) (cu₁ : F) (cut₁ ru₁ : Vector.t F ((2 + n))) 
          (cu₂ : F) (cut₂ ru₂ : Vector.t F ((2 + n))), 
          generalised_accepting_encryption_proof_elgamal ms g h 
            (c₁, c₂) (a; cu₁ :: cut₁; ru₁) = true ->
          generalised_accepting_encryption_proof_elgamal ms g h 
            (c₁, c₂) (a; cu₂ :: cut₂; ru₂) = true -> 
          cu₁ ≠ cu₂ -> ∃ (y : F), g^y = c₁ ∧ 
          ∃ (f : Fin.t ((2 + n))), h^y = gop c₂ (ginv (nth ms f)).
        Proof.
          intro n.
          assert (hu : ∃ (m₁ m₂ : nat), (2 + n = m₁ + (1 + m₂))%nat).
          exists 1, n. reflexivity.
          destruct hu as (m₁ & m₂ & hu).
          rewrite !hu.
          intros * ha hb hc.
          eapply generalised_accepting_elgamal_soundness.
          exact ha. exact hb. exact hc.
        Qed.

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


        (* completeness 
         Context
          {m n : nat}
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (* Prover knows a relation *)
          (msl : Vector.t G m) 
          (mc : G)
          (msr : Vector.t G n) 
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv mc)).
        *)

        (* completeness of real function *)
        Lemma construct_encryption_proof_elgamal_real_completeness 
          {m n : nat}
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (msl : Vector.t G m) 
          (mc : G)
          (msr : Vector.t G n) 
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv mc)) : 
          forall (c : F) (uscs : Vector.t F ((m + (1 + n)) + (m + n))), 
          generalised_accepting_encryption_proof_elgamal 
          (msl ++ [mc] ++ msr)  g h (c₁, c₂) 
            (construct_encryption_proof_elgamal_real (x : F)
            uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c) = true. 
        Proof.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness.
          unfold construct_encryption_proof_elgamal_real, 
          construct_encryption_proof_elgamal_commitment.
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


        Theorem generalised_construct_encryption_proof_elgamal_real_completeness_fin : 
          forall (m n : nat) (rindex : Fin.t (m + S n)) 
          (msl : Vector.t G m) (h ms : G) (msr : Vector.t G n) (x : F)
          (c₂ : G),
          m = proj1_sig (Fin.to_nat rindex) ->
          h ^ x = gop c₂ (ginv (msl ++ ms :: msr)[@rindex]) -> 
          h ^ x = gop c₂ (ginv ms). 
        Proof.
          intros * ha hb.
          assert (hc : rindex = Fin.R m (Fin.F1 : Fin.t (1 + n))).
          eapply fin_to_nat. exact ha.
          subst. rewrite VectorSpec.nth_append_R in hb.
          cbn in hb.
          exact hb.
        Qed.

        (* completeness of real function *)
        Lemma generalised_construct_encryption_proof_elgamal_real_completeness 
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) : 
          forall (c : F) (uscs : Vector.t F (((2 + n)) + (1 + n))), 
          generalised_accepting_encryption_proof_elgamal 
          ms g h (c₁, c₂) 
            (generalised_construct_encryption_proof_elgamal_real rindex (x : F)
            uscs ms g h (c₁, c₂) c) = true.
        Proof.
          intros *.
          unfold generalised_construct_encryption_proof_elgamal_real.
          destruct (splitat (2 + n) uscs) as (us & cs).
          destruct (@vector_fin_app_pred F (1 + n) rindex us cs) as 
          (m₁ & m₂ & v₁ & v₃ & vm & v₂ & v₄ & pfaa & pfbb & haa).
          destruct pfaa as [pfa].
          destruct pfbb as [pfb].
          destruct haa as [ha].
          destruct ha as (ha & hb & hc & hd).
          generalize dependent ms. generalize dependent us. 
          generalize dependent cs. generalize dependent rindex. 
          cbn in * |- *. rewrite !pfa, !pfb. cbn.
          intros rindex ha cs hb us hc hd ms he.
          destruct (splitat m₁ ms) as (msl & msrr) eqn:hm.
          eapply append_splitat in hm.
          destruct (vector_inv_S msrr) as (m & msr & hmm).
          subst. 
          eapply construct_encryption_proof_elgamal_real_completeness.
          destruct he as (hel & her).
          split. exact hel.
          eapply generalised_construct_encryption_proof_elgamal_real_completeness_fin.
          exact ha. exact her.
        Qed.
          
          

        (* simulator completeness *)
        Lemma generalised_construct_encryption_proof_elgamal_simulator_completeness 
          {n : nat}
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n)) : 
          forall (c : F) (uscs : Vector.t F (((2 + n)) + (1 + n))), 
          generalised_accepting_encryption_proof_elgamal 
          ms g h (c₁, c₂) 
            (generalised_construct_encryption_proof_elgamal_simulator uscs 
             ms g h (c₁, c₂) c) = true.
        Proof.
          intros *.
          eapply generalised_accepting_elgamal_conversations_correctness_gen.
          unfold generalised_construct_encryption_proof_elgamal_simulator.
          destruct (splitat ((2 + n)) uscs) as (us & cs).
          split.
          + cbn; field. 
          + 
            intros *.
            remember (c - fold_right add cs zero :: cs) as cst. cbn.
            rewrite !dec_true.
            split.
            ++
              clear uscs Heqcst.
              assert (ha : (∃ (m₁ m₂ : nat), 2 + n = m₁ + (1 + m₂))%nat).
              exists 1, n. reflexivity.
              destruct ha as (m₁ & m₂ & ha).
              revert us cst f ms. cbn in * |- *. 
              rewrite !ha. intros *. 
              destruct (splitat m₁ us) as (usl & usrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S usrr) as (u & usr & hc).
              subst.
              destruct (splitat m₁ ms) as (msl & msrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S msrr) as (mc & msr & hc).
              subst.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_first.
            ++
              clear uscs Heqcst.
              assert (ha : (∃ (m₁ m₂ : nat), 2 + n = m₁ + (1 + m₂))%nat).
              exists 1, n. reflexivity.
              destruct ha as (m₁ & m₂ & ha).
              revert us cst f ms. cbn in * |- *. 
              rewrite !ha. intros *. 
              destruct (splitat m₁ us) as (usl & usrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S usrr) as (u & usr & hc).
              subst.
              destruct (splitat m₁ ms) as (msl & msrr) eqn:hb.
              eapply append_splitat in hb.
              destruct (vector_inv_S msrr) as (mc & msr & hc).
              subst.
              eapply construct_encryption_proof_elgamal_simulator_completeness_generic_second.
        Qed.


        (* zero-knowledge *)

        (* honest verifier zero knowledge proof *)

        #[local] Notation "p / q" := (mk_prob p (Pos.of_nat q)).

        Lemma construct_encryption_proof_elgamal_distribution_probability_generic  
          {m n : nat}
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (msl : Vector.t G m) 
          (mc : G)
          (msr : Vector.t G n) : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F (m + (1 + n) + (m + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_encryption_proof_elgamal_real x 
              uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c))) → pr = 1 / q.
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

        Lemma generalised_construct_encryption_proof_elgamal_distribution_probability_generic  
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n)) : 
          forall (l : dist (t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_real rindex x 
              uscs ms g h (c₁, c₂) c))) → pr = 1 / q.
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

        Lemma construct_encryption_proof_elgamal_distribution_transcript_generic 
          {m n : nat}
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (msl : Vector.t G m) 
          (mc : G)
          (msr : Vector.t G n) 
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv mc)) : 
          forall (l : dist (t F (m + (1 + n) + (m + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F (m + (1 + n) + (m + n)),
              Ret (construct_encryption_proof_elgamal_real x 
              uscs (msl ++ [mc] ++ msr) g h (c₁, c₂) c))) → 
          generalised_accepting_encryption_proof_elgamal (msl ++ [mc] ++ msr) 
            g h (c₁, c₂) trans = true.
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
              now eapply construct_encryption_proof_elgamal_real_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply construct_encryption_proof_elgamal_real_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.


        Lemma generalised_construct_encryption_proof_elgamal_distribution_transcript_generic 
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n) )
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) : 
          forall (l : dist (t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_real rindex x 
              uscs ms g h (c₁, c₂) c))) → 
          generalised_accepting_encryption_proof_elgamal ms 
            g h (c₁, c₂) trans = true.
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
              now eapply generalised_construct_encryption_proof_elgamal_real_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                now eapply generalised_construct_encryption_proof_elgamal_real_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

        (* Definition generalised_encryption_proof_elgamal_real_distribution  
        {n : nat} (lf : list F) (Hlfn : lf <> List.nil) (rindex : Fin.t (2 + n))
        (x : F) (cp : G * G) (g h : G) (ms : Vector.t G ((2 + n))) (c : F) *)
        Lemma generalised_encryption_proof_elgamal_special_honest_verifier_dist 
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) : 
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_encryption_proof_elgamal_real_distribution lf Hlfn 
            rindex x (c₁, c₂) g h ms c) ->
            (* it's an accepting conversation and probability is *)
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_construct_encryption_proof_elgamal_distribution_transcript_generic.
            exact R.
            exact Ha.
          +
            eapply generalised_construct_encryption_proof_elgamal_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.

        (* simulator *)

         Lemma generalised_construct_encryption_proof_elgamal_simulator_distribution_probability_generic  
          {n : nat}
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n)) :  
          forall (l : dist (t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F) (q : nat),
          (∀ (trx : Vector.t F ((2 + n) + (1 + n))) (prx : prob), 
            List.In (trx, prx) l → prx = 1 / q) -> 
          List.In (trans, pr)
            (Bind l (λ uscs :  Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_simulator uscs
             ms g h (c₁, c₂) c))) → pr = 1 / q.
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

        Lemma generalised_construct_encryption_proof_elgamal_simulator_distribution_transcript_generic 
          {n : nat}
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n)) : 
          forall (l : dist (t F ((2 + n) + (1 + n)))) 
          (trans : sigma_proto) (pr : prob) (c : F),
          List.In (trans, pr)
            (Bind l (λ uscs : Vector.t F ((2 + n) + (1 + n)),
              Ret (generalised_construct_encryption_proof_elgamal_simulator uscs
              ms g h (c₁, c₂) c))) → 
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) trans = true.
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
              eapply generalised_construct_encryption_proof_elgamal_simulator_completeness.
            ++
              intros * Ha.
              remember (((la, lp) :: l)%list) as ls.
              cbn in Ha.
              destruct Ha as [Ha | Ha].
              +++
                inversion Ha.
                eapply generalised_construct_encryption_proof_elgamal_simulator_completeness.
              +++
                eapply IHl; try assumption.
                exact Ha.
        Qed.

         Lemma generalised_construct_encryption_proof_elgamal_simulator_special_honest_verifier_dist 
          {n : nat}
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n)) :
          forall (lf : list F) (Hlfn : lf <> List.nil) 
          (c : F) a b, 
          List.In (a, b) 
            (generalised_encryption_proof_elgamal_simulator_distribution lf Hlfn
              g h (c₁, c₂) ms c) ->
            (* it's an accepting conversation and probability is *)
          generalised_accepting_encryption_proof_elgamal ms
            g h (c₁, c₂) a = true ∧ 
          b = 1 / (Nat.pow (List.length lf) ((2 + n) + (1 + n))).
        Proof.
          intros * Ha.
          refine(conj _ _).
          + 
            eapply generalised_construct_encryption_proof_elgamal_simulator_distribution_transcript_generic. 
            exact Ha.
          +
            eapply generalised_construct_encryption_proof_elgamal_simulator_distribution_probability_generic.
            intros * Hc.
            eapply uniform_probability_multidraw_prob; exact Hc.
            exact Ha.
        Qed.


         Lemma generalised_encryption_proof_elgamal_special_honest_verifier_zkp 
          {n : nat}
          (rindex : Fin.t (2 + n))
          (x : F) (* secret witness *)
          (g h c₁ c₂ : G) (* public values *)
          (ms : Vector.t G (2 + n))
          (R : g^x = c₁ ∧ h^x = gop c₂ (ginv (Vector.nth ms rindex))) : 
          forall (lf : list F) (Hlfn : lf <> List.nil) (c : F),
          List.map (fun '(a, p) => 
            (generalised_accepting_encryption_proof_elgamal ms 
              g h (c₁, c₂) a, p))
            (generalised_encryption_proof_elgamal_real_distribution lf Hlfn 
              rindex x (c₁, c₂) g h ms c) = 
          List.map (fun '(a, p) => 
            (generalised_accepting_encryption_proof_elgamal ms
              g h (c₁, c₂) a, p))
            (generalised_encryption_proof_elgamal_simulator_distribution lf Hlfn
              g h (c₁, c₂) ms c).
        Proof.
          intros ? ? ?.
          eapply map_ext_eq.
          +
            unfold generalised_encryption_proof_elgamal_real_distribution,
            generalised_encryption_proof_elgamal_simulator_distribution; cbn.
            repeat rewrite distribution_length.
            reflexivity.
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_encryption_proof_elgamal_special_honest_verifier_dist.
            exact R.
            exact Ha. 
          +
            intros (aa, cc, rr) y Ha.
            eapply generalised_construct_encryption_proof_elgamal_simulator_special_honest_verifier_dist.
            exact Ha.
        Qed.
    
    End Proofs. 
  End EncProof.
End DL.