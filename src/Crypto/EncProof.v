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
      Definition generalised_encryption_proof_elgamal_supplement {n : nat}
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


      (* verify OR sigma protocol *)
      (* Check that 
        - the sum of c_i (from i=1 to n) equals c mod q.
        - For each i from 1 to n: check that g^{r_i} = t_1i * c₁^{c_i} and 
          h^{r_i} = t2i * (c₂ / m_i)^{c_i}.
        *)
      Definition generalised_encryption_proof_elgamal  {m n : nat} 
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
              generalised_encryption_proof_elgamal_supplement g h ms cp (a; cs; r)
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

    End Proofs.
  End EncProof.
Section DL.

