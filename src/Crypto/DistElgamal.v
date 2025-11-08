From Stdlib Require Import Setoid
  Lia Vector Utf8 Fin setoid_ring.Field.
From Algebra Require Import
  Hierarchy Group Monoid
  Field Integral_domain
  Ring Vector_space.
From Utility Require Import 
  Util.
From Crypto Require Import Elgamal.
Import VectorNotations.

Section DistElgamal.

  (* Underlying Field of Vector Space *)
  Context 
    {F : Type}
    {zero one : F} 
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.

  (* Vector Element *)
  Context 
    {G : Type} 
    {gid : G} 
    {ginv : G -> G}
    {gop : G -> G -> G} 
    {gpow : G -> F -> G}
    {Hvec: @vector_space F (@eq F) zero one add mul sub 
      div opp inv G (@eq G) gid ginv gop gpow}.

  Local Infix "^" := gpow.
  Local Infix "*" := mul.
  Local Infix "+" := add.

  Section Def.

      (* This function encrypts a value m as g ^ m by using public keys 
      supplied as hs. *)
      Definition encrypt_value_dist {n : nat}
        (g : G) (hs : Vector.t G (1 + n)) (m r : F) : G * G.
      Proof.
        (* multiply all the public keys *)
        set (h := Vector.fold_right (fun hi acc => gop hi acc) hs gid).
        exact(@enc F G gop gpow g h m r).
      Defined.

      (* returns partial decryption *)
      Definition decrypt_value_partial (c : G * G) (x : F) : G.
      Proof.
        refine 
          match c as c' in _ * _ return G 
          with 
          | (c₁, c₂) => gpow c₁ x 
          end. 
      Defined.

      (* decrypt a ciphter text completely, given all the 
      decrypton factor  *)
      Definition decrypt_value {n : nat} (c : G * G)  
        (ds : Vector.t G (1 + n)) : G.
      Proof.
        (* multiply all the partial decryption *)
        set (d := Vector.fold_right (fun hi acc => gop hi acc) ds gid).
        refine 
          match c as c' in _ * _ return G 
          with 
          | (c₁, c₂) => gop c₂ (ginv d)
          end. 
      Defined.

      (* encrypts a ballot *)
      Definition encrypt_ballot_dist {n m : nat}
        (g : G) (hs : Vector.t G (1 + n)) 
        (ms rs : Vector.t F m) : Vector.t (G * G) m.
      Proof.
        (* multiply all the public keys *)
        set (h := Vector.fold_right (fun hi acc => gop hi acc) hs gid).
        exact(@encrypted_ballot F G gop gpow g h _ ms rs).
      Defined.

      (* partially decrypts a ballot *)
      Definition decrypt_ballot_partial {m : nat} 
        (cs : Vector.t (G * G) m) (x : F) : Vector.t G m.
      Proof.
        exact (Vector.map (fun c => decrypt_value_partial c x) cs).
      Defined.

      (* decrypt a ciphter text completely. 1 + n election monitors 
      produce their partial decryption of cs. 
          
    decrypt_ballot_value
    cs : [ (c₁₀,c₂₀), (c₁₁,c₂₁), ..., (c₁m,c₂m) ]          (ciphertext vector)
    ds : [
          [d₀₀ d₀₁ ... d₀m],   ← partial decryptions from monitor 0
          [d₁₀ d₁₁ ... d₁m],   ← monitor 1
          ...
          [dₙ₀ dₙ₁ ... dₙm]    ← monitor n
         ]


      cs:       (c₁,c₂) (c₁,c₂) (c₁,c₂) ... (c₁,c₂)
                │        │        │            │
                ▼        ▼        ▼            ▼
      ds:   d00   d01   d02  ...   d0m     ← combine into initial decrypt
            │     │     │          │
            ▼     ▼     ▼          ▼
            dr0   dr1   dr2  ...   drm      ← recursive partial decrypt
            │     │     │          │
        d10 │ d11 │ d12 │ ...  d1m │
            ▼     ▼     ▼          ▼
      final: f0    f1    f2   ...   fm

      Where:
        base layer      fi = gop c₂ ginv d0i
        recursive layer fi = gop dsh[i] dret[i]

      *)

      Definition decrypt_ballot_value {n m : nat} (cs : Vector.t (G * G) m)
        (ds : Vector.t (Vector.t G m) (1 + n)) : Vector.t G m.
      Proof.
        revert n m cs ds.
        induction n as [|n ihn].
        +
          intros * cs ds.
          destruct (vector_inv_S ds) as (dsh & dst & _).
          exact (Vector.map (fun '((c₁, c₂), d) =>  gop c₂ (ginv d)) (zip_with (fun x y => (x, y)) cs dsh)).
        +
          intros * cs ds.
          destruct (vector_inv_S ds) as (dsh & dst & _).
          remember (ihn m cs dst) as dret.
          exact (Vector.map (fun '(df, dr) =>  gop df dr) (zip_with (fun x y => (x, y)) dsh dret)).
      Defined.

  End Def.



  Section Proofs. 


    Add Field field : (@field_theory_for_stdlib_tactic F
       eq zero one opp add mul sub inv div vector_space_field).
       
    (* This and a lot of other proofs can be automated. *)
    Theorem group_shuffle_commutative : ∀ (u v x y : G),
      gop (gop u v) (gop x y) = gop (gop u x) (gop v y).
    Proof.
      intros *.
      rewrite <-associative.
      assert (ha : (gop v (gop x y) = (gop x (gop v y)))).
      rewrite associative. 
      assert (hb : gop v x = gop x v). rewrite commutative;
      reflexivity. rewrite hb. rewrite <-associative.
      reflexivity.
      rewrite ha. clear ha.
      rewrite associative.
      reflexivity.
    Qed.

  
    (*
      This theorem states the correctness of decrypting a single encrypted ballot entry
      in the base case (i.e., without recursion over trustee layers).

      We assume:
        - g : G is a group generator.
        - x : F is the secret key.
        - h = g^x is the public key.
        - ms : Vector.t F n contains the message exponents (the actual vote values).
        - rs : Vector.t F n contains the random exponents used during encryption.
        - ds : Vector.t G n contains the decryption factors.

      Each ciphertext in the encrypted ballot is formed as:
          c1 = g^(rs[i])
          c2 = (g^x)^(rs[i]) * g^(ms[i])
            = g^(x * rs[i]) * g^(ms[i])

      The corresponding decryption factor is:
          d[i] = g^(x * rs[i])

      Therefore, decrypting is simply:
          c2 * (d[i])^(-1) = g^(ms[i])

      The theorem asserts exactly this: for every index f, when we take the second
      component of the ciphertext and multiply it by the inverse of the matching
      decryption factor, we recover g^(ms[f]). In other words, ElGamal decryption
      works correctly for each entry of an encrypted ballot.
*)


    Theorem decrypt_ballot_value_correct_base_case : 
      ∀ (n : nat) (x : F) (g h : G)
      (ms rs : Vector.t F n) (ds : Vector.t G n),
      h = g ^ x -> (∀ (fa : Fin.t n), ds[@fa] = (g ^ rs[@fa]) ^ x) ->
      ∀ (f : Fin.t n),g ^ ms[@f] = (map (λ '(_, c₂, d), gop c₂ (ginv d))
      (zip_with (λ (u : G * G) (v : G), (u, v)) 
        (@encrypted_ballot F G gop gpow g (gop h gid) _ ms rs) ds))[@f].
    Proof.
      induction n as [|n ihn].
      +
        intros * ha hb *.
        refine match f with end.
      +
        intros * ha hb *.
        destruct (vector_inv_S ms) as (msh & mst & hc).
        destruct (vector_inv_S rs) as (rsh & rst & hd).
        destruct (vector_inv_S ds) as (dsh & dst & he).
        destruct (fin_inv_S _ f) as [|(f' & hf)].
        ++
          subst. specialize (hb Fin.F1).
          cbn in * |- *. subst.
          rewrite right_identity.
          pose proof vector_space_smul_associative_fmul as hi.
          unfold is_smul_associative_fmul in hi.
          specialize (hi x rsh g).
          rewrite <-hi. clear hi.
          pose proof vector_space_smul_associative_fmul as hi.
          unfold is_smul_associative_fmul in hi.
          specialize (hi rsh x g). 
          rewrite <-hi. clear hi.
          assert (hi : x * rsh = rsh * x). field.
          rewrite hi. rewrite <-associative, right_inverse,
          right_identity.
          reflexivity.
        ++
          specialize (ihn x g h mst rst dst ha).
          assert (hi : (∀ fa : t n, dst[@fa] = (g ^ rst[@fa]) ^ x)).
          {
            intro fa. subst.
            exact (hb (Fin.FS fa)).
          }
          specialize (ihn hi f'); clear hi. 
          subst. specialize (hb (Fin.FS f')).
          cbn in * |- *. exact ihn.
    Qed.

    Theorem decrypt_ballot_value_correct_induction_enc_forward_base_case : 
      ∀ (n : nat) (g h hsh : G) (ms rs : Vector.t F n), 
      @encrypted_ballot F G gop gpow g (gop h (gop hsh gid)) _ ms rs =
      map (λ '(c₁, c₂, r), (c₁, gop c₂ (h ^ r)))
        (zip_with (λ (x : G * G) (y : F), (x, y)) (@encrypted_ballot F G gop gpow g (gop hsh gid) _ ms rs) rs).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        pose proof (vector_inv_0 ms) as ha.
        pose proof (vector_inv_0 rs) as hb.
        subst; cbn. reflexivity.
      +
        intros *.
        destruct (vector_inv_S ms) as (msh & mst & ha).
        destruct (vector_inv_S rs) as (rsh & rst & hb).
        subst. cbn. 
        f_equal.
        ++
          unfold enc.
          f_equal.
          rewrite <-associative.
          remember (gop hsh gid) as ghi.
          f_equal.
          (*  setoid_rewrite vector_space_smul_distributive_vadd. not 
          working? *)
          pose proof vector_space_smul_distributive_vadd as hg.
          unfold is_smul_distributive_vadd in hg.
          specialize (hg rsh ghi h).
          rewrite <-hg.
          rewrite commutative. reflexivity.
        ++
          eapply ihn.
    Qed.

    Theorem decrypt_ballot_value_correct_induction_enc_forward_induction_case :
      ∀ (n : nat) (g h hsh hii : G) (ms rs : Vector.t F n), 
      map (λ '(c₁, c₂, r), (c₁, gop c₂ (gop h hsh ^ r)))
        (zip_with (λ (x : G * G) (y : F), (x, y)) 
        (@encrypted_ballot F G gop gpow g hii _ ms rs) rs) =
      map (λ '(c₁, c₂, r), (c₁, gop c₂ (h ^ r)))
        (zip_with (λ (x : G * G) (y : F), (x, y)) 
        (@encrypted_ballot F G gop gpow g (gop hsh hii) _ ms rs) rs).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        pose proof (vector_inv_0 ms) as ha.
        pose proof (vector_inv_0 rs) as hb.
        subst; cbn. reflexivity.
      +
        intros *.
        destruct (vector_inv_S ms) as (msh & mst & ha).
        destruct (vector_inv_S rs) as (rsh & rst & hb).
        subst. cbn.
        f_equal.
        ++
          f_equal.
          rewrite <-associative, <-associative.
          f_equal. 
          pose proof vector_space_smul_distributive_vadd as hg.
          unfold is_smul_distributive_vadd in hg.
          specialize (hg rsh h hsh).
          rewrite hg; clear hg.
          assert (ha : (gop (h ^ rsh) (hsh ^ rsh)) = 
            (gop (hsh ^ rsh) (h ^ rsh))).
          rewrite commutative. reflexivity.
          rewrite ha; clear ha.
          rewrite associative. 
          f_equal. 
          pose proof vector_space_smul_distributive_vadd as hg.
          unfold is_smul_distributive_vadd in hg.
          specialize (hg rsh hsh hii). 
          rewrite hg, commutative;
          reflexivity.
        ++
          unfold encrypted_ballot in ihn.
          rewrite ihn. reflexivity.
    Qed.


    Theorem decrypt_ballot_value_correct_induction_enc_forward {m : nat} : 
      ∀ (n : nat) (g h : G) (hs : Vector.t G (1 + n)) (ms rs : Vector.t F m), 
      encrypt_ballot_dist g (h :: hs) ms rs = 
      Vector.map (fun '((c₁, c₂), r) => 
      (c₁, gop c₂ (h ^ r))) (zip_with (fun x y => (x, y)) 
      (encrypt_ballot_dist g hs ms rs) rs).
    Proof.
      induction n as [|n ihn].
      +
        intros *. 
        unfold encrypt_ballot_dist.
        cbn.
        destruct (vector_inv_S hs) as (hsh & hst & ha).
        pose proof (vector_inv_0 hst) as hb.
        subst. cbn.
        eapply decrypt_ballot_value_correct_induction_enc_forward_base_case.
      +
        intros *.
        destruct (vector_inv_S hs) as (hsh & hst & ha).
        unfold encrypt_ballot_dist in ihn |- *.
        cbn in ihn |- *. subst. cbn.
        specialize (ihn g (gop h hsh) hst ms rs).
        remember ((fold_right (λ hi acc : G, gop hi acc) hst gid)) as hii.
        assert (ha : (gop (gop h hsh) hii) = 
          gop h (gop hsh hii)).
        rewrite associative. reflexivity.
        rewrite ha in ihn; clear ha.
        rewrite ihn.
        eapply decrypt_ballot_value_correct_induction_enc_forward_induction_case.
    Qed.


    Theorem decrypt_ballot_value_correct_induction_enc_backward {m : nat} : 
      ∀ (n : nat) (g h : G) (hs : Vector.t G (1 + n)) (ms rs : Vector.t F m)
      (cs : Vector.t (G * G) m), 
      encrypt_ballot_dist g hs ms rs = 
      Vector.map (fun '((c₁, c₂), r) => 
      (c₁, gop c₂ (ginv (h ^ r)))) (zip_with (fun x y => (x, y)) 
      (encrypt_ballot_dist g (h :: hs) ms rs) rs).
    Proof.
    Admitted.
    
    

    Context 
      {n : nat}
      {g : G} 
      {xs : Vector.t F (1 + n)} (* private keys of trustess *)
      {hs : Vector.t G (1 + n)} (* public keys of the trustess *)
      (* under the assumption each hi = g ^ xi --there is zero-knowledge proof for this 
      fact as well in the tallysheet. *)
      (hrel : ∀ (i : Fin.t (1 + n)), gpow g (Vector.nth xs i) = (Vector.nth hs i)).
    


    Theorem fold_right_identity : ∀ (r : F) (ds : Vector.t G (1 + n)), 
      (∀ f : t (S n), ds[@f] = (g ^ r) ^ xs[@f]) ->
      gop (fold_right (λ hi acc : G, gop hi acc) hs gid ^ r) 
      (ginv (fold_right (λ hi acc : G, gop hi acc) ds gid)) = gid. 
    Proof.
      revert n xs hs hrel.
      induction n as [|n' ihn].
      +
        intros * ha * hb.
        destruct (vector_inv_S xs) as (x & xs' & hc). 
        pose proof (vector_inv_0 xs') as hd.
        destruct (vector_inv_S hs) as (h & hs' & he). 
        pose proof (vector_inv_0 hs') as hf.
        destruct (vector_inv_S ds) as (d & ds' & hg). 
        pose proof (vector_inv_0 ds') as hh.
        subst; cbn.
        specialize (ha Fin.F1).
        specialize (hb Fin.F1).
        cbn in * |-; subst.
        rewrite !right_identity.
        rewrite <- !(@vector_space_smul_associative_fmul F (@eq F) 
          zero one add mul sub div 
          opp inv G (@eq G) gid ginv gop gpow Hvec).
        assert (ha : x * r = r * x). field.
        rewrite ha; clear ha.
        rewrite !right_inverse.
        reflexivity.
      +
        intros * ha * hb.
        destruct (vector_inv_S xs) as (x & xs' & hd).
        destruct (vector_inv_S hs) as (h & hs' & he).
        destruct (vector_inv_S ds) as (d & ds' & hf).
        specialize (ihn xs' hs').
        assert (hg : (∀ i : t (1 + n'), g ^ xs'[@i] = hs'[@i])).
        {
          intro f. rewrite hd, he in ha.
          exact (ha (Fin.FS f)).
        }
        specialize (ihn hg r ds'); clear hg.
        assert (hg : (∀ f : Fin.t (S n'), ds'[@f] = (g ^ r) ^ xs'[@f])).
        {
          intro f. rewrite hd, hf in hb.
          exact (hb (Fin.FS f)).
        }
        specialize (ihn hg); clear hg.
        rewrite he, hf. cbn.
        remember (fold_right (λ hi acc : G, gop hi acc) hs' gid) as hii.
        remember (fold_right (λ hi acc : G, gop hi acc) ds' gid) as dii.
        (* why is rewrite not working? *)
        pose proof vector_space_smul_distributive_vadd as hg.
        unfold is_smul_distributive_vadd in hg.
        specialize (hg r h hii).
        rewrite hg; clear hg.
        rewrite group_inv_flip.
        assert (hj : gop (ginv dii) (ginv d) = gop (ginv d) (ginv dii)).
        rewrite commutative; reflexivity. rewrite hj; clear hj.
        (* rewrite fails but setoid_rewrite works! *)
        setoid_rewrite <-Heqhii in ihn.
        setoid_rewrite <-Heqdii in ihn.
        rewrite group_shuffle_commutative, ihn.
        rewrite hd, hf in hb.
        pose proof (hb Fin.F1) as hg.
        cbn in hg.
        rewrite hd, he in ha.
        pose proof (ha Fin.F1) as hh.
        cbn in hh.
        rewrite <-hh, hg.
        (* setoid_rewrite is also not working! Why? *)
        pose proof vector_space_smul_associative_fmul as hi.
        unfold is_smul_associative_fmul in hi.
        specialize (hi x r g).
        rewrite <-hi. clear hi.
        pose proof vector_space_smul_associative_fmul as hi.
        unfold is_smul_associative_fmul in hi.
        specialize (hi r x g). 
        rewrite <-hi. clear hi.
        assert (hi : x * r = r * x). field.
        rewrite hi, right_inverse, right_identity.
        reflexivity.
    Qed.


    Theorem decryption_value_correct : ∀ (m r : F) (c : G * G) (ds : Vector.t G (1 + n)),
      c = encrypt_value_dist g hs m r -> 
      (∀ (f : Fin.t (1 + n)), Vector.nth ds f = decrypt_value_partial c (Vector.nth xs f)) -> 
      decrypt_value c ds = g ^ m.
    Proof.
      intros m r (c₁, c₂) * ha hb.
      cbn in * |- *.
      unfold encrypt_value_dist, enc in ha.
      inversion ha as [[hc hd]]; subst; 
      clear ha.
      rewrite <- (@monoid_is_associative G (@eq G) gop gid).
      rewrite fold_right_identity; try assumption.
      rewrite right_identity; exact eq_refl.
      typeclasses eauto.
    Qed.


    Theorem decrypt_ballot_value_correct : ∀ {m : nat} 
      (ms rs : Vector.t F m) (cs : Vector.t (G * G) m)
      (ds : Vector.t (Vector.t G m) (1 + n)), 
      (* partial decryption factor is well-formed/correct *)
      (∀ (fa : Fin.t (1 + n)) (fb : Fin.t m), ds[@fa][@fb] = (g ^ rs[@fb]) ^ xs[@fa]) ->
      (* cs is encryption of ms *)
      cs = @encrypt_ballot_dist n m g hs ms rs -> 
      ∀ (f : Fin.t m), g ^ ms[@f] = (@decrypt_ballot_value n m cs ds)[@f].
    Proof.
      revert n xs hs hrel.
      induction n as [|n' ihn].
      + 
        (* base case: one trustee *)
        intros * ha * hb hc f.
        cbn in * |-.
        subst.
        destruct (vector_inv_S ds) as (dsh & dst & hc). 
        pose proof (vector_inv_0 dst) as hd.
        destruct (vector_inv_S xs) as (xsh & xst & he).
        pose proof (vector_inv_0 xst) as hf.
        destruct (vector_inv_S hs) as (hsh & hst & hg).
        pose proof (vector_inv_0 hst) as hh.
        subst.
        specialize (ha Fin.F1). 
        specialize (hb Fin.F1).
        cbn in ha, hb. cbn.
        unfold encrypt_ballot_dist. cbn.
        eapply  decrypt_ballot_value_correct_base_case.
        rewrite ha; reflexivity.
        exact hb.
      +
        intros * ha * hb hc f.
        destruct (vector_inv_S ds) as (dsh & dst & hd). 
        destruct (vector_inv_S xs) as (xsh & xst & he).
        destruct (vector_inv_S hs) as (hsh & hst & hf).
        specialize (ihn xst hst).
        assert(hg : (∀ i : Fin.t (1 + n'), g ^ xst[@i] = hst[@i])).
        {
          intros *.
          subst. exact (ha (Fin.FS i)).
        }
        specialize (ihn hg m ms rs 
          (Vector.map (fun '((c₁, c₂), r) => 
          (c₁, gop c₂ (ginv (hsh ^ r)))) (zip_with (fun x y => (x, y)) cs rs)) dst); clear hg.
        assert(hg : (∀ (fa : Fin.t (1 + n')) (fb : Fin.t m), (dst[@fa])[@fb] = (g ^ rs[@fb]) ^ xst[@fa])).
        {
          intros *. subst.
          exact (hb (Fin.FS fa) fb).
        }
        specialize (ihn hg); clear hg.

        





    Admitted.






  End Proofs. 
End DistElgamal.