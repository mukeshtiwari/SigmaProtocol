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
      produce their partial decryption of cs. To decrypt c_i from cs, 
      we take the ith column of ds and run the decrypt_value function.
          
      cs : Vector.t (G * G) m  
      [c0, c1, c2, ..., c_{m-1}]          
      
      
      ds : Vector.t (Vector.t G m) (1 + n)
      [ row0: [d0_0 d0_1 d0_2 ... d0_{m-1}]
        row1: [d1_0 d1_1 d1_2 ... d1_{m-1}]
        ...
        row_{n}: [...]
      ]

      To decrypt c_i:
        cs[i]  ----------------+
                                |   take ith column of ds
        decrypt_value( cs[i], [d0_i, d1_i, ..., d_{n}_i] )  --> plaintext g ^ m_i
      *)

      Definition decrypt_ballotvalue {n m : nat} (cs : Vector.t (G * G) m)
        (ds : Vector.t (Vector.t G m) (1 + n)) : Vector.t G m.
      Proof.
      Admitted.

  End Def.



  Section Proofs. 


    Add Field field : (@field_theory_for_stdlib_tactic F
       eq zero one opp add mul sub inv div vector_space_field).
       
    
    Theorem group_shuffle_commutative : ∀ (u v x y : G),
      gop (gop u v) (gop x y) = gop (gop u x) (gop v y).
    Proof.
      intros *.
    Admitted.

    Context 
      {n : nat}
      {g : G} 
      {xs : Vector.t F (1 + n)}
      {hs : Vector.t G (1 + n)}
      (* under the assumption each hi = g ^ xi *)
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


    Theorem decryption_correct : ∀ (m r : F) (c : G * G) (ds : Vector.t G (1 + n)),
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

  End Proofs. 
End DistElgamal.