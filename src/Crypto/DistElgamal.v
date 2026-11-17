(** * Distributed ElGamal: Joint Keys and Combined Partial Decryption *)

(** This file formalises the multi-trustee (n-out-of-n) variant of
    exponential ElGamal used by e-voting systems such as Helios: each of
    [1 + n] trustees holds a secret key share [xᵢ] with public share
    [hᵢ = g ^ xᵢ]; the election public key is the product of the shares,

    [[
      h = h₁ · h₂ · … · h₍₁₊ₙ₎ = g ^ (x₁ + … + x₍₁₊ₙ₎)
    ]]

    and ballots are encrypted under [h] with the ordinary scheme of
    [Elgamal]. To decrypt [(c₁, c₂)], each trustee publishes the partial
    decryption (decryption factor) [dᵢ = c₁ ^ xᵢ]; anyone can then combine
    them into

    [[
      c₂ · (d₁ · … · d₍₁₊ₙ₎)⁻¹ = g ^ m.
    ]]

    The secret key [x = Σ xᵢ] is never reconstructed. This is additive
    sharing: all trustees are needed, and there is no threshold
    (t-out-of-n, Shamir-style) reconstruction in this file. The proofs that
    each [hᵢ] is well formed and that each [dᵢ] is correct are not part of
    this file; they are separate Chaum–Pedersen / Schnorr proofs (see
    [ChaumPedersen] and [DecProof]). Here the correctness theorems simply
    assume [hᵢ = g ^ xᵢ] (section hypothesis [hrel]) and well-formed
    decryption factors.

    Main results:

    - [decryption_value_correct]: combining correct partial decryptions of
      an encryption of [m] under the joint key yields [g ^ m];
    - [decrypt_ballot_value_correct]: the same for a whole ballot (vector of
      [m] ciphertexts), component-wise.

    The file also contains auxiliary lemmas relating encryption under a
    product key to encryption under its factors
    ([decrypt_ballot_value_correct_induction_enc_forward] and
    [decrypt_ballot_value_correct_induction_enc_backward]), which are not
    used by the main theorems. The concrete instance is in
    [Examples.DistElgamalIns]. *)
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

(** ** Parameters *)
Section DistElgamal.

  (** The scalar field [F]. *)
  Context
    {F : Type}
    {zero one : F}
    {add mul sub div : F -> F -> F}
    {opp inv : F -> F}.

  (** The group [G], an [F]-vector space. *)
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

  (** ** Definitions *)
  Section Def.

      (** [encrypt_value_dist g hs m r] encrypts [g ^ m] with randomness [r]
          under the joint public key [h], the product of the trustees’
          public shares [hs] (computed by a right fold of [gop] starting
          from [gid]). *)
      Definition encrypt_value_dist {n : nat}
        (g : G) (hs : Vector.t G (1 + n)) (m r : F) : G * G.
      Proof.
        set (h := Vector.fold_right (fun hi acc => gop hi acc) hs gid).
        exact(@enc F G gop gpow g h m r).
      Defined.

      (** [decrypt_value_partial (c₁, c₂) x] is a trustee’s decryption
          factor [c₁ ^ x] for its secret share [x]. *)
      Definition decrypt_value_partial (c : G * G) (x : F) : G.
      Proof.
        refine
          match c as c' in _ * _ return G
          with
          | (c₁, c₂) => gpow c₁ x
          end.
      Defined.

      (** [decrypt_value (c₁, c₂) ds] combines all decryption factors:
          it returns [c₂ · (Π ds)⁻¹]. *)
      Definition decrypt_value {n : nat} (c : G * G)
        (ds : Vector.t G (1 + n)) : G.
      Proof.
        set (d := Vector.fold_right (fun hi acc => gop hi acc) ds gid).
        refine
          match c as c' in _ * _ return G
          with
          | (c₁, c₂) => gop c₂ (ginv d)
          end.
      Defined.

      (** [encrypt_ballot_dist g hs ms rs] encrypts every entry of the
          ballot [ms] with the matching randomness of [rs] under the joint key
          [Π hs]. *)
      Definition encrypt_ballot_dist {n m : nat}
        (g : G) (hs : Vector.t G (1 + n))
        (ms rs : Vector.t F m) : Vector.t (G * G) m.
      Proof.
        set (h := Vector.fold_right (fun hi acc => gop hi acc) hs gid).
        exact(@encrypted_ballot F G gop gpow g h _ ms rs).
      Defined.

      (** [decrypt_ballot_partial cs x] is one trustee’s vector of decryption
          factors for a ballot [cs]. *)
      Definition decrypt_ballot_partial {m : nat}
        (cs : Vector.t (G * G) m) (x : F) : Vector.t G m.
      Proof.
        exact (Vector.map (fun c => decrypt_value_partial c x) cs).
      Defined.

      (** [decrypt_ballot_value cs ds] combines the factor vectors [ds] of
          all [1 + n] trustees (one row per trustee) by multiplying them
          component-wise, and returns [c₂ · (combined factor)⁻¹] for every
          ciphertext of the ballot. *)
      Definition decrypt_ballot_value {n m : nat}
        (cs : Vector.t (G * G) m)
        (ds : Vector.t (Vector.t G m) (1 + n)) : Vector.t G m.
      Proof.
        destruct (vector_inv_S ds) as (dsh & dst & _).
        set (acc := fold_right (zip_with gop) dst dsh).
        exact (zip_with (fun '(c₁, c₂) d =>  gop c₂ (ginv d)) cs acc).
      Defined.

  End Def.

  (** ** Correctness proofs *)
  Section Proofs.

    (** *** Auxiliary algebra *)
    Add Field field : (@field_theory_for_stdlib_tactic F
       eq zero one opp add mul sub inv div vector_space_field).

    (** In an abelian group, [(u · v) · (x · y) = (u · x) · (v · y)]. *)
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

    (** Single-trustee ballot decryption: with public key [h = g ^ x] (the
        product key of one trustee is [h · gid]) and factors
        [dsᵢ = (g ^ rsᵢ) ^ x], decrypting each component of
        [encrypted_ballot ms rs] yields [g ^ msᵢ]. Not used by the
        main theorems. *)
    Theorem decrypt_ballot_value_correct_base_case :
      ∀ (n : nat) (x : F) (g h : G)
      (ms rs : Vector.t F n) (ds : Vector.t G n),
      h = g ^ x -> (∀ (fa : Fin.t n), ds[@fa] = (g ^ rs[@fa]) ^ x) ->
      ∀ (f : Fin.t n),
      g ^ ms[@f] =  (zip_with (λ '(_, c₂) (d : G), gop c₂ (ginv d))
      (@encrypted_ballot F G gop gpow g (gop h gid) _ ms rs) ds)[@f].
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

    (** Encryption under [h · (hsh · gid)] equals encryption under
        [hsh · gid] followed by multiplying each second component by
        [h ^ r]. Base case of
        [decrypt_ballot_value_correct_induction_enc_forward]. *)
    Theorem decrypt_ballot_value_correct_induction_enc_forward_base_case :
      ∀ (n : nat) (g h hsh : G) (ms rs : Vector.t F n),
      @encrypted_ballot F G gop gpow g (gop h (gop hsh gid)) _ ms rs =
      zip_with (λ '(c₁, c₂) (r : F), (c₁, gop c₂ (h ^ r)))
        (@encrypted_ballot F G gop gpow g (gop hsh gid) _ ms rs) rs.
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
          pose proof vector_space_smul_distributive_vadd as hg.
          unfold is_smul_distributive_vadd in hg.
          specialize (hg rsh ghi h).
          rewrite <-hg.
          rewrite commutative. reflexivity.
        ++
          eapply ihn.
    Qed.

    (** Inductive-step helper for
        [decrypt_ballot_value_correct_induction_enc_forward]: moving the key
        factor [hsh] between the encryption key and the extra mask. *)
    Theorem decrypt_ballot_value_correct_induction_enc_forward_induction_case :
      ∀ (n : nat) (g h hsh hii : G) (ms rs : Vector.t F n),
      zip_with (λ '(c₁, c₂) (r : F), (c₁, gop c₂ (gop h hsh ^ r)))
        (@encrypted_ballot F G gop gpow g hii _ ms rs) rs =
      zip_with (λ '(c₁, c₂) (r : F), (c₁, gop c₂ (h ^ r)))
        (@encrypted_ballot F G gop gpow g (gop hsh hii) _ ms rs) rs.
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

    (** Adding a trustee: encrypting under the shares [h :: hs] is the same
        as encrypting under [hs] and multiplying the second component of the
        [i]-th ciphertext by [h ^ rsᵢ]. *)
    Theorem decrypt_ballot_value_correct_induction_enc_forward {m : nat} :
      ∀ (n : nat) (g h : G) (hs : Vector.t G (1 + n)) (ms rs : Vector.t F m),
      encrypt_ballot_dist g (h :: hs) ms rs =
      zip_with (fun '(c₁, c₂) r =>  (c₁, gop c₂ (h ^ r)))
      (encrypt_ballot_dist g hs ms rs) rs.
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

    (** Base case of [decrypt_ballot_value_correct_induction_enc_backward]:
        removing the factor [h] from the key corresponds to dividing each
        second component by [h ^ r]. *)
    Theorem decrypt_ballot_value_correct_induction_enc_backward_base_case :
      ∀ (n : nat) (g h hsh : G) (ms rs : Vector.t F n),
      @encrypted_ballot F G gop gpow g (gop hsh gid) _ ms rs =
      zip_with (λ '(c₁, c₂) r, (c₁, gop c₂ (ginv (h ^ r))))
        (@encrypted_ballot F G gop gpow g (gop h (gop hsh gid)) _ ms rs) rs.
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
          pose proof vector_space_smul_distributive_vadd as hg.
          unfold is_smul_distributive_vadd in hg.
          specialize (hg rsh h ghi).
          rewrite hg.
          rewrite commutative, associative.
          rewrite group_is_left_inverse, left_identity.
          reflexivity.
        ++
          eapply ihn.
    Qed.

    (** Inductive-step helper for
        [decrypt_ballot_value_correct_induction_enc_backward]. *)
    Theorem decrypt_ballot_value_correct_induction_enc_backward_induction_case :
      ∀ (n : nat) (g h hsh hii : G) (ms rs : Vector.t F n),
      @encrypted_ballot F G gop gpow g hii _ ms rs =
      zip_with (λ '(c₁, c₂) r, (c₁, gop c₂ (ginv (h ^ r))))
        (@encrypted_ballot F G gop gpow g (gop h hii) _ ms rs) rs ->
      @encrypted_ballot F G gop gpow g (gop hsh hii) _ ms rs =
      zip_with (λ '(c₁, c₂) r, (c₁, gop c₂ (ginv (h ^ r))))
        (@encrypted_ballot F G gop gpow g (gop hsh (gop h hii)) _ ms rs) rs.
    Proof.
      induction n as [|n ihn].
      +
        intros * ha.
        pose proof (vector_inv_0 ms) as hb.
        pose proof (vector_inv_0 rs) as hc.
        subst; cbn. reflexivity.
      +
        intros * ha.
        destruct (vector_inv_S ms) as (msh & mst & hb).
        destruct (vector_inv_S rs) as (rsh & rst & hc).
        subst. cbn.
        f_equal.
        ++
          unfold enc. f_equal.
          rewrite <-associative.
          f_equal.
          pose proof vector_space_smul_distributive_vadd as hg.
          unfold is_smul_distributive_vadd in hg.
          pose proof (hg rsh hsh (gop h hii)) as hb.
          rewrite hb. clear hb.
          rewrite <-associative.
          pose proof (hg rsh h hii) as hb.
          rewrite hb; clear hb.
          assert (hb : (gop (h ^ rsh) (hii ^ rsh)) =
            (gop (hii ^ rsh) (h ^ rsh))).
          rewrite commutative; reflexivity.
          rewrite hb; clear hb.
          rewrite <-associative.
          rewrite group_is_right_inverse,
          right_identity.
          eapply hg.
        ++
          eapply ihn.
          cbn in ha. unfold encrypted_ballot, enc in ha.
          pose proof @vec_inv_tail _ _ (g ^ rsh, gop (g ^ msh) (hii ^ rsh))
          (g ^ rsh, gop (gop (g ^ msh) (gop h hii ^ rsh)) (ginv (h ^ rsh)))
          (zip_with (λ m r : F, (g ^ r, gop (g ^ m) (hii ^ r))) mst rst)
          (zip_with (λ '(c₁, c₂) (r : F), (c₁, gop c₂ (ginv (h ^ r))))
            (zip_with (λ m r : F, (g ^ r, gop (g ^ m) (gop h hii ^ r))) mst rst) rst)
          ha as hb.
          exact hb.
    Qed.

    (** Removing a trustee: encrypting under [hs] equals encrypting under
        [h :: hs] and dividing the second component of the [i]-th ciphertext
        by [h ^ rsᵢ]. Converse of
        [decrypt_ballot_value_correct_induction_enc_forward]. *)
    Theorem decrypt_ballot_value_correct_induction_enc_backward {m : nat} :
      ∀ (n : nat) (g h : G) (hs : Vector.t G (1 + n)) (ms rs : Vector.t F m),
      encrypt_ballot_dist g hs ms rs =
      zip_with (fun '(c₁, c₂) r => (c₁, gop c₂ (ginv (h ^ r))))
      (encrypt_ballot_dist g (h :: hs) ms rs) rs.
    Proof.
       induction n as [|n ihn].
      +
        intros *.
        unfold encrypt_ballot_dist.
        cbn.
        destruct (vector_inv_S hs) as (hsh & hst & ha).
        pose proof (vector_inv_0 hst) as hb.
        subst. cbn.
        eapply decrypt_ballot_value_correct_induction_enc_backward_base_case.
      +
        intros *.
        destruct (vector_inv_S hs) as (hsh & hst & ha).
        unfold encrypt_ballot_dist in ihn |- *.
        cbn in ihn |- *. subst. cbn.
        specialize (ihn g h hst ms rs).
        remember ((fold_right (λ hi acc : G, gop hi acc) hst gid)) as hii.
        assert(ha : (gop h (gop hsh hii)) =
          (gop hsh (gop h hii))).
        rewrite associative.
        assert (hb : gop h hsh = gop hsh h).
        rewrite commutative; reflexivity.
        rewrite hb; clear hb.
        rewrite associative; reflexivity.
        rewrite ha; clear ha.
        eapply decrypt_ballot_value_correct_induction_enc_backward_induction_case.
        exact ihn.
    Qed.

    (** The joint public key is [g] raised to the sum of the secret shares:
        if [g ^ xsᵢ = hsᵢ] for all [i], then [Π hs = g ^ (Σ xs)]. By
        induction on the number of shares. *)
    Theorem group_gen_mul_power_add : ∀ (n : nat)
      (g : G) (hs : Vector.t G n) (xs : Vector.t F n),
      (∀ i : Fin.t n, g ^ xs[@i] = hs[@i]) ->
      (fold_right (λ hi acc : G, gop hi acc) hs gid) =
      g ^ (fold_right (λ hi acc : F, add hi acc) xs zero).
    Proof.
      induction n as [|n ihn].
      +
        intros * hf.
        pose proof (vector_inv_0 hs) as ha.
        pose proof (vector_inv_0 xs) as hb.
        subst. cbn.
        rewrite vector_space_field_zero;
        reflexivity.
      +
        intros * hf.
        destruct (vector_inv_S hs) as (hsh & hst & ha).
        destruct (vector_inv_S xs) as (xsh & xst & hb).
        subst. cbn.
        pose proof (hf Fin.F1) as ha.
        cbn in ha.
        assert(hb : (∀ i : Fin.t n, g ^ xst[@i] = hst[@i])).
        refine (fun i : Fin.t n => _). specialize (hf (Fin.FS i)).
        cbn in hf. exact hf.
        specialize (ihn g hst xst hb).
        rewrite ihn. subst.
        pose proof vector_space_smul_distributive_fadd as hc.
        specialize (hc xsh (fold_right (λ hi acc : F, hi + acc) xst zero) g).
        rewrite hc.
        reflexivity.
    Qed.

    (** Base case of [encryption_factor_combine]: one trustee’s factors
        [dshᵢ = (g ^ rsᵢ) ^ xsh] equal [(g ^ (xsh + 0)) ^ rsᵢ]. *)
    Theorem encryption_factor_combine_base_case :
      ∀ (m : nat) (g : G) (xsh : F)
      (dsh : Vector.t G m) (rs : Vector.t F m),
      (∀ fb : t m, dsh[@fb] = (g ^ rs[@fb]) ^ xsh) ->
      dsh = map (λ r : F, (g ^ (xsh + zero)) ^ r) rs.
    Proof.
      induction m as [|m ihm].
      +
        intros * ha.
        pose proof (vector_inv_0 dsh) as hb.
        pose proof (vector_inv_0 rs) as hc.
        subst. cbn.
        reflexivity.
      +
        intros * ha.
        destruct (vector_inv_S dsh) as (dshh & dsht & hc).
        destruct (vector_inv_S rs) as (rsh & rst & hd).
        subst. cbn.
        f_equal.
        ++
          specialize (ha Fin.F1).
          cbn in ha.
          subst.
          rewrite right_identity.
          pose proof vector_space_smul_associative_fmul as ha.
          rewrite <-(ha rsh xsh g).
          rewrite <-(ha xsh rsh g).
          assert (hb : rsh * xsh = xsh * rsh). field.
          rewrite hb. reflexivity.
        ++
          eapply ihm.
          exact (fun f : Fin.t m => ha (Fin.FS f)).
    Qed.

    (** Adding one trustee’s factors: if [dsᵢ = (g ^ rsᵢ) ^ xa], then
        [dsᵢ · (g ^ xb) ^ rsᵢ = (g ^ (xa + xb)) ^ rsᵢ] component-wise. *)
    Theorem encryption_factor_combine_induction_case :
      ∀ (m : nat) (g : G) (xa xb : F) (ds : Vector.t G m)
      (rs : Vector.t F m),
      (∀ fb : Fin.t m, ds[@fb] = (g ^ rs[@fb]) ^ xa) ->
      zip_with gop ds (map (λ r : F, (g ^ xb) ^ r) rs) =
      map (λ r : F, (g ^ (xa + xb)) ^ r) rs.
    Proof.
      induction m as [|m ihm].
      +
        intros * ha.
        pose proof (vector_inv_0 ds) as hc.
        pose proof (vector_inv_0 rs) as hd.
        subst. cbn.
        reflexivity.
      +
        intros * ha.
        destruct (vector_inv_S ds) as (dsh & dst & hc).
        destruct (vector_inv_S rs) as (rsh & rst & hd).
        subst. cbn.
        f_equal.
        ++
          specialize (ha Fin.F1).
          cbn in ha. subst.
          pose proof vector_space_smul_associative_fmul as ha.
          rewrite <-(ha rsh xa g).
          rewrite <-(ha xb rsh g).
          rewrite <-(ha (xa + xb) rsh g).
          pose proof vector_space_smul_distributive_fadd as hc.
          rewrite <-(hc (rsh * xa) (xb * rsh)).
          assert (hd : (rsh * xa + xb * rsh) = ((xa + xb) * rsh)).
          field.
          rewrite hd. reflexivity.
        ++
          eapply ihm.
          exact (fun f : Fin.t m => ha (Fin.FS f)).
    Qed.

    (** Combining decryption factors: if each trustee’s factor vector is
        well formed, [dsᵢ = (g ^ rsᵢ) ^ xⱼ] for trustee [j], then their
        component-wise product is the vector of [(g ^ (Σ xⱼ)) ^ rsᵢ], i.e. the
        mask [h ^ rsᵢ] under the joint key. By induction on the number of
        additional trustees. *)
    Theorem encryption_factor_combine : ∀ (n m : nat)
      (g : G) (dst : Vector.t (Vector.t G m) n)
      (dsh : Vector.t G m) (rs : Vector.t F m)
      (xsh : F) (xst : Vector.t F n),
      (∀ fb : t m, dsh[@fb] = (g ^ rs[@fb]) ^ xsh) ->
      (∀ (f : t n) (fb : t m), (dst[@f])[@fb] = (g ^ rs[@fb]) ^ xst[@f]) ->
      fold_right (zip_with gop) dst dsh =
      map (λ r : F, (g ^ (xsh + fold_right
        (λ hi acc : F, hi + acc) xst zero)) ^ r) rs.
    Proof.
      induction n as [|n ihn].
      +
        intros * ha hb.
        pose proof (vector_inv_0 dst) as hc.
        pose proof (vector_inv_0 xst) as hd.
        subst. cbn.
        eapply encryption_factor_combine_base_case;
        assumption.
      +
        intros * ha hb.
        destruct (vector_inv_S dst) as (dsth & dstt & hc).
        destruct (vector_inv_S xst) as (xsth & xstt & hd).
        subst. cbn.
        specialize (ihn _ g dstt dsh rs xsh xstt ha
          (fun f : Fin.t n => hb (Fin.FS f))).
        rewrite ihn.
        remember (fold_right (λ hi acc : F, hi + acc) xstt zero) as xsacc.
        specialize (hb Fin.F1). cbn in hb.
        assert (hc : (xsh + (xsth + xsacc)) =
          (xsth + (xsh + xsacc))). field.
        rewrite hc.
        remember (xsh + xsacc) as xc.
        eapply encryption_factor_combine_induction_case;
        assumption.
    Qed.

    (** Plain ElGamal decryption with secret key [xsacc] and the correct
        mask: [c₂ · (mask)⁻¹] for [enc mᵢ rᵢ] under [g ^ xsacc] gives
        [g ^ mᵢ] component-wise. *)
    Theorem simplify_decryption :
      ∀ (n : nat) g (ms rs : Vector.t F n) (xsacc : F),
      Vector.map (λ x : F, g ^ x) ms =
      zip_with (λ '(_, c₂) (d : G), gop c₂ (ginv d))
        (zip_with (λ m r : F, (g ^ r, gop (g ^ m) ((g ^ xsacc) ^ r)))
          ms rs)
        (Vector.map (λ r : F, (g ^ xsacc) ^ r) rs).
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        pose proof (vector_inv_0 ms) as hc.
        pose proof (vector_inv_0 rs) as hd.
        subst. cbn.
        reflexivity.
      +
        intros *.
        destruct (vector_inv_S ms) as (msh & mst & hc).
        destruct (vector_inv_S rs) as (rsh & rst & hd).
        subst. cbn.
        f_equal.
        ++
          rewrite <-associative.
          pose proof vector_space_smul_associative_fmul as ha.
          rewrite <-(ha xsacc rsh g).
          rewrite group_is_right_inverse, right_identity.
          reflexivity.
        ++
          eapply ihn.
    Qed.

    (** Index-wise view of [map]: [g ^ msᶠ] is the [f]-th entry of
        [map (fun x => g ^ x) ms]. *)
    Theorem fin_map_rel : ∀ (n : nat)
      (g : G) (ms : Vector.t F n),
      ∀ (f : Fin.t n),
      g ^ ms[@f] = (map (λ x : F, g ^ x) ms)[@f].
    Proof.
      induction n as [|n ihn].
      +
        intros *.
        refine match f with end.
      +
        intros *.
        destruct (vector_inv_S ms) as (msh & mst & ha).
        destruct (fin_inv_S _ f) as [f' | (f' & hb)].
        ++
          subst; cbn.
          reflexivity.
        ++
          subst; cbn.
          eapply ihn.
    Qed.

    (** *** Main correctness theorems

        For the remainder of the section, fix [1 + n] trustees with secret
        shares [xs] and public shares [hs], and assume [hrel]:
        [g ^ xsᵢ = hsᵢ] for every trustee [i]. In a deployment this
        relation is established by a zero-knowledge proof of knowledge of
        each share. *)
    Context
      {n : nat}
      {g : G}
      {xs : Vector.t F (1 + n)}
      {hs : Vector.t G (1 + n)}
      (hrel : ∀ (i : Fin.t (1 + n)), gpow g (Vector.nth xs i) = (Vector.nth hs i)).

    (** Cancellation of the combined mask: if every [dsᵢ = (g ^ r) ^ xsᵢ],
        then [(Π hs) ^ r · (Π ds)⁻¹ = gid]. By induction on [n]
        (generalising [xs], [hs] and [hrel]). *)
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
        (* Inductive step: split off the first trustee, distribute [^ r]
           over the product key, regroup with
           [group_shuffle_commutative], cancel the tail by the induction
           hypothesis and the head by [h ^ r = (g ^ r) ^ x]. *)
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
        pose proof vector_space_smul_distributive_vadd as hg.
        unfold is_smul_distributive_vadd in hg.
        specialize (hg r h hii).
        rewrite hg; clear hg.
        rewrite group_inv_flip.
        assert (hj : gop (ginv dii) (ginv d) = gop (ginv d) (ginv dii)).
        rewrite commutative; reflexivity. rewrite hj; clear hj.
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

    (** Correctness of distributed decryption for one ciphertext: if
        [c = encrypt_value_dist g hs m r] and each [dsᵢ] is the correct
        partial decryption [decrypt_value_partial c xsᵢ], then
        [decrypt_value c ds = g ^ m]. Follows from
        [fold_right_identity]. *)
    Theorem decryption_value_correct : ∀ (m r : F) (c : G * G)
      (ds : Vector.t G (1 + n)), c = encrypt_value_dist g hs m r ->
      (∀ (f : Fin.t (1 + n)), Vector.nth ds f =
      decrypt_value_partial c (Vector.nth xs f)) ->
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

    (** Ballot-level correctness as a vector equation: for well-formed
        factor rows [dsh :: dst], decrypting the ballot encrypted under the
        joint key yields [map (fun x => g ^ x) ms]. Proof: rewrite the joint
        key as [g ^ Σ xs] ([group_gen_mul_power_add]), combine the factor
        rows ([encryption_factor_combine]) and apply
        [simplify_decryption]. *)
    Theorem decrypt_ballot_value_correct_aux : ∀ {m : nat}
      (ms rs : Vector.t F m)
      (dsh : (Vector.t G m)) (dst : Vector.t (Vector.t G m) n),
      (∀ (fa : Fin.t (1 + n)) (fb : Fin.t m),
        (dsh :: dst)[@fa][@fb] = (g ^ rs[@fb]) ^ xs[@fa]) ->
      Vector.map (fun x => g ^ x) ms = @decrypt_ballot_value n m
        (@encrypt_ballot_dist n m g hs ms rs) (dsh :: dst).
    Proof.
      intros * ha.
      cbn. unfold encrypt_ballot_dist.
      assert (hb : (fold_right (λ hi acc : G, gop hi acc) hs gid) =
        g ^ (fold_right (λ hi acc : F, add hi acc) xs zero)).
      eapply  group_gen_mul_power_add; assumption.
      rewrite hb; clear hb.
      remember (fold_right (λ hi acc : F, hi + acc) xs zero) as xsacc.
      pose proof (ha Fin.F1) as hc. cbn in hc.
      pose proof (fun f : Fin.t n => ha (Fin.FS f)) as hd.
      cbn in hd.
      destruct (vector_inv_S xs) as (xsh & xst & he).
      subst. cbn in hc, hd. cbn.
      assert (he : (fold_right (zip_with gop) dst dsh) =
        map (fun r => (g ^ (xsh + fold_right (λ hi acc : F, hi + acc)
          xst zero)) ^ r) rs).
      apply encryption_factor_combine; try assumption.
      rewrite he.
      remember (xsh + fold_right (λ hi acc : F, hi + acc) xst zero) as xsacc.
      unfold encrypted_ballot, enc.
      eapply simplify_decryption.
    Qed.

    (** Correctness of distributed ballot decryption: if each trustee’s
        factor row is well formed, [dsⱼᵢ = (g ^ rsᵢ) ^ xsⱼ] (i.e. trustee
        [j] raised the first component of ciphertext [i] to its share), and
        [cs = encrypt_ballot_dist g hs ms rs], then the [f]-th entry of
        [decrypt_ballot_value cs ds] is [g ^ msᶠ] for every [f]. Index-wise
        restatement of [decrypt_ballot_value_correct_aux]. *)
    Theorem decrypt_ballot_value_correct : ∀ {m : nat}
      (ms rs : Vector.t F m) (cs : Vector.t (G * G) m)
      (ds : Vector.t (Vector.t G m) (1 + n)),
      (∀ (fa : Fin.t (1 + n)) (fb : Fin.t m),
        ds[@fa][@fb] = (g ^ rs[@fb]) ^ xs[@fa]) ->
      cs = @encrypt_ballot_dist n m g hs ms rs ->
      ∀ (f : Fin.t m), g ^ ms[@f] =
      (@decrypt_ballot_value n m cs ds)[@f].
    Proof.
      intros * ha hb f.
      destruct (vector_inv_S ds) as (dsh & dst & hc).
      pose proof Vector.eq_nth_iff G m
      (Vector.map (fun x => g ^ x) ms)
      (decrypt_ballot_value cs ds) as hd.
      assert (he : (∀ fa fb : Fin.t m, fa = fb →
        (map (λ x : F, g ^ x) ms)[@fa] =
        (decrypt_ballot_value cs ds)[@fb])).
      {
        intros * hf.
        subst.
        erewrite decrypt_ballot_value_correct_aux.
        reflexivity.
        assumption.
      }
      destruct hd as (hdl & hdr).
      specialize (hdl he).
      rewrite <-hdl.
      eapply fin_map_rel.
    Qed.

  End Proofs.
End DistElgamal.
