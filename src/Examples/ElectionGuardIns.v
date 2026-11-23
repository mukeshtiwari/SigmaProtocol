(** * The ElectionGuard 2.0 verifier at the standard parameters *)

(** This file instantiates the certified ElectionGuard verifier
([Backend/ElectionGuardTally.v]) at the parameters of the ElectionGuard
2.0 specification (section 3.1.1): the 4096-bit prime [p], the 256-bit
prime [q = 2^256 - 189] with [p - 1 = q·r], and the generator
[g = 2^r mod p] of the subgroup of order [q]. The scalar field is [Z_q] and
the group is the order-[q] subgroup of [Z_p^*] ([Utility/Zpstar.v]), as
for Helios.

All parameters are certified. [q] is prime by the Pocklington certificate
of [primeQEG.v]. For [p], the cofactor [r] (about 3840 bits) is not
factored, so Pocklington's criterion does not apply; [p] is proved prime by
the 147-step elliptic-curve (ECPP) certificate of [primePEG.v], generated
by PARI/GP's [primecert] and converted by [bench/ecpp2coq.py]. The
relation [p = r·q + 1] and the membership [g^q mod p = 1] are checked by
computation, the latter with the [BigN] exponentiation of [BigNPow.v].

The hash functions of ElectionGuard (HMAC-SHA-256 over the encodings of
section 5) are computed by the OCaml driver [Executable/Egverifier] and
passed in through the hash records; they are trusted, as are the parser
and the checks that concern only hashes (manifest, base hashes,
confirmation codes), which the driver performs. The file is extracted by
[src/Extraction/Electionguardlib]. *)

(** ** How an ElectionGuard 2.0 election is checked

Guardian [i] chooses a polynomial with coefficients [a_ij] and publishes
[K_ij = g^a_ij], each with a Schnorr proof of knowledge; the joint key is
[K = ∏ᵢ K_i0]. Version 2.0 puts the vote in the exponent of [K]: a
selection [σ] is encrypted with nonce [ξ] as [(α, β) = (g^ξ, K^ξ·K^σ)].

Each option carries a range proof that it encrypts a value in [0..R], and
each contest a selection-limit proof that the product of its option
ciphertexts encrypts a value in [0..L]. Both are disjunctions over [j] of
the Chaum–Pedersen statement [(α, β/K^j) = (g, K)^ξ], a Schnorr statement
in [G × G]. ElectionGuard stores [(c_j, v_j)] per branch; the verifier
reconstructs the announcements and accepts if the hash (keyed by the
extended base hash) equals [Σ c_j]. This is the same reconstruction as in
Belenios, so the Fiat–Shamir layer of [Backend/BeleniosTally.v] is reused.

The tally is the product of the cast ballots' ciphertexts per option. The
guardians publish [M = A^s] for the joint secret [s] with a Chaum–Pedersen
proof of [(K, M) = (g, A)^s], and the decrypted value [t] satisfies
[B/M = K^t].

[Backend/ElectionGuardTally.v] proves that accepted coefficient, range,
selection-limit and decryption proofs are accepting transcripts of the
library's protocols, and [compute_final_count] returns a certificate of the
counting relation. This file restates two of those theorems at the
concrete parameters. *)
From Stdlib Require Import Utf8 ZArith Znumtheory Zpow_facts List Lia.
From Algebra Require Import Hierarchy.
From Sigma Require Import Sigma OrSigmaGen.
From Backend Require Import BeleniosTally ElectionGuardTally.
From Utility Require Import Zpstar Util.
From Examples Require Import primeQEG primePEG BigNPow.
Import Vspace Schnorr Zpfield Zpgroup.

(** ** The parameters *)
Section ElectionGuardIns.

  Local Open Scope Z_scope.

  (** [q = 2^256 - 189], the order of the group. *)
  Definition q : Z := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF43.

  (** The 4096-bit prime [p] of the ElectionGuard 2.0 specification. *)
  Definition p : Z := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFB17217F7D1CF79ABC9E3B39803F2F6AF40F343267298B62D8A0D175B8BAAFA2BE7B876206DEBAC98559552FB4AFA1B10ED2EAE35C138214427573B291169B8253E96CA16224AE8C51ACBDA11317C387EB9EA9BC3B136603B256FA0EC7657F74B72CE87B19D6548CAF5DFA6BD38303248655FA1872F20E3A2DA2D97C50F3FD5C607F4CA11FB5BFB90610D30F88FE551A2EE569D6DFC1EFA157D2E23DE1400B39617460775DB8990E5C943E732B479CD33CCCC4E659393514C4C1A1E0BD1D6095D25669B333564A3376A9C7F8A5E148E82074DB6015CFE7AA30C480A5417350D2C955D5179B1E17B9DAE313CDB6C606CB1078F735D1B2DB31B5F50B5185064C18B4D162DB3B365853D7598A1951AE273EE5570B6C68F96983496D4E6D330AF889B44A02554731CDC8EA17293D1228A4EF98D6F5177FBCF0755268A5C1F9538B98261AFFD446B1CA3CF5E9222B88C66D3C5422183EDC99421090BBB16FAF3D949F236E02B20CEE886B905C128D53D0BD2F9621363196AF503020060E49908391A0C57339BA2BEBA7D052AC5B61CC4E9207CEF2F0CE2D7373958D762265890445744FB5F2DA4B751005892D356890DEFE9CAD9B9D4B713E06162A2D8FDD0DF2FD608FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF.

  (** The cofactor [r = (p - 1)/q]. *)
  Definition r : Z := 0x100000000000000000000000000000000000000000000000000000000000000BCB17217F7D1CF79ABC9E3B39803F2F6AF40F343267298B62D8A0D175B8BAB857AE8F428165418806C62B0EA36355A3A73E0C741985BF6A0E3130179BF2F0B43E33AD862923861B8C9F768C4169519600BAD06093F964B27E02D86831231A9160DE48F4DA53D8AB5E69E386B694BEC1AE722D47579249D5424767C5C33B9151E07C5C11D106AC446D330B47DB59D352E47A53157DE04461900F6FE360DB897DF5316D87C94AE71DAD0BE84B647C4BCF818C23A2D4EBB53C702A5C8062D19F5E9B5033A94F7FF732F54129712869D97B8C96C412921A9D8679770F499A041C297CFF79D4C9149EB6CAF67B9EA3DC563D965F3AAD1377FF22DE9C3E62068DD0ED6151C37B4F74634C2BD09DA912FD599F4333A8D2CC005627DCA37BAD43E64A3963119C0BFE34810A21EE7CFC421D53398CBC7A95B3BF585E5A04B790E2FE1FE9BC264FDA8109F6454A082F5EFB2F37EA237AA29DF320D6EA860C41A9054CCD24876C6253F667BFB0139B5531FF30189961202FD2B0D55A75272C7FD73343F7899BCA0B36A4C470A64A009244C84E77CEBC92417D5BB13BF18167D8033EB6C4DD7879FD4A7F529FD4A7F529FD4A7F529FD4A7F529FD4A7F529FD4A7F529FD4A7F52A.

  (** The generator [g = 2^r mod p], as an integer. *)
  Definition gval : Z := 0x36036FED214F3B50DC566D3A312FE4131FEE1C2BCE6D02EA39B477AC05F7F885F38CFE77A7E45ACF4029114C4D7A9BFE058BF2F995D2479D3DDA618FFD910D3C4236AB2CFDD783A5016F7465CF59BBF45D24A22F130F2D04FE93B2D58BB9C1D1D27FC9A17D2AF49A779F3FFBDCA22900C14202EE6C99616034BE35CBCDD3E7BB7996ADFE534B63CCA41E21FF5DC778EBB1B86C53BFBE99987D7AEA0756237FB40922139F90A62F2AA8D9AD34DFF799E33C857A6468D001ACF3B681DB87DC4242755E2AC5A5027DB81984F033C4D178371F273DBB4FCEA1E628C23E52759BC7765728035CEA26B44C49A65666889820A45C33DD37EA4A1D00CB62305CD541BE1E8A92685A07012B1A20A746C3591A2DB3815000D2AACCFE43DC49E828C1ED7387466AFD8E4BF1935593B2A442EEC271C50AD39F733797A1EA11802A2557916534662A6B7E9A9E449A24C8CFF809E79A4D806EB681119330E6C57985E39B200B4893639FDFDEA49F76AD1ACD997EBA13657541E79EC57437E504EDA9DD011061516C643FB30D6D58AFCCD28B73FEDA29EC12B01A5EB86399A593A9D5F450DE39CB92962C5EC6925348DB54D128FD99C14B457F883EC20112A75A6A0581D3D80A3B4EF09EC86F9552FFDA1653F133AA2534983A6F31B0EE4697935A6B1EA2F75B85E7EBA151BA486094D68722B054633FEC51CA3F29B31E77E317B178B6B9D8AE0F.

  (** [q] is prime, by the Pocklington certificate of [primeQEG.v]. *)
  Theorem prime_q : prime q.
  Proof. exact primeQEG.prime_q_eg. Qed.

  (** [p] is prime, by the ECPP certificate of [primePEG.v]. *)
  Theorem prime_p : prime p.
  Proof. exact primePEG.prime_p_eg. Qed.

  (** [p = r·q + 1], checked by computation. *)
  Theorem cofactor : p = r * q + 1.
  Proof. vm_cast_no_check (eq_refl p). Qed.

  (** [g^q mod p = 1], so [g] lies in the subgroup of order [q]; computed with
      the [BigN] exponentiation of [BigNPow], proved equal to [Zpow_mod]. *)
  Theorem g_order : Zpow_mod gval q p = 1.
  Proof.
    unfold q; rewrite BigNPow.bpow_mod_spec by (vm_compute; discriminate).
    vm_cast_no_check (eq_refl 1).
  Qed.

  (** The scalar field [Z_q]. *)
  Definition F : Type := @Zp q.
  (** The order-[q] subgroup of [Z_p^*]. *)
  Definition G : Type := @Schnorr_group p q.

  (** [g] as a group element, with membership proof [g_order]. *)
  Definition generator : G.
  Proof.
    refine {| Schnorr.v := gval; Ha := conj eq_refl eq_refl : (0 < gval < p); Hb := g_order |}.
  Defined.

  (** The field operations [Fzero], [Fone], [Fadd], [Fdec] and the group
      operations [Gone], [Ginv], [Gmul], [Gpow], [Gdec] at these parameters. *)
  Definition Fzero : F := @Zpfield.zero q prime_q.
  Definition Fone : F := @Zpfield.one q prime_q.
  Definition Fadd : F -> F -> F := @zp_add q.
  Definition Fdec : forall x y : F, {x = y} + {x <> y} := @zp_dec q.
  Definition Gone : G := @Schnorr.one p q prime_p prime_q.
  Definition Ginv : G -> G := @inv_schnorr_group r p q cofactor prime_p prime_q.
  Definition Gmul : G -> G -> G := @mul_schnorr_group p q prime_p prime_q.
  Definition Gpow : G -> F -> G := @pow r p q cofactor prime_p prime_q.
  Definition Gdec : forall x y : G, {x = y} + {x <> y} := @Schnorr.dec_zpstar p q.

  (** ** The data types

      The records of [Backend/ElectionGuardTally.v] at these parameters, for
      the driver: a proof (one challenge/response pair), a ciphertext, a
      contest specification, the election record, a selection, a contest, a
      ballot, the driver-computed ballot hashes, a guardian, the guardian
      hashes, a decryption share and the decryption hashes. *)
  Definition proof := @proof F.
  Definition ciphertext := @ciphertext G.
  Definition contest_spec := contest_spec.
  Definition election := @election G.
  Definition selection := @selection F G.
  Definition contest := @contest F G.
  Definition ballot := @ballot F G.
  Definition ballot_hashes := @ballot_hashes F G.
  Definition guardian := @guardian F G.
  Definition guardian_hashes := @guardian_hashes F G.
  Definition decryption := @decryption F G.
  Definition decryption_hashes := @decryption_hashes F G.

  (** The constructors of the records above. *)
  Definition mk_contest_spec := mk_contest_spec.
  Definition mk_election := @mk_election G.
  Definition mk_selection := @mk_selection F G.
  Definition mk_contest := @mk_contest F G.
  Definition mk_ballot := @mk_ballot F G.
  Definition mk_ballot_hashes := @mk_ballot_hashes F G.
  Definition mk_guardian := @mk_guardian F G.
  Definition mk_guardian_hashes := @mk_guardian_hashes F G.
  Definition mk_decryption := @mk_decryption F G.
  Definition mk_decryption_hashes := @mk_decryption_hashes F G.

  (** ** The verifier

      Checks one ballot: its contest indices are strictly increasing and
      name contests of the manifest, and each contest is valid (the range
      proofs of its selections and its selection-limit proof). *)
  Definition verify_ballot_ins (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    verify_ballot (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) E hs b.

  (** The encrypted tally: per contest and option, the product of the ballots'
      ciphertexts. *)
  Definition encrypted_tally_ins (E : election) (bs : list ballot) : list (list ciphertext) :=
    encrypted_tally (gid := Gone) (gop := Gmul) E bs.

  (** Checks the guardians (verifications 2 and 3 of the specification):
      their number and indices, each coefficient's Schnorr proof, and that
      the joint key equals [K]. *)
  Definition verify_guardians_ins (E : election) (gh : guardian_hashes) (gs : list guardian) : bool :=
    verify_guardians (zero := Fzero) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) E gh gs.

  (** Checks the decryption of a challenged ballot (verifications 12 and 13);
      not part of the counting relation. *)
  Definition verify_ballot_decryptions_ins (E : election) (dh : decryption_hashes)
    (b : ballot) (ds : list (list decryption)) : bool :=
    verify_ballot_decryptions (zero := Fzero) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) E dh b ds.

  (** The certified verifier and entry point of the extracted code: from the
      ballots, guardians, published tally and decryptions it returns the
      valid and invalid ballots, the final flag and a certificate of the
      counting relation [count]. *)
  Definition compute_final_count_ins (E : election) (hs : ballot -> ballot_hashes)
    (gh : guardian_hashes) (gs : list guardian) (bs : list ballot)
    (published : list (list ciphertext)) (dh : decryption_hashes)
    (ds : list (list decryption)) :
    existsT (vbs inbs : list ballot) (bfinal : bool),
      count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
        (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
        E hs (finished (List.rev bs) vbs inbs bfinal) :=
    compute_final_count (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (gid := Gone) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec)
      E hs gh gs bs published dh ds.

  (** ** Theorems at these parameters

      The vector-space structure of [G] over [Z_q], needed to apply the
      backend's theorems. *)
  Definition eg_vspace :
    @vector_space F (@eq F) Fzero Fone Fadd (@zp_mul q) (@zp_sub q) (@zp_div q)
      (@zp_opp q prime_q) (@zp_inv q) G (@eq G) Gone Ginv Gmul Gpow :=
    @pow_vspace r p q cofactor prime_p prime_q.

  (** A range (or selection-limit) proof with [R = n + 1 ≥ 1] accepted by
      [verify_range], for any hash [H], is an accepting conversation of the
      generalised OR composition ([Crypto/OrSigmaGen.v]) for the statements
      [(α, β/K^j) = (g, K)^ξ], [j = 0..R], with the reconstructed
      announcements and the challenge vector [(-Σ cⱼ) :: (-c₀, …, -c_R)].
      Instance of [verify_range_or_accepting]. *)
  Theorem verify_range_or_accepting_ins : forall (E : election) (H : list (G * G) -> F)
    (c : ciphertext) (n : nat) (cs ss : Vector.t F (2 + n)),
    verify_range (zero := Fzero) (one := Fone) (add := Fadd) (Fdec := Fdec)
      (ginv := Ginv) (gop := Gmul) (gpow := Gpow)
      E H c (S n) (Vector.to_list (Vector.map2 pair cs ss)) = true ->
    @generalised_or_accepting_conversations F Fzero Fadd Fdec (G * G)
      (gop2 (gop := Gmul)) (gpow2 (gpow := Gpow)) (Gdec2 (Gdec := Gdec)) (2 + n)
      (Vector.const (g E, K E) (2 + n))
      (messages_from (zero := Fzero) (one := Fone) (add := Fadd) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) E c 0 (2 + n))
      (mk_sigma _ _ _
        (announcements_vec (vadd := gop2 (gop := Gmul)) (smul := gpow2 (gpow := Gpow))
          (Vector.const (g E, K E) (2 + n))
          (messages_from (zero := Fzero) (one := Fone) (add := Fadd) (ginv := Ginv) (gop := Gmul) (gpow := Gpow) E c 0 (2 + n)) cs ss)
        (Vector.cons _ (@zp_opp q prime_q (Vector.fold_right Fadd cs Fzero)) _ (Vector.map (@zp_opp q prime_q) cs)) ss) = true.
  Proof.
    intros * hv; exact (verify_range_or_accepting (Hvec := eg_vspace) E H c n cs ss hv).
  Qed.

  (** A decryption share [d] of ciphertext [c = (α, β)] accepted by
      [verify_decryption] is an accepting Schnorr conversation in [G × G]
      for the Chaum–Pedersen statement [(K, β·T⁻¹) = (g, α)^s], with the
      reconstructed announcement and challenge [-c]. Instance of
      [verify_decryption_schnorr_accepting]. *)
  Theorem verify_decryption_schnorr_accepting_ins : forall (E : election) (H : list (G * G) -> F)
    (c : ciphertext) (d : decryption),
    verify_decryption (zero := Fzero) (add := Fadd) (Fdec := Fdec)
      (ginv := Ginv) (gop := Gmul) (gpow := Gpow) (Gdec := Gdec) E H c d = true ->
    @accepting_conversation F (G * G) (gop2 (gop := Gmul)) (gpow2 (gpow := Gpow)) (Gdec2 (Gdec := Gdec))
      (g E, fst c) (K E, Gmul (snd c) (Ginv d.(dT)))
      (mk_sigma _ _ _
        (Vector.cons _ (reconstruct (vadd := gop2 (gop := Gmul)) (smul := gpow2 (gpow := Gpow))
          (g E, fst c) (K E, Gmul (snd c) (Ginv d.(dT))) (fst d.(dproof)) (snd d.(dproof))) _ (Vector.nil _))
        (Vector.cons _ (@zp_opp q prime_q (fst d.(dproof))) _ (Vector.nil _))
        (Vector.cons _ (snd d.(dproof)) _ (Vector.nil _))) = true.
  Proof.
    intros * hv; exact (verify_decryption_schnorr_accepting (Hvec := eg_vspace) E H c d hv).
  Qed.

End ElectionGuardIns.
