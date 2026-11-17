(** * SHA-256 in Rocq

    This file is an executable implementation of the SHA-256 hash function
    as specified in NIST FIPS 180-4 (see also RFC 4634/6234), written over
    the binary naturals [N] and the standard library's [byte] type.  It was
    written so that Fiat–Shamir challenges could be computed inside Rocq.
    At present no other Rocq file imports it: the extracted verifiers in
    [src/Executable] hash with OCaml's Cryptokit instead.

    Only functional behaviour is checked.  The four lemmas [sha256_1st] to
    [sha256_4th] evaluate [sha256_string] with [vm_compute] on standard
    test vectors (the empty string, ‘abc’, and the 448-bit and 896-bit
    messages from FIPS 180-2) and compare against the published digests.
    No correspondence with a formal specification of SHA-256 is proved.
    The structural facts that are proved concern the message preparation:
    the padded message has length [n + wt + 8], a multiple of 64 bytes
    ([prepared_message_correctness], [div_64]), and the length field is
    exactly 8 bytes ([message_length_byte_8]).

    Layout of the file:

    - [Wf_proof] and [Util]: well-foundedness of [<] on [N] and base-256
      logarithm lemmas, used to convert a natural number into bytes.
    - [Fuel]: the fuel-driven conversion [byte_list_from_N] of a number into
      its little-endian base-256 digits, with the correctness theorem
      [byte_list_from_N_correct] ([horner_eval_byte_list] inverts it).
    - [Wellfounded]: an alternative conversion [byte_list_sig] by
      well-founded recursion, with its specification in the type.  It is
      slow because it carries proofs, and is not used further.
    - [Sha256]: the 32-bit word operations, the round functions, the
      constants, message padding, the message schedule [W], the compression
      function [sha256_intermediate] and the hash [sha256].
    - Top level: [sha256_string] and the test vectors. *)
From Stdlib Require Import Lia
  Utf8 Bool Init.Byte
  NArith Strings.Byte
  ZArith Lists.List.

Import Notations ListNotations.
Local Open Scope N_scope.

(** ** Well-founded induction on [N]

    These lemmas show that [<] on [N] is well-founded so that functions on
    [N] can be defined by well-founded recursion ([byte_list_sig]). *)
Section Wf_proof.

  (** Local abbreviation for [N.to_nat]. *)
  Let f (a : N) := N.to_nat a.

  (** [zwf x y] orders binary naturals by their [nat] value. *)
  Definition zwf (x y : N) := (f x < f y)%nat.

  (** [zwf] is well-founded (it is the inverse image of [<] on [nat]). *)
  Lemma zwf_well_founded : well_founded zwf.
  Proof.
    exact (well_founded_ltof _ f).
  Defined.

  (** Every [a < x] is accessible for [N.lt]; proof by induction on
      [N.to_nat x]. *)
  Lemma N_acc (x : N) : forall a, a < x -> Acc N.lt a.
  Proof.
    induction (zwf_well_founded x) as [z Hz IHz].
    intros ? Hxa.
    constructor; intros y Hy.
    eapply IHz with (y := a).
    unfold zwf. unfold f.
    abstract nia. abstract nia.
  Defined.

  (** [N.lt] is well-founded. *)
  Lemma N_lt_wf : well_founded N.lt.
  Proof.
    red; intros ?.
    constructor; intros y Hy.
    eapply N_acc with (x := a).
    exact Hy.
  Defined.

  (** Every [up : N] is accessible for [<]; used as the recursion principle of
      [byte_list_sig]. *)
  Lemma N_Lt_wf : forall up, Acc (fun x y => x < y) up.
  Proof.
    intros up.
    pose proof (N_lt_wf up).
    exact H.
  Defined.

End Wf_proof.

(** ** Bytes and base-256 logarithms *)
Section Util.

  (** [np_total np H] converts a natural [np] together with a proof
      [np <? 256 = true] into a [byte], making the partial
      [Byte.of_N] total.  The impossible [None] branch is discharged with an
      abstracted proof, and the definition ends with [Defined] so that it
      computes. *)
  Definition np_total (np : N):  (np <? 256 = true) ->  byte.
  Proof.
    intros H.
    pose proof of_N_None_iff np as Hn.
    destruct (of_N np) as [b | ].
    + exact b.
    + exfalso; abstract (apply N.ltb_lt in H;
        intuition nia).
  Defined.

  (** [np_total] agrees with [Byte.of_N] when the latter succeeds. *)
  Lemma np_true : forall np (H : np <? 256 = true) x, of_N np = Some x ->
    np_total np H = x.
  Proof.
    unfold np_total; intros * Heq.
    generalize (of_N_None_iff np).
    rewrite Heq; intros; reflexivity.
  Qed.

  (** [np mod 256 < 256]. *)
  Lemma nmod_256 : forall np, np mod 256 < 256.
  Proof.
    intros; eapply N.mod_lt; intro H;
    inversion H.
  Qed.

  (** Boolean form of [nmod_256], the proof argument passed to [np_total]. *)
  Lemma nmod_256_dec : forall np, (np mod 256 <? 256) = true.
  Proof.
    intros; apply N.ltb_lt.
    apply nmod_256.
  Qed.

  (** For [up ≥ 256] and [t = up / 256], [t / 256 < t]: dividing by [256]
      strictly decreases a number that is at least [1]. *)
  Lemma N_eq_gt : forall up t : N, 256 <= up -> t = up / 256 -> 0 <=  t / 256 < t.
  Proof.
    intros up t Hup Ht.
    split.
    apply N.le_0_l.
    apply N.Div0.div_lt_upper_bound.
    assert (Hot: 1 <= t).
    rewrite Ht.
    apply N.div_le_lower_bound.
    nia.
    simpl. exact Hup. nia.
  Qed.

  (** [log256 n = ⌊log₂ n⌋ / 8] is the integer base-256 logarithm, that is,
      one less than the number of bytes needed to write [n] (for [n > 0];
      [log256 0 = 0]). *)
  Definition log256 n := N.div (N.log2 n) 8.

  (** For [t ≥ 1], [t + 1 ≤ 2 · 2^⌊log₂ t⌋]. *)
  Lemma ulogt : forall t : N, 1 <= t -> t + 1 <= 2 * 2 ^ N.log2 t.
  Proof.
    intros t Ht.
    assert (Htw : t + 1 = N.succ t).
    nia. rewrite Htw.
    apply N.lt_pred_le.
    rewrite N.pred_succ.
    assert (Hs : 2 * 2 ^ N.log2 t = 2 ^ (1 + N.log2 t)).
    rewrite N.pow_add_r. simpl. nia. rewrite Hs; clear Hs.
    assert (Hn : 1 + N.log2 t = N.succ (N.log2 t)).
    nia. assert (Htt : 0 < t). nia.
    pose proof  (N.log2_spec t Htt).
    rewrite Hn. nia.
  Qed.

  (** Uniqueness of [log₂] under shifting: if [a = t · 2^b + c] with
      [t ≥ 1] and [0 ≤ c < 2^b], then [⌊log₂ a⌋ = b + ⌊log₂ t⌋]. *)
  Lemma log256_unique : forall t a b c, 1 <= t -> 0 <= b -> 0 <= c < 2 ^ b -> a = t * 2 ^ b + c ->
    N.log2 a = b + N.log2 t.
  Proof.
    intros t a b c Ht Hb (Hc,H) EQ.
    apply N.log2_unique.
    - nia.
    - rewrite EQ. split.
      + rewrite N.pow_add_r.
        assert (Htz : 0 < t). nia.
        pose proof (N.log2_spec t Htz) as Hze.
        nia.
      + rewrite N.pow_succ_r.
        rewrite N.pow_add_r.
        rewrite N.mul_assoc.
        assert (t + 1 <= 2 * 2 ^ N.log2 t).
        apply ulogt. exact Ht.
        nia. nia.
  Qed.

  (** One base-256 digit more: if [up = 256 · t + r] with [t ≥ 1] and
      [r < 256], then [log256 up = 1 + log256 t]. *)
  Lemma nlog256 : forall up t r, 1 <= t ->  r < 256 -> up = 256 * t + r ->
   log256 up =  1 + log256 t.
  Proof.
    intros ? ? ? Ht Hr Hup; unfold log256.
    assert (Htw : 256 = 2 ^ 8). reflexivity.
    assert (Hte : 0 <= 8). nia.
    assert (Hre : 0 <= r < 2^8). nia.
    assert (Hupn : up = t * 2^8 + r). nia.
    pose proof (log256_unique t up 8 r Ht Hte Hre Hupn).
    rewrite H.
    assert (Hs : (8 + N.log2 t) = (1 * 8 + N.log2 t))
      by nia.
    rewrite Hs. rewrite N.div_add_l.
    reflexivity. nia.
  Qed.

  (** Numbers below [256] have exactly one byte: [N.to_nat (⌊log₂ up⌋/8 + 1) = 1]. *)
  Lemma nlogle256 : forall up : N, up < 256 -> 1%nat = N.to_nat (N.log2 up / 8 + 1).
  Proof.
    intros ? Hup.
    assert (Hun : 256 = 2^8).
    reflexivity. rewrite Hun in Hup.
    clear Hun.
    assert (Hn : N.log2 up < 8).
    destruct up. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hup.
    assert (Htn : N.log2 up / 8 = 0).
    apply N.div_small. exact Hn.
    rewrite Htn. nia.
  Qed.

  (** Decidable comparison on [N]: [{n < m} + {m ≤ n}], with [Defined] so it
      computes. *)
  Lemma N_dec : forall n m : N, {n < m} + {m <= n}.
  Proof.
    intros [| n] [| m].
    + right; nia.
    + left; nia.
    + right; nia.
    + destruct (n <? m)%positive eqn:Ht.
      ++
      apply Pos.ltb_lt in Ht.
      left. abstract nia.
      ++
      apply Pos.ltb_ge in Ht.
      right. abstract nia.
  Defined.

  (** Characterisation of single-byte numbers: [up < 256] iff
      [N.to_nat (⌊log₂ up⌋ / 8) = 0]. *)
  Lemma nlog_le256 : forall up : N, up < 256 <-> 0%nat = N.to_nat (N.log2 up / 8).
  Proof.
    intros ?; split; intro Hup.
    assert (Hun : 256 = 2^8).
    reflexivity. rewrite Hun in Hup.
    clear Hun.
    assert (Hn : N.log2 up < 8).
    destruct up. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hup.
    assert (Htn : N.log2 up / 8 = 0).
    apply N.div_small. exact Hn.
    rewrite Htn. nia.
    (* Converse: if [up ≥ 256], write [up = 256 · t + r] with [t ≥ 1]; then
       [⌊log₂ up⌋ = 8 + ⌊log₂ t⌋] by [log256_unique], so the quotient by 8 is
       positive, a contradiction. *)
    assert(Hp : {up < 256} + {256 <= up}).
    apply N_dec. destruct Hp.
    exact l. remember (N.div up 256) as t.
    remember (N.modulo up 256) as r.
    assert (Hp: up = 256 * t + r).
    subst t; subst r. apply N.div_mod'.
    assert (Ht: 1 <= t). subst t.
    apply N.div_le_lower_bound.
    nia. simpl. exact l.
    assert (Hr : 0 <= r < 256).
    rewrite Heqr.
    eapply N.mod_bound_pos.
    nia. nia.
    assert (H256 : 256 = 2^8).
    reflexivity. rewrite H256 in Hr.
    assert (H8 : 0 <= 8). nia.
    pose proof (log256_unique t up 8 r Ht H8 Hr).
    rewrite N.mul_comm, H256 in Hp.
    specialize(H Hp). rewrite H in Hup.
    assert (H18: 8 = 1 * 8).
    reflexivity.
    rewrite H18 in Hup at 1.
    rewrite N.div_add_l in Hup.
    rewrite N2Nat.inj_add in Hup.
    simpl in Hup. inversion Hup.
    nia.
  Qed.

End Util.

(** ** Converting numbers to byte lists

    A natural number is written in base 256, least significant byte first.
    The recursion is driven by fuel [log256 np], which is exactly the number
    of digits minus one. *)
Section Fuel.

  (** [byte_list_from_N_fuel n up] emits [n + 1] little-endian base-256
      digits of [up]: the lowest byte [up mod 256] followed by the digits of
      [up / 256]. *)
  Fixpoint byte_list_from_N_fuel (n : nat) (up : N) : list byte :=
  match n with
  | 0%nat => [np_total (N.modulo up 256) (nmod_256_dec up)]
  | S n' =>
    let r := N.modulo up 256 in
    let t := N.div up 256 in
    List.cons (np_total r (nmod_256_dec up)) (byte_list_from_N_fuel n' t)
  end.

  (** Unfolding equation for one step of [byte_list_from_N_fuel]. *)
  Lemma byte_list_Sn : forall n np, byte_list_from_N_fuel (S n) np =
    List.cons (np_total (N.modulo np 256) (nmod_256_dec np)) (byte_list_from_N_fuel n (N.div np 256)).
  Proof.
    reflexivity.
  Qed.

  (** With fuel [n], exactly [n + 1] bytes are produced. *)
  Lemma fuel_byte_list_length_correctness : forall (n : nat) (np : N),
    List.length (byte_list_from_N_fuel n np) = (1 + n)%nat.
  Proof.
    induction n; simpl; intro np.
    + reflexivity.
    + f_equal. apply IHn.
  Qed.

  (** [byte_list_from_N np] is the minimal little-endian byte representation
      of [np] (one byte for [np < 256], and always at least one byte). *)
  Definition byte_list_from_N (np : N) :=
    byte_list_from_N_fuel (N.to_nat (log256 np)) np.

  (** [big_endien_list_N np] is the minimal big-endian byte representation of
      [np] (the reverse of [byte_list_from_N]).  It has no leading zero bytes,
      so it is not padded to a fixed width. *)
  Definition big_endien_list_N (np : N) :=
      List.rev (byte_list_from_N np).

  (** [byte_list_from_N np] has [1 + log256 np] bytes. *)
  Lemma byte_list_length_correctness : forall np, List.length (byte_list_from_N np) =
    (1 + N.to_nat (log256 np))%nat.
  Proof.
    intros ?. unfold byte_list_from_N.
    rewrite fuel_byte_list_length_correctness;
    reflexivity.
  Qed.

  (** [big_endien_list_N np] has [1 + log256 np] bytes. *)
  Lemma big_endien_list_correctness : forall np, List.length (big_endien_list_N np) =
    (1 + N.to_nat (log256 np))%nat.
  Proof.
    intros np. unfold big_endien_list_N.
    rewrite length_rev, byte_list_length_correctness;
    reflexivity.
  Qed.

  (** [horner_eval_byte_list l] reads a little-endian byte list as a number:
      [l₀ + 256 · (l₁ + 256 · (…))]. *)
  Fixpoint horner_eval_byte_list (l : list byte) :=
    match l with
    | List.nil => 0
    | List.cons h tl =>
          to_N h + 256 * horner_eval_byte_list tl
  end.

  (** Unfolding equation of [horner_eval_byte_list] on a cons. *)
  Lemma eval_byte_list_cons : forall h tl, horner_eval_byte_list (List.cons h tl) =
    to_N h + 256 * horner_eval_byte_list tl.
  Proof.
    reflexivity.
  Qed.

  (** The byte produced from [np mod 256] has numeric value [np mod 256]. *)
  Lemma np_mod_total : forall np, to_N (np_total (np mod 256) (nmod_256_dec np)) = np mod 256.
  Proof.
    intros ?; unfold np_total.
    generalize (of_N_None_iff (np mod 256)).
    generalize (np_total_subproof (np mod 256) (nmod_256_dec np)).
    intros; destruct (of_N (np mod 256)) eqn:Htn.
    ++ apply to_of_N; exact Htn.
    ++ apply of_N_None_iff in Htn.
       assert (Hn : np mod 256 < 256).
       apply nmod_256. nia.
  Qed.

  (** Correctness of the byte conversion:
      [horner_eval_byte_list (byte_list_from_N np) = np].  Induction on the
      fuel: in the step case [np ≥ 256], the fuel for [np / 256] is one less
      ([nlog256]), and [np = np mod 256 + 256 · (np / 256)]. *)
  Lemma byte_list_from_N_correct : forall np, horner_eval_byte_list (byte_list_from_N np) = np.
  Proof.
    intro np. unfold byte_list_from_N.
    remember (N.to_nat (log256 np)) as n.
    unfold log256 in Heqn. generalize dependent np.
    induction n.
    + simpl. intros ? Hn.
      apply nlog_le256 in Hn.
      unfold np_total.
      generalize (of_N_None_iff (np mod 256)).
      generalize (np_total_subproof (np mod 256) (nmod_256_dec np)).
      intros; destruct (of_N (np mod 256)) eqn:Htn.
      ++
        rewrite N.add_0_r.
        assert (Hnp : np mod 256 = np).
        apply N.mod_small; exact Hn.
        rewrite Hnp in Htn.
        apply to_of_N; exact Htn.
      ++
        assert (Hnp : np mod 256 = np).
        apply N.mod_small; exact Hn.
        rewrite Hnp in Htn.
        apply of_N_None_iff in Htn.
        nia.
    (* Step case: the case [np < 256] contradicts the positive fuel; otherwise
       apply the induction hypothesis to [np / 256]. *)
    + intros ? Hn. rewrite byte_list_Sn,
      eval_byte_list_cons.
      destruct ( N_dec np 256) as [Hnl |  Hnr].
      ++
        apply nlog_le256 in Hnl.
        rewrite <-Hnl in Hn. nia.
      ++
        specialize (IHn (N.div np 256)).
        assert (Hnp : np = 256 * (N.div np 256) + (N.modulo np 256)).
        apply N.div_mod. nia.
        assert (Hnt : 1 <= N.div np 256).
        apply N.div_le_lower_bound; nia.
        assert (Hnw : np mod 256 < 256).
        apply nmod_256.
        pose proof (nlog256 np _ _ Hnt Hnw Hnp).
        unfold log256 in H; rewrite H,  N2Nat.inj_add  in Hn;
        simpl in Hn. apply eq_add_S in Hn.
        specialize (IHn Hn). rewrite IHn.
        rewrite np_mod_total. nia.
  Qed.

End Fuel.

(** ** Byte conversion by well-founded recursion *)
Section Wellfounded.

  (** [byte_list_sig np] computes, by well-founded recursion on [np], a byte
      list [l] of length [log256 np + 1] whose little-endian value is [np].
      The specification is part of the result type.  This version
      is slow to evaluate because the proofs are part of the computation, and
      the rest of the file uses [byte_list_from_N] instead. *)
  Definition byte_list_sig (np : N) :  {l : list byte | List.length l = N.to_nat (log256 np + 1) ∧
    np = horner_eval_byte_list l}.
  Proof.
  induction (N_Lt_wf np) as [up Hacc IHuz].
  destruct (up <? 256) eqn:Hnp.
  + exists (List.cons (np_total up Hnp) List.nil).
    pose proof (proj1 (N.ltb_lt up 256) Hnp) as Ht.
    split.
    ++ abstract (simpl; apply nlogle256; exact Ht).
    ++ simpl. pose proof (np_true up Hnp).
      rewrite N.add_comm; simpl.
      destruct (of_N up) as [b | ] eqn:Hb.
      specialize(H b eq_refl); rewrite H.
      apply to_of_N_iff in Hb; intuition.
      apply of_N_None_iff in Hb; intuition.
      abstract nia.
  (* Case [up ≥ 256]: recurse on [t = up / 256 < up] and prepend the byte
     [r = up mod 256]. *)
  + pose proof (proj1 (N.ltb_ge up 256) Hnp) as Ht.
    refine(
      let r := N.modulo up 256 in
      let t := N.div up 256 in _ ).
    assert (Htt: t < up).
    abstract (unfold t;
      apply N.div_lt; nia).
    destruct (IHuz t Htt) as [lr Hlr].
    assert (Hr : r <? 256 = true).
    abstract (apply N.ltb_lt; unfold r;
    apply (nmod_256 up)).
    exists (List.cons (np_total r Hr) lr).
    split.
    ++
      simpl. assert (Hup: up = 256 * t + r).
      abstract (unfold t, r; rewrite <-N.div_mod with (b := 256);
      [reflexivity | nia]).
      rewrite nlog256 with (t := t) (r := r).
      abstract nia.
      assert (Hot: 1 <= t).
      abstract (unfold t;
      apply N.div_le_lower_bound; nia).
      exact Hot.
      apply N.ltb_lt in Hr. exact Hr.
      exact Hup.
    ++
      destruct Hlr as [Hlr1 Hlr2].
      rewrite eval_byte_list_cons, <-Hlr2.
      assert (Htn : to_N (np_total r Hr) = r).
      unfold np_total.
      generalize (of_N_None_iff r).
      destruct (of_N r) eqn:Hnr.
      intros. apply to_of_N_iff; exact Hnr.
      apply of_N_None_iff in Hnr.
      pose proof (proj1 (N.ltb_lt r 256) Hr).
      abstract nia. rewrite Htn; unfold r, t.
      rewrite N.add_comm.
      apply N.div_mod. abstract nia.
  Defined.

End Wellfounded.

(** ** SHA-256

    Words are 32-bit values represented as elements of [N] below [2^32].
    Addition and left shifts are truncated modulo [2^32]; right shifts and
    the bitwise operations cannot exceed 32 bits on such inputs. *)
Section Sha256.

  (** The word size [w = 32]. *)
  Definition word := 32.

  (** Addition modulo [2^32]. *)
  Definition add (x y : N) := (x + y) mod (2 ^ word).

  (** Left shift truncated to 32 bits: [(x << n) mod 2^32]. *)
  Definition shift_left (x n : N) := (N.shiftl x n) mod (2 ^ word).

  (** Logical right shift [x >> n]. *)
  Definition shift_right (x n : N) := N.shiftr x n.

  (** Bitwise and, or and xor on [N]. *)
  Definition bitwise_and (x y : N) := N.land x y.

  Definition bitwise_or (x y : N) := N.lor x y.

  Definition bitwise_xor (x y : N) := N.lxor x y.

  (** Bitwise complement of the low 32 bits ([N.lnot x 32]). *)
  Definition bitwise_neg (x : N) := N.lnot x word.

  (** Rotate left by [n] bits: [ROTL n x = (x << n) ∨ (x >> (32 - n))],
      as in FIPS 180-4 Section 3.2, for [0 ≤ n < 32]. *)
  Definition ROTL (n x : N) :=  bitwise_or (shift_left x n)
    (shift_right x (word - n)).

  (** Rotate right by [n] bits: [ROTR n x = (x >> n) ∨ (x << (32 - n))]. *)
  Definition ROTR (n x : N) :=  bitwise_or (shift_right x n)
    (shift_left x (word - n)).

  (** Right shift by [n] bits, [SHR n x = x >> n]. *)
  Definition SHR (n x : N) := shift_right x n.

  (** For [0 ≤ n < 32], [ROTL n x = ROTR (32 - n) x]. *)
  Lemma rotl_rotr : forall (x ml : N), 0 <= ml < word -> ROTL ml x = ROTR (word - ml) x.
  Proof.
    intros ? ? Hm.
    unfold ROTL, ROTR,
    bitwise_or, shift_left,
    shift_right.
    assert(H32: word - (word - ml) = ml) by nia.
    rewrite H32, N.lor_comm.
    reflexivity.
  Qed.

  (** For [0 ≤ n < 32], [ROTR n x = ROTL (32 - n) x]. *)
  Lemma rotr_rotl : forall (x ml : N), 0 <= ml < word -> ROTR ml x = ROTL (word - ml) x.
  Proof.
    intros ? ? Hm.
    unfold ROTL, ROTR,
    bitwise_or, shift_left,
    shift_right.
    assert(H32: word - (word - ml) = ml) by nia.
    rewrite H32, N.lor_comm.
    reflexivity.
  Qed.

  (** The choice function [Ch(x,y,z) = (x ∧ y) ⊕ (¬x ∧ z)] (FIPS 180-4,
      equation 4.2): each bit of [x] chooses between [y] and [z]. *)
  Definition Ch (x y z : N) := bitwise_xor (bitwise_and x y)
    (bitwise_and (bitwise_neg x) z).

  (** The majority function [Maj(x,y,z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)]. *)
  Definition Maj (x y z : N) := bitwise_xor (bitwise_xor (bitwise_and x y)
    (bitwise_and x z)) (bitwise_and y z).

  (** [Σ₀(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)], used on the working
      variable [a] in each round. *)
  Definition Sigma₀ (x : N) := bitwise_xor (bitwise_xor (ROTR 2 x)
    (ROTR 13 x)) (ROTR 22 x).

  (** [Σ₁(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)], used on [e]. *)
  Definition Sigma₁ (x : N) :=  bitwise_xor (bitwise_xor (ROTR 6 x)
    (ROTR 11 x)) (ROTR 25 x).

  (** [σ₀(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)], used in the message
      schedule. *)
  Definition sigma₀ x := bitwise_xor (bitwise_xor (ROTR 7 x)
    (ROTR 18 x)) (SHR 3 x).

  (** [σ₁(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)], used in the message
      schedule. *)
  Definition sigma₁ x := bitwise_xor (bitwise_xor (ROTR 17 x)
     (ROTR 19 x)) (SHR 10 x).

  (** The initial hash value [H⁽⁰⁾] (FIPS 180-4, Section 5.3.3): the first 32
      bits of the fractional parts of the square roots of the first eight
      primes. *)
  Definition H₀ : list N := [
    0x6a09e667; 0xbb67ae85; 0x3c6ef372; 0xa54ff53a; 0x510e527f;
    0x9b05688c; 0x1f83d9ab; 0x5be0cd19].

  (** The 64 round constants [K₀ … K₆₃] (FIPS 180-4, Section 4.2.2): the
      first 32 bits of the fractional parts of the cube roots of the first 64
      primes. *)
  Definition K : list N := [
    0x428a2f98; 0x71374491; 0xb5c0fbcf; 0xe9b5dba5; 0x3956c25b; 0x59f111f1; 0x923f82a4; 0xab1c5ed5;
    0xd807aa98; 0x12835b01; 0x243185be; 0x550c7dc3; 0x72be5d74; 0x80deb1fe; 0x9bdc06a7; 0xc19bf174;
    0xe49b69c1; 0xefbe4786; 0x0fc19dc6; 0x240ca1cc; 0x2de92c6f; 0x4a7484aa; 0x5cb0a9dc; 0x76f988da;
    0x983e5152; 0xa831c66d; 0xb00327c8; 0xbf597fc7; 0xc6e00bf3; 0xd5a79147; 0x06ca6351; 0x14292967;
    0x27b70a85; 0x2e1b2138; 0x4d2c6dfc; 0x53380d13; 0x650a7354; 0x766a0abb; 0x81c2c92e; 0x92722c85;
    0xa2bfe8a1; 0xa81a664b; 0xc24b8b70; 0xc76c51a3; 0xd192e819; 0xd6990624; 0xf40e3585; 0x106aa070;
    0x19a4c116; 0x1e376c08; 0x2748774c; 0x34b0bcb5; 0x391c0cb3; 0x4ed8aa4a; 0x5b9cca4f; 0x682e6ff3;
    0x748f82ee; 0x78a5636f; 0x84c87814; 0x8cc70208; 0x90befffa; 0xa4506ceb; 0xbef9a3f7; 0xc67178f2].

  (** *** Message preprocessing

      The rest of the section is parameterised by the message [m], a list of
      bytes.  [n] is its length in bytes, [mbits = 8n] its length in bits, and
      [Hn] requires [mbits < 2^64] as in the standard.  [k] is the number of
      zero bits appended after the single [1] bit, the least [k ≥ 0] with
      [mbits + 1 + k ≡ 448 (mod 512)]. *)
  Context (m : list byte).

  Let n := N.of_nat (List.length m).
  Let mbits := 8 * n.
  Context {Hn : mbits < 2^64}.
  Let k := Z.to_N (Z.modulo (448 - (Z.of_N mbits + 1)) 512).

  (** [get_zero_bytes v] is a list of [v] zero bytes. *)
  Fixpoint get_zero_bytes (v : nat) : list byte :=
  match v with
  | 0%nat => []
  | S v' => List.cons x00 (get_zero_bytes v')
  end.

  (** A list of zero bytes has value [0]. *)
  Lemma eval_zero_byte : forall v : nat, horner_eval_byte_list (get_zero_bytes v) = 0%N.
  Proof.
    induction v.
    + simpl; reflexivity.
    + simpl; rewrite IHv;
      reflexivity.
  Qed.

  (** [get_zero_bytes v] has length [v]. *)
  Lemma get_zero_bytes_len : forall v, List.length (get_zero_bytes v) = v%nat.
  Proof.
    induction v.
    + simpl; reflexivity.
    + simpl; rewrite IHv;
      reflexivity.
  Qed.

  (** [message_padding v] is the padding block of [v] bytes: the byte [0x80]
      (a [1] bit followed by seven [0] bits) followed by [v - 1] zero bytes;
      empty when [v = 0]. *)
  Definition message_padding (v : nat) : list byte :=
  match v with
  | 0%nat => []
  | S v' => List.cons x80 (get_zero_bytes v')
  end.

  (** Unfolding equation for nonempty padding. *)
  Lemma message_padding_app : forall v, message_padding (S v) = List.cons x80 (get_zero_bytes v).
  Proof.
    simpl; destruct v.
    + reflexivity.
    + simpl; reflexivity.
  Qed.

  (** [message_padding v] has length [v]. *)
  Lemma message_padding_length : forall v, List.length (message_padding v) = v.
  Proof.
    unfold message_padding.
    induction v.
    + simpl; reflexivity.
    + simpl; rewrite get_zero_bytes_len;
      reflexivity.
  Qed.

  (** Nonempty padding read little-endian has value [0x80]. *)
  Lemma message_padding_correct : forall v, (0 < v)%nat -> horner_eval_byte_list (message_padding v) = to_N x80.
  Proof.
    destruct v.
    + intro H; nia.
    + intros H. rewrite message_padding_app, eval_byte_list_cons,
      eval_zero_byte; nia.
  Qed.

  (** Since [mbits < 2^64], the bit length fits in at most 8 bytes. *)
  Lemma upper_bound_on_msg_len : (N.to_nat (log256 mbits + 1) <= 8)%nat.
  Proof.
    unfold log256; unfold mbits.
    assert (Hnt : N.log2 (8 * n) < 64).
    destruct n. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hn.
    assert (Hnw: N.log2 (8 * n) / 8 < 8).
    apply N.Div0.div_lt_upper_bound with (q := 8).
    exact Hnt.
    nia.
  Qed.

  (** [append_zero_in_length_byte lb] left-pads a big-endian byte list with
      zero bytes to 8 bytes (lists longer than 8 bytes are returned
      unchanged, which cannot happen here). *)
  Definition append_zero_in_length_byte (lb : list byte) : list byte :=
    let nl := List.length lb in
    if (nl <=? 8)%nat then get_zero_bytes (8 - nl) ++ lb
    else lb.

  (** The 64-bit big-endian encoding of the bit length [mbits]. *)
  Definition message_length_byte : list byte :=
    append_zero_in_length_byte (big_endien_list_N mbits).

  (** The length field is exactly 8 bytes long. *)
  Lemma message_length_byte_8 : (List.length message_length_byte = 8)%nat.
  Proof.
    unfold message_length_byte,
    append_zero_in_length_byte.
    assert (Ht: (List.length (big_endien_list_N mbits) <= 8)%nat).
    rewrite big_endien_list_correctness.
    unfold log256.
    assert (Hnt : N.log2 mbits < 64).
    destruct mbits. simpl. nia.
    apply N.log2_lt_pow2. nia.
    exact Hn.
    assert (Hwt: N.log2 mbits / 8 < 8).
    apply N.Div0.div_lt_upper_bound; nia.
    nia.
    apply Nat.leb_le in Ht.
    rewrite Ht.
    apply Nat.leb_le in Ht.
    rewrite length_app.
    rewrite get_zero_bytes_len.
    nia.
  Qed.

  (** [1 + Z.to_N a = Z.to_N (1 + a)] for [a ≥ 0]. *)
  Lemma push_N : forall a : Z, (0 <= a)%Z -> (1 + Z.to_N a) = Z.to_N (1 + a).
  Proof.
    intros. rewrite Z2N.inj_add.
    all: nia.
  Qed.

  (** [a mod b = a - b · (a / b)] for [b > 0]. *)
  Lemma mod_eq_custom : forall (a b : Z), (0 < b)%Z -> Z.modulo a b = (a - b * (a / b))%Z.
  Proof.
    intros a b Hb; rewrite Zmod_eq; nia.
  Qed.

  (** [k] is [7] modulo [8]: [k = 8w + 7] with
      [w = 55 - n - 64 · ⌊(447 - 8n)/512⌋ ≥ 0].  This holds because the message
      is a whole number of bytes, so the zero bits plus the leading [1] bit
      fill whole bytes. *)
  Lemma k_plus_gen : exists w : N, k =  8 * w + 7 /\
    (w = (Z.to_N (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))) /\
    (0 <= (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))%Z.
  Proof.
    unfold k, mbits.
    assert (H: (448 - (Z.of_N (8 * n) + 1))%Z = (447 - (Z.of_N (8 * n)))%Z).
    nia. rewrite H.
    assert (Hp : (0 <= (447 - Z.of_N (8 * n)) mod 512 < 512)%Z).
    apply Z.mod_pos_bound; nia.
    rewrite mod_eq_custom.
    assert (Ht: (447 - Z.of_N (8 * n) - 512 * ((447 - Z.of_N (8 * n)) / 512))%Z =
        (8 * (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)) + 7)%Z).
    nia. rewrite Ht.
    exists (Z.to_N (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512))).
    rewrite mod_eq_custom in Hp.
    all:nia.
  Qed.

  (** Consequently [1 + k = 8(w + 1)]. *)
  Lemma k_plus_gen_one : exists w : N, 1 + k = 8 * (w + 1) /\
    (w = (Z.to_N (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))) /\
    (0 <= (55 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)))%Z.
  Proof.
    destruct k_plus_gen as [x [Hx H]].
    exists x. rewrite Hx. nia.
  Qed.

  (** [8 ∣ 1 + k]. *)
  Lemma k_plus_one_div_8 : N.modulo (1 + k) 8 = 0.
  Proof.
    destruct k_plus_gen as [x [H1 H2]].
    assert (Ht : 1 + (8 * x + 7) =  (x + 1) * 8).
    nia. rewrite H1, Ht.
    rewrite N.Div0.mod_mul.
    reflexivity.
  Qed.

  (** [wt = (1 + k) / 8] is the number of padding bytes, including the
      leading [0x80] byte. *)
  Let wt := N.div (1 + k) 8.

  (** Closed form of [wt], and [wt > 0] (there is always at least the
      [0x80] byte). *)
  Lemma wt_exact_val : wt = Z.to_N (56 - Z.of_N n - 64 * ((447 - Z.of_N (8 * n)) / 512)) /\
    (0 < wt).
  Proof.
    destruct k_plus_gen_one as [x [Hx [Hy Hz]]].
    assert (wt = x + 1). unfold wt.
    rewrite Hx. rewrite N.mul_comm, N.div_mul.
    reflexivity. nia.
    rewrite H, Hy.
    nia.
  Qed.

  (** The padded length [n + wt + 8] is a positive multiple of 64 bytes, in
      closed form. *)
  Lemma sha_64_byte : n + wt + 8 = 64 * Z.to_N (1 -  ((447 - Z.of_N (8 * n)) / 512)) ∧
    (0 < (64 - 64 * ((447 - Z.of_N (8 * n)) / 512)))%Z.
  Proof.
    destruct wt_exact_val as [H1 H2].
    nia.
  Qed.

  (** The padded message length is divisible by 64 bytes (512 bits). *)
  Lemma div_64 : N.modulo (n +  wt + 8) 64 = 0.
  Proof.
    destruct sha_64_byte as [H1 H2].
    rewrite H1, N.mul_comm, N.Div0.mod_mul.
    reflexivity.
  Qed.

  (** [ms] is the number of 512-bit blocks of the padded message. *)
  Let ms := N.div (n + wt + 8) 64.

  (** The padded message [m ‖ 0x80 ‖ 0…0 ‖ len₆₄(m)] of FIPS 180-4
      Section 5.1.1. *)
  Definition prepared_message : list byte :=
    m ++ message_padding (N.to_nat wt) ++ message_length_byte.

  (** The padded message has [n + wt + 8] bytes. *)
  Lemma prepared_message_correctness : List.length prepared_message = N.to_nat (n + wt + 8).
  Proof.
    unfold prepared_message.
    repeat rewrite length_app.
    rewrite message_padding_length,
    message_length_byte_8.
    nia.
  Qed.

  (** Reads four bytes [a b c d] as a big-endian 32-bit word. *)
  Definition big_endien_32_bit_to_N (a b c d : byte) : N :=
    ((to_N a * 256 + to_N b) * 256 + to_N c) * 256 + to_N d.

  (** [M i j] is the [j]-th 32-bit word ([0 ≤ j < 16]) of the [i]-th
      512-bit block of the padded message, written [M_j⁽ⁱ⁾] in FIPS 180-4. *)
  Definition M (i j : nat) : N := big_endien_32_bit_to_N
    (nth (64 * i + 4 * j) prepared_message x00)
    (nth (64 * i + 4 * j + 1) prepared_message x00)
    (nth (64 * i + 4 * j + 2) prepared_message x00)
    (nth (64 * i + 4 * j + 3) prepared_message x00).

  (** [from_n n] is [[n-1; …; 1; 0]]. *)
  Fixpoint from_n (n : nat) :=
    match n with
    | 0%nat => []
    | S n' => n' :: (from_n n')
    end.

  (** [upto_n n] is [[0; 1; …; n-1]], used as the iteration range of folds. *)
  Definition upto_n (n : nat) := List.rev (from_n n).

  (** The message schedule for block [i] (FIPS 180-4, Section 6.2.2, step 1):
      [W_t = M_t⁽ⁱ⁾] for [t < 16] and
      [W_t = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}] for
      [16 ≤ t < 64], all modulo [2^32].  The list is built left to right
      by appending, so it is quadratic in [64], which is negligible. *)
  Definition W (i : nat) : list N :=
    List.fold_left
    (fun (acc : list N) (t : nat) =>
      let wtp :=
        if (t <? 16)%nat then M i t
        else
          let a := nth (t - 2) acc 0 in
          let b := nth (t - 7) acc 0 in
          let c := nth (t - 15) acc 0 in
          let d := nth (t - 16) acc 0 in
          add (add (add (sigma₁ a) b) (sigma₀ c)) d
      in acc ++ [wtp]) (upto_n 64) [].

  (** The SHA-256 compression function: given the message schedule [W] of
      one block and the current hash value [H] (eight words), run the 64
      rounds on the working variables [a, …, h] with
      [T₁ = h + Σ₁(e) + Ch(e,f,g) + K_t + W_t] and [T₂ = Σ₀(a) + Maj(a,b,c)],
      then add the result to [H] word by word. *)
  Definition sha256_intermediate (W : list N) (H : list N) : list N :=
    let a := nth 0 H 0 in
    let b := nth 1 H 0 in
    let c := nth 2 H 0 in
    let d := nth 3 H 0 in
    let e := nth 4 H 0 in
    let f := nth 5 H 0 in
    let g := nth 6 H 0 in
    let h := nth 7 H 0 in
    let '(a, b, c, d, e, f, g, h) :=
    List.fold_left
    (fun '(a, b, c, d, e, f, g, h) t =>
      let T₁ := add (add (add (add h (Sigma₁ e)) (Ch e f g)) (nth t K 0)) (nth t W 0) in
      let T₂ := add (Sigma₀ a) (Maj a b c) in
      let h := g in
      let g := f in
      let f := e in
      let e := add d T₁ in
      let d := c in
      let c := b in
      let b := a in
      let a := add T₁ T₂ in
      (a, b, c, d, e, f, g, h)) (upto_n 64) (a, b, c, d, e, f, g, h)
    in
    [add a (nth 0 H 0); add b (nth 1 H 0); add c (nth 2 H 0);
    add d (nth 3 H 0); add e (nth 4 H 0); add f (nth 5 H 0);
    add g (nth 6 H 0); add h (nth 7 H 0)].

  (** The SHA-256 hash of [m] as a list of eight 32-bit words: the
      compression function folded over the [ms] blocks, starting from [H₀]. *)
  Definition sha256 :=
    List.fold_left
    (fun H i => sha256_intermediate (W i) H)
    (upto_n (N.to_nat ms)) H₀.

End Sha256.

From Stdlib Require Import String Ascii.

(** ** String interface and test vectors *)

(** [concat_bytes bs] reads a big-endian byte list as a natural number. *)
Definition concat_bytes (bs : list byte) : N :=
    List.fold_left (fun acc b => acc * (N.shiftl 1 8) + to_N b) bs 0.

(** [sha256_string s] hashes the bytes of the string [s] and returns the
    256-bit digest as a single number.  Each output word is serialised with
    [big_endien_list_N], which drops leading zero bytes.  The result is
    therefore the standard digest only when no output word starts with a
    zero byte, which is the case for the test vectors below. *)
Definition sha256_string (s : string) :=
  concat_bytes (List.flat_map big_endien_list_N (sha256 (list_byte_of_string s))).

(** Test vector: SHA-256 of ‘abc’ (FIPS 180-2, Appendix B.1), checked by
    [vm_compute]. *)
Lemma sha256_1st : sha256_string "abc" =
  0xba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad.
Proof.
 Time vm_compute; reflexivity.
Qed.

(** Test vector: SHA-256 of the empty string. *)
Lemma sha256_2nd : sha256_string "" =
  0xe3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.
Proof.
  Time vm_compute; reflexivity.
Qed.

(** Test vector: the 448-bit two-block message
    ‘abcdbcde…nopq’ (FIPS 180-2, Appendix B.2). *)
Lemma sha256_3rd : sha256_string  "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" =
  0x248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1.
Proof.
  Time vm_compute; reflexivity.
Qed.

(** Test vector: the 896-bit message ‘abcdefgh…nopqrstu’ (the 896-bit
    test of FIPS 180-4 examples / RFC 6234). *)
Lemma sha256_4th : sha256_string ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghij" ++
 "klmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu") =
  0xcf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1.
Proof.
  Time vm_compute; reflexivity.
Qed.
