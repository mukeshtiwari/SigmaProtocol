(** A constant-time variant [scalarmult_ct] of the double-and-add scalar
    multiplication [scalarmult] of [ScalarMult], with the same
    specification and the same top-level theorem against [Ed.gpow_fast].

    The loop body [step_ct] doubles the accumulator into a scratch buffer
    [p_t], always adds the base point into a second scratch buffer [p_s],
    and then selects [p_t] or [p_s] into the accumulator with [cmov], a
    word-wise masked selection over the 25 words of an extended point:
    with [mask = 0 - b] each output word is [x ^ ((x ^ y) & mask)], which
    is [x] for [b = 0] and [y] for [b = 1].

    Constant time, as a syntactic property of the programs below: the
    scalar bit [b] enters [step_ct] and [cmov] only as an operand of
    arithmetic ([0 - b], [&], [^]); no [if] or [while] condition and no
    load or store address depends on it. The loop counts of [cmov] (25)
    and of [scalarmult_ct] (256) are constants, and the bit is read from
    the public address [p_k + (i >> 3)], where [i] is the loop counter.
    [double] and [add] are AUCurves' and [ToCached2]'s straight-line
    field code. No leakage-trace semantics is used; the theorems below are
    functional correctness only. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Crypto.Algebra.Field.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Word.LittleEndianList.
Require Import coqutil.Tactics.letexists coqutil.Tactics.ident_of_string.
From Stdlib Require Import Zmod.
Require Fiat.Algebra.ScalarMult.
Require Import Bridge.FieldTransport Bridge.ExecReadd Bridge.ExecDouble Bridge.ToCached2.
Require Import Bridge.ScalarMult.
Import ProgramLogic.Coercions ListNotations.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.
Module SM := Fiat.Algebra.ScalarMult.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* The notations of [ScalarMult] (module-local there), restated. *)
Local Notation word := (Naive.word 64).
Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
Local Notation bounded_by := (bounded_by(FieldRepresentation:=frep25519)).
Local Notation felem_size := 40.
Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).
Local Notation "p .+ n" := (word.add p (word.of_Z n)) (at level 50, format "p .+ n", left associativity).
Local Notation "c 'p5@' p" := (let '(X,Y,Z,Ta,Tb) := proj1_sig c in sep (sep (sep (sep
                              (FElem (p) X)
                              (FElem (p .+ felem_size) Y))
                              (FElem (p .+ (felem_size + felem_size)) Z))
                              (FElem (p .+ (felem_size + felem_size + felem_size)) Ta))
                              (FElem (p .+ (felem_size + felem_size + felem_size + felem_size)) Tb))
                              (at level 10, format "c 'p5@' p").
Local Notation Fd := Crypto.Spec.Curve25519.E.d.

Local Ltac ecancel_assumption_fast :=
  multimatch goal with
  | |- _ ?m1 =>
    multimatch goal with
    | H: _ ?m2 |- _ =>
      syntactic_unify_deltavar m1 m2;
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ H); clear H;
      solve [ecancel]
    end
  end.
Local Ltac ecancel_assumption ::= first [ecancel_assumption_fast | ecancel_assumption_impl].

Module ZL := Curve.Ed25519.Ed25519.Zl.
Local Notation smul := (@SM.scalarmult_ref SP.point SP.padd SP.pzero SP.popp).

(** ** Masked selection of words *)

(** [sel mask x y] is [x] for [mask = 0] and [y] for [mask = -1]. *)
Definition sel (mask x y : word) : word := word.xor x (word.and (word.xor x y) mask).

Fixpoint sel_list (mask : word) (xs ys : list word) : list word :=
  match xs, ys with
  | x :: xs', y :: ys' => sel mask x y :: sel_list mask xs' ys'
  | _, _ => []
  end.

(** The mask of a bit. *)
Definition bit_mask (bit : bool) : word := word.sub (word.of_Z 0) (word.of_Z (Z.b2z bit)).

Lemma testbit_high (w : word) (n : Z) : 64 <= n -> Z.testbit (word.unsigned w) n = false.
Proof.
  intro h; pose proof (Properties.word.unsigned_range w) as hr.
  rewrite <-(Z.mod_small (word.unsigned w) (2 ^ 64)) by exact hr.
  apply Z.mod_pow2_bits_high; lia.
Qed.

Lemma sel_bit (bit : bool) (x y : word) : sel (bit_mask bit) x y = if bit then y else x.
Proof.
  apply Properties.word.unsigned_inj; cbv [sel bit_mask].
  rewrite !Properties.word.unsigned_xor_nowrap, Properties.word.unsigned_and_nowrap,
    Properties.word.unsigned_xor_nowrap.
  destruct bit; cbn [Z.b2z].
  - change (word.unsigned (word.sub (word.of_Z 0) (word.of_Z 1) : word)) with (Z.ones 64).
    apply Z.bits_inj'; intros n hn.
    rewrite !Z.lxor_spec, Z.land_spec, Z.lxor_spec, Z.testbit_ones by lia.
    destruct (Z.ltb_spec n 64) as [h | h].
    + rewrite (proj2 (Z.leb_le 0 n) hn); cbn [andb].
      destruct (Z.testbit (word.unsigned x) n), (Z.testbit (word.unsigned y) n); reflexivity.
    + rewrite !testbit_high by exact h.
      rewrite Bool.andb_false_r; reflexivity.
  - change (word.unsigned (word.sub (word.of_Z 0) (word.of_Z 0) : word)) with 0.
    rewrite Z.land_0_r, Z.lxor_0_r; reflexivity.
Qed.

Lemma sel_list_bit (bit : bool) (xs ys : list word) :
  Datatypes.length xs = Datatypes.length ys ->
  sel_list (bit_mask bit) xs ys = if bit then ys else xs.
Proof.
  revert ys; induction xs as [| x xs ih]; intros [| y ys] hl; cbn [Datatypes.length] in hl;
    try discriminate.
  - destruct bit; reflexivity.
  - cbn [sel_list]; rewrite sel_bit, ih by lia; destruct bit; reflexivity.
Qed.

(** ** Extended points as arrays of 25 words *)

Definition p5w (c : B.projective_coords) : list word :=
  let '(X, Y, Z, Ta, Tb) := proj1_sig c in
  proj1_sig X ++ proj1_sig Y ++ proj1_sig Z ++ proj1_sig Ta ++ proj1_sig Tb.

Lemma felem_words (x : felem) : Datatypes.length (proj1_sig x) = 5%nat.
Proof. exact (proj2_sig x). Qed.

Lemma p5w_length (c : B.projective_coords) : Datatypes.length (p5w c) = 25%nat.
Proof.
  destruct c as [[[[[X Y] Z] Ta] Tb] hc]; cbn [p5w proj1_sig].
  rewrite !length_app, !felem_words; reflexivity.
Qed.

Lemma array_app_w (p q : word) (xs ys : list word) :
  Datatypes.length xs = 5%nat -> q = p .+ 40 ->
  Lift1Prop.iff1 (array scalar (word.of_Z 8) p (xs ++ ys))
                 (sep (array scalar (word.of_Z 8) p xs) (array scalar (word.of_Z 8) q ys)).
Proof.
  intros hl hq; subst q.
  etransitivity; [apply Array.array_append |].
  rewrite hl.
  replace (word.add p (word.of_Z (word.unsigned (word.of_Z 8 : word) * Z.of_nat 5)))
    with (p .+ 40) by ZnWords.
  reflexivity.
Qed.

Lemma felem_array (p : word) (x : felem) :
  Lift1Prop.iff1 (FElem p x) (array scalar (word.of_Z 8) p (proj1_sig x)).
Proof. reflexivity. Qed.

(** The memory of an extended point is the array of its 25 words. *)
Lemma p5_words (c : B.projective_coords) (p : word) :
  Lift1Prop.iff1 (c p5@ p) (array scalar (word.of_Z 8) p (p5w c)).
Proof.
  destruct c as [[[[[X Y] Z] Ta] Tb] hc]; cbn [p5w proj1_sig].
  rewrite (array_app_w p (p .+ felem_size) _ _ (felem_words X) eq_refl).
  rewrite (array_app_w (p .+ felem_size) (p .+ (felem_size + felem_size)) _ _ (felem_words Y)
             (add_40_40 p 40)).
  rewrite (array_app_w (p .+ (felem_size + felem_size)) (p .+ (felem_size + felem_size + felem_size))
             _ _ (felem_words Z) (add_40_40 p (40 + 40))).
  rewrite (array_app_w (p .+ (felem_size + felem_size + felem_size))
             (p .+ (felem_size + felem_size + felem_size + felem_size))
             _ _ (felem_words Ta) (add_40_40 p (40 + 40 + 40))).
  rewrite !felem_array.
  cancel.
Qed.

Lemma p5_words_r (c : B.projective_coords) (p : word) :
  Lift1Prop.iff1 (array scalar (word.of_Z 8) p (p5w c)) (c p5@ p).
Proof. symmetry; apply p5_words. Qed.

(** ** [cmov]: constant-time conditional copy of an extended point

    [cmov(p_o, p_x, p_y, b)] writes at [p_o] the point at [p_x] if [b = 0]
    and the point at [p_y] if [b = 1], word by word through the mask
    [0 - b]; every word of both inputs is read and every word of the
    output is written, whatever [b] is. *)

Definition cmov := func! (p_o, p_x, p_y, b) {
  mask = $0 - b;
  n = $25;
  w = $0;
  while n {
    w = load(p_x);
    store(p_o, w ^ ((w ^ load(p_y)) & mask));
    p_o = p_o + $8;
    p_x = p_x + $8;
    p_y = p_y + $8;
    n = n - $1
  }
}.

Global Instance spec_of_cmov : spec_of "cmov" :=
  fnspec! "cmov"
    (p_o p_x p_y b : word) / (bit : bool) (o x y : B.projective_coords) (R : _ -> Prop), {
      requires t m :=
        m =* o p5@ p_o * x p5@ p_x * y p5@ p_y * R /\
        b = word.of_Z (Z.b2z bit);
      ensures t' m' :=
        t = t' /\
        m' =* (if bit then y else x) p5@ p_o * x p5@ p_x * y p5@ p_y * R
  }.

(* [straightline], with variable lookups in the locals map done by
   computation; [straightline]'s own lookup makes no progress on the
   locals of the [cmov] loop body. *)
Local Ltac sl :=
  lazymatch goal with
  | |- WeakestPrecondition.get _ _ _ =>
      cbv beta delta [WeakestPrecondition.get]; eexists; split; [exact eq_refl | cbv beta]
  | |- WeakestPrecondition.cmd _ (cmd.set ?s ?e) _ _ _ ?post =>
      unfold1_cmd_goal; cbv beta match delta [cmd_body];
      ident_of_constr_string_cps s ltac:(fun x =>
        ensure_free x; letexists _ as x; split; [solve [repeat sl] |])
  | |- _ => straightline
  end.

(** The loop invariant, for [v] words left: the three pointers address
    word arrays [os], [xs], [ys] of length [v] and [n] holds [v]; on exit
    the array at the initial [p_o] is [sel_list mask xs ys]. The frame is a
    loop variable, so that the words already processed move into it. *)
Lemma cmov_ok : program_logic_goal_for_function! cmov.
Proof.
  repeat straightline.
  lazymatch goal with Hm : _ m |- _ =>
    seprewrite_in (p5_words o p_o) Hm; seprewrite_in (p5_words x p_x) Hm;
    seprewrite_in (p5_words y p_y) Hm end.
  refine ((Loops.tailrec
    (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _
      (HList.polymorphic_list.cons _ (HList.polymorphic_list.cons _
        HList.polymorphic_list.nil))))
    ("p_o" :: "p_x" :: "p_y" :: "b" :: "mask" :: "n" :: "w" :: nil)%list
    (fun (v : nat) (os xs ys : list word) Rf t' m' p_o' p_x' p_y' b' mask' n' w' =>
     PrimitivePair.pair.mk
      (m' =* array scalar (word.of_Z 8) p_o' os * array scalar (word.of_Z 8) p_x' xs *
             array scalar (word.of_Z 8) p_y' ys * Rf /\
       Datatypes.length os = v /\ Datatypes.length xs = v /\ Datatypes.length ys = v /\
       word.unsigned n' = Z.of_nat v /\ t' = t)
      (fun t'' m'' _ _ _ _ _ _ _ => t'' = t /\
        m'' =* array scalar (word.of_Z 8) p_o' (sel_list mask' xs ys) *
               array scalar (word.of_Z 8) p_x' xs * array scalar (word.of_Z 8) p_y' ys * Rf))
    lt _ 25%nat (p5w o) (p5w x) (p5w y) R _ _ _));
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  { repeat straightline. }
  { exact lt_wf. }
  { ssplit; try reflexivity; try ecancel_assumption; apply p5w_length. }
  { intros v os xs ys Rf t' m' p_o' p_x' p_y' b' mask' n' w'.
    clear dependent p_o; clear dependent p_x; clear dependent p_y; clear dependent b;
      clear dependent n; clear dependent w.
    repeat straightline.
    - destruct v as [| v]; [cbn [Z.of_nat] in *; lia |].
      destruct os as [| o0 os]; [discriminate |].
      destruct xs as [| x0 xs]; [discriminate |].
      destruct ys as [| y0 ys]; [discriminate |].
      cbn [Datatypes.length array] in *.
      repeat (lazymatch goal with |- Markers.unique _ => fail | _ => sl end).
      cbv [Markers.unique Markers.left Markers.split Markers.right].
      exists p_o, p_x, p_y, b', mask', n, x0.
      split; [exact (conj eq_refl eq_refl) |].
      subst p_o p_x p_y n v0.
      exists os, xs, ys, (sep (sep (scalar p_o' (sel mask' x0 y0)) (scalar p_x' x0))
                            (sep (scalar p_y' y0) Rf)), v.
      split.
      { ssplit; try lia; try reflexivity.
        - cbv [sel]; ecancel_assumption.
        - rewrite Properties.word.unsigned_sub_nowrap; rewrite ?Properties.word.unsigned_of_Z_1; lia. }
      split; [lia |].
      intros T M ? ? ? ? ? ? ? [HT HM]; split; [exact HT |].
      cbn [sel_list array]; ecancel_assumption.
    - assert (Hl : (Datatypes.length os = 0 /\ Datatypes.length xs = 0 /\
                      Datatypes.length ys = 0)%nat) by lia.
      destruct Hl as (Ho & Hx & Hy).
      apply length_zero_iff_nil in Ho, Hx, Hy; subst os xs ys.
      cbn [sel_list array] in *.
      ecancel_assumption. }
  { intros t0 m0 ? ? ? ? ? ? ? [Ht Hm'].
    cbn [PrimitivePair.pair._1 PrimitivePair.pair._2] in Hm'.
    cbv beta match fix delta [WeakestPrecondition.list_map WeakestPrecondition.list_map_body].
    split; [reflexivity |]. split; [symmetry; exact Ht |].
    replace mask with (bit_mask bit) in Hm' by reflexivity.
    rewrite sel_list_bit in Hm' by (rewrite !p5w_length; reflexivity).
    replace (if bit then p5w y else p5w x) with (p5w (if bit then y else x)) in Hm'
      by (destruct bit; reflexivity).
    seprewrite_in (p5_words_r (if bit then y else x) p_o) Hm'.
    seprewrite_in (p5_words_r x p_x) Hm'.
    seprewrite_in (p5_words_r y p_y) Hm'.
    ecancel_assumption. }
Qed.

(** ** [step_ct]: one constant-time iteration of double-and-add

    The accumulator at [p_acc] is doubled into [p_t], the base point at
    [p_P] is added to the double into [p_s], and [cmov] copies [p_t]
    ([b = 0]) or [p_s] ([b = 1]) back into [p_acc]. The same calls run on
    the same addresses for both values of [b]. *)

Definition step_ct := func! (p_acc, p_t, p_s, p_P, p_d, b) {
  double(p_t, p_acc);
  add(p_s, p_t, p_P, p_d);
  cmov(p_acc, p_t, p_s, b)
}.

#[local] Existing Instance spec_of_double_p5 | 0.

Global Instance spec_of_step_ct : spec_of "step_ct" :=
  fnspec! "step_ct"
    (p_acc p_t p_s p_P p_d b: word) /
    (bit : bool) (A P : SP.xpoint) (a pP: B.projective_coords) (d2: felem)
    (tb sb : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* a p5@ p_acc * tb $@ p_t * sb $@ p_s * pP p5@ p_P * FElem p_d d2 * R /\
        Datatypes.length tb = Z.to_nat (5 * felem_size) /\
        Datatypes.length sb = Z.to_nat (5 * felem_size) /\
        b = word.of_Z (Z.b2z bit) /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2 /\
        B.feval_projective_coords a = phi5 (proj1_sig A) /\
        B.feval_projective_coords pP = phi5 (proj1_sig P);
      ensures t' m' :=
        t = t' /\
        exists (a' : B.projective_coords) (tb' sb' : list byte) (A' : SP.xpoint),
          m' =* a' p5@ p_acc * tb' $@ p_t * sb' $@ p_s * pP p5@ p_P * FElem p_d d2 * R /\
          Datatypes.length tb' = Z.to_nat (5 * felem_size) /\
          Datatypes.length sb' = Z.to_nat (5 * felem_size) /\
          B.feval_projective_coords a' = phi5 (proj1_sig A') /\
          SP.to_affine A' = dbl_add bit (SP.to_affine A) (SP.to_affine P)
  }.

Lemma step_ct_ok : program_logic_goal_for_function! step_ct.
Proof.
  repeat straightline.
  straightline_call; ssplit; try ecancel_assumption; try eassumption.
  repeat straightline.
  straightline_call; ssplit; try ecancel_assumption; try eassumption.
  repeat straightline.
  straightline_call; ssplit; try ecancel_assumption; try eassumption; try reflexivity.
  repeat straightline.
  lazymatch goal with
  | Hd : ScalarMult.B.feval_projective_coords ?d = phi5 (proj1_sig (SP.xdouble A)),
    Hs : ToCached2.B.feval_projective_coords ?s = phi5 (proj1_sig ?S),
    Haff : SP.to_affine ?S = SP.padd (SP.to_affine (SP.xdouble A)) (SP.to_affine P),
    Hm : _ ?m |- exists _ _ _ _, _ ?m /\ _ =>
      assert (Hm1 : sep (d p5@ p_t) (sep (sep (sep (sep ((if bit then s else d) p5@ p_acc)
                      (s p5@ p_s)) (pP p5@ p_P)) (FElem p_d d2)) R) m)
        by ecancel_assumption;
      destruct (p5_to_bytes _ _ _ _ Hm1) as (tb' & hlt & Hm2);
      assert (Hm3 : sep (s p5@ p_s) (sep (sep (sep (sep ((if bit then s else d) p5@ p_acc)
                      (tb' $@ p_t)) (pP p5@ p_P)) (FElem p_d d2)) R) m)
        by ecancel_assumption;
      destruct (p5_to_bytes _ _ _ _ Hm3) as (sb' & hls & Hm4);
      exists (if bit then s else d), tb', sb', (if bit then S else SP.xdouble A); ssplit;
        [ ecancel_assumption | rewrite hlt; reflexivity | rewrite hls; reflexivity
        | destruct bit; assumption
        | destruct bit; cbn [dbl_add]; rewrite ?Haff, SP.to_affine_xdouble; reflexivity ]
  end.
Qed.

(** ** [scalarmult_ct]: the loop over the 256 bits of the scalar

    As [scalarmult], with [step_ct] in place of [step] and a second
    200-byte scratch buffer [p_s]. *)

Definition scalarmult_ct := func! (p_out, p_P, p_k, p_d) {
  stackalloc 200 as p_t;
  stackalloc 200 as p_s;
  set_identity(p_out);
  b = $0;
  i = $256;
  while ($0 < i) {
    i = i - $1;
    b = (load1(p_k + (i >> $3)) >> (i & $7)) & $1;
    step_ct(p_out, p_t, p_s, p_P, p_d, b)
  }
}.

Global Instance spec_of_scalarmult_ct : spec_of "scalarmult_ct" :=
  fnspec! "scalarmult_ct"
    (p_out p_P p_k p_d: word) /
    (P : SP.xpoint) (pP : B.projective_coords) (d2 : felem) (kb out : list byte)
    (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        Datatypes.length kb = 32%nat /\
        F.add Fd Fd = feval d2 /\
        bounded_by tight_bounds d2 /\
        B.feval_projective_coords pP = phi5 (proj1_sig P);
      ensures t' m' :=
        t = t' /\
        exists (a : B.projective_coords) (A : SP.xpoint),
          m' =* a p5@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
          B.feval_projective_coords a = phi5 (proj1_sig A) /\
          SP.to_affine A = smul (le_combine kb) (SP.to_affine P)
  }.

Lemma scalarmult_ct_ok : program_logic_goal_for_function! scalarmult_ct.
Proof.
  repeat straightline.
  straightline_call; ssplit; try ecancel_assumption; try eassumption.
  repeat straightline.
  rename a into p_t, a0 into p_s, a1 into t0.
  refine ((Loops.tailrec HList.polymorphic_list.nil
    ("p_out" :: "p_P" :: "p_k" :: "p_d" :: "p_t" :: "p_s" :: "b" :: "i" :: nil)%list
    (fun (v : nat) t' m' p_out' p_P' p_k' p_d' p_t' p_s' b' i' => PrimitivePair.pair.mk
      (word.unsigned i' = Z.of_nat v /\ (v <= 256)%nat /\ p_out' = p_out /\ p_P' = p_P /\
       p_k' = p_k /\ p_d' = p_d /\ p_t' = p_t /\ p_s' = p_s /\ t' = t0 /\
       exists (acc : B.projective_coords) (tb sb : list byte) (A : SP.xpoint),
         m' =* acc p5@ p_out * tb $@ p_t * sb $@ p_s * pP p5@ p_P * kb $@ p_k *
               FElem p_d d2 * R /\
         Datatypes.length tb = 200%nat /\ Datatypes.length sb = 200%nat /\
         B.feval_projective_coords acc = phi5 (proj1_sig A) /\
         SP.to_affine A = smul (Z.shiftr (le_combine kb) (Z.of_nat v)) (SP.to_affine P))
      (fun t'' m'' _ _ _ _ _ _ _ _ => t'' = t0 /\
       exists (acc : B.projective_coords) (tb sb : list byte) (A : SP.xpoint),
         m'' =* acc p5@ p_out * tb $@ p_t * sb $@ p_s * pP p5@ p_P * kb $@ p_k *
                FElem p_d d2 * R /\
         Datatypes.length tb = 200%nat /\ Datatypes.length sb = 200%nat /\
         B.feval_projective_coords acc = phi5 (proj1_sig A) /\
         SP.to_affine A = smul (le_combine kb) (SP.to_affine P)))
    lt _ 256%nat _ _ _));
    cbn [HList.hlist.foralls HList.tuple.foralls
         HList.hlist.existss HList.tuple.existss
         HList.hlist.apply  HList.tuple.apply
         HList.hlist
         List.repeat Datatypes.length
         HList.polymorphic_list.repeat HList.polymorphic_list.length
         PrimitivePair.pair._1 PrimitivePair.pair._2] in *.
  { repeat straightline. }
  { exact lt_wf. }
  { (* initialisation *)
    cbn [PrimitivePair.pair._1 PrimitivePair.pair._2 HList.tuple.apply] in *.
    match goal with
    | Hx : B.feval_projective_coords ?x0 = phi5 (proj1_sig (SP.from_affine SP.pzero)),
      Hm : ?Pm ?mm |- _ =>
      lazymatch Pm with context [array ptsto _ p_t stack] => idtac end;
      subst i; ssplit; try reflexivity; try lia;
      exists x0, stack, stack0, (SP.from_affine SP.pzero); ssplit;
      [ assert (Hm2 : sep (stack $@ p_t) (sep (x0 p5@ p_out) (sep (pP p5@ p_P)
                  (sep (kb $@ p_k) (sep (FElem p_d d2)
                  (sep R (array ptsto (word.of_Z 1) p_s stack0)))))) mm)
          by (apply arr_to_map; [rewrite length_stack; reflexivity | ecancel_assumption]);
        assert (Hm3 : sep (stack0 $@ p_s) (sep (x0 p5@ p_out) (sep (pP p5@ p_P)
                  (sep (kb $@ p_k) (sep (FElem p_d d2) (sep R (stack $@ p_t)))))) mm)
          by (apply arr_to_map; [rewrite length_stack0; reflexivity | ecancel_assumption]);
        ecancel_assumption
      | rewrite length_stack; reflexivity
      | rewrite length_stack0; reflexivity
      | exact Hx
      | ]
    end.
    rewrite SP.to_from_affine; change (Z.of_nat 256) with 256.
    rewrite shiftr_large; [rewrite SP.smul_0_l; reflexivity | lia | apply scalar_bound; assumption]. }
  { (* loop body *)
    intros v t' m' p_out' p_P' p_k' p_d' p_t' p_s' b' i'.
    repeat straightline.
    - (* bit [i' - 1] *)
      assert (hv : (0 < v)%nat).
      { subst br; destruct (word.ltu (word.of_Z 0) i') eqn:E; [| contradiction].
        rewrite word.unsigned_ltu, Properties.word.unsigned_of_Z_0 in E.
        apply Z.ltb_lt in E; lia. }
      assert (hi : word.unsigned i = Z.of_nat (v - 1)).
      { subst i; rewrite Properties.word.unsigned_sub_nowrap; rewrite ?Properties.word.unsigned_of_Z_1; lia. }
      set (n := Z.to_nat (word.unsigned i / 8)).
      assert (hn : (n < Datatypes.length kb)%nat).
      { subst n; rewrite H3. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; lia). lia. }
      exists (word.of_Z (Z.b2z (Z.testbit (le_combine kb) (word.unsigned i)))); split.
      { cbv [dexpr]. repeat straightline.
        exists (word.of_Z (byte.unsigned (nth n kb Byte.x00))); split.
        - match goal with |- context [word.sru i ?s] => subst s end.
          replace (word.sru i (word.of_Z 3)) with (word.of_Z (Z.of_nat n) : word).
          + lazymatch goal with
            | Hacc : B.feval_projective_coords ?acc = phi5 (proj1_sig ?A),
              Hlen : Datatypes.length ?tb = 200%nat,
              Hlen' : Datatypes.length ?sb = 200%nat |- _ =>
              assert (Hk : sep (kb $@ p_k) (sep (acc p5@ p_out) (sep (tb $@ p_t)
                             (sep (sb $@ p_s) (sep (pP p5@ p_P) (sep (FElem p_d d2) R))))) m')
                by ecancel_assumption
            end.
            exact (load_byte kb p_k n _ m' Hk hn ltac:(rewrite H3; cbn; lia)).
          + apply Properties.word.unsigned_inj.
            rewrite sru3, Properties.word.unsigned_of_Z_nowrap; subst n;
              rewrite ?Z2Nat.id; try (apply Z.div_pos; lia); try reflexivity.
            pose proof (Properties.word.unsigned_range i); split; [lia |].
            pose proof (Z.div_le_upper_bound (word.unsigned i) 8 (2 ^ 64) ltac:(lia) ltac:(lia)); lia.
        - repeat straightline. rewrite bit_word.
          f_equal; f_equal.
          assert (hdm : word.unsigned i = 8 * Z.of_nat n + word.unsigned i mod 8)
            by (subst n; rewrite Z2Nat.id by (apply Z.div_pos; lia); apply Z.div_mod; lia).
          pose proof (testbit_le_combine kb n (word.unsigned i mod 8)
                        (Z.mod_pos_bound _ 8 ltac:(lia))) as Ht.
          rewrite <-hdm in Ht.
          first [exact Ht | symmetry; exact Ht]. }
      repeat straightline.
      straightline_call; ssplit; try ecancel_assumption; try eassumption; try reflexivity.
      lazymatch goal with
      | Hp : ?r = [] /\ _ |- _ =>
          destruct Hp as (-> & Ht & acc' & tb' & sb' & A' & Hm' & Hl' & Hls' & Hf' & Ha')
      end.
      eexists; split; [reflexivity |].
      cbv [Markers.unique Markers.left Markers.split Markers.right].
      set (bv := word.of_Z (Z.b2z (Z.testbit (le_combine kb) (word.unsigned i))) : word) in *.
      clearbody bv i.
      exists p_out, p_P, p_k, p_d, p_t, p_s, bv, i.
      split; [exact (conj eq_refl eq_refl) |].
      exists (v - 1)%nat.
      lazymatch goal with
      | Hinv : SP.to_affine ?A0 = smul (Z.shiftr (le_combine kb) (Z.of_nat v)) _ |- _ =>
        split;
        [ ssplit; try reflexivity; try lia; try congruence;
          exists acc', tb', sb', A'; ssplit; [ecancel_assumption | assumption | assumption | assumption |];
          rewrite Ha', hi; apply step_affine; [lia |];
          replace (Z.of_nat (v - 1) + 1) with (Z.of_nat v) by lia; exact Hinv
        | split; [lia | intros ? ? ? ? ? ? ? ? ? ? Hp; exact Hp] ]
      end.
    - (* exit of the loop *)
      assert (hv : v = 0%nat).
      { subst br; destruct (word.ltu (word.of_Z 0) i') eqn:E.
        - exfalso; match goal with Hz : word.unsigned (word.of_Z 1) = 0 |- _ => cbv in Hz; discriminate Hz end.
        - rewrite word.unsigned_ltu, Properties.word.unsigned_of_Z_0 in E.
          apply Z.ltb_ge in E. pose proof (Properties.word.unsigned_range i'); lia. }
      subst v.
      lazymatch goal with
      | Hinv : SP.to_affine ?A0 = smul (Z.shiftr (le_combine kb) (Z.of_nat 0)) _,
        Hf : B.feval_projective_coords ?acc0 = phi5 (proj1_sig ?A0),
        Hl : Datatypes.length ?tb0 = 200%nat,
        Hls : Datatypes.length ?sb0 = 200%nat |- _ =>
        exists acc0, tb0, sb0, A0; ssplit; [ecancel_assumption | exact Hl | exact Hls | exact Hf |];
        rewrite Hinv; reflexivity
      end. }
  { (* after the loop: release the two scratch buffers *)
    intros t' m' ? ? ? ? ? ? ? ? (Ht & acc & tb & sb & A & Hm & Hl & Hls & Hf & Ha).
    assert (Hm2 : sep (array ptsto (word.of_Z 1) p_s sb)
                    (sep (acc p5@ p_out) (sep (tb $@ p_t) (sep (pP p5@ p_P)
                    (sep (kb $@ p_k) (sep (FElem p_d d2) R))))) m')
      by (apply map_to_arr; [exact Hls | ecancel_assumption]).
    destruct Hm2 as (mS & mR & Hsplit & HmS & HmR).
    exists mR, mS; ssplit;
      [ pose proof (Array.array_1_to_anybytes _ _ _ HmS) as Hany; rewrite Hls in Hany; exact Hany
      | apply Properties.map.split_comm; exact Hsplit | ].
    assert (Hm3 : sep (array ptsto (word.of_Z 1) p_t tb)
                    (sep (acc p5@ p_out) (sep (pP p5@ p_P)
                    (sep (kb $@ p_k) (sep (FElem p_d d2) R)))) mR)
      by (apply map_to_arr; [exact Hl | ecancel_assumption]).
    destruct Hm3 as (mS' & mR' & Hsplit' & HmS' & HmR').
    exists mR', mS'; ssplit;
      [ pose proof (Array.array_1_to_anybytes _ _ _ HmS') as Hany; rewrite Hl in Hany; exact Hany
      | apply Properties.map.split_comm; exact Hsplit' | ].
    cbv beta match fix delta [WeakestPrecondition.list_map WeakestPrecondition.list_map_body].
    split; [reflexivity |]. split; [congruence |].
    exists acc, A; ssplit; [ecancel_assumption | exact Hf | exact Ha]. }
Qed.

(** ** The top-level theorem

    As [ed25519_exec_scalarmult], for [scalarmult_ct]: for a group element
    [x] of SigmaProtocol, held at [p_P] as the image of
    [Ed.from_affine x], and a scalar [s] held at [p_k] as the 32 bytes of
    its unsigned value, [scalarmult_ct] writes at [p_out] the image of an
    extended point [A] that is projectively equal to
    [xsmul s (Ed.from_affine x)] and whose affine image is
    [Ed.gpow_fast x s]. *)
Theorem ed25519_exec_scalarmult_ct functions :
  map.get functions "scalarmult_ct" = Some scalarmult_ct ->
  map.get functions "step_ct" = Some step_ct ->
  map.get functions "cmov" = Some cmov ->
  map.get functions "set_identity" = Some set_identity ->
  map.get functions "add" = Some add ->
  map.get functions "to_cached2" = Some to_cached2 ->
  map.get functions "readd" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.readd ->
  map.get functions "double" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.double ->
  B.spec_of_fe25519_square64 functions ->
  B.spec_of_fe25519_carry_add64 functions ->
  B.spec_of_fe25519_add64 functions ->
  B.spec_of_fe25519_carry_sub64 functions ->
  B.spec_of_fe25519_sub64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  B.spec_of_fe25519_from_word64 functions ->
  forall (p_out p_P p_k p_d : word) (x : SP.G) (s : ZL.F) (pP : B.projective_coords)
         (d2 : felem) (kb out : list byte) (R : _ -> Prop) t m,
    m =* out $@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R ->
    Datatypes.length out = Z.to_nat (5 * felem_size) ->
    Datatypes.length kb = 32%nat ->
    le_combine kb = ZL.to_Z s ->
    F.add Fd Fd = feval d2 -> bounded_by tight_bounds d2 ->
    B.feval_projective_coords pP = phi5 (proj1_sig (SP.from_affine (proj1_sig x))) ->
    WeakestPrecondition.call functions "scalarmult_ct" t m [p_out; p_P; p_k; p_d]
      (fun t' m' rets => rets = [] /\ t' = t /\
         exists (a : B.projective_coords) (A : SP.xpoint),
           m' =* a p5@ p_out * pP p5@ p_P * kb $@ p_k * FElem p_d d2 * R /\
           B.feval_projective_coords a = phi5 (proj1_sig A) /\
           SXeq A (xsmul (ZL.to_Z s) (SP.from_affine (proj1_sig x))) /\
           SP.to_affine A = proj1_sig (SP.gpow_fast x s)).
Proof.
  intros Hsm Hst Hcm Hid Hadd_fn Htc Hrd Hdbl Hsq Hcadd Hadd Hcsub Hsub Hmul Hfw
    p_out p_P p_k p_d x s pP d2 kb out R t m Hm Hlo Hlk Hk Hd Hb HP.
  assert (Hcmov : spec_of_cmov functions).
  { pose proof cmov_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; exact Hcm. }
  assert (Hstep : spec_of_step_ct functions).
  { pose proof step_ct_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; [exact Hst | | | exact Hcmov].
    - apply double_spec_p5, ed25519_exec_double; assumption.
    - apply ed25519_exec_add_fn; assumption. }
  assert (Hsi : spec_of_set_identity functions).
  { pose proof set_identity_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; assumption. }
  assert (Hsmul : spec_of_scalarmult_ct functions).
  { pose proof scalarmult_ct_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
    apply H; assumption. }
  eapply WeakestPreconditionProperties.Proper_call;
    [| apply (Hsmul p_out p_P p_k p_d (SP.from_affine (proj1_sig x)) pP d2 kb out R t m);
       ssplit; assumption].
  intros t' m' rets (Hrets & Ht & a & A & Hm' & Ha & HA).
  split; [exact Hrets |]. split; [symmetry; exact Ht |].
  rewrite SP.to_from_affine, Hk in HA.
  destruct (gpow_fast_affine x s A HA) as [Heq Haff].
  exists a, A; ssplit; assumption.
Qed.

Print Assumptions cmov_ok.
Print Assumptions step_ct_ok.
Print Assumptions scalarmult_ct_ok.
Print Assumptions ed25519_exec_scalarmult_ct.
