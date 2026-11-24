(** The bedrock2 arithmetic modulo [l] of [FieldL.v], stated on
    SigmaProtocol's scalar field [Zl.F], a record around [Zmod l].

    A residue [a : Zl.F] has two encodings by a fully reduced limb list
    [w] ([valid w], i.e. [bounded_by tight_bounds w]):
    - [enc_mont w a] (Montgomery form): [feval w = phiL a] for the
      representation [frepL], i.e. [eval (from_montgomerymod w) = a mod l],
      i.e. [eval w = a * 2^256 mod l];
    - [enc_raw w a] (plain form): [feval w = phiL a] for [frepL_raw], i.e.
      [eval w = a].
    [phiL : Zl.F -> F l] is the isomorphism [x |-> F.of_Z l (unsigned x)]
    to fiat-crypto's [F l].

    For each function the theorem [fl_exec_*] states that under the
    environment hypothesis ([functions] maps its name to the bedrock2 code)
    a call satisfies a specification over [Zl.F]:
    - [fl_exec_add], [fl_exec_sub], [fl_exec_opp], [fl_exec_mul]: the call on
      Montgomery encodings of [a], [b] returns a Montgomery encoding of
      [Zl.add a b], [Zl.sub a b], [Zl.opp a], [Zl.mul a b];
    - [fl_exec_add_raw], [fl_exec_sub_raw], [fl_exec_opp_raw]: the same on
      plain encodings (addition, subtraction and negation commute with the
      factor [2^256]);
    - [fl_exec_mul_raw]: on a plain encoding of [a] and a Montgomery
      encoding of [b] the call returns a plain encoding of [Zl.mul a b];
    - [fl_exec_to_mont], [fl_exec_from_mont]: the conversions between the
      encodings;
    - [fl_exec_from_bytes], [fl_exec_to_bytes]: the conversions between a
      plain encoding of [a] and the 32 little-endian bytes of
      [Zl.to_Z a]. *)

From Stdlib Require Import String List ZArith Zmod Lia.
From Curve Require Ed25519.
Require Import Crypto.Spec.ModularArithmetic.
Require Crypto.Arithmetic.ModularArithmeticTheorems.
Require Crypto.Arithmetic.PrimeFieldTheorems.
Require Import Crypto.Bedrock.Specs.Field.
Require Import Crypto.Bedrock.Field.Synthesis.New.WordByWordMontgomery.
Require Crypto.Bedrock.Field.Synthesis.New.Signature.
Require Import Crypto.Bedrock.Field.Translation.Parameters.Defaults64.
Require Crypto.Arithmetic.WordByWordMontgomery Crypto.Arithmetic.Partition
        Crypto.Arithmetic.UniformWeight Crypto.Arithmetic.Core Crypto.Arithmetic.ModOps.
Require Crypto.Bedrock.Field.Common.Arrays.ByteBounds.
Require Crypto.PushButtonSynthesis.WordByWordMontgomery.
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Byte.
Require Import coqutil.Word.LittleEndianList coqutil.Map.OfListWord.
Import bedrock2.Memory.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.ProgramLogic bedrock2.WeakestPrecondition
        bedrock2.WeakestPreconditionProperties bedrock2.Syntax bedrock2.Array
        bedrock2.Scalars.
Require Import bedrock2.BasicC64Semantics coqutil.Word.Bitwidth64.
Require Import Bridge.FieldL.
Import ListNotations.

Local Open Scope string_scope.
Local Open Scope Z_scope.

Module Zl := Curve.Ed25519.Ed25519.Zl.
Module MAT := Crypto.Arithmetic.ModularArithmeticTheorems.F.
Module WBW := Crypto.Arithmetic.WordByWordMontgomery.WordByWordMontgomery.
Module PBS := Crypto.PushButtonSynthesis.WordByWordMontgomery.

#[local] Existing Instances BasicC64Semantics.word BasicC64Semantics.wordok Bitwidth64.BW64
  BasicC64Semantics.mem BasicC64Semantics.mapok
  Defaults64.default_parameters Defaults64.default_parameters_ok
  FieldL.field_parametersL FieldL.frepL.

Local Notation word := BasicC64Semantics.word.
Local Notation ML := (@M_pos FieldL.field_parametersL).
Local Notation FL := (F ML).
Local Notation feval_raw := (@feval _ _ _ _ _ FieldL.frepL_raw).

(** ** The isomorphism [Zmod l -> F l] *)

Lemma ML_eq : Z.pos ML = 2^252 + 27742317777372353535851937790883648493.
Proof. vm_compute. reflexivity. Qed.

Definition phiL (x : Zl.F) : FL := F.of_Z ML (Zl.to_Z x).

Lemma of_Z_modl z : F.of_Z ML (z mod (2^252 + 27742317777372353535851937790883648493)) = F.of_Z ML z.
Proof. rewrite <-ML_eq. symmetry; apply MAT.of_Z_mod. Qed.

Lemma phiL_add x y : phiL (Zl.add x y) = F.add (phiL x) (phiL y).
Proof. unfold phiL; rewrite Zl.unsigned_add, of_Z_modl; apply MAT.of_Z_add. Qed.

Lemma phiL_sub x y : phiL (Zl.sub x y) = F.sub (phiL x) (phiL y).
Proof. unfold phiL; rewrite Zl.unsigned_sub, of_Z_modl; apply MAT.of_Z_sub. Qed.

Lemma phiL_mul x y : phiL (Zl.mul x y) = F.mul (phiL x) (phiL y).
Proof. unfold phiL; rewrite Zl.unsigned_mul, of_Z_modl; apply MAT.of_Z_mul. Qed.

Lemma phiL_opp x : phiL (Zl.opp x) = F.opp (phiL x).
Proof. unfold phiL; rewrite Zl.unsigned_opp, of_Z_modl; apply MAT.of_Z_opp. Qed.

Lemma phiL_to_Z x : F.to_Z (phiL x) = Zl.to_Z x.
Proof.
  unfold phiL; rewrite MAT.to_Z_of_Z, ML_eq.
  apply Zl.to_Z_mod.
Qed.

Lemma phiL_inj x y : phiL x = phiL y -> x = y.
Proof.
  intro h; apply (f_equal F.to_Z) in h; rewrite !phiL_to_Z in h.
  apply Zl.to_Z_inj; exact h.
Qed.

(** ** Plain and Montgomery forms *)

(** The fully reduced limb lists, the bounds of every function below. *)
Definition valid (x : felem) : Prop := bounded_by tight_bounds x.

Definition enc_mont (x : felem) (a : Zl.F) : Prop := feval x = phiL a.
Definition enc_raw (x : felem) (a : Zl.F) : Prop := feval_raw x = phiL a.

Lemma loose_tight : loose_bounds = tight_bounds.
Proof. reflexivity. Qed.

(** [R^-1 = (2^64)^-4 mod l] and [R = (2^64)^4], the factors of
    [from_mont_model] and [to_mont_model]. *)
Local Notation Rinv := (F.of_Z ML (Field.r' (width:=64) ^ Z.of_nat felem_size_in_words)).
Local Notation R := (F.of_Z ML (Field.r (width:=64) ^ Z.of_nat felem_size_in_words)).

Add Ring FLring : (MAT.ring_theory ML).

Lemma Rinv_R : F.mul Rinv R = F.one.
Proof. apply MAT.eq_to_Z_iff; vm_compute; reflexivity. Qed.

Lemma mul_Rinv_R (u : FL) : F.mul (F.mul u Rinv) R = u.
Proof.
  transitivity (F.mul u (F.mul Rinv R)); [ring | rewrite Rinv_R; ring].
Qed.

Lemma mul_Rinv_inj (u v : FL) : F.mul u Rinv = F.mul v Rinv -> u = v.
Proof.
  intro h. apply (f_equal (fun z => F.mul z R)) in h.
  transitivity (F.mul u (F.mul Rinv R)); [rewrite Rinv_R; ring |].
  transitivity (F.mul (F.mul u Rinv) R); [ring |]. rewrite h.
  transitivity (F.mul v (F.mul Rinv R)); [ring | rewrite Rinv_R; ring].
Qed.

(** The Montgomery value of a fully reduced limb list is its plain value
    times [R^-1]: fiat-crypto's [from_montgomerymod_correct]. *)
Lemma feval_mont_raw (x : felem) :
  valid x -> feval x = F.mul (feval_raw x) Rinv.
Proof.
  cbv [valid bounded_by tight_bounds FieldL.frepL FieldL.frepL_raw
       field_representation field_representation_raw
       Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation
       Crypto.Bedrock.Field.Interface.Representation.frep feval
       Crypto.Bedrock.Field.Interface.Representation.eval_words
       list_in_bounds eval_trans eval_raw].
  intro hv.
  rewrite <-MAT.of_Z_mul. apply MAT.eq_of_Z_iff.
  epose proof (WBW.from_montgomerymod_correct 64 _ FieldL.m (Field.r' (width:=64)) _ _ _ _ _ _ _ _ hv) as [h _].
  cbv [WBW.eval] in h. rewrite ML_eq. rewrite h. reflexivity.
  Unshelve. all: vm_compute; try reflexivity; try discriminate; try congruence.
Qed.

(** ** Specifications over [Zl.F] *)

Section Specs.
  Local Notation "m =* P" := ((P%sep) m) (at level 70, only parsing).

  (** A binary operation: encodings [ex], [ey] of the inputs, [eo] of the
      output, Gallina operation [op]. *)
  Definition zl_binop_spec name (ex ey eo : felem -> Zl.F -> Prop)
      (op : Zl.F -> Zl.F -> Zl.F) : spec_of name :=
    fnspec! name (pout px py : word) / (a b : Zl.F) (x y : felem) out Rr,
    { requires tr mem :=
        valid x /\ valid y /\ ex x a /\ ey y b
        /\ length out = Z.to_nat felem_size_in_bytes
        /\ (exists Rx, (FElem px x * Rx)%sep mem)
        /\ (exists Ry, (FElem py y * Ry)%sep mem)
        /\ (out$@pout * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out : felem, eo out (op a b) /\ valid out
          /\ (FElem pout out * Rr)%sep mem' }.

  Definition zl_unop_spec name (ex eo : felem -> Zl.F -> Prop)
      (op : Zl.F -> Zl.F) : spec_of name :=
    fnspec! name (pout px : word) / (a : Zl.F) (x : felem) out Rr,
    { requires tr mem :=
        valid x /\ ex x a
        /\ length out = Z.to_nat felem_size_in_bytes
        /\ (exists Rx, (FElem px x * Rx)%sep mem)
        /\ (out$@pout * Rr)%sep mem;
      ensures tr' mem' :=
        tr = tr' /\
        exists out : felem, eo out (op a) /\ valid out
          /\ (FElem pout out * Rr)%sep mem' }.

  (** [fl_from_bytes]: the 32 little-endian bytes of [unsigned a] to a plain
      encoding of [a]. *)
  Definition spec_of_fl_from_bytes_zl : spec_of "fl_from_bytes" :=
    fnspec! "fl_from_bytes" (pout px : word) / (a : Zl.F) out Rr,
    { requires tr mem :=
        (exists Ra, (array ptsto (word.of_Z 1) px
                       (le_split 32 (Zl.to_Z a)) * Ra)%sep mem)
        /\ (out$@pout * Rr)%sep mem
        /\ length out = Z.to_nat felem_size_in_bytes;
      ensures tr' mem' :=
        tr = tr' /\
        exists X : felem, enc_raw X a /\ valid X
          /\ (FElem pout X * Rr)%sep mem' }.

  (** [fl_to_bytes]: a plain encoding of [a] to the 32 little-endian bytes
      of [unsigned a]. *)
  Definition spec_of_fl_to_bytes_zl : spec_of "fl_to_bytes" :=
    fnspec! "fl_to_bytes" (pout px : word) / (a : Zl.F) (out : list byte) (x : felem) Rr,
    { requires tr mem :=
        (array ptsto (word.of_Z 1) pout out * Rr)%sep mem
        /\ length out = 32%nat
        /\ (exists Ra, (FElem px x * Ra)%sep mem)
        /\ valid x /\ enc_raw x a;
      ensures tr' mem' :=
        tr = tr' /\
        (array ptsto (word.of_Z 1) pout (le_split 32 (Zl.to_Z a)) * Rr)%sep mem' }.
End Specs.

(** ** Transport of fiat-crypto's specifications *)

Lemma binop_transport {name} (op : BinOp name) functions
    (ex ey eo : felem -> Zl.F -> Prop) (zop : Zl.F -> Zl.F -> Zl.F) :
  bin_xbounds = tight_bounds -> bin_ybounds = tight_bounds ->
  bin_outbounds = tight_bounds ->
  (forall x y o a b, valid x -> valid y -> valid o -> ex x a -> ey y b ->
     feval o = bin_model (feval x) (feval y) -> eo o (zop a b)) ->
  spec_of_BinOp op functions -> zl_binop_spec name ex ey eo zop functions.
Proof.
  intros Hxb Hyb Hob Halg H pout px py a b x y out Rr tr mem
    (Hx & Hy & Hex & Hey & Hlen & HRx & HRy & Hout).
  eapply Proper_call; [ | apply (H pout px py x y out Rr tr mem);
    refine (conj _ (conj _ (conj Hlen (conj HRx (conj HRy Hout)))));
    [rewrite Hxb; exact Hx | rewrite Hyb; exact Hy] ].
  intros tr' mem' rets (Hrets & Htr & o & Ho & Hob' & Hm').
  split; [exact Hrets |]. split; [exact Htr |].
  rewrite Hob in Hob'.
  exists o; split; [ | split; assumption].
  exact (Halg x y o a b Hx Hy Hob' Hex Hey Ho).
Qed.

Lemma unop_transport {name} (op : UnOp name) functions
    (ex eo : felem -> Zl.F -> Prop) (zop : Zl.F -> Zl.F) :
  un_xbounds = tight_bounds -> un_outbounds = tight_bounds ->
  (forall x o a, valid x -> valid o -> ex x a ->
     feval o = un_model (feval x) -> eo o (zop a)) ->
  spec_of_UnOp op functions -> zl_unop_spec name ex eo zop functions.
Proof.
  intros Hxb Hob Halg H pout px a x out Rr tr mem
    (Hx & Hex & Hlen & HRx & Hout).
  eapply Proper_call; [ | apply (H pout px x out Rr tr mem);
    refine (conj _ (conj Hlen (conj HRx Hout))); rewrite Hxb; exact Hx ].
  intros tr' mem' rets (Hrets & Htr & o & Ho & Hob' & Hm').
  split; [exact Hrets |]. split; [exact Htr |].
  rewrite Hob in Hob'.
  exists o; split; [ | split; assumption].
  exact (Halg x o a Hx Hob' Hex Ho).
Qed.

(** ** The theorems *)

Theorem fl_exec_add functions :
  map.get functions "fl_add" = Some (snd FieldL.fl_add) ->
  zl_binop_spec "fl_add" enc_mont enc_mont enc_mont Zl.add functions.
Proof.
  intro H; apply (binop_transport bin_add); try reflexivity.
  - intros x y o a b _ _ _ hx hy ho; unfold enc_mont in *.
    rewrite phiL_add, <-hx, <-hy; exact ho.
  - apply FieldL.fl_add_correct; exact H.
Qed.

Theorem fl_exec_sub functions :
  map.get functions "fl_sub" = Some (snd FieldL.fl_sub) ->
  zl_binop_spec "fl_sub" enc_mont enc_mont enc_mont Zl.sub functions.
Proof.
  intro H; apply (binop_transport bin_sub); try reflexivity.
  - intros x y o a b _ _ _ hx hy ho; unfold enc_mont in *.
    rewrite phiL_sub, <-hx, <-hy; exact ho.
  - apply FieldL.fl_sub_correct; exact H.
Qed.

Theorem fl_exec_mul functions :
  map.get functions "fl_mul" = Some (snd FieldL.fl_mul) ->
  zl_binop_spec "fl_mul" enc_mont enc_mont enc_mont Zl.mul functions.
Proof.
  intro H; apply (binop_transport bin_mul); try reflexivity.
  - intros x y o a b _ _ _ hx hy ho; unfold enc_mont in *.
    rewrite phiL_mul, <-hx, <-hy; exact ho.
  - apply FieldL.fl_mul_correct; exact H.
Qed.

Theorem fl_exec_opp functions :
  map.get functions "fl_opp" = Some (snd FieldL.fl_opp) ->
  zl_unop_spec "fl_opp" enc_mont enc_mont Zl.opp functions.
Proof.
  intro H; apply (unop_transport un_opp); try reflexivity.
  - intros x o a _ _ hx ho; unfold enc_mont in *.
    rewrite phiL_opp, <-hx; exact ho.
  - apply FieldL.fl_opp_correct; exact H.
Qed.

Theorem fl_exec_add_raw functions :
  map.get functions "fl_add" = Some (snd FieldL.fl_add) ->
  zl_binop_spec "fl_add" enc_raw enc_raw enc_raw Zl.add functions.
Proof.
  intro H; apply (binop_transport bin_add); try reflexivity.
  - intros x y o a b vx vy vo hx hy ho; unfold enc_raw in *.
    cbn [bin_model bin_add] in ho.
    rewrite (feval_mont_raw o vo), (feval_mont_raw x vx), (feval_mont_raw y vy) in ho.
    apply mul_Rinv_inj. rewrite ho, phiL_add, <-hx, <-hy; ring.
  - apply FieldL.fl_add_correct; exact H.
Qed.

Theorem fl_exec_sub_raw functions :
  map.get functions "fl_sub" = Some (snd FieldL.fl_sub) ->
  zl_binop_spec "fl_sub" enc_raw enc_raw enc_raw Zl.sub functions.
Proof.
  intro H; apply (binop_transport bin_sub); try reflexivity.
  - intros x y o a b vx vy vo hx hy ho; unfold enc_raw in *.
    cbn [bin_model bin_sub] in ho.
    rewrite (feval_mont_raw o vo), (feval_mont_raw x vx), (feval_mont_raw y vy) in ho.
    apply mul_Rinv_inj. rewrite ho, phiL_sub, <-hx, <-hy; ring.
  - apply FieldL.fl_sub_correct; exact H.
Qed.

Theorem fl_exec_opp_raw functions :
  map.get functions "fl_opp" = Some (snd FieldL.fl_opp) ->
  zl_unop_spec "fl_opp" enc_raw enc_raw Zl.opp functions.
Proof.
  intro H; apply (unop_transport un_opp); try reflexivity.
  - intros x o a vx vo hx ho; unfold enc_raw in *.
    cbn [un_model un_opp] in ho.
    rewrite (feval_mont_raw o vo), (feval_mont_raw x vx) in ho.
    apply mul_Rinv_inj. rewrite ho, phiL_opp, <-hx; ring.
  - apply FieldL.fl_opp_correct; exact H.
Qed.

Theorem fl_exec_mul_raw functions :
  map.get functions "fl_mul" = Some (snd FieldL.fl_mul) ->
  zl_binop_spec "fl_mul" enc_raw enc_mont enc_raw Zl.mul functions.
Proof.
  intro H; apply (binop_transport bin_mul); try reflexivity.
  - intros x y o a b vx vy vo hx hy ho; unfold enc_raw, enc_mont in *.
    cbn [bin_model bin_mul] in ho.
    rewrite (feval_mont_raw o vo), (feval_mont_raw x vx) in ho.
    apply mul_Rinv_inj. rewrite ho, phiL_mul, <-hx, <-hy; ring.
  - apply FieldL.fl_mul_correct; exact H.
Qed.

Theorem fl_exec_to_mont functions :
  map.get functions "fl_to_mont" = Some (snd FieldL.fl_to_mont) ->
  zl_unop_spec "fl_to_mont" enc_raw enc_mont (fun a => a) functions.
Proof.
  intro H; apply (unop_transport (un_to_mont (to_mont:=FieldL.to_mont_string)));
    try reflexivity.
  - intros x o a vx vo hx ho; unfold enc_raw, enc_mont in *.
    cbn [un_model un_to_mont to_mont_model] in ho.
    rewrite (feval_mont_raw x vx) in ho.
    rewrite ho, hx. apply mul_Rinv_R.
  - apply FieldL.fl_to_mont_correct; exact H.
Qed.

Theorem fl_exec_from_mont functions :
  map.get functions "fl_from_mont" = Some (snd FieldL.fl_from_mont) ->
  zl_unop_spec "fl_from_mont" enc_mont enc_raw (fun a => a) functions.
Proof.
  intro H; apply (unop_transport (un_from_mont (from_mont:=FieldL.from_mont_string)));
    try reflexivity.
  - intros x o a vx vo hx ho; unfold enc_raw, enc_mont in *.
    cbn [un_model un_from_mont from_mont_model] in ho.
    rewrite (feval_mont_raw o vo), hx in ho.
    apply mul_Rinv_inj. exact ho.
  - apply FieldL.fl_from_mont_correct; exact H.
Qed.

(** ** Byte conversions *)

Lemma n_bytes_eq : PBS.n_bytes FieldL.m = 32%nat.
Proof. vm_compute. reflexivity. Qed.

(** The bytes of [le_split 32 z] are the base-[2^8] digits of [z]. *)
Lemma le_split_digits z :
  map byte.unsigned (le_split 32 z) = Crypto.Arithmetic.Partition.Partition.partition (Crypto.Arithmetic.ModOps.weight 8 1) 32 z.
Proof.
  rewrite <-(Crypto.Bedrock.Field.Synthesis.New.Signature.partition_le_split (width:=64) 32 z).
  rewrite Crypto.Bedrock.Field.Common.Arrays.ByteBounds.byte_map_unsigned_of_Z.
  apply (Crypto.Bedrock.Field.Common.Arrays.ByteBounds.map_byte_wrap_bounded 32), Crypto.Bedrock.Field.Common.Arrays.ByteBounds.partition_bounded_by.
Qed.

Lemma eval_digits z : 0 <= z < 2^256 ->
  Crypto.Arithmetic.Core.Positional.eval (Crypto.Arithmetic.ModOps.weight 8 1) 32 (Crypto.Arithmetic.Partition.Partition.partition (Crypto.Arithmetic.ModOps.weight 8 1) 32 z) = z.
Proof.
  intro hz.
  rewrite (@Crypto.Arithmetic.Partition.eval_partition _ (Crypto.Arithmetic.UniformWeight.uwprops 8 ltac:(lia))).
  apply Z.mod_small.
  replace (Crypto.Arithmetic.UniformWeight.uweight 8 32%nat) with (2^256) by reflexivity. lia.
Qed.

Lemma unsigned_range (a : Zl.F) :
  0 <= Zl.to_Z a < 2^252 + 27742317777372353535851937790883648493.
Proof. apply Zl.to_Z_range. Qed.

(** The 32 little-endian bytes of [unsigned a] are in the bounds of
    [fl_from_bytes] and evaluate to [phiL a]. *)
Lemma bytes_of_Zl (a : Zl.F) :
  bytes_in_bounds (FieldRepresentation:=FieldL.frepL_raw) (le_split 32 (Zl.to_Z a)) /\
  feval_bytes (FieldRepresentation:=FieldL.frepL_raw) (le_split 32 (Zl.to_Z a)) = phiL a.
Proof.
  pose proof (unsigned_range a) as ha.
  assert (hz : 0 <= Zl.to_Z a < 2^256) by lia.
  cbv [bytes_in_bounds feval_bytes FieldL.frepL_raw field_representation_raw
       Crypto.Bedrock.Field.Synthesis.New.Signature.field_representation
       Crypto.Bedrock.Field.Interface.Representation.frep
       Crypto.Bedrock.Field.Interface.Representation.eval_bytes list_in_bounds].
  rewrite n_bytes_eq, le_split_digits.
  cbv [WBW.valid WBW.small WBW.eval Crypto.Arithmetic.UniformWeight.uweight].
  rewrite eval_digits by exact hz.
  split; [split; [reflexivity | exact ha] | reflexivity].
Qed.

Theorem fl_exec_from_bytes functions :
  map.get functions "fl_from_bytes" = Some (snd FieldL.fl_from_bytes) ->
  spec_of_fl_from_bytes_zl functions.
Proof.
  intros H pout px a out Rr tr mem (HRa & Hout & Hlen).
  destruct (bytes_of_Zl a) as [Hb Hv].
  eapply Proper_call; [ | apply (FieldL.fl_from_bytes_correct functions H pout px out
    (le_split 32 (Zl.to_Z a)) Rr tr mem); exact (conj HRa (conj Hout (conj Hlen Hb))) ].
  intros tr' mem' rets (Hrets & Htr & X & HX & HXb & Hm').
  split; [exact Hrets |]. split; [exact Htr |].
  exists X. split; [ | split; assumption].
  unfold enc_raw. rewrite <-Hv. exact HX.
Qed.

Theorem fl_exec_to_bytes functions :
  map.get functions "fl_to_bytes" = Some (snd FieldL.fl_to_bytes) ->
  spec_of_fl_to_bytes_zl functions.
Proof.
  intros H pout px a out x Rr tr mem (Hout & Hlen & HRa & Hx & Hex).
  eapply Proper_call; [ | apply (FieldL.fl_to_bytes_correct functions H pout px out x Rr tr mem);
    refine (conj Hout (conj _ (conj HRa Hx))); rewrite Hlen; symmetry; exact n_bytes_eq ].
  intros tr' mem' rets (Hrets & Htr & Hm' & _).
  split; [exact Hrets |]. split; [exact Htr |].
  unfold enc_raw in Hex. cbv zeta in Hm'.
  change (@encoded_felem_size_in_bytes _ _ _ _ _ FieldL.frepL_raw) with
    (PBS.n_bytes FieldL.m) in Hm'.
  rewrite n_bytes_eq in Hm'.
  match type of Hm' with context [le_split _ (F.to_Z ?v)] =>
    replace v with (phiL a) in Hm' by (symmetry; exact Hex) end.
  rewrite phiL_to_Z in Hm'. exact Hm'.
Qed.

Print Assumptions fl_exec_add.
Print Assumptions fl_exec_sub.
Print Assumptions fl_exec_mul.
Print Assumptions fl_exec_opp.
Print Assumptions fl_exec_add_raw.
Print Assumptions fl_exec_sub_raw.
Print Assumptions fl_exec_opp_raw.
Print Assumptions fl_exec_mul_raw.
Print Assumptions fl_exec_to_mont.
Print Assumptions fl_exec_from_mont.
Print Assumptions fl_exec_from_bytes.
Print Assumptions fl_exec_to_bytes.
