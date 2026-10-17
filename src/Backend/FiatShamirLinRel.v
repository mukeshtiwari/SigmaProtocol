(* Fiat-Shamir verification of multi-base proofs of knowledge, and its link
   to the library's generalised Okamoto protocol (Crypto/Okamoto.v): the
   statement is h = g_1^{x_1} ⋯ g_k^{x_k} in a vector space V, the proof is
   published as (challenge c, responses s_1..s_k), and the verifier
   reconstructs the announcement

       A = g_1^{s_1} ⋯ g_k^{s_k} · h^{d}

   and checks the challenge against the hash of A. Deployed systems use
   both signs for the response: Belenios, Verificatum and the BBS family
   write s = w − c·x and reconstruct with d = c; U-Prove writes
   s = w + c·x and reconstructs with d = −c. The theorem below is stated
   for an arbitrary d: the reconstructed announcement with challenge −d
   and the published responses is an accepting transcript of the Okamoto
   protocol. A verifier chooses d = c or d = −c and gets the accepting
   transcript with challenge −c or c respectively.

   Backend/BeleniosTally.v has the single-base version (fs_verify,
   fs_verify_schnorr_accepting, fs_verify_or_accepting); this file adds the
   multi-base one. *)

From Stdlib Require Import Utf8 Vector List Bool setoid_ring.Field.
From Algebra Require Import Hierarchy Group Monoid Field Integral_domain Ring Vector_space.
From Crypto Require Import Sigma Okamoto.
From Utility Require Import Util.
Import VectorNotations.

Section FiatShamirLinRel.

  Context
    {F : Type} {zero one : F} {add mul sub div : F -> F -> F} {opp inv : F -> F}
    {Fdec : forall x y : F, {x = y} + {x <> y}}
    {V : Type} {vid : V} {vopp : V -> V} {vadd : V -> V -> V} {smul : V -> F -> V}
    {Vdec : forall x y : V, {x = y} + {x <> y}}
    {HV : @vector_space F (@eq F) zero one add mul sub div opp inv V (@eq V) vid vopp vadd smul}.

  Add Field field : (@field_theory_for_stdlib_tactic F
    eq zero one opp add mul sub inv div vector_space_field).

  (* g_1^{s_1} ⋯ g_k^{s_k}, as Okamoto writes it *)
  Definition multi_exp {k : nat} (gs : Vector.t V k) (ss : Vector.t F k) : V :=
    Vector.fold_right (fun '(g, s) acc => vadd (smul g s) acc) (zip_with pair gs ss) vid.

  (* the reconstructed announcement *)
  Definition reconstruct_linrel {k : nat} (gs : Vector.t V k) (h : V) (d : F)
    (ss : Vector.t F k) : V :=
    vadd (multi_exp gs ss) (smul h d).

  (* Verification of a published multi-base proof (c, ss) against the hash
    H of the reconstructed announcement, with d = c or d = −c depending on
    the system's sign convention. *)
  Definition fs_verify_linrel {k : nat} (H : V -> F) (gs : Vector.t V k) (h : V)
    (d c : F) (ss : Vector.t F k) : bool :=
    match Fdec c (H (reconstruct_linrel gs h d ss)) with
    | left _ => true | right _ => false
    end.

  (* ---- link to the library ---- *)

  Lemma multi_exp_okamoto : forall (n : nat) (gs : Vector.t V (2 + n)) (ss : Vector.t F (2 + n)),
    Vector.fold_right (fun gr acc => vadd gr acc) (zip_with (fun g r => smul g r) gs ss) vid =
    multi_exp gs ss.
  Proof.
    intros n; generalize (2 + n); clear n.
    intros m; induction m as [| m ih]; intros gs ss.
    + rewrite (vector_inv_0 gs), (vector_inv_0 ss); reflexivity.
    + destruct (vector_inv_S gs) as (g & gs' & ->).
      destruct (vector_inv_S ss) as (s & ss' & ->).
      unfold multi_exp in *; cbn; f_equal; apply ih.
  Qed.

  (* The reconstructed announcement, the challenge −d and the responses form
    an accepting transcript of the generalised Okamoto protocol for
    h = g_1^{x_1} ⋯ g_k^{x_k}. *)
  Theorem reconstruct_linrel_accepting : forall (n : nat) (gs : Vector.t V (2 + n)) (h : V)
    (d : F) (ss : Vector.t F (2 + n)),
    generalised_okamoto_accepting_conversation (gid := vid) (gop := vadd) (gpow := smul) (Gdec := Vdec) gs h
      (mk_sigma _ _ _ [reconstruct_linrel gs h d ss] [opp d] ss) = true.
  Proof.
    intros *; unfold generalised_okamoto_accepting_conversation;
    cbn [Vector.hd announcement challenge response].
    rewrite multi_exp_okamoto.
    assert (he : multi_exp gs ss = vadd (reconstruct_linrel gs h d ss) (smul h (opp d))).
    { unfold reconstruct_linrel.
      pose proof (@vector_space_commutative_group F (@eq F) zero one add mul sub div
        opp inv V (@eq V) vid vopp vadd smul HV) as hcg.
      pose proof (@associative V (@eq V) vadd (@monoid_is_associative V (@eq V) vadd vid
        (@group_monoid V (@eq V) vadd vid vopp
          (@commutative_group_group V (@eq V) vadd vid vopp hcg)))) as hassoc.
      pose proof (@right_identity V (@eq V) vadd vid (@monoid_is_right_identity V (@eq V)
        vadd vid (@group_monoid V (@eq V) vadd vid vopp
          (@commutative_group_group V (@eq V) vadd vid vopp hcg)))) as hrid.
      rewrite <-hassoc.
      pose proof (@vector_space_smul_distributive_fadd F (@eq F) zero one add mul
        sub div opp inv V (@eq V) vid vopp vadd smul HV) as hd.
      rewrite <-(hd d (opp d) h).
      assert (ha : add d (opp d) = zero) by field.
      rewrite ha.
      pose proof (@vector_space_field_zero F (@eq F) zero one add mul
        sub div opp inv V (@eq V) vid vopp vadd smul HV) as hz.
      rewrite (hz h), hrid; reflexivity. }
    simpl.
    match goal with
    | |- context [Vdec ?a ?b] => destruct (Vdec a b) as [_ | hne]; [reflexivity | exfalso; apply hne; exact he]
    end.
  Qed.

  Theorem fs_verify_linrel_accepting : forall (n : nat) (H : V -> F) (gs : Vector.t V (2 + n)) (h : V)
    (d c : F) (ss : Vector.t F (2 + n)),
    fs_verify_linrel H gs h d c ss = true ->
    generalised_okamoto_accepting_conversation (gid := vid) (gop := vadd) (gpow := smul) (Gdec := Vdec) gs h
      (mk_sigma _ _ _ [reconstruct_linrel gs h d ss] [opp d] ss) = true.
  Proof. intros; apply reconstruct_linrel_accepting. Qed.

End FiatShamirLinRel.
