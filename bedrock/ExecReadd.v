(** Second bridge theorem: AUCurves' bedrock2 [readd] adds two extended
    points of SigmaProtocol up to projective equality. The second operand
    is passed in cached coordinates [xprep Q] ([FieldTransport]); the
    result has a phi-preimage that is [Extended.eq] to [Ed.xadd P Q] and
    whose affine image is the sum of the affine images of [P] and [Q].

    The cached operand is not produced by AUCurves' bedrock2 [to_cached]:
    [to_cached64_ok] assumes a callee "fe25519_half", for which neither
    fiat-crypto nor AUCurves has an implementation (fiat's bedrock2 field
    pipeline synthesises mul, square, add, sub, carry_add, carry_sub, opp,
    scmula24, inv, from/to_bytes, copy, from_word, select). The
    precondition here is stated on the limb values only, so a caller
    supplies [xprep Q] computed in Gallina, e.g. once for a fixed base.
    The precondition holds for every representative [Q] of the point, so a
    halving-free preparation also meets it: [(Y-X, Y+X, 2Z, 2d Ta Tb)] is
    [xprep] of the representative [(2X, 2Y, 2Z, 2Ta, Tb)]. *)

Require Import Bedrock.End2End.Ed25519.EdwardsXYZT64_Imports.
Require Bedrock.End2End.Ed25519.EdwardsXYZT64.
Require Import Bridge.FieldTransport.

Module B := Bedrock.End2End.Ed25519.EdwardsXYZT64.Ed25519XYZT64.

Local Open Scope string_scope.
Local Open Scope Z_scope.

(* The notations of [Ed25519XYZT64] (module-local there), restated. *)
Local Notation word := (Naive.word 64).
Local Notation FElem := (FElem(FieldRepresentation:=frep25519)).
Local Notation felem := (felem(FieldRepresentation:=frep25519)).
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
Local Notation "c 'p4@' p" := (let '(half_ymx, half_ypx ,z,td) := proj1_sig c in sep (sep (sep
                              (FElem (p) half_ymx)
                              (FElem (p .+ felem_size) half_ypx))
                              (FElem (p .+ (felem_size + felem_size)) z))
                              (FElem (p .+ (felem_size + felem_size + felem_size)) td))
                              (at level 10, format "c 'p4@' p").

(** The specification of [readd] against SigmaProtocol's points: the limbs
    at [p_a] represent the extended point [P], the limbs at [p_c] the
    cached coordinates [xprep Q] of the extended point [Q]. The output
    limbs are the image under [phi] of an extended point [S] projectively
    equal to [Ed.xadd P Q]; its affine image is [padd] of those of [P] and
    [Q]. *)
Definition spec_of_readd_sigma : spec_of "readd" :=
  fnspec! "readd"
    (p_out p_a p_c: word) /
    (P Q : SP.xpoint) (a: B.projective_coords) (c: B.cached_coords)
    (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * c p4@ p_c * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        B.feval_projective_coords a = phi5 (proj1_sig P) /\
        B.feval_cached_coords c = phi4 (xprep Q);
      ensures t' m' :=
        t = t' /\
        exists a_plus_c : B.projective_coords,
          m' =* a_plus_c p5@ p_out * a p5@ p_a * c p4@ p_c * R /\
          exists S : SP.xpoint,
            B.feval_projective_coords a_plus_c = phi5 (proj1_sig S) /\
            SXeq S (SP.xadd P Q) /\
            SP.to_affine S = SP.padd (SP.to_affine P) (SP.to_affine Q)
    }.

(** Spec-level implication: AUCurves' [spec_of_readd64] implies the
    SigmaProtocol-facing specification. *)
Lemma readd_spec_sigma functions :
  B.spec_of_readd64 functions -> spec_of_readd_sigma functions.
Proof.
  intros H p_out p_a p_c P Q a c out R t m (Hm & Hlen & Ha & Hc).
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (H p_out p_a p_c a c out R t m (conj Hm Hlen)) ].
  intros t' m' rets (Hrets & Ht & apc & Hm' & Heq).
  split; [exact Hrets |].
  split; [exact Ht |].
  exists apc; split; [exact Hm' |].
  assert (hA : AXeq (B.coords_to_point apc) (phiX (SP.xadd P Q)))
    by (eapply readd_transport with (A := B.coords_to_point a)
          (C := B.cached_coords_to_cached c); [exact Ha | exact Hc | exact Heq]).
  assert (hS : SXeq (psiX (B.coords_to_point apc)) (SP.xadd P Q)).
  { apply SXeq_of_AXeq; eapply AXeq_coords; [ | reflexivity | exact hA ].
    symmetry; apply phiX_psiX. }
  exists (psiX (B.coords_to_point apc)).
  split; [symmetry; exact (phiX_psiX (B.coords_to_point apc)) |].
  split; [exact hS | exact (readd_affine _ _ _ hS)].
Qed.

(** [ed25519_exec_readd]: under the hypotheses of AUCurves' [readd64_ok]
    (the environment maps "readd" to the bedrock2 function, and the field
    operations it calls meet their specifications), a call of [readd]
    satisfies [spec_of_readd_sigma]. *)
Theorem ed25519_exec_readd functions :
  map.get functions "readd" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.readd ->
  B.spec_of_fe25519_sub64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  B.spec_of_fe25519_add64 functions ->
  spec_of_readd_sigma functions.
Proof.
  intros Henv Hsub Hmul Hadd.
  apply readd_spec_sigma.
  pose proof B.readd64_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; assumption.
Qed.

(** The group-level reading: if [P] and [Q] represent the subgroup
    elements [g] and [h], the point [S] of [spec_of_readd_sigma]
    represents [Ed.gop g h]. *)
Corollary ed25519_exec_readd_gop (g h : SP.G) (P Q S : SP.xpoint) :
  SP.to_affine P = proj1_sig g -> SP.to_affine Q = proj1_sig h ->
  SXeq S (SP.xadd P Q) -> SP.to_affine S = proj1_sig (SP.gop g h).
Proof. apply readd_gop. Qed.

Print Assumptions ed25519_exec_readd.
Print Assumptions ed25519_exec_readd_gop.
