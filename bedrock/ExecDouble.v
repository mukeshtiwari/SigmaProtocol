(** First bridge theorem: AUCurves' bedrock2 [double] computes
    SigmaProtocol's extended-coordinate doubling [Ed.xdouble], read through
    the field isomorphism [phi : Zmod p -> F p] of [FieldTransport]. *)

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

(** The specification of [double] with the postcondition stated against
    SigmaProtocol's [Ed.xdouble]: the input point [a] in memory represents
    the extended point [P] of SigmaProtocol ([feval] of its limbs is [phi]
    of [P]'s coordinates), and the output limbs represent [Ed.xdouble P]. *)
Definition spec_of_double_sigma : spec_of "double" :=
  fnspec! "double"
    (p_out p_a: word) /
    (P : SP.xpoint) (a: B.projective_coords) (out : list byte) (R: _ -> Prop), {
      requires t m :=
        m =* out $@ p_out * a p5@ p_a * R /\
        Datatypes.length out = Z.to_nat (5 * felem_size) /\
        B.feval_projective_coords a = phi5 (proj1_sig P);
      ensures t' m' :=
        t = t' /\
        exists (X Y Z Ta Tb : felem),
          B.valid_projective_coords X Y Z Ta Tb /\
          bounded_by tight_bounds X /\
          bounded_by tight_bounds Y /\
          bounded_by tight_bounds Z /\
          bounded_by loose_bounds Ta /\
          bounded_by loose_bounds Tb /\
          m' =* (FElem p_out X * FElem (p_out.+felem_size) Y *
                 FElem (p_out.+(felem_size+felem_size)) Z *
                 FElem (p_out.+(felem_size+felem_size+felem_size)) Ta *
                 FElem (p_out.+(felem_size+felem_size+felem_size+felem_size)) Tb) *
                a p5@ p_a * R /\
          (feval X, feval Y, feval Z, feval Ta, feval Tb) = phi5 (proj1_sig (SP.xdouble P))
    }.

(** Spec-level implication: AUCurves' [spec_of_double64] implies the
    SigmaProtocol-facing specification. *)
Lemma double_spec_sigma functions :
  B.spec_of_double64 functions -> spec_of_double_sigma functions.
Proof.
  intros H p_out p_a P a out R t m (Hm & Hlen & Ha).
  eapply WeakestPreconditionProperties.Proper_call;
    [ | apply (H p_out p_a a out R t m (conj Hm Hlen)) ].
  intros t' m' rets (Hrets & Ht & X & Y & Z & Ta & Tb & Hv & HX & HY & HZ & HTa & HTb & Hm' & Hc).
  split; [exact Hrets |].
  split; [exact Ht |].
  exists X, Y, Z, Ta, Tb.
  do 7 (split; [assumption |]).
  rewrite <-Hc. apply m1double_transport. exact Ha.
Qed.

(** [ed25519_exec_double]: under the hypotheses of AUCurves' [double64_ok]
    (the environment maps "double" to the bedrock2 function, and the field
    operations it calls meet their specifications), a call of [double]
    satisfies [spec_of_double_sigma]. *)
Theorem ed25519_exec_double functions :
  map.get functions "double" = Some Crypto.Bedrock.End2End.X25519.EdwardsXYZT.double ->
  B.spec_of_fe25519_square64 functions ->
  B.spec_of_fe25519_carry_add64 functions ->
  B.spec_of_fe25519_add64 functions ->
  B.spec_of_fe25519_carry_sub64 functions ->
  B.spec_of_fe25519_sub64 functions ->
  B.spec_of_fe25519_mul64 functions ->
  spec_of_double_sigma functions.
Proof.
  intros Henv Hsq Hcadd Hadd Hcsub Hsub Hmul.
  apply double_spec_sigma.
  pose proof B.double64_ok as H; cbv [ProgramLogic.program_logic_goal_for] in H.
  apply H; assumption.
Qed.

Print Assumptions ed25519_exec_double.
