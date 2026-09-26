(* The library at Ed25519: Schnorr proofs, Chaum-Pedersen proofs and
   approval-voting ballots (individual 0/1 proofs and the overall proof)
   over the order-l subgroup of Curve25519, with Z/lZ as the scalar field.
   Everything is an instance of the generic definitions; the only
   Ed25519-specific inputs are the vector-space instance
   Ed25519.Ed.ed25519_vspace_fast and the base point Ed25519.Ed.B.

   As everywhere in this development the proofs are interactive: the
   challenges are computed by the OCaml driver (Executable/Ed25519code)
   from the announcements, and the *_ins functions receive them. The
   serialisation helpers at the end expose points and scalars as
   integers so that the driver can hash them. *)

From Stdlib Require Import Utf8 ZArith Zmod Vector Lia.
From Crypto Require Import Sigma ChaumPedersen EncProof.
From Frontend Require Import Approval.
From Curve Require Import Ed25519.
From Utility Require Import Util.
Import VectorNotations.

Section Ed25519Ins.

  Import Ed25519.

  Local Notation F := Zl.F.
  Local Notation G := Ed.G.
  Local Notation l := (2^252 + 27742317777372353535851937790883648493)%Z.

  (* ---------------------------------------------------------------- *)
  (* scalars and points as integers, for the driver                   *)
  (* ---------------------------------------------------------------- *)

  Definition of_Z (z : Z) : F := Zmod.of_Z l z.
  Definition to_Z (k : F) : Z := Zmod.unsigned k.
  Definition point_to_Z (P : G) : Z * Z :=
    (Zmod.unsigned (fst (proj1_sig (proj1_sig P))),
     Zmod.unsigned (snd (proj1_sig (proj1_sig P)))).

  (* the base point, and a keypair *)
  Definition g : G := Ed.B.
  Definition x : F := of_Z 3.
  Definition h : G := Ed.gpow_fast g x.

  (* ---------------------------------------------------------------- *)
  (* Schnorr: knowledge of x with h = g^x                              *)
  (* ---------------------------------------------------------------- *)

  Definition schnorr_protocol_commitment_ins (u : F) : G :=
    @schnorr_protocol_commitment F G Ed.gpow_fast g u.

  Definition schnorr_protocol_construction_ins (u c : F) :
    @sigma_proto F G 1 1 1 :=
    @schnorr_protocol F Zl.add Zl.mul G Ed.gpow_fast x g u c.

  Definition schnorr_protocol_verification_ins
    (t : @sigma_proto F G 1 1 1) : bool :=
    @accepting_conversation F G Ed.gop Ed.gpow_fast Ed.Gdec g h t.

  (* ---------------------------------------------------------------- *)
  (* Chaum-Pedersen: c₁ = g^x ∧ c₂ = h^x                                *)
  (* ---------------------------------------------------------------- *)

  Definition c₁ : G := Ed.gpow_fast g x.
  Definition c₂ : G := Ed.gpow_fast h x.

  Definition construct_cp_conversations_schnorr_commitment_ins (u : F) :
    Vector.t G 2 :=
    @construct_cp_conversations_schnorr_commitment F G Ed.gpow_fast g h u.

  Definition construct_cp_conversations_schnorr_ins (u c : F) :
    @sigma_proto F G 2 1 1 :=
    @construct_cp_conversations_schnorr F Zl.add Zl.mul G Ed.gpow_fast x g h u c.

  Definition generalised_cp_accepting_conversations_ins
    (t : @sigma_proto F G 2 1 1) : bool :=
    @generalised_cp_accepting_conversations F G Ed.gop Ed.gpow_fast Ed.Gdec
      g h c₁ c₂ t.

  (* ---------------------------------------------------------------- *)
  (* Approval voting: ElGamal ballots with 0/1 proofs and the overall  *)
  (* proof, as in ApprovalIns.v                                        *)
  (* ---------------------------------------------------------------- *)

  Definition encrypt_ballot_ins {n : nat} (rs ms : Vector.t F n) :
    Vector.t (G * G) n :=
    @encrypt_ballot F G Ed.gop Ed.gpow_fast n g h rs ms.

  Definition generate_ballot_commitment_ins {n : nat}
    (rs ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n) :
    Vector.t (Vector.t (G * G) 2) n :=
    @generate_ballot_commitment F Zl.zero Zl.one Zl.opp Zl.Fdec
      G Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs.

  Definition encrypt_ballot_and_generate_enc_proof_ins {n : nat}
    (rs ms : Vector.t F n) (uscs : Vector.t (Vector.t F 3) n)
    (c : Vector.t F n) :
    Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n :=
    @encrypt_ballot_and_generate_enc_proof F Zl.zero Zl.one Zl.add Zl.mul
      Zl.sub Zl.opp Zl.Fdec G Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs c.

  Definition verify_encryption_ballot_proof_ins {n : nat}
    (proof : Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n) : bool :=
    @verify_encryption_ballot_proof F Zl.zero Zl.one Zl.add Zl.Fdec
      G Ed.ginv Ed.gop Ed.gpow_fast Ed.Gdec n g h proof.

  Definition generate_overall_proof_ins {n : nat}
    (rs ms : Vector.t F (S n)) (uscs : Vector.t F ((2 + n) + (1 + n))) (c : F) :
    @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n) :=
    @generate_overall_proof F Zl.zero Zl.one Zl.add Zl.mul Zl.sub Zl.opp Zl.Fdec
      G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast n g h rs ms uscs c.

  Definition verify_overall_proof_ins {n : nat}
    (cps : Vector.t (G * G) n)
    (pf : @sigma_proto F (G * G) (S n) (S (S n)) (S n)) : bool :=
    @verify_overall_proof F Zl.zero Zl.add Zl.Fdec
      G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast Ed.Gdec n g h cps pf.

  Definition verify_ballot_ins {n : nat}
    (b : Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) n *
         @sigma_proto F (G * G) (S n) (S (S n)) (S n)) : bool :=
    @verify_ballot F Zl.zero Zl.one Zl.add Zl.Fdec
      G Ed.gid Ed.ginv Ed.gop Ed.gpow_fast Ed.Gdec n g h b.

  (* the announcements of a ballot, flattened for the random oracle *)
  Definition vector_unfold : ∀ {n : nat}, Vector.t (Vector.t (G * G) 2) n ->
    Vector.t G (4 * n).
  Proof.
    refine
    (fix fn {n : nat} (v : Vector.t (Vector.t (G * G) 2) n) :
      Vector.t G (4 * n) :=
      match v as v' in Vector.t _ n' return Vector.t G (4 * n') with
      | [] =>  []
      | @Vector.cons _ vh nt vt =>
         let ret := fn vt in _
      end).
    assert (ha : 4 * S nt = 4 + 4 * nt) by nia.
    rewrite ha; clear ha.
    destruct (vector_inv_S vh) as ((vha, vhb) & vht & _).
    destruct (vector_inv_S vht) as ((vhta, vhtb) & _ & _).
    exact (vha :: vhb :: vhta :: vhtb :: ret).
  Defined.

  Definition announcement_to_list {k : nat} (a : Vector.t (G * G) k) : list G :=
    Vector.fold_right (fun '(u, v) acc => (u :: v :: acc)%list) a List.nil.

  (* Non-interactive ballot. fn returns the n challenges of the individual
    proofs from the public parameters and their announcements; fo returns
    the challenge of the overall proof from the public parameters and its
    announcement, which does not depend on the challenge (so it is computed
    first with the challenge zero). *)
  Definition nizk_encrypt_ballot_with_overall_proof_ins {n : nat}
    (fn : ∀ {m : nat}, Vector.t G m -> Vector.t F (S n))
    (fo : ∀ {m : nat}, Vector.t G m -> F)
    (rs ms : Vector.t F (S n))
    (uscs : Vector.t (Vector.t F 3) (S n))
    (uscs' : Vector.t F ((2 + n) + (1 + n))) :
    Vector.t (G * G * @sigma_proto F (G * G) 2 3 2) (S n) *
    @sigma_proto F (G * G) (2 + n) (1 + (2 + n)) (2 + n) :=
    let comm := generate_ballot_commitment_ins rs ms uscs in
    let c := fn ([g; h] ++ vector_unfold comm) in
    let b := encrypt_ballot_and_generate_enc_proof_ins rs ms uscs c in
    let pf0 := generate_overall_proof_ins rs ms uscs' Zl.zero in
    let co := fo (Vector.of_list
      ((g :: h :: announcement_to_list (announcement pf0))%list)) in
    (b, generate_overall_proof_ins rs ms uscs' co).

End Ed25519Ins.
