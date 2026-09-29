(* The Belenios verifier (Backend/BeleniosTally.v) at Ed25519, the group
   used by Belenios 3.x. The hash functions of Belenios (SHA-256 over its
   serialisation of points and strings) are computed by the driver
   (Executable/Beleniosverifier) and passed in through the ballot_hashes
   and trustee_hashes records. *)

From Stdlib Require Import Utf8 ZArith Zmod List.
From Backend Require Import BeleniosTally.
From Utility Require Import Util.
From Curve Require Import Ed25519.
From Examples Require Import Ed25519Ins.

Section BeleniosIns.

  Import Ed25519.

  Local Notation F := Zl.F.
  Local Notation G := Ed.G.

  (* the types, at Ed25519 *)
  Definition proof := @proof F.
  Definition ciphertext := @ciphertext G.
  Definition question := question.
  Definition answer := @answer F G.
  Definition ballot := @ballot F G.
  Definition ballot_hashes := @ballot_hashes F G.
  Definition election := @election F G.
  Definition trustee := @trustee F G.
  Definition trustee_hashes := @trustee_hashes F G.

  Definition mk_question := mk_question.
  Definition mk_answer := @mk_answer F G.
  Definition mk_ballot := @mk_ballot F G.
  Definition mk_ballot_hashes := @mk_ballot_hashes F G.
  Definition mk_election := @mk_election F G.
  Definition mk_trustee := @mk_trustee F G.
  Definition mk_trustee_hashes := @mk_trustee_hashes F G.

  Definition verify_ballot_ins (E : election) (hs : ballot_hashes) (b : ballot) : bool :=
    verify_ballot (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
      (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec) 
      E hs b.

  Definition encrypted_tally_ins (E : election) (bs : list ballot) : list (list ciphertext) :=
    encrypted_tally (zero := Zl.zero) (gid := Ed.gid) (gop := Ed.gop) (gpow := Ed.gpow_fast) 
      (Gdec := Ed.Gdec) E bs.

  Definition last_per_credential_ins (bs : list ballot) : list ballot :=
    last_per_credential (Gdec := Ed.Gdec) bs.

  Definition compute_final_count_ins (E : election) (hs : ballot -> ballot_hashes)
    (th : trustee_hashes) (bs : list ballot) (published : list (list ciphertext))
    (trs : list trustee) (result : list (list F)) :
    existsT (vbs inbs : list ballot) (bfinal : bool), 
      count (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
        (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec)
        E hs (finished (List.rev bs) vbs inbs bfinal) :=
    compute_final_count (zero := Zl.zero) (one := Zl.one) (add := Zl.add) (Fdec := Zl.Fdec)
      (gid := Ed.gid) (ginv := Ed.ginv) (gop := Ed.gop) (gpow := Ed.gpow_fast) (Gdec := Ed.Gdec)
      E hs th bs published trs result.

  (* the base point, for the driver *)
  Definition base : G := Ed.B.

End BeleniosIns.
