(** * The approval ballot extracted to λ□ for Peregrine's C backend

    Each program builds the fixed 7-candidate ballot (encryption and 0-or-1
    proofs) and verifies it. The [*_verify] programs must print [true]; the
    [*_forged] programs swap the two components of every ciphertext, so the
    proofs no longer match and the verifier must print [false]. Every entry
    point reads its result in a [match], so that Peregrine's dead-code
    elimination keeps the computation. *)
From Stdlib Require Import ZArith Vector.
From Examples Require Import WasmBenchSmallDefs.
From Bench Require Import Helios2048Defs.
From Peregrine.Plugin Require Import Loader.

(** Swap the two components of every ciphertext of a ballot. *)
Definition swap_ballot {G P : Type} {n : nat} (b : Vector.t (G * G * P) n) :
  Vector.t (G * G * P) n :=
  Vector.map (fun x => match x with (c1, c2, pf) => (c2, c1, pf) end) b.

Definition small64_verify : bool :=
  if Small64.ballot_verify_bench then true else false.
Definition small128_verify : bool :=
  if Small128.ballot_verify_bench then true else false.
Definition small256_verify : bool :=
  if Small256.ballot_verify_bench then true else false.
Definition helios2048_verify : bool :=
  if Helios2048.ballot_verify_bench then true else false.

Definition small64_forged : bool :=
  if Small64.small_verify_encryption_ballot_proof (swap_ballot Small64.ballot_bench)
  then true else false.
Definition helios2048_forged : bool :=
  if Helios2048.small_verify_encryption_ballot_proof (swap_ballot Helios2048.ballot_bench)
  then true else false.

Peregrine Extract "small64_verify.ast" small64_verify.
Peregrine Extract "small128_verify.ast" small128_verify.
Peregrine Extract "small256_verify.ast" small256_verify.
Peregrine Extract "helios2048_verify.ast" helios2048_verify.
Peregrine Extract "small64_forged.ast" small64_forged.
Peregrine Extract "helios2048_forged.ast" helios2048_forged.
