(* Fiat–Shamir binding test for the extracted encryption proof.

   The non-interactive prover [nizk_generalised_construct_encryption_proof_elgamal_real_ins]
   hashes the commitments returned by [construct_encryption_proof_elgamal_commitment_ins]
   and then builds the transcript with [generalised_construct_encryption_proof_elgamal_real_ins].
   For the proof to be a Fiat–Shamir proof, the commitments it hashes must be exactly
   the announcement it publishes, so that a verifier can recompute the challenge from
   the transcript alone. For many random [uscs], this test checks that:
   1. the hashed commitments equal the announcement in the transcript,
   2. recomputing the hash from the transcript gives the transcript's main challenge,
   3. the Rocq verifier accepts. *)

open EncProoflib
open EncProoflib.EncProofIns

let rec list_of_vector (v : 'a VectorDef.t) : 'a list =
  match v with
  | VectorDef.Coq_nil -> []
  | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

let rec vector_of_list (l : 'a list) : 'a VectorDef.t =
  match l with
  | [] -> VectorDef.Coq_nil
  | h :: t ->
    VectorDef.Coq_cons (h, Big_int_Z.big_int_of_int (List.length t), vector_of_list t)

let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q

let rng = Cryptokit.Random.device_rng "/dev/urandom"

let rnd_vector (n : int) : Z.t VectorDef.t =
  let buf = Bytes.create 4 in
  vector_of_list (List.init n (fun _ ->
    rng#random_bytes buf 0 4; big_int_of_bytes_mod_q buf q))

(* Same oracle as main.ml: SHAKE-256 over the decimal encoding of every entry. *)
let random_oracle _ (v : (Z.t, (Z.t, Z.t * Z.t) Datatypes.sum) Datatypes.sum VectorDef.t) : Z.t =
  let s = Big_int_Z.string_of_big_int in
  let enc = function
    | Datatypes.Coq_inl z -> s z
    | Datatypes.Coq_inr (Datatypes.Coq_inl z) -> s z
    | Datatypes.Coq_inr (Datatypes.Coq_inr (a, b)) -> s a ^ s b in
  let msg = String.concat "" (List.map enc (list_of_vector v)) in
  big_int_of_bytes_mod_q
    (Hacl_star.Hacl.Keccak.shake256 ~msg:(String.to_bytes msg) ~size:4) q

(* The hash input the prover uses, rebuilt from the published announcement. *)
let challenge_from_transcript (announcement : (Z.t * Z.t) VectorDef.t) : Z.t =
  let open Datatypes in
  let pre = [ Coq_inl p; Coq_inl q; Coq_inr (Coq_inl g); Coq_inr (Coq_inl h);
              Coq_inr (Coq_inl m_UU2080_); Coq_inr (Coq_inl m_UU2081_);
              Coq_inr (Coq_inl m_UU2082_) ] in
  let comms = List.map (fun x -> Coq_inr (Coq_inr x)) (cp :: list_of_vector announcement) in
  random_oracle () (vector_of_list (pre @ comms))

let () =
  let trials = 1000 in
  let bad_comm = ref 0 and bad_chal = ref 0 and bad_verify = ref 0 in
  for _ = 1 to trials do
    let uscs = rnd_vector 5 in
    let hashed = list_of_vector (construct_encryption_proof_elgamal_commitment_ins uscs) in
    let proof = nizk_generalised_construct_encryption_proof_elgamal_real_ins random_oracle uscs in
    let announced = list_of_vector proof.Sigma.announcement in
    if hashed <> announced then incr bad_comm;
    (match list_of_vector proof.Sigma.challenge with
     | c :: _ when Big_int_Z.eq_big_int c (challenge_from_transcript proof.Sigma.announcement) -> ()
     | _ -> incr bad_chal);
    if not (generalised_accepting_encryption_proof_elgamal_ins proof) then incr bad_verify
  done;
  Printf.printf "trials: %d\n" trials;
  Printf.printf "hashed commitments <> announcement: %d\n" !bad_comm;
  Printf.printf "challenge not recomputable from transcript: %d\n" !bad_chal;
  Printf.printf "rejected by verifier: %d\n" !bad_verify;
  if !bad_comm + !bad_chal + !bad_verify > 0 then (print_endline "FAIL"; exit 1)
  else print_endline "PASS"
