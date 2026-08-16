(* Benchmark: ballot encryption + NIZK proof generation and ballot
   verification at the 2048-bit Helios parameters. *)
open HeliosTallylib
open Hacl_star.Hacl.Keccak

let q = HeliosTallyIns.q
let p = HeliosTallyIns.p

let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q

let rng = Cryptokit.Random.device_rng "/dev/urandom"

let rnd_list (q : Z.t) (n : int) : Z.t VectorDef.t =
  let buf = Bytes.create 32 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 32 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

let rec rnd_list_list (q : Z.t) (n : int) (m : int) : (Z.t VectorDef.t) VectorDef.t =
  match m with
  | 0 -> Coq_nil
  | _ -> Coq_cons (rnd_list q n, Big_int_Z.big_int_of_int 0, rnd_list_list q n (m - 1))

(* ballot of 0/1 of length n *)
let generate_valid_ballot (n : int) : Z.t VectorDef.t =
  rnd_list (Big_int_Z.big_int_of_int 2) n

let vector_to_bytes (m : Z.t) (v : (Z.t, Z.t) Datatypes.sum VectorDef.t) : bytes =
  Vector.fold_right
    (fun x acc ->
       let s = match x with
         | Datatypes.Coq_inl xa
         | Datatypes.Coq_inr xa -> Big_int_Z.string_of_big_int xa
       in
       Bytes.cat acc (Bytes.of_string s)) m v Bytes.empty

let rec construct_challenge_vector (n : int) (msg : bytes) : Z.t VectorDef.t =
  match n with
  | 0 -> VectorDef.Coq_nil
  | _ ->
    let start = (n - 1) * 4 in
    let chunk = Bytes.sub msg start 4 in
    let z = big_int_of_bytes_mod_q chunk q in
    VectorDef.Coq_cons (z, Big_int_Z.big_int_of_int (n - 1),
    (construct_challenge_vector (n - 1) msg))

let random_oracle (n : int) (m : Z.t)
  (v : (Z.t, Z.t) Datatypes.sum VectorDef.t) : Z.t VectorDef.t =
  let inp_msg = vector_to_bytes m v in
  let out_msg = shake256 ~msg:inp_msg ~size:(4 * n) in
  construct_challenge_vector n out_msg

let time_it (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  (r, (t1 -. t0) *. 1000.0)

let median (xs : float list) : float =
  let s = List.sort compare xs in
  let l = List.length s in
  if l mod 2 = 1 then List.nth s (l / 2)
  else (List.nth s (l / 2 - 1) +. List.nth s (l / 2)) /. 2.0

let mean (xs : float list) : float =
  List.fold_left (+.) 0.0 xs /. float_of_int (List.length xs)

let () =
  let n = try int_of_string Sys.argv.(1) with _ -> 7 in
  let iters = try int_of_string Sys.argv.(2) with _ -> 30 in
  let enc_times = ref [] and ver_times = ref [] in
  let ok = ref true in
  (* warm-up round, not measured *)
  let _ =
    let ms = generate_valid_ballot n in
    let rs = rnd_list q n in
    let uscs = rnd_list_list q 3 n in
    HeliosFrontendIns.helios_nizk_encrypt_ballot_and_generate_enc_proof
      (Big_int_Z.big_int_of_int n) (random_oracle n)
      HeliosTallyIns.h2024 rs ms uscs
  in
  for _ = 1 to iters do
    let ms = generate_valid_ballot n in
    let rs = rnd_list q n in
    let uscs = rnd_list_list q 3 n in
    let (proof, te) = time_it (fun () ->
      HeliosFrontendIns.helios_nizk_encrypt_ballot_and_generate_enc_proof
        (Big_int_Z.big_int_of_int n) (random_oracle n)
        HeliosTallyIns.h2024 rs ms uscs) in
    let (b, tv) = time_it (fun () ->
      HeliosFrontendIns.helios_verify_encryption_ballot_proof
        (Big_int_Z.big_int_of_int n) HeliosTallyIns.h2024 proof) in
    ok := !ok && b;
    enc_times := te :: !enc_times;
    ver_times := tv :: !ver_times
  done;
  Printf.printf "candidates n = %d, iterations = %d, all ballots verified = %b\n" n iters !ok;
  Printf.printf "ballot encryption + NIZK proofs: median %.2f ms, mean %.2f ms\n"
    (median !enc_times) (mean !enc_times);
  Printf.printf "ballot verification:             median %.2f ms, mean %.2f ms\n"
    (median !ver_times) (mean !ver_times);
  Printf.printf "p bits = %d, q bits = %d\n"
    (Z.numbits p) (Z.numbits q)
