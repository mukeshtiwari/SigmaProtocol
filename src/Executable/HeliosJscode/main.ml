(* Browser / Node.js benchmark of the certified Helios ballot client:
   ballot encryption + NIZK proof generation, and ballot verification,
   at the 2048-bit Helios parameters, compiled to JavaScript with
   js_of_ocaml. This is the same computation as HeliosBenchcode/main.ml;
   only the platform services differ: randomness comes from Web Crypto
   (crypto.getRandomValues), the random oracle is built from SHA3-256
   (digestif, pure OCaml) instead of SHAKE-256 from HACL-star, and time is
   measured with performance.now (). *)
open HeliosTallylib
open Js_of_ocaml

let q = HeliosTallyIns.q
let p = HeliosTallyIns.p

let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q

(* n random bytes from Web Crypto; falls back to OCaml's PRNG if the
   platform has no crypto object (benchmark timings only). *)
let random_bytes (n : int) : bytes =
  let buf = Bytes.create n in
  (try
    let crypto = Js.Unsafe.get Js.Unsafe.global (Js.string "crypto") in
    let arr = Js.Unsafe.new_obj
      (Js.Unsafe.get Js.Unsafe.global (Js.string "Uint8Array"))
      [| Js.Unsafe.inject n |] in
    ignore (Js.Unsafe.meth_call crypto "getRandomValues" [| Js.Unsafe.inject arr |]);
    for i = 0 to n - 1 do
      Bytes.set buf i (Char.chr ((Js.Unsafe.get arr i : int) land 255))
    done
  with _ ->
    Random.self_init ();
    for i = 0 to n - 1 do Bytes.set buf i (Char.chr (Random.int 256)) done);
  buf

let rnd_list (q : Z.t) (n : int) : Z.t VectorDef.t =
  let rec rnd_list_aux m =
    match m with
    | 0 -> VectorDef.Coq_nil
    | _ ->
      let v = big_int_of_bytes_mod_q (random_bytes 32) q in
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

(* 4 n bytes of hash output: SHA3-256 (msg || i) for i = 0, 1, ... *)
let expand (msg : bytes) (len : int) : bytes =
  let out = Buffer.create len in
  let i = ref 0 in
  while Buffer.length out < len do
    let block = Digestif.SHA3_256.(to_raw_string
      (digest_string (Bytes.to_string msg ^ "|" ^ string_of_int !i))) in
    Buffer.add_string out block;
    incr i
  done;
  Bytes.sub (Buffer.to_bytes out) 0 len

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
  construct_challenge_vector n (expand (vector_to_bytes m v) (4 * n))

let now_ms () : float =
  Js.Unsafe.meth_call
    (Js.Unsafe.get Js.Unsafe.global (Js.string "performance")) "now" [||]

let time_it (f : unit -> 'a) : 'a * float =
  let t0 = now_ms () in
  let r = f () in
  let t1 = now_ms () in
  (r, t1 -. t0)

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
