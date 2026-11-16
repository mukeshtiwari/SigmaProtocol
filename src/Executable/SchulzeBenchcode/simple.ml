(* Benchmark of the simplified batched Schulze ballot
   (Frontend/SchulzeSimple.v) at the 2048-bit Helios
   parameters: ballot encryption with the five-row linear proof and the
   single zero argument, and verification, for m candidates. The commitment
   key is hashed to the order-q subgroup; the derived position key g' is
   computed from it by the extracted gd. Usage: simple.exe m iterations *)
open SchulzeBenchlib.SchulzeBenchIns
open Hacl_star.Hacl.Keccak
module VectorDef = SchulzeBenchlib.VectorDef
module SS = SchulzeBenchlib.SchulzeSimple
module BG = SchulzeBenchlib.BayerGroth
module HT = SchulzeBenchlib.HeliosTallyIns

let q = HT.q
let p = HT.p
let big = Big_int_Z.big_int_of_int
let z = Big_int_Z.string_of_big_int
let toi = Big_int_Z.int_of_big_int

let rec vector_to_list (v : 'a VectorDef.t) : 'a list =
  match v with
  | VectorDef.Coq_nil -> []
  | VectorDef.Coq_cons (h, _, r) -> h :: vector_to_list r

(* ---- randomness, hashing ---- *)

let big_int_of_bytes_mod (s : bytes) (md : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8) (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n md

let rng = Cryptokit.Random.device_rng "/dev/urandom"
let random_field () : Z.t =
  let buf = Bytes.create 40 in rng#random_bytes buf 0 40; big_int_of_bytes_mod buf q
let random_list (n : int) : Z.t list = List.init n (fun _ -> random_field ())
let random_int (bound : int) : int =
  let buf = Bytes.create 4 in rng#random_bytes buf 0 4;
  (Int32.to_int (Bytes.get_int32_le buf 0) land 0x3fffffff) mod bound

(* an element of the order-q subgroup from a label: SHAKE-256(label) mod p, raised to (p-1)/q *)
let hash_to_group (label : string) : Z.t =
  let rec go i =
    let msg = Bytes.of_string (Printf.sprintf "%s|%d" label i) in
    let x = big_int_of_bytes_mod (shake256 ~msg ~size:264) p in
    let y = Z.powm x HT.k p in
    if Z.equal y Z.one || Z.equal x Z.zero then go (i + 1) else y in
  go 0

(* the random oracle of the ballot *)
let oracle (l : (Z.t, Z.t) SS.b3_item list) : Z.t =
  let item = function
    | SS.B3G x -> "G" ^ z x | SS.B3F x -> "F" ^ z x | SS.B3N k -> "N" ^ z k in
  big_int_of_bytes_mod (shake256 ~msg:(Bytes.of_string (String.concat "," (List.map item l))) ~size:32) q

(* ---- sizes: (group elements, field elements) ---- *)

let size_zero (za : (Z.t, Z.t) BG.zero_argument) =
  (2 + List.length za.za_cd, List.length za.za_a + List.length za.za_b + 3)

let size_ballot3 (b : (Z.t, Z.t) SS.ballot3) =
  let ga = List.length (vector_to_list b.b3_lin.lin_a) in
  let (gz, fz) = size_zero b.b3_z in
  (2 * List.length b.b3_cs + 3 + List.length b.b3_CX + ga + gz, List.length b.b3_lin.lin_z + fz)

let kb (gel, fel) = float_of_int (gel * 256 + fel * 32) /. 1024.0

(* ---- timing ---- *)

let time_it f = let t0 = Unix.gettimeofday () in let r = f () in (r, Unix.gettimeofday () -. t0)
let median xs = let s = List.sort compare xs in let l = List.length s in
  if l = 0 then 0.0 else if l mod 2 = 1 then List.nth s (l / 2)
  else (List.nth s (l / 2 - 1) +. List.nth s (l / 2)) /. 2.0

let rec log2_ceil (x : int) : int = if x <= 1 then 0 else 1 + log2_ceil ((x + 1) / 2)

let () =
  let m = try int_of_string Sys.argv.(1) with _ -> 3 in
  let iters = try int_of_string Sys.argv.(2) with _ -> 3 in
  let n = big (m - 1) in
  let lk = log2_ceil (m + 1) in
  let kk = toi (coq_K2 n) and w = toi (coq_W3_bench n) and r = toi (coq_R3_bench (big lk)) in
  Printf.printf "simplified batched Schulze ballot at the Helios parameters: p %d bits, q %d bits, m = %d, L = %d, K = %d, W = %d, rows = %d\n%!"
    (Z.numbits p) (Z.numbits q) m lk kk w r;
  let (keys, tk) = time_it (fun () ->
    let h1 = hash_to_group "h1" in
    let gs1 = List.init kk (fun i -> hash_to_group (Printf.sprintf "gs1-%d" i)) in
    (h1, gs1)) in
  let (h1, gs1) = keys in
  let (_, tg) = time_it (fun () -> gd_bench n gs1) in
  Printf.printf "commitment key (%d generators, hashed to the group): %.1f s; derived position key: %.2f s\n%!" (1 + kk) tk tg;
  let zeros k = List.init k (fun _ -> Z.zero) in
  let chal0 : Z.t SS.chal3 = { SS.c3_beta = zeros kk; c3_y = Z.zero; c3_z = Z.zero; c3_c = Z.zero; c3_x = Z.zero } in
  let fresh_rand () : Z.t SS.rand3 = {
    SS.r3_r = random_list kk; r3_rd = random_field (); r3_rb = random_field (); r3_rp = random_field ();
    r3_rX = random_list lk; r3_a = random_list w;
    r3_a0 = random_list kk; r3_bm = random_list kk; r3_r0 = random_field (); r3_sm = random_field ();
    r3_t1 = random_list (r + 1); r3_t2 = random_list (r - 1) } in
  let enc_times = ref [] and ver_times = ref [] and ok = ref true and size = ref (0, 0) in
  for _ = 1 to iters do
    let sn = List.init m (fun _ -> big (random_int (m + 1))) in
    let rd = fresh_rand () in
    (* the three passes of the Fiat–Shamir prover; the last is the prover's cost *)
    let b0 = encrypt_ballot3_bench n (big lk) h1 gs1 chal0 sn rd in
    let ch1 = challenges3_bench n oracle b0 in
    let b1 = encrypt_ballot3_bench n (big lk) h1 gs1 ch1 sn rd in
    let ch2 = challenges3_bench n oracle b1 in
    let (b2, te) = time_it (fun () -> encrypt_ballot3_bench n (big lk) h1 gs1 ch2 sn rd) in
    let (v, tv) = time_it (fun () -> nizk_verify_ballot3_bench n (big lk) h1 gs1 oracle b2) in
    ok := !ok && v; size := size_ballot3 b2;
    enc_times := te :: !enc_times; ver_times := tv :: !ver_times
  done;
  (* tampering: the verifier must reject a changed ciphertext (the random
     linear combination no longer matches the committed bits), a changed
     commitment, and a changed bit commitment (C₀ no longer opens) *)
  let sn = List.init m (fun _ -> big (random_int (m + 1))) in
  let rd = fresh_rand () in
  let b0 = encrypt_ballot3_bench n (big lk) h1 gs1 chal0 sn rd in
  let b1 = encrypt_ballot3_bench n (big lk) h1 gs1 (challenges3_bench n oracle b0) sn rd in
  let b2 = encrypt_ballot3_bench n (big lk) h1 gs1 (challenges3_bench n oracle b1) sn rd in
  let gg = HT.g in
  let mulg x = Big_int_Z.mod_big_int (Big_int_Z.mult_big_int x gg) p in
  let tampered_cs = match b2.b3_cs with (c1, c2) :: rest -> (c1, mulg c2) :: rest | [] -> [] in
  let tampered_cx = match b2.b3_CX with c :: rest -> mulg c :: rest | [] -> [] in
  Printf.printf "  honest ballot verifies: %b; ciphertext (0,0) times Enc(1;0) verifies: %b; C_b times g verifies: %b; C_X(0) times g verifies: %b\n%!"
    (nizk_verify_ballot3_bench n (big lk) h1 gs1 oracle b2)
    (nizk_verify_ballot3_bench n (big lk) h1 gs1 oracle { b2 with SS.b3_cs = tampered_cs })
    (nizk_verify_ballot3_bench n (big lk) h1 gs1 oracle { b2 with SS.b3_Cb = mulg b2.b3_Cb })
    (nizk_verify_ballot3_bench n (big lk) h1 gs1 oracle { b2 with SS.b3_CX = tampered_cx });
  let (gel, fel) = !size in
  Printf.printf "ballot (%d iterations, all verified = %b)\n" iters !ok;
  Printf.printf "  encryption + proofs (one prover pass): median %.2f s\n" (median !enc_times);
  Printf.printf "  verification:                          median %.2f s\n" (median !ver_times);
  Printf.printf "  size: %d group elements, %d field elements, %.1f KB\n%!" gel fel (kb !size)
