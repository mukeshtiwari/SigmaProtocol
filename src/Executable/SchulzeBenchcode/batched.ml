(* Benchmark of the batched Schulze ballot (Frontend/SchulzeBatched.v) at the 2048-bit Helios parameters: ballot encryption with
   the linear proof and the two zero arguments, and verification, for m
   candidates. The commitment keys are hashed to the order-q subgroup.
   Usage: batched.exe m iterations *)
open SchulzeBenchlib.SchulzeBenchIns
open Hacl_star.Hacl.Keccak
module VectorDef = SchulzeBenchlib.VectorDef
module SB = SchulzeBenchlib.SchulzeBatched
module LS = SchulzeBenchlib.LinearSigma
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
let oracle (l : (Z.t, Z.t) SB.b2_item list) : Z.t =
  let item = function
    | SB.B2G x -> "G" ^ z x | SB.B2F x -> "F" ^ z x | SB.B2N k -> "N" ^ z k in
  big_int_of_bytes_mod (shake256 ~msg:(Bytes.of_string (String.concat "," (List.map item l))) ~size:32) q

(* ---- sizes: (group elements, field elements) ---- *)

let size_zero (za : (Z.t, Z.t) BG.zero_argument) =
  (2 + List.length za.za_cd, List.length za.za_a + List.length za.za_b + 3)

let size_ballot2 (b : (Z.t, Z.t) SB.ballot2) =
  let (ga, fa) = (List.length (vector_to_list (fst b.b2_lin.lin_a)), List.length (vector_to_list (snd b.b2_lin.lin_a))) in
  let (g1, f1) = size_zero b.b2_z1 and (g2, f2) = size_zero b.b2_z2 and (g3, f3) = size_zero b.b2_z3 in
  (2 * List.length b.b2_cs + 5 + ga + g1 + g2 + g3, List.length b.b2_lin.lin_z + fa + f1 + f2 + f3)

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
  let kk = toi (coq_K2 n) and nx = toi (coq_NX2 n (big lk)) and w = toi (coq_W2 n (big lk)) in
  Printf.printf "batched Schulze ballot at the Helios parameters: p %d bits, q %d bits, m = %d, L = %d, K = %d, NX = %d, W = %d\n%!"
    (Z.numbits p) (Z.numbits q) m lk kk nx w;
  let (keys, tk) = time_it (fun () ->
    let h1 = hash_to_group "h1" in
    let gs1 = List.init kk (fun i -> hash_to_group (Printf.sprintf "gs1-%d" i)) in
    let gs2 = List.init nx (fun i -> hash_to_group (Printf.sprintf "gs2-%d" i)) in
    (h1, gs1, gs2)) in
  let (h1, gs1, gs2) = keys in
  Printf.printf "commitment keys (%d generators, hashed to the group): %.1f s\n%!" (1 + kk + nx) tk;
  let zeros k = List.init k (fun _ -> Z.zero) in
  let chal0 : Z.t SB.chal2 = { SB.ch_beta = zeros kk; ch_g1 = zeros kk; ch_g2 = zeros kk;
    ch_c = Z.zero; ch_y1 = Z.zero; ch_x1 = Z.zero; ch_y2 = Z.zero; ch_x2 = Z.zero; ch_y3 = Z.zero; ch_x3 = Z.zero } in
  let enc_times = ref [] and ver_times = ref [] and ok = ref true and size = ref (0, 0) in
  for _ = 1 to iters do
    let sn = List.init m (fun _ -> big (random_int (m + 1))) in
    let rd : Z.t SB.rand2 = {
      SB.rd_r = random_list kk; rd_rs = random_field (); rd_rd = random_field (); rd_rb = random_field ();
      rd_rp = random_field (); rd_rX = random_field (); rd_a = random_list w;
      rd_a1 = random_list kk; rd_b1 = random_list kk; rd_r1 = random_field (); rd_s1 = random_field ();
      rd_t1 = random_list 3; rd_u1 = random_list 1;
      rd_a2 = random_list nx; rd_b2 = random_list nx; rd_r2 = random_field (); rd_s2 = random_field ();
      rd_t2 = random_list 2; rd_u2 = [];
      rd_a3 = random_list kk; rd_b3 = random_list kk; rd_r3 = random_field (); rd_s3 = random_field ();
      rd_t3 = random_list 2; rd_u3 = [] } in
    (* the three passes of the Fiat–Shamir prover; the last is the prover's cost *)
    let b0 = encrypt_ballot2_bench n (big lk) h1 gs1 gs2 chal0 sn rd in
    let ch1 = challenges2_bench n oracle b0 in
    let b1 = encrypt_ballot2_bench n (big lk) h1 gs1 gs2 ch1 sn rd in
    let ch2 = challenges2_bench n oracle b1 in
    let (b2, te) = time_it (fun () -> encrypt_ballot2_bench n (big lk) h1 gs1 gs2 ch2 sn rd) in
    let (v, tv) = time_it (fun () -> nizk_verify_ballot2_bench n (big lk) h1 gs1 gs2 oracle b2) in
    ok := !ok && v; size := size_ballot2 b2;
    enc_times := te :: !enc_times; ver_times := tv :: !ver_times
  done;
  (* tampering: the verifier must reject a changed ciphertext (the random
     linear combination no longer matches the committed bits) and a changed
     commitment *)
  let sn = List.init m (fun _ -> big (random_int (m + 1))) in
  let rd : Z.t SB.rand2 = {
    SB.rd_r = random_list kk; rd_rs = random_field (); rd_rd = random_field (); rd_rb = random_field ();
    rd_rp = random_field (); rd_rX = random_field (); rd_a = random_list w;
    rd_a1 = random_list kk; rd_b1 = random_list kk; rd_r1 = random_field (); rd_s1 = random_field ();
    rd_t1 = random_list 3; rd_u1 = random_list 1;
    rd_a2 = random_list nx; rd_b2 = random_list nx; rd_r2 = random_field (); rd_s2 = random_field ();
    rd_t2 = random_list 2; rd_u2 = [];
    rd_a3 = random_list kk; rd_b3 = random_list kk; rd_r3 = random_field (); rd_s3 = random_field ();
    rd_t3 = random_list 2; rd_u3 = [] } in
  let b0 = encrypt_ballot2_bench n (big lk) h1 gs1 gs2 chal0 sn rd in
  let b1 = encrypt_ballot2_bench n (big lk) h1 gs1 gs2 (challenges2_bench n oracle b0) sn rd in
  let b2 = encrypt_ballot2_bench n (big lk) h1 gs1 gs2 (challenges2_bench n oracle b1) sn rd in
  let gg = HT.g in
  let mulg x = Big_int_Z.mod_big_int (Big_int_Z.mult_big_int x gg) p in
  let tampered_cs = match b2.b2_cs with (c1, c2) :: rest -> (c1, mulg c2) :: rest | [] -> [] in
  Printf.printf "  honest ballot verifies: %b; ciphertext (0,0) times Enc(1;0) verifies: %b; C_b times g verifies: %b\n%!"
    (nizk_verify_ballot2_bench n (big lk) h1 gs1 gs2 oracle b2)
    (nizk_verify_ballot2_bench n (big lk) h1 gs1 gs2 oracle { b2 with SB.b2_cs = tampered_cs })
    (nizk_verify_ballot2_bench n (big lk) h1 gs1 gs2 oracle { b2 with SB.b2_Cb = mulg b2.b2_Cb });
  let (gel, fel) = !size in
  Printf.printf "ballot (%d iterations, all verified = %b)\n" iters !ok;
  Printf.printf "  encryption + proofs (one prover pass): median %.2f s\n" (median !enc_times);
  Printf.printf "  verification:                          median %.2f s\n" (median !ver_times);
  Printf.printf "  size: %d group elements, %d field elements, %.1f KB\n%!" gel fel (kb !size)
