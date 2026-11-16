(* Benchmark of the receipt-free Schulze protocol (Frontend/Schulze.v, 
   Backend/SchulzeTally.v) at the 2048-bit Helios parameters 
   (Examples/SchulzeBenchIns.v): ballot encryption with its NIZK proofs 
   and ballot verification for m candidates, and generation and 
   verification of the tally certificate for N ballots. 
   Usage: main.exe m N iterations *)
open SchulzeBenchlib.SchulzeBenchIns
open Hacl_star.Hacl.Keccak
module VectorDef = SchulzeBenchlib.VectorDef
module Fin = SchulzeBenchlib.Fin
module Sigma = SchulzeBenchlib.Sigma
module Schulze = SchulzeBenchlib.Schulze
module SchulzeTally = SchulzeBenchlib.SchulzeTally
module HeliosTallyIns = SchulzeBenchlib.HeliosTallyIns

let q = HeliosTallyIns.q
let p = HeliosTallyIns.p
let big = Big_int_Z.big_int_of_int
let z = Big_int_Z.string_of_big_int

let rec vector_to_list (v : 'a VectorDef.t) : 'a list =
  match v with
  | VectorDef.Coq_nil -> []
  | VectorDef.Coq_cons (h, _, r) -> h :: vector_to_list r

let rec vector_of_list (l : 'a list) : 'a VectorDef.t =
  match l with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, big (List.length t), vector_of_list t)

let rec fin_of_int (n : int) (i : int) : Fin.t =
  (* element i of Fin.t (S n) *)
  if i = 0 then Fin.F1 (big n) else Fin.FS (big n, fin_of_int (n - 1) (i - 1))

let rec fin_to_int (f : Fin.t) : int =
  match f with
  | Fin.F1 _ -> 0
  | Fin.FS (_, f') -> 1 + fin_to_int f'

(* ---- randomness and random oracles (as in Schulzecode/main.ml) ---- *)

let big_int_of_bytes_mod_q (s : bytes) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q

let rng = Cryptokit.Random.device_rng "/dev/urandom"

let random_field (_ : Big_int_Z.big_int) : Z.t =
  let buf = Bytes.create 40 in
  rng#random_bytes buf 0 40;
  big_int_of_bytes_mod_q buf

(* the trustees' randomness: generate_tally addresses its randomness by 
   slot number and reads a slot several times (encryption, then proof), 
   so the oracle must be a function of the slot: fresh per run, memoised *)
let memo_random_field () : Big_int_Z.big_int -> Z.t =
  let tbl = Hashtbl.create 4096 in
  fun k ->
    match Hashtbl.find_opt tbl k with
    | Some v -> v
    | None -> let v = random_field k in Hashtbl.add tbl k v; v

let random_int (bound : int) : int =
  let buf = Bytes.create 4 in
  rng#random_bytes buf 0 4;
  (Int32.to_int (Bytes.get_int32_le buf 0) land 0x3fffffff) mod bound

let hash_oracle (l : (Z.t * Z.t) list) : Z.t =
  let msg = Bytes.of_string (String.concat "," (List.map (fun (a, b) -> z a ^ ":" ^ z b) l)) in
  big_int_of_bytes_mod_q (shake256 ~msg ~size:32)

let tally_hash_oracle (l : Z.t SchulzeTally.tr_item list) : Z.t =
  let item = function
    | SchulzeTally.TrC (a, b) -> "C" ^ z a ^ ":" ^ z b
    | SchulzeTally.TrG a -> "G" ^ z a
    | SchulzeTally.TrN k -> "N" ^ z k in
  let msg = Bytes.of_string (String.concat "," (List.map item l)) in
  big_int_of_bytes_mod_q (shake256 ~msg ~size:32)

(* ---- sizes: group elements and field elements published ---- *)

let vlen v = List.length (vector_to_list v)

(* (pairs of group elements, single group elements, field elements) *)
let size_proof2 (pf : (Z.t, Z.t * Z.t) Sigma.sigma_proto) =
  (vlen pf.announcement, 0, vlen pf.challenge + vlen pf.response)
let size_proof1 (pf : (Z.t, Z.t) Sigma.sigma_proto) =
  (0, vlen pf.announcement, vlen pf.challenge + vlen pf.response)
let add3 (a, b, c) (a', b', c') = (a + a', b + b', c + c')
let sum3 l = List.fold_left add3 (0, 0, 0) l
let matrix_list m = List.concat_map vector_to_list (vector_to_list m)

let size_ballot (b : (Z.t, Z.t) Schulze.ballot) =
  let (poss, pairs) = b in
  add3
    (sum3 (List.map (fun (_, pf) -> add3 (1, 0, 0) (size_proof2 pf)) (vector_to_list poss)))
    (sum3 (List.map (fun ((_, pfb), pfm) -> 
      add3 (1, 0, 0) (add3 (size_proof2 pfb) (size_proof2 pfm))) (matrix_list pairs)))

let size_tally (pf : (Z.t, Z.t) SchulzeTally.tally_proof) =
  let open SchulzeTally in
  sum3 [
    (List.length (matrix_list pf.tp_encD'), 0, 0);
    sum3 (List.map size_proof1 (matrix_list pf.tp_dec));
    (List.length (matrix_list pf.tp_enc_d), 0, 0);
    (List.length (matrix_list pf.tp_enc_p), 0, 0);
    sum3 (List.map size_proof2 (matrix_list pf.tp_d_range));
    sum3 (List.map size_proof2 (matrix_list pf.tp_defeat));
    sum3 (List.map size_proof2 (matrix_list pf.tp_lower));
    sum3 (List.concat_map (fun m -> List.map size_proof2 (matrix_list m)) (vector_to_list pf.tp_upper));
    sum3 (List.concat_map (fun l -> List.map size_proof2 l) (matrix_list pf.tp_edges));
    sum3 (List.map size_proof2 (vector_to_list pf.tp_winner)) ]

let bytes_of (pairs, singles, scalars) = 
  pairs * 2 * 256 + singles * 256 + scalars * 32

let string_of_size (pairs, singles, scalars) =
  Printf.sprintf "%d group elements, %d field elements, %.1f KB" 
    (2 * pairs + singles) scalars (float_of_int (bytes_of (pairs, singles, scalars)) /. 1024.0)

(* ---- timing ---- *)

let time_it (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  let t1 = Unix.gettimeofday () in
  (r, t1 -. t0)

let median (xs : float list) : float =
  let s = List.sort compare xs in
  let l = List.length s in
  if l mod 2 = 1 then List.nth s (l / 2)
  else (List.nth s (l / 2 - 1) +. List.nth s (l / 2)) /. 2.0

let mean (xs : float list) : float =
  List.fold_left (+.) 0.0 xs /. float_of_int (List.length xs)

(* ---- the benchmark ---- *)

let random_positions (m : int) : Big_int_Z.big_int VectorDef.t =
  (* s_i in [0, m], m = unranked *)
  vector_of_list (List.init m (fun _ -> big (random_int (m + 1))))

let () =
  let m = try int_of_string Sys.argv.(1) with _ -> 3 in
  let nb = try int_of_string Sys.argv.(2) with _ -> 5 in
  let iters = try int_of_string Sys.argv.(3) with _ -> 3 in
  let n = big (m - 1) and n' = big (nb - 1) in
  Printf.printf "Schulze at the Helios parameters: p %d bits, q %d bits, m = %d candidates, N = %d ballots\n%!" 
    (Z.numbits p) (Z.numbits q) m nb;
  (* ballots *)
  let enc_times = ref [] and ver_times = ref [] and ok = ref true and size = ref (0, 0, 0) in
  for _ = 1 to iters do
    let s = random_positions m in
    let (b, te) = time_it (fun () -> nizk_encrypt_ballot_bench n hash_oracle s random_field) in
    let (v, tv) = time_it (fun () -> nizk_verify_ballot_bench n hash_oracle b) in
    ok := !ok && v;
    size := size_ballot b;
    enc_times := te :: !enc_times; ver_times := tv :: !ver_times
  done;
  Printf.printf "ballot (%d iterations, all verified = %b)\n" iters !ok;
  Printf.printf "  encryption + NIZK proofs: median %.2f s, mean %.2f s\n" (median !enc_times) (mean !enc_times);
  Printf.printf "  verification:             median %.2f s, mean %.2f s\n" (median !ver_times) (mean !ver_times);
  Printf.printf "  size: %s\n%!" (string_of_size !size);
  if Array.length Sys.argv > 4 && Sys.argv.(4) = "ballot" then exit 0;
  (* tally: N random ballots' positions, their margins encrypted directly *)
  let positions = List.init nb (fun _ -> random_positions m) in
  let d = margins_bench n positions in
  let w = match winner_bench n d with Some w -> w | None -> fin_of_int (m - 1) 0 in
  let encD = encrypt_margins_bench n d random_field in
  Printf.printf "tally: margins D (row i: D_ij = ballots with i above j)\n";
  List.iter (fun row -> print_endline ("  " ^ String.concat " " (List.map z (vector_to_list row)))) 
    (vector_to_list d);
  Printf.printf "  winner: candidate %d\n%!" (fin_to_int w);
  let (pf, tg) = time_it (fun () -> nizk_generate_tally_bench n n' tally_hash_oracle encD w (memo_random_field ())) in
  Printf.printf "  certificate generation (decryption, closure, proofs): %.2f s\n%!" tg;
  let (v, tv) = time_it (fun () -> nizk_verify_tally_bench n n' tally_hash_oracle encD w pf) in
  Printf.printf "  certificate verification: %.2f s, verified = %b\n" tv v;
  if not v then
    Printf.printf "  checks: %s\n" 
      (String.concat " " (List.map string_of_bool (tally_checks_bench n n' encD w pf)));
  Printf.printf "  certificate size: %s\n%!" (string_of_size (size_tally pf))
