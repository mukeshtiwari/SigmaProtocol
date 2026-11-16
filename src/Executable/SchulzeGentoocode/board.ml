(* Shared by encrypt.ml (the voters) and main.ml (the verifier and the
   trustees): the instance at the 2048-bit Helios parameters, randomness,
   the random oracles, and the bulletin-board file format. *)
open SchulzeBenchlib.SchulzeBenchIns
open Hacl_star.Hacl.Keccak
module VectorDef = SchulzeBenchlib.VectorDef
module Fin = SchulzeBenchlib.Fin
module Sigma = SchulzeBenchlib.Sigma
module SchulzeTally = SchulzeBenchlib.SchulzeTally
module HeliosTallyIns = SchulzeBenchlib.HeliosTallyIns

let q = HeliosTallyIns.q
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
let rec fin_to_int (f : Fin.t) : int =
  match f with Fin.F1 _ -> 0 | Fin.FS (_, f') -> 1 + fin_to_int f'

(* ---- randomness and oracles ---- *)

let big_int_of_bytes_mod_q (s : bytes) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8) (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q
let rng = Cryptokit.Random.device_rng "/dev/urandom"
let random_field (_ : Big_int_Z.big_int) : Z.t =
  let buf = Bytes.create 40 in rng#random_bytes buf 0 40; big_int_of_bytes_mod_q buf
(* the trustees' prover reads every randomness slot twice (encryption,
   then proof), so its oracle is memoised by slot *)
let memo_random_field () =
  let tbl = Hashtbl.create 4096 in
  fun k -> match Hashtbl.find_opt tbl k with
    | Some v -> v | None -> let v = random_field k in Hashtbl.add tbl k v; v

(* the ballot oracle is bound to the voter: H_v(l) = SHAKE-256(v || l) *)
let hash_oracle_for (vid : string) (l : (Z.t * Z.t) list) : Z.t =
  let msg = Bytes.of_string (vid ^ "|" ^ String.concat "," (List.map (fun (a, b) -> z a ^ ":" ^ z b) l)) in
  big_int_of_bytes_mod_q (shake256 ~msg ~size:32)
let tally_hash_oracle (l : Z.t SchulzeTally.tr_item list) : Z.t =
  let item = function
    | SchulzeTally.TrC (a, b) -> "C" ^ z a ^ ":" ^ z b
    | SchulzeTally.TrG a -> "G" ^ z a | SchulzeTally.TrN k -> "N" ^ z k in
  big_int_of_bytes_mod_q (shake256 ~msg:(Bytes.of_string (String.concat "," (List.map item l))) ~size:32)

(* ---- the positions file (bench/gentoo_leak.py --positions) ----
   line 1: m followed by the candidate names; then one line per ballot
   with the position of every candidate, 0 = first, m = unranked *)

let read_positions file =
  let ic = open_in file in
  let header = String.split_on_char ' ' (String.trim (input_line ic)) in
  let m = int_of_string (List.hd header) and names = List.tl header in
  let rec read acc = match input_line ic with
    | l -> read ((List.map int_of_string (String.split_on_char ' ' (String.trim l))) :: acc)
    | exception End_of_file -> close_in ic; List.rev acc in
  (m, names, read [])

(* ---- the bulletin-board file: decimal numbers separated by spaces ----
   line 1: election <name> m <m> voters <N> candidates <names...>
   then one line per ballot: ballot <voter-id> <m>, the position cell of
   every candidate (ciphertext, membership proof), then for every ordered
   pair (i, j) in row-major order the pair cell (ciphertext, 0/1 proof,
   membership proof). A ciphertext is two numbers; a proof is its three
   vectors, each preceded by its length, announcements being pairs. *)

type ballot = (Z.t, Z.t) SchulzeBenchlib.Schulze.ballot

let write_header (oc : out_channel) (election : string) (m : int) (nv : int) (names : string list) =
  Printf.fprintf oc "election %s m %d voters %d candidates %s\n" election m nv (String.concat " " names)

let write_ballot (oc : out_channel) (vid : string) (m : int) (b : ballot) : unit =
  let add s = output_string oc s; output_char oc ' ' in
  let pair (a, c) = add (z a); add (z c) in
  let proof (pf : (Z.t, Z.t * Z.t) Sigma.sigma_proto) =
    let ann = vector_to_list pf.announcement and ch = vector_to_list pf.challenge
    and rs = vector_to_list pf.response in
    add (string_of_int (List.length ann)); List.iter pair ann;
    add (string_of_int (List.length ch)); List.iter (fun x -> add (z x)) ch;
    add (string_of_int (List.length rs)); List.iter (fun x -> add (z x)) rs in
  add "ballot"; add vid; add (string_of_int m);
  let (poss, pairs) = b in
  List.iter (fun (cp, pf) -> pair cp; proof pf) (vector_to_list poss);
  List.iter (fun row -> List.iter (fun ((cb, pfb), pfm) -> pair cb; proof pfb; proof pfm)
    (vector_to_list row)) (vector_to_list pairs);
  output_char oc '\n'

let ballot_of_line (line : string) : string * int * ballot =
  let toks = Array.of_list (List.filter (fun s -> s <> "") (String.split_on_char ' ' line)) in
  let pos = ref 0 in
  let next () = let t = toks.(!pos) in incr pos; t in
  let num () = Big_int_Z.big_int_of_string (next ()) in
  let int () = int_of_string (next ()) in
  let pair () = let a = num () in let c = num () in (a, c) in
  let vec f = let n = int () in vector_of_list (List.init n (fun _ -> f ())) in
  let proof () : (Z.t, Z.t * Z.t) Sigma.sigma_proto =
    let announcement = vec pair in let challenge = vec num in let response = vec num in
    { Sigma.announcement; challenge; response } in
  if next () <> "ballot" then failwith "bad ballot line";
  let vid = next () in
  let m = int () in
  let poss = vector_of_list (List.init m (fun _ -> let cp = pair () in let pf = proof () in (cp, pf))) in
  let pairs = vector_of_list (List.init m (fun _ ->
    vector_of_list (List.init m (fun _ ->
      let cb = pair () in let pfb = proof () in let pfm = proof () in ((cb, pfb), pfm))))) in
  if !pos <> Array.length toks then failwith "trailing data in ballot line";
  (vid, m, (poss, pairs))

(* the header and the ballots of a bulletin-board file *)
let read_board (file : string) =
  let ic = open_in file in
  let header = String.split_on_char ' ' (String.trim (input_line ic)) in
  let m = int_of_string (List.nth header 3) in
  let names = Array.of_list (List.filteri (fun i _ -> i >= 7) header) in
  let rec read acc = match input_line ic with
    | l -> read (ballot_of_line l :: acc)
    | exception End_of_file -> close_in ic; List.rev acc in
  (m, names, read [])

(* ---- timing ---- *)

let time_it f = let t0 = Unix.gettimeofday () in let r = f () in (r, Unix.gettimeofday () -. t0)
(* wall-clock and processor time of f, for machines whose wall-clock speed varies *)
let time_it2 f = let t0 = Unix.gettimeofday () and c0 = Sys.time () in let r = f () in
  (r, Unix.gettimeofday () -. t0, Sys.time () -. c0)
let median xs = let s = List.sort compare xs in let l = List.length s in
  if l = 0 then 0.0 else if l mod 2 = 1 then List.nth s (l / 2)
  else (List.nth s (l / 2 - 1) +. List.nth s (l / 2)) /. 2.0
let sum xs = List.fold_left (+.) 0.0 xs
