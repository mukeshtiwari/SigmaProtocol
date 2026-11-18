(* Parallel prover for the Schulze certificate (Backend/SchulzeTally.v) at the
   2048-bit Helios parameters (Examples/SchulzeBenchIns.v).

   Usage: par.exe m N workers [onepass] [chunkhash] [check] [noverify] [seed=HEX]

   The certificate is a tally_proof of the extracted library. Its sub-proofs
   (one per cell of each part) do not depend on each other, so this driver
   computes them in `workers` forked processes and assembles the record. The
   sub-proofs themselves come from the extracted functions (prove_range,
   prove_or, edge_proofs, ...), called with exactly the arguments that the
   extracted generate_tally_with gives them. Only the loop over the cells is
   new, and it is not verified. It does not have to be: the result is checked
   by the extracted verifier nizk_verify_tally, whose soundness theorem
   (verify_tally_sound) does not depend on how a certificate was made. With
   `check` the driver also runs the extracted sequential prover on the same
   randomness and tests that the two certificates are equal.

   The trustees' randomness is derived from a fresh seed: slot k gets
   SHAKE-256(seed | k) reduced modulo q. This makes a slot's value the same
   in every worker without sharing a table.

   The Fiat-Shamir oracle is the one of main.ml. By default both passes of
   the prover are run (challenge zero, then the hashed challenge), as in
   the extracted nizk_generate_tally_with. With `onepass` the second pass is
   replaced by a patch: the announcements do not depend on the challenge c,
   and in every sub-proof only the main challenge (0 -> c), the challenge of
   the real branch (+ c) and its response (+ c * witness) change. This
   halves the work. `check` tests the result against the extracted prover
   in this mode too.

   `chunkhash` replaces the oracle by one that hashes the transcript in
   chunks of 4096 items and then hashes the chunk digests. It needs far
   less memory than building the whole transcript as one string, which
   matters for certificates of several gigabytes. *)
open SchulzeBenchlib.SchulzeBenchIns
open Hacl_star.Hacl.Keccak
module VectorDef = SchulzeBenchlib.VectorDef
module Fin = SchulzeBenchlib.Fin
module Sigma = SchulzeBenchlib.Sigma
module Schulze = SchulzeBenchlib.Schulze
module T = SchulzeBenchlib.SchulzeTally
module U = SchulzeBenchlib.Util
module Elgamal = SchulzeBenchlib.Elgamal
module DecProof = SchulzeBenchlib.DecProof
module HeliosTallyIns = SchulzeBenchlib.HeliosTallyIns

let q = HeliosTallyIns.q
let p = HeliosTallyIns.p
let g = HeliosTallyIns.g
let big = Big_int_Z.big_int_of_int
let z = Big_int_Z.string_of_big_int
let succ = Big_int_Z.succ_big_int
let zero_n = Big_int_Z.zero_big_int

let rec vector_to_list (v : 'a VectorDef.t) : 'a list =
  match v with
  | VectorDef.Coq_nil -> []
  | VectorDef.Coq_cons (h, _, r) -> h :: vector_to_list r

let rec vector_of_list (l : 'a list) : 'a VectorDef.t =
  match l with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, big (List.length t), vector_of_list t)

let rec fin_of_int (n : int) (i : int) : Fin.t =
  if i = 0 then Fin.F1 (big n) else Fin.FS (big n, fin_of_int (n - 1) (i - 1))

let rec fin_to_int (f : Fin.t) : int =
  match f with
  | Fin.F1 _ -> 0
  | Fin.FS (_, f') -> 1 + fin_to_int f'

(* ---- randomness and the random oracle (as in main.ml) ---- *)

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

let random_int (bound : int) : int =
  let buf = Bytes.create 4 in
  rng#random_bytes buf 0 4;
  (Int32.to_int (Bytes.get_int32_le buf 0) land 0x3fffffff) mod bound

let hex_of_bytes (b : bytes) : string =
  String.concat "" (List.init (Bytes.length b) (fun i -> Printf.sprintf "%02x" (Char.code (Bytes.get b i))))

(* slot k of the trustees' randomness: a function of (seed, k) only *)
let seeded_field (seed : string) (k : Big_int_Z.big_int) : Z.t =
  big_int_of_bytes_mod_q (shake256 ~msg:(Bytes.of_string (seed ^ "|" ^ z k)) ~size:40)

let tally_hash_oracle (l : Z.t T.tr_item list) : Z.t =
  let item = function
    | T.TrC (a, b) -> "C" ^ z a ^ ":" ^ z b
    | T.TrG a -> "G" ^ z a
    | T.TrN k -> "N" ^ z k in
  let msg = Bytes.of_string (String.concat "," (List.map item l)) in
  big_int_of_bytes_mod_q (shake256 ~msg ~size:32)

(* the same transcript hashed in chunks: SHAKE-256 of the SHAKE-256 digests
   of consecutive chunks of 4096 items *)
let chunked_hash_oracle (l : Z.t T.tr_item list) : Z.t =
  let item = function
    | T.TrC (a, b) -> "C" ^ z a ^ ":" ^ z b
    | T.TrG a -> "G" ^ z a
    | T.TrN k -> "N" ^ z k in
  let buf = Buffer.create (1 lsl 22) and digests = Buffer.create (1 lsl 16) and cnt = ref 0 in
  let flush () =
    if Buffer.length buf > 0 then begin
      Buffer.add_bytes digests (shake256 ~msg:(Buffer.to_bytes buf) ~size:32);
      Buffer.clear buf
    end in
  List.iter (fun it ->
    Buffer.add_string buf (item it); Buffer.add_char buf ',';
    incr cnt; if !cnt land 4095 = 0 then flush ()) l;
  flush ();
  big_int_of_bytes_mod_q (shake256 ~msg:(Buffer.to_bytes digests) ~size:32)

(* ---- sizes (as in main.ml) ---- *)

let vlen v = List.length (vector_to_list v)
let size_proof2 (pf : (Z.t, Z.t * Z.t) Sigma.sigma_proto) =
  (vlen pf.Sigma.announcement, 0, vlen pf.Sigma.challenge + vlen pf.Sigma.response)
let size_proof1 (pf : (Z.t, Z.t) Sigma.sigma_proto) =
  (0, vlen pf.Sigma.announcement, vlen pf.Sigma.challenge + vlen pf.Sigma.response)
let add3 (a, b, c) (a', b', c') = (a + a', b + b', c + c')
let sum3 l = List.fold_left add3 (0, 0, 0) l
let matrix_list m = List.concat_map vector_to_list (vector_to_list m)

let size_tally (pf : (Z.t, Z.t) T.tally_proof) =
  sum3 [
    (List.length (matrix_list pf.T.tp_encD'), 0, 0);
    sum3 (List.map size_proof1 (matrix_list pf.T.tp_dec));
    (List.length (matrix_list pf.T.tp_enc_d), 0, 0);
    (List.length (matrix_list pf.T.tp_enc_p), 0, 0);
    sum3 (List.map size_proof2 (matrix_list pf.T.tp_d_range));
    sum3 (List.map size_proof2 (matrix_list pf.T.tp_defeat));
    sum3 (List.map size_proof2 (matrix_list pf.T.tp_lower));
    sum3 (List.concat_map (fun m -> List.map size_proof2 (matrix_list m)) (vector_to_list pf.T.tp_upper));
    sum3 (List.concat_map (fun l -> List.map size_proof2 l) (matrix_list pf.T.tp_edges));
    sum3 (List.map size_proof2 (vector_to_list pf.T.tp_winner)) ]

let string_of_size (pairs, singles, scalars) =
  Printf.sprintf "%d group elements, %d field elements, %.1f KB"
    (2 * pairs + singles) scalars
    (float_of_int (pairs * 2 * 256 + singles * 256 + scalars * 32) /. 1024.0)

let time_it (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  (r, Unix.gettimeofday () -. t0)

(* ---- running an array of independent tasks in forked workers ---- *)

(* Worker t computes the tasks with index t, t + workers, t + 2 workers, ...
   and writes each result to its own file as it is ready. The parent waits
   for all workers and reads the files back. *)
let par_run (workers : int) (tasks : (unit -> 'a) array) : 'a array =
  let nt = Array.length tasks in
  if workers <= 1 || nt = 0 then Array.map (fun f -> f ()) tasks
  else begin
    let files = Array.init workers (fun _ -> Filename.temp_file "schulze-par-" ".bin") in
    flush_all ();
    let pids = Array.init workers (fun t ->
      match Unix.fork () with
      | 0 ->
        (try
           let oc = open_out_bin files.(t) in
           let i = ref t in
           while !i < nt do
             Marshal.to_channel oc (!i, tasks.(!i) ()) [];
             i := !i + workers
           done;
           close_out oc;
           Unix._exit 0
         with e ->
           prerr_endline ("worker " ^ string_of_int t ^ ": " ^ Printexc.to_string e);
           Unix._exit 1)
      | pid -> pid) in
    let ok = ref true in
    Array.iter (fun pid ->
      match Unix.waitpid [] pid with
      | (_, Unix.WEXITED 0) -> ()
      | _ -> ok := false) pids;
    if not !ok then begin
      Array.iter (fun f -> try Sys.remove f with _ -> ()) files;
      failwith "a worker failed"
    end;
    let res : 'a option array = Array.make nt None in
    Array.iteri (fun t f ->
      let ic = open_in_bin f in
      let i = ref t in
      while !i < nt do
        let (j, v) : int * 'a = Marshal.from_channel ic in
        if j <> !i then failwith "worker output out of order";
        res.(j) <- Some v;
        i := !i + workers
      done;
      close_in ic;
      Sys.remove f) files;
    Array.map (function Some v -> v | None -> failwith "missing worker output") res
  end

(* ---- the certificate, one cell at a time ---- *)

(* A membership or or-proof comes with the index of its real branch and the
   witness of that branch (used by `onepass` only). *)
type pf2 = (Z.t, Z.t * Z.t) Sigma.sigma_proto * int * Z.t
type cell =
  | CDec of (Z.t, Z.t) Sigma.sigma_proto
  | CPf of pf2
  | CEdges of pf2 list

let mapi_vec (f : int -> 'a -> 'a) (v : 'a VectorDef.t) : 'a VectorDef.t =
  vector_of_list (List.mapi f (vector_to_list v))

(* the proof for main challenge c, from the proof for main challenge zero *)
let patch2 (c : Z.t) ((pf, ri, wit) : pf2) : pf2 =
  ({ Sigma.announcement = pf.Sigma.announcement;
     challenge = mapi_vec (fun i ch -> if i = 0 then c else if i = ri + 1 then coq_Fadd ch c else ch) pf.Sigma.challenge;
     response = mapi_vec (fun i r -> if i = ri then coq_Fadd r (coq_Fmul c wit) else r) pf.Sigma.response },
   ri, wit)

let patch_cell (c : Z.t) (cell : cell) : cell =
  match cell with
  | CDec pf ->
    CDec { Sigma.announcement = pf.Sigma.announcement;
           challenge = mapi_vec (fun _ _ -> c) pf.Sigma.challenge;
           response = mapi_vec (fun _ r -> coq_Fadd r (coq_Fmul c x)) pf.Sigma.response }
  | CPf p -> CPf (patch2 c p)
  | CEdges l -> CEdges (List.map (patch2 c) l)

(* One pass of the prover for the challenge `chal`. Every cell below is the
   corresponding cell of the extracted generate_tally_with, with the same
   slot numbers (tags 0, 1, 3, 4, 5, 7, 9, 11, 13, 15). *)
let tally_cells (n : Big_int_Z.big_int) (n' : Big_int_Z.big_int)
    (encD : (Z.t * Z.t) VectorDef.t VectorDef.t)
    (d : Fin.t -> Fin.t -> Big_int_Z.big_int) (pm : Fin.t -> Fin.t -> Big_int_Z.big_int)
    (paths : Fin.t -> Fin.t -> Fin.t list) (w : Fin.t)
    (rnd : Big_int_Z.big_int -> Z.t) (chal : Z.t)
    : (unit -> cell) array * (cell array -> (Z.t, Z.t) T.tally_proof) =
  let zero = coq_Fzero and one = coq_Fone and add0 = coq_Fadd and mul0 = coq_Fmul
  and sub0 = coq_Fsub and opp0 = coq_Fopp and ginv = coq_Ginv and gop = coq_Gmul
  and gpow = coq_Gpow in
  let sn = succ n and sn' = succ n' in
  let m = Big_int_Z.int_of_big_int sn in
  let fins = Array.of_list (vector_to_list (U.fin_enum sn)) in
  let idx f = U.fin_idx sn f in
  let natF k = U.nat_to_F zero one add0 k in
  let add = Big_int_Z.add_big_int in
  let d0 = T.defeat sn d in
  let k = natF (T.tally_shift sn') in
  let slot tag i j e = T.slot n n' (big tag) i j e in
  let rD i j = rnd (slot 0 (idx i) (idx j) zero_n) in
  let rd i j = rnd (slot 3 (idx i) (idx j) zero_n) in
  let rp i j = rnd (slot 4 (idx i) (idx j) zero_n) in
  let mget mx i j = T.mget sn mx i j in
  (* the 3 m^2 fresh ciphertexts are cheap and are needed by every worker *)
  let encD' = T.mat_of n (fun i j -> Elgamal.enc gop gpow g h (natF (T.nat_of_Z (d i j))) (rD i j)) in
  let enc_d = T.mat_of n (fun i j -> Elgamal.enc gop gpow g h (natF (T.nat_of_Z (d0 i j))) (rd i j)) in
  let enc_p = T.mat_of n (fun i j -> Elgamal.enc gop gpow g h (natF (T.nat_of_Z (pm i j))) (rp i j)) in
  (* lengths of the randomness vectors: (2 + k) + (1 + k) for a k+2 branch proof *)
  let len_range = add (add (big 2) n') (add (big 1) n') in
  let kd = add n' sn' in
  let len_defeat = add (add (big 2) kd) (add (big 1) kd) in
  let ku = add n' (succ sn') in
  let len_upper = add (add (big 2) ku) (add (big 1) ku) in
  let range v r uscs cp =
    (T.prove_range zero one add0 mul0 sub0 opp0 ginv gop gpow n' g h v r uscs cp chal,
     fin_to_int (U.fin_of_nat_default (T.nat_of_Z v) sn'), r) in
  let prove_or kk ri r hs uscs =
    (T.prove_or zero add0 mul0 sub0 opp0 gop gpow g h kk ri r hs uscs chal, fin_to_int ri, r) in
  let dec_cell i j () =
    let c = Schulze.cmul gop (mget encD' i j) (Schulze.cinv ginv (mget encD i j)) in
    CDec (DecProof.construct_decryption_proof_elgamal_real add0 mul0 gpow x g c
            (rnd (slot 1 (idx i) (idx j) zero_n)) chal) in
  let d_range_cell i j () =
    CPf (range (d0 i j) (rd i j) (T.rvec rnd (slot 5 (idx i) (idx j) zero_n) len_range) (mget enc_d i j)) in
  let defeat_cell i j () =
    let delta = Z.sub (d i j) (d j i) in
    let rdelta = sub0 (rD i j) (rD j i) in
    let hs = T.defeat_statements zero one add0 ginv gop gpow sn sn' g encD' enc_d i j in
    let uscs = T.rvec rnd (slot 7 (idx i) (idx j) zero_n) len_defeat in
    if Z.lt Z.zero delta
    then CPf (prove_or kd
                (U.fin_of_nat_default (add sn' (T.nat_of_Z delta)) (add sn' sn'))
                (add0 (mul0 k (sub0 (rd i j) (rD i j))) rdelta) hs uscs)
    else CPf (prove_or kd
                (U.fin_of_nat_default (T.nat_of_Z (Z.neg delta)) (add sn' sn'))
                (add0 (mul0 k (rd i j)) rdelta) hs uscs) in
  let lower_cell i j () =
    CPf (range (Z.sub (pm i j) (d0 i j)) (sub0 (rp i j) (rd i j))
           (T.rvec rnd (slot 9 (idx i) (idx j) zero_n) len_range)
           (Schulze.cmul gop (mget enc_p i j) (Schulze.cinv ginv (mget enc_d i j)))) in
  let upper_cell k0 i j () =
    let hs = T.upper_statements zero one add0 ginv gop gpow sn sn' g enc_p k0 i j in
    let uscs = T.rvec rnd (slot 11 (idx i) (idx j) (idx k0)) len_upper in
    if Z.leq (pm i k0) (pm i j)
    then CPf (prove_or ku
                (U.fin_of_nat_default (T.nat_of_Z (Z.sub (pm i j) (pm i k0))) (add sn' (succ sn')))
                (sub0 (rp i j) (rp i k0)) hs uscs)
    else CPf (prove_or ku
                (U.fin_of_nat_default (add (succ sn') (T.nat_of_Z (Z.sub (pm i j) (pm k0 j)))) (add sn' (succ sn')))
                (sub0 (rp i j) (rp k0 j)) hs uscs) in
  let edges_cell i j () =
    match paths i j with
    | [] -> CEdges []
    | u :: l ->
      let pfs = T.edge_proofs zero one add0 mul0 sub0 opp0 ginv gop gpow n n' g h d0 pm
                  enc_d enc_p rd rp rnd chal i j u l zero_n in
      (* the value and the randomness of each edge, as edge_proofs takes them *)
      let rec hints u l = match l with
        | [] -> []
        | v :: l' ->
          (fin_to_int (U.fin_of_nat_default (T.nat_of_Z (Z.sub (d0 u v) (pm i j))) sn'),
           sub0 (rd u v) (rp i j)) :: hints v l' in
      CEdges (List.map2 (fun pf (ri, r) -> (pf, ri, r)) pfs (hints u l)) in
  let winner_cell j () =
    CPf (range (Z.sub (pm w j) (pm j w)) (sub0 (rp w j) (rp j w))
           (T.rvec rnd (slot 15 (idx j) zero_n zero_n) len_range)
           (Schulze.cmul gop (mget enc_p w j) (Schulze.cinv ginv (mget enc_p j w)))) in
  (* the tasks: the m^3 closure disjunctions first, then the other parts *)
  let m2 = m * m in
  let o_upper = 0 in
  let o_dec = o_upper + m * m2 in
  let o_range = o_dec + m2 in
  let o_defeat = o_range + m2 in
  let o_lower = o_defeat + m2 in
  let o_edges = o_lower + m2 in
  let o_winner = o_edges + m2 in
  let nt = o_winner + m in
  let tasks : (unit -> cell) array = Array.init nt (fun t ->
    if t < o_dec then
      let k0 = t / m2 and r = t mod m2 in upper_cell fins.(k0) fins.(r / m) fins.(r mod m)
    else if t < o_range then let r = t - o_dec in dec_cell fins.(r / m) fins.(r mod m)
    else if t < o_defeat then let r = t - o_range in d_range_cell fins.(r / m) fins.(r mod m)
    else if t < o_lower then let r = t - o_defeat in defeat_cell fins.(r / m) fins.(r mod m)
    else if t < o_edges then let r = t - o_lower in lower_cell fins.(r / m) fins.(r mod m)
    else if t < o_winner then let r = t - o_edges in edges_cell fins.(r / m) fins.(r mod m)
    else winner_cell fins.(t - o_winner)) in
  let assemble (res : cell array) : (Z.t, Z.t) T.tally_proof =
    let ij off i j = res.(off + fin_to_int i * m + fin_to_int j) in
    let pf_of = function CPf (x, _, _) -> x | _ -> failwith "cell: expected a membership or or-proof" in
    let dec_of = function CDec x -> x | _ -> failwith "cell: expected a decryption proof" in
    let edges_of = function CEdges l -> List.map (fun (x, _, _) -> x) l | _ -> failwith "cell: expected edge proofs" in
    { T.tp_encD' = encD';
      tp_dec = T.mat_of n (fun i j -> dec_of (ij o_dec i j));
      tp_enc_d = enc_d;
      tp_enc_p = enc_p;
      tp_d_range = T.mat_of n (fun i j -> pf_of (ij o_range i j));
      tp_defeat = T.mat_of n (fun i j -> pf_of (ij o_defeat i j));
      tp_lower = T.mat_of n (fun i j -> pf_of (ij o_lower i j));
      tp_upper = vector_of_list (List.init m (fun k0 ->
        T.mat_of n (fun i j -> pf_of (res.(o_upper + k0 * m2 + fin_to_int i * m + fin_to_int j)))));
      tp_paths = T.mat_of n paths;
      tp_edges = T.mat_of n (fun i j -> edges_of (ij o_edges i j));
      tp_winner = vector_of_list (List.init m (fun j -> pf_of res.(o_winner + j))) } in
  (tasks, assemble)

(* ---- the benchmark ---- *)

let random_positions (m : int) : Big_int_Z.big_int VectorDef.t =
  vector_of_list (List.init m (fun _ -> big (random_int (m + 1))))

let () =
  let arg i d = try int_of_string Sys.argv.(i) with _ -> d in
  let m = arg 1 3 and nb = arg 2 5 and workers = arg 3 1 in
  let flags = Array.to_list (Array.sub Sys.argv (min 4 (Array.length Sys.argv)) (max 0 (Array.length Sys.argv - 4))) in
  let check = List.mem "check" flags and verify = not (List.mem "noverify" flags)
  and onepass = List.mem "onepass" flags in
  let oracle = if List.mem "chunkhash" flags then chunked_hash_oracle else tally_hash_oracle in
  let seed =
    match List.find_opt (fun s -> String.length s > 5 && String.sub s 0 5 = "seed=") flags with
    | Some s -> String.sub s 5 (String.length s - 5)
    | None -> let b = Bytes.create 32 in rng#random_bytes b 0 32; hex_of_bytes b in
  let n = big (m - 1) and n' = big (nb - 1) in
  Printf.printf "Schulze certificate, parallel prover: p %d bits, q %d bits, m = %d candidates, N = %d ballots, %d workers, %s\n%!"
    (Z.numbits p) (Z.numbits q) m nb workers (if onepass then "one pass" else "two passes");
  (* N random ballots' positions, their margins encrypted directly (as main.ml) *)
  let positions = List.init nb (fun _ -> random_positions m) in
  let dm = margins_bench n positions in
  let w = match winner_bench n dm with Some w -> w | None -> fin_of_int (m - 1) 0 in
  let encD = encrypt_margins_bench n dm random_field in
  Printf.printf "  winner: candidate %d\n%!" (fin_to_int w);
  let rnd = seeded_field seed in
  let sn = succ n in
  (* the trustees: decryption, closure, paths (sequential), then the proofs *)
  let t0 = Unix.gettimeofday () in
  let d = T.fun_of n (decrypt_margins_bench n n' encD) in
  let d0 = T.defeat sn d in
  let pm = T.minmax_closure sn d0 in
  let paths = T.witness_path sn d0 pm in
  let t1 = Unix.gettimeofday () in
  let (tasks0, assemble) = tally_cells n n' encD d pm paths w rnd coq_Fzero in
  let res0 = par_run workers tasks0 in
  let pf0 = assemble res0 in
  let t2 = Unix.gettimeofday () in
  let chal = oracle (T.tally_transcript n n' encD w pf0) in
  let t3 = Unix.gettimeofday () in
  let pf =
    if onepass then assemble (Array.map (patch_cell chal) res0)
    else let (tasks, assemble) = tally_cells n n' encD d pm paths w rnd chal in
      assemble (par_run workers tasks) in
  let t4 = Unix.gettimeofday () in
  Printf.printf "  decryption, closure, paths: %.2f s\n" (t1 -. t0);
  Printf.printf "  first pass (challenge zero): %.2f s\n" (t2 -. t1);
  Printf.printf "  hashing the transcript:      %.2f s\n" (t3 -. t2);
  Printf.printf "  %s %.2f s\n" (if onepass then "patching the challenge:     " else "second pass:                ") (t4 -. t3);
  Printf.printf "  certificate generation, wall-clock, %d workers: %.2f s\n%!" workers (t4 -. t0);
  let (pairs, _, _) as sz = size_tally pf in
  Printf.printf "  certificate size: %s, %d disjunction branches\n%!" (string_of_size sz) (pairs - 3 * m * m);
  if verify then begin
    let (v, tv) = time_it (fun () -> nizk_verify_tally_bench n n' oracle encD w pf) in
    Printf.printf "  extracted verifier (one process): %.2f s, verified = %b\n%!" tv v;
    if not v then begin
      Printf.printf "  checks: %s\n" (String.concat " " (List.map string_of_bool (tally_checks_bench n n' encD w pf)));
      exit 2
    end
  end;
  if check then begin
    let (pf_seq, ts) = time_it (fun () ->
      T.nizk_generate_tally_with coq_Fzero coq_Fone coq_Fadd coq_Fmul coq_Fsub coq_Fopp
        coq_Ginv coq_Gmul coq_Gpow n n' x g h oracle encD d pm paths w rnd) in
    let same = (pf_seq = pf) in
    Printf.printf "  extracted sequential prover on the same randomness: %.2f s, equal certificate = %b\n%!" ts same;
    if not same then exit 3
  end
