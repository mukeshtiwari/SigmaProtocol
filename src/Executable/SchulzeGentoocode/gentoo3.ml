(* A Gentoo council election through the simplified batched ballot
   (Frontend/SchulzeSimple.v) at the 2048-bit Helios
   parameters, voters and verifier in one process (a ballot takes seconds,
   not minutes, so no resumable board is needed):

     gentoo3.exe positions-file board-file [--no-cert]

   gives voter k the credential voter-k, encrypts every ballot with its
   proofs under the voter-bound oracle H_v = SHAKE-256(v || transcript),
   writes it to board-file (one decimal line per ballot, for the size),
   verifies every ballot under its voter's oracle, checks that a ballot
   replayed under another credential is rejected, aggregates, decrypts the
   margins with the trustee key of the instance, certifies the Schulze
   winner and verifies the certificate (skipped with --no-cert: the
   certificate does not depend on the ballot protocol). The commitment key
   is hashed to the order-q subgroup from fixed labels. The log lines follow
   encrypt.exe and main.exe so that bench/gentoo_table.py reads them. *)
open SchulzeBenchlib.SchulzeBenchIns
open Hacl_star.Hacl.Keccak
open Board
module SS = SchulzeBenchlib.SchulzeSimple
module BG = SchulzeBenchlib.BayerGroth
module HT = SchulzeBenchlib.HeliosTallyIns

let p = HT.p
let toi = Big_int_Z.int_of_big_int

let random_list (n : int) : Z.t list = List.init n (fun _ -> random_field (big 0))
let rec log2_ceil (x : int) : int = if x <= 1 then 0 else 1 + log2_ceil ((x + 1) / 2)

let hash_to_group (label : string) : Z.t =
  let rec go i =
    let msg = Bytes.of_string (Printf.sprintf "%s|%d" label i) in
    let x = Big_int_Z.mod_big_int (let n = ref Big_int_Z.zero_big_int in
      Bytes.iter (fun c -> n := Big_int_Z.add_big_int (Big_int_Z.shift_left_big_int !n 8)
        (Big_int_Z.big_int_of_int (Char.code c))) (shake256 ~msg ~size:264); !n) p in
    let y = Z.powm x HT.k p in
    if Z.equal y Z.one || Z.equal x Z.zero then go (i + 1) else y in
  go 0

(* the ballot oracle, bound to the voter *)
let oracle3_for (vid : string) (l : (Z.t, Z.t) SS.b3_item list) : Z.t =
  let item = function
    | SS.B3G x -> "G" ^ z x | SS.B3F x -> "F" ^ z x | SS.B3N k -> "N" ^ z k in
  big_int_of_bytes_mod_q (shake256 ~msg:(Bytes.of_string (vid ^ "|" ^ String.concat "," (List.map item l))) ~size:32)

(* the ballot as one line of decimal numbers: cs, C_δ, C_b, C_p, C_X,
   linear announcement and response, zero argument; vectors preceded by
   their length *)
let write_ballot3 (oc : out_channel) (vid : string) (b : (Z.t, Z.t) SS.ballot3) : unit =
  let add s = output_string oc s; output_char oc ' ' in
  let num x = add (z x) in
  let vec l = add (string_of_int (List.length l)); List.iter num l in
  add "ballot3"; add vid;
  add (string_of_int (List.length b.b3_cs)); List.iter (fun (a, c) -> num a; num c) b.b3_cs;
  num b.b3_Cd; num b.b3_Cb; num b.b3_Cp; vec b.b3_CX;
  vec (vector_to_list b.b3_lin.lin_a); vec b.b3_lin.lin_z;
  let za = b.b3_z in
  num za.BG.za_cA0; num za.za_cBm; vec za.za_cd; vec za.za_a; vec za.za_b; num za.za_r; num za.za_s; num za.za_t;
  output_char oc '\n'

let () =
  match Array.to_list Sys.argv with
  | _ :: positions_file :: board_file :: rest ->
    let with_cert = not (List.mem "--no-cert" rest) in
    let (m, names, rankings) = read_positions positions_file in
    let names = Array.of_list names in
    let nb = List.length rankings in
    let n = big (m - 1) and n' = big (nb - 1) in
    let lk = log2_ceil (m + 1) in
    let kk = toi (coq_K2 n) and w = toi (coq_W3_bench n) and r = toi (coq_R3_bench (big lk)) in
    let election = Filename.basename positions_file in
    Printf.printf "%s (simplified batched ballot): m = %d candidates, N = %d ballots, L = %d, K = %d\n%!" election m nb lk kk;
    let (keys, tk) = time_it (fun () ->
      (hash_to_group "h1", List.init kk (fun i -> hash_to_group (Printf.sprintf "gs1-%d" i)))) in
    let (h1, gs1) = keys in
    Printf.printf "commitment key: %d generators hashed to the group in %.1f s\n%!" (1 + kk) tk;
    (* the voters *)
    let oc = open_out board_file in
    write_header oc election m nb (Array.to_list names);
    let ballots = List.mapi (fun k s ->
      let vid = Printf.sprintf "voter-%d" k in
      let rd : Z.t SS.rand3 = {
        SS.r3_r = random_list kk; r3_rd = random_field (big 0); r3_rb = random_field (big 0); r3_rp = random_field (big 0);
        r3_rX = random_list lk; r3_a = random_list w;
        r3_a0 = random_list kk; r3_bm = random_list kk; r3_r0 = random_field (big 0); r3_sm = random_field (big 0);
        r3_t1 = random_list (r + 1); r3_t2 = random_list (r - 1) } in
      let (b, te) = time_it (fun () ->
        nizk_encrypt_ballot3_bench n (big lk) h1 gs1 (oracle3_for vid) (List.map big s) rd) in
      write_ballot3 oc vid b; flush oc;
      Printf.printf "  %s encrypted and proved in %.1f s\n%!" vid te;
      (vid, b, te)) rankings in
    close_out oc;
    let enc_times = List.map (fun (_, _, t) -> t) ballots in
    Printf.printf "%s: %d ballots encrypted, median %.1f s per ballot, total %.0f s, board %s (%d bytes)\n%!"
      election nb (median enc_times) (sum enc_times) board_file (Unix.stat board_file).Unix.st_size;
    (* the verifier *)
    Printf.printf "%s: m = %d candidates, N = %d ballots read in 0.0 s\n%!" election m nb;
    let ver_times = ref [] and ver_cpu = ref [] in
    let accepted = List.filter (fun (vid, b, _) ->
      let (ok, tv, cv) = time_it2 (fun () -> nizk_verify_ballot3_bench n (big lk) h1 gs1 (oracle3_for vid) b) in
      ver_times := tv :: !ver_times; ver_cpu := cv :: !ver_cpu; ok) ballots in
    Printf.printf "ballots: verify median %.1f s, total %.0f s, accepted %d of %d, cpu median %.1f s, cpu total %.0f s\n%!"
      (median !ver_times) (sum !ver_times) (List.length accepted) nb (median !ver_cpu) (sum !ver_cpu);
    let (v0, b0, _) = List.hd ballots in
    Printf.printf "ballot of %s replayed under another credential verifies: %b\n%!" v0
      (nizk_verify_ballot3_bench n (big lk) h1 gs1 (oracle3_for "voter-replay") b0);
    let (encD, ta) = time_it (fun () -> aggregate3_bench n (List.map (fun (_, b, _) -> b) accepted)) in
    let (d, td) = time_it (fun () -> decrypt_margins_bench n n' encD) in
    Printf.printf "aggregation %.2f s, decryption of the margins %.1f s\n" ta td;
    List.iter (fun row -> print_endline ("  " ^ String.concat " " (List.map z (vector_to_list row))))
      (vector_to_list d);
    let wn = match winner_bench n d with Some w -> w | None -> failwith "no winner" in
    Printf.printf "Schulze winner: %s\n%!" names.(fin_to_int wn);
    if with_cert then begin
      let (pf, tg, cg) = time_it2 (fun () ->
        nizk_generate_tally_bench n n' tally_hash_oracle encD wn (memo_random_field ())) in
      Printf.printf "certificate generated in %.0f s (cpu %.0f s)\n%!" tg cg;
      let (ok, tv, cv) = time_it2 (fun () -> nizk_verify_tally_bench n n' tally_hash_oracle encD wn pf) in
      Printf.printf "certificate: generation %.0f s, verification %.0f s, verified %b, transcript entries %s, cpu generation %.0f s, cpu verification %.0f s\n%!"
        tg tv ok (z (tally_board_size n n' encD wn pf)) cg cv
    end
  | _ -> prerr_endline "usage: gentoo3.exe positions-file board-file [--no-cert]"; exit 2
