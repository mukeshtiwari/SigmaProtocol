(* Certified verifier for ElectionGuard 2.0 election records
   (specification version 2.0.0, JSON records as written by the reference
   implementation electionguard-kotlin-multiplatform).

   Usage: main.exe RECORD_DIRECTORY

   The driver reads constants.json, election_config.json, manifest.json,
   election_initialized.json, encrypted_ballots/*/eballot-*.json,
   encrypted_tally.json, tally.json and, if present,
   challenged_ballots/dballot-*.json, each parsed with the grammar of
   parsing/ (parser.mly, lexer.mll; ast.ml checks that every group element
   is in the order-q subgroup and every scalar in Z_q). It checks the
   parameters against the certified ones, recomputes the base hashes H_P,
   H_M, H_B, H_E, the contest hashes and the confirmation codes (the checks
   that are only about hashes), computes ElectionGuard's hash functions
   (HMAC-SHA-256 over the fixed-width encodings of section 5 of the
   specification) and hands everything to the certified verifier
   Examples/ElectionGuardIns.v, which checks the guardians' proofs and the
   joint public key, every range and selection-limit proof of every
   ballot, recomputes the encrypted tally of the cast ballots, and checks
   the decryption proofs and the decrypted values. The certificate it
   returns is printed. *)

open Electionguardlib
open Electionguardlib.ElectionGuardIns
open Electionguardlib.ElectionGuardTally
open Eg_parser
open Eg_parser.Ast
(* the extracted library defines modules named List and Nat *)
module List = Stdlib.List
module String = Stdlib.String

let bi = Big_int_Z.big_int_of_int
let idx (i : Big_int_Z.big_int) : int = Big_int_Z.int_of_big_int i

(* ---- the parameters, from the certified instantiation ---- *)

let r : Z.t = ElectionGuardIns.r
let gval : Z.t = ElectionGuardIns.gval

(* ---- the hash function H of section 5: HMAC-SHA-256 with a 32-byte
   key, over the concatenation of the fixed-width encodings ---- *)

let hex_decode (h : string) : string = Cryptokit.transform_string (Cryptokit.Hexa.decode ()) h
let hex_encode (s : string) : string =
  String.uppercase_ascii (Cryptokit.transform_string (Cryptokit.Hexa.encode ()) s)

(* big-endian, fixed width in bytes *)
let fixed (width : int) (x : Z.t) : string =
  let h = Z.format "%x" x in
  let h = if String.length h mod 2 = 1 then "0" ^ h else h in
  let s = hex_decode h in
  if String.length s > width then failwith "value too wide";
  String.make (width - String.length s) '\000' ^ s

let enc_p (x : Z.t) = fixed 512 x          (* elements of Z_p: 512 bytes *)
let enc_q (x : Z.t) = fixed 32 x           (* elements of Z_q: 32 bytes *)
let enc_int (n : int) = fixed 4 (Z.of_int n)   (* small integers: 4 bytes *)
let enc_file (s : string) = enc_int (String.length s) ^ s   (* files: length-prefixed *)

let hmac (key : string) (parts : string list) : string =
  let h = Cryptokit.MAC.hmac_sha256 key in
  List.iter (fun s -> h#add_string s) parts;
  h#result

let hash_hex (key : string) (parts : string list) : string = hex_encode (hmac key parts)

(* the hash as a challenge: the 256-bit value modulo q *)
let hash_q (key : string) (parts : string list) : scalar =
  Z.erem (Z.of_string_base 16 (hash_hex key parts)) q

(* the version string, padded with 0x00 to 32 bytes *)
let version = "v2.0.0" ^ String.make 26 '\000'

(* ---- the files ---- *)

let read_bytes (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in close_in ic; s

let parse (path : string) (start : (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) : 'a =
  let lexbuf = Lexing.from_string (read_bytes path) in
  let what = Filename.basename path in
  try start Lexer.token lexbuf with
  | Lexer.SyntaxError msg -> failwith (Printf.sprintf "%s: %s at offset %d" what msg (Lexing.lexeme_start lexbuf))
  | Parser.Error -> failwith (Printf.sprintf "%s: syntax error at offset %d" what (Lexing.lexeme_start lexbuf))
  | Failure msg -> failwith (what ^ ": " ^ msg)

let by_sequence (seq : 'a -> int) (l : 'a list) : 'a list = List.stable_sort (fun a b -> compare (seq a) (seq b)) l

(* the encodings of a ciphertext's components, as hashed *)
let ciphertext_enc (c : ciphertext) : string list = [enc_p c.pad; enc_p c.data]
let ciphertext_pair (c : ciphertext) : ElectionGuardIns.ciphertext = (c.pad, c.data)

let pairs_enc (pairs : (Z.t * Z.t) list) : string list =
  List.concat_map (fun (a, b) -> [enc_p a; enc_p b]) pairs

let mulp (a : Z.t) (b : Z.t) : Z.t = Z.erem (Z.mul a b) p

let main () =
  let dir = Sys.argv.(1) in
  let path f = Filename.concat dir f in
  let failures = ref [] in
  let check (item : string) (ok : bool) =
    Printf.printf "%-60s %b\n" item ok;
    if not ok then failures := item :: !failures in
  (* ---- verification 1: parameters and base hashes ---- *)
  let constants = parse (path "constants.json") Parser.constants in
  check "1.B-E constants are the parameters of the specification"
    (Z.equal constants.large_prime p && Z.equal constants.small_prime q &&
     Z.equal constants.cofactor r && Z.equal constants.generator gval);
  let config = parse (path "election_config.json") Parser.config in
  check "1.A specification version v2.0.0" (config.config_version = "v2.0.0");
  let n = config.number_of_guardians and k = config.quorum in
  let hp_stored = config.parameter_base_hash in
  let hp = hash_hex version ["\x00"; enc_p p; enc_q q; enc_p gval] in
  check "1.F parameter base hash H_P = H(ver; 0x00, p, q, g)" (hp = hp_stored);
  let hp_key = hex_decode hp_stored in
  let hm_stored = config.manifest_hash in
  let manifest_bytes = read_bytes (path "manifest.json") in
  let hm = hash_hex hp_key ["\x01"; enc_file manifest_bytes] in
  check "1.G manifest hash H_M = H(H_P; 0x01, manifest)" (hm = hm_stored);
  let hb_stored = config.election_base_hash in
  let hb = hash_hex hp_key ["\x02"; hex_decode hm_stored; enc_int n; enc_int k] in
  check "1.H election base hash H_B = H(H_P; 0x02, H_M, n, k)" (hb = hb_stored);
  let hb_key = hex_decode hb_stored in
  (* ---- the manifest: contests and options, in sequence order ---- *)
  let manifest = parse (path "manifest.json") Parser.manifest in
  let contest_specs = List.map (fun (c : contest_spec) ->
    let sels = by_sequence (fun (s : selection_spec) -> s.ss_sequence_order) c.cs_ballot_selections in
    let option_limit = match c.cs_option_selection_limit with Some l -> l | None -> 1 in
    (c.cs_object_id, List.map (fun (s : selection_spec) -> s.ss_object_id) sels,
     mk_contest_spec (bi (List.length sels)) (bi option_limit) (bi c.cs_votes_allowed)))
    (by_sequence (fun (c : contest_spec) -> c.cs_sequence_order) manifest.m_contests) in
  let contest_index = Hashtbl.create 64 in
  List.iteri (fun i (id, _, _) -> Hashtbl.replace contest_index id i) contest_specs;
  let selection_ids = Array.of_list (List.map (fun (_, ids, _) -> ids) contest_specs) in
  let limits = Array.of_list (List.map (fun (_, _, spec) -> spec) contest_specs) in
  (* ---- verifications 2, 3, 4: guardians, joint key, extended base hash ---- *)
  let init = parse (path "election_initialized.json") Parser.initialized in
  let kz = init.joint_public_key in
  let he_stored = init.extended_base_hash in
  let he = hash_hex hb_key ["\x12"; enc_p kz] in
  check "4.A extended base hash H_E = H(H_B; 0x12, K)" (he = he_stored);
  let he_key = hex_decode he_stored in
  let guardians_sorted = by_sequence (fun (g : guardian) -> g.g_x_coordinate) init.guardians in
  let guardians = List.map (fun (g : guardian) ->
    mk_guardian (bi g.g_x_coordinate)
      (List.map (fun (c : coefficient) -> c.k_public_key) g.g_coefficient_proofs)
      (List.map (fun (c : coefficient) -> c.k_proof) g.g_coefficient_proofs)) guardians_sorted in
  (* h_coef i j [h] = H(H_P; 0x10, i, j, K_ij, h) *)
  let coefficient_key = Hashtbl.create 16 in
  List.iter (fun (g : guardian) -> List.iteri (fun j (c : coefficient) ->
    Hashtbl.replace coefficient_key (g.g_x_coordinate, j) c.k_public_key) g.g_coefficient_proofs) guardians_sorted;
  let h_coef i j (pts : elem list) =
    let i = idx i and j = idx j in
    let kij = try Hashtbl.find coefficient_key (i, j) with Not_found -> failwith "unknown coefficient" in
    hash_q hp_key (["\x10"; enc_int i; enc_int j; enc_p kij] @ List.map enc_p pts) in
  let gh = mk_guardian_hashes h_coef in
  let election = mk_election generator kz (bi n) (bi k) (List.map (fun (_, _, spec) -> spec) contest_specs) in
  (* ---- the ballots ---- *)
  let ballot_files =
    let sub = path "encrypted_ballots" in
    if not (Sys.file_exists sub) then [] else
    List.concat_map (fun d ->
      let dd = Filename.concat sub d in
      if Sys.is_directory dd then
        List.map (Filename.concat dd) (List.filter (fun f ->
          String.length f > 8 && String.sub f 0 8 = "eballot-" && Filename.check_suffix f ".json")
          (Array.to_list (Sys.readdir dd)))
      else []) (Array.to_list (Sys.readdir sub)) in
  let ballot_files = List.sort compare ballot_files in
  let malformed = ref 0 in
  (* a ballot: the certified data, its hash functions, and its id; the
     ciphertexts of each contest and their aggregate serve the hash functions *)
  let check_ballot (file : string) =
    let b = parse file Parser.eballot in
    let id = b.ballot_id in
    if b.b_election_id <> he_stored then failwith "ballot election id";
    let cast = b.state = "CAST" in
    let contests = by_sequence (fun (c : contest) -> c.con_sequence_order) b.b_contests in
    let chis = ref [] in
    let per_contest = Hashtbl.create 32 in
    let cts = List.map (fun (cj : contest) ->
      let cid = cj.con_id in
      let i = try Hashtbl.find contest_index cid with Not_found -> failwith ("unknown contest " ^ cid) in
      let sels = by_sequence (fun (s : selection) -> s.sel_sequence_order) cj.con_selections in
      let ids = List.map (fun (s : selection) -> s.sel_id) sels in
      if ids <> selection_ids.(i) then failwith ("options of contest " ^ cid);
      let cts = List.map (fun (s : selection) -> s.sel_encrypted_vote) sels in
      (* 7.A contest hash χ = H(H_E; 0x23, ℓ, K, α_1, β_1, …) *)
      let chi = hash_hex he_key (["\x23"; enc_int cj.con_sequence_order; enc_p kz] @ List.concat_map ciphertext_enc cts) in
      if chi <> cj.con_hash then failwith ("contest hash of " ^ cid);
      chis := hex_decode chi :: !chis;
      (* the aggregate, for the selection-limit proof's hash *)
      let (a, bb) = List.fold_left (fun (a, bb) (c : ciphertext) -> (mulp a c.pad, mulp bb c.data)) (Z.one, Z.one) cts in
      Hashtbl.replace per_contest i (Array.of_list cts, (a, bb));
      let selections = List.map (fun (s : selection) -> mk_selection (ciphertext_pair s.sel_encrypted_vote) s.sel_proofs) sels in
      mk_contest (bi i) selections cj.con_proofs) contests in
    (* 7.B confirmation code H(B) = H(H_E; 0x24, χ_1, …, χ_m, B_aux) *)
    let baux = hex_decode b.code_baux in
    let code = hash_hex he_key (["\x24"] @ List.rev !chis @ [baux]) in
    if code <> b.confirmation_code then failwith "confirmation code";
    let h_range i jj (pairs : (Z.t * Z.t) list) =
      let (cts, _) = Hashtbl.find per_contest (idx i) in
      hash_q he_key (["\x21"; enc_p kz] @ ciphertext_enc cts.(idx jj) @ pairs_enc pairs) in
    let h_limit i (pairs : (Z.t * Z.t) list) =
      let (_, (a, bb)) = Hashtbl.find per_contest (idx i) in
      hash_q he_key (["\x21"; enc_p kz; enc_p a; enc_p bb] @ pairs_enc pairs) in
    (mk_ballot cts cast, mk_ballot_hashes h_range h_limit, id) in
  let parsed = List.filter_map (fun f ->
    try Some (check_ballot f) with Failure msg ->
      incr malformed; Printf.printf "MALFORMED ballot %s rejected by the parser: %s\n" (Filename.basename f) msg; None)
    ballot_files in
  let ballots = List.map (fun (b, _, _) -> b) parsed in
  let hs (b : ElectionGuardIns.ballot) = match List.find_opt (fun (b', _, _) -> b' == b) parsed with
    | Some (_, h, _) -> h | None -> failwith "unknown ballot" in
  let id_of (b : ElectionGuardIns.ballot) = match List.find_opt (fun (b', _, _) -> b' == b) parsed with
    | Some (_, _, id) -> id | None -> "?" in
  (* ---- the published encrypted tally ---- *)
  let etally = parse (path "encrypted_tally.json") Parser.encrypted_tally in
  check "8 encrypted tally names the extended base hash" (etally.et_election_id = he_stored);
  let published_by_id = Hashtbl.create 64 in
  List.iter (fun (cj : tally_contest) ->
    let sels = by_sequence (fun (s : tally_selection) -> s.ts_sequence_order) cj.tc_selections in
    Hashtbl.replace published_by_id cj.tc_id (List.map (fun (s : tally_selection) -> (s.ts_id, s.ts_encrypted_vote)) sels))
    etally.et_contests;
  let published = List.map (fun (cid, ids, _) ->
    let sels = try Hashtbl.find published_by_id cid with Not_found -> failwith ("encrypted tally lacks contest " ^ cid) in
    if List.map fst sels <> ids then failwith ("options of contest " ^ cid ^ " in the encrypted tally");
    List.map (fun (_, c) -> ciphertext_pair c) sels) contest_specs in
  (* ---- the decrypted tally ---- *)
  let dtally = parse (path "tally.json") Parser.decryptions in
  check "9 decrypted tally names the extended base hash" (dtally.dec_election_id = Some he_stored);
  (* decryptions of a tally or a ballot, in manifest order, with the
     hash function h_dec i j [(a, b)] = H(H_E; 0x30, K, A, B, a, b, M) *)
  let decryptions (dj : Ast.decryptions) =
    let by_id = Hashtbl.create 64 in
    List.iter (fun (cj : dcontest) ->
      Hashtbl.replace by_id cj.dc_id (List.map (fun (s : decryption) -> (s.d_id, s)) cj.dc_selections)) dj.dec_contests;
    let table = Hashtbl.create 64 in
    let ds = List.mapi (fun i (cid, ids, _) ->
      match Hashtbl.find_opt by_id cid with
      | None -> []
      | Some sels ->
        List.mapi (fun jj sid ->
          let s = try List.assoc sid sels with Not_found -> failwith ("decryption of option " ^ sid) in
          let a = s.d_encrypted_vote.pad and bb = s.d_encrypted_vote.data in
          let m = mulp bb (Z.invert s.d_b_over_m p) in
          Hashtbl.replace table (i, jj) (a, bb, m);
          mk_decryption s.d_b_over_m s.d_proof (scalar_of_int s.d_tally)) ids) contest_specs in
    let h_dec i jj (pairs : (Z.t * Z.t) list) =
      let (a, bb, m) = Hashtbl.find table (idx i, idx jj) in
      hash_q he_key (["\x30"; enc_p kz; enc_p a; enc_p bb] @ pairs_enc pairs @ [enc_p m]) in
    (ds, mk_decryption_hashes h_dec) in
  let (ds, dh) = decryptions dtally in
  (* ---- the certified verifier ---- *)
  let t0 = Unix.gettimeofday () in
  let cert = compute_final_count_ins election hs gh guardians ballots published dh ds in
  let t1 = Unix.gettimeofday () in
  let (vbs, inbs, bfinal) = match cert with
    | Specif.Coq_existT (vbs, Specif.Coq_existT (inbs, Specif.Coq_existT (bfinal, count))) ->
      (* the certificate, printed as the Helios verifier prints its own: every
         ballot with its ciphertexts and proofs, the encrypted tally before and
         after it, and the final state. Elements and scalars are printed in
         decimal, proofs as (challenge, response). The certificate carries the
         encrypted tally only in its final state, so the driver maintains the
         running one for display, with the certified tally function (only the
         cast ballots count); its final value is checked against the
         certificate's. *)
      let line = String.make 150 '-' in
      let list_string pr sep xs = String.concat sep (List.map pr xs) in
      let cipher_string ((a, b) : ElectionGuardIns.ciphertext) : string = "(" ^ Z.to_string a ^ ", " ^ Z.to_string b ^ ")" in
      let proof_string ((c, v) : ElectionGuardIns.proof) : string =
        "{challenge = " ^ Z.to_string c ^ "; response = " ^ Z.to_string v ^ "}" in
      let proofs_string (ps : ElectionGuardIns.proof list) : string = "[" ^ list_string proof_string ", " ps ^ "]" in
      let contest_ids = Array.of_list (List.map (fun (id, _, _) -> id) contest_specs) in
      let contest_string (c : ElectionGuardIns.contest) : string =
        Printf.sprintf "contest %s: {encrypted selections: [%s]; range proofs: [%s]; selection limit proof: %s}" contest_ids.(idx c.cindex)
          (list_string (fun (s : ElectionGuardIns.selection) -> cipher_string s.encrypted_vote) ", " c.selections)
          (list_string (fun (s : ElectionGuardIns.selection) -> proofs_string s.range_proof) ", " c.selections)
          (proofs_string c.limit_proof) in
      let ballot_string (b : ElectionGuardIns.ballot) : string =
        Printf.sprintf "ballot_id: %s; state: %s; contests: [%s]" (id_of b) (if b.cast then "cast" else "challenged")
          (list_string contest_string "; " b.bcontests) in
      let per_contest pr t = String.concat "; " (List.mapi (fun i x -> Printf.sprintf "contest %s: %s" contest_ids.(i) (pr x)) t) in
      let tally_string (t : ElectionGuardIns.ciphertext list list) : string = per_contest (list_string cipher_string " ") t in
      let running = ref (encrypted_tally_ins election []) in
      let rec print_count (c : (scalar, elem) count) : unit = match c with
        | Coq_ax -> Printf.printf "Identity-tally : %s\n%s\n" (tally_string !running) line
        | Coq_cvalid (b, _, _, _, c') -> print_count c';
          let previous = tally_string !running in
          running := mul_tallies coq_Gmul (encrypted_tally_ins election [b]) !running;
          Printf.printf "Valid ballot : %s\nPrevious tally : %s\nCurrent tally : %s\n%s\n" (ballot_string b) previous (tally_string !running) line
        | Coq_cinvalid (b, _, _, _, c') -> print_count c';
          let t = tally_string !running in
          Printf.printf "Invalid ballot : %s\nPrevious tally : %s\nCurrent tally : %s\n%s\n" (ballot_string b) t t line
        | Coq_cfinish (_, _, _, _, gs, _, tally, published, ds, bg, bt, bd, c') -> print_count c';
          assert (!running = tally);
          Printf.printf "Final tally: [%s]\n" (tally_string tally);
          Printf.printf "Published encrypted tally: [%s]\n" (tally_string published);
          Printf.printf "Guardians' coefficient commitments: [%s]\n" (list_string (fun (g : ElectionGuardIns.guardian) ->
            Printf.sprintf "guardian %s: %s" (Z.to_string g.xcoord) (list_string Z.to_string " " g.coefficients)) "; " gs);
          Printf.printf "Final decrypted tally: [%s]\n"
            (per_contest (list_string (fun (d : ElectionGuardIns.decryption) -> Z.to_string d.dvalue) " ") ds);
          Printf.printf "Guardians' coefficient proofs and joint public key are valid : %b\n" bg;
          Printf.printf "Encrypted tally of the cast ballots is equal to the published one : %b\n" bt;
          Printf.printf "Decryption proofs and decrypted values of the tally are valid : %b\n%s\n" bd line in
      print_string "Count : "; print_count count; print_newline ();
      (vbs, inbs, bfinal) in
  Printf.printf "Final tally: [%b]\n" bfinal;
  Printf.printf "All votes : [%d]\n" (List.length ballots);
  Printf.printf "Cast votes : [%d]\n" (List.length (List.filter (fun (b : ElectionGuardIns.ballot) -> b.cast) vbs));
  Printf.printf "Valid vote : [%d]\n" (List.length vbs);
  Printf.printf "Invalid votes : [%d]\n" (List.length inbs);
  if !malformed > 0 then Printf.printf "Malformed votes : [%d]\n" !malformed;
  (* ---- challenged ballots (verifications 12 and 13) ---- *)
  let challenged_dir = path "challenged_ballots" in
  let challenged_ok = ref true in
  let nchallenged = ref 0 in
  if Sys.file_exists challenged_dir then begin
    List.iter (fun f ->
      if Filename.check_suffix f ".json" then begin
        let dj = parse (Filename.concat challenged_dir f) Parser.decryptions in
        let id = match dj.dec_id with Some id -> id | None -> failwith (f ^ ": challenged ballot without id") in
        incr nchallenged;
        match List.find_opt (fun (_, _, id') -> id' = id) parsed with
        | None -> Printf.printf "challenged ballot %s: no encrypted ballot\n" id; challenged_ok := false
        | Some (b, _, _) ->
          let (ds, dh) = decryptions dj in
          let ok = verify_ballot_decryptions_ins election dh b ds in
          (* 13.B the decrypted values are in range *)
          let in_range = List.for_all (fun (cj : dcontest) ->
            let i = try Hashtbl.find contest_index cj.dc_id with Not_found -> failwith ("unknown contest " ^ cj.dc_id) in
            let l = idx (limits.(i)).option_limit in
            List.for_all (fun (s : decryption) -> 0 <= s.d_tally && s.d_tally <= l) cj.dc_selections) dj.dec_contests in
          Printf.printf "challenged ballot %s: decryption proofs %b, values in range %b\n" id ok in_range;
          if not (ok && in_range && not b.cast) then challenged_ok := false
      end) (List.sort compare (Array.to_list (Sys.readdir challenged_dir)))
  end;
  let verdict = bfinal && !malformed = 0 && inbs = [] && !failures = [] && !challenged_ok in
  Printf.printf "election %s: verified = %b (certified verifier: %.2f s)\n" (String.sub he_stored 0 16) verdict (t1 -. t0);
  if !nchallenged > 0 then Printf.printf "challenged ballots: %d\n" !nchallenged;
  exit (if verdict then 0 else 1)

(* a record the parser cannot accept (wrong parameters, an element outside
   the subgroup, a scalar out of range, a missing contest or option) is
   rejected before the certified verifier runs *)
let () =
  if Array.length Sys.argv < 2 then (prerr_endline "usage: main.exe RECORD_DIRECTORY"; exit 2);
  try main () with
  | Failure msg -> Printf.printf "record rejected by the parser: %s\n" msg; exit 1
  | Sys_error msg -> Printf.printf "record rejected: %s\n" msg; exit 1
