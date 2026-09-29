(* Certified verifier for Belenios elections (Belenios 3.x, specification
   version 1, group Ed25519).

   Usage: main.exe ELECTION.bel

   The driver reads the public-data archive (a tar file of JSON documents
   and events), parses every document with the grammar of parsing/
   (parser.mly, lexer.mll; ast.ml decodes the compressed Ed25519 points and
   checks that each lies on the curve, is canonically encoded and has order
   l, and checks the range of every scalar), follows the event chain (Setup,
   Ballot..., EndBallots, EncryptedTally, PartialDecryption..., Result),
   computes the Fiat-Shamir hash functions of Belenios (SHA-256 over its
   serialisation), and hands everything to the certified verifier
   Examples/BeleniosIns.v, which reconstructs the announcements of every
   proof, checks the challenges against the hashes, recomputes the encrypted
   tally from the last ballot of each credential, checks the trustees'
   proofs of knowledge and decryption proofs, and checks the published
   result. The certificate it returns is printed. *)

open Belenioslib
open Belenioslib.BeleniosIns
open Belenioslib.BeleniosTally
open Belenioslib.Ed25519Ins
open Belenios_parser
open Belenios_parser.Ast
(* the extracted library defines modules named List and Nat *)
module List = Stdlib.List
module String = Stdlib.String

let bi = Big_int_Z.big_int_of_int
let idx (i : Big_int_Z.big_int) : int = Big_int_Z.int_of_big_int i

(* ---- hashing ---- *)

let sha256_hex (s : string) : string =
  let h = Cryptokit.Hash.sha256 () in
  h#add_string s; Cryptokit.transform_string (Cryptokit.Hexa.encode ()) h#result

let sha256_b64 (s : string) : string =
  let h = Cryptokit.Hash.sha256 () in
  h#add_string s;
  Cryptokit.transform_string (Cryptokit.Base64.encode_compact ()) h#result

(* Belenios: SHA256(prefix ^ points joined by commas), as a big-endian
   number, modulo l *)
let hash_points (prefix : string) (pts : point list) : scalar =
  let msg = prefix ^ String.concat "," (List.map hex_of_point pts) in
  of_Z (Z.erem (Z.of_string_base 16 (sha256_hex msg)) l)

(* announcements in G × G are serialised as A,B *)
let hash_pairs (prefix : string) (pairs : (point * point) list) : scalar =
  hash_points prefix (List.concat_map (fun (a, b) -> [a; b]) pairs)

(* ---- the archive ---- *)

let run_lines (cmd : string) : string list =
  let ic = Unix.open_process_in cmd in
  let rec loop acc = match input_line ic with
    | line -> loop (line :: acc) | exception End_of_file -> List.rev acc in
  let ls = loop [] in ignore (Unix.close_process_in ic); ls

let archive = ref ""

let read_entry (name : string) : string =
  let ic = Unix.open_process_in (Printf.sprintf "tar -xOf %s %s" (Filename.quote !archive) (Filename.quote name)) in
  let buf = Buffer.create 4096 in
  (try while true do Buffer.add_channel buf ic 1 done with End_of_file -> ());
  ignore (Unix.close_process_in ic);
  Buffer.contents buf

(* BELENIOS_SKIP_HASH_CHECK=1 disables the checks of the archive's own
   content hashes, so that tampered archives reach the certified verifier
   (for testing only) *)
let skip_hash_check = Sys.getenv_opt "BELENIOS_SKIP_HASH_CHECK" <> None

let read_data (hash : string) : string =
  let s = read_entry (hash ^ ".data.json") in
  if (not skip_hash_check) && sha256_hex s <> hash then failwith ("data hash mismatch: " ^ hash);
  s

(* ---- parsing a document ---- *)

let parse (what : string) (start : (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) (s : string) : 'a =
  let lexbuf = Lexing.from_string s in
  try start Lexer.token lexbuf with
  | Lexer.SyntaxError msg -> failwith (Printf.sprintf "%s: %s at offset %d" what msg (Lexing.lexeme_start lexbuf))
  | Parser.Error -> failwith (Printf.sprintf "%s: syntax error at offset %d" what (Lexing.lexeme_start lexbuf))
  | Failure msg -> failwith (what ^ ": " ^ msg)

let () =
  if Array.length Sys.argv < 2 then (prerr_endline "usage: main.exe ELECTION.bel"; exit 2);
  archive := Sys.argv.(1);
  let entries = run_lines (Printf.sprintf "tar -tf %s" (Filename.quote !archive)) in
  (* the events, with the text of each (its hash names the entry and is the next event's parent) *)
  let events = List.filter_map (fun e ->
    if not (Filename.check_suffix e ".event.json") then None else begin
      let s = read_entry e in
      if (not skip_hash_check) && sha256_hex s <> Filename.chop_suffix e ".event.json" then failwith ("event hash mismatch: " ^ e);
      Some (parse e Parser.event s, s)
    end) entries in
  let _ = List.fold_left (fun (h, parent) (ev, raw) ->
    if ev.ev_height <> h then failwith "event height";
    (match parent, ev.ev_parent with
     | None, None -> () | Some q, Some q' when q = q' -> ()
     | _ -> failwith "event parent");
    (h + 1, Some (sha256_hex raw))) (0, None) events in
  let events = List.map fst events in
  let payload ev = match ev.ev_payload with Some p -> p | None -> failwith ("event without payload: " ^ ev.ev_type) in
  let typed t = List.filter (fun ev -> ev.ev_type = t) events in
  let single t = match typed t with [e] -> e | _ -> failwith ("expected exactly one " ^ t ^ " event") in
  (* setup *)
  let setup = parse "setup" Parser.setup (read_data (payload (single "Setup"))) in
  let election_raw = read_data setup.s_election in
  let el = parse "election" Parser.election election_raw in
  let fingerprint = sha256_b64 election_raw in
  let questions = List.map (fun q -> mk_question (bi q.q_answers) (bi q.q_min) (bi q.q_max) q.q_blank) el.e_questions in
  let trustee_keys = parse "trustees" Parser.trustees (read_data setup.s_trustees) in
  let credentials = List.map (fun c -> (c.c_point.pt, c.c_weight)) (parse "credentials" Parser.credentials (read_data setup.s_credentials)) in
  let election = mk_election base el.e_public_key.pt questions credentials in
  (* ballots, in casting order *)
  let ballots_raw = List.map (fun e -> read_data (payload e)) (typed "Ballot") in
  let check_ballot (raw : string) : BeleniosIns.ballot * BeleniosIns.ballot_hashes =
    let b = parse "ballot" Parser.ballot raw in
    if b.b_uuid <> el.e_uuid then failwith "ballot uuid";
    if b.b_hash <> fingerprint then failwith "ballot election hash";
    (* the signature covers the ballot without its signature field *)
    let without_sig =
      let pre = String.trim (String.sub raw 0 b.b_sig_pos) in
      let k = String.length pre in
      if k = 0 || pre.[k - 1] <> ',' then failwith "signature field";
      String.trim (String.sub pre 0 (k - 1)) ^ "}" in
    if sha256_b64 without_sig <> b.b_sig_hash then failwith "signature hash";
    let answers = List.map (fun a ->
      mk_answer (List.map ciphertext_points a.a_choices) a.a_individual a.a_overall a.a_blank) b.b_answers in
    let ballot = mk_ballot b.b_credential.pt answers b.b_sig_proof in
    (* the hash functions of this ballot *)
    let zkp = fingerprint ^ "|" ^ b.b_credential.hex in
    let answers_arr = Array.of_list b.b_answers in
    let choice_strings i = List.map ciphertext_string answers_arr.(idx i).a_choices in
    let h_sig pts = hash_points ("sig|" ^ b.b_sig_hash ^ "|") pts in
    let h_indiv i k pairs = hash_pairs ("prove|" ^ zkp ^ "|" ^ List.nth (choice_strings i) (idx k) ^ "|") pairs in
    let zkp_s i = zkp ^ "|" ^ String.concat "," (choice_strings i) in
    let h_overall i pairs =
      let q = List.nth questions (idx i) in
      if q.qblank then hash_pairs ("bproof1|" ^ zkp_s i ^ "|") pairs
      else begin
        (* the interval proof is on the product of the choices *)
        let cs = List.nth answers (idx i) in
        let (sa, sb) = List.fold_left (fun (a, b) (c, e) -> (Ed25519.Ed25519.Ed.gop a c, Ed25519.Ed25519.Ed.gop b e))
          (Ed25519.Ed25519.Ed.gid, Ed25519.Ed25519.Ed.gid) cs.choices in
        hash_pairs ("prove|" ^ zkp_s i ^ "|" ^ hex_of_point sa ^ "," ^ hex_of_point sb ^ "|") pairs
      end in
    let h_blank i pairs = hash_pairs ("bproof0|" ^ zkp_s i ^ "|") pairs in
    (ballot, mk_ballot_hashes h_sig h_indiv h_overall h_blank) in
  (* a ballot the parser cannot accept (wrong election, non-canonical or
     malformed data, wrong signature hash) is reported and makes the
     verdict false; it never reaches the certified verifier *)
  let malformed = ref 0 in
  let parsed = List.filter_map (fun raw ->
    try Some (check_ballot raw) with Failure msg ->
      incr malformed; Printf.printf "MALFORMED ballot rejected by the parser: %s\n" msg; None) ballots_raw in
  let ballots = List.map fst parsed in
  (* the hash functions of a ballot, looked up by physical identity *)
  let hs (b : BeleniosIns.ballot) = match List.find_opt (fun (b', _) -> b' == b) parsed with
    | Some (_, h) -> h | None -> failwith "unknown ballot" in
  (* encrypted tally *)
  let tally = parse "encrypted tally" Parser.tally_header (read_data (payload (single "EncryptedTally"))) in
  let published = List.map (List.map ciphertext_points)
    (parse "encrypted tally" Parser.encrypted_tally (read_data tally.th_encrypted_tally)) in
  (* trustees, with their partial decryptions (owner t refers to the t-th trustee, from 1) *)
  let pds = List.map (fun e ->
    let hd = parse "partial decryption" Parser.pd_header (read_data (payload e)) in
    (hd.pd_owner, parse "partial decryption" Parser.partial_decryption (read_data hd.pd_payload))) (typed "PartialDecryption") in
  let trustees = List.mapi (fun t tk ->
    let pd = try List.assoc (t + 1) pds with Not_found -> failwith "missing partial decryption" in
    mk_trustee tk.t_public_key.pt tk.t_pok pd.pd_factors pd.pd_proofs) trustee_keys in
  let pk_strings = Array.of_list (List.map (fun tk -> tk.t_public_key.hex) trustee_keys) in
  let h_pok t pts = hash_points ("pok|Ed25519|" ^ pk_strings.(idx t) ^ "|") pts in
  let h_dec t pairs = hash_pairs ("decrypt|" ^ fingerprint ^ "|" ^ pk_strings.(idx t) ^ "|") pairs in
  let trustee_hashes = mk_trustee_hashes h_pok h_dec in
  (* result *)
  let result = parse "result" Parser.result (read_data (payload (single "Result"))) in
  (* the certified verifier *)
  let t0 = Unix.gettimeofday () in
  let cert = compute_final_count_ins election hs trustee_hashes ballots published trustees result in
  let t1 = Unix.gettimeofday () in
  match cert with
  | Specif.Coq_existT (vbs, Specif.Coq_existT (inbs, Specif.Coq_existT (bfinal, count))) ->
    (* the certificate, printed as the Helios verifier prints its own: every
       ballot with its ciphertexts and proofs, the encrypted tally before and
       after it, and the final state. Points are printed in their compressed
       encoding, scalars in decimal, proofs as (challenge, response). The
       tally shown after a ballot is the certified encrypted tally of the
       valid ballots so far (the last one of each credential, weighted). *)
    let line = String.make 150 '-' in
    let list_string pr sep xs = String.concat sep (List.map pr xs) in
    let scalar_string (x : scalar) : string = Big_int_Z.string_of_big_int (to_Z x) in
    let cipher_string ((a, b) : BeleniosIns.ciphertext) : string = "(" ^ hex_of_point a ^ ", " ^ hex_of_point b ^ ")" in
    let proof_string ((c, r) : BeleniosIns.proof) : string =
      "{challenge = " ^ scalar_string c ^ "; response = " ^ scalar_string r ^ "}" in
    let proofs_string (ps : BeleniosIns.proof list) : string = "[" ^ list_string proof_string ", " ps ^ "]" in
    let answer_string (i : int) (a : BeleniosIns.answer) : string =
      Printf.sprintf "question %d: {encrypted choices: [%s]; individual proofs of 0 or 1: [%s]; overall proof: %s%s}" i
        (list_string cipher_string ", " a.choices)
        (list_string proofs_string ", " a.individual_proofs)
        (proofs_string a.overall_proof)
        (match a.blank_proof with None -> "" | Some ps -> "; blank proof: " ^ proofs_string ps) in
    let ballot_string (b : BeleniosIns.ballot) : string =
      "credential: " ^ hex_of_point b.credential ^ "; answers: [" ^
      String.concat "; " (List.mapi answer_string b.answers) ^ "]; signature: " ^ proof_string b.signature in
    let tally_string (t : BeleniosIns.ciphertext list list) : string =
      String.concat "; " (List.mapi (fun i cs -> Printf.sprintf "question %d: %s" i (list_string cipher_string " " cs)) t) in
    (* The running tally. The certificate carries the encrypted tally only
       in its final state, so the driver maintains it for display: the
       contribution of one ballot is the certified tally of that ballot
       alone (weighted), a valid ballot multiplies the tally by its
       contribution and divides it by that of the ballot it replaces (same
       credential). The final value is checked against the certificate's. *)
    let module Ed = Ed25519.Ed25519.Ed in
    let contribution (b : BeleniosIns.ballot) = encrypted_tally_ins election [b] in
    let map_tally f t u = List.map2 (List.map2 (fun (a, b) (c, d) -> (f a c, f b d))) t u in
    let mul_tally = map_tally Ed.gop in
    let div_tally = map_tally (fun a c -> Ed.gop a (Ed.ginv c)) in
    let current : (string, BeleniosIns.ciphertext list list) Hashtbl.t = Hashtbl.create 64 in
    let running = ref (encrypted_tally_ins election []) in
    let add_ballot (b : BeleniosIns.ballot) : string * string =
      let previous = tally_string !running in
      let cred = hex_of_point b.credential in
      let cb = contribution b in
      (match Hashtbl.find_opt current cred with
       | Some old -> running := div_tally !running old
       | None -> ());
      Hashtbl.replace current cred cb;
      running := mul_tally !running cb;
      (previous, tally_string !running) in
    let rec print_count (c : (scalar, point) count) : unit = match c with
      | Coq_ax -> Printf.printf "Identity-tally : %s\n%s\n" (tally_string !running) line
      | Coq_cvalid (b, _, _, _, c') -> print_count c';
        let (previous, now) = add_ballot b in
        Printf.printf "Valid ballot : %s\nPrevious tally : %s\nCurrent tally : %s\n%s\n" (ballot_string b) previous now line
      | Coq_cinvalid (b, _, _, _, c') -> print_count c';
        let t = tally_string !running in
        Printf.printf "Invalid ballot : %s\nPrevious tally : %s\nCurrent tally : %s\n%s\n" (ballot_string b) t t line
      | Coq_cfinish (_, _, _, _, trs, tally, published, result, bt, btr, bres, c') -> print_count c';
        if tally_string !running <> tally_string tally then failwith "the displayed running tally differs from the certificate's tally";
        Printf.printf "Final tally: [%s]\n" (tally_string tally);
        Printf.printf "Published encrypted tally: [%s]\n" (tally_string published);
        Printf.printf "Trustees' public keys: [%s]\n" (list_string (fun (tr : BeleniosIns.trustee) -> hex_of_point tr.public_key) " " trs);
        Printf.printf "Final decrypted tally: [%s]\n"
          (String.concat "; " (List.mapi (fun i rs -> Printf.sprintf "question %d: %s" i (list_string scalar_string " " rs)) result));
        Printf.printf "Encrypted tally is equal to the published one : %b\n" bt;
        Printf.printf "Trustees' pok, decryption factors and proofs are valid : %b\n" btr;
        Printf.printf "Published result is correct decryption of the encrypted tally : %b\n%s\n" bres line in
    print_string "Count : "; print_count count; print_newline ();
    Printf.printf "Final tally: [%b]\n" bfinal;
    Printf.printf "All votes : [%d]\n" (List.length ballots);
    Printf.printf "Tallied votes (last per credential) : [%d]\n" (List.length (last_per_credential_ins (List.rev vbs)));
    Printf.printf "Valid vote : [%d]\n" (List.length vbs);
    Printf.printf "Invalid votes : [%d]\n" (List.length inbs);
    if !malformed > 0 then Printf.printf "Malformed votes : [%d]\n" !malformed;
    (* Belenios only accepts valid ballots on the bulletin board, so an
       invalid or malformed ballot in the archive is a failure *)
    let verdict = bfinal && !malformed = 0 && inbs = [] in
    Printf.printf "election %s: verified = %b (%.2f s)\n" el.e_uuid verdict (t1 -. t0);
    exit (if verdict then 0 else 1)
