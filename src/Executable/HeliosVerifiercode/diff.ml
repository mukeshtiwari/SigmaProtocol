(* Differential-testing mode of the certified Helios verifier
   (bench/helios-diff): for each election file (the IACR bulletin-board
   format read by main.ml), the verdicts of compute_final_count_ins
   component by component, as one JSON object per line:

     {"file", "parse": "ok" | error, "ballots": [true|false, ...],
      "pk": b, "decryption": b, "pok": b, "tally": b, "final": b}

   The extracted verifier indexes ballots and talliers by vectors of fixed
   length (n candidates, m trustees), and the parser builds them from lists
   of any length. The shapes are checked here, at the trusted boundary,
   before the certified code runs: a ballot whose choices or proofs are not
   n long is invalid (as in Helios); talliers, their factors and proofs, or
   a result of the wrong length reject the election.

   A ballot is bound to its election by its election_hash and election_uuid
   (Helios's EncryptedVote.verify); the certified verifier does not read
   them, so a ballot whose hash or UUID is not the election's is invalid
   here, at the boundary (found by bench/helios-diff).

   usage: diff.exe N_CANDIDATES N_TRUSTEES H ELECTION_HASH ELECTION_UUID FILE... *)
open HeliosTallylib.HeliosTallyIns
open HeliosTallylib.HeliosTally
open Helios_parser

let rec list_of_vector (v : 'a HeliosTallylib.VectorDef.t) : 'a list =
  match v with HeliosTallylib.VectorDef.Coq_nil -> [] | Coq_cons (h, _, t) -> h :: list_of_vector t

let json_bool b = if b then "true" else "false"
let json_str s = Yojson.Safe.to_string (`String s)

let () =
  let n = int_of_string Sys.argv.(1) and m = int_of_string Sys.argv.(2) in
  if n < 1 || m < 1 then failwith "N_CANDIDATES and N_TRUSTEES must be positive";
  let h = Big_int_Z.big_int_of_string Sys.argv.(3) in
  let ehash = Sys.argv.(4) and euuid = Sys.argv.(5) in
  for i = 6 to Array.length Sys.argv - 1 do
    let file = Sys.argv.(i) in
    let reject err =
      Printf.printf "{\"file\": %s, \"parse\": %s, \"ballots\": [], \"pk\": false, \"decryption\": false, \"pok\": false, \"tally\": false, \"final\": false}\n%!"
        (json_str file) (json_str err) in
    match
      let ic = open_in_bin file in
      let r = try Ok (Parser.main Lexer.token (Lexing.from_channel ic))
        with Failure e -> Error e | Parser.Error -> Error "syntax error" | Lexer.SyntaxError e -> Error e
           | e -> Error (Printexc.to_string e) in
      close_in ic; r
    with
    | Error e -> reject e
    | Ok (bs, ts, rs) ->
      let len v = List.length (list_of_vector v) in
      let trustees = list_of_vector ts in
      if List.length trustees <> m then reject "shape: number of trustees"
      else if len rs <> n then reject "shape: result length"
      else if List.exists (fun ((((((fs, ps), _), _), _), _), _) -> len fs <> n || len ps <> n) trustees
      then reject "shape: decryption factors or proofs"
      else begin
        let well_formed (((((((_, cs), ps), eh), eu), _), _), _) = len cs = n && len ps = n && eh = ehash && eu = euuid in
        let good = List.filter well_formed bs in
        (* compute_final_count_ins takes the talliers as a vector of length 1 + m' *)
        let HeliosTallylib.Specif.Coq_existT (bfinal, HeliosTallylib.Specif.Coq_existT (vbs, HeliosTallylib.Specif.Coq_existT (_, count))) =
          compute_final_count_ins (Big_int_Z.big_int_of_int n) (Big_int_Z.big_int_of_int (m - 1)) h good ts rs in
        let pk, dec, pok, tally = match count with
          | Coq_finish (_, _, _, _, _, _, _, bptds, bdec, bpok, bhmul, _, _) -> (bhmul, bdec, bpok, bptds)
          | _ -> (false, false, false, false) in
        (* the parser returns the ballots in reverse order; report them in file order *)
        let valid = List.map (fun b -> List.memq b vbs) (List.rev bs) in
        Printf.printf "{\"file\": %s, \"parse\": \"ok\", \"ballots\": [%s], \"pk\": %s, \"decryption\": %s, \"pok\": %s, \"tally\": %s, \"final\": %s}\n%!"
          (json_str file) (String.concat ", " (List.map json_bool valid))
          (json_bool pk) (json_bool dec) (json_bool pok) (json_bool tally) (json_bool bfinal)
      end
  done
