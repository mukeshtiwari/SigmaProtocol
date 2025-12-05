open HeliosTallylib.HeliosTallyIns
open HeliosTallylib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak
open Helios_parser
open Helios_parser.Parser
open Ast 

let rec vector_to_string (printer : 'a -> string) (sep : string) (v : 'a HeliosTallylib.VectorDef.t) : string =
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) ->
      (printer h) ^ 
      (if r = Coq_nil then "" else sep ^ " " ^ vector_to_string printer sep r)

(* Specializations *)

let vector_string sep =
  vector_to_string Big_int_Z.string_of_big_int sep

let vector_string_pair sep =
  vector_to_string (fun (h1, h2) ->
    "(" ^ Big_int_Z.string_of_big_int h1 ^ ", " ^ Big_int_Z.string_of_big_int h2 ^ ")") sep 

let rec iterate_char (c : string) (n : int) : string =
    if n = 0 then "" else c^iterate_char c (n - 1)

let proof_string_pair (proof : (Z.t, Z.t * Z.t) HeliosTallylib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string_pair "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 

let proof_and_enc_string (u : (Z.t, Z.t) HeliosTallylib.HeliosTally.ballot) = 
    match u with 
    | (((((((cast_at, cipher_vec), proof_vec), election_hash), election_uuid), vote_hash), voter_hash), voter_uuid) -> 
      "cast_at: " ^ cast_at ^"; encrypted ballot: [" ^ vector_string_pair ", " cipher_vec ^ "]; encryption proof of 0 or 1: [" ^ 
      vector_to_string proof_string_pair "," proof_vec ^ "]; election_hash: " ^ election_hash ^ "; election_uuid: " ^ election_uuid ^ "; " ^ 
      "vote_hash: " ^ vote_hash ^ "; voter_hash: " ^ voter_hash ^ "; voter_uuid: " ^ voter_uuid 




let rec print_count (bs : (Z.t, Z.t) HeliosTallylib.HeliosTally.count) : string = 
  match bs with 
  | Coq_ax ms -> "Identity-tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
  | Coq_cvalid (u, us, vbs, inbs, ms, nms, p) -> print_count p ^ "Valid ballot : " ^ proof_and_enc_string u  ^ 
    "\nPrevious tally : " ^ vector_string_pair " " ms ^ 
    "\nCurrent tally : " ^ vector_string_pair " " nms ^ "\n" ^ iterate_char "-" 150 ^ "\n" 
  | Coq_cinvalid (u, us, vbs, inbs, ms, p) -> print_count p ^ "Invalid ballot : " ^ proof_and_enc_string u ^ 
    "\nPrevious tally : " ^ vector_string_pair " " ms ^ 
    "\nCurrent tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
  | Coq_finish (us, vbs, inbs, ms, ts, pt, ds, bptds, bdec, bpok, bhmul, b, p) -> print_count p ^
    "Final tally: [" ^ vector_string_pair " " ms ^ "]\nFinal decrypted tally: [" ^ vector_string " " ds 
    ^ "]\nFinal DL-search tally: [" ^ vector_string " " pt ^ "]\n" ^ 
    "Plaintext tally is correct decryption of the encrypted tally : " ^ string_of_bool bptds ^ 
    "\nTalliers' decryption factor and proofs are valid : "  ^ string_of_bool bdec ^ 
    "\nTalliers' pok are valid : " ^ string_of_bool bpok ^ 
    "\nPublic key h is equal to all public keys of talliers : " ^ string_of_bool bhmul ^ "\n" ^ iterate_char "-" 150 ^ "\n"


 
let _ = 
  let (bs, us, rs) = Parser.main Lexer.token (Lexing.from_channel stdin) in
  let result = HeliosTallylib.HeliosTallyIns.compute_final_count_ins 
    (Big_int_Z.big_int_of_int 6) (Big_int_Z.big_int_of_int 2) 
    (HeliosTallylib.HeliosTallyIns.h2023) bs us rs in 
  match result with
  | HeliosTallylib.Specif.Coq_existT (bfinal, 
    HeliosTallylib.Specif.Coq_existT (vbs, 
    HeliosTallylib.Specif.Coq_existT (inbs, count))) -> 
    Printf.printf "Count : %s\n" (print_count count);
    Printf.printf "Final tally: [%b]\n" bfinal;
    Printf.printf "All votes : [%d]\n" (List.length bs);
    Printf.printf "Valid vote : [%d]\n" (List.length vbs);
    Printf.printf "Invalid votes : [%d]\n" (List.length inbs);
    

  