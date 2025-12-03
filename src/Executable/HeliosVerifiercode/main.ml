open HeliosTallylib.HeliosTallyIns
open HeliosTallylib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak
open Helios_parser
open Helios_parser.Parser
open Ast 

let string_of_token = function
  | LBRACE -> "LBRACE"
  | RBRACE -> "RBRACE"
  | LBRACKET -> "LBRACKET"
  | RBRACKET -> "RBRACKET"
  | COLON -> "COLON"
  | COMMA -> "COMMA"
  | STRING s -> "STRING(" ^ s ^ ")"
  | BIGINT s -> "BIGINT(" ^ s ^ ")"
  | EOF -> "EOF"
  | Y -> "Y"
  | VOTE_HASH -> "VOTE_HASH"
  | VOTER_HASH -> "VOTER_HASH"
  | VOTER_UUID -> "VOTER_UUID"
  | ELECTION_HASH -> "ELECTION_HASH"
  | ELECTION_UUID -> "ELECTION_UUID"
  | CAST_AT -> "CAST_AT"
  | ALPHA -> "ALPHA"
  | BETA -> "BETA"
  | SEMICOLON -> "SEMICOLON"
  | _ -> "OTHER_TOKEN"


  (* 
  type ballot = 
  ((((((string * ('g * 'g) t) * ('f, 'g * 'g) sigma_proto t)
   * string)
  * string)
 * string)
* string)
* string
  

type ballot' = (Big_int_Z.big_int, Big_int_Z.big_int) ballot
  
*)

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


let proof_string (proof : (Z.t, Z.t) HeliosTallylib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 
let cipher_string (cp : (Z.t * Z.t)) : string = 
  match cp with 
  |(cpa, cpb) -> "ciphertext = (" ^ Big_int_Z.string_of_big_int cpa ^ ", " ^ Big_int_Z.string_of_big_int cpb ^ ")"

let proof_and_enc_string (cppf : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto)) : string = 
  match cppf with
  | (cp, pf) ->  cipher_string cp ^ " "^  proof_string_pair pf 

let rec print_count (bs : (Z.t, Z.t) HeliosTallylib.HeliosTally.count) : string = 
  match bs with 
  | Coq_ax ms -> "Identity-tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
  | Coq_cvalid (u, us, vbs, inbs, ms, nms, p) -> print_count p ^ "Valid ballot : " (*^ vector_to_string proof_and_enc_string " " u *) ^ " \nPrevious tally : " ^ vector_string_pair " " ms ^ 
    "\nCurrent tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n" 
  | Coq_cinvalid (u, us, vbs, inbs, ms, p) -> print_count p ^ "Invalid ballot : " (* ^ vector_to_string proof_and_enc_string " " u *) ^ " \nPrevious tally : " ^ vector_string_pair " " ms ^ 
    "\nCurrent tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
  | Coq_finish (us, vbs, inbs, ms, ts, pt, ds, bptds, bdec, bpok, bhmul, b, p) -> print_count p ^ "pt is the correct plaintext tally: " ^ string_of_bool bptds ^ 
    ", all talliers' decryption factor and proofs are valid: "  ^ string_of_bool bdec ^ ", talliers' pok is valid: " ^ string_of_bool bpok ^ 
    ", public key h is equal to all public keys of talliers: " ^ string_of_bool bhmul ^ "\n" ^ iterate_char "-" 150 ^ "\n"


 
let _ = 
  let (bs, us, rs) = Parser.main Lexer.token (Lexing.from_channel stdin) in
  let result = HeliosTallylib.HeliosTallyIns.compute_final_count_ins 
    (Big_int_Z.big_int_of_int 7) 
    (Big_int_Z.big_int_of_int 2) bs us rs in 
  match result with
  | HeliosTallylib.Specif.Coq_existT (bfinal, 
    HeliosTallylib.Specif.Coq_existT (vbs, 
    HeliosTallylib.Specif.Coq_existT (inbs, count))) -> 
    Printf.printf "Count : %s\n" (print_count count)
    (*  
    Printf.printf "Final tally: [%b]\n" bfinal;
    Printf.printf "All votes : [%d]\n" (List.length bs);
    Printf.printf "Valid vote : [%d]\n" (List.length vbs);
    Printf.printf "Invalid votes : [%d]\n" (List.length inbs);
    *)
(* 
let _ =
  let lexbuf = Lexing.from_channel stdin in
  let rec loop () =
    let tok = Lexer.token lexbuf in
    print_endline (string_of_token tok);
    if tok <> EOF then loop ()
  in
  loop ()
*)

  