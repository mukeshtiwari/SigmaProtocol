(* Tokens of the Belenios archive documents: JSON punctuation, literals,
   and the field names as keywords. A field name is recognised together
   with the colon that follows it, so that a string value equal to a field
   name (a question text, a description) is still a STRING. *)
{
  open Parser
  exception SyntaxError of string
}

let digit = ['0'-'9']
let ws = [' ' '\t' '\r' '\n']
let str = '"' ([^ '"' '\\'] | '\\' _)* '"'

rule token = parse
  | ws+ { token lexbuf }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | ',' { COMMA }
  | "true" { TRUE }
  | "false" { FALSE }
  | "null" { NULL }
  (* events *)
  | "\"height\"" ws* ':' { HEIGHT }
  | "\"parent\"" ws* ':' { PARENT }
  | "\"type\"" ws* ':' { TYPE }
  | "\"payload\"" ws* ':' { PAYLOAD }
  (* setup *)
  | "\"election\"" ws* ':' { ELECTION }
  | "\"trustees\"" ws* ':' { TRUSTEES }
  | "\"credentials\"" ws* ':' { CREDENTIALS }
  (* election *)
  | "\"version\"" ws* ':' { VERSION }
  | "\"description\"" ws* ':' { DESCRIPTION }
  | "\"name\"" ws* ':' { NAME }
  | "\"group\"" ws* ':' { GROUP }
  | "\"public_key\"" ws* ':' { PUBLIC_KEY }
  | "\"questions\"" ws* ':' { QUESTIONS }
  | "\"answers\"" ws* ':' { ANSWERS }
  | "\"blank\"" ws* ':' { BLANK }
  | "\"min\"" ws* ':' { MIN }
  | "\"max\"" ws* ':' { MAX }
  | "\"question\"" ws* ':' { QUESTION }
  | "\"uuid\"" ws* ':' { UUID }
  | "\"administrator\"" ws* ':' { ADMINISTRATOR }
  | "\"credential_authority\"" ws* ':' { CREDENTIAL_AUTHORITY }
  (* trustees and proofs *)
  | "\"pok\"" ws* ':' { POK }
  | "\"challenge\"" ws* ':' { CHALLENGE }
  | "\"response\"" ws* ':' { RESPONSE }
  (* ballots *)
  | "\"election_uuid\"" ws* ':' { ELECTION_UUID }
  | "\"election_hash\"" ws* ':' { ELECTION_HASH }
  | "\"credential\"" ws* ':' { CREDENTIAL }
  | "\"choices\"" ws* ':' { CHOICES }
  | "\"alpha\"" ws* ':' { ALPHA }
  | "\"beta\"" ws* ':' { BETA }
  | "\"individual_proofs\"" ws* ':' { INDIVIDUAL_PROOFS }
  | "\"overall_proof\"" ws* ':' { OVERALL_PROOF }
  | "\"blank_proof\"" ws* ':' { BLANK_PROOF }
  | "\"signature\"" ws* ':' { SIGNATURE }
  | "\"hash\"" ws* ':' { HASH }
  | "\"proof\"" ws* ':' { PROOF }
  (* tally, decryption and result *)
  | "\"num_tallied\"" ws* ':' { NUM_TALLIED }
  | "\"total_weight\"" ws* ':' { TOTAL_WEIGHT }
  | "\"encrypted_tally\"" ws* ':' { ENCRYPTED_TALLY }
  | "\"owner\"" ws* ':' { OWNER }
  | "\"decryption_factors\"" ws* ':' { DECRYPTION_FACTORS }
  | "\"decryption_proofs\"" ws* ':' { DECRYPTION_PROOFS }
  | "\"result\"" ws* ':' { RESULT }
  | str ws* ':' as s { raise (SyntaxError ("unexpected field " ^ s)) }
  | str as s { STRING (String.sub s 1 (String.length s - 2)) }
  | '-'? digit+ as n { INT n }
  | eof { EOF }
  | _ { raise (SyntaxError ("unexpected character " ^ Lexing.lexeme lexbuf)) }
