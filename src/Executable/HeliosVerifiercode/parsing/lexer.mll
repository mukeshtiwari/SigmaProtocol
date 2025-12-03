{
  open Parser
  exception SyntaxError of string
}

let digit = ['0'-'9']
let bigint = '-'? digit+
let whitespace = [' ' '\t' '\r' '\n']
let string_literal = '"' [^'"']* '"'

rule token = parse
  | whitespace+ { token lexbuf }
  | '{' { LBRACE }
  | '}' { RBRACE }
  | '[' { LBRACKET }
  | ']' { RBRACKET }
  | ',' { COMMA }
  | ':' { COLON }
  | ';' { SEMICOLON }
  | "null" { NULL }
  | "\"cast_at\"" { CAST_AT }
  | "\"vote\"" { VOTE }
  | "\"answers\"" { ANSWERS }
  | "\"choices\"" { CHOICES }
  | "\"alpha\"" { ALPHA }
  | "\"beta\"" { BETA }
  | "\"individual_proofs\"" { INDIVIDUAL_PROOFS }
  | "\"overall_proof\"" { OVERALL_PROOF }
  | "\"challenge\"" { CHALLENGE }
  | "\"commitment\"" { COMMITMENT }
  | "\"A\"" { A }
  | "\"B\"" { B }
  | "\"response\"" { RESPONSE }
  | "\"election_hash\"" { ELECTION_HASH }
  | "\"election_uuid\"" { ELECTION_UUID }
  | "\"vote_hash\"" { VOTE_HASH }
  | "\"voter_hash\"" { VOTER_HASH }
  | "\"voter_uuid\"" { VOTER_UUID }
  | "\"decryption_factors\"" { DECRYPTION_FACTORS }
  | "\"decryption_proofs\"" { DECRYPTION_PROOFS }
  | "\"email\"" { EMAIL }
  | "\"pok\"" { POK }
  | "\"public_key\"" { PUBLIC_KEY }
  | "\"public_key_hash\"" { PUBLIC_KEY_HASH }
  | "\"g\"" { G }
  | "\"p\"" { P }
  | "\"q\"" { Q }
  | "\"y\"" { Y }
  | "\"uuid\"" { UUID }
  | string_literal as s { STRING (String.sub s 1 (String.length s - 2)) }
  | ['0' - '9']+ as num { BIGINT num }
  | eof { EOF }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }