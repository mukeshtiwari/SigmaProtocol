{
  open Tallylib.BinInt
  open Parser
  open Tallylib.BinInt.Z
  exception Lexing_error of string
}

let whitespace = [' ' '\t']+

rule token = parse
  | whitespace { token lexbuf }
  | ['\n' '\r']+ {NEWLINE}
  | "ciphertext" { CIPHERTEXT }
  | "proof"      { PROOF }
  | "annoucement" { ANNOUNCEMENT }
  | "announcement" { ANNOUNCEMENT }
  | "challenge"  { CHALLENGE }
  | "response"   { RESPONSE }
  | "("          { LPAR }
  | ")"          { RPAR }
  | "{"          { LBRACE }
  | "}"          { RBRACE }
  | ","          { COMMA }
  | ";"          { SEMI }
  | "="          { EQ }
  | ['0' - '9']+ as num { INT (Big_int_Z.big_int_of_string num) }
  | eof          { EOF }
  | _ as c       { raise (Lexing_error (Printf.sprintf "Unexpected char: %c" c)) }
