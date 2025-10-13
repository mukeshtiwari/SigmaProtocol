{
  open Parser
  exception Lexing_error of string
}

let whitespace = [' ' '\t']+
let newline = '\n'
let digit = ['0'-'9']
let int = ['-']? digit+
let keyword s = s

rule token = parse
  | whitespace { token lexbuf }
  | newline { NEWLINE }
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
  | int as i     { INT i }
  | eof          { EOF }
  | _ as c       { raise (Lexing_error (Printf.sprintf "Unexpected char: %c" c)) }
