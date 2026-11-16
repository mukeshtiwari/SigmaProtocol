(* Tokens of the Swiss Post fixture files: JSON punctuation, literals, and
   the field names as keywords (recognised with the colon that follows them,
   so that a string value equal to a field name is still a STRING). *)
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
  (* a test case *)
  | "\"description\"" ws* ':' { DESCRIPTION }
  | "\"context\"" ws* ':' { CONTEXT }
  | "\"input\"" ws* ':' { INPUT }
  | "\"output\"" ws* ':' { OUTPUT }
  | "\"statement\"" ws* ':' { STATEMENT }
  | "\"argument\"" ws* ':' { ARGUMENT }
  | "\"result\"" ws* ':' { RESULT }
  (* the context *)
  | "\"p\"" ws* ':' { P }
  | "\"q\"" ws* ':' { Q }
  | "\"g\"" ws* ':' { G }
  | "\"pk\"" ws* ':' { PK }
  | "\"ck\"" ws* ':' { CK }
  | "\"h\"" ws* ':' { H }
  (* challenges *)
  | "\"x\"" ws* ':' { X }
  | "\"y\"" ws* ':' { Y }
  | "\"z\"" ws* ':' { Z }
  (* statements *)
  | "\"ciphertexts\"" ws* ':' { CIPHERTEXTS }
  | "\"shuffled_ciphertexts\"" ws* ':' { SHUFFLED_CIPHERTEXTS }
  | "\"ciphertext_product\"" ws* ':' { CIPHERTEXT_PRODUCT }
  | "\"gamma\"" ws* ':' { GAMMA }
  | "\"phis\"" ws* ':' { PHIS }
  | "\"c_a\"" ws* ':' { C_A }
  | "\"c_b\"" ws* ':' { C_B }
  | "\"b\"" ws* ':' { B }
  (* arguments *)
  | "\"ca\"" ws* ':' { CA }
  | "\"cb\"" ws* ':' { CB }
  | "\"product_argument\"" ws* ':' { PRODUCT_ARGUMENT }
  | "\"multi_exp_argument\"" ws* ':' { MULTI_EXP_ARGUMENT }
  | "\"single_vpa\"" ws* ':' { SINGLE_VPA }
  | "\"hadamard_argument\"" ws* ':' { HADAMARD_ARGUMENT }
  | "\"cUpperB\"" ws* ':' { CUPPERB }
  | "\"zero_argument\"" ws* ':' { ZERO_ARGUMENT }
  | "\"c_d\"" ws* ':' { C_D }
  | "\"c_lower_delta\"" ws* ':' { C_LOWER_DELTA }
  | "\"c_upper_delta\"" ws* ':' { C_UPPER_DELTA }
  | "\"a_tilde\"" ws* ':' { A_TILDE }
  | "\"b_tilde\"" ws* ':' { B_TILDE }
  | "\"r_tilde\"" ws* ':' { R_TILDE }
  | "\"s_tilde\"" ws* ':' { S_TILDE }
  | "\"c_a0\"" ws* ':' { C_A0 }
  | "\"c_bm\"" ws* ':' { C_BM }
  | "\"a\"" ws* ':' { A }
  | "\"r\"" ws* ':' { R }
  | "\"s\"" ws* ':' { S }
  | "\"t\"" ws* ':' { T }
  | "\"c_a_0\"" ws* ':' { C_A_0 }
  | "\"e\"" ws* ':' { E }
  | "\"tau\"" ws* ':' { TAU }
  | str ws* ':' as s { raise (SyntaxError ("unexpected field " ^ s)) }
  | str as s { STRING (String.sub s 1 (String.length s - 2)) }
  | eof { EOF }
  | _ { raise (SyntaxError ("unexpected character " ^ Lexing.lexeme lexbuf)) }
