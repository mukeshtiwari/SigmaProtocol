(* Tokens of the ElectionGuard record files: JSON punctuation, literals, the
   field names the verifier uses as keywords, and every other field name as
   KEY (its value is skipped by the grammar). A field name is recognised
   together with the colon that follows it, so a string value equal to a
   field name is still a STRING. *)
{
  open Parser
  exception SyntaxError of string
}

let digit = ['0'-'9']
let ws = [' ' '\t' '\r' '\n']
let str = '"' ([^ '"' '\\'] | '\\' _)* '"'
let number = '-'? digit+ ('.' digit+)? (['e' 'E'] ['+' '-']? digit+)?

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
  (* constants and configuration *)
  | "\"large_prime\"" ws* ':' { LARGE_PRIME }
  | "\"small_prime\"" ws* ':' { SMALL_PRIME }
  | "\"cofactor\"" ws* ':' { COFACTOR }
  | "\"generator\"" ws* ':' { GENERATOR }
  | "\"config_version\"" ws* ':' { CONFIG_VERSION }
  | "\"number_of_guardians\"" ws* ':' { NUMBER_OF_GUARDIANS }
  | "\"quorum\"" ws* ':' { QUORUM }
  | "\"parameter_base_hash\"" ws* ':' { PARAMETER_BASE_HASH }
  | "\"manifest_hash\"" ws* ':' { MANIFEST_HASH }
  | "\"election_base_hash\"" ws* ':' { ELECTION_BASE_HASH }
  (* the manifest *)
  | "\"contests\"" ws* ':' { CONTESTS }
  | "\"object_id\"" ws* ':' { OBJECT_ID }
  | "\"sequence_order\"" ws* ':' { SEQUENCE_ORDER }
  | "\"votes_allowed\"" ws* ':' { VOTES_ALLOWED }
  | "\"option_selection_limit\"" ws* ':' { OPTION_SELECTION_LIMIT }
  | "\"ballot_selections\"" ws* ':' { BALLOT_SELECTIONS }
  (* initialisation *)
  | "\"joint_public_key\"" ws* ':' { JOINT_PUBLIC_KEY }
  | "\"extended_base_hash\"" ws* ':' { EXTENDED_BASE_HASH }
  | "\"guardians\"" ws* ':' { GUARDIANS }
  | "\"x_coordinate\"" ws* ':' { X_COORDINATE }
  | "\"coefficient_proofs\"" ws* ':' { COEFFICIENT_PROOFS }
  | "\"public_key\"" ws* ':' { PUBLIC_KEY }
  | "\"challenge\"" ws* ':' { CHALLENGE }
  | "\"response\"" ws* ':' { RESPONSE }
  (* ballots, tallies and decryptions *)
  | "\"ballot_id\"" ws* ':' { BALLOT_ID }
  | "\"election_id\"" ws* ':' { ELECTION_ID }
  | "\"state\"" ws* ':' { STATE }
  | "\"code_baux\"" ws* ':' { CODE_BAUX }
  | "\"confirmation_code\"" ws* ':' { CONFIRMATION_CODE }
  | "\"contest_id\"" ws* ':' { CONTEST_ID }
  | "\"contest_hash\"" ws* ':' { CONTEST_HASH }
  | "\"selections\"" ws* ':' { SELECTIONS }
  | "\"selection_id\"" ws* ':' { SELECTION_ID }
  | "\"encrypted_vote\"" ws* ':' { ENCRYPTED_VOTE }
  | "\"pad\"" ws* ':' { PAD }
  | "\"data\"" ws* ':' { DATA }
  | "\"proof\"" ws* ':' { PROOF }
  | "\"proofs\"" ws* ':' { PROOFS }
  | "\"tally\"" ws* ':' { TALLY }
  | "\"b_over_m\"" ws* ':' { B_OVER_M }
  | "\"id\"" ws* ':' { ID }
  | str ws* ':' as s { KEY s }
  | str as s { STRING (String.sub s 1 (String.length s - 2)) }
  | number as n { NUMBER n }
  | eof { EOF }
  | _ { raise (SyntaxError ("unexpected character " ^ Lexing.lexeme lexbuf)) }
