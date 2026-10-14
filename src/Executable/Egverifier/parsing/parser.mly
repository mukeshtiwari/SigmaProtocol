%{
  (* One start symbol per record file. Objects are lists of keyed members in
     any order; Ast's builders assemble the fields the verifier uses and the
     others are skipped (KEY, or a keyword that is not used in that object,
     followed by any JSON value). Elements and scalars are validated by Ast
     when they are read. *)
  open Ast
%}

%token <string> STRING NUMBER KEY
%token LBRACE RBRACE LBRACKET RBRACKET COMMA TRUE FALSE NULL
%token LARGE_PRIME SMALL_PRIME COFACTOR GENERATOR
%token CONFIG_VERSION NUMBER_OF_GUARDIANS QUORUM PARAMETER_BASE_HASH MANIFEST_HASH ELECTION_BASE_HASH
%token CONTESTS OBJECT_ID SEQUENCE_ORDER VOTES_ALLOWED OPTION_SELECTION_LIMIT BALLOT_SELECTIONS
%token JOINT_PUBLIC_KEY EXTENDED_BASE_HASH GUARDIANS X_COORDINATE COEFFICIENT_PROOFS PUBLIC_KEY CHALLENGE RESPONSE
%token BALLOT_ID ELECTION_ID STATE CODE_BAUX CONFIRMATION_CODE CONTEST_ID CONTEST_HASH SELECTIONS SELECTION_ID
%token ENCRYPTED_VOTE PAD DATA PROOF PROOFS TALLY B_OVER_M ID
%token EOF

%start <Ast.constants> constants
%start <Ast.config> config
%start <Ast.manifest> manifest
%start <Ast.initialized> initialized
%start <Ast.eballot> eballot
%start <Ast.encrypted_tally> encrypted_tally
%start <Ast.decryptions> decryptions

%%

(* ---- the files ---- *)

constants:
  | LBRACE ms = separated_list(COMMA, constants_member) RBRACE EOF { build_constants ms }
constants_member:
  | LARGE_PRIME s = STRING { `Large_prime (z_of_hex s) }
  | SMALL_PRIME s = STRING { `Small_prime (z_of_hex s) }
  | COFACTOR s = STRING { `Cofactor (z_of_hex s) }
  | GENERATOR s = STRING { `Generator (z_of_hex s) }
  | skipped { `Skip }

config:
  | LBRACE ms = separated_list(COMMA, config_member) RBRACE EOF { build_config ms }
config_member:
  | CONFIG_VERSION s = STRING { `Config_version s }
  | NUMBER_OF_GUARDIANS n = integer { `Number_of_guardians n }
  | QUORUM n = integer { `Quorum n }
  | PARAMETER_BASE_HASH s = STRING { `Parameter_base_hash s }
  | MANIFEST_HASH s = STRING { `Manifest_hash s }
  | ELECTION_BASE_HASH s = STRING { `Election_base_hash s }
  | skipped { `Skip }

manifest:
  | LBRACE ms = separated_list(COMMA, manifest_member) RBRACE EOF { build_manifest ms }
manifest_member:
  | CONTESTS LBRACKET cs = separated_list(COMMA, contest_spec) RBRACKET { `Contests cs }
  | skipped { `Skip }

contest_spec:
  | LBRACE ms = separated_list(COMMA, contest_spec_member) RBRACE { build_contest_spec ms }
contest_spec_member:
  | OBJECT_ID s = STRING { `Object_id s }
  | SEQUENCE_ORDER n = integer { `Sequence_order n }
  | VOTES_ALLOWED n = integer { `Votes_allowed n }
  | OPTION_SELECTION_LIMIT n = integer { `Option_selection_limit n }
  | BALLOT_SELECTIONS LBRACKET ss = separated_list(COMMA, selection_spec) RBRACKET { `Ballot_selections ss }
  | skipped { `Skip }

selection_spec:
  | LBRACE ms = separated_list(COMMA, selection_spec_member) RBRACE { build_selection_spec ms }
selection_spec_member:
  | OBJECT_ID s = STRING { `Object_id s }
  | SEQUENCE_ORDER n = integer { `Sequence_order n }
  | skipped { `Skip }

initialized:
  | LBRACE ms = separated_list(COMMA, initialized_member) RBRACE EOF { build_initialized ms }
initialized_member:
  | JOINT_PUBLIC_KEY s = STRING { `Joint_public_key (elem_of_hex s) }
  | EXTENDED_BASE_HASH s = STRING { `Extended_base_hash s }
  | GUARDIANS LBRACKET gs = separated_list(COMMA, guardian) RBRACKET { `Guardians gs }
  | skipped { `Skip }

guardian:
  | LBRACE ms = separated_list(COMMA, guardian_member) RBRACE { build_guardian ms }
guardian_member:
  | X_COORDINATE n = integer { `X_coordinate n }
  | COEFFICIENT_PROOFS LBRACKET cs = separated_list(COMMA, coefficient) RBRACKET { `Coefficient_proofs cs }
  | skipped { `Skip }

coefficient:
  | LBRACE ms = separated_list(COMMA, coefficient_member) RBRACE { build_coefficient ms }
coefficient_member:
  | PUBLIC_KEY s = STRING { `Public_key (elem_of_hex s) }
  | CHALLENGE s = STRING { `Challenge (scalar_of_hex s) }
  | RESPONSE s = STRING { `Response (scalar_of_hex s) }
  | skipped { `Skip }

eballot:
  | LBRACE ms = separated_list(COMMA, eballot_member) RBRACE EOF { build_eballot ms }
eballot_member:
  | BALLOT_ID s = STRING { `Ballot_id s }
  | ELECTION_ID s = STRING { `Election_id s }
  | STATE s = STRING { `State s }
  | CODE_BAUX s = STRING { `Code_baux s }
  | CONFIRMATION_CODE s = STRING { `Confirmation_code s }
  | CONTESTS LBRACKET cs = separated_list(COMMA, contest) RBRACKET { `Contests cs }
  | skipped { `Skip }

contest:
  | LBRACE ms = separated_list(COMMA, contest_member) RBRACE { build_contest ms }
contest_member:
  | CONTEST_ID s = STRING { `Contest_id s }
  | SEQUENCE_ORDER n = integer { `Sequence_order n }
  | CONTEST_HASH s = STRING { `Contest_hash s }
  | SELECTIONS LBRACKET ss = separated_list(COMMA, selection) RBRACKET { `Selections ss }
  | PROOF ps = proofs { `Proofs ps }
  | VOTES_ALLOWED json_value { `Skip }
  | skipped { `Skip }

selection:
  | LBRACE ms = separated_list(COMMA, selection_member) RBRACE { build_selection ms }
selection_member:
  | SELECTION_ID s = STRING { `Selection_id s }
  | SEQUENCE_ORDER n = integer { `Sequence_order n }
  | ENCRYPTED_VOTE c = ciphertext { `Encrypted_vote c }
  | PROOF ps = proofs { `Proofs ps }
  | skipped { `Skip }

(* the range and selection-limit proofs: {"proofs": [{"challenge", "response"}, …]} *)
proofs:
  | LBRACE ms = separated_list(COMMA, proofs_member) RBRACE { build_proofs ms }
proofs_member:
  | PROOFS LBRACKET ps = separated_list(COMMA, proof) RBRACKET { `Proofs ps }
  | skipped { `Skip }

proof:
  | LBRACE ms = separated_list(COMMA, proof_member) RBRACE { build_proof ms }
proof_member:
  | CHALLENGE s = STRING { `Challenge (scalar_of_hex s) }
  | RESPONSE s = STRING { `Response (scalar_of_hex s) }
  | skipped { `Skip }

ciphertext:
  | LBRACE ms = separated_list(COMMA, ciphertext_member) RBRACE { build_ciphertext ms }
ciphertext_member:
  | PAD s = STRING { `Pad (elem_of_hex s) }
  | DATA s = STRING { `Data (elem_of_hex s) }
  | skipped { `Skip }

encrypted_tally:
  | LBRACE ms = separated_list(COMMA, encrypted_tally_member) RBRACE EOF { build_encrypted_tally ms }
encrypted_tally_member:
  | ELECTION_ID s = STRING { `Election_id s }
  | CONTESTS LBRACKET cs = separated_list(COMMA, tally_contest) RBRACKET { `Contests cs }
  | skipped { `Skip }

tally_contest:
  | LBRACE ms = separated_list(COMMA, tally_contest_member) RBRACE { build_tally_contest ms }
tally_contest_member:
  | CONTEST_ID s = STRING { `Contest_id s }
  | SEQUENCE_ORDER n = integer { `Sequence_order n }
  | SELECTIONS LBRACKET ss = separated_list(COMMA, tally_selection) RBRACKET { `Selections ss }
  | skipped { `Skip }

tally_selection:
  | LBRACE ms = separated_list(COMMA, tally_selection_member) RBRACE { build_tally_selection ms }
tally_selection_member:
  | SELECTION_ID s = STRING { `Selection_id s }
  | SEQUENCE_ORDER n = integer { `Sequence_order n }
  | ENCRYPTED_VOTE c = ciphertext { `Encrypted_vote c }
  | skipped { `Skip }

(* tally.json and challenged ballots *)
decryptions:
  | LBRACE ms = separated_list(COMMA, decryptions_member) RBRACE EOF { build_decryptions ms }
decryptions_member:
  | ID s = STRING { `Id s }
  | ELECTION_ID s = STRING { `Election_id s }
  | CONTESTS LBRACKET cs = separated_list(COMMA, dcontest) RBRACKET { `Contests cs }
  | skipped { `Skip }

dcontest:
  | LBRACE ms = separated_list(COMMA, dcontest_member) RBRACE { build_dcontest ms }
dcontest_member:
  | CONTEST_ID s = STRING { `Contest_id s }
  | SELECTIONS LBRACKET ds = separated_list(COMMA, decryption) RBRACKET { `Selections ds }
  | SEQUENCE_ORDER json_value { `Skip }
  | skipped { `Skip }

decryption:
  | LBRACE ms = separated_list(COMMA, decryption_member) RBRACE { build_decryption ms }
decryption_member:
  | SELECTION_ID s = STRING { `Selection_id s }
  | TALLY n = integer { `Tally n }
  | B_OVER_M s = STRING { `B_over_m (elem_of_hex s) }
  | ENCRYPTED_VOTE c = ciphertext { `Encrypted_vote c }
  | PROOF p = proof { `Proof p }
  | SEQUENCE_ORDER json_value { `Skip }
  | skipped { `Skip }

(* ---- integers, and the generic JSON of skipped fields ---- *)

integer:
  | n = NUMBER { match int_of_string_opt n with Some k -> k | None -> failwith ("not an integer: " ^ n) }

(* a field the verifier does not use *)
skipped:
  | KEY json_value { () }

json_value:
  | STRING { () }
  | NUMBER { () }
  | TRUE { () }
  | FALSE { () }
  | NULL { () }
  | LBRACKET separated_list(COMMA, json_value) RBRACKET { () }
  | LBRACE separated_list(COMMA, json_member) RBRACE { () }

json_member:
  | anykey json_value { () }

anykey:
  | KEY { () }
  | LARGE_PRIME | SMALL_PRIME | COFACTOR | GENERATOR
  | CONFIG_VERSION | NUMBER_OF_GUARDIANS | QUORUM | PARAMETER_BASE_HASH | MANIFEST_HASH | ELECTION_BASE_HASH
  | CONTESTS | OBJECT_ID | SEQUENCE_ORDER | VOTES_ALLOWED | OPTION_SELECTION_LIMIT | BALLOT_SELECTIONS
  | JOINT_PUBLIC_KEY | EXTENDED_BASE_HASH | GUARDIANS | X_COORDINATE | COEFFICIENT_PROOFS | PUBLIC_KEY | CHALLENGE | RESPONSE
  | BALLOT_ID | ELECTION_ID | STATE | CODE_BAUX | CONFIRMATION_CODE | CONTEST_ID | CONTEST_HASH | SELECTIONS | SELECTION_ID
  | ENCRYPTED_VOTE | PAD | DATA | PROOF | PROOFS | TALLY | B_OVER_M | ID
    { () }
