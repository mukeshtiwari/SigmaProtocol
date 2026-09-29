%{
  (* The grammar follows the serialisation of Belenios 3.2 (the field order
     of its JSON writers); each document type is a start symbol. Points and
     scalars are validated by Ast when they are read. *)
  open Ast
%}

%token <string> STRING INT
%token LBRACE RBRACE LBRACKET RBRACKET COMMA TRUE FALSE NULL
%token HEIGHT PARENT TYPE PAYLOAD
%token ELECTION TRUSTEES CREDENTIALS
%token VERSION DESCRIPTION NAME GROUP PUBLIC_KEY QUESTIONS ANSWERS BLANK MIN MAX QUESTION UUID
%token ADMINISTRATOR CREDENTIAL_AUTHORITY
%token POK CHALLENGE RESPONSE
%token ELECTION_UUID ELECTION_HASH CREDENTIAL CHOICES ALPHA BETA
%token INDIVIDUAL_PROOFS OVERALL_PROOF BLANK_PROOF SIGNATURE HASH PROOF
%token NUM_TALLIED TOTAL_WEIGHT ENCRYPTED_TALLY OWNER DECRYPTION_FACTORS DECRYPTION_PROOFS RESULT
%token EOF

%start <Ast.event> event
%start <Ast.setup> setup
%start <Ast.election> election
%start <Ast.trustee list> trustees
%start <Ast.credential list> credentials
%start <Ast.ballot> ballot
%start <Ast.tally_header> tally_header
%start <Ast.ciphertext list list> encrypted_tally
%start <Ast.pd_header> pd_header
%start <Ast.partial_decryption> partial_decryption
%start <Ast.result> result

%%

(* ---- the event chain ---- *)

event:
  | LBRACE parent = option(PARENT s = STRING COMMA { s })
    HEIGHT h = INT COMMA TYPE t = STRING payload = option(COMMA PAYLOAD s = STRING { s }) RBRACE EOF
    { { ev_height = int_of_string h; ev_parent = parent; ev_type = t; ev_payload = payload } }

(* ---- setup ---- *)

setup:
  | LBRACE ELECTION e = STRING COMMA TRUSTEES t = STRING COMMA CREDENTIALS c = STRING RBRACE EOF
    { { s_election = e; s_trustees = t; s_credentials = c } }

election:
  | LBRACE VERSION v = INT COMMA DESCRIPTION d = STRING COMMA NAME n = STRING COMMA GROUP g = STRING COMMA
    PUBLIC_KEY y = STRING COMMA QUESTIONS LBRACKET qs = separated_list(COMMA, question) RBRACKET COMMA
    UUID u = STRING list(COMMA election_extra { () }) RBRACE EOF
    { if g <> "Ed25519" then failwith ("only the Ed25519 group is supported: " ^ g);
      { e_version = int_of_string v; e_description = d; e_name = n; e_group = g;
        e_public_key = point_of_hex y; e_questions = qs; e_uuid = u } }

election_extra:
  | ADMINISTRATOR STRING { () }
  | CREDENTIAL_AUTHORITY STRING { () }

question:
  | LBRACE ANSWERS LBRACKET ans = separated_list(COMMA, STRING) RBRACKET COMMA
    blank = option(BLANK b = boolean COMMA { b })
    MIN mn = INT COMMA MAX mx = INT COMMA QUESTION q = STRING RBRACE
    { { q_answers = List.length ans; q_blank = (match blank with Some b -> b | None -> false);
        q_min = int_of_string mn; q_max = int_of_string mx; q_text = q } }
  | LBRACE TYPE json_value list(COMMA member { () }) RBRACE
    { failwith "only homomorphic questions are supported" }

boolean:
  | TRUE { true }
  | FALSE { false }

(* ---- trustees ---- *)

trustees:
  | LBRACKET ts = separated_list(COMMA, trustee) RBRACKET EOF { ts }

trustee:
  | LBRACKET kind = STRING COMMA LBRACE POK pok = proof COMMA PUBLIC_KEY y = STRING RBRACE RBRACKET
    { if kind <> "Single" then failwith ("only Single trustees are supported: " ^ kind);
      { t_public_key = point_of_hex y; t_pok = pok } }

proof:
  | LBRACE CHALLENGE c = STRING COMMA RESPONSE r = STRING RBRACE
    { (scalar_of_string c, scalar_of_string r) }

proof_list:
  | LBRACKET ps = separated_list(COMMA, proof) RBRACKET { ps }

(* ---- credentials ---- *)

credentials:
  | LBRACKET cs = separated_list(COMMA, STRING) RBRACKET EOF { List.map credential_of_string cs }

(* ---- ballots ---- *)

ballot:
  | LBRACE ELECTION_UUID u = STRING COMMA ELECTION_HASH eh = STRING COMMA CREDENTIAL c = STRING COMMA
    ANSWERS LBRACKET ans = separated_list(COMMA, answer) RBRACKET COMMA
    sg = SIGNATURE LBRACE HASH sh = STRING COMMA PROOF sp = proof RBRACE RBRACE EOF
    { ignore sg;
      { b_uuid = u; b_hash = eh; b_credential = point_of_hex c; b_answers = ans;
        b_sig_hash = sh; b_sig_proof = sp; b_sig_pos = $startpos(sg).Lexing.pos_cnum } }

answer:
  | LBRACE CHOICES LBRACKET cs = separated_list(COMMA, ciphertext) RBRACKET COMMA
    INDIVIDUAL_PROOFS LBRACKET ips = separated_list(COMMA, proof_list) RBRACKET COMMA
    OVERALL_PROOF ov = proof_list blank = option(COMMA BLANK_PROOF b = proof_list { b }) RBRACE
    { { a_choices = cs; a_individual = ips; a_overall = ov; a_blank = blank } }

ciphertext:
  | LBRACE ALPHA a = STRING COMMA BETA b = STRING RBRACE
    { { alpha = point_of_hex a; beta = point_of_hex b } }

(* ---- the encrypted tally ---- *)

tally_header:
  | LBRACE NUM_TALLIED n = INT COMMA TOTAL_WEIGHT w = int_or_string COMMA ENCRYPTED_TALLY h = STRING RBRACE EOF
    { { th_num_tallied = int_of_string n; th_total_weight = w; th_encrypted_tally = h } }

encrypted_tally:
  | LBRACKET rows = separated_list(COMMA, ciphertext_row) RBRACKET EOF { rows }

ciphertext_row:
  | LBRACKET cs = separated_list(COMMA, ciphertext) RBRACKET { cs }

(* ---- partial decryptions ---- *)

pd_header:
  | LBRACE OWNER o = INT COMMA PAYLOAD p = STRING RBRACE EOF
    { { pd_owner = int_of_string o; pd_payload = p } }

partial_decryption:
  | LBRACE DECRYPTION_FACTORS LBRACKET fs = separated_list(COMMA, point_row) RBRACKET COMMA
    DECRYPTION_PROOFS LBRACKET ps = separated_list(COMMA, proof_list) RBRACKET RBRACE EOF
    { { pd_factors = fs; pd_proofs = ps } }

point_row:
  | LBRACKET ps = separated_list(COMMA, STRING) RBRACKET { List.map (fun s -> (point_of_hex s).pt) ps }

(* ---- the result ---- *)

result:
  | LBRACE RESULT LBRACKET rs = separated_list(COMMA, scalar_row) RBRACKET RBRACE EOF { rs }

scalar_row:
  | LBRACKET xs = separated_list(COMMA, int_or_string) RBRACKET { List.map scalar_of_string xs }

(* Belenios writes small numbers as JSON numbers and big ones as strings *)
int_or_string:
  | s = STRING { s }
  | n = INT { n }

(* ---- generic JSON, to skip the body of an unsupported question ---- *)

json_value:
  | STRING { () }
  | INT { () }
  | TRUE { () }
  | FALSE { () }
  | NULL { () }
  | LBRACKET separated_list(COMMA, json_value) RBRACKET { () }
  | LBRACE separated_list(COMMA, member) RBRACE { () }

member:
  | anykey json_value { () }

anykey:
  | HEIGHT | PARENT | TYPE | PAYLOAD | ELECTION | TRUSTEES | CREDENTIALS
  | VERSION | DESCRIPTION | NAME | GROUP | PUBLIC_KEY | QUESTIONS | ANSWERS | BLANK | MIN | MAX | QUESTION | UUID
  | ADMINISTRATOR | CREDENTIAL_AUTHORITY | POK | CHALLENGE | RESPONSE
  | ELECTION_UUID | ELECTION_HASH | CREDENTIAL | CHOICES | ALPHA | BETA
  | INDIVIDUAL_PROOFS | OVERALL_PROOF | BLANK_PROOF | SIGNATURE | HASH | PROOF
  | NUM_TALLIED | TOTAL_WEIGHT | ENCRYPTED_TALLY | OWNER | DECRYPTION_FACTORS | DECRYPTION_PROOFS | RESULT
    { () }
