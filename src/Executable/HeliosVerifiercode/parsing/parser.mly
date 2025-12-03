%{
  open Ast
  open Big_int_Z
%}


%token <string> BIGINT STRING
%token LBRACE RBRACE LBRACKET RBRACKET
%token COMMA COLON NULL
%token CAST_AT VOTE ANSWERS CHOICES ALPHA BETA
%token INDIVIDUAL_PROOFS OVERALL_PROOF CHALLENGE COMMITMENT A B RESPONSE
%token ELECTION_HASH ELECTION_UUID VOTE_HASH VOTER_HASH VOTER_UUID
%token DECRYPTION_FACTORS DECRYPTION_PROOFS EMAIL POK PUBLIC_KEY PUBLIC_KEY_HASH
%token G P Q Y
%token SEMICOLON UUID
%token EOF


%start main
%type <(ballot' list * tallier' HeliosTallylib.VectorDef.t * big_int HeliosTallylib.VectorDef.t )> main

%%

main:
  | bs = voters SEMICOLON ts = trustees SEMICOLON rs = result EOF { (bs, ts, rs) }
  

voters:
  | vs = list(voter_section) { List.rev vs }
  

voter_section:
  | vd = voter_data { vd : ballot' }
  

voter_data:
  | LBRACE vf = voter_fields RBRACE { vf : ballot' }
  

voter_fields:
  | CAST_AT COLON cast_at = STRING COMMA
    VOTE COLON LBRACE vf = vote_fields RBRACE COMMA
    VOTE_HASH COLON vote_hash = STRING COMMA
    VOTER_HASH COLON voter_hash = STRING COMMA
    VOTER_UUID COLON voter_uuid = STRING
    { 
      let ((choices_vec, proofs_vec), election_hash, election_uuid) = vf in
      (((((((cast_at, choices_vec), proofs_vec), election_hash), election_uuid), vote_hash), voter_hash), voter_uuid) : ballot'
    }
  
  

vote_fields:
  | ANSWERS COLON LBRACKET al = answer_list RBRACKET COMMA 
    ELECTION_HASH COLON election_hash = STRING COMMA
    ELECTION_UUID COLON election_uuid = STRING 
    { (al, election_hash, election_uuid) : 
      ((Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.VectorDef.t * 
      (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.Sigma.sigma_proto 
      HeliosTallylib.VectorDef.t) * string * string }
  

answer_list:
  | LBRACE af = answer_fields RBRACE 
    { af : 
      ((Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.VectorDef.t * 
      (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.Sigma.sigma_proto 
      HeliosTallylib.VectorDef.t) }
  

answer_fields:
  | CHOICES COLON LBRACKET cl = separated_nonempty_list(COMMA, choice) RBRACKET COMMA
    INDIVIDUAL_PROOFS COLON LBRACKET pl = separated_nonempty_list(COMMA, proof) RBRACKET COMMA
    OVERALL_PROOF COLON NULL
    { 
      (vector_of_list cl, vector_of_list pl) : 
      ((Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.VectorDef.t * 
      (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.Sigma.sigma_proto 
      HeliosTallylib.VectorDef.t) 
    }
  
  
 
choice:
  | LBRACE ALPHA COLON a = STRING COMMA BETA COLON b = STRING RBRACE 
    { (big_int_of_string a, big_int_of_string b) : Big_int_Z.big_int * Big_int_Z.big_int}
  
 

proof:
  | LBRACKET 
    LBRACE 
    CHALLENGE COLON cone = STRING COMMA
    COMMITMENT COLON LBRACE A COLON aone = STRING COMMA B COLON atwo = STRING RBRACE COMMA
    RESPONSE COLON rone = STRING 
    RBRACE 
    COMMA
    LBRACE 
    CHALLENGE COLON ctwo = STRING COMMA
    COMMITMENT COLON LBRACE A COLON bone = STRING COMMA B COLON btwo = STRING RBRACE COMMA
    RESPONSE COLON rtwo = STRING 
    RBRACE
    RBRACKET
    { 
      {
        HeliosTallylib.Sigma.announcement = vector_of_list [(big_int_of_string aone, big_int_of_string atwo); (big_int_of_string bone, big_int_of_string btwo)];
        HeliosTallylib.Sigma.challenge = vector_of_list 
          [mod_big_int (add_big_int (big_int_of_string cone) (big_int_of_string ctwo)) HeliosTallylib.HeliosTallyIns.q; 
          big_int_of_string cone; big_int_of_string ctwo];
        HeliosTallylib.Sigma.response = vector_of_list [big_int_of_string rone; big_int_of_string rtwo]
      } : (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) HeliosTallylib.Sigma.sigma_proto

    }


trustees:
  | LBRACKET tl = separated_nonempty_list(COMMA, trustee) RBRACKET 
  { vector_of_list tl : tallier' HeliosTallylib.VectorDef.t}
  


trustee:
  | LBRACE tf = trustee_fields RBRACE { tf : tallier'}
  

trustee_fields:
  | DECRYPTION_FACTORS COLON LBRACKET LBRACKET fl = separated_nonempty_list(COMMA, factors) RBRACKET RBRACKET COMMA
    DECRYPTION_PROOFS COLON LBRACKET LBRACKET pl = separated_nonempty_list(COMMA, proofs) RBRACKET RBRACKET COMMA
    EMAIL COLON email = STRING COMMA
    POK COLON LBRACE pok = pok_fields RBRACE COMMA
    PUBLIC_KEY COLON LBRACE key = key_fields RBRACE COMMA
    PUBLIC_KEY_HASH COLON pub_key_hash = STRING COMMA
    UUID COLON uuid = STRING
    { 
      let factors_vec = vector_of_list fl in
      let proofs_vec = vector_of_list pl in
      ((((((factors_vec, proofs_vec), email), pok), key), pub_key_hash), uuid) 
    }
  

factors:
  | f = STRING { big_int_of_string f : Big_int_Z.big_int}

proofs:
  | LBRACE 
    CHALLENGE COLON c = STRING COMMA
    COMMITMENT COLON LBRACE A COLON aone = STRING COMMA B COLON atwo = STRING RBRACE COMMA
    RESPONSE COLON r = STRING 
    RBRACE
     { 
      {
        HeliosTallylib.Sigma.announcement = vector_of_list ([big_int_of_string aone; big_int_of_string atwo]);
        HeliosTallylib.Sigma.challenge = vector_of_list ([big_int_of_string c]);
        HeliosTallylib.Sigma.response = vector_of_list ([big_int_of_string r])
      }
    }
  


pok_fields:
  | CHALLENGE COLON c = STRING COMMA
    COMMITMENT COLON a = STRING COMMA
    RESPONSE COLON r = STRING
    { 
      {
        HeliosTallylib.Sigma.announcement =  vector_of_list ([big_int_of_string a]);
        HeliosTallylib.Sigma.challenge =  vector_of_list ([big_int_of_string c]);  
        HeliosTallylib.Sigma.response =  vector_of_list ([big_int_of_string r])
      }
    }
  

key_fields:
  | G COLON g = STRING COMMA
    P COLON p = STRING COMMA
    Q COLON q = STRING COMMA
    Y COLON y = STRING
    { (((big_int_of_string g, big_int_of_string p), big_int_of_string q), big_int_of_string y) }
  

result :
  | LBRACKET LBRACKET rl = separated_nonempty_list(COMMA, data) RBRACKET RBRACKET { vector_of_list rl : Big_int_Z.big_int HeliosTallylib.VectorDef.t}
  

data:
  | i = BIGINT { big_int_of_string i : Big_int_Z.big_int}