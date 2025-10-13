%{
open Ast
%}


%token <Big_int_Z.big_int> INT
%token CIPHERTEXT PROOF ANNOUNCEMENT CHALLENGE RESPONSE
%token EQ COMMA SEMI LPAR RPAR LBRACE RBRACE NEWLINE EOF


%start<ballot list> prog

%%

prog:
  | vs = ballots; EOF { vs : ballot list}

ballots:
  | bs = separated_nonempty_list(NEWLINE, ballot) {bs : ballot list}
  
ballot:
  | cpf = items { vector_of_list cpf :  ballot}


items:
  | pfs = separated_nonempty_list(SEMI, item) {pfs : ((Big_int_Z.big_int * Big_int_Z.big_int) * (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) Tallylib.Sigma.sigma_proto) list}

item:
  | CIPHERTEXT; EQ; pr = cipherpair; PROOF; EQ; LBRACE; fs = fields; RBRACE { (pr, fs) : ((Big_int_Z.big_int * Big_int_Z.big_int) * (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) Tallylib.Sigma.sigma_proto)}
  
  
cipherpair:
  | LPAR; n1 = INT; COMMA; n2 = INT; RPAR { (n1, n2) : Big_int_Z.big_int * Big_int_Z.big_int }

fields:
  | ANNOUNCEMENT; EQ; a = ann_list; SEMI; CHALLENGE; EQ; c = scalar_list; SEMI; RESPONSE; EQ; r = scalar_list { {announcement = vector_of_list a; challenge = vector_of_list c;  response = vector_of_list r} : (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) Tallylib.Sigma.sigma_proto}

ann_list:
  | vs = separated_nonempty_list(COMMA, cipherpair) {vs : (Big_int_Z.big_int * Big_int_Z.big_int) list} 

scalar_list:
  | vs = separated_nonempty_list(COMMA, INT) {vs : Big_int_Z.big_int list} 
