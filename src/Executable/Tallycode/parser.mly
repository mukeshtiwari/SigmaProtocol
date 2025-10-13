%{
open Ast
open Tallylib.BinInt
open Tallylib.VectorDef
%}


%token <string> INT
%token CIPHERTEXT PROOF ANNOUNCEMENT CHALLENGE RESPONSE
%token EQ COMMA SEMI LPAR RPAR LBRACE RBRACE NEWLINE EOF

%start ballot_file
%type <Ast.ballot_file> ballot_file



ballot_file:
  ballots EOF { $1 }

ballots:
    ballot { [$1] }
  | ballot NEWLINE ballots { $1 :: $3 }

ballot:
  items { vector_of_list $1 }


items:
    item { [$1] }
  | item SEMI items { $1 :: $3 }
  | item SEMI { [$1] } 


item:
  CIPHERTEXT EQ pair PROOF EQ LBRACE fields RBRACE
  {
    let (c1,c2) = $3 in
    let (anns, chs, rs) = $7 in
    {
      ciphertext = (c1,c2);
      proof = {
        announcement = vector_of_list anns;
        challenge = vector_of_list chs;
        response = vector_of_list rs;
      }
    }
  }


pair:
  LPAR INT COMMA INT RPAR { (Big_int_Z.big_int_of_string $2, Big_int_Z.big_int_of_string $4) }

fields:
    ANNOUNCEMENT EQ ann_list SEMI CHALLENGE EQ scalar_list SEMI RESPONSE EQ scalar_list
    { ($3, $7, $11) }

ann_list:
    pair { [$1] }
  | ann_list COMMA pair { $1 @ [$3] }

scalar_list:
    INT { [Big_int_Z.big_int_of_string $1] }
  | scalar_list COMMA INT { $1 @ [Big_int_Z.big_int_of_string $3] }
