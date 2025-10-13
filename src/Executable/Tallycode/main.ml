open Tallylib.TallyIns
open Tallylib.Sigma
open Ballot_parser
open Ast

module Z = Big_int_Z
module V = Tallylib.VectorDef 

let rec print_ann_vec v =
  match v with
  | V.Coq_nil -> ()
  | V.Coq_cons ((a,b), tail_len, tl) ->
    Printf.printf "(%s, %s) [tail=%s]\n" (Z.string_of_big_int a) (Z.string_of_big_int b) (Z.string_of_big_int tail_len);
    print_ann_vec tl

let rec print_scalar_vec v =
  match v with
  | V.Coq_nil -> ()
  | V.Coq_cons (x, tail_len, tl) ->
    Printf.printf "%s [tail=%s]\n" (Z.string_of_big_int x) (Z.string_of_big_int tail_len);
    print_scalar_vec tl

let rec print_ballot b =
  match b with 
  | V.Coq_nil -> ()
  | V.Coq_cons (((c1, c2), b), _, tl) ->
  Printf.printf "ciphertext = (%s, %s)\n" (Z.string_of_big_int c1) (Z.string_of_big_int c2);
  Printf.printf "announcement:\n"; print_ann_vec b.announcement;
  Printf.printf "challenge:\n"; print_scalar_vec b.challenge;
  Printf.printf "response:\n"; print_scalar_vec b.response;
  Printf.printf "----\n";
  print_ballot tl


let _ =
  let ballots = Parser.prog Lexer.token (Lexing.from_channel stdin) in 
  Printf.printf "Parsed vector of ballots (as Vectordef):\n";
  List.iter print_ballot ballots

