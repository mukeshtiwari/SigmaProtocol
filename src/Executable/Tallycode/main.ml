open Tallylib.TallyIns
open Tallylib.Sigma
open Ballot_parser
open Ast
open Cryptokit 
open Hacl_star.Hacl.Keccak



let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q 

let rng = Random.device_rng "/dev/urandom" 

let rnd_list (q : Z.t) (n : int) : Z.t Tallylib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> Tallylib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      Tallylib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

let rec rnd_list_list (q : Z.t) (n : int) (m : int) : (Z.t Tallylib.VectorDef.t) Tallylib.VectorDef.t = 
 match m with 
 | 0 -> Coq_nil
 | _ -> Coq_cons (rnd_list q n, Big_int_Z.big_int_of_int 10, rnd_list_list q n (m - 1))  



let discrete_log_search (g : Z.t) (c : Z.t) : Z.t =
  let rec search x acc =
    if Z.equal acc c then x
    else if Z.equal x (Tallylib.TallyIns.p) then failwith "No discrete log found"
    else search (Z.succ x) (Big_int_Z.mod_big_int (Z.mul acc g) p)
  in
  search Z.zero Z.one


let rec vector_to_string (printer : 'a -> string) (sep : string) (v : 'a Tallylib.VectorDef.t) : string =
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) ->
      (printer h) ^ 
      (if r = Coq_nil then "" else sep ^ " " ^ vector_to_string printer sep r)

(* Specializations *)

let vector_string sep =
  vector_to_string Big_int_Z.string_of_big_int sep


let vector_string_pair sep =
  vector_to_string (fun (h1, h2) ->
    "(" ^ Big_int_Z.string_of_big_int h1 ^ ", " ^ Big_int_Z.string_of_big_int h2 ^ ")") sep 


let proof_string_pair (proof : (Z.t, Z.t * Z.t) Tallylib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string_pair "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 


let proof_string (proof : (Z.t, Z.t) Tallylib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 


let vector_proof_string sep = 
    vector_to_string proof_string sep 


let cipher_string (cp : (Z.t * Z.t)) : string = 
  match cp with 
  |(cpa, cpb) -> "ciphertext = (" ^ Big_int_Z.string_of_big_int cpa ^ ", " ^ Big_int_Z.string_of_big_int cpb ^ ")"

let proof_and_enc_string (cppf : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto)) : string = 
  match cppf with
  | (cp, pf) ->  cipher_string cp ^ " "^  proof_string_pair pf 


let rec iterate_char (c : string) (n : int) : string =
    if n = 0 then "" else c^iterate_char c (n - 1)

let rec print_count (bs : (Z.t, Z.t) Tallylib.Tally.count) : string = 
    match bs with 
    | Coq_ax (ms, ds, pf) -> "Encrypted zero-tally : " ^ vector_string_pair " " ms ^ "\nDecrypted zero-tally (g^0) : " ^ vector_string " " ds ^ "\nDecryption zero-knowledge proof : "  ^ vector_proof_string " " pf  ^ "\n" ^ iterate_char "-" 150 ^ "\n"
    | Coq_cvalid (u, us, vbs, inbs, ms, nms, p) -> print_count p ^ "Valid ballot : " ^ vector_to_string proof_and_enc_string " " u ^ " \nPrevious tally : " ^ vector_string_pair " " ms ^ "\nCurrent tally : " ^ vector_string_pair " " nms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
    | Coq_cinvalid (u, us, vbs, inbs, ms, p) -> print_count p ^ "Invalid ballot : " ^ vector_to_string proof_and_enc_string " " u ^ " \nPrevious tally : " ^ vector_string_pair " " ms ^ "\nCurrent tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
    | Coq_cfinish (us, vbs, inbs, ms, ds, pf, pt, p) -> print_count p ^ "Final tally : " ^ vector_string_pair " " ms ^ "\nFinal Decrypted Tally : " ^ vector_string " " ds ^ "\nFinal Decrypted Tally (Discrete Logarithm Search) : " ^ vector_string " " pt ^ "\n" ^ iterate_char "-" 150 ^ "\n"


let _ =
  let bs = Parser.prog Lexer.token (Lexing.from_channel stdin) in 
  let rs = rnd_list Tallylib.TallyIns.q 10 in (* goes for encryption zero values *)
  let us = rnd_list Tallylib.TallyIns.q 20 in (* goes for decryption proof construciton *)
  let cs = rnd_list Tallylib.TallyIns.q 20 in (* challenge but it needs to be hashed from all the public values so I need to change API. *)
  let tally = compute_final_count_ins (Big_int_Z.big_int_of_int 10) discrete_log_search rs us cs bs in 
  match tally with 
  | Tallylib.Specif.Coq_existT (vbs, 
    Tallylib.Specif.Coq_existT (inbs, Tallylib.Specif.Coq_existT (pt, count))) -> 
    print_string (print_count count)
  
