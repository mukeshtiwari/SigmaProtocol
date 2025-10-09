open Approvallib.ApprovalIns
open Approvallib.Sigma 
open Cryptokit 
open Hacl_star.Hacl.Keccak


let rec vector_to_string (printer : 'a -> string) (sep : string) (v : 'a Approvallib.VectorDef.t) : string =
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) ->
      (printer h) ^ 
      (if r = Coq_nil then "" else sep ^ " " ^ vector_to_string printer sep r)

(* Specializations *)

let vector_string sep =
  vector_to_string Big_int_Z.string_of_big_int sep

let vector_vector_string sep = 
  vector_to_string (vector_to_string 
    (fun (x, y) -> "(" ^ Big_int_Z.string_of_big_int x ^ ", " ^ Big_int_Z.string_of_big_int y ^ ")") sep) sep


let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q 


let rnd_list (q : Z.t) (n : int) : Z.t Approvallib.VectorDef.t =
  let rng = Random.device_rng "/dev/urandom" in
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> Approvallib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      Approvallib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

let rec rnd_list_list (q : Z.t) (n : int) (m : int) : (Z.t Approvallib.VectorDef.t) Approvallib.VectorDef.t = 
 match m with 
 | 0 -> Coq_nil
 | _ -> Coq_cons (rnd_list q n, Big_int_Z.big_int_of_int 0, rnd_list_list q n (m - 1))  

(* generates a ballot of 0/1 of length n *)
let generate_valid_ballot_of_length_n (n : int) : Z.t Approvallib.VectorDef.t = 
    rnd_list (Big_int_Z.big_int_of_int 2) n 

let generate_invalid_ballot_of_length_n (n : int) : Z.t Approvallib.VectorDef.t = 
    rnd_list Approvallib.ApprovalIns.q n 



let _ = 
  let ms = generate_valid_ballot_of_length_n 10 in 
  let inms = generate_invalid_ballot_of_length_n 10 in 
  let rs = rnd_list Approvallib.ApprovalIns.q 10 in 
  let uscs = rnd_list_list Approvallib.ApprovalIns.q 3 10 in 
  let cms = generate_ballot_commitment (Big_int_Z.big_int_of_int 10) rs ms uscs in
  let com = Approvallib.Vector.map (fun x -> 
      (vector_to_string (fun (u, v) -> "(" ^ Big_int_Z.string_of_big_int u ^ ", " ^ 
      Big_int_Z.string_of_big_int v ^ ")") "," x)) 
      (Big_int_Z.big_int_of_int 10) cms in   
  let cha = Approvallib.Vector.map (fun x -> 
    big_int_of_bytes_mod_q (String.to_bytes  ("p = " ^ Big_int_Z.string_of_big_int Approvallib.ApprovalIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.g ^ ", h  = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.h ^ ", com = " ^ x)) Approvallib.ApprovalIns.q) 
   (Big_int_Z.big_int_of_int 10) com in 
  let proof = encrypt_ballot_and_generate_enc_proof_ins (Big_int_Z.big_int_of_int 10) rs ms uscs cha in 
  let verify = 
        match verify_encryption_ballot_proof_ins  (Big_int_Z.big_int_of_int 10)  proof with
        | true -> "true"
        | _ -> "false"
  in
  print_string verify;
  print_endline "";
  print_string (vector_string "," ms);
  print_endline "";
  print_string (vector_string "," inms); 

