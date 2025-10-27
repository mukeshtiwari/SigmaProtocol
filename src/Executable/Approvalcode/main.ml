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


let vector_string_pair sep =
  vector_to_string (fun (h1, h2) ->
    "(" ^ Big_int_Z.string_of_big_int h1 ^ ", " ^ Big_int_Z.string_of_big_int h2 ^ ")") sep 


let proof_string (proof : (Z.t, Z.t * Z.t) Approvallib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string_pair "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 

let cipher_string (cp : (Z.t * Z.t)) : string = 
  match cp with 
  |(cpa, cpb) -> "ciphertext = (" ^ Big_int_Z.string_of_big_int cpa ^ ", " ^ Big_int_Z.string_of_big_int cpb ^ ")"

let proof_and_enc_string (cppf : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto)) : string = 
  match cppf with
  | (cp, pf) ->  cipher_string cp ^ " "^  proof_string pf 

let vector_proof_and_enc_string (cppf : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto) Approvallib.VectorDef.t) : string = 
  vector_to_string proof_and_enc_string "; " cppf 


let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q 

let rng = Random.device_rng "/dev/urandom" 
let rnd_list (q : Z.t) (n : int) : Z.t Approvallib.VectorDef.t =
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
let generate_valid_ballot (n : int) : Z.t Approvallib.VectorDef.t = 
    rnd_list (Big_int_Z.big_int_of_int 2) n 

(* generates a ballot of arbitary values of length n *)
let generate_invalid_ballot (n : int) : Z.t Approvallib.VectorDef.t = 
    rnd_list Approvallib.ApprovalIns.q n 

(* I need a function --random-oracle-- that takes m bytes and return n bytes *)
(* Convert Z.t to string *)

(* Flatten vector to bytes *)
let vector_to_bytes (m : Z.t) (v : (Z.t, Z.t) Approvallib.Datatypes.sum Approvallib.VectorDef.t) : 
  bytes =
  Approvallib.Vector.fold_right
    (fun x acc ->
       let s = match x with
         | Approvallib.Datatypes.Coq_inl xa
         | Approvallib.Datatypes.Coq_inr xa -> Big_int_Z.string_of_big_int xa
       in
       Bytes.cat acc (Bytes.of_string s)) m v Bytes.empty

let rec construct_challenge_vector (n : int) (msg : bytes) : Z.t Approvallib.VectorDef.t = 
  match n with 
  | 0 -> Approvallib.VectorDef.Coq_nil
  | _ -> 
    let start = (n - 1) * 4 in
    let chunk = Bytes.sub msg start 4 in
    let z = big_int_of_bytes_mod_q chunk q in
    Approvallib.Vector.Coq_cons (z, Big_int_Z.big_int_of_int (n - 1), 
    (construct_challenge_vector (n - 1) msg))


let random_oracle (n : int) (m : Z.t) 
  (v : (Z.t, Z.t) Approvallib.Datatypes.sum Approvallib.VectorDef.t) :
  Z.t Approvallib.VectorDef.t =
  let inp_msg = vector_to_bytes m v in
  let out_msg = shake256 ~msg:inp_msg ~size:(4 * n) in (* 4 n bytes *) 
  construct_challenge_vector (n : int) out_msg 
  
  
(* 
let generate_valid_ballot_and_proof (n : int) : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto) Approvallib.VectorDef.t = 
  let ms = generate_valid_ballot n in 
  let rs = rnd_list Approvallib.ApprovalIns.q n in 
  let uscs = rnd_list_list Approvallib.ApprovalIns.q 3 n in 
  let cms = generate_ballot_commitment_ins (Big_int_Z.big_int_of_int n) rs ms uscs in
  let com = Approvallib.Vector.map (fun x -> 
      (vector_to_string (fun (u, v) -> "(" ^ Big_int_Z.string_of_big_int u ^ ", " ^ 
      Big_int_Z.string_of_big_int v ^ ")") "," x)) 
      (Big_int_Z.big_int_of_int n) cms in   
  let cha = Approvallib.Vector.map (fun x -> 
    big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes  ("p = " ^ Big_int_Z.string_of_big_int Approvallib.ApprovalIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.g ^ ", h  = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.h ^ ", com = " ^ x)) ~size:4) Approvallib.ApprovalIns.q) 
   (Big_int_Z.big_int_of_int n) com in 
  encrypt_ballot_and_generate_enc_proof_ins (Big_int_Z.big_int_of_int n) rs ms uscs cha
*)


let generate_valid_ballot_and_proof (n : int) : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto) Approvallib.VectorDef.t = 
  let ms = generate_valid_ballot n in 
  let rs = rnd_list Approvallib.ApprovalIns.q n in 
  let uscs = rnd_list_list Approvallib.ApprovalIns.q 3 n in 
  nizk_encrypt_ballot_and_generate_enc_proof_ins (Big_int_Z.big_int_of_int n) 
  (random_oracle n) rs ms uscs 

  
(* This would not pass the check *)
(* 
let generate_invalid_ballot_and_proof (n : int) : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto) Approvallib.VectorDef.t = 
  let ms = generate_invalid_ballot n in 
  let rs = rnd_list Approvallib.ApprovalIns.q n in 
  let uscs = rnd_list_list Approvallib.ApprovalIns.q 3 n in 
  let cms = generate_ballot_commitment_ins (Big_int_Z.big_int_of_int n) rs ms uscs in
  let com = Approvallib.Vector.map (fun x -> 
      (vector_to_string (fun (u, v) -> "(" ^ Big_int_Z.string_of_big_int u ^ ", " ^ 
      Big_int_Z.string_of_big_int v ^ ")") "," x)) 
      (Big_int_Z.big_int_of_int 10) cms in   
   let cha = Approvallib.Vector.map (fun x -> 
    big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes  
    ("p = " ^ Big_int_Z.string_of_big_int Approvallib.ApprovalIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.g ^ ", h  = " ^ 
    Big_int_Z.string_of_big_int Approvallib.ApprovalIns.h ^ ", com = " ^ x)) ~size:4) Approvallib.ApprovalIns.q) 
   (Big_int_Z.big_int_of_int n) com in 
  encrypt_ballot_and_generate_enc_proof_ins (Big_int_Z.big_int_of_int n) rs ms uscs cha
*)

let generate_invalid_ballot_and_proof (n : int) : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto) Approvallib.VectorDef.t = 
  let ms = generate_invalid_ballot n in 
  let rs = rnd_list Approvallib.ApprovalIns.q n in 
  let uscs = rnd_list_list Approvallib.ApprovalIns.q 3 n in 
  nizk_encrypt_ballot_and_generate_enc_proof_ins (Big_int_Z.big_int_of_int n) 
  (random_oracle n) rs ms uscs 

let generate_random_ballots (m : int) (n : int) : unit =
  for i = 1 to m do
    let valid_proof = generate_valid_ballot_and_proof n in
    let invalid_proof = generate_invalid_ballot_and_proof n in
    print_string (vector_proof_and_enc_string valid_proof);
    print_string "\n";
    print_string (vector_proof_and_enc_string invalid_proof);
    (* Only print newline if not the last iteration *)
    if i <> m then print_newline ()
  done


let _ = 
    let m = 100 in 
    let n = 10 in 
    generate_random_ballots m n   
(* 
let _ = 
  let n = 5 in 
  let valid_proof = generate_valid_ballot_and_proof n in 
  let invalid_proof = generate_invalid_ballot_and_proof n in 
  let vf1 = verify_encryption_ballot_proof_ins  (Big_int_Z.big_int_of_int n) valid_proof in 
  let vf2 = verify_encryption_ballot_proof_ins  (Big_int_Z.big_int_of_int n) invalid_proof in 
  print_string ("valid proof: " ^ vector_proof_and_enc_string valid_proof); 
  print_endline "";
  print_string ("invalid proof: " ^ vector_proof_and_enc_string invalid_proof); 
  print_endline "";
  print_string ("valid proof returns: " ^ string_of_bool vf1);
  print_endline "";
  print_string ("invalid proof returns: " ^ string_of_bool vf2)
*)
