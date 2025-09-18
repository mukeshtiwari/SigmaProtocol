open Sigmalib.SigmaIns 
open Sigmalib.Sigma
open Cryptokit


let rec vector_string (v : Z.t Sigmalib.VectorDef.t) : string = 
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) -> (Big_int_Z.string_of_big_int h) ^ ", " ^ vector_string r 

let proof_string (proof : (Z.t, Z.t) Sigmalib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {annoucement = "^ vector_string a ^ " challenge = " ^ vector_string c ^ 
      " response = " ^ vector_string r ^ "}" 


let big_int_of_bytes (s : bytes) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  !n

let rnd (q : Z.t)= 
  let rng = Random.device_rng "/dev/urandom" in 
  let buf  = Bytes.create 4 in 
  rng#random_bytes buf 0 4; 
  Big_int_Z.mod_big_int (big_int_of_bytes buf) q 
  
let () = 
  let cha = rnd Sigmalib.SigmaIns.q in 
  let res = rnd Sigmalib.SigmaIns.q in 
  let proof = schnorr_protocol_construction_ins cha res in
  let verify = 
    match schnorr_protocol_verification_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string (proof_string proof);
  print_endline "";
  print_string verify;




