open SigmaHelioslib.SigmaInsHelios
open SigmaHelioslib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak 


let rec vector_string (v : Z.t SigmaHelioslib.VectorDef.t) : string = 
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) -> (Big_int_Z.string_of_big_int h) ^ ", " ^ vector_string r 

let proof_string (proof : (Z.t, Z.t) SigmaHelioslib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {annoucement = "^ vector_string a ^ " challenge = " ^ vector_string c ^ 
      " response = " ^ vector_string r ^ "}" 


let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q 

(* 32 bytes of randomness because q is 256 bit prime *)
let rnd (q : Z.t) : Z.t = 
  let rng = Random.device_rng "/dev/urandom" in 
  let buf  = Bytes.create 32 in 
  rng#random_bytes buf 0 32; 
  big_int_of_bytes_mod_q buf q 

  
let _ = 
  let u = rnd SigmaHelioslib.SigmaInsHelios.q in
  let com = SigmaHelioslib.SigmaInsHelios.schnorr_protocol_commitment_ins u in
  let cha = "p = " ^ Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.g ^ ", h = " ^ 
    Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.h ^ ", com = " ^ 
    Big_int_Z.string_of_big_int com in
  let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:32) 
    SigmaHelioslib.SigmaInsHelios.q in
  let proof = schnorr_protocol_construction_ins u c in
  let verify = 
    match schnorr_protocol_verification_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.p ^ ", q = " ^ 
  Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.q  ^ ", g = " ^ 
  Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.g ^ 
  ", h = " ^ Big_int_Z.string_of_big_int SigmaHelioslib.SigmaInsHelios.h ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;


