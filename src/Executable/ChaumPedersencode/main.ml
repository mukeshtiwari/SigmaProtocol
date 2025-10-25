open ChaumPedersenlib.ChaumPedersenIns
open Cryptokit
open Hacl_star.Hacl.Keccak



let rec vector_to_string (printer : 'a -> string) (v : 'a ChaumPedersenlib.VectorDef.t) : string =
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) ->
      (printer h) ^ 
      (if r = Coq_nil then "" else ", " ^ vector_to_string printer r)

(* Specializations *)

let vector_string =
  vector_to_string Big_int_Z.string_of_big_int

let proof_string (proof : (Z.t, Z.t) ChaumPedersenlib.Sigma.sigma_proto) : string = 
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

let rng = Random.device_rng "/dev/urandom"

let rnd (q : Z.t) : Z.t =
  let buf  = Bytes.create 4 in 
  rng#random_bytes buf 0 4; 
  big_int_of_bytes_mod_q buf q 
  



let _ = 
  let u = rnd ChaumPedersenlib.ChaumPedersenIns.q in 
  let c =  rnd ChaumPedersenlib.ChaumPedersenIns.q in 
  let proof = construct_cp_conversations_schnorr_ins u c in  
  let verify = 
    match generalised_cp_accepting_conversations_ins proof with
    | true ->"true"
    | false -> "false"
  in 
  print_string( "p = " ^ Big_int_Z.string_of_big_int ChaumPedersenlib.ChaumPedersenIns.p ^ 
    ", q = " ^ Big_int_Z.string_of_big_int ChaumPedersenlib.ChaumPedersenIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int ChaumPedersenlib.ChaumPedersenIns.g ^  ", h = " ^ 
    Big_int_Z.string_of_big_int ChaumPedersenlib.ChaumPedersenIns.h);
  print_endline "";  
  print_string (proof_string proof);
  print_endline "";
  print_string verify;

