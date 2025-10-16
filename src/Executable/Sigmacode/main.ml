open Sigmalib.SigmaIns 
open Sigmalib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak 

(* Convert vector of Z.t to a list of strings *)
let rec vector_to_list (v : Z.t Sigmalib.VectorDef.t) : string list =
  match v with
  | Coq_nil -> []
  | Coq_cons (h, _, r) -> Big_int_Z.string_of_big_int h :: vector_to_list r

(* Join the elements with ", " without leaving a trailing comma *)
let vector_string (v : Z.t Sigmalib.VectorDef.t) : string =
  String.concat ", " (vector_to_list v)

(* Format the proof without trailing commas *)
let proof_string (proof : (Z.t, Z.t) Sigmalib.Sigma.sigma_proto) : string =
  match proof with
  | { announcement = a; challenge = c; response = r } ->
      "proof = { announcement = " ^ vector_string a ^
      "; challenge = " ^ vector_string c ^
      "; response = " ^ vector_string r ^ " }"

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

(* Ideally, one would like to prove the whole sigma protocol in random-oracle model
to avoid this. *)
let rec random_oracle (acc : string) 
  (n : Z.t) (v : (Z.t, Z.t) Sigmalib.Datatypes.sum Sigmalib.VectorDef.t) : Z.t = 
  match v with
  | Coq_nil -> big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes acc) ~size:4) 
    Sigmalib.SigmaIns.q
  | Coq_cons (hv, _, tv) -> 
      match hv with 
      | Coq_inl hv' 
      | Coq_inr hv' -> random_oracle (acc ^ Big_int_Z.string_of_big_int hv') n tv


   
(* 

let _ = 
  let u = rnd Sigmalib.SigmaIns.q in 
  (* c is computed using fiat-shamir but 
  we have hit bugs in extraction so we moved it 
  to the main (OCaml) function. *) 
  let com = Sigmalib.SigmaIns.schnorr_protocol_commitment_ins u in
  let cha = "p = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int Sigmalib.SigmaIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int Sigmalib.SigmaIns.g ^ ", h = " ^ 
    Big_int_Z.string_of_big_int Sigmalib.SigmaIns.h ^ ", com = " ^ 
    Big_int_Z.string_of_big_int com in
  let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:4) Sigmalib.SigmaIns.q in  
  let proof = schnorr_protocol_construction_ins u c in
  let verify = 
    match schnorr_protocol_verification_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.p ^ ", q = " ^ 
  Big_int_Z.string_of_big_int Sigmalib.SigmaIns.q  ^ ", g = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.g ^ 
  ", h = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.h ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;

*)


let _ = 
  let u = rnd Sigmalib.SigmaIns.q in 
  (* c is computed using strong fiat-shamir *) 
  let proof = nizk_schnorr_protocol_construction_ins (random_oracle "") u in
  let verify = 
    match schnorr_protocol_verification_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.p ^ ", q = " ^ 
  Big_int_Z.string_of_big_int Sigmalib.SigmaIns.q  ^ ", g = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.g ^ 
  ", h = " ^ Big_int_Z.string_of_big_int Sigmalib.SigmaIns.h ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;



