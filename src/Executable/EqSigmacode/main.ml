open EqSigmalib.EqSigmaIns
open Cryptokit
open Hacl_star.Hacl.Keccak



let rec vector_to_string (printer : 'a -> string) (v : 'a EqSigmalib.VectorDef.t) : string =
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) ->
      (printer h) ^ 
      (if r = Coq_nil then "" else ", " ^ vector_to_string printer r)

(* Specializations *)

let vector_string =
  vector_to_string Big_int_Z.string_of_big_int

let vector_string_pair =
  vector_to_string (fun (h1, h2) ->
    "(" ^ Big_int_Z.string_of_big_int h1 ^ ", " ^ Big_int_Z.string_of_big_int h2 ^ ")")

let proof_string (proof : (Z.t, Z.t) EqSigmalib.Sigma.sigma_proto) : string = 
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


let rnd (q : Z.t) : Z.t = 
  let rng = Random.device_rng "/dev/urandom" in 
  let buf  = Bytes.create 4 in 
  rng#random_bytes buf 0 4; 
  big_int_of_bytes_mod_q buf q 
  


let _ = 
  let u = rnd EqSigmalib.EqSigmaIns.q in 
  let com = vector_string (EqSigmalib.EqSigmaIns.construct_eq_conversations_schnorr_commitment_ins u) in 
  let cha = "p = " ^ Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.q ^ ", g_UU2081_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2081_ ^ ", g_UU2082_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2082_ ^ ", g_UU2083_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2083_ ^ ", h_UU2081_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.h_UU2081_ ^ ", h_UU2082_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.h_UU2082_ ^ ", h_UU2083_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2083_ ^ ", com = " ^ com in 
  let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:4) EqSigmalib.EqSigmaIns.q in 
  let proof = construct_eq_conversations_schnorr_ins u c in  
  let verify = 
    match generalised_eq_accepting_conversations_ins proof with
    | true ->"true"
    | false -> "false"
  in 
  print_string( "p = " ^ Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.q ^ ", g_UU2081_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2081_ ^ ", g_UU2082_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2082_ ^ ", g_UU2083_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2083_ ^ ", h_UU2081_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.h_UU2081_ ^ ", h_UU2082_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.h_UU2082_ ^ ", h_UU2083_ = " ^ 
    Big_int_Z.string_of_big_int EqSigmalib.EqSigmaIns.g_UU2083_ ^ ", com = " ^ com);
  print_endline "";  
  print_string (proof_string proof);
  print_endline "";
  print_string verify;

