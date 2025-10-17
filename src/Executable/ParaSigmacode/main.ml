open ParaSigmalib.ParaSigmaIns
open ParaSigmalib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak

(* Convert vector of Z.t to a list of strings *)
let rec vector_to_list (v : Z.t ParaSigmalib.VectorDef.t) : string list =
  match v with
  | Coq_nil -> []
  | Coq_cons (h, _, r) -> Big_int_Z.string_of_big_int h :: vector_to_list r

(* Join the elements with ", " without leaving a trailing comma *)
let vector_string (v : Z.t ParaSigmalib.VectorDef.t) : string =
  String.concat ", " (vector_to_list v)

(* Format the proof without trailing commas *)
let proof_string (proof : (Z.t, Z.t) ParaSigmalib.Sigma.sigma_proto) : string =
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

let rnd_list (q : Z.t) (n : int) : Z.t ParaSigmalib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> ParaSigmalib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      ParaSigmalib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let split_bytes_to_bigints (b : bytes) (m : int) (q : Z.t) : Z.t ParaSigmalib.VectorDef.t  =
  let n = Bytes.length b in
  if m <= 0 || m > n then invalid_arg "split_bytes_to_bigints: invalid m";
  let rec aux i =
    if i + m > n then ParaSigmalib.VectorDef.Coq_nil
    else
      let chunk = Bytes.sub b i m in
      let bi = big_int_of_bytes_mod_q chunk q in
      ParaSigmalib.VectorDef.Coq_cons (bi, Big_int_Z.big_int_of_int 0, aux (i + m))
  in aux 0

(* Full pipeline: SHAKE256 → split → bigints *)
let shake256_to_bigints ~(msg : string) ~(n : int) ~(m : int) ~(q : Z.t) : Z.t ParaSigmalib.VectorDef.t =
  let b = shake256 ~msg:(String.to_bytes msg) ~size:n in
  split_bytes_to_bigints b m q


let rec random_oracle (acc : string) 
  (n : Z.t) (v : (Z.t, Z.t) ParaSigmalib.Datatypes.sum ParaSigmalib.VectorDef.t) : Z.t ParaSigmalib.VectorDef.t = 
  match v with
  | Coq_nil -> shake256_to_bigints ~msg:acc ~n:8 ~m:4 ~q:ParaSigmalib.ParaSigmaIns.q  
  | Coq_cons (hv, _, tv) -> 
      match hv with 
      | Coq_inl hv' 
      | Coq_inr hv' -> random_oracle (acc ^ Big_int_Z.string_of_big_int hv') n tv

let _  = 
  let us = rnd_list ParaSigmalib.ParaSigmaIns.q 2 in 
  let proof = nizk_construct_parallel_conversations_schnorr_ins (random_oracle "") us in
  let verify = 
    match generalised_parallel_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.g ^ ", h = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.h ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;


(* 
let _  = 
  let u = rnd_list ParaSigmalib.ParaSigmaIns.q 2 in 
  (* c is computed using fiat-shamir but 
  we have hit bugs in extraction. *)
  let com = vector_string (ParaSigmalib.ParaSigmaIns.construct_parallel_conversations_schnorr_commitment_ins u) in
  let cha = "p = " ^ Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.g ^ ", h = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.h ^ ", com = " ^ com in 
  let c = shake256_to_bigints ~msg:cha ~n:8 ~m:4 ~q:ParaSigmalib.ParaSigmaIns.q in
  let proof = construct_parallel_conversations_schnorr_ins u c in
  let verify = 
    match generalised_parallel_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.g ^ ", h = " ^ 
    Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.h ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;
*)


