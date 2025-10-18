open AndSigmalib.AndSigmaIns
open AndSigmalib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak

let rec vector_to_list (v : Z.t AndSigmalib.VectorDef.t) : string list =
  match v with
  | Coq_nil -> []
  | Coq_cons (h, _, r) -> Big_int_Z.string_of_big_int h :: vector_to_list r

(* Join the elements with ", " without leaving a trailing comma *)
let vector_string (v : Z.t AndSigmalib.VectorDef.t) : string =
  String.concat ", " (vector_to_list v)

(* Format the proof without trailing commas *)
let proof_string (proof : (Z.t, Z.t) AndSigmalib.Sigma.sigma_proto) : string =
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
let rnd_list (q : Z.t) (n : int) : Z.t AndSigmalib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> AndSigmalib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      AndSigmalib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let rec random_oracle (acc : string) 
  (n : Z.t) (v : (Z.t, Z.t) AndSigmalib.Datatypes.sum AndSigmalib.VectorDef.t) : Z.t = 
  match v with
  | Coq_nil -> big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes acc) ~size:4) 
    AndSigmalib.AndSigmaIns.q
  | Coq_cons (hv, _, tv) -> 
      match hv with 
      | Coq_inl hv' 
      | Coq_inr hv' -> random_oracle (acc ^ Big_int_Z.string_of_big_int hv') n tv


let _ = 
  let u = rnd_list AndSigmalib.AndSigmaIns.q 3 in 
  let proof = nizk_construct_and_conversations_schnorr_ins (random_oracle "") u in
  let verify = 
    match generalised_and_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.g ^ ", h1 = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2081_ ^ ", h2 = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2082_ ^ ", h3 = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2083_ ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;

(* 
let _ = 
  let u = rnd_list AndSigmalib.AndSigmaIns.q 3 in 
  (* c is computed using fiat-shamir but 
  we have hit bugs in extraction. *)
  let com = vector_string (AndSigmalib.AndSigmaIns.construct_and_conversations_schnorr_commitment_ins u) in 
  let cha = "p = " ^ Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.q  ^ 
    ", g = " ^ Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.g ^ ", h_UU2081_ = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2081_ ^ ", h_UU2082_ = " ^
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2082_ ^ ", h_UU2083_ = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2083_ ^ ", com = " ^ com in
  let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:4) 
    AndSigmalib.AndSigmaIns.q in 
  let proof = construct_and_conversations_schnorr_ins u c in
  let verify = 
    match generalised_and_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.g ^ ", h1 = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2081_ ^ ", h2 = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2082_ ^ ", h3 = " ^ 
    Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2083_ ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;

*)