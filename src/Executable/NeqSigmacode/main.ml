open NeqSigmalib.NeqSigmaIns
open NeqSigmalib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak



let rec vector_to_list (v : Z.t NeqSigmalib.VectorDef.t) : string list =
  match v with
  | Coq_nil -> []
  | Coq_cons (h, _, r) -> Big_int_Z.string_of_big_int h :: vector_to_list r

(* Join the elements with ", " without leaving a trailing comma *)
let vector_string (v : Z.t NeqSigmalib.VectorDef.t) : string =
  String.concat ", " (vector_to_list v)

(* Format the proof without trailing commas *)
let proof_string (proof : (Z.t, Z.t) NeqSigmalib.Sigma.sigma_proto) : string =
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
let rnd_list (q : Z.t) (n : int) : Z.t NeqSigmalib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> NeqSigmalib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      NeqSigmalib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let rec random_oracle (acc : string) 
  (n : Z.t) (v : (Z.t, Z.t) NeqSigmalib.Datatypes.sum NeqSigmalib.VectorDef.t) : Z.t =
  match v with
  | Coq_nil -> big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes acc) ~size:4) 
    NeqSigmalib.NeqSigmaIns.q
  | Coq_cons (hv, _, tv) -> 
      match hv with 
      | Coq_inl hv' 
      | Coq_inr hv' -> random_oracle (acc ^ Big_int_Z.string_of_big_int hv') n tv


let _ =
  let us = rnd_list NeqSigmalib.NeqSigmaIns.q 9 in
  let proof = nizk_generalised_construct_neq_conversations_real_transcript_ins 
    (random_oracle "") us in
  let verify = 
    match generalised_neq_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.q  ^ ", g1 = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.g_UU2081_ ^ ", g2 = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.g_UU2082_ ^ ", g3 = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.g_UU2083_ ^ ", h1 = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.h_UU2081_ ^ ", h2 = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.h_UU2082_ ^ ", h3 = " ^ 
    Big_int_Z.string_of_big_int NeqSigmalib.NeqSigmaIns.h_UU2083_ ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;