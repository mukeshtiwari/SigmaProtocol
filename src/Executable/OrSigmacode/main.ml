open OrSigmalib.OrSigmaIns
open OrSigmalib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak



let rec vector_string (v : Z.t OrSigmalib.VectorDef.t) : string = 
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) -> (Big_int_Z.string_of_big_int h) ^ ", " ^ vector_string r 

let proof_string (proof : (Z.t, Z.t) OrSigmalib.Sigma.sigma_proto) : string = 
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


let rnd_list (q : Z.t) (n : int) : Z.t OrSigmalib.VectorDef.t =
  let rng = Random.device_rng "/dev/urandom" in
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> OrSigmalib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      OrSigmalib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let split_bytes_to_bigints (b : bytes) (m : int) (q : Z.t) : Z.t OrSigmalib.VectorDef.t  =
  let n = Bytes.length b in
  if m <= 0 || m > n then invalid_arg "split_bytes_to_bigints: invalid m";
  let rec aux i =
    if i + m > n then OrSigmalib.VectorDef.Coq_nil
    else
      let chunk = Bytes.sub b i m in
      let bi = big_int_of_bytes_mod_q chunk q in
      OrSigmalib.VectorDef.Coq_cons (bi, Big_int_Z.big_int_of_int 0, aux (i + m))
  in
  aux 0

(* Full pipeline: SHAKE256 → split → bigints *)
let shake256_to_bigints ~(msg : string) ~(n : int) ~(m : int) ~(q : Z.t) : Z.t OrSigmalib.VectorDef.t =
  let b = shake256 ~msg:(String.to_bytes msg) ~size:n in
  split_bytes_to_bigints b m q


let _ = 
    let us = rnd_list OrSigmalib.OrSigmaIns.q 3 in (* randomness for commitment *)
    let cs = rnd_list OrSigmalib.OrSigmaIns.q 2 in (* degree of freedom for cheating *)
    let com =  vector_string (OrSigmalib.OrSigmaIns.construct_or_conversations_schnorr_commitment_ins us cs) in 
    let cha = "p = " ^ Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.p ^ ", q = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.q  ^ ", g = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.g ^ ", h_UU2081_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2081_ ^ ", h_UU2082_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2082_ ^ ", h_UU2083_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2083_ ^ ", com = " ^ com in 
    let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:4) OrSigmalib.OrSigmaIns.q in
    let proof = OrSigmalib.OrSigmaIns.generalised_construct_or_conversations_schnorr_ins us cs c in 
    let verify = 
        match OrSigmalib.OrSigmaIns.generalised_or_accepting_conversations_ins proof with
        | true -> "true"
        | _ -> "false"
    in
    print_string ("p = " ^ Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.p ^ ", q = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.q  ^ ", g = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.g ^ ", h_UU2081_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2081_ ^ ", h_UU2082_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2082_ ^ ", h_UU2083_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2083_ ^ ", com = " ^ com);
    print_endline "";
    print_string (proof_string proof);
    print_endline "";
    print_string verify;


    



(*   
let () = 
  let u = rnd_list ParaSigmalib.ParaSigmaIns.q 2 in 
  (* c is computed using fiat-shamir but 
  we have hit bugs in extraction. *)
  let com = vector_string (ParaSigmalib.ParaSigmaIns.construct_parallel_conversations_schnorr_commitment_ins g u) in
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