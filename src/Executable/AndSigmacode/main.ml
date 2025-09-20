open AndSigmalib.AndSigmaIns
open AndSigmalib.Sigma
open Cryptokit


let rec vector_string (v : Z.t AndSigmalib.VectorDef.t) : string = 
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) -> (Big_int_Z.string_of_big_int h) ^ ", " ^ vector_string r 

let proof_string (proof : (Z.t, Z.t) AndSigmalib.Sigma.sigma_proto) : string = 
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

let rnd_list (q : Z.t) (n : int) : Z.t AndSigmalib.VectorDef.t =
  let rng = Random.device_rng "/dev/urandom" in
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> AndSigmalib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = Big_int_Z.mod_big_int (big_int_of_bytes buf) q in
      let vs = rnd_list_aux (m - 1) in
      AndSigmalib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

let rnd (q : Z.t)= 
  let rng = Random.device_rng "/dev/urandom" in 
  let buf  = Bytes.create 4 in 
  rng#random_bytes buf 0 4; 
  Big_int_Z.mod_big_int (big_int_of_bytes buf) q 
  
let () = 
  let u = rnd_list AndSigmalib.AndSigmaIns.q 3 in 
  (* c is computed using fiat-shamir but 
  we have hit bugs in extraction. Also, this 
  is just for demonstration. *)
  let c = rnd  AndSigmalib.AndSigmaIns.q in 
  let proof = construct_and_conversations_schnorr_ins u c in
  let verify = 
    match generalised_and_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("g = " ^ Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.g ^ ", h1 = " ^ 
  Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2081_ ^ ", h2 = " ^ 
  Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2082_ ^ ", h3 = " ^ 
  Big_int_Z.string_of_big_int AndSigmalib.AndSigmaIns.h_UU2083_ ^ "\n"); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;

