open ParaSigmalib.ParaSigmaIns
open ParaSigmalib.Sigma
open Cryptokit


let rec vector_string (v : Z.t ParaSigmalib.VectorDef.t) : string = 
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) -> (Big_int_Z.string_of_big_int h) ^ ", " ^ vector_string r 

let proof_string (proof : (Z.t, Z.t) ParaSigmalib.Sigma.sigma_proto) : string = 
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
  
let rnd_list (q : Z.t) (n : int) : Z.t ParaSigmalib.VectorDef.t =
  let rng = Random.device_rng "/dev/urandom" in
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> ParaSigmalib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = Big_int_Z.mod_big_int (big_int_of_bytes buf) q in
      let vs = rnd_list_aux (m - 1) in
      ParaSigmalib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let () = 
  let u = rnd_list ParaSigmalib.ParaSigmaIns.q 2 in 
  (* c is computed using fiat-shamir but 
  we have hit bugs in extraction. Also, this 
  is just for demonstration. *)
  let c = rnd_list ParaSigmalib.ParaSigmaIns.q 2 in
  let proof = construct_parallel_conversations_schnorr_ins u c in
  let verify = 
    match generalised_parallel_accepting_conversations_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string ("g = " ^ Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.g ^ 
  ", h = " ^ Big_int_Z.string_of_big_int ParaSigmalib.ParaSigmaIns.h ^ ", "); 
  print_string (proof_string proof);
  print_endline "";
  print_string verify;



