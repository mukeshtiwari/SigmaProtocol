open OrSigmalib.OrSigmaIns
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

let rng = Random.device_rng "/dev/urandom" 

let rnd_list (q : Z.t) (n : int) : Z.t OrSigmalib.VectorDef.t =
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


let _ = 
    let uscs = rnd_list OrSigmalib.OrSigmaIns.q 5 in (* 3 randomness for commitment and 2 degree of freedom for cheating*)
    let com =  vector_string (OrSigmalib.OrSigmaIns.construct_or_conversations_schnorr_commitment_ins uscs) in 
    let cha = "p = " ^ Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.p ^ ", q = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.q  ^ ", g = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.g ^ ", h_UU2081_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2081_ ^ ", h_UU2082_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2082_ ^ ", h_UU2083_  = " ^ 
      Big_int_Z.string_of_big_int OrSigmalib.OrSigmaIns.h_UU2083_ ^ ", com = " ^ com in 
    let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:4) OrSigmalib.OrSigmaIns.q in
    let proof = generalised_construct_or_conversations_schnorr_ins uscs c in 
    let verify = 
        match generalised_or_accepting_conversations_ins proof with
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


