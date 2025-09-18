open Sigmalib.SigmaIns 
open Sigmalib.Sigma

(* 
type vec = Z.t Sigmalib.VectorDef.t [@@deriving sexp]
*)

let rec vector_string (v : Z.t Sigmalib.VectorDef.t) : string = 
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) -> (Big_int_Z.string_of_big_int h) ^ ", " ^ vector_string r 

let proof_string (proof : (Z.t, Z.t) Sigmalib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {annoucement = "^ vector_string a ^ " challenge = " ^ vector_string c ^ 
      " response = " ^ vector_string r ^ "}" 

let () = 
  Random.self_init ();
  let cha = Big_int_Z.big_int_of_int (Random.int 593) in 
  let res = Big_int_Z.big_int_of_int (Random.int 593) in 
  let proof = schnorr_protocol_construction_ins cha res in
  let verify = 
    match schnorr_protocol_verification_ins proof with  
    | true -> "true"
    | _ -> "false"
  in
  print_string (proof_string proof);
  print_endline "";
  print_string verify;




