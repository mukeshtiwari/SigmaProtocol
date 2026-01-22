open PedLinearRellib.PedLinearRelIns
open PedLinearRellib.Sigma
open Cryptokit
open Hacl_star.Hacl.Keccak

(* Convert vector of Z.t to a list of strings *)
let rec vector_to_list (v : Z.t PedLinearRellib.VectorDef.t) : string list =
  match v with
  | Coq_nil -> []
  | Coq_cons (h, _, r) -> Big_int_Z.string_of_big_int h :: vector_to_list r  

(* Join the elements with ", " without leaving a trailing comma *)
let vector_string (v : Z.t PedLinearRellib.VectorDef.t) : string =
  String.concat ", " (vector_to_list v) 

(* Format the proof without trailing commas *)
let proof_string (proof : (Z.t, Z.t) PedLinearRellib.Sigma.sigma_proto) : string =
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
let rnd_list (q : Z.t) (n : int) : Z.t PedLinearRellib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> PedLinearRellib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      PedLinearRellib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let rec random_oracle (acc : string) 
  (n : Z.t) (v : (Z.t, Z.t) PedLinearRellib.Datatypes.sum PedLinearRellib.VectorDef.t) : Z.t = 
  match v with
  | Coq_nil -> big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes acc) ~size:4) 
    PedLinearRellib.PedLinearRelIns.q
  | Coq_cons (hv, _, tv) -> 
      match hv with 
      | Coq_inl hv' 
      | Coq_inr hv' -> random_oracle (acc ^ Big_int_Z.string_of_big_int hv') n tv


let vector_of_list (xs : 'a list) : 'a PedLinearRellib.VectorDef.t  =
  let rec aux l =
    match l with
    | [] -> PedLinearRellib.VectorDef.Coq_nil
    | lh :: lt ->
      let tail_len = Big_int_Z.big_int_of_int (List.length lt) in
      Coq_cons (lh, tail_len, aux lt)
    in aux xs


let _ = 
  (* 1 * 5 + (-1) * 2 + (-1) * 2 = 0 *)
  let vs = vector_of_list [Big_int_Z.big_int_of_int 5; Big_int_Z.big_int_of_int 2; Big_int_Z.big_int_of_int 3] in
  let rs = rnd_list PedLinearRellib.PedLinearRelIns.q 3 in
  let cs = PedLinearRellib.PedLinearRelIns.pedersen_commitment_vector_ins vs rs in
  let usws = rnd_list PedLinearRellib.PedLinearRelIns.q 6 in
  let proof = PedLinearRellib.PedLinearRelIns.nizk_construct_pedersen_linear_relation_generalised_real_proof_ins 
    (random_oracle "") vs rs usws in 
  let verify = PedLinearRellib.PedLinearRelIns.verify_pedersen_linear_relation_generalised_proof_ins cs proof in
  print_endline ("commitment = " ^ vector_string cs);
  print_endline (proof_string proof);
  if verify then
    print_endline "Proof verified successfully."
  else
    print_endline "Proof verification failed."