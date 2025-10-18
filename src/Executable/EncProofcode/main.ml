open EncProoflib.EncProofIns
open Cryptokit
open Hacl_star.Hacl.Keccak


let rec vector_to_string (printer : 'a -> string) (v : 'a EncProoflib.VectorDef.t) : string =
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

let proof_string (proof : (Z.t, Z.t * Z.t) EncProoflib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {annoucement = "^ vector_string_pair a ^ " challenge = " ^ vector_string c ^ 
      " response = " ^ vector_string r ^ "}" 


let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q 

let rng = Random.device_rng "/dev/urandom"

let rnd_list (q : Z.t) (n : int) : Z.t EncProoflib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> EncProoflib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      EncProoflib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

  (* Z.t -> (Z.t, (Z.t, Z.t * Z.t) sum) sum VectorDef.t -> Z.t *)
 let rec random_oracle (acc : string) 
  (n : Z.t) (v : (Z.t, (Z.t, Z.t * Z.t) EncProoflib.Datatypes.sum) EncProoflib.Datatypes.sum EncProoflib.VectorDef.t) : Z.t = 
  match v with
  | Coq_nil -> big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes acc) ~size:4) 
    EncProoflib.EncProofIns.q
  | Coq_cons (hv, _, tv) -> 
      match hv with 
      | Coq_inl hv' -> random_oracle (acc ^ Big_int_Z.string_of_big_int hv') n tv 
      | Coq_inr hv' -> 
          match hv' with 
          | Coq_inl hva ->  random_oracle (acc ^ Big_int_Z.string_of_big_int hva) n tv 
          | Coq_inr (hva, hvb) -> random_oracle (acc ^ Big_int_Z.string_of_big_int hva ^ Big_int_Z.string_of_big_int hvb) n tv 
     

let _ = 
    let uscs = rnd_list EncProoflib.EncProofIns.q 5 in (* 3 randomness for commitment and 2 degree of freedom for cheating*)
    let proof = nizk_generalised_construct_encryption_proof_elgamal_real_ins (random_oracle "") uscs in
    let verify = 
          match generalised_accepting_encryption_proof_elgamal_ins  proof with
          | true -> "true"
          | _ -> "false"
    in
    print_string ("p = " ^ Big_int_Z.string_of_big_int EncProoflib.EncProofIns.p ^ ", q = " ^ 
      Big_int_Z.string_of_big_int EncProoflib.EncProofIns.q  ^ ", g = " ^ 
      Big_int_Z.string_of_big_int EncProoflib.EncProofIns.g ^ ", h  = " ^ 
      Big_int_Z.string_of_big_int EncProoflib.EncProofIns.h ^ ", m_UU2080_  = " ^ 
      Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2080_ ^ ", m_UU2081_  = " ^ 
      Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2081_ ^ ", m_UU2082_ = " ^ 
      Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2082_ ^ ", cp = (" ^ 
      Big_int_Z.string_of_big_int (fst EncProoflib.EncProofIns.cp) ^ ", " ^ 
      Big_int_Z.string_of_big_int (snd EncProoflib.EncProofIns.cp) ^ ")");
    print_endline "";
    print_string (proof_string proof);
    print_endline "";
    print_string verify;

(* 
let _ = 
  let uscs = rnd_list EncProoflib.EncProofIns.q 5 in (* 3 randomness for commitment and 2 degree of freedom for cheating*)
  let com =  vector_string_pair (EncProoflib.EncProofIns.construct_encryption_proof_elgamal_commitment_ins uscs) in 
  let cha = "p = " ^ Big_int_Z.string_of_big_int EncProoflib.EncProofIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.g ^ ", h  = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.h ^ ", m_UU2080_  = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2080_ ^ ", m_UU2081_  = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2081_ ^ ", m_UU2082_ = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2082_ ^ ", fst cp = " ^ 
    Big_int_Z.string_of_big_int (fst EncProoflib.EncProofIns.cp) ^ ", snd cp = " ^ 
    Big_int_Z.string_of_big_int (snd EncProoflib.EncProofIns.cp) ^ ", com = " ^ com in 
  let c = big_int_of_bytes_mod_q (shake256 ~msg:(String.to_bytes cha) ~size:4) EncProoflib.EncProofIns.q in
  let proof = generalised_construct_encryption_proof_elgamal_real_ins uscs c in
  let verify = 
        match generalised_accepting_encryption_proof_elgamal_ins  proof with
        | true -> "true"
        | _ -> "false"
  in
  print_string ("p = " ^ Big_int_Z.string_of_big_int EncProoflib.EncProofIns.p ^ ", q = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.q  ^ ", g = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.g ^ ", h  = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.h ^ ", m_UU2080_  = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2080_ ^ ", m_UU2081_  = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2081_ ^ ", m_UU2082_ = " ^ 
    Big_int_Z.string_of_big_int EncProoflib.EncProofIns.m_UU2082_ ^ ", cp = (" ^ 
    Big_int_Z.string_of_big_int (fst EncProoflib.EncProofIns.cp) ^ ", " ^ 
    Big_int_Z.string_of_big_int (snd EncProoflib.EncProofIns.cp) ^ "), com = " ^ com);
  print_endline "";
  print_string (proof_string proof);
  print_endline "";
  print_string verify;
*)
