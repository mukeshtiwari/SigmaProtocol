open DistElgamallib.DistElgamalIns 
open Cryptokit
open Big_int_Z




let rec vector_to_string (printer : 'a -> string) (v : 'a DistElgamallib.VectorDef.t) : string =
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

let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q

let rng = Random.device_rng "/dev/urandom"

let rnd_list (q : Z.t) (n : int) : Z.t DistElgamallib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> DistElgamallib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      DistElgamallib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n


let discrete_log_search (g : Z.t) (c : Z.t) (p : Z.t) : Z.t =
  let rec search x acc =
    if Z.equal acc c then x
    else if Z.equal x p then failwith "No discrete log found"
    else search (Z.succ x) (Big_int_Z.mod_big_int (Z.mul acc g) p)
  in
  search Z.zero Z.one


 
let _ = 
  let ms = rnd_list DistElgamallib.DistElgamalIns.q 10 in 
  let rs = rnd_list DistElgamallib.DistElgamalIns.q 10 in
  let cs = DistElgamallib.DistElgamalIns.encrypt_dist_ballot_ins (Big_int_Z.big_int_of_int 10) ms rs in
  let df1 = DistElgamallib.DistElgamalIns.decrypt_ballot_partial_first_ins (Big_int_Z.big_int_of_int 10) cs in
  let df2 = DistElgamallib.DistElgamalIns.decrypt_ballot_partial_second_ins (Big_int_Z.big_int_of_int 10) cs in
  let df3 = DistElgamallib.DistElgamalIns.decrypt_ballot_partial_third_ins (Big_int_Z.big_int_of_int 10) cs in
  let ds = DistElgamallib.DistElgamalIns.decrypt_ballot_value_ins (Big_int_Z.big_int_of_int 10) cs df1 df2 df3 in
  let fn = fun x -> discrete_log_search DistElgamallib.DistElgamalIns.g x DistElgamallib.DistElgamalIns.p in 
  let ms' =  DistElgamallib.Vector.map fn (Big_int_Z.big_int_of_int 10) ds in 
  Printf.printf "Original messages: [%s]\n" (vector_string ms);
  Printf.printf "Ciphertexts: [%s]\n" (vector_string_pair cs);
  Printf.printf "First decryption factors: [%s]\n" (vector_string df1);
  Printf.printf "Second decryption factors: [%s]\n" (vector_string df2);
  Printf.printf "Third decryption factors: [%s]\n" (vector_string df3);
  Printf.printf "Decrypted messages: [%s]\n" (vector_string ms')
