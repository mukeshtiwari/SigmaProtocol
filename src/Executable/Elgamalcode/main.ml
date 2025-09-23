open Elgamallib.ElgamalIns
open Cryptokit
open Big_int_Z


let rec vector_to_string (printer : 'a -> string) (v : 'a Elgamallib.VectorDef.t) : string =
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


let rnd_list (q : Z.t) (n : int) : Z.t Elgamallib.VectorDef.t =
  let rng = Random.device_rng "/dev/urandom" in
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> Elgamallib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      Elgamallib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

let discrete_log_bsgs (g : Z.t) (c : Z.t) (p : Z.t) (n : int) : Z.t =
  let m = n + 1 in
  let table = Hashtbl.create m in
  (* build baby-step table: g^j mod p for j = 0..m-1 *)
  let rec build_table j acc =
    if j < m then (
      Hashtbl.replace table acc j;
      build_table (j + 1) (Z.(mod_big_int (acc * g) p)))
  in
  build_table 0 Z.one;
  (* compute g^(-m) mod p *)
  let g_inv = Z.invert g p in
  let g_m_inv = Z.powm g_inv (Z.of_int m) p in
  (* giant steps: c * (g^(-m))^i for i = 0..m *)
  let rec search i acc =
    if i > m then failwith "No discrete log found"
    else
      match Hashtbl.find_opt table acc with
      | Some j ->
          let x = Z.(add (mul (of_int i) (of_int m)) (of_int j)) in
          if Z.equal (Z.powm g x p) c then x else search (i + 1) (Z.(mod_big_int (acc * g_m_inv) p))
      | None ->
          search (i + 1) (Z.(mod_big_int (acc * g_m_inv) p))
  in
  search 0 c


let discrete_log_search (g : Z.t) (c : Z.t) (p : Z.t) : Z.t =
  let rec search x acc =
    if Z.equal acc c then x
    else if Z.equal x p then failwith "No discrete log found"
    else search (Z.succ x) (Big_int_Z.mod_big_int (Z.mul acc g) p)
  in
  search Z.zero Z.one


let _ = 
  let ms1 = rnd_list Elgamallib.ElgamalIns.q 10 in
  let cs1 = Elgamallib.ElgamalIns.encrypt_ballot (Big_int_Z.big_int_of_int 10) ms1 (rnd_list Elgamallib.ElgamalIns.q 10) in
  let fn = fun x -> 
    discrete_log_bsgs Elgamallib.ElgamalIns.g x Elgamallib.ElgamalIns.p 1000000 in 
  let ds1 = Elgamallib.Vector.map fn 
    (Big_int_Z.big_int_of_int 10) 
    (Elgamallib.ElgamalIns.decrypt_ballot (Big_int_Z.big_int_of_int 10) cs1) in
  let cs2 = Elgamallib.ElgamalIns.reencrypt_ballots (Big_int_Z.big_int_of_int 10) cs1 (rnd_list Elgamallib.ElgamalIns.q 10) in
  let ds2 = Elgamallib.Vector.map fn 
    (Big_int_Z.big_int_of_int 10) 
    (Elgamallib.ElgamalIns.decrypt_ballot (Big_int_Z.big_int_of_int 10) cs2) in 
  let cs3 = Elgamallib.ElgamalIns.multiply_encrypted_ballots (Big_int_Z.big_int_of_int 10) cs1 cs2 in 
  let ds3 = Elgamallib.Vector.map fn 
    (Big_int_Z.big_int_of_int 10) 
    (Elgamallib.ElgamalIns.decrypt_ballot (Big_int_Z.big_int_of_int 10) cs3) in 
  print_string ("message ms1 = " ^ vector_string ms1); 
  print_endline "";
  print_string ("encryption cs1 = " ^vector_string_pair cs1);
  print_endline "";
  print_string ("decryption ds1 = " ^ vector_string ds1);
  print_endline "";
  print_string ("rencryption cs2 = " ^ vector_string_pair cs2);
  print_endline "";
  print_string ("decryption ds2 = " ^ vector_string ds2);
  print_endline "";
  print_string ("multiplication enc ballot cs3 = " ^ vector_string_pair cs3);
  print_endline "";
  print_string ("decryption ds3 = " ^ vector_string ds3);
  
  
