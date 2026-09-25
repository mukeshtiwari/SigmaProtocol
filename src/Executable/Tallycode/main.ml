open Tallylib.TallyIns
open Tallylib.Sigma
open Ballot_parser
open Ast
open Cryptokit 
open Hacl_star.Hacl.Keccak



let big_int_of_bytes_mod_q (s : bytes) (q : Z.t) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q 

let rng = Random.device_rng "/dev/urandom" 

let rnd_list (q : Z.t) (n : int) : Z.t Tallylib.VectorDef.t =
  let buf = Bytes.create 4 in
  let rec rnd_list_aux m =
    match m with
    | 0 -> Tallylib.VectorDef.Coq_nil
    | _ ->
      let _ = rng#random_bytes buf 0 4 in
      let v = big_int_of_bytes_mod_q buf q in
      let vs = rnd_list_aux (m - 1) in
      Tallylib.VectorDef.Coq_cons (v, Big_int_Z.big_int_of_int 0, vs)
  in
  rnd_list_aux n

let rec rnd_list_list (q : Z.t) (n : int) (m : int) : (Z.t Tallylib.VectorDef.t) Tallylib.VectorDef.t = 
 match m with 
 | 0 -> Coq_nil
 | _ -> Coq_cons (rnd_list q n, Big_int_Z.big_int_of_int 10, rnd_list_list q n (m - 1))  



let discrete_log_search (g : Z.t) (c : Z.t) : Z.t =
  let rec search x acc =
    if Z.equal acc c then x
    else if Z.equal x (Tallylib.TallyIns.p) then failwith "No discrete log found"
    else search (Z.succ x) (Big_int_Z.mod_big_int (Z.mul acc g) p)
  in
  search Z.zero Z.one


let rec vector_to_string (printer : 'a -> string) (sep : string) (v : 'a Tallylib.VectorDef.t) : string =
  match v with
  | Coq_nil -> ""
  | Coq_cons (h, _, r) ->
      (printer h) ^ 
      (if r = Coq_nil then "" else sep ^ " " ^ vector_to_string printer sep r)

(* Specializations *)

let vector_string sep =
  vector_to_string Big_int_Z.string_of_big_int sep


let vector_string_pair sep =
  vector_to_string (fun (h1, h2) ->
    "(" ^ Big_int_Z.string_of_big_int h1 ^ ", " ^ Big_int_Z.string_of_big_int h2 ^ ")") sep 


let proof_string_pair (proof : (Z.t, Z.t * Z.t) Tallylib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string_pair "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 


let proof_string (proof : (Z.t, Z.t) Tallylib.Sigma.sigma_proto) : string = 
    match  proof with
    | {announcement = a; challenge = c; 
      response = r} -> "proof = {announcement = "^ vector_string "," a  ^ "; challenge = " ^ vector_string  "," c ^ 
      "; response = " ^ vector_string  "," r ^ "}" 


let vector_proof_string sep = 
    vector_to_string proof_string sep 


let cipher_string (cp : (Z.t * Z.t)) : string = 
  match cp with 
  |(cpa, cpb) -> "ciphertext = (" ^ Big_int_Z.string_of_big_int cpa ^ ", " ^ Big_int_Z.string_of_big_int cpb ^ ")"

let proof_and_enc_string (cppf : ((Z.t * Z.t) * (Z.t, Z.t * Z.t) sigma_proto)) : string = 
  match cppf with
  | (cp, pf) ->  cipher_string cp ^ " "^  proof_string_pair pf 


let rec iterate_char (c : string) (n : int) : string =
    if n = 0 then "" else c^iterate_char c (n - 1)

let rec print_count (bs : (Z.t, Z.t) Tallylib.Tally.count) : string = 
    match bs with 
    | Coq_ax ms -> "Identity-tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
    | Coq_cvalid (u, us, vbs, inbs, ms, nms, p) -> print_count p ^ "Valid ballot : " ^ vector_to_string proof_and_enc_string " " (fst u) ^ " \nPrevious tally : " ^ vector_string_pair " " ms ^ "\nCurrent tally : " ^ vector_string_pair " " nms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
    | Coq_cinvalid (u, us, vbs, inbs, ms, p) -> print_count p ^ "Invalid ballot : " ^ vector_to_string proof_and_enc_string " " (fst u) ^ " \nPrevious tally : " ^ vector_string_pair " " ms ^ "\nCurrent tally : " ^ vector_string_pair " " ms ^ "\n" ^ iterate_char "-" 150 ^ "\n"
    | Coq_cfinish (us, vbs, inbs, ms, ds, pf, pt, b, p) -> print_count p ^ "Final tally : " ^ vector_string_pair " " ms ^ "\nFinal Decrypted Tally : " ^ vector_string " " ds ^ "\nFinal Decrypted Tally (Discrete Logarithm Search) : " ^ vector_string " " pt ^ "\nPlaintext tally checked (g^pt = ds for every candidate) : " ^ string_of_bool b ^ "\n" ^ iterate_char "-" 150 ^ "\n"


(* ---- Fiat-Shamir: recompute every challenge from the announcements ----
   The client derives the challenges of the individual proofs with SHAKE-256 
   over the public parameters and all commitments of the ballot, and the 
   challenge of the overall proof over the public parameters and its 
   announcement (see Approvalcode/main.ml). The tally recomputes both and 
   installs them in the transcripts, so the certified verifier accepts a 
   proof only if its responses answer the recomputed challenges. This 
   recomputation is part of the trusted computing base, like the parser. *)

type ('a, 'b) sum = Coq_inl of 'a | Coq_inr of 'b

let vector_to_bytes (m : Z.t) (v : (Z.t, Z.t) sum Tallylib.VectorDef.t) : bytes =
  Tallylib.Vector.fold_right
    (fun x acc ->
       let s = match x with
         | Coq_inl xa
         | Coq_inr xa -> Big_int_Z.string_of_big_int xa
       in
       Bytes.cat acc (Bytes.of_string s)) m v Bytes.empty

let rec construct_challenge_vector (n : int) (msg : bytes) : Z.t Tallylib.VectorDef.t = 
  match n with 
  | 0 -> Tallylib.VectorDef.Coq_nil
  | _ -> 
    let start = (n - 1) * 4 in
    let chunk = Bytes.sub msg start 4 in
    let z = big_int_of_bytes_mod_q chunk Tallylib.TallyIns.q in
    Tallylib.VectorDef.Coq_cons (z, Big_int_Z.big_int_of_int (n - 1), 
    (construct_challenge_vector (n - 1) msg))

let random_oracle (n : int) (m : Z.t) 
  (v : (Z.t, Z.t) sum Tallylib.VectorDef.t) : Z.t Tallylib.VectorDef.t =
  construct_challenge_vector n (shake256 ~msg:(vector_to_bytes m v) ~size:(4 * n))

let random_oracle_single (m : Z.t) 
  (v : (Z.t, Z.t) sum Tallylib.VectorDef.t) : Z.t =
  big_int_of_bytes_mod_q (shake256 ~msg:(vector_to_bytes m v) ~size:4) Tallylib.TallyIns.q

let public_prefix : (Z.t, Z.t) sum list =
  [Coq_inl Tallylib.TallyIns.p; Coq_inl Tallylib.TallyIns.q;
   Coq_inr Tallylib.TallyIns.g; Coq_inr Tallylib.TallyIns.h]

let flatten_announcement (a : (Z.t * Z.t) Tallylib.VectorDef.t) : (Z.t, Z.t) sum list =
  List.concat_map (fun (u, v) -> [Coq_inr u; Coq_inr v]) 
    (list_of_vector a)

let with_head_challenge (pf : (Z.t, Z.t * Z.t) sigma_proto) (c : Z.t) : (Z.t, Z.t * Z.t) sigma_proto =
  { pf with challenge = vector_of_list (c :: List.tl (list_of_vector pf.challenge)) }

let recompute_challenges (n : int) ((b, pf) : ballot) : ballot =
  let items = list_of_vector b in
  let input = public_prefix @ List.concat_map (fun (_, p) -> flatten_announcement p.announcement) items in
  let chal = list_of_vector (random_oracle n (Big_int_Z.big_int_of_int (List.length input)) (vector_of_list input)) in
  let b' = vector_of_list (List.map2 (fun (cp, p) c -> (cp, with_head_challenge p c)) items chal) in
  let input' = public_prefix @ flatten_announcement pf.announcement in
  let c' = random_oracle_single (Big_int_Z.big_int_of_int (List.length input')) (vector_of_list input') in
  (b', with_head_challenge pf c')


let _ =
  let n = 10 in (* candidates per ballot *)
  let bs = Parser.prog Lexer.token (Lexing.from_channel stdin) in 
  let bs = List.map (recompute_challenges n) bs in
  let us = rnd_list Tallylib.TallyIns.q n in (* goes for decryption proof construciton *)
  let cs = rnd_list Tallylib.TallyIns.q n in (* challenge but it needs to be hashed from all the public values so I need to change API. *)
  let tally = compute_final_count_ins (Big_int_Z.big_int_of_int n) discrete_log_search us cs bs in 
  match tally with 
  | Tallylib.Specif.Coq_existT (vbs, 
    Tallylib.Specif.Coq_existT (inbs, Tallylib.Specif.Coq_existT (pt, 
    Tallylib.Specif.Coq_existT (bfinal, count)))) -> 
    print_string (print_count count)
