open Tallylib.BinInt.Z
open Tallylib.VectorDef
open Tallylib.Sigma

(* one ciphertext and 0/1 proof per candidate, and the overall proof *)
type ballot = 
  ((Big_int_Z.big_int * Big_int_Z.big_int) * 
   (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) Tallylib.Sigma.sigma_proto) 
  Tallylib.VectorDef.t *
  (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) Tallylib.Sigma.sigma_proto

let vector_of_list (xs : 'a list) : 'a Tallylib.VectorDef.t =
  let rec aux l =
    match l with
    | [] -> Coq_nil
    | lh :: lt ->
      let tail_len = Big_int_Z.big_int_of_int (List.length lt) in
      Coq_cons (lh, tail_len, aux lt)
    in aux xs

let rec list_of_vector (v : 'a Tallylib.VectorDef.t) : 'a list =
  match v with
  | Coq_nil -> []
  | Coq_cons (h, _, t) -> h :: list_of_vector t
