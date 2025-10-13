open Tallylib.BinInt
open Tallylib.VectorDef
open Tallylib.Sigma


type ballot = ((Big_int_Z.big_int * Big_int_Z.big_int) * (Big_int_Z.big_int, Big_int_Z.big_int * Big_int_Z.big_int) Tallylib.Sigma.sigma_proto) Tallylib.VectorDef.t

let vector_of_list (xs : 'a list) : 'a Tallylib.VectorDef.t =
  let rec aux l =
    match l with
    | [] -> Coq_nil
    | lh :: lt ->
      let tail_len = Big_int_Z.big_int_of_int (List.length lt) in
      Coq_cons (lh, tail_len, aux lt)
    in aux xs

let vector_to_list (v : 'a  Tallylib.VectorDef.t) : 'a list =
  let rec aux acc = function
    | Coq_nil -> List.rev acc
    | Coq_cons (x, _, tl) -> aux (x :: acc) tl
in aux [] v