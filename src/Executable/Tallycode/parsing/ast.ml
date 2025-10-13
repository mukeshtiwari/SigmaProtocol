open Tallylib.BinInt.Z
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