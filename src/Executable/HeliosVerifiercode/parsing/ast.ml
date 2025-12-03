open HeliosTallylib.BinInt.Z
open HeliosTallylib.VectorDef
open HeliosTallylib.Sigma
open HeliosTallylib.HeliosTally

(* 

    Record ballot := mk_ballot {
      cast_at : string;
      ciphertext : Vector.t (G * G) n;
      encryption_proof : Vector.t (@Sigma.sigma_proto F (G * G) 2 3 2) n;
      election_hash : string;
      election_uuid : string;
      vote_hash : string;
      voter_hash : string;
      voter_uuid : string
    }.
*)


type ballot' = (Big_int_Z.big_int, Big_int_Z.big_int) ballot
  
(* 

 Record tallier := mk_tallier {
      decryption_factor : Vector.t G n;
      decryption_proof : Vector.t (@Sigma.sigma_proto F G 2 1 1) n;
      email : string;
      pok : @Sigma.sigma_proto F G 1 1 1;
      public_key : G * F * F * G (* g, p, q, y *);
      public_key_hash : string;
      uuid : strin

*)


type tallier' = (Big_int_Z.big_int, Big_int_Z.big_int) tallier


(* 
  Decrypted final tally   
*)

type tally = Big_int_Z.big_int HeliosTallylib.VectorDef.t



let vector_of_list (xs : 'a list) : 'a HeliosTallylib.VectorDef.t =
  let rec aux l =
    match l with
    | [] -> Coq_nil
    | lh :: lt ->
      let tail_len = Big_int_Z.big_int_of_int (List.length lt) in
      Coq_cons (lh, tail_len, aux lt)
    in aux xs