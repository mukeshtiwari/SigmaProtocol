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

(* Helios's Fiat-Shamir challenge (helios/crypto/algs.py, functions
   EG_disjunctive_challenge_generator and DLog_challenge_generator): SHA-1
   over the decimal strings of the group elements joined by commas, read as
   a 160-bit integer. That integer is below the 256-bit q, so the reduction
   modulo q is the identity; it is kept so the value is a field element by
   construction. The challenge is computed here, at the top level, and
   handed to the certified verifier inside the transcript, exactly as the
   frontend driver hands challenges to the certified prover. *)
let helios_challenge (xs : Big_int_Z.big_int list) : Big_int_Z.big_int =
  let s = String.concat "," (List.map Big_int_Z.string_of_big_int xs) in
  let digest = Cryptokit.hash_string (Cryptokit.Hash.sha1 ()) s in
  let hex = Cryptokit.transform_string (Cryptokit.Hexa.encode ()) digest in
  Big_int_Z.mod_big_int (Z.of_string_base 16 hex) HeliosTallylib.HeliosTallyIns.q
