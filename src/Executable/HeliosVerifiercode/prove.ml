(* The certified Helios ballot prover (Examples/HeliosFrontendIns.v) with
   Helios's Fiat-Shamir challenges, for bench/helios-diff: each candidate's
   challenge is SHA-1 over the decimal strings of its announcements
   A0,B0,A1,B1 (helios/crypto/algs.py, EG_disjunctive_challenge_generator),
   computed from helios_generate_ballot_commitment, whose announcements are
   those of the proofs (Approval.ballot_commitment_announcement). All
   randomness is an input, so the output is a function of the input.

   stdin:  {"h": "<decimal>", "ballots": [{"votes": [0|1, ...],
            "rs": ["<r>", ...], "uscs": [["<u>", "<s>", "<c>"], ...]}, ...]}
   stdout: one JSON object per ballot, {"choices": [{"alpha", "beta"}, ...],
            "individual_proofs": [[{challenge, commitment: {A, B}, response}, x2], ...]} *)
open HeliosTallylib
open HeliosTallylib.HeliosFrontendIns

let bi = Big_int_Z.big_int_of_int
let rec vector_of_list xs = match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t)
let rec list_of_vector v = match v with VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

let z = Big_int_Z.string_of_big_int
let challenge xs = Helios_parser.Ast.helios_challenge xs

let member k = function `Assoc kvs -> List.assoc k kvs | _ -> failwith ("missing " ^ k)
let num j = match j with `String s -> Big_int_Z.big_int_of_string s | `Int i -> bi i | _ -> failwith "not a number"
let nums j = match j with `List l -> List.map num l | _ -> failwith "not a list"

let () =
  let doc = Yojson.Safe.from_channel stdin in
  let h = num (member "h" doc) in
  let ballots = match member "ballots" doc with `List l -> l | _ -> failwith "ballots" in
  List.iter (fun b ->
    let ms = nums (member "votes" b) and rs = nums (member "rs" b) in
    let uscs = match member "uscs" b with `List l -> List.map (fun t -> vector_of_list (nums t)) l | _ -> failwith "uscs" in
    let n = List.length ms in
    let rsv = vector_of_list rs and msv = vector_of_list ms and uv = vector_of_list uscs in
    let comm = list_of_vector (helios_generate_ballot_commitment (bi n) h rsv msv uv) in
    let cs = List.map (fun br -> match list_of_vector br with
      | [(a0, b0); (a1, b1)] -> challenge [a0; b0; a1; b1] | _ -> failwith "two branches") comm in
    let out = list_of_vector (helios_encrypt_ballot_and_generate_enc_proof (bi n) h rsv msv uv (vector_of_list cs)) in
    let choice ((alpha, beta), _) = `Assoc [("alpha", `String (z alpha)); ("beta", `String (z beta))] in
    let proof (_, (pr : (Z.t, Z.t * Z.t) Sigma.sigma_proto)) =
      match list_of_vector pr.Sigma.announcement, list_of_vector pr.Sigma.challenge, list_of_vector pr.Sigma.response with
      | [(a0, b0); (a1, b1)], [_; c0; c1], [r0; r1] ->
        let br a b c r = `Assoc [("challenge", `String (z c)); ("commitment", `Assoc [("A", `String (z a)); ("B", `String (z b))]);
                                 ("response", `String (z r))] in
        `List [br a0 b0 c0 r0; br a1 b1 c1 r1]
      | _ -> failwith "proof shape" in
    print_endline (Yojson.Safe.to_string (`Assoc [("choices", `List (List.map choice out));
                                                   ("individual_proofs", `List (List.map proof out))])))
    ballots
