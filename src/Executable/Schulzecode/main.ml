(* The three-candidate Schulze example (Examples/SchulzeIns.v):
   five position-encoded ballots with their proofs, two invalid ballots, the 
   aggregated margins, and the trustees' tally certificate. Everything that 
   the bulletin board would carry is printed in full. *)
open Schulzelib.SchulzeIns
open Schulzelib.Sigma

let rec vector_to_list (v : 'a Schulzelib.VectorDef.t) : 'a list =
  match v with
  | Schulzelib.VectorDef.Coq_nil -> []
  | Schulzelib.VectorDef.Coq_cons (h, _, r) -> h :: vector_to_list r

let z = Big_int_Z.string_of_big_int
let cand = [| "A"; "B"; "C" |]

let rec fin_to_int (f : Schulzelib.Fin.t) : int =
  match f with
  | Schulzelib.Fin.F1 _ -> 0
  | Schulzelib.Fin.FS (_, f') -> 1 + fin_to_int f'

let string_of_bool_vec v = 
  String.concat " " (List.map string_of_bool (vector_to_list v))

let string_of_opt o = 
  match o with 
  | None -> "?" 
  | Some x -> z x

let string_of_z_row row = 
  "  " ^ String.concat " " (List.map z (vector_to_list row))

let cipher (c1, c2) = "(" ^ z c1 ^ ", " ^ z c2 ^ ")"

let cipher_list v = String.concat " " (List.map cipher (vector_to_list v))

let scalar_list v = String.concat " " (List.map z (vector_to_list v))

(* a proof whose announcements are ciphertext pairs (EncProof, OrSigmaGen over G × G) *)
let proof2 (pf : (Z.t, Z.t * Z.t) sigma_proto) : string =
  "announcement [" ^ cipher_list pf.announcement ^ "]  challenge [" ^ 
  scalar_list pf.challenge ^ "]  response [" ^ scalar_list pf.response ^ "]"

(* a proof whose announcements are group elements (DecProof) *)
let proof1 (pf : (Z.t, Z.t) sigma_proto) : string =
  "announcement [" ^ scalar_list pf.announcement ^ "]  challenge [" ^ 
  scalar_list pf.challenge ^ "]  response [" ^ scalar_list pf.response ^ "]"

let path_string (l : Schulzelib.Fin.t list) : string =
  String.concat " -> " (List.map (fun f -> cand.(fin_to_int f)) l)

let iter_matrix (f : int -> int -> 'a -> unit) (m : 'a Schulzelib.VectorDef.t Schulzelib.VectorDef.t) =
  List.iteri (fun i row -> List.iteri (fun j x -> f i j x) (vector_to_list row)) 
    (vector_to_list m)

let print_ballot_body (b : ballot3) =
  let (poss, pairs) = b in
  List.iteri (fun i (cp, pf) ->
    Printf.printf "  position %s: Enc(s_%s) = %s\n    membership s in {0..3}: %s\n" 
      cand.(i) cand.(i) (cipher cp) (proof2 pf)) (vector_to_list poss);
  iter_matrix (fun i j ((cb, pfb), pfm) ->
    Printf.printf "  pair (%s,%s): Enc(b) = %s\n" cand.(i) cand.(j) (cipher cb);
    Printf.printf "    bit proof b in {0,1}:              %s\n" (proof2 pfb);
    Printf.printf "    membership K b + delta (K = 7):    %s\n" (proof2 pfm)) pairs

let print_ballot (k : int) (b : ballot3) =
  Printf.printf "ballot %d\n" (k + 1);
  print_ballot_body b

let print_cipher_matrix (name : string) (m : (Z.t * Z.t) Schulzelib.VectorDef.t Schulzelib.VectorDef.t) =
  print_endline name;
  iter_matrix (fun i j c -> 
    Printf.printf "  (%s,%s) %s\n" cand.(i) cand.(j) (cipher c)) m

let print_proof2_matrix (name : string) m =
  print_endline name;
  iter_matrix (fun i j pf -> 
    Printf.printf "  (%s,%s) %s\n" cand.(i) cand.(j) (proof2 pf)) m

let print_tally_proof (pf : (Z.t, Z.t) Schulzelib.SchulzeTally.tally_proof) =
  let open Schulzelib.SchulzeTally in
  print_cipher_matrix "1. fresh re-encryptions Enc'(D_ij) of the margins:" pf.tp_encD';
  print_endline "   decryption proofs: Enc'(D_ij) / Enc(D_ij) decrypts to 1 (Chaum-Pedersen with the secret key):";
  iter_matrix (fun i j p -> 
    Printf.printf "  (%s,%s) %s\n" cand.(i) cand.(j) (proof1 p)) pf.tp_dec;
  print_cipher_matrix "2. encrypted defeats Enc(d_ij):" pf.tp_enc_d;
  print_proof2_matrix "   range proofs d_ij in {0..5}:" pf.tp_d_range;
  print_proof2_matrix "   defeat disjunctions (11 branches: 6 for d_ij = 0 and D_ij - D_ji in {-5..0}, 5 for d_ij = D_ij and D_ij - D_ji in {1..5}):" pf.tp_defeat;
  print_cipher_matrix "3. encrypted strongest paths Enc(p_ij):" pf.tp_enc_p;
  print_proof2_matrix "   lower bound p_ij - d_ij in {0..5}:" pf.tp_lower;
  print_endline "   closure disjunctions p_ij >= p_ik or p_ij >= p_kj (12 branches), indexed [k][i][j]:";
  List.iteri (fun k m -> 
    iter_matrix (fun i j p -> 
      Printf.printf "  k=%s (%s,%s) %s\n" cand.(k) cand.(i) cand.(j) (proof2 p)) m) 
    (vector_to_list pf.tp_upper);
  print_endline "   witness paths and edge proofs d_uv - p_ij in {0..5}:";
  let edges = pf.tp_edges in
  iter_matrix (fun i j path ->
    Printf.printf "  (%s,%s) path %s\n" cand.(i) cand.(j) (path_string path);
    let pfs = List.nth (vector_to_list (List.nth (vector_to_list edges) i)) j in
    List.iteri (fun e p -> Printf.printf "    edge %d: %s\n" (e + 1) (proof2 p)) pfs) 
    pf.tp_paths;
  print_endline "4. winner inequalities p_wj - p_jw in {0..5}:";
  List.iteri (fun j p -> Printf.printf "  j=%s %s\n" cand.(j) (proof2 p)) 
    (vector_to_list pf.tp_winner)

(* the random oracle: SHAKE-256 of the decimal serialisation of the 
   transcript, reduced modulo q *)
let big_int_of_bytes_mod_q (s : bytes) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  Big_int_Z.mod_big_int !n q

let hash_oracle (l : (Z.t * Z.t) list) : Z.t =
  let msg = Bytes.of_string (String.concat "," (List.map (fun (a, b) -> z a ^ ":" ^ z b) l)) in
  big_int_of_bytes_mod_q (Hacl_star.Hacl.Keccak.shake256 ~msg ~size:32)

let tally_hash_oracle (l : Z.t Schulzelib.SchulzeTally.tr_item list) : Z.t =
  let item = function
    | Schulzelib.SchulzeTally.TrC (a, b) -> "C" ^ z a ^ ":" ^ z b
    | Schulzelib.SchulzeTally.TrG a -> "G" ^ z a
    | Schulzelib.SchulzeTally.TrN k -> "N" ^ z k in
  let msg = Bytes.of_string (String.concat "," (List.map item l)) in
  big_int_of_bytes_mod_q (Hacl_star.Hacl.Keccak.shake256 ~msg ~size:32)

let nizk_ballots : ballot3 list =
  List.map2 (fun s k -> nizk_encrypt_ballot_ins hash_oracle s (ballot_rand_of k))
    (vector_to_list positions) 
    (List.map Big_int_Z.big_int_of_int [1; 2; 3; 4; 5])


(* ---- the count as a state machine ----
   compute_final_count_ins returns the verdict together with its evidence, 
   a derivation of count (finished ...). As in Tallycode/main.ml, we walk 
   the derivation from the axiom upwards and print every step: the ballot 
   that was read, its challenge and verdict, the margins before and after, 
   and finally the certificate and the checks of the finish rule. *)

let rule = String.make 100 '-'

let print_margins (name : string) m =
  print_endline name;
  List.iteri (fun i row ->
    Printf.printf "  %s: %s\n" cand.(i)
      (String.concat "  " (List.mapi (fun j c -> 
        Printf.sprintf "(%s,%s) %s" cand.(i) cand.(j) (cipher c)) (vector_to_list row))))
    (vector_to_list m)

(* returns the number of ballots read so far *)
let rec print_count (c : (Z.t, Z.t) Schulzelib.SchulzeTally.count) : int =
  let open Schulzelib.SchulzeTally in
  match c with
  | Coq_ax ms ->
    print_endline "[ax] initial state: no ballot read, every margin encrypts 0";
    print_margins "  margins:" ms;
    print_endline rule;
    0
  | Coq_cvalid (b, _us, vbs, inbs, ms, nms, p) ->
    let k = print_count p in
    Printf.printf "[cvalid] ballot %d read\n" (k + 1);
    print_ballot_body b;
    Printf.printf "  challenge H(ballot) = %s\n" (z (ballot_challenge_ins hash_oracle b));
    Printf.printf "  nizk_verify_ballot = true: the ballot is aggregated\n";
    print_margins "  previous margins:" ms;
    print_margins "  current margins (previous * Enc(b_ij)):" nms;
    Printf.printf "  valid so far %d, invalid so far %d\n" (List.length vbs + 1) (List.length inbs);
    print_endline rule;
    k + 1
  | Coq_cinvalid (b, _us, vbs, inbs, ms, p) ->
    let k = print_count p in
    Printf.printf "[cinvalid] ballot %d read\n" (k + 1);
    print_ballot_body b;
    Printf.printf "  challenge H(ballot) = %s\n" (z (ballot_challenge_ins hash_oracle b));
    Printf.printf "  nizk_verify_ballot = false: the ballot is set aside\n";
    print_margins "  margins (unchanged):" ms;
    Printf.printf "  valid so far %d, invalid so far %d\n" (List.length vbs) (List.length inbs + 1);
    print_endline rule;
    k + 1
  | Coq_finish (_us, vbs, inbs, ms, w, pf, bsize, bpf, bfinal, p) ->
    let k = print_count p in
    Printf.printf "[finish] all %d ballots read: %d valid, %d invalid\n" 
      k (List.length vbs) (List.length inbs);
    print_margins "  final encrypted margins Enc(D_ij):" ms;
    Printf.printf "  announced winner: %s\n" cand.(fin_to_int w);
    print_endline "  certificate:";
    print_tally_proof pf;
    Printf.printf "  challenge H(transcript) = %s\n" (z (tally_challenge_ins tally_hash_oracle w pf));
    Printf.printf "  valid ballots <= N = 5:                   %b\n" bsize;
    Printf.printf "  nizk_verify_tally on the final margins:   %b\n" bpf;
    Printf.printf "  verdict (both):                           %b\n" bfinal;
    print_endline rule;
    k

(* run the certified count and walk its derivation; compute_final_count 
   recurses on the tail first, so the ballots are read from the end of the 
   list (as in Tallycode): the list is reversed so that the walk reads them 
   in the order given *)
let run_count (name : string) (verbose : bool) (bs : ballot3 list) 
    (w : Schulzelib.Fin.t) (pf : (Z.t, Z.t) Schulzelib.SchulzeTally.tally_proof) =
  match compute_final_count_ins hash_oracle tally_hash_oracle (List.rev bs) w pf with
  | Schulzelib.Specif.Coq_existT (bfinal, Schulzelib.Specif.Coq_existT (vbs, 
      Schulzelib.Specif.Coq_existT (inbs, c))) ->
    Printf.printf "%s\n" name;
    if verbose then ignore (print_count c);
    Printf.printf "  => %d ballots, %d valid, %d invalid, winner %s, verdict %b\n" 
      (List.length bs) (List.length vbs) (List.length inbs) cand.(fin_to_int w) bfinal

let () =
  Printf.printf "p = %s, q = %s, g = %s, h = %s, m = 3 candidates A, B, C\n" 
    (z p) (z q) (z g) (z h);
  print_endline "=== ballots (A>B=C, B>C>A, B>C>A, C>A>B, A>C>B) ===";
  List.iteri print_ballot (vector_to_list ballots);
  Printf.printf "ballots verify:                                    %s\n" 
    (string_of_bool_vec ballots_ok);
  print_endline "=== invalid ballots ===";
  print_ballot 5 ballot_bad_pos;
  Printf.printf "ballot with a position out of range verifies:     %b\n" 
    ballot_bad_pos_ok;
  print_ballot 6 ballot_bad_pair;
  Printf.printf "ballot with cell (B,A) replaced by (A,B) verifies: %b\n" 
    ballot_bad_pair_ok;
  print_endline "=== non-interactive ballots (Fiat-Shamir, SHAKE-256 challenge) ===";
  List.iteri (fun k b ->
    Printf.printf "ballot %d: challenge %s, verifies %b\n" (k + 1)
      (z (ballot_challenge_ins hash_oracle b)) (nizk_verify_ballot_ins hash_oracle b))
    nizk_ballots;
  Printf.printf "interactive ballot 1 under the non-interactive verifier: %b\n"
    (nizk_verify_ballot_ins hash_oracle (List.hd (vector_to_list ballots)));
  print_endline "=== aggregation ===";
  print_cipher_matrix "encrypted margins Enc(D_ij) = product of the ballots' Enc(b_ij):" encD;
  print_endline "margins D decrypted with the secret key (demonstration only):";
  List.iter (fun row -> 
    print_endline ("  " ^ String.concat " " (List.map string_of_opt (vector_to_list row)))) 
    (vector_to_list coq_D_plain);
  print_endline "=== trustees' plaintext computation (never published) ===";
  print_endline "defeats d:";
  List.iter (fun row -> print_endline (string_of_z_row row)) (vector_to_list d_Z);
  print_endline "strongest paths p (closure):";
  List.iter (fun row -> print_endline (string_of_z_row row)) (vector_to_list p_Z);
  Printf.printf "winner index (0 = A, 1 = B, 2 = C): %s\n" (string_of_opt w_idx);
  Printf.printf "plaintext certificate passes cert_ok_b:          %b\n" cert_ok_ins;
  print_endline "=== tally certificate for C ===";
  print_tally_proof tally_pf;
  Printf.printf "certificate for C verifies:                        %b\n" tally_ok;
  Printf.printf "  checks (re-encryption, d range, defeat, p >= d, closed, paths, winner): %s\n"
    (String.concat " " (List.map string_of_bool tally_checks_ins));
  Printf.printf "certificate for A (not a winner) verifies:         %b\n" tally_bad_ok;
  Printf.printf "certificate for C checked against winner A:        %b\n" tally_wrong_winner_ok;
  print_endline "=== non-interactive tally (Fiat-Shamir, SHAKE-256 challenge) ===";
  let pfC = nizk_generate_tally_ins tally_hash_oracle wC in
  Printf.printf "challenge of the certificate for C:               %s\n" 
    (z (tally_challenge_ins tally_hash_oracle wC pfC));
  Printf.printf "non-interactive certificate for C verifies:        %b\n" 
    (nizk_verify_tally_ins tally_hash_oracle wC pfC);
  Printf.printf "interactive certificate under the NIZK verifier:   %b\n" 
    (nizk_verify_tally_ins tally_hash_oracle wC tally_pf);
  let pfA = nizk_generate_tally_ins tally_hash_oracle (Schulzelib.Fin.F1 (Big_int_Z.big_int_of_int 2)) in
  Printf.printf "non-interactive certificate for A verifies:        %b\n" 
    (nizk_verify_tally_ins tally_hash_oracle (Schulzelib.Fin.F1 (Big_int_Z.big_int_of_int 2)) pfA);
  print_endline "=== the count as a state machine (count : state -> Type) ===";
  let all = nizk_ballots @ [ballot_bad_pos; ballot_bad_pair] in
  let fA = Schulzelib.Fin.F1 (Big_int_Z.big_int_of_int 2) in
  run_count "--- 5 NIZK ballots + 2 bad ballots, certificate for C (full walk) ---" true all wC pfC;
  print_endline "--- other runs (verdict only) ---";
  run_count "5 NIZK ballots + 2 bad ballots, certificate for A:" false all fA pfA;
  run_count "5 NIZK ballots + 2 bad ballots, certificate for C checked against A:" false all fA pfC;
  run_count "5 interactive ballots (no NIZK challenge), certificate for C:" false 
    (vector_to_list ballots) wC pfC;
  run_count "4 NIZK ballots only (aggregate differs), certificate for C:" false 
    (List.tl nizk_ballots) wC pfC
