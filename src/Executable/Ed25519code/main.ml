(* Driver for the Ed25519 instantiation (Examples/Ed25519Ins.v): Schnorr
   and Chaum-Pedersen proofs, and approval-voting ballots with individual
   0/1 proofs and the overall proof, over the order-l subgroup of
   Curve25519. The certified code is interactive; this driver draws the
   randomness and computes the Fiat-Shamir challenges (SHAKE-256 over the
   decimal coordinates of the public values and announcements) and hands
   them to the extracted functions. Also benchmarks a ballot. *)
open Ed25519lib
open Ed25519lib.Ed25519Ins
open Hacl_star.Hacl.Keccak

let l = Big_int_Z.big_int_of_string
  "7237005577332262213973186563042994240857116359379907606001950938285454250989"

(* ---- big-integer and vector helpers ---- *)

let big_int_of_bytes (s : bytes) : Z.t =
  let n = ref Big_int_Z.zero_big_int in
  Bytes.iter (fun c -> n := Big_int_Z.add_big_int
    (Big_int_Z.shift_left_big_int !n 8)
    (Big_int_Z.big_int_of_int (Char.code c))) s;
  !n

let rng = Cryptokit.Random.device_rng "/dev/urandom"

(* a uniformly random scalar in Z/lZ: 64 random bytes reduced modulo l *)
let rnd_scalar () : Ed25519.Ed25519.Zl.coq_F =
  let buf = Bytes.create 64 in
  rng#random_bytes buf 0 64;
  of_Z (big_int_of_bytes buf)

let rec vector_of_list (xs : 'a list) : 'a VectorDef.t =
  match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, Big_int_Z.big_int_of_int (List.length t), vector_of_list t)

let rec list_of_vector (v : 'a VectorDef.t) : 'a list =
  match v with
  | VectorDef.Coq_nil -> []
  | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

let rnd_vector (n : int) = vector_of_list (List.init n (fun _ -> rnd_scalar ()))
let rnd_vector_vector (n : int) (k : int) = vector_of_list (List.init n (fun _ -> rnd_vector k))

(* ---- serialisation and the random oracle ---- *)

let scalar_string (k : Ed25519.Ed25519.Zl.coq_F) : string =
  Big_int_Z.string_of_big_int (to_Z k)

let point_string (p : Ed25519.Ed25519.Ed.coq_G) : string =
  let (x, y) = point_to_Z p in
  "(" ^ Big_int_Z.string_of_big_int x ^ "," ^ Big_int_Z.string_of_big_int y ^ ")"

let points_string (v : Ed25519.Ed25519.Ed.coq_G VectorDef.t) : string =
  String.concat "," (List.map point_string (list_of_vector v))

let scalars_string (v : Ed25519.Ed25519.Zl.coq_F VectorDef.t) : string =
  String.concat "," (List.map scalar_string (list_of_vector v))

let pair_string ((a, b) : Ed25519.Ed25519.Ed.coq_G * Ed25519.Ed25519.Ed.coq_G) : string =
  point_string a ^ point_string b

(* k scalars from SHAKE-256 of a message: 64 bytes per scalar, reduced modulo l *)
let oracle_scalars (msg : string) (k : int) : Ed25519.Ed25519.Zl.coq_F list =
  let out = shake256 ~msg:(Bytes.of_string msg) ~size:(64 * k) in
  List.init k (fun i -> of_Z (big_int_of_bytes (Bytes.sub out (64 * i) 64)))

let oracle_scalar (msg : string) : Ed25519.Ed25519.Zl.coq_F =
  List.hd (oracle_scalars msg 1)

let proof_string (pf : (Ed25519.Ed25519.Zl.coq_F, Ed25519.Ed25519.Ed.coq_G) Sigma.sigma_proto) : string =
  "{ announcement = " ^ points_string pf.Sigma.announcement ^
  "; challenge = " ^ scalars_string pf.Sigma.challenge ^
  "; response = " ^ scalars_string pf.Sigma.response ^ " }"

(* replace the first response of a proof by response + 1 *)
let tamper (pf : ('f, 'g) Sigma.sigma_proto) : ('f, 'g) Sigma.sigma_proto =
  match list_of_vector pf.Sigma.response with
  | r :: rest -> { pf with Sigma.response =
      vector_of_list (Ed25519.Ed25519.Zl.add r Ed25519.Ed25519.Zl.one :: rest) }
  | [] -> pf

let time_it (f : unit -> 'a) : 'a * float =
  let t0 = Unix.gettimeofday () in
  let r = f () in
  (r, (Unix.gettimeofday () -. t0) *. 1000.0)

let median (xs : float list) : float =
  let s = List.sort compare xs in
  let n = List.length s in
  if n mod 2 = 1 then List.nth s (n / 2) else (List.nth s (n / 2 - 1) +. List.nth s (n / 2)) /. 2.0

let () =
  print_endline ("Ed25519: l = " ^ Big_int_Z.string_of_big_int l);
  print_endline ("g = B = " ^ point_string g);
  print_endline ("h = g^3 = " ^ point_string h);

  (* ---- Schnorr ---- *)
  let u = rnd_scalar () in
  let com = schnorr_protocol_commitment_ins u in
  let c = oracle_scalar ("schnorr|" ^ point_string g ^ point_string h ^ point_string com) in
  let pf = schnorr_protocol_construction_ins u c in
  print_endline ("schnorr proof " ^ proof_string pf);
  print_endline ("schnorr verify: " ^ string_of_bool (schnorr_protocol_verification_ins pf));
  print_endline ("schnorr verify (tampered): " ^ string_of_bool (schnorr_protocol_verification_ins (tamper pf)));

  (* ---- Chaum-Pedersen ---- *)
  let u = rnd_scalar () in
  let com = construct_cp_conversations_schnorr_commitment_ins u in
  let c = oracle_scalar ("cp|" ^ point_string g ^ point_string h ^ point_string c_UU2081_ ^
                          point_string c_UU2082_ ^ points_string com) in
  let pf = construct_cp_conversations_schnorr_ins u c in
  print_endline ("chaum-pedersen proof " ^ proof_string pf);
  print_endline ("chaum-pedersen verify: " ^ string_of_bool (generalised_cp_accepting_conversations_ins pf));
  print_endline ("chaum-pedersen verify (tampered): " ^ string_of_bool (generalised_cp_accepting_conversations_ins (tamper pf)));

  (* ---- approval ballot with n candidates ---- *)
  let n = try int_of_string Sys.argv.(1) with _ -> 7 in
  let iters = try int_of_string Sys.argv.(2) with _ -> 30 in
  let nz = Big_int_Z.big_int_of_int (n - 1) in
  let fn _ (v : Ed25519.Ed25519.Ed.coq_G VectorDef.t) : Ed25519.Ed25519.Zl.coq_F VectorDef.t =
    vector_of_list (oracle_scalars ("ballot|" ^ points_string v) n) in
  let fo _ (v : Ed25519.Ed25519.Ed.coq_G VectorDef.t) : Ed25519.Ed25519.Zl.coq_F =
    oracle_scalar ("overall|" ^ points_string v) in
  let make_ballot () =
    let rs = rnd_vector n in
    let ms = vector_of_list (List.init n (fun _ -> of_Z (Big_int_Z.big_int_of_int (Random.int 2)))) in
    let uscs = rnd_vector_vector n 3 in
    let uscs' = rnd_vector ((n + 1) + n) in
    nizk_encrypt_ballot_with_overall_proof_ins nz fn fo rs ms uscs uscs' in
  Random.self_init ();
  let (b, pf) = make_ballot () in
  print_endline ("ballot of " ^ string_of_int n ^ " candidates: individual proofs verify: " ^
    string_of_bool (verify_encryption_ballot_proof_ins (Big_int_Z.big_int_of_int n) b));
  print_endline ("overall proof verify: " ^
    string_of_bool (verify_overall_proof_ins (Big_int_Z.big_int_of_int n) (Vector.map (fun (cp, _) -> cp) (Big_int_Z.big_int_of_int n) b) pf));
  print_endline ("full ballot verify: " ^ string_of_bool (verify_ballot_ins (Big_int_Z.big_int_of_int n) (b, pf)));
  print_endline ("full ballot verify (overall proof tampered): " ^
    string_of_bool (verify_ballot_ins (Big_int_Z.big_int_of_int n) (b, tamper pf)));
  (* a ballot with an invalid vote (value 5) must be rejected *)
  let rs = rnd_vector n in
  let ms = vector_of_list (of_Z (Big_int_Z.big_int_of_int 5) :: List.init (n - 1) (fun _ -> of_Z Big_int_Z.zero_big_int)) in
  let (b5, pf5) = nizk_encrypt_ballot_with_overall_proof_ins nz fn fo rs ms (rnd_vector_vector n 3) (rnd_vector ((n + 1) + n)) in
  print_endline ("ballot encrypting 5 verify: " ^ string_of_bool (verify_ballot_ins (Big_int_Z.big_int_of_int n) (b5, pf5)));

  (* ---- benchmark ---- *)
  let enc = ref [] and ver = ref [] and ok = ref true in
  for _ = 1 to iters do
    let (bp, te) = time_it make_ballot in
    let (r, tv) = time_it (fun () -> verify_ballot_ins (Big_int_Z.big_int_of_int n) bp) in
    ok := !ok && r; enc := te :: !enc; ver := tv :: !ver
  done;
  Printf.printf "benchmark n = %d, iterations = %d, all verified = %b\n" n iters !ok;
  Printf.printf "ballot encryption + proofs (individual + overall): median %.2f ms\n" (median !enc);
  Printf.printf "ballot verification (individual + overall):        median %.2f ms\n" (median !ver)
