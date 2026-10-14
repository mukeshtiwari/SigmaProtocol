(* The input language of the ElectionGuard verifier: the JSON documents of
   an ElectionGuard 2.0 election record as the reference implementation
   electionguard-kotlin-multiplatform writes them (constants, election
   configuration, manifest, initialisation, encrypted ballots, encrypted
   tally, decrypted tally and challenged ballots), and the trusted boundary
   between them and the certified verifier.

   Trusted boundary. The certified verifier's types assume that every group
   element lies in the subgroup of order q of Z_p^* and every scalar is in
   Z_q (verifications 2.A, 3.A, 5.A, 5.B, 5.C, 9.A, … of the specification).
   Every hexadecimal element and scalar is checked here as it is read. The
   records are written by a Kotlin serializer, so the grammar does not fix
   the order of the fields of an object: each object is a list of keyed
   members that the builders assemble, requiring the fields the verifier
   uses exactly once and skipping the others. *)

open Electionguardlib
open Electionguardlib.ElectionGuardIns
module List = Stdlib.List
module String = Stdlib.String

type elem = Zpstar.Schnorr.coq_Schnorr_group
type scalar = Zpstar.Zpfield.coq_Zp
type proof = scalar BeleniosTally.proof

(* ---- the parameters, from the certified instantiation ---- *)

let p : Z.t = ElectionGuardIns.p
let q : Z.t = ElectionGuardIns.q

let z_of_hex (s : string) : Z.t =
  try Z.of_string_base 16 s with Invalid_argument _ -> failwith ("not a hexadecimal number: " ^ s)

let in_group (x : Z.t) : bool = Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one

let elem_of_hex (s : string) : elem =
  let x = z_of_hex s in
  if not (in_group x) then failwith ("element not in the order-q subgroup: " ^ String.sub s 0 (min 16 (String.length s)) ^ "…");
  x

let scalar_of_hex (s : string) : scalar =
  let x = z_of_hex s in
  if Z.sign x < 0 || Z.geq x q then failwith ("scalar out of range: " ^ s);
  x

let scalar_of_int (n : int) : scalar =
  if n < 0 then failwith "negative value";
  Z.of_int n

(* ---- the documents ---- *)

type ciphertext = { pad : elem; data : elem }
type constants = { large_prime : Z.t; small_prime : Z.t; cofactor : Z.t; generator : Z.t }
type config = {
  config_version : string; number_of_guardians : int; quorum : int;
  parameter_base_hash : string; manifest_hash : string; election_base_hash : string }
type selection_spec = { ss_object_id : string; ss_sequence_order : int }
type contest_spec = {
  cs_object_id : string; cs_sequence_order : int; cs_votes_allowed : int;
  cs_option_selection_limit : int option; cs_ballot_selections : selection_spec list }
type manifest = { m_contests : contest_spec list }
type coefficient = { k_public_key : elem; k_proof : proof }
type guardian = { g_x_coordinate : int; g_coefficient_proofs : coefficient list }
type initialized = { joint_public_key : elem; extended_base_hash : string; guardians : guardian list }
type selection = { sel_id : string; sel_sequence_order : int; sel_encrypted_vote : ciphertext; sel_proofs : proof list }
type contest = {
  con_id : string; con_sequence_order : int; con_hash : string; con_selections : selection list; con_proofs : proof list }
type eballot = {
  ballot_id : string; b_election_id : string; state : string; code_baux : string;
  confirmation_code : string; b_contests : contest list }
type tally_selection = { ts_id : string; ts_sequence_order : int; ts_encrypted_vote : ciphertext }
type tally_contest = { tc_id : string; tc_sequence_order : int; tc_selections : tally_selection list }
type encrypted_tally = { et_election_id : string; et_contests : tally_contest list }
type decryption = { d_id : string; d_tally : int; d_b_over_m : elem; d_encrypted_vote : ciphertext; d_proof : proof }
type dcontest = { dc_id : string; dc_selections : decryption list }
(* the decrypted tally (tally.json) and a challenged ballot (dballot-*.json) *)
type decryptions = { dec_id : string option; dec_election_id : string option; dec_contests : dcontest list }

(* ---- builders: the fields used, exactly once ---- *)

let set (what : string) (name : string) (r : 'a option ref) (v : 'a) : unit =
  match !r with Some _ -> failwith (what ^ ": duplicate field " ^ name) | None -> r := Some v
let req (what : string) (name : string) (r : 'a option ref) : 'a =
  match !r with Some v -> v | None -> failwith (what ^ ": missing field " ^ name)

let build_ciphertext ms : ciphertext =
  let pad = ref None and data = ref None in
  List.iter (function `Pad v -> set "ciphertext" "pad" pad v | `Data v -> set "ciphertext" "data" data v | `Skip -> ()) ms;
  { pad = req "ciphertext" "pad" pad; data = req "ciphertext" "data" data }

let build_proof ms : proof =
  let c = ref None and r = ref None in
  List.iter (function `Challenge v -> set "proof" "challenge" c v | `Response v -> set "proof" "response" r v | `Skip -> ()) ms;
  (req "proof" "challenge" c, req "proof" "response" r)

let build_proofs ms : proof list =
  let ps = ref None in
  List.iter (function `Proofs v -> set "proof" "proofs" ps v | `Skip -> ()) ms;
  req "proof" "proofs" ps

let build_constants ms : constants =
  let lp = ref None and sp = ref None and co = ref None and ge = ref None in
  List.iter (function
    | `Large_prime v -> set "constants" "large_prime" lp v | `Small_prime v -> set "constants" "small_prime" sp v
    | `Cofactor v -> set "constants" "cofactor" co v | `Generator v -> set "constants" "generator" ge v | `Skip -> ()) ms;
  { large_prime = req "constants" "large_prime" lp; small_prime = req "constants" "small_prime" sp;
    cofactor = req "constants" "cofactor" co; generator = req "constants" "generator" ge }

let build_config ms : config =
  let v = ref None and n = ref None and k = ref None and hp = ref None and hm = ref None and hb = ref None in
  List.iter (function
    | `Config_version x -> set "config" "config_version" v x | `Number_of_guardians x -> set "config" "number_of_guardians" n x
    | `Quorum x -> set "config" "quorum" k x | `Parameter_base_hash x -> set "config" "parameter_base_hash" hp x
    | `Manifest_hash x -> set "config" "manifest_hash" hm x | `Election_base_hash x -> set "config" "election_base_hash" hb x
    | `Skip -> ()) ms;
  { config_version = req "config" "config_version" v; number_of_guardians = req "config" "number_of_guardians" n;
    quorum = req "config" "quorum" k; parameter_base_hash = req "config" "parameter_base_hash" hp;
    manifest_hash = req "config" "manifest_hash" hm; election_base_hash = req "config" "election_base_hash" hb }

let build_selection_spec ms : selection_spec =
  let id = ref None and seq = ref None in
  List.iter (function `Object_id v -> set "selection" "object_id" id v | `Sequence_order v -> set "selection" "sequence_order" seq v | `Skip -> ()) ms;
  { ss_object_id = req "selection" "object_id" id; ss_sequence_order = req "selection" "sequence_order" seq }

let build_contest_spec ms : contest_spec =
  let id = ref None and seq = ref None and va = ref None and osl = ref None and sels = ref None in
  List.iter (function
    | `Object_id v -> set "contest" "object_id" id v | `Sequence_order v -> set "contest" "sequence_order" seq v
    | `Votes_allowed v -> set "contest" "votes_allowed" va v | `Option_selection_limit v -> set "contest" "option_selection_limit" osl v
    | `Ballot_selections v -> set "contest" "ballot_selections" sels v | `Skip -> ()) ms;
  { cs_object_id = req "contest" "object_id" id; cs_sequence_order = req "contest" "sequence_order" seq;
    cs_votes_allowed = req "contest" "votes_allowed" va; cs_option_selection_limit = !osl;
    cs_ballot_selections = req "contest" "ballot_selections" sels }

let build_manifest ms : manifest =
  let cs = ref None in
  List.iter (function `Contests v -> set "manifest" "contests" cs v | `Skip -> ()) ms;
  { m_contests = req "manifest" "contests" cs }

let build_coefficient ms : coefficient =
  let pk = ref None and c = ref None and r = ref None in
  List.iter (function
    | `Public_key v -> set "coefficient proof" "public_key" pk v | `Challenge v -> set "coefficient proof" "challenge" c v
    | `Response v -> set "coefficient proof" "response" r v | `Skip -> ()) ms;
  { k_public_key = req "coefficient proof" "public_key" pk;
    k_proof = (req "coefficient proof" "challenge" c, req "coefficient proof" "response" r) }

let build_guardian ms : guardian =
  let x = ref None and cps = ref None in
  List.iter (function `X_coordinate v -> set "guardian" "x_coordinate" x v | `Coefficient_proofs v -> set "guardian" "coefficient_proofs" cps v | `Skip -> ()) ms;
  { g_x_coordinate = req "guardian" "x_coordinate" x; g_coefficient_proofs = req "guardian" "coefficient_proofs" cps }

let build_initialized ms : initialized =
  let k = ref None and he = ref None and gs = ref None in
  List.iter (function
    | `Joint_public_key v -> set "initialization" "joint_public_key" k v | `Extended_base_hash v -> set "initialization" "extended_base_hash" he v
    | `Guardians v -> set "initialization" "guardians" gs v | `Skip -> ()) ms;
  { joint_public_key = req "initialization" "joint_public_key" k; extended_base_hash = req "initialization" "extended_base_hash" he;
    guardians = req "initialization" "guardians" gs }

let build_selection ms : selection =
  let id = ref None and seq = ref None and ev = ref None and pf = ref None in
  List.iter (function
    | `Selection_id v -> set "selection" "selection_id" id v | `Sequence_order v -> set "selection" "sequence_order" seq v
    | `Encrypted_vote v -> set "selection" "encrypted_vote" ev v | `Proofs v -> set "selection" "proof" pf v | `Skip -> ()) ms;
  { sel_id = req "selection" "selection_id" id; sel_sequence_order = req "selection" "sequence_order" seq;
    sel_encrypted_vote = req "selection" "encrypted_vote" ev; sel_proofs = req "selection" "proof" pf }

let build_contest ms : contest =
  let id = ref None and seq = ref None and h = ref None and sels = ref None and pf = ref None in
  List.iter (function
    | `Contest_id v -> set "contest" "contest_id" id v | `Sequence_order v -> set "contest" "sequence_order" seq v
    | `Contest_hash v -> set "contest" "contest_hash" h v | `Selections v -> set "contest" "selections" sels v
    | `Proofs v -> set "contest" "proof" pf v | `Skip -> ()) ms;
  { con_id = req "contest" "contest_id" id; con_sequence_order = req "contest" "sequence_order" seq;
    con_hash = req "contest" "contest_hash" h; con_selections = req "contest" "selections" sels; con_proofs = req "contest" "proof" pf }

let build_eballot ms : eballot =
  let id = ref None and eid = ref None and st = ref None and baux = ref None and code = ref None and cs = ref None in
  List.iter (function
    | `Ballot_id v -> set "ballot" "ballot_id" id v | `Election_id v -> set "ballot" "election_id" eid v
    | `State v -> set "ballot" "state" st v | `Code_baux v -> set "ballot" "code_baux" baux v
    | `Confirmation_code v -> set "ballot" "confirmation_code" code v | `Contests v -> set "ballot" "contests" cs v | `Skip -> ()) ms;
  { ballot_id = req "ballot" "ballot_id" id; b_election_id = req "ballot" "election_id" eid; state = req "ballot" "state" st;
    code_baux = req "ballot" "code_baux" baux; confirmation_code = req "ballot" "confirmation_code" code;
    b_contests = req "ballot" "contests" cs }

let build_tally_selection ms : tally_selection =
  let id = ref None and seq = ref None and ev = ref None in
  List.iter (function
    | `Selection_id v -> set "selection" "selection_id" id v | `Sequence_order v -> set "selection" "sequence_order" seq v
    | `Encrypted_vote v -> set "selection" "encrypted_vote" ev v | `Skip -> ()) ms;
  { ts_id = req "selection" "selection_id" id; ts_sequence_order = req "selection" "sequence_order" seq;
    ts_encrypted_vote = req "selection" "encrypted_vote" ev }

let build_tally_contest ms : tally_contest =
  let id = ref None and seq = ref None and sels = ref None in
  List.iter (function
    | `Contest_id v -> set "contest" "contest_id" id v | `Sequence_order v -> set "contest" "sequence_order" seq v
    | `Selections v -> set "contest" "selections" sels v | `Skip -> ()) ms;
  { tc_id = req "contest" "contest_id" id; tc_sequence_order = req "contest" "sequence_order" seq;
    tc_selections = req "contest" "selections" sels }

let build_encrypted_tally ms : encrypted_tally =
  let eid = ref None and cs = ref None in
  List.iter (function `Election_id v -> set "encrypted tally" "election_id" eid v | `Contests v -> set "encrypted tally" "contests" cs v | `Skip -> ()) ms;
  { et_election_id = req "encrypted tally" "election_id" eid; et_contests = req "encrypted tally" "contests" cs }

let build_decryption ms : decryption =
  let id = ref None and t = ref None and bm = ref None and ev = ref None and pf = ref None in
  List.iter (function
    | `Selection_id v -> set "decryption" "selection_id" id v | `Tally v -> set "decryption" "tally" t v
    | `B_over_m v -> set "decryption" "b_over_m" bm v | `Encrypted_vote v -> set "decryption" "encrypted_vote" ev v
    | `Proof v -> set "decryption" "proof" pf v | `Skip -> ()) ms;
  { d_id = req "decryption" "selection_id" id; d_tally = req "decryption" "tally" t; d_b_over_m = req "decryption" "b_over_m" bm;
    d_encrypted_vote = req "decryption" "encrypted_vote" ev; d_proof = req "decryption" "proof" pf }

let build_dcontest ms : dcontest =
  let id = ref None and sels = ref None in
  List.iter (function `Contest_id v -> set "contest" "contest_id" id v | `Selections v -> set "contest" "selections" sels v | `Skip -> ()) ms;
  { dc_id = req "contest" "contest_id" id; dc_selections = req "contest" "selections" sels }

let build_decryptions ms : decryptions =
  let id = ref None and eid = ref None and cs = ref None in
  List.iter (function
    | `Id v -> set "decryptions" "id" id v | `Election_id v -> set "decryptions" "election_id" eid v
    | `Contests v -> set "decryptions" "contests" cs v | `Skip -> ()) ms;
  { dec_id = !id; dec_election_id = !eid; dec_contests = req "decryptions" "contests" cs }
