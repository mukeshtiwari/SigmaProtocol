(* The input language of the Belenios verifier: the JSON documents of a
   Belenios 3.x public-data archive (events, setup, election, trustees,
   credentials, ballots, encrypted tally, partial decryptions, result), as
   Belenios 3.2 serialises them, and the trusted boundary between them and
   the certified verifier.

   Trusted boundary. The certified verifier's types assume that every group
   element is a point of the order-l subgroup of Ed25519 and that every
   field element is below l. The parser decodes every compressed point,
   checks that it lies on the curve, is canonically encoded and has order l
   (Belenios's own [check]), and checks the range of every scalar; it
   refuses the document otherwise. Points keep the hexadecimal string
   Belenios hashes next to the decoded coordinates. *)

open Belenioslib
open Belenioslib.Ed25519Ins
(* the extracted library defines modules named List and Nat *)
module List = Stdlib.List
module String = Stdlib.String

type point = Ed25519.Ed25519.Ed.coq_G
type scalar = Ed25519.Ed25519.Zl.coq_F
type proof = scalar BeleniosTally.proof

(* a validated point with its compressed encoding *)
type hex_point = { pt : point; hex : string }
type ciphertext = { alpha : hex_point; beta : hex_point }

type event = { ev_height : int; ev_parent : string option; ev_type : string; ev_payload : string option }
type setup = { s_election : string; s_trustees : string; s_credentials : string }
type question = { q_answers : int; q_blank : bool; q_min : int; q_max : int; q_text : string }
type election = {
  e_version : int; e_description : string; e_name : string; e_group : string;
  e_public_key : hex_point; e_questions : question list; e_uuid : string }
type trustee = { t_public_key : hex_point; t_pok : proof }
type credential = { c_point : hex_point; c_weight : scalar }
type answer = { a_choices : ciphertext list; a_individual : proof list list; a_overall : proof list; a_blank : proof list option }
type ballot = {
  b_uuid : string; b_hash : string; b_credential : hex_point; b_answers : answer list;
  b_sig_hash : string; b_sig_proof : proof;
  b_sig_pos : int  (* byte offset of the "signature" field, which the signed text excludes *) }
type tally_header = { th_num_tallied : int; th_total_weight : string; th_encrypted_tally : string }
type pd_header = { pd_owner : int; pd_payload : string }
type partial_decryption = { pd_factors : point list list; pd_proofs : proof list list }
type result = scalar list list

(* ---- Ed25519 constants (RFC 8032) ---- *)

let bis = Big_int_Z.big_int_of_string
let p = Z.sub (Z.shift_left Z.one 255) (Z.of_int 19)
let l = bis "7237005577332262213973186563042994240857116359379907606001950938285454250989"
let d = Z.erem (Z.mul (Z.neg (Z.of_int 121665)) (Z.invert (Z.of_int 121666) p)) p
let a = Z.sub p Z.one
let mask255 = Z.sub (Z.shift_left Z.one 255) Z.one

let modsqrt (x2 : Z.t) : Z.t =
  (* p = 5 mod 8: sqrt(x) = x·v·(i − 1) with v = (2x)^((p−5)/8), i = 2x·v² *)
  let e = Z.div (Z.sub p (Z.of_int 5)) (Z.of_int 8) in
  let v = Z.powm (Z.shift_left x2 1) e p in
  let i = Z.erem (Z.shift_left (Z.mul (Z.mul x2 v) v) 1) p in
  Z.erem (Z.mul (Z.mul x2 v) (Z.sub i Z.one)) p

let on_curve (x, y) =
  let x2 = Z.erem (Z.mul x x) p and y2 = Z.erem (Z.mul y y) p in
  Z.equal (Z.erem (Z.add (Z.mul a x2) y2) p)
          (Z.erem (Z.add Z.one (Z.mul (Z.mul d x2) y2)) p)

(* compressed form: y with the low bit of x in bit 255, as 64 hex digits *)
let compress ((x, y) : Z.t * Z.t) : string =
  let z = Z.logor y (Z.shift_left (Z.logand x Z.one) 255) in
  let s = Z.format "%x" z in
  String.make (64 - String.length s) '0' ^ s

let uncompress (hex : string) : (Z.t * Z.t) option =
  if String.length hex <> 64 then None else
  match Z.of_string_base 16 hex with
  | exception Invalid_argument _ -> None
  | z ->
    let y = Z.logand z mask255 in
    if Z.geq y p then None else
    let sign = Z.shift_right z 255 in
    let y2 = Z.erem (Z.mul y y) p in
    let x2 = Z.erem (Z.mul (Z.sub y2 Z.one) (Z.invert (Z.add (Z.mul d y2) Z.one) p)) p in
    let x = modsqrt x2 in
    if not (Z.equal (Z.erem (Z.mul x x) p) x2) then None else
    let x = if Z.equal (Z.logand x Z.one) sign then x else Z.sub p x in
    Some (x, y)

(* ---- the trusted boundary ---- *)

(* A point of the order-l subgroup, as the certified code represents it:
   the pair of coordinates (the proof components are erased). The checks
   are those of Belenios's [check]: on the curve, canonical encoding, and
   l·P = 0 (computed with the certified fast scalar multiplication). *)
let identity : Z.t * Z.t = (Z.zero, Z.one)

let point_of_hex (s : string) : hex_point =
  match uncompress s with
  | None -> failwith ("not a point: " ^ s)
  | Some pt ->
    if not (on_curve pt) then failwith ("not on the curve: " ^ s);
    if compress pt <> s then failwith ("non-canonical point encoding: " ^ s);
    let lp = Ed25519.Ed25519.Ed.fast_smul l pt in
    if lp <> identity then failwith ("point not of order l: " ^ s);
    { pt; hex = s }

let hex_of_point (pt : point) : string = compress (point_to_Z pt)

let scalar_of_string (s : string) : scalar =
  let z = match bis s with z -> z | exception _ -> failwith ("not a scalar: " ^ s) in
  if Z.sign z < 0 || Z.geq z l then failwith ("scalar out of range: " ^ s);
  of_Z z

(* a credential line: the public key, optionally followed by its weight *)
let credential_of_string (s : string) : credential =
  match String.split_on_char ',' s with
  | [pk] -> { c_point = point_of_hex pk; c_weight = of_Z Z.one }
  | [pk; w] -> { c_point = point_of_hex pk; c_weight = scalar_of_string w }
  | _ -> failwith ("credential: " ^ s)

(* the strings Belenios hashes: a ciphertext as "alpha,beta" *)
let ciphertext_string (c : ciphertext) : string = c.alpha.hex ^ "," ^ c.beta.hex
let ciphertext_points (c : ciphertext) : point * point = (c.alpha.pt, c.beta.pt)
