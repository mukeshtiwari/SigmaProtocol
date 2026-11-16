(* The input language of the Bayer–Groth verifier: the six test-vector files
   of the Swiss Post crypto-primitives library (verify-*-argument.json,
   specification 1.6.0, Section 9), and the trusted boundary between them
   and the certified verifier.

   Trusted boundary. The certified verifier's types assume that every group
   element lies in the subgroup of order q of Z_p^* and that every exponent
   is below q. Every Base64 value of the fixtures is decoded here (Java
   BigInteger.toByteArray: big-endian, possibly with a leading zero byte)
   and checked before it becomes an element or an exponent; the parser
   refuses the document otherwise. The fixtures are written by a Java JSON
   library, so the grammar does not fix the order of the fields of an
   object: each object is a list of keyed members that the builders below
   assemble, requiring every field exactly once. *)

open BayerGrothlib
open BayerGrothlib.BayerGrothIns
module List = Stdlib.List
module String = Stdlib.String

type f = Zpstar.Zpfield.coq_Zp
type g = Zpstar.Schnorr.coq_Schnorr_group
type ct = g VectorDef.t

let bi = Big_int_Z.big_int_of_int
let rec vector_of_list (xs : 'a list) : 'a VectorDef.t =
  match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t)
let rec list_of_vector (v : 'a VectorDef.t) : 'a list =
  match v with VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

(* ---- the group, from the certified instantiation ---- *)

let p : Z.t = BayerGrothIns.p
let q : Z.t = BayerGrothIns.q

let in_group (x : Z.t) = Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one
let elem (x : Z.t) : g =
  if not (in_group x) then failwith "element not in the group"; x
let scalar (x : Z.t) : f =
  if Z.sign x < 0 || Z.geq x q then failwith "exponent out of range"; of_Z x

(* ---- bytes and integers ---- *)

let z_of_bytes (s : string) : Z.t =
  String.fold_left (fun acc c -> Z.add (Z.shift_left acc 8) (Z.of_int (Char.code c))) Z.zero s

let base64 (s : string) : string =
  try Cryptokit.transform_string (Cryptokit.Base64.decode ()) s
  with _ -> failwith ("not Base64: " ^ s)
(* Java BigInteger.toByteArray of a non-negative integer: big-endian two's
   complement, so a leading 0x00 when the top bit is set; a first byte with
   the top bit set is a negative number, which the Swiss Post parser
   rejects as an element or exponent (found by bench/swisspost-diff) *)
let z_of_b64 (s : string) : Z.t =
  let b = base64 s in
  if b = "" then failwith "empty integer";
  if Char.code b.[0] >= 0x80 then failwith "negative integer";
  z_of_bytes b
let elem_of_b64 (s : string) : g = elem (z_of_b64 s)
let scalar_of_b64 (s : string) : f = scalar (z_of_b64 s)

(* ---- the documents ---- *)

(* the context (p, q, pk, ck): the group parameters as read, checked by the driver *)
type ctx = { c_p : Z.t; c_q : Z.t; c_g : Z.t; pk : g list; h : g; gs : g list }
(* the fixture's verdict and, when recorded, its challenges *)
type output = { result : bool; out_x : Z.t option; out_y : Z.t option; out_z : Z.t option }
type 'a case = { description : string; context : ctx; input : 'a; output : output }

type shuffle_stmt = { ciphertexts : ct list; shuffled : ct list }
type product_stmt = { p_ca : g list; p_b : f }
type hadamard_stmt = { h_ca : g list; h_cb : g }
type zero_stmt = { z_ca : g list; z_cb : g list; z_y : f }
type svp_stmt = { s_ca : g; s_b : f }
type mexp_stmt = { m_rows : ct list list; m_product : ct; m_ca : g list }

(* ---- builders: every field exactly once ---- *)

let set (what : string) (name : string) (r : 'a option ref) (v : 'a) : unit =
  match !r with Some _ -> failwith (what ^ ": duplicate field " ^ name) | None -> r := Some v
let req (what : string) (name : string) (r : 'a option ref) : 'a =
  match !r with Some v -> v | None -> failwith (what ^ ": missing field " ^ name)

let build_ct ms : ct =
  let gamma = ref None and phis = ref None in
  List.iter (function `Gamma v -> set "ciphertext" "gamma" gamma v | `Phis v -> set "ciphertext" "phis" phis v) ms;
  vector_of_list (req "ciphertext" "gamma" gamma :: req "ciphertext" "phis" phis)

let build_ck ms : g * g list =
  let h = ref None and gs = ref None in
  List.iter (function `H v -> set "ck" "h" h v | `Gs v -> set "ck" "g" gs v) ms;
  (req "ck" "h" h, req "ck" "g" gs)

let build_ctx ms : ctx =
  let p = ref None and q = ref None and g = ref None and pk = ref None and ck = ref None in
  List.iter (function
    | `P v -> set "context" "p" p v | `Q v -> set "context" "q" q v | `G v -> set "context" "g" g v
    | `Pk v -> set "context" "pk" pk v | `Ck v -> set "context" "ck" ck v) ms;
  let (h, gs) = req "context" "ck" ck in
  { c_p = req "context" "p" p; c_q = req "context" "q" q; c_g = req "context" "g" g; pk = req "context" "pk" pk; h; gs }

let build_output ms : output =
  let result = ref None and x = ref None and y = ref None and z = ref None in
  List.iter (function
    | `Result v -> set "output" "result" result v | `X v -> set "output" "x" x v
    | `Y v -> set "output" "y" y v | `Z v -> set "output" "z" z v) ms;
  { result = req "output" "result" result; out_x = !x; out_y = !y; out_z = !z }

let build_case ms : 'a case =
  let d = ref None and c = ref None and i = ref None and o = ref None in
  List.iter (function
    | `Description v -> set "case" "description" d v | `Context v -> set "case" "context" c v
    | `Input v -> set "case" "input" i v | `Output v -> set "case" "output" o v) ms;
  { description = req "case" "description" d; context = req "case" "context" c;
    input = req "case" "input" i; output = req "case" "output" o }

let build_input ms : 'a * 'b =
  let s = ref None and a = ref None in
  List.iter (function `Statement v -> set "input" "statement" s v | `Argument v -> set "input" "argument" a v) ms;
  (req "input" "statement" s, req "input" "argument" a)

let build_shuffle_stmt ms : shuffle_stmt =
  let cs = ref None and cs' = ref None in
  List.iter (function `Ciphertexts v -> set "statement" "ciphertexts" cs v | `Shuffled v -> set "statement" "shuffled_ciphertexts" cs' v) ms;
  { ciphertexts = req "statement" "ciphertexts" cs; shuffled = req "statement" "shuffled_ciphertexts" cs' }
let build_product_stmt ms : product_stmt =
  let ca = ref None and b = ref None in
  List.iter (function `Ca v -> set "statement" "c_a" ca v | `B v -> set "statement" "b" b v) ms;
  { p_ca = req "statement" "c_a" ca; p_b = req "statement" "b" b }
let build_hadamard_stmt ms : hadamard_stmt =
  let ca = ref None and cb = ref None in
  List.iter (function `Ca v -> set "statement" "c_a" ca v | `Cb v -> set "statement" "c_b" cb v) ms;
  { h_ca = req "statement" "c_a" ca; h_cb = req "statement" "c_b" cb }
let build_zero_stmt ms : zero_stmt =
  let ca = ref None and cb = ref None and y = ref None in
  List.iter (function `Ca v -> set "statement" "c_a" ca v | `Cb v -> set "statement" "c_b" cb v | `Y v -> set "statement" "y" y v) ms;
  { z_ca = req "statement" "c_a" ca; z_cb = req "statement" "c_b" cb; z_y = req "statement" "y" y }
let build_svp_stmt ms : svp_stmt =
  let ca = ref None and b = ref None in
  List.iter (function `Ca v -> set "statement" "c_a" ca v | `B v -> set "statement" "b" b v) ms;
  { s_ca = req "statement" "c_a" ca; s_b = req "statement" "b" b }
let build_mexp_stmt ms : mexp_stmt =
  let rows = ref None and prod = ref None and ca = ref None in
  List.iter (function
    | `Ciphertexts v -> set "statement" "ciphertexts" rows v | `Product v -> set "statement" "ciphertext_product" prod v
    | `Ca v -> set "statement" "c_a" ca v) ms;
  { m_rows = req "statement" "ciphertexts" rows; m_product = req "statement" "ciphertext_product" prod; m_ca = req "statement" "c_a" ca }

(* the arguments, as the certified records *)
let build_svp ms : svp_argument =
  let cd = ref None and cdel = ref None and cDel = ref None and a = ref None and b = ref None and r = ref None and s = ref None in
  List.iter (function
    | `Cd v -> set "svp" "c_d" cd v | `Cdelta v -> set "svp" "c_lower_delta" cdel v | `CDelta v -> set "svp" "c_upper_delta" cDel v
    | `Atilde v -> set "svp" "a_tilde" a v | `Btilde v -> set "svp" "b_tilde" b v
    | `Rtilde v -> set "svp" "r_tilde" r v | `Stilde v -> set "svp" "s_tilde" s v) ms;
  mk_svp (req "svp" "c_d" cd) (req "svp" "c_lower_delta" cdel) (req "svp" "c_upper_delta" cDel)
    (req "svp" "a_tilde" a) (req "svp" "b_tilde" b) (req "svp" "r_tilde" r) (req "svp" "s_tilde" s)

let build_zero ms : zero_argument =
  let ca0 = ref None and cbm = ref None and cd = ref None and a = ref None and b = ref None
  and r = ref None and s = ref None and t = ref None in
  List.iter (function
    | `Ca0 v -> set "zero" "c_a0" ca0 v | `Cbm v -> set "zero" "c_bm" cbm v | `Cds v -> set "zero" "c_d" cd v
    | `A v -> set "zero" "a" a v | `B v -> set "zero" "b" b v
    | `R v -> set "zero" "r" r v | `S v -> set "zero" "s" s v | `T v -> set "zero" "t" t v) ms;
  mk_zero (req "zero" "c_a0" ca0) (req "zero" "c_bm" cbm) (req "zero" "c_d" cd)
    (req "zero" "a" a) (req "zero" "b" b) (req "zero" "r" r) (req "zero" "s" s) (req "zero" "t" t)

let build_hadamard ms : hadamard_argument =
  let cB = ref None and za = ref None in
  List.iter (function `CB v -> set "hadamard" "cUpperB" cB v | `Zero v -> set "hadamard" "zero_argument" za v) ms;
  mk_had (req "hadamard" "cUpperB" cB) (req "hadamard" "zero_argument" za)

(* the multi-exponentiation and shuffle arguments carry the number l of message
   components of the ciphertexts, which the context gives (|pk|); they are read
   into these records and converted once l is known *)
type mexp_arg = { me_ca0 : g; me_cb : g list; me_e : ct list; me_a : f list; me_r : f; me_b : f; me_s : f; me_tau : f }
type shuffle_arg = { sh_ca : g list; sh_cb : g list; sh_prod : product_argument; sh_mexp : mexp_arg }

let build_mexp ms : mexp_arg =
  let ca0 = ref None and cb = ref None and e = ref None and a = ref None and r = ref None
  and b = ref None and s = ref None and tau = ref None in
  List.iter (function
    | `Ca0 v -> set "multiexp" "c_a_0" ca0 v | `Cbs v -> set "multiexp" "c_b" cb v | `E v -> set "multiexp" "e" e v
    | `A v -> set "multiexp" "a" a v | `R v -> set "multiexp" "r" r v | `B v -> set "multiexp" "b" b v
    | `S v -> set "multiexp" "s" s v | `Tau v -> set "multiexp" "tau" tau v) ms;
  { me_ca0 = req "multiexp" "c_a_0" ca0; me_cb = req "multiexp" "c_b" cb; me_e = req "multiexp" "e" e;
    me_a = req "multiexp" "a" a; me_r = req "multiexp" "r" r; me_b = req "multiexp" "b" b;
    me_s = req "multiexp" "s" s; me_tau = req "multiexp" "tau" tau }

let to_mexp (l : int) (m : mexp_arg) : multiexp_argument =
  mk_mexp (bi l) m.me_ca0 m.me_cb m.me_e m.me_a m.me_r m.me_b m.me_s m.me_tau

(* the constants take the (erased) primality hypotheses as a dummy argument *)
let gone : g = coq_Gone

(* for m = 1 the product argument has no c_b and no Hadamard argument *)
let build_product ms : product_argument =
  let cb = ref None and had = ref None and svp = ref None in
  List.iter (function
    | `Cb v -> set "product" "c_b" cb v | `Hadamard v -> set "product" "hadamard_argument" had v
    | `Svp v -> set "product" "single_vpa" svp v) ms;
  mk_prod (match !cb with Some v -> v | None -> gone) !had (req "product" "single_vpa" svp)

let build_shuffle ms : shuffle_arg =
  let ca = ref None and cb = ref None and prod = ref None and mexp = ref None in
  List.iter (function
    | `Ca v -> set "shuffle" "ca" ca v | `Cb v -> set "shuffle" "cb" cb v
    | `Product v -> set "shuffle" "product_argument" prod v | `Mexp v -> set "shuffle" "multi_exp_argument" mexp v) ms;
  { sh_ca = req "shuffle" "ca" ca; sh_cb = req "shuffle" "cb" cb;
    sh_prod = req "shuffle" "product_argument" prod; sh_mexp = req "shuffle" "multi_exp_argument" mexp }

let to_shuffle (l : int) (s : shuffle_arg) : shuffle_argument =
  mk_shuffle (bi l) s.sh_ca s.sh_cb s.sh_prod (to_mexp l s.sh_mexp)
