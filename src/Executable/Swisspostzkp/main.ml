(* Driver for the certified verifier of the Swiss Post zero-knowledge proofs
   (Examples/SwissPostZkpIns.v: verify_rows of Backend/BBSSharpVerifier.v at
   the 3072-bit group of BayerGrothIns.v) on files in the format of the
   crypto-primitives test vectors (src/test/resources/zeroknowledgeproofs/
   verify-(schnorr, exponentiation, plaintext-equality, decryption).json,
   specification 1.6.0, Section 10).

   Trusted: the decoding of the values (Base64 of Java BigInteger.toByteArray,
   checked: non-negative, elements in the subgroup of order q, exponents
   below q, the auxiliary strings valid UTF-8), the rows and targets of each
   proof's φ (see SwissPostZkpIns.v), and the RecursiveHash challenge
   (specification Algorithm 5.5; ByteArrayToInteger of SHA3-256, below q).
   The group must be that of the certified instance (p, q); the generator g
   of the context may be any element of G_q other than 1, as in the
   specification (the exponentiation proof does not use it).

   For every case: one line "index, certified verdict, recorded verdict,
   agree/DISAGREE, description"; a case whose values the boundary refuses
   is a rejection ("false (input: reason)"). Exit code 1 if any case
   disagrees with the recorded verdict.

   usage: main.exe KIND FILE, KIND one of schnorr, exponentiation,
          plaintext-equality, decryption *)
open SwissPostZkplib
open SwissPostZkplib.BayerGrothIns
open SwissPostZkplib.SwissPostZkpIns
module List = Stdlib.List
module String = Stdlib.String

let bi = Big_int_Z.big_int_of_int
let rec vector_of_list (xs : 'a list) : 'a VectorDef.t =
  match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t)

(* ---- bytes, integers, the boundary ---- *)

let z_of_bytes (s : string) : Z.t =
  String.fold_left (fun acc c -> Z.add (Z.shift_left acc 8) (Z.of_int (Char.code c))) Z.zero s

let bytes_of_z (z : Z.t) : string =
  if Z.sign z = 0 then "" else begin
    let n = (Z.numbits z + 7) / 8 in
    let s = Bytes.make n '\000' in
    let rec go z i = if i >= 0 && Z.sign z > 0 then begin
        Bytes.set s i (Char.chr (Z.to_int (Z.logand z (Z.of_int 255)))); go (Z.shift_right z 8) (i - 1) end in
    go z (n - 1); Bytes.to_string s end

exception Input of string
let fail fmt = Printf.ksprintf (fun s -> raise (Input s)) fmt

(* Java BigInteger.toByteArray of a non-negative integer *)
let z_of_b64 (s : string) : Z.t =
  let b = try Cryptokit.transform_string (Cryptokit.Base64.decode ()) s with _ -> fail "not Base64" in
  if b = "" then fail "empty integer";
  if Char.code b.[0] >= 0x80 then fail "negative integer";
  z_of_bytes b

let elem_z (x : Z.t) : coq_G =
  if not (Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one) then fail "element not in the group"; x
let scalar_z (x : Z.t) : coq_F =
  if Z.sign x < 0 || Z.geq x q then fail "exponent out of range"; x

(* ---- JSON ---- *)

let member (k : string) (j : Yojson.Safe.t) : Yojson.Safe.t =
  match j with
  | `Assoc kvs -> (match List.assoc_opt k kvs with Some v -> v | None -> fail "missing field %s" k)
  | _ -> fail "not an object (field %s)" k
let str (j : Yojson.Safe.t) = match j with `String s -> s | _ -> fail "not a string"
let arr (j : Yojson.Safe.t) = match j with `List l -> l | _ -> fail "not an array"
let elem j = elem_z (z_of_b64 (str j))
let scalar j = scalar_z (z_of_b64 (str j))
let elems j = List.map elem (arr j)
let scalars j = List.map scalar (arr j)
let aux_strings j =
  List.map (fun s -> let s = str s in if not (String.is_valid_utf_8 s) then fail "auxiliary string not UTF-8"; s) (arr j)

(* the recorded verdict: "true"/"false" or a boolean, under one of the
   names the four files use *)
let recorded (j : Yojson.Safe.t) : bool =
  let o = member "output" j in
  let v = List.find_map (fun k -> match o with `Assoc kvs -> List.assoc_opt k kvs | _ -> None)
      ["verif_result"; "output"; "result"] in
  match v with
  | Some (`Bool b) -> b
  | Some (`String "true") -> true
  | Some (`String "false") -> false
  | _ -> fail "no recorded verdict"

(* ---- RecursiveHash (specification Algorithm 5.5) ---- *)

let sha3_256 (s : string) : string = Cryptokit.hash_string (Cryptokit.Hash.sha3 256) s
type hashable = B of string | I of Z.t | S of string | L of hashable list
let rec rh (v : hashable) : string =
  match v with
  | B b -> sha3_256 ("\000" ^ b)
  | I z -> sha3_256 ("\001" ^ bytes_of_z z)
  | S s -> sha3_256 ("\002" ^ s)
  | L vs -> sha3_256 ("\003" ^ String.concat "" (List.map rh vs))
let () =
  assert (Z.format "%064x" (z_of_bytes (sha3_256 "")) =
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")

let il xs = L (List.map (fun x -> I x) xs)
(* h_aux = (tag, extra…, i_aux), i_aux omitted when empty *)
let haux tag extra aux = L ((S tag :: extra) @ (if aux = [] then [] else [L (List.map (fun s -> S s) aux)]))
(* e' = ByteArrayToInteger(RecursiveHash(f, y, c', h_aux)); 256 bits, below q *)
let challenge (f : hashable) (y : hashable) (c : hashable) (h : hashable) : coq_F =
  z_of_bytes (rh (L [f; y; c; h]))

let rec list_of_vector (v : 'a VectorDef.t) : 'a list =
  match v with VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

(* ---- the four proofs: rows B, targets y, responses z, the hash closure ---- *)

type statement = { k : int; rows : coq_G list list; ys : coq_G list; e : coq_F; zs : coq_F list;
                   hash : coq_G list -> coq_F }

let inv (x : coq_G) : coq_G = Z.invert x p
let mulg (x : coq_G) (y : coq_G) : coq_G = Z.rem (Z.mul x y) p
let fbase g = [I p; I q; I g]

(* Algorithm 10.3 *)
let schnorr g j =
  let i = member "input" j in
  let pr = member "proof" i in
  let y = elem (member "statement" i) and e = scalar (member "e" pr) and z = scalar (member "z" pr) in
  let aux = aux_strings (member "additional_information" i) in
  { k = 1; rows = [[g]]; ys = [y]; e; zs = [z];
    hash = (fun cs -> challenge (L (fbase g)) (I y) (I (List.hd cs)) (haux "SchnorrProof" [] aux)) }

(* Algorithm 10.9 *)
let exponentiation _ j =
  let i = member "input" j in
  let pr = member "proof" i in
  let gs = elems (member "bases" i) and ys = elems (member "statement" i) in
  let e = scalar (member "e" pr) and z = scalar (member "z" pr) in
  let aux = aux_strings (member "additional_information" i) in
  if gs = [] then fail "no bases";
  if List.length gs <> List.length ys then fail "|bases| <> |statement|";
  { k = 1; rows = List.map (fun g -> [g]) gs; ys; e; zs = [z];
    hash = (fun cs -> challenge (L [I p; I q; il gs]) (il ys) (il cs) (haux "ExponentiationProof" [] aux)) }

let ciphertext j = (elem (member "gamma" j), elems (member "phis" j))

(* Algorithm 10.12 *)
let plaintext_equality g j =
  let i = member "input" j in
  let pr = member "proof" i in
  let (c0, phis) = ciphertext (member "upper_c" i) and (c0', phis') = ciphertext (member "upper_c_prime" i) in
  let h = elem (member "h" i) and h' = elem (member "h_prime" i) in
  let e = scalar (member "e" pr) and zs = scalars (member "z" pr) in
  let aux = aux_strings (member "i_aux" i) in
  let c1, c1' = match phis, phis' with [a], [b] -> a, b | _ -> fail "ciphertexts must have one phi" in
  if List.length zs <> 2 then fail "|z| <> 2";
  let ys = [c0; c0'; mulg c1 (inv c1')] in
  { k = 2; rows = [[g; Z.one]; [Z.one; g]; [h; inv h']]; ys; e; zs;
    hash = (fun cs -> challenge (L (fbase g @ [I h; I h'])) (il ys) (il cs) (haux "PlaintextEqualityProof" [I c1; I c1'] aux)) }

(* Algorithm 10.6 *)
let decryption g j =
  let i = member "input" j in
  let pr = member "proof" i in
  let (gamma, phis) = ciphertext (member "ciphertext" i) in
  let pk = elems (member "public_key" i) and ms = elems (member "message" i) in
  let e = scalar (member "e" pr) and zs = scalars (member "z" pr) in
  let aux = aux_strings (member "additional_information" i) in
  let l = List.length phis in
  if l < 1 then fail "l < 1";
  if l > List.length pk then fail "l > k";
  if List.length ms <> l || List.length zs <> l then fail "|m|, |z| <> l";
  let unit_row b i = List.init l (fun j -> if j = i then b else Z.one) in
  let ys = List.filteri (fun j _ -> j < l) pk @ List.map2 (fun phi m -> mulg phi (inv m)) phis ms in
  { k = l; rows = List.init l (unit_row g) @ List.init l (unit_row gamma); ys; e; zs;
    hash = (fun cs -> challenge (L (fbase g @ [I gamma])) (il ys) (il cs) (haux "DecryptionProof" [il phis; il ms] aux)) }

let verify (s : statement) : bool =
  let m = List.length s.ys in
  verify_zkp_ins (bi s.k) (bi m) (fun cs -> s.hash (list_of_vector cs))
    (vector_of_list (List.map vector_of_list s.rows)) (vector_of_list s.ys) s.e (vector_of_list s.zs)

let () =
  if Array.length Sys.argv < 3 then (prerr_endline "usage: main.exe KIND FILE"; exit 2);
  let build = match Sys.argv.(1) with
    | "schnorr" -> schnorr | "exponentiation" -> exponentiation
    | "plaintext-equality" -> plaintext_equality | "decryption" -> decryption
    | k -> prerr_endline ("unknown kind " ^ k); exit 2 in
  let cases = arr (Yojson.Safe.from_file Sys.argv.(2)) in
  let bad = ref 0 in
  List.iteri (fun idx j ->
    let desc = match j with `Assoc kvs -> (match List.assoc_opt "description" kvs with Some (`String d) -> d | _ -> "") | _ -> "" in
    let expected = try recorded j with Input _ -> false in
    let verdict, note =
      try
        let c = member "context" j in
        if not (Z.equal (z_of_b64 (str (member "p" c))) p && Z.equal (z_of_b64 (str (member "q" c))) q)
        then fail "not the certified group";
        (* the generator: any element of G_q other than 1 (specification 10.2–10.5) *)
        let g = elem (member "g" c) in
        if Z.equal g Z.one then fail "generator 1";
        (verify (build g j), "")
      with Input msg -> (false, " (input: " ^ msg ^ ")") in
    let agree = verdict = expected in
    if not agree then incr bad;
    Printf.printf "%d\t%b\t%b\t%s\t%s%s\n%!" idx verdict expected (if agree then "agree" else "DISAGREE") desc note)
    cases;
  exit (if !bad = 0 then 0 else 1)
