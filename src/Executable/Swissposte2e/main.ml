(* Driver for the certified verifiers of the Swiss Post tally
   (Examples/BayerGrothE2EIns.v and SwissPostZkpE2EIns.v, at the encryption
   group of the election event, whose primality is assumed) on the
   statements of an election event: every shuffle (Bayer–Groth argument,
   crypto-primitives Algorithm 9.12) and every decryption proof (Algorithm
   10.6) of every ballot box, as wired by
   bench/swisspost-e2e/certified/e2e_extract.py, which also records the
   protocol's checks that involve no proof; they are reported here too.

   Trusted: the input boundary (every group element is checked to lie in
   the subgroup of order q, every exponent to be below q), the RecursiveHash
   challenges (the same closures as Executable/Bgverifier and
   Executable/Swisspostzkp) and the matrix of the decryption proofs.

   usage: main.exe STATEMENTS.json   (exit status 0 iff everything verifies) *)
open SwissPostE2Elib
open SwissPostE2Elib.BayerGrothE2EIns
open SwissPostE2Elib.SwissPostZkpE2EIns
module List = Stdlib.List
module String = Stdlib.String

exception Input of string
let fail fmt = Printf.ksprintf (fun s -> raise (Input s)) fmt

let bi = Big_int_Z.big_int_of_int
let rec vector_of_list (xs : 'a list) : 'a VectorDef.t =
  match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t)
let rec list_of_vector (v : 'a VectorDef.t) : 'a list =
  match v with VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

(* ---- the boundary: integers are IntegerToByteArray, unsigned big-endian ---- *)

let z_of_bytes (s : string) : Z.t =
  String.fold_left (fun acc c -> Z.add (Z.shift_left acc 8) (Z.of_int (Char.code c))) Z.zero s
let bytes_of_z (z : Z.t) : string =
  if Z.sign z = 0 then "" else begin
    let n = (Z.numbits z + 7) / 8 in
    let s = Bytes.make n '\000' in
    let rec go z i = if i >= 0 && Z.sign z > 0 then begin
        Bytes.set s i (Char.chr (Z.to_int (Z.logand z (Z.of_int 255)))); go (Z.shift_right z 8) (i - 1) end in
    go z (n - 1); Bytes.to_string s end
let z_of_b64 (s : string) : Z.t =
  try z_of_bytes (Cryptokit.transform_string (Cryptokit.Base64.decode ()) s) with _ -> fail "not Base64: %s" s

let elem_z (x : Z.t) : coq_G =
  if Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one then x else fail "element not in G_q"
let scalar_z (x : Z.t) : coq_F = if Z.sign x >= 0 && Z.lt x q then of_Z x else fail "exponent out of range"

let member k (j : Yojson.Safe.t) = match j with
  | `Assoc kvs -> (match List.assoc_opt k kvs with Some v -> v | None -> fail "missing field %s" k)
  | _ -> fail "not an object (field %s)" k
let str = function `String s -> s | _ -> fail "not a string"
let arr = function `List l -> l | _ -> fail "not an array"
let elem j = elem_z (z_of_b64 (str j))
let scalar j = scalar_z (z_of_b64 (str j))
let elems j = List.map elem (arr j)
let scalars j = List.map scalar (arr j)
let ct j : coq_G VectorDef.t = vector_of_list (elem (member "gamma" j) :: elems (member "phis" j))

(* ---- RecursiveHash (crypto-primitives Algorithm 5.5) ---- *)

let sha3_256 (s : string) : string = Cryptokit.hash_string (Cryptokit.Hash.sha3 256) s
type hashable = I of Z.t | S of string | L of hashable list
let rec rh (v : hashable) : string =
  match v with
  | I z -> sha3_256 ("\001" ^ bytes_of_z z)
  | S s -> sha3_256 ("\002" ^ s)
  | L vs -> sha3_256 ("\003" ^ String.concat "" (List.map rh vs))
let () =
  assert (Z.format "%064x" (z_of_bytes (sha3_256 "")) =
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")
let fz (b : string) : coq_F = of_Z (z_of_bytes b)   (* 256 bits, below the 3071-bit q *)

(* ---- shuffles: the oracles of Executable/Bgverifier, over (p, q, pk, ck) ---- *)

let he (x : coq_G) = I (elem_to_Z x)
let hf (x : coq_F) = I (to_Z x)
let hl xs = L (List.map he xs)
let hct (c : coq_G VectorDef.t) = hl (list_of_vector c)
let hcl cs = L (List.map hct cs)
let hmat rows = L (List.map hcl rows)

let shuffle_oracles pk h gs l cs cs' =
  let base = [I p; I q; hl pk; L (he h :: List.map he gs)] in
  let challenge vs = fz (rh (L vs)) in
  let stmt = [hcl cs; hcl cs'] in
  mk_oracles (bi l)
    (fun cA -> challenge (base @ stmt @ [hl cA]))
    (fun cA cB -> challenge (hl cB :: base @ stmt @ [hl cA]))
    (fun cA cB -> challenge (S "1" :: hl cB :: base @ stmt @ [hl cA]))
    (fun cA cb cB -> challenge (base @ [hl cA; he cb; hl cB]))
    (fun cA cb cB -> challenge (S "1" :: base @ [hl cA; he cb; hl cB]))
    (fun cA0 cBm cd cB cA -> challenge (base @ [he cA0; he cBm; hl cd; hl cB; hl cA]))
    (fun cDelta cdelta cd b ca -> challenge (base @ [he cDelta; he cdelta; he cd; hf b; he ca]))
    (fun rows cc cA cA0 cB e -> challenge (base @ [hmat rows; hct cc; hl cA; he cA0; hl cB; hcl e]))

(* the argument in the payload format; m = 1, so the product argument is a
   single value product argument (no c_b, no Hadamard argument) *)
let shuffle_argument l (a : Yojson.Safe.t) =
  let pa = member "productArgument" a and me = member "multiExponentiationArgument" a in
  (match pa with `Assoc kvs when List.mem_assoc "hadamardArgument" kvs || List.mem_assoc "c_b" kvs -> fail "m > 1" | _ -> ());
  let s = member "singleValueProductArgument" pa in
  let svp = mk_svp (elem (member "c_d" s)) (elem (member "c_delta" s)) (elem (member "c_Delta" s))
      (scalars (member "a_tilde" s)) (scalars (member "b_tilde" s)) (scalar (member "r_tilde" s)) (scalar (member "s_tilde" s)) in
  let mexp = mk_mexp (bi l) (elem (member "c_A_0" me)) (elems (member "c_B" me)) (List.map ct (arr (member "E" me)))
      (scalars (member "a" me)) (scalar (member "r" me)) (scalar (member "b" me)) (scalar (member "s" me)) (scalar (member "tau" me)) in
  (elems (member "c_A" a), mk_shuffle (bi l) (elems (member "c_A" a)) (elems (member "c_B" a)) (mk_prod coq_Gone None svp) mexp)

let verify_shuffle (j : Yojson.Safe.t) : bool =
  let pk = elems (member "pk" j) and h = elem (member "h" j) and gs = elems (member "gs" j) in
  let cs = List.map ct (arr (member "C" j)) and cs' = List.map ct (arr (member "Cp" j)) in
  let len v = List.length (list_of_vector v) in
  let nn = List.length cs in
  let l = match cs with c :: _ -> len c - 1 | [] -> fail "no ciphertexts" in
  if l < 1 || l > List.length pk then fail "ciphertext size not in [1, k]";
  if List.length cs' <> nn || List.exists (fun c -> len c <> l + 1) (cs @ cs') then fail "statement shapes";
  let cA, arg = shuffle_argument l (member "argument" j) in
  if List.length cA <> 1 then fail "m <> 1";
  if List.exists (fun c -> len c <> l + 1) arg.BayerGroth.sh_mexp.BayerGroth.me_E then fail "E shapes";
  if List.length gs <> nn then fail "|ck| <> N";
  (* pk is hashed whole; its first l elements encrypt *)
  let pkl = List.filteri (fun i _ -> i < l) pk in
  shuffle_verify_fs_ins (bi l) (shuffle_oracles pk h gs l cs cs') h gs (elem_z (Z.of_int 2)) (vector_of_list pkl) (bi 1) (bi nn) cs cs' arg

(* ---- decryption proofs (Algorithm 10.6), as Executable/Swisspostzkp ---- *)

let inv (x : coq_G) : coq_G = Z.invert x p
let mulg (x : coq_G) (y : coq_G) : coq_G = Z.rem (Z.mul x y) p
let il xs = L (List.map (fun x -> I x) xs)
let haux tag extra aux = L ((S tag :: extra) @ (if aux = [] then [] else [L (List.map (fun s -> S s) aux)]))

let verify_decryption (j : Yojson.Safe.t) : bool =
  let g = elem (member "g" j) in
  let c = member "ciphertext" j in
  let gamma = elem (member "gamma" c) and phis = elems (member "phis" c) in
  let pk = elems (member "pk" j) and ms = elems (member "message" j) in
  let pr = member "proof" j in
  let e = scalar (member "e" pr) and zs = scalars (member "z" pr) in
  let aux = List.map str (arr (member "aux" j)) in
  let l = List.length phis in
  if l < 1 || l > List.length pk then fail "l not in [1, k]";
  if List.length ms <> l || List.length zs <> l then fail "|m|, |z| <> l";
  let unit_row b i = List.init l (fun j -> if j = i then b else Z.one) in
  let ys = List.filteri (fun j _ -> j < l) pk @ List.map2 (fun phi m -> mulg phi (inv m)) phis ms in
  let hash cs = fz (rh (L [L [I p; I q; I g; I gamma]; il ys; il cs; haux "DecryptionProof" [il phis; il ms] aux])) in
  let rows = List.init l (unit_row g) @ List.init l (unit_row gamma) in
  verify_zkp_ins (bi l) (bi (List.length ys)) (fun cs -> hash (list_of_vector cs))
    (vector_of_list (List.map vector_of_list rows)) (vector_of_list ys) e (vector_of_list zs)

let () =
  if Array.length Sys.argv < 2 then (prerr_endline "usage: main.exe STATEMENTS.json"; exit 2);
  let doc = Yojson.Safe.from_file Sys.argv.(1) in
  let ok = ref true in
  (try
     if not (Z.equal (z_of_b64 (str (member "p" doc))) p && Z.equal (z_of_b64 (str (member "q" doc))) q) then
       fail "not the group of this instance"
   with Input m -> Printf.printf "group\tfalse\t%s\n" m; exit 1);
  List.iter (fun c ->
    let good = member "ok" c = `Bool true in
    if not good then ok := false;
    Printf.printf "check\t%b\t%s\n%!" good (str (member "name" c))) (arr (member "checks" doc));
  List.iter (fun s ->
    let kind = str (member "kind" s) and desc = str (member "desc" s) in
    let t0 = Unix.gettimeofday () in
    let verdict, note =
      try ((match kind with "shuffle" -> verify_shuffle s | "decryption" -> verify_decryption s | k -> fail "kind %s" k), "")
      with Input m -> (false, " (input: " ^ m ^ ")") in
    if not verdict then ok := false;
    Printf.printf "%s\t%b\t%s%s\t%.0f ms\n%!" kind verdict desc note ((Unix.gettimeofday () -. t0) *. 1000.))
    (arr (member "statements" doc));
  Printf.printf "overall\t%b\n" !ok;
  exit (if !ok then 0 else 1)
