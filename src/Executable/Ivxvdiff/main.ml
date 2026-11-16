(* Certified side of the IVXV differential campaign (bench/ivxv-diff), at the
   safe-prime group of Examples/IvxvGroupIns.v (primality assumed).

   main.exe shuffle protInfo.xml PROOF_DIRECTORY
     A Verificatum 3.1.0 shuffling session (the session type IVXV's auditor
     verifies), key width κ ≥ 1, ciphertext width 1, ModPGroup. Every proof
     of a shuffle is checked by the certified verifier verify_pos_ins of
     Examples/VerificatumIvxvIns.v, which is stated for key width 1. For key
     width κ the ciphertexts are in (G^κ)², the key is (g^κ, (y_1..y_κ)) and
     the reply k_F is in Z_q^κ: the equations A, B, C, D and the reply k_E do
     not depend on the key width, and the equation F in (G^κ)² holds iff it
     holds in every component j with the key (g, y_j), the announcement F'_j
     and the reply k_F,j. The driver therefore runs the certified verifier
     once per component, with the batching vector e and the challenge v
     computed once from the whole session (Verificatum's random oracles over
     the byte trees of the session). This reduction, the chaining of the
     lists of the mix-servers (L_0 = Ciphertexts.bt, L_l = CiphertextsXX.bt,
     L_λ = ShuffledCiphertexts.bt) and the parser are trusted.
     Exit status 0 iff verified.

   main.exe dec CASES.json
     IVXV decryption proofs (ElGamalDecryptionProof, announcement form
     (a, b, s)) checked by the certified Maurer verifier verify_zkp_ins of
     Examples/SwissPostZkpIvxvIns.v; the challenge is IVXV's (a DPRNG seeded
     with the DER encoding of the statement and the announcement), computed
     here from the prefix that bench/ivxv-diff/ivxvlib.py encodes.

   main.exe nizkp CASES.json
     IVXV Go core decryption-share proofs (compact form (e, s)), the same
     verifier; the challenge is SHAKE-256 over a DER prefix (ivxvlib.py)
     completed with the reconstructed commitments. *)

open Ivxvlib
module List = Stdlib.List
module String = Stdlib.String

let bi = Big_int_Z.big_int_of_int
let rec vector_of_list = function
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t)
let rec list_of_vector = function VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t

let p : Z.t = IvxvGroupIns.p
let q : Z.t = IvxvGroupIns.q
let in_group (x : Z.t) = Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one

(* ================================================================== *)
(* shuffles                                                           *)
(* ================================================================== *)

module Shuffle = struct
  open VerificatumIvxvIns
  let elem (x : Z.t) = if not (in_group x) then failwith "element not in the group"; x
  let scalar (x : Z.t) = if Z.sign x < 0 || Z.geq x q then failwith "scalar out of range"; of_Z x

  type bt = Leaf of string | Node of bt list
  let rec encode = function
    | Leaf d -> let b = Bytes.create 5 in Bytes.set b 0 '\001'; Bytes.set_int32_be b 1 (Int32.of_int (String.length d)); Bytes.to_string b ^ d
    | Node cs -> let b = Bytes.create 5 in Bytes.set b 0 '\000'; Bytes.set_int32_be b 1 (Int32.of_int (List.length cs));
      Bytes.to_string b ^ String.concat "" (List.map encode cs)
  let decode (s : string) : bt =
    let rec go pos =
      if pos + 5 > String.length s then failwith "byte tree: truncated";
      let tag = Char.code s.[pos] in
      let n = Int32.to_int (String.get_int32_be s (pos + 1)) in
      if n < 0 then failwith "byte tree: length";
      let pos = pos + 5 in
      if tag = 1 then (if pos + n > String.length s then failwith "byte tree: truncated"; (Leaf (String.sub s pos n), pos + n))
      else if tag = 0 then begin
        let rec children k pos acc = if k = 0 then (List.rev acc, pos) else
          let (c, pos') = go pos in children (k - 1) pos' (c :: acc) in
        let (cs, pos') = children n pos [] in (Node cs, pos')
      end else failwith "byte tree: tag" in
    let (t, pos) = go 0 in
    if pos <> String.length s then failwith "byte tree: trailing data"; t
  let read_file path = let ic = open_in_bin path in let s = really_input_string ic (in_channel_length ic) in close_in ic; s
  let read_bt path = decode (read_file path)
  let read_ascii path = String.trim (read_file path)
  let int_of_leaf = function
    | Leaf d ->
      let z = Z.of_bits (String.init (String.length d) (fun i -> d.[String.length d - 1 - i])) in
      if String.length d > 0 && Char.code d.[0] >= 128 then Z.sub z (Z.shift_left Z.one (8 * String.length d)) else z
    | Node _ -> failwith "byte tree: expected a leaf"
  let leaf_of_int k n =
    if Z.sign n < 0 then failwith "negative";
    let bits = Z.to_bits n in
    let get i = if i < String.length bits then bits.[i] else '\000' in
    if Z.numbits n > 8 * k - 1 then failwith "too large";
    Leaf (String.init k (fun i -> get (k - 1 - i)))
  let width_of m = let k = ref 1 in while Z.geq m (Z.shift_left Z.one (8 * !k - 1)) do incr k done; !k
  let kp = width_of p
  let leaf_p = leaf_of_int kp
  let leaf_int4 n = leaf_of_int 4 (Z.of_int n)
  let children = function Node cs -> cs | Leaf _ -> failwith "byte tree: expected a node"

  (* hash, PRG, random oracles (VMN manual, section 5) *)
  let hash_name = ref "SHA-256" and prg_name = ref "SHA-256"
  let mk = function "SHA-256" -> Cryptokit.Hash.sha256 () | "SHA-384" -> Cryptokit.Hash.sha384 ()
                  | "SHA-512" -> Cryptokit.Hash.sha512 () | s -> failwith ("hash " ^ s)
  let hash s = let h = mk !hash_name in h#add_string s; h#result
  let prg_hash s = let h = mk !prg_name in h#add_string s; h#result
  let encode_int4 n = let b = Bytes.create 4 in Bytes.set_int32_be b 0 (Int32.of_int n); Bytes.to_string b
  let prg seed nbytes =
    let buf = Buffer.create nbytes in let i = ref 0 in
    while Buffer.length buf < nbytes do Buffer.add_string buf (prg_hash (seed ^ encode_int4 !i)); incr i done;
    Buffer.sub buf 0 nbytes
  let random_oracle nout_bits data =
    let seed = hash (encode_int4 nout_bits ^ data) in
    let a = Bytes.of_string (prg seed ((nout_bits + 7) / 8)) in
    if nout_bits mod 8 <> 0 then Bytes.set a 0 (Char.chr (Char.code (Bytes.get a 0) land ((1 lsl (nout_bits mod 8)) - 1)));
    Bytes.to_string a
  let z_of_bytes s = Z.of_bits (String.init (String.length s) (fun i -> s.[String.length s - 1 - i]))
  let tag xml name =
    let re = Str.regexp ("<" ^ name ^ ">\\(\\([^<]\\|\n\\)*\\)</" ^ name ^ ">") in
    ignore (Str.search_forward re xml 0); String.trim (Str.matched_group 1 xml)

  let run prot dir =
    let xml = read_file prot in
    let path f = Filename.concat dir f and ppath f = Filename.concat (Filename.concat dir "proofs") f in
    let version_prot = tag xml "version" and sid = tag xml "sid" in
    let ne = int_of_string (tag xml "ebitlenro") and nr = int_of_string (tag xml "statdist")
    and nv = int_of_string (tag xml "vbitlenro") in
    let s_h = tag xml "rohash" and s_prg = tag xml "prg" and s_gq = tag xml "pgroup" in
    let kappa = int_of_string (tag xml "keywidth") and w_default = int_of_string (tag xml "width") in
    hash_name := s_h; prg_name := s_prg;
    if kappa < 1 then failwith "key width";
    let hex = List.nth (String.split_on_char ':' s_gq) (List.length (String.split_on_char ':' s_gq) - 1) in
    let gt = decode (Cryptokit.transform_string (Cryptokit.Hexa.decode ()) hex) in
    let (cls, params) = match children gt with [Leaf c; ps] -> (c, ps) | _ -> failwith "group" in
    if cls <> "com.verificatum.arithm.ModPGroup" then failwith "only ModPGroup";
    let (pg, qg, gg) = match children params with
      | [pp; qq; g; _] -> (int_of_leaf pp, int_of_leaf qq, int_of_leaf g) | _ -> failwith "group parameters" in
    if not (Z.equal pg p && Z.equal qg q) then failwith "the group of the protocol is not the certified one";
    if not (Z.equal gg (elem_to_Z generator)) then failwith "the generator is not the certified one";
    let g = generator in
    let version = read_ascii (path "version") and typ = read_ascii (path "type")
    and auxsid = read_ascii (path "auxsid") and width = int_of_string (read_ascii (path "width")) in
    if version <> version_prot || version <> "3.1.0" then failwith "version";
    if typ <> "shuffling" then failwith "only shuffling sessions";
    if width <> 1 || w_default <> 1 then failwith "only ciphertext width 1";
    let rho = hash (encode (Node [Leaf version; Leaf (sid ^ "." ^ auxsid); leaf_int4 nr; leaf_int4 nv;
      leaf_int4 ne; Leaf s_prg; Leaf s_gq; Leaf s_h])) in
    let ns = 8 * String.length (prg_hash "") in
    let ro_seed data = random_oracle ns (rho ^ data) in
    let ro_chal data = z_of_bytes (random_oracle nv (rho ^ data)) in
    (* elements of G^κ: a leaf for κ = 1, a node of κ leaves otherwise *)
    let prod_of t = if kappa = 1 then [int_of_leaf t] else
        (let cs = children t in if List.length cs <> kappa then failwith "product element width"; List.map int_of_leaf cs) in
    let bt_prod xs = if kappa = 1 then leaf_p (List.hd xs) else Node (List.map leaf_p xs) in
    let pk = match children (read_bt (path "FullPublicKey.bt")) with
      | [a; b] -> (prod_of a, prod_of b) | _ -> failwith "public key" in
    if List.exists (fun x -> not (Z.equal x (elem_to_Z g))) (fst pk) then failwith "public key generator";
    (* a ciphertext list: (u_i, v_i) with u_i, v_i ∈ G^κ. An array of elements of
       G^κ is stored as κ component arrays (for κ = 1, the array itself) *)
    let rec transpose = function [] -> [] | [] :: _ -> [] | rows -> List.map List.hd rows :: transpose (List.map List.tl rows) in
    let prod_array t =
      if kappa = 1 then List.map (fun x -> [int_of_leaf x]) (children t) else begin
        let comps = List.map (fun c -> List.map int_of_leaf (children c)) (children t) in
        if List.length comps <> kappa then failwith "product array width";
        (match comps with c :: cs -> if List.exists (fun c' -> List.length c' <> List.length c) cs then failwith "product array lengths" | [] -> ());
        transpose comps end in
    let bt_prod_array xs =
      if kappa = 1 then Node (List.map (fun x -> leaf_p (List.hd x)) xs)
      else Node (List.map (fun c -> Node (List.map leaf_p c)) (transpose xs)) in
    let ciph_array t = match children t with
      | [us; vs] -> let us = prod_array us and vs = prod_array vs in
        if List.length us <> List.length vs then failwith "ciphertext array"; List.combine us vs
      | _ -> failwith "ciphertext array" in
    let l0 = ciph_array (read_bt (path "Ciphertexts.bt")) in
    let n = List.length l0 in
    if n = 0 then failwith "no ciphertexts";
    let lambda_a = int_of_string (read_ascii (ppath "activethreshold")) in
    if lambda_a < 1 then failwith "active threshold";
    let lists = List.init lambda_a (fun i -> ciph_array (read_bt (ppath (Printf.sprintf "Ciphertexts%02d.bt" (i + 1))))) in
    let final = ciph_array (read_bt (path "ShuffledCiphertexts.bt")) in
    List.iter (fun l -> if List.length l <> n then failwith "list length") (final :: lists);
    let hs =
      let s = ro_seed (encode (Leaf "generators")) in
      let np = Z.numbits p in
      let nb = (np + nr + 7) / 8 in
      let out = prg s (nb * n) in
      List.init n (fun i ->
        let t = Z.erem (z_of_bytes (String.sub out (nb * i) nb)) (Z.shift_left Z.one (np + nr)) in
        Z.powm t (Z.divexact (Z.sub p Z.one) q) p) in
    let batch s = let nb = (ne + 7) / 8 in let out = prg s (nb * n) in
      List.init n (fun i -> Z.erem (z_of_bytes (String.sub out (nb * i) nb)) (Z.shift_left Z.one ne)) in
    let bt_elems xs = Node (List.map leaf_p xs) in
    let bt_ciphs cs = Node [bt_prod_array (List.map fst cs); bt_prod_array (List.map snd cs)] in
    let bt_pk = Node [bt_prod (fst pk); bt_prod (snd pk)] in
    let velems xs = vector_of_list (List.map elem xs) in
    let vscalars xs = vector_of_list (List.map scalar xs) in
    let nz = bi (n - 1) in
    let comp j xs = List.nth xs j in
    (* the proof of a shuffle of server l, on the lists w -> w' *)
    let verify_server l w w' =
      let mu = read_bt (ppath (Printf.sprintf "PermutationCommitment%02d.bt" l)) in
      let tau = read_bt (ppath (Printf.sprintf "PoSCommitment%02d.bt" l)) in
      let sigma = read_bt (ppath (Printf.sprintf "PoSReply%02d.bt" l)) in
      let u = List.map int_of_leaf (children mu) in
      let ints t = List.map int_of_leaf (children t) in
      let (b, a', b', c', d', f') = match children tau with
        | [b; a'; b'; c'; d'; f'] -> (ints b, int_of_leaf a', ints b', int_of_leaf c', int_of_leaf d',
            (match children f' with [x; y] -> (prod_of x, prod_of y) | _ -> failwith "F'"))
        | _ -> failwith "PoSCommitment" in
      let (ka, kb, kc, kd, ke, kf) = match children sigma with
        | [ka; kb; kc; kd; ke; kf] -> (int_of_leaf ka, ints kb, int_of_leaf kc, int_of_leaf kd, ints ke,
            (if kappa = 1 then [int_of_leaf kf] else (let cs = children kf in if List.length cs <> kappa then failwith "k_F width"; List.map int_of_leaf cs)))
        | _ -> failwith "PoSReply" in
      if List.length u <> n || List.length b <> n || List.length b' <> n || List.length kb <> n || List.length ke <> n
      then failwith "array length in the proof of a shuffle";
      (* the byte trees of the proof must be canonical: they are what is hashed *)
      let tau' = Node [bt_elems b; leaf_p a'; bt_elems b'; leaf_p c'; leaf_p d'; Node [bt_prod (fst f'); bt_prod (snd f')]] in
      if encode tau' <> encode tau then failwith "PoSCommitment: non-canonical encoding";
      if encode (bt_elems u) <> encode mu then failwith "PermutationCommitment: non-canonical encoding";
      let s = ro_seed (encode (Node [leaf_p (elem_to_Z g); bt_elems hs; bt_elems u; bt_pk; bt_ciphs w; bt_ciphs w'])) in
      let es = vscalars (List.map (fun e -> Z.erem e q) (batch s)) in
      let v = scalar (Z.erem (ro_chal (encode (Node [Leaf s; tau']))) q) in
      let o = mk_pos_oracles nz (fun _ _ _ -> es) (fun _ _ _ _ -> v) in
      List.for_all (fun j ->
        let pf = mk_pos_proof nz (velems u) (velems b) (elem a') (velems b') (elem c') (elem d')
          (elem (comp j (fst f')), elem (comp j (snd f'))) (scalar ka) (vscalars kb) (scalar kc) (scalar kd)
          (vscalars ke) (scalar (comp j kf)) in
        let wj = vector_of_list (List.map (fun (a, b) -> (elem (comp j a), elem (comp j b))) w) in
        let wj' = vector_of_list (List.map (fun (a, b) -> (elem (comp j a), elem (comp j b))) w') in
        verify_pos_ins nz (velems hs) (g, elem (comp j (snd pk))) o wj wj' pf) (List.init kappa Fun.id) in
    let ok = ref true and prev = ref l0 in
    List.iteri (fun i w' -> let l = i + 1 in
      let r = verify_server l !prev w' in
      Printf.printf "server %d: proof of a shuffle %b\n" l r;
      if not r then ok := false; prev := w') lists;
    let same = List.for_all2 (fun (a, b) (c, d) -> List.for_all2 Z.equal a c && List.for_all2 Z.equal b d) !prev final in
    if not same then (print_endline "ShuffledCiphertexts.bt is not the output of the last server"; ok := false);
    Printf.printf "session %s.%s (N=%d, key width %d, %d server(s)): verified = %b\n" sid auxsid n kappa lambda_a !ok;
    !ok
end

(* ================================================================== *)
(* decryption proofs (Java) and decryption-share proofs (Go)          *)
(* ================================================================== *)

module Zkp = struct
  open SwissPostZkpIvxvIns
  let elem (x : Z.t) = if not (in_group x) then failwith "element not in the group"; x
  let scalar (x : Z.t) = if Z.sign x < 0 || Z.geq x q then failwith "scalar out of range"; BayerGrothIvxvIns.of_Z x
  let member k (j : Yojson.Safe.t) = match j with
    | `Assoc kvs -> (match List.assoc_opt k kvs with Some v -> v | None -> failwith ("missing " ^ k))
    | _ -> failwith "not an object"
  let str = function `String s -> s | _ -> failwith "not a string"
  let num j = Z.of_string (str j)   (* decimal strings; may be negative or out of range: checked below *)
  let hexs j = Cryptokit.transform_string (Cryptokit.Hexa.decode ()) (str j)
  let mulg x y = Z.erem (Z.mul x y) p
  let inv x = Z.invert x p

  (* DER: INTEGER (minimal two's complement), SEQUENCE *)
  let der_len n =
    if n < 128 then String.make 1 (Char.chr n) else begin
      let rec bytes n acc = if n = 0 then acc else bytes (n lsr 8) (String.make 1 (Char.chr (n land 255)) ^ acc) in
      let b = bytes n "" in String.make 1 (Char.chr (0x80 lor String.length b)) ^ b end
  let der_int (x : Z.t) =
    let nb = Z.numbits x / 8 + 1 in   (* non-negative: room for a sign bit *)
    let bits = Z.to_bits x in
    let b = String.init nb (fun i -> let k = nb - 1 - i in if k < String.length bits then bits.[k] else '\000') in
    "\002" ^ der_len nb ^ b
  let der_seq content = "\048" ^ der_len (String.length content) ^ content
  let sha256 s = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s

  (* IVXV DPRNG: blocks SHA-256(bytes8(counter) | seed), counter from 1;
     IntegerConstructor: draw ⌈|q|/8⌉ bytes, mask the top byte, reject ≥ q *)
  let dprng_int (seed : string) (upper : Z.t) : Z.t =
    let counter = ref 1 and buf = Buffer.create 64 in
    let next n = while Buffer.length buf < n do
        let c = Bytes.create 8 in Bytes.set_int64_be c 0 (Int64.of_int !counter); incr counter;
        Buffer.add_string buf (sha256 (Bytes.to_string c ^ seed)) done;
      let s = Buffer.sub buf 0 n in let rest = Buffer.sub buf n (Buffer.length buf - n) in
      Buffer.clear buf; Buffer.add_string buf rest; s in
    let nbits = Z.numbits upper in
    let nb = (nbits + 7) / 8 and mask = (let m = nbits mod 8 in if m = 0 then 255 else (1 lsl m) - 1) in
    let rec loop () =
      let b = Bytes.of_string (next nb) in
      Bytes.set b 0 (Char.chr (Char.code (Bytes.get b 0) land mask));
      let x = Z.of_bits (String.init nb (fun i -> Bytes.get b (nb - 1 - i))) in
      if Z.lt x upper then x else loop () in
    loop ()

  let verify rows ys e zs hash =
    verify_zkp_ins (bi (List.length zs)) (bi (List.length ys)) (fun cs -> hash (list_of_vector cs))
      (vector_of_list (List.map vector_of_list rows)) (vector_of_list ys) e (vector_of_list zs)

  (* ElGamalDecryptionProof: c1^s = a·(c2/d)^k and g^s = b·y^k with
     k = DPRNG(DER SEQUENCE(prefix…, INTEGER a, INTEGER b)) mod-rejected below q *)
  let dec_case j =
    let g = elem (num (member "g" j)) and y = elem (num (member "y" j)) in
    let c1 = elem (num (member "c1" j)) and c2 = elem (num (member "c2" j)) and d = elem (num (member "d" j)) in
    let a = elem (num (member "a" j)) and b = elem (num (member "b" j)) and s = scalar (num (member "s" j)) in
    let prefix = hexs (member "prefix" j) in
    let h cs = match cs with
      | [a'; b'] -> BayerGrothIvxvIns.of_Z (dprng_int (der_seq (prefix ^ der_int a' ^ der_int b')) q)
      | _ -> failwith "arity" in
    let k = h [a; b] in
    verify [[c1]; [g]] [mulg c2 (inv d); y] k [s] h

end

(* SHAKE-256 (FIPS 202): Keccak-f[1600], rate 136 bytes, padding 0x1F … 0x80 *)
module Shake = struct
  let rc = [| 0x0000000000000001L; 0x0000000000008082L; 0x800000000000808AL; 0x8000000080008000L;
              0x000000000000808BL; 0x0000000080000001L; 0x8000000080008081L; 0x8000000000008009L;
              0x000000000000008AL; 0x0000000000000088L; 0x0000000080008009L; 0x000000008000000AL;
              0x000000008000808BL; 0x800000000000008BL; 0x8000000000008089L; 0x8000000000008003L;
              0x8000000000008002L; 0x8000000000000080L; 0x000000000000800AL; 0x800000008000000AL;
              0x8000000080008081L; 0x8000000000008080L; 0x0000000080000001L; 0x8000000080008008L |]
  let rotc = [| 1; 3; 6; 10; 15; 21; 28; 36; 45; 55; 2; 14; 27; 41; 56; 8; 25; 43; 62; 18; 39; 61; 20; 44 |]
  let piln = [| 10; 7; 11; 17; 18; 3; 5; 16; 8; 21; 24; 4; 15; 23; 19; 13; 12; 2; 20; 14; 22; 9; 6; 1 |]
  let rotl x n = Int64.logor (Int64.shift_left x n) (Int64.shift_right_logical x (64 - n))
  let keccakf (st : int64 array) =
    let bc = Array.make 5 0L in
    for round = 0 to 23 do
      for i = 0 to 4 do
        bc.(i) <- Int64.logxor st.(i) (Int64.logxor st.(i + 5) (Int64.logxor st.(i + 10) (Int64.logxor st.(i + 15) st.(i + 20))))
      done;
      for i = 0 to 4 do
        let t = Int64.logxor bc.((i + 4) mod 5) (rotl bc.((i + 1) mod 5) 1) in
        List.iter (fun j -> st.(j + i) <- Int64.logxor st.(j + i) t) [0; 5; 10; 15; 20]
      done;
      let t = ref st.(1) in
      for i = 0 to 23 do
        let j = piln.(i) in let tmp = st.(j) in st.(j) <- rotl !t rotc.(i); t := tmp
      done;
      List.iter (fun j ->
        for i = 0 to 4 do bc.(i) <- st.(j + i) done;
        for i = 0 to 4 do
          st.(j + i) <- Int64.logxor bc.(i) (Int64.logand (Int64.lognot bc.((i + 1) mod 5)) bc.((i + 2) mod 5))
        done) [0; 5; 10; 15; 20];
      st.(0) <- Int64.logxor st.(0) rc.(round)
    done
  let rate = 136
  let shake256 (msg : string) (outlen : int) : string =
    let st = Array.make 25 0L in
    let xor_block (b : Bytes.t) =
      for i = 0 to rate / 8 - 1 do st.(i) <- Int64.logxor st.(i) (Bytes.get_int64_le b (8 * i)) done; keccakf st in
    let n = String.length msg in
    let full = n / rate in
    for k = 0 to full - 1 do xor_block (Bytes.of_string (String.sub msg (k * rate) rate)) done;
    let last = Bytes.make rate '\000' in
    Bytes.blit_string msg (full * rate) last 0 (n - full * rate);
    Bytes.set last (n - full * rate) (Char.chr (Char.code (Bytes.get last (n - full * rate)) lxor 0x1f));
    Bytes.set last (rate - 1) (Char.chr (Char.code (Bytes.get last (rate - 1)) lxor 0x80));
    xor_block last;
    let out = Buffer.create outlen in
    let rec squeeze () =
      let b = Bytes.create rate in
      for i = 0 to rate / 8 - 1 do Bytes.set_int64_le b (8 * i) st.(i) done;
      Buffer.add_bytes out b;
      if Buffer.length out < outlen then (keccakf st; squeeze ()) in
    squeeze (); Buffer.sub out 0 outlen
  let () =  (* FIPS 202 test value: SHAKE-256("") *)
    assert (Cryptokit.transform_string (Cryptokit.Hexa.encode ()) (shake256 "" 32) =
            "46b9dd2b0ba88d13233b3feb743eeb243fcd52ea62b81b82b50c27646ed5762f")
end

(* IVXV Go core decryption proofs (crypto/elgamal PublicKey.Verify) at RFC 3526
   group 14: compact (e, s) with keyc = g^s·y^{-e}, msgc = c1^s·(c2/d)^{-e} and
   e = rand.Int(SHAKE-256(DER SEQUENCE(prefix, msgc, keyc, suffix)), q), 0 mapped to 1 *)
module Gonizkp = struct
  open SwissPostZkpIvxvGoIns
  let p = BayerGrothIvxvGoIns.p and q = BayerGrothIvxvGoIns.q
  let in_group x = Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one
  let elem x = if not (in_group x) then failwith "element not in the group"; x
  let scalar x = if Z.sign x < 0 || Z.geq x q then failwith "scalar out of range"; BayerGrothIvxvGoIns.of_Z x
  let rand_int (stream : string) (mx : Z.t) : Z.t =
    let bl = Z.numbits (Z.pred mx) in
    let k = (bl + 7) / 8 and b = (let r = bl mod 8 in if r = 0 then 8 else r) in
    let rec loop pos =
      if pos + k > String.length stream then failwith "stream exhausted";
      let c = Bytes.of_string (String.sub stream pos k) in
      Bytes.set c 0 (Char.chr (Char.code (Bytes.get c 0) land ((1 lsl b) - 1)));
      let n = Z.of_bits (String.init k (fun i -> Bytes.get c (k - 1 - i))) in
      if Z.lt n mx then (if Z.sign n = 0 then Z.one else n) else loop (pos + k) in
    loop 0
  let case j =
    let member = Zkp.member and num = Zkp.num and hexs = Zkp.hexs and der_seq = Zkp.der_seq and der_int = Zkp.der_int in
    let g = elem (Z.of_int 2) and y = elem (num (member "y" j)) in
    let c1 = elem (num (member "c1" j)) and c2 = elem (num (member "c2" j)) and d = elem (num (member "d" j)) in
    let e = scalar (num (member "e" j)) and s = scalar (num (member "s" j)) in
    let prefix = hexs (member "prefix" j) and suffix = hexs (member "suffix" j) in
    let mulg x y = Z.erem (Z.mul x y) p in
    let h cs = match cs with
      | [msgc; keyc] -> BayerGrothIvxvGoIns.of_Z (rand_int (Shake.shake256 (der_seq (prefix ^ der_int msgc ^ der_int keyc ^ suffix)) 4096) q)
      | _ -> failwith "arity" in
    verify_zkp_ins (bi 1) (bi 2) (fun cs -> h (list_of_vector cs))
      (vector_of_list [vector_of_list [c1]; vector_of_list [g]]) (vector_of_list [mulg c2 (Z.invert d p); y]) e (vector_of_list [s])
end

let () =
  if Array.length Sys.argv < 3 then (prerr_endline "usage: main.exe shuffle protInfo.xml DIR | dec CASES.json | nizkp CASES.json"; exit 2);
  match Sys.argv.(1) with
  | "shuffle" ->
    let ok = (try Shuffle.run Sys.argv.(2) Sys.argv.(3) with
        | Failure m -> Printf.printf "rejected by the parser: %s\n" m; false
        | Not_found | Invalid_argument _ -> print_endline "rejected by the parser: malformed data"; false
        | Sys_error m -> Printf.printf "rejected: %s\n" m; false) in
    exit (if ok then 0 else 1)
  | "dec" ->
    let cases = match Yojson.Safe.from_file Sys.argv.(2) with `List l -> l | _ -> failwith "cases" in
    List.iter (fun c ->
      let r = try if Zkp.dec_case c then "true" else "false" with
        | Failure m -> "false\tparser: " ^ m | Invalid_argument m -> "false\tparser: " ^ m | Division_by_zero -> "false\tparser: division" in
      print_endline r) cases
  | "nizkp" ->
    let cases = match Yojson.Safe.from_file Sys.argv.(2) with `List l -> l | _ -> failwith "cases" in
    List.iter (fun c ->
      let r = try if Gonizkp.case c then "true" else "false" with
        | Failure m -> "false\tparser: " ^ m | Invalid_argument m -> "false\tparser: " ^ m | Division_by_zero -> "false\tparser: division" in
      print_endline r) cases
  | m -> prerr_endline ("unknown mode " ^ m); exit 2
