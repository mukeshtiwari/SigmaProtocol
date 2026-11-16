(* Certified verifier for Verificatum mix-net proofs (VMN 3.1.0, "How to
   Implement a Stand-alone Verifier for the Verificatum Mix-Net"), for
   mixing sessions with key width 1 and ciphertext width 1 over a
   multiplicative group modulo a prime, without pre-computation.

   Usage: main.exe protInfo.xml PROOF_DIRECTORY

   The driver parses the protocol info file and the byte trees of the
   proof directory, checks the group against the certified one, computes
   the prefix ρ, the independent generators, and the random oracles
   (SHA-256 based, sections 5 and 8 of the manual), checks that every
   element is in the group and every scalar in the field, and hands
   everything to the certified verifier Examples/VerificatumIns.v: the
   proofs of a shuffle of the mix-servers (Algorithm 19 and 25, the
   Okamoto acceptance test at the statement space of Crypto/ShuffleTW.v),
   the joint decryption (Algorithm 22, a Chaum–Pedersen acceptance test)
   and the plaintexts. *)

open Verificatumlib
open Verificatumlib.VerificatumIns
module List = Stdlib.List
module String = Stdlib.String

let bi = Big_int_Z.big_int_of_int

(* ---- the group, from the certified instantiation ---- *)

let p : Z.t = HeliosTallyIns.p
let q : Z.t = HeliosTallyIns.q

let in_group (x : Z.t) = Z.sign x > 0 && Z.lt x p && Z.equal (Z.powm x q p) Z.one
let elem (x : Z.t) : Zpstar.Schnorr.coq_Schnorr_group =
  if not (in_group x) then failwith "element not in the group"; x
let scalar (x : Z.t) : Zpstar.Zpfield.coq_Zp =
  if Z.sign x < 0 || Z.geq x q then failwith "scalar out of range"; of_Z x

(* ---- byte trees (section 4) ---- *)

type bt = Leaf of string | Node of bt list

let rec encode = function
  | Leaf d ->
    let n = String.length d in
    let b = Bytes.create 5 in
    Bytes.set b 0 '\001'; Bytes.set_int32_be b 1 (Int32.of_int n);
    Bytes.to_string b ^ d
  | Node cs ->
    let b = Bytes.create 5 in
    Bytes.set b 0 '\000'; Bytes.set_int32_be b 1 (Int32.of_int (List.length cs));
    Bytes.to_string b ^ String.concat "" (List.map encode cs)

let decode (s : string) : bt =
  let rec go pos =
    let tag = Char.code s.[pos] in
    let n = Int32.to_int (String.get_int32_be s (pos + 1)) in
    let pos = pos + 5 in
    if tag = 1 then (Leaf (String.sub s pos n), pos + n)
    else begin
      let rec children k pos acc = if k = 0 then (List.rev acc, pos) else
        let (c, pos') = go pos in children (k - 1) pos' (c :: acc) in
      let (cs, pos') = children n pos [] in (Node cs, pos')
    end in
  let (t, pos) = go 0 in
  if pos <> String.length s then failwith "byte tree: trailing data"; t

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in close_in ic; s

let read_bt path = decode (read_file path)
let read_ascii path = String.trim (read_file path)

(* two's complement big-endian integers *)
let int_of_leaf = function
  | Leaf d ->
    let z = Z.of_bits (String.init (String.length d) (fun i -> d.[String.length d - 1 - i])) in
    if String.length d > 0 && Char.code d.[0] >= 128 then Z.sub z (Z.shift_left Z.one (8 * String.length d)) else z
  | Node _ -> failwith "byte tree: expected a leaf"

(* bytes_k(n): k-byte two's complement of a non-negative n *)
let leaf_of_int (k : int) (n : Z.t) : bt =
  if Z.sign n < 0 then failwith "negative";
  let bits = Z.to_bits n in
  let get i = if i < String.length bits then bits.[i] else '\000' in
  Leaf (String.init k (fun i -> get (k - 1 - i)))

(* field and group elements use the fixed size of their modulus *)
let width_of (m : Z.t) = let k = ref 1 in while Z.geq m (Z.shift_left Z.one (8 * !k - 1)) do incr k done; !k
let kp = width_of p
let kq = width_of q
let leaf_p (x : Z.t) = leaf_of_int kp x
let leaf_q (x : Z.t) = leaf_of_int kq x
let leaf_str s = Leaf s
let leaf_int4 n = leaf_of_int 4 (Z.of_int n)

let children = function Node cs -> cs | Leaf _ -> failwith "byte tree: expected a node"
let ints t = List.map int_of_leaf (children t)

(* ---- hash function, PRG and random oracles (section 5) ---- *)

let hash_name = ref "SHA-256"
let hash_fn () = match !hash_name with
  | "SHA-256" -> Cryptokit.Hash.sha256 () | "SHA-384" -> Cryptokit.Hash.sha384 ()
  | "SHA-512" -> Cryptokit.Hash.sha512 () | s -> failwith ("hash " ^ s)
let hash (s : string) : string = let h = hash_fn () in h#add_string s; h#result
let outlen () = String.length (hash "")

let prg_name = ref "SHA-256"
let prg_hash (s : string) : string =
  let h = (match !prg_name with
    | "SHA-256" -> Cryptokit.Hash.sha256 () | "SHA-384" -> Cryptokit.Hash.sha384 ()
    | "SHA-512" -> Cryptokit.Hash.sha512 () | s -> failwith ("prg " ^ s)) in
  h#add_string s; h#result
let prg_seedlen () = String.length (prg_hash "")

let encode_int4 n = let b = Bytes.create 4 in Bytes.set_int32_be b 0 (Int32.of_int n); Bytes.to_string b

(* r_0 | r_1 | … with r_i = H(seed | bytes4(i)) *)
let prg (seed : string) (nbytes : int) : string =
  let buf = Buffer.create nbytes in
  let i = ref 0 in
  while Buffer.length buf < nbytes do
    Buffer.add_string buf (prg_hash (seed ^ encode_int4 !i)); incr i
  done;
  Buffer.sub buf 0 nbytes

let random_oracle (nout_bits : int) (data : string) : string =
  let seed = hash (encode_int4 nout_bits ^ data) in
  let nbytes = (nout_bits + 7) / 8 in
  let a = Bytes.of_string (prg seed nbytes) in
  if nout_bits mod 8 <> 0 then
    Bytes.set a 0 (Char.chr (Char.code (Bytes.get a 0) land ((1 lsl (nout_bits mod 8)) - 1)));
  Bytes.to_string a

let z_of_bytes (s : string) : Z.t = Z.of_bits (String.init (String.length s) (fun i -> s.[String.length s - 1 - i]))

(* ---- protocol info ---- *)

let tag (xml : string) (name : string) : string =
  let re = Str.regexp ("<" ^ name ^ ">\\(\\([^<]\\|\n\\)*\\)</" ^ name ^ ">") in
  ignore (Str.search_forward re xml 0); String.trim (Str.matched_group 1 xml)

let main () =
  let xml = read_file Sys.argv.(1) and dir = Sys.argv.(2) in
  let path f = Filename.concat dir f in
  let ppath f = Filename.concat (path "proofs") f in
  let version_prot = tag xml "version" and sid = tag xml "sid" in
  let k = int_of_string (tag xml "nopart") and lambda = int_of_string (tag xml "thres") in
  let ne = int_of_string (tag xml "ebitlenro") and nr = int_of_string (tag xml "statdist")
  and nv = int_of_string (tag xml "vbitlenro") in
  let s_h = tag xml "rohash" and s_prg = tag xml "prg" and s_gq = tag xml "pgroup" in
  let kappa = int_of_string (tag xml "keywidth") and w_default = int_of_string (tag xml "width") in
  hash_name := s_h; prg_name := s_prg;
  if kappa <> 1 then failwith "only key width 1 is supported";
  (* the group: unmarshal and compare with the certified one *)
  let hex = List.nth (String.split_on_char ':' s_gq) (List.length (String.split_on_char ':' s_gq) - 1) in
  let gt = decode (Cryptokit.transform_string (Cryptokit.Hexa.decode ()) hex) in
  let (cls, params) = match children gt with [Leaf c; ps] -> (c, ps) | _ -> failwith "group" in
  if cls <> "com.verificatum.arithm.ModPGroup" then failwith "only ModPGroup is supported";
  let (pg, qg, gg) = match children params with
    | [pp; qq; g; _] -> (int_of_leaf pp, int_of_leaf qq, int_of_leaf g) | _ -> failwith "group parameters" in
  if not (Z.equal pg p && Z.equal qg q) then failwith "the group of the protocol is not the certified one";
  if not (Z.equal gg (elem_to_Z generator)) then failwith "the generator of the protocol is not the certified one";
  let g = generator in
  (* proof parameters *)
  let version = read_ascii (path "version") and typ = read_ascii (path "type")
  and auxsid = read_ascii (path "auxsid") and width = int_of_string (read_ascii (path "width")) in
  if version <> version_prot || version <> "3.1.0" then failwith "version";
  if typ <> "mixing" then failwith "only mixing sessions are supported";
  if width <> 1 || w_default <> 1 then failwith "only width 1 is supported";
  (* ρ *)
  let rho = hash (encode (Node [leaf_str version; leaf_str (sid ^ "." ^ auxsid); leaf_int4 nr; leaf_int4 nv;
    leaf_int4 ne; leaf_str s_prg; leaf_str s_gq; leaf_str s_h])) in
  let ns = 8 * prg_seedlen () in
  let ro_seed data = random_oracle ns (rho ^ data) in
  let ro_chal data = z_of_bytes (random_oracle nv (rho ^ data)) in
  (* keys and lists *)
  let pk = match children (read_bt (path "FullPublicKey.bt")) with
    | [a; b] -> (int_of_leaf a, int_of_leaf b) | _ -> failwith "public key" in
  if not (Z.equal (fst pk) (elem_to_Z g)) then failwith "public key generator";
  let ciph_array t = match children t with
    | [us; vs] -> List.combine (ints us) (ints vs) | _ -> failwith "ciphertext array" in
  let l0 = ciph_array (read_bt (path "Ciphertexts.bt")) in
  let n = List.length l0 in
  if n = 0 then failwith "no ciphertexts";
  let lambda_a = int_of_string (read_ascii (ppath "activethreshold")) in
  let m = ints (read_bt (path "Plaintexts.bt")) in
  let gamma = ints (read_bt (ppath "PolynomialInExponent.bt")) in
  (* independent generators (sections 6.8 and 8.2) *)
  let hs =
    let s = ro_seed (encode (leaf_str "generators")) in
    let np = Z.numbits p in
    let nb = (np + nr + 7) / 8 in
    let out = prg s (nb * n) in
    List.init n (fun i ->
      let t = Z.erem (z_of_bytes (String.sub out (nb * i) nb)) (Z.shift_left Z.one (np + nr)) in
      Z.powm t (Z.divexact (Z.sub p Z.one) q) p) in
  (* batching vector from a seed *)
  let batch (s : string) : Z.t list =
    let nb = (ne + 7) / 8 in
    let out = prg s (nb * n) in
    List.init n (fun i -> Z.erem (z_of_bytes (String.sub out (nb * i) nb)) (Z.shift_left Z.one ne)) in
  (* byte trees of the data, as hashed *)
  let bt_elems xs = Node (List.map leaf_p xs) in
  let bt_ciphs cs = Node [Node (List.map (fun (u, _) -> leaf_p u) cs); Node (List.map (fun (_, v) -> leaf_p v) cs)] in
  let bt_pk = Node [leaf_p (fst pk); leaf_p (snd pk)] in
  (* ---- conversion to the certified types ---- *)
  let rec vector_of_list = function
    | [] -> VectorDef.Coq_nil
    | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t) in
  let velems xs = vector_of_list (List.map elem xs) in
  let vscalars xs = vector_of_list (List.map scalar xs) in
  let vciphs cs = vector_of_list (List.map (fun (u, v) -> (elem u, elem v)) cs) in
  let nz = bi (n - 1) in
  (* the proof of a shuffle of one server, with its oracles *)
  let pos_of l =
    let mu = read_bt (ppath (Printf.sprintf "PermutationCommitment%02d.bt" l)) in
    let tau = read_bt (ppath (Printf.sprintf "PoSCommitment%02d.bt" l)) in
    let sigma = read_bt (ppath (Printf.sprintf "PoSReply%02d.bt" l)) in
    let u = ints mu in
    let (b, a', b', c', d', f') = match children tau with
      | [b; a'; b'; c'; d'; f'] -> (ints b, int_of_leaf a', ints b', int_of_leaf c', int_of_leaf d',
          (match children f' with [x; y] -> (int_of_leaf x, int_of_leaf y) | _ -> failwith "F'"))
      | _ -> failwith "PoSCommitment" in
    let (ka, kb, kc, kd, ke, kf) = match children sigma with
      | [ka; kb; kc; kd; ke; kf] -> (int_of_leaf ka, ints kb, int_of_leaf kc, int_of_leaf kd, ints ke, int_of_leaf kf)
      | _ -> failwith "PoSReply" in
    if List.length u <> n || List.length b <> n || List.length b' <> n || List.length kb <> n || List.length ke <> n
    then failwith "array length in the proof of a shuffle";
    let pf = mk_pos_proof nz (velems u) (velems b) (elem a') (velems b') (elem c') (elem d')
      (elem (fst f'), elem (snd f')) (scalar ka) (vscalars kb) (scalar kc) (scalar kd) (vscalars ke) (scalar kf) in
    (pf, u, tau) in
  (* the oracles of Algorithm 19: e from RO_seed(ρ | node(g, h, u, pk, w, w')),
     v from RO_challenge(ρ | node(leaf(s), τ)); they receive the certified
     data, which is only used to pick the byte trees of the same server *)
  let seed_of u w w' = ro_seed (encode (Node [leaf_p (elem_to_Z g); bt_elems hs; bt_elems u; bt_pk; bt_ciphs w; bt_ciphs w'])) in
  let list_of_vector v = let rec go = function VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: go t in go v in
  let ciph_list v = List.map (fun (a, b) -> (elem_to_Z a, elem_to_Z b)) (list_of_vector v) in
  let oracle_es u w w' =
    let u = List.map elem_to_Z (list_of_vector u) in
    vscalars (List.map (fun e -> Z.erem e q) (batch (seed_of u (ciph_list w) (ciph_list w')))) in
  (* τ = (B, A', B', C', D', F') is re-encoded from the proof the certified
     verifier is checking. (It used to be looked up in a table keyed by A':
     two proofs with the same A' then shared one τ, so a proof's challenge
     could be computed from another server's commitments, leaving its own
     B, B', C', D', F' outside the hash; found by bench/verificatum-diff.) *)
  let tau_of (pf : (Zpstar.Zpfield.coq_Zp, Zpstar.Schnorr.coq_Schnorr_group) VerificatumVerifier.pos_proof) =
    let open VerificatumVerifier in
    let z = elem_to_Z in
    let (f1, f2) = pf.pF' in
    Node [bt_elems (List.map z (list_of_vector pf.pB)); leaf_p (z pf.pA'); bt_elems (List.map z (list_of_vector pf.pB'));
          leaf_p (z pf.pC'); leaf_p (z pf.pD'); Node [leaf_p (z f1); leaf_p (z f2)]] in
  let oracle_v u w w' pf =
    let u = List.map elem_to_Z (list_of_vector u) in
    let s = seed_of u (ciph_list w) (ciph_list w') in
    scalar (Z.erem (ro_chal (encode (Node [Leaf s; tau_of pf]))) q) in
  let o = mk_pos_oracles nz oracle_es oracle_v in
  (* the steps: the lists L_1, …, L_λa with the proofs *)
  let lists = List.init lambda_a (fun i -> let l = i + 1 in
    ciph_array (read_bt (ppath (Printf.sprintf "Ciphertexts%02d.bt" l)))) in
  let steps = List.init lambda_a (fun i -> let l = i + 1 in
    let (pf, _, tau) = pos_of l in
    (* the re-encoded τ must be the byte tree of the proof file *)
    if encode (tau_of pf) <> encode tau then failwith "PoSCommitment: non-canonical encoding";
    (vciphs (List.nth lists i), pf)) in
  (* the decryption proofs of all k parties *)
  let parties = List.init k (fun i -> let l = i + 1 in
    let f = ints (read_bt (ppath (Printf.sprintf "DecryptionFactors%02d.bt" l))) in
    let tau = read_bt (ppath (Printf.sprintf "DecrFactCommitment%02d.bt" l)) in
    let (y', b') = match children tau with [a; b] -> (int_of_leaf a, int_of_leaf b) | _ -> failwith "DecrFactCommitment" in
    let kx = int_of_leaf (read_bt (ppath (Printf.sprintf "DecrFactReply%02d.bt" l))) in
    if List.length f <> n then failwith "decryption factors length";
    (bi l, mk_dec_proof nz (velems f) (elem y') (elem b') (scalar kx), f, tau)) in
  let delta = match read_bt (ppath "CorrectIndices.bt") with
    | Leaf d -> List.filter (fun l -> l >= 1 && Char.code d.[l] = 1) (List.init (String.length d) (fun i -> i))
    | Node _ -> failwith "CorrectIndices" in
  if List.length delta < lambda then failwith "too few correct parties";
  let l_last = List.nth lists (lambda_a - 1) in
  let dec_seed_data = encode (Node [Node [leaf_p (elem_to_Z g); bt_ciphs l_last];
    Node [bt_elems gamma; Node (List.map (fun (_, _, f, _) -> bt_elems f) parties)]]) in
  let dec_taus = Node (List.map (fun (_, _, _, tau) -> tau) parties) in
  let oracle_dec_es _ _ _ = vscalars (List.map (fun e -> Z.erem e q) (batch (ro_seed dec_seed_data))) in
  let oracle_dec_v _ _ _ = scalar (Z.erem (ro_chal (encode (Node [Leaf (ro_seed dec_seed_data); dec_taus]))) q) in
  let od = mk_dec_oracles nz oracle_dec_es oracle_dec_v in
  (* VMN_DEBUG=1: recompute the five equations of Algorithm 19 directly, to
     locate a discrepancy with the certified verifier *)
  if Sys.getenv_opt "VMN_DEBUG" <> None then begin
    let mulp a b = Z.erem (Z.mul a b) p and powp a e = Z.powm a e p in
    let mexp bs es = List.fold_left2 (fun acc b e -> mulp acc (powp b e)) Z.one bs es in
    let gz = elem_to_Z g and y = snd pk in
    let prev = ref l0 in
    List.iteri (fun i (_, pf) ->
      let l = i + 1 in
      let (_, u, tau) = pos_of l in
      let (b, a', b', c', d', f') = match children tau with
        | [b; a'; b'; c'; d'; f'] -> (ints b, int_of_leaf a', ints b', int_of_leaf c', int_of_leaf d',
            (match children f' with [x; y] -> (int_of_leaf x, int_of_leaf y) | _ -> failwith "F'"))
        | _ -> failwith "tau" in
      let sigma = read_bt (ppath (Printf.sprintf "PoSReply%02d.bt" l)) in
      let (ka, kb, kc, kd, ke, kf) = match children sigma with
        | [ka; kb; kc; kd; ke; kf] -> (int_of_leaf ka, ints kb, int_of_leaf kc, int_of_leaf kd, ints ke, int_of_leaf kf)
        | _ -> failwith "sigma" in
      let w = !prev and w' = List.nth lists i in
      let s = seed_of u w w' in
      let es = batch s in
      let v = ro_chal (encode (Node [Leaf s; tau])) in
      let a = mexp u es in
      let fu = mexp (List.map fst w) es and fv = mexp (List.map snd w) es in
      let c = mulp (List.fold_left mulp Z.one u) (Z.invert (List.fold_left mulp Z.one hs) p) in
      let pe = List.fold_left (fun acc e -> Z.erem (Z.mul acc e) q) Z.one es in
      let d = mulp (List.nth b (n - 1)) (Z.invert (powp (List.hd hs) pe) p) in
      let bprev = List.hd hs :: List.filteri (fun j _ -> j < n - 1) b in
      let e1 = Z.equal (mulp (powp a v) a') (mulp (powp gz ka) (mexp hs ke)) in
      let e2 = Z.equal (mulp (powp c v) c') (powp gz kc) in
      let e3 = Z.equal (mulp (powp d v) d') (powp gz kd) in
      let e4 = List.for_all (fun j -> Z.equal (mulp (powp (List.nth b j) v) (List.nth b' j))
        (mulp (powp gz (List.nth kb j)) (powp (List.nth bprev j) (List.nth ke j)))) (List.init n (fun j -> j)) in
      let e5 = Z.equal (mulp (powp fu v) (fst f')) (mulp (powp gz (Z.neg kf)) (mexp (List.map fst w') ke)) &&
               Z.equal (mulp (powp fv v) (snd f')) (mulp (powp y (Z.neg kf)) (mexp (List.map snd w') ke)) in
      Printf.printf "debug server %d: A %b C %b D %b B %b F %b; certified verify_pos %b\n" l e1 e2 e3 e4 e5
        (verify_pos_ins nz (velems hs) (elem (fst pk), elem (snd pk)) o (vciphs w) (vciphs w') pf);
      prev := w') steps
  end;
  (* ---- the certified verifier ---- *)
  let t0 = Unix.gettimeofday () in
  let pk_c = (elem (fst pk), elem (snd pk)) in
  let shuffles = verify_shuffling_ins nz (velems hs) pk_c o (vciphs l0) steps in
  let y = elem (List.hd gamma) in
  let dec = verify_decryption_ins nz y od (vciphs l_last) (List.map elem gamma)
    (List.map (fun (l, pf, _, _) -> (l, pf)) parties) (List.map bi delta) (velems m) in
  let all = verify_mixing_ins nz (velems hs) pk_c o od (vciphs l0) steps (List.map elem gamma)
    (List.map (fun (l, pf, _, _) -> (l, pf)) parties) (List.map bi delta) (velems m) in
  let t1 = Unix.gettimeofday () in
  Printf.printf "%-55s %b\n" "proofs of a shuffle of the mix-servers (Algorithm 25)" shuffles;
  Printf.printf "%-55s %b\n" "joint decryption and plaintexts (Algorithms 22, 27)" dec;
  Printf.printf "ciphertexts: %d, mix-servers: %d (active threshold %d), decrypting parties: %s\n"
    n k lambda_a (String.concat "," (List.map string_of_int delta));
  Printf.printf "session %s.%s: verified = %b (certified verifier: %.2f s)\n" sid auxsid all (t1 -. t0);
  exit (if all then 0 else 1)

(* a proof the parser cannot accept (wrong group or version, an element
   outside the group, a scalar out of range, a malformed byte tree, a
   missing file) is rejected before the certified verifier runs *)
let () =
  if Array.length Sys.argv < 3 then (prerr_endline "usage: main.exe protInfo.xml PROOF_DIRECTORY"; exit 2);
  try main () with
  | Failure msg -> Printf.printf "proof rejected by the parser: %s\n" msg; exit 1
  | Not_found | Invalid_argument _ -> print_endline "proof rejected by the parser: malformed data"; exit 1
  | Sys_error msg -> Printf.printf "proof rejected: %s\n" msg; exit 1
