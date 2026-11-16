(* Driver for the certified BBS# code (Examples/BBSSharpIns.v) at P-256 with
   SHA-256: issuance of a MAC_BBS credential, a verifiable presentation with
   selective disclosure (holder-binding proof, validity proof, and the
   Issuer's discrete-logarithm-equality proof that replaces the pairing
   check), its verification with the certified verifier, tamper tests and a
   benchmark. Both the prover and the verifier are the extracted Rocq code;
   this file draws the randomness, derives the public generators and
   computes the Fiat-Shamir challenges.

   There is no published BBS# test-vector suite or interoperable encoding
   (the paper specifies the protocol, not a wire format), so the challenges
   are computed here as in the IETF BBS draft: hash_to_scalar = OS2IP of
   expand_message_xmd (RFC 9380, SHA-256, 48 bytes) mod n, over the
   serialisation of the hashed values (points as uncompressed SEC1, scalars
   as 32-byte big-endian integers, octet strings with an 8-byte length),
   with a separate domain-separation tag for each of H_2, H_3, H_4. The
   generators g̃, g_0, g_1, ... are derived from SHA-256 by try-and-increment,
   as the U-Prove driver derives its scope element.

   usage: main.exe [N_ATTRIBUTES] [DISCLOSED] [ITERATIONS]   (default 10 1 50) *)
open BBSSharplib
open BBSSharplib.BBSSharpIns

type f = P256.P256.Zn.coq_F
type g = P256.P256.Wp.coq_G

let n = Z.of_string_base 16 "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551"
let p = Z.of_string_base 16 "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF"
let a_curve = Z.sub p (Z.of_int 3)
let b_curve = Z.of_string_base 16 "5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B"

(* ---- bytes, integers, points ---- *)

let z_of_bytes (s : string) : Z.t =
  String.fold_left (fun acc c -> Z.add (Z.shift_left acc 8) (Z.of_int (Char.code c))) Z.zero s

let bytes_of_z_fixed (z : Z.t) (len : int) : string =
  let s = Bytes.make len '\000' in
  let rec go z i = if i >= 0 && Z.sign z > 0 then begin
      Bytes.set s i (Char.chr (Z.to_int (Z.logand z (Z.of_int 255)))); go (Z.shift_right z 8) (i - 1) end in
  go z (len - 1); Bytes.to_string s

let sha256 (s : string) : string = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s
let xor (a : string) (b : string) : string =
  String.init (String.length a) (fun i -> Char.chr (Char.code a.[i] lxor Char.code b.[i]))

(* expand_message_xmd with SHA-256 (RFC 9380, section 5.3.1) *)
let expand_message_xmd (msg : string) (dst : string) (len : int) : string =
  let ell = (len + 31) / 32 in
  assert (ell <= 255 && String.length dst <= 255);
  let dst_prime = dst ^ String.make 1 (Char.chr (String.length dst)) in
  let z_pad = String.make 64 '\000' in
  let l_i_b_str = bytes_of_z_fixed (Z.of_int len) 2 in
  let b0 = sha256 (z_pad ^ msg ^ l_i_b_str ^ "\000" ^ dst_prime) in
  let b1 = sha256 (b0 ^ "\001" ^ dst_prime) in
  let rec go i prev acc =
    if i > ell then acc
    else let bi = sha256 (xor b0 prev ^ String.make 1 (Char.chr i) ^ dst_prime) in go (i + 1) bi (acc ^ bi) in
  String.sub (go 2 b1 b1) 0 len

let () =
  (* RFC 9380, Appendix K.1 *)
  let v = expand_message_xmd "" "QUUX-V01-CS02-with-expander-SHA256-128" 0x20 in
  assert (Z.format "%064x" (z_of_bytes v) = "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235");
  let v = expand_message_xmd "abc" "QUUX-V01-CS02-with-expander-SHA256-128" 0x20 in
  assert (Z.format "%064x" (z_of_bytes v) = "d8ccab23b5985ccea865c6c97b6e5b8350e794e603b4b97902f53a8a0d605615")

(* hash_to_scalar: 48 uniform bytes reduced modulo n (IETF BBS draft, section 4.2.2) *)
let hash_to_scalar (msg : string) (dst : string) : f =
  of_Z (Z.rem (z_of_bytes (expand_message_xmd msg dst 48)) n)

let point (x : Z.t) (y : Z.t) : g =
  match mk_G x y with Some pt -> pt | None -> failwith "not a point of the P-256 group"

(* serialisation for hashing *)
let ser_point (pt : g) : string =
  match point_to_Z pt with
  | Some (x, y) -> "\004" ^ bytes_of_z_fixed x 32 ^ bytes_of_z_fixed y 32
  | None -> failwith "point at infinity"
let ser_scalar (k : f) : string = bytes_of_z_fixed (to_Z k) 32
let ser_octets (s : string) : string = bytes_of_z_fixed (Z.of_int (String.length s)) 8 ^ s
let ser_int (i : int) : string = bytes_of_z_fixed (Z.of_int i) 8

(* a generator from a label, by try-and-increment on SHA-256 *)
let derive_generator (label : string) : g =
  let rec go counter =
    let x = Z.rem (z_of_bytes (sha256 ("BBS#-P256 generator|" ^ label ^ "|" ^ string_of_int counter))) p in
    let alpha = Z.rem (Z.add (Z.add (Z.mul x (Z.mul x x)) (Z.mul a_curve x)) b_curve) p in
    let y = Z.powm alpha (Z.div (Z.add p Z.one) (Z.of_int 4)) p in
    if Z.sign alpha <> 0 && Z.equal (Z.rem (Z.mul y y) p) alpha then point x (Z.min y (Z.sub p y))
    else go (counter + 1) in
  go 0

(* ---- randomness and vectors ---- *)

let rng = Cryptokit.Random.device_rng "/dev/urandom"
let rnd_scalar () : f =
  let buf = Bytes.create 64 in rng#random_bytes buf 0 64; of_Z (z_of_bytes (Bytes.to_string buf))
let rnd_nonzero () : f = let rec go () = let k = rnd_scalar () in if Z.sign (to_Z k) = 0 then go () else k in go ()
let rnd_bytes (k : int) : string = let buf = Bytes.create k in rng#random_bytes buf 0 k; Bytes.to_string buf

let bi = Big_int_Z.big_int_of_int
let rec vector_of_list (xs : 'a list) : 'a VectorDef.t =
  match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, bi (List.length t), vector_of_list t)
let rec list_of_vector (v : 'a VectorDef.t) : 'a list =
  match v with VectorDef.Coq_nil -> [] | VectorDef.Coq_cons (h, _, t) -> h :: list_of_vector t
let hd v = List.hd (list_of_vector v)

(* ---- the setting ---- *)

type setting = {
  nattr : int; ndisc : int;
  g_t : g; g0 : g; gens : g array;   (* g̃, g_0, g_1..g_n *)
  x : f; pk_i : g;                    (* Issuer key *)
  sk : f; pk : g;                     (* holder key *)
  attrs : f array;
}

let setup (nattr : int) (ndisc : int) : setting =
  let g_t = derive_generator "g~" and g0 = derive_generator "g0" in
  let gens = Array.init nattr (fun i -> derive_generator ("g" ^ string_of_int (i + 1))) in
  let x = rnd_nonzero () in
  let pk_i = P256.P256.Wp.gpow_fast g_t x in
  let sk = rnd_nonzero () in
  let pk = P256.P256.Wp.gpow_fast g sk in
  let attrs = Array.init nattr (fun i -> hash_to_scalar ("attribute " ^ string_of_int (i + 1)) "BBS#-P256-SHA256-MSG") in
  { nattr; ndisc; g_t; g0; gens; x; pk_i; sk; pk; attrs }

(* disclosed attributes are the first ndisc ones *)
let split st = 
  let d = st.ndisc and u = st.nattr - st.ndisc in
  let gD = vector_of_list (Array.to_list (Array.sub st.gens 0 d)) in
  let mD = vector_of_list (Array.to_list (Array.sub st.attrs 0 d)) in
  let gU = vector_of_list (Array.to_list (Array.sub st.gens d u)) in
  let mU = vector_of_list (Array.to_list (Array.sub st.attrs d u)) in
  (d, u, gD, mD, gU, mU)

(* ---- oracles ---- *)

let h2 (abar : g) (bbar : g) (g_t : g) (pk_i : g) (com1 : g) (com2 : g) : f =
  hash_to_scalar (String.concat "" (List.map ser_point [abar; bbar; g_t; pk_i; com1; com2])) "BBS#-P256-SHA256-H2-DLEQ"

let h3 (nonce : string) (pkb : g) (com : g) : f =
  hash_to_scalar (ser_octets nonce ^ ser_point pkb ^ ser_point com) "BBS#-P256-SHA256-H3-HB"

let h4 (nonce : string) (abar : g) (bbar : g) (dd : g) (pkb : g) (disclosed : (int * f) list) (coms : g VectorDef.t) : f =
  let parts = [ser_octets nonce; ser_point abar; ser_point bbar; ser_point dd; ser_point pkb; ser_int (List.length disclosed)]
    @ List.concat_map (fun (i, m) -> [ser_int i; ser_scalar m]) disclosed
    @ List.map ser_point (list_of_vector coms) in
  hash_to_scalar (String.concat "" parts) "BBS#-P256-SHA256-H4-VALIDITY"

(* ---- issuance ---- *)

type credential = { cm : g; a : g; e : f }

let issue (st : setting) : credential * bool =
  let (_, _, gD, mD, gU, mU) = split st in
  let cm = cm_ins (bi st.ndisc) (bi (st.nattr - st.ndisc)) st.g0 st.pk gD mD gU mU in
  let e = rnd_nonzero () in
  let a = mac_ins cm st.x e in
  (* the Issuer's proof that B = A^x (Remark 2 of the paper), checked with the certified verifier *)
  let b = mac_B_ins cm a e in
  let u = rnd_scalar () in
  let ann = (dleq_prove_ins st.g_t a st.x u (of_Z Z.zero)).Sigma.announcement in
  let com1 = List.nth (list_of_vector ann) 0 and com2 = List.nth (list_of_vector ann) 1 in
  let c = h2 a b st.g_t st.pk_i com1 com2 in
  let pf = dleq_prove_ins st.g_t a st.x u c in
  let ok = verify_dleq_ins (fun c1 c2 -> h2 a b st.g_t st.pk_i c1 c2) st.g_t st.pk_i a b c (hd pf.Sigma.response) in
  ({ cm; a; e }, ok)

(* ---- presentation ---- *)

type vp = {
  pr : (f, g) BBSSharpVerifier.presentation;
  nonce : string; disclosed : (int * f) list;
}

let present (st : setting) (cr : credential) (nonce : string) : vp =
  let (d, u, gD, mD, gU, mU) = split st in
  let disclosed = List.mapi (fun i m -> (i + 1, m)) (list_of_vector mD) in
  (* blind the key, randomise the credential *)
  let r = rnd_scalar () and r1 = rnd_nonzero () and r2 = rnd_nonzero () in
  let pkb = pk_blind_ins st.sk r in
  let abar = rand_A_ins cr.a r1 r2 in
  let dd = rand_D_ins cr.cm r2 in
  let bbar = rand_B_ins abar dd cr.e r1 in
  let r3 = P256.P256.Zn.inv r2 in
  let pp = target_P_ins (bi d) st.g0 pkb gD mD in
  (* π_HB *)
  let uh = rnd_scalar () in
  let com = hd (hb_prove_ins st.sk r uh (of_Z Z.zero)).Sigma.announcement in
  let hb_c = h3 nonce pkb com in
  let hb_r = hd (hb_prove_ins st.sk r uh hb_c).Sigma.response in
  (* π_validity *)
  let us = vector_of_list (List.init (4 + u) (fun _ -> rnd_scalar ())) in
  let coms = hd (validity_prove_ins (bi u) cr.e r1 r3 r mU abar dd gU bbar pp us (of_Z Z.zero)).Sigma.announcement in
  let c = h4 nonce abar bbar dd pkb disclosed coms in
  let rs = (validity_prove_ins (bi u) cr.e r1 r3 r mU abar dd gU bbar pp us c).Sigma.response in
  (* π_DLEQ from the Issuer on (Ā, B̄) *)
  let ud = rnd_scalar () in
  let ann = (dleq_prove_ins st.g_t abar st.x ud (of_Z Z.zero)).Sigma.announcement in
  let com1 = List.nth (list_of_vector ann) 0 and com2 = List.nth (list_of_vector ann) 1 in
  let dleq_c = h2 abar bbar st.g_t st.pk_i com1 com2 in
  let dleq_r = hd (dleq_prove_ins st.g_t abar st.x ud dleq_c).Sigma.response in
  { pr = mk_presentation_ins (bi d) (bi u) mD pkb hb_c hb_r abar bbar dd c rs dleq_c dleq_r; nonce; disclosed }

let verify (st : setting) (v : vp) : bool =
  let (d, u, gD, _, gU, _) = split st in
  let pr = v.pr in
  let abar = pr.BBSSharpVerifier.pr_Abar and bbar = pr.BBSSharpVerifier.pr_Bbar and dd = pr.BBSSharpVerifier.pr_D in
  let pkb = pr.BBSSharpVerifier.pr_pkB in
  let disclosed = List.mapi (fun i m -> (i + 1, m)) (list_of_vector pr.BBSSharpVerifier.pr_mD) in
  verify_presentation_ins (bi d) (bi u)
    (fun c1 c2 -> h2 abar bbar st.g_t st.pk_i c1 c2)
    (fun com -> h3 v.nonce pkb com)
    (fun coms -> h4 v.nonce abar bbar dd pkb disclosed coms)
    st.g_t st.g0 st.pk_i gD gU pr

(* ---- tampering ---- *)

let plus_one (k : f) : f = of_Z (Z.add (to_Z k) Z.one)
let with_pr v pr = { v with pr }
let tampers (st : setting) (v : vp) : (string * vp) list =
  let pr = v.pr in
  let open BBSSharpVerifier in
  let rs = list_of_vector pr.pr_rs in
  let bump i = vector_of_list (List.mapi (fun j r -> if j = i then plus_one r else r) rs) in
  [ "validity response rho_1 + 1", with_pr v { pr with pr_rs = bump 0 };
    "validity response resp + 1", with_pr v { pr with pr_rs = bump 3 };
    "holder-binding response + 1", with_pr v { pr with pr_hb_r = plus_one pr.pr_hb_r };
    "DLEQ response + 1", with_pr v { pr with pr_dleq_r = plus_one pr.pr_dleq_r };
    "disclosed attribute + 1", with_pr v { pr with pr_mD = vector_of_list (List.map plus_one (list_of_vector pr.pr_mD)) };
    "B-bar replaced by A-bar", with_pr v { pr with pr_Bbar = pr.pr_Abar };
    "pk_Blind replaced by g", with_pr v { pr with pr_pkB = g };
    "A-bar replaced by the identity", with_pr v { pr with pr_Abar = P256.P256.Wp.gid; pr_Bbar = P256.P256.Wp.gid };
    "different nonce", { v with nonce = v.nonce ^ "!" };
    "other Issuer key", v ]

let time_it f = let t0 = Unix.gettimeofday () in let r = f () in (r, (Unix.gettimeofday () -. t0) *. 1000.)

let () =
  let nattr = try int_of_string Sys.argv.(1) with _ -> 10 in
  let ndisc = try int_of_string Sys.argv.(2) with _ -> 1 in
  let iters = try int_of_string Sys.argv.(3) with _ -> 50 in
  Printf.printf "BBS# at P-256 / SHA-256: %d attributes, %d disclosed\n" nattr ndisc;
  let st = setup nattr ndisc in
  let (cr, issuance_ok) = issue st in
  Printf.printf "issuance: MAC_BBS credential (A, e) issued; Issuer's DLEQ proof B = A^x verified: %b\n" issuance_ok;
  let nonce = rnd_bytes 16 in
  let (v, tgen) = time_it (fun () -> present st cr nonce) in
  let (ok, tver) = time_it (fun () -> verify st v) in
  Printf.printf "presentation: generated in %.1f ms, certified verification: %b in %.1f ms\n" tgen ok tver;
  print_endline "--- tampered presentations (every line must show false) ---";
  let other = setup nattr ndisc in
  let results = List.map (fun (name, v') ->
      let r = if name = "other Issuer key" then verify { st with pk_i = other.pk_i } v' else verify st v' in
      Printf.printf "%-34s %b\n" name r; r) (tampers st v) in
  let rejected = List.for_all (fun r -> not r) results in
  Printf.printf "all tampered presentations rejected: %b\n" rejected;
  (* benchmark *)
  let gens = List.init iters (fun _ -> snd (time_it (fun () -> present st cr nonce))) in
  let vers = List.init iters (fun _ -> snd (time_it (fun () -> assert (verify st v)))) in
  let med xs = let s = List.sort compare xs in List.nth s (List.length s / 2) in
  Printf.printf "benchmark over %d iterations (median): presentation %.1f ms, verification %.1f ms\n"
    iters (med gens) (med vers);
  if not (issuance_ok && ok && rejected) then exit 1
