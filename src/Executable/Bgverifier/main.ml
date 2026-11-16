(* Driver for the certified Bayer–Groth shuffle verifier
   (Examples/BayerGrothIns.v, Backend/BayerGrothVerifier.v) on the test
   vectors of the Swiss Post crypto-primitives library (data/*.json,
   specification 1.6.0, Section 9), at the 3072-bit group p = 2q + 1, g = 2.

   The fixtures are parsed with the grammar of parsing/ (parser.mly,
   lexer.mll; ast.ml decodes the Base64 values of Java BigInteger byte
   arrays and checks that every group element is in the subgroup of order q
   and every exponent below q). The driver computes the RecursiveHash
   challenges (SHA3-256, Section 3 of the specification: prefixes 0x00 byte
   array, 0x01 integer as minimal big-endian bytes, 0x02 string, 0x03 list of
   hashes) as closures over the public parameters and the statement, and
   hands everything to the certified verifiers. It checks the challenges x,
   y, z of the shuffle fixtures against the values recorded in the fixtures,
   verifies every case of the six fixture files, rejects tampered arguments,
   and finally runs the extracted honest prover on fresh ciphertexts and
   verifies its argument with the same verifier.

   usage: main.exe [DATA_DIR]
          main.exe --diff FILE   (differential testing, bench/swisspost-diff)
          main.exe --gen FILE M,N,L ...   (cases from the extracted prover, same)
          main.exe --diff-sub KIND FILE   (sub-arguments, bench/swisspost-diff/forge.py) *)
open BayerGrothlib
open BayerGrothlib.BayerGrothIns
open Bg_parser
open Bg_parser.Ast
module List = Stdlib.List
module String = Stdlib.String

(* the constants take the (erased) primality hypotheses as a dummy argument *)
let fone : f = coq_Fone

(* ---- bytes and integers ---- *)

(* minimal big-endian encoding, 0 as the empty string (IntegerToByteArray) *)
let bytes_of_z (z : Z.t) : string =
  if Z.sign z = 0 then "" else begin
    let n = (Z.numbits z + 7) / 8 in
    let s = Bytes.make n '\000' in
    let rec go z i = if i >= 0 && Z.sign z > 0 then begin
        Bytes.set s i (Char.chr (Z.to_int (Z.logand z (Z.of_int 255)))); go (Z.shift_right z 8) (i - 1) end in
    go z (n - 1); Bytes.to_string s end

(* ---- RecursiveHash (specification 1.6.0, Algorithm 3.5) ---- *)

let sha3_256 (s : string) : string = Cryptokit.hash_string (Cryptokit.Hash.sha3 256) s
let () =
  assert (Z.format "%064x" (z_of_bytes (sha3_256 "")) =
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")

type hashable = B of string | I of Z.t | S of string | L of hashable list

let rec rh (v : hashable) : string =
  match v with
  | B b -> sha3_256 ("\000" ^ b)
  | I z -> sha3_256 ("\001" ^ bytes_of_z z)
  | S s -> sha3_256 ("\002" ^ s)
  | L vs -> sha3_256 ("\003" ^ String.concat "" (List.map rh vs))

(* recursiveHash(v_1, …, v_k) with k ≥ 2 hashes the list; the 256-bit value is
   below the 3071-bit q, so it is an exponent as such *)
let challenge (vs : hashable list) : f = of_Z (z_of_bytes (rh (L vs)))

let he (x : g) : hashable = I (elem_to_Z x)
let hf (x : f) : hashable = I (to_Z x)
let hl (xs : g list) : hashable = L (List.map he xs)
let hct (c : g VectorDef.t) : hashable = hl (list_of_vector c)
let hcl (cs : g VectorDef.t list) : hashable = L (List.map hct cs)
let hmat (rows : g VectorDef.t list list) : hashable = L (List.map hcl rows)

(* ---- the context: (p, q, pk, ck) ---- *)

let base (c : ctx) : hashable list = [I p; I q; hl c.pk; L (he c.h :: List.map he c.gs)]

(* the oracles for a shuffle statement (C, C'); the sub-argument oracles do
   not depend on the statement *)
let oracles (c : ctx) (l : int) (cs : g VectorDef.t list) (cs' : g VectorDef.t list) =
  let stmt = [hcl cs; hcl cs'] in
  mk_oracles (bi l)
    (fun cA -> challenge (base c @ stmt @ [hl cA]))
    (fun cA cB -> challenge (hl cB :: base c @ stmt @ [hl cA]))
    (fun cA cB -> challenge (S "1" :: hl cB :: base c @ stmt @ [hl cA]))
    (fun cA cb cB -> challenge (base c @ [hl cA; he cb; hl cB]))
    (fun cA cb cB -> challenge (S "1" :: base c @ [hl cA; he cb; hl cB]))
    (fun cA0 cBm cd cB cA -> challenge (base c @ [he cA0; he cBm; hl cd; hl cB; hl cA]))
    (fun cDelta cdelta cd b ca -> challenge (base c @ [he cDelta; he cdelta; he cd; hf b; he ca]))
    (fun rows cc cA cA0 cB e -> challenge (base c @ [hmat rows; hct cc; hl cA; he cA0; hl cB; hcl e]))

(* ---- parsing a fixture file ---- *)

let parse_file (file : string) (start : (Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> 'a) : 'a =
  let ic = open_in_bin file in
  let s = really_input_string ic (in_channel_length ic) in close_in ic;
  let lexbuf = Lexing.from_string s in
  try start Lexer.token lexbuf with
  | Lexer.SyntaxError msg -> failwith (Printf.sprintf "%s: %s at offset %d" file msg (Lexing.lexeme_start lexbuf))
  | Parser.Error -> failwith (Printf.sprintf "%s: syntax error at offset %d" file (Lexing.lexeme_start lexbuf))
  | Failure msg -> failwith (file ^ ": " ^ msg)

(* the context of a case: the certified group, and l = |pk| *)
let context (t : 'a case) : ctx * int =
  let c = t.context in
  if not (Z.equal c.c_p p && Z.equal c.c_q q && Z.equal c.c_g (Z.of_int 2))
  then failwith "the fixture is not at the certified 3072-bit group";
  (c, List.length c.pk)

(* ---- running the fixtures ---- *)

let time_it f = let t0 = Unix.gettimeofday () in let r = f () in (r, (Unix.gettimeofday () -. t0) *. 1000.)
let results = ref []   (* (name, ok) *)
let record name (ok : bool) (expected : bool) ms =
  Printf.printf "  %-56s %-8s (expected %-5b) %8.1f ms\n" name (if ok then "accepted" else "rejected") expected ms;
  results := (name, ok = expected) :: !results

let desc (t : 'a case) = t.description
let expected (t : 'a case) = t.output.result
let same (recorded : Z.t option) (v : f) = match recorded with Some z -> Z.equal (to_Z v) z | None -> false

let run_shuffle dir =
  Printf.printf "verify-shuffle-argument.json (Algorithm 9.12)\n";
  List.iter (fun t ->
    let c, l = context t in
    let (st, sa) = t.input in
    let cs = st.ciphertexts and cs' = st.shuffled in
    let arg = to_shuffle l sa in
    let m = List.length sa.sh_ca in
    let nn = List.length cs in
    if nn mod m <> 0 then failwith "N is not a multiple of m";
    let n = nn / m in
    let o = oracles c l cs cs' in
    (* the challenges recorded in the fixture *)
    let cA = sa.sh_ca and cB = sa.sh_cb in
    let x = o.BayerGrothVerifier.o_x cA and y = o.BayerGrothVerifier.o_y cA cB and z = o.BayerGrothVerifier.o_z cA cB in
    let sx = same t.output.out_x x and sy = same t.output.out_y y and sz = same t.output.out_z z in
    Printf.printf "  %s: recomputed challenges x, y, z match the fixture: %b %b %b\n" (desc t) sx sy sz;
    results := (desc t ^ " challenges", sx && sy && sz) :: !results;
    (* the arguments commit to vectors of length n with the first n generators of the key *)
    let gs = List.filteri (fun i _ -> i < n) c.gs in
    let ok, ms = time_it (fun () -> shuffle_verify_fs_ins (bi l) o c.h gs (elem (Z.of_int 2)) (vector_of_list c.pk) (bi m) (bi n) cs cs' arg) in
    record (desc t) ok (expected t) ms;
    (* tampered arguments *)
    let tamper name arg' cs'' =
      let ok, ms = time_it (fun () -> shuffle_verify_fs_ins (bi l) (oracles c l cs cs'') c.h gs (elem (Z.of_int 2)) (vector_of_list c.pk) (bi m) (bi n) cs cs'' arg') in
      record ("  tamper: " ^ name) ok false ms in
    let swap xs = match xs with a :: b :: r -> b :: a :: r | _ -> xs in
    tamper "two shuffled ciphertexts swapped" arg (swap cs');
    let g2 = elem (Z.of_int 2) in
    tamper "c_A[0] multiplied by g" { arg with BayerGroth.sh_cA = (coq_Gmul g2 (List.hd arg.BayerGroth.sh_cA) :: List.tl arg.BayerGroth.sh_cA) } cs';
    let me = arg.BayerGroth.sh_mexp in
    tamper "multi-exponentiation response r + 1" { arg with BayerGroth.sh_mexp = { me with BayerGroth.me_r = coq_Fadd me.BayerGroth.me_r fone } } cs';
    let pa = arg.BayerGroth.sh_prod in
    let sv = pa.BayerGroth.pa_svp in
    tamper "single value product response r~ + 1"
      { arg with BayerGroth.sh_prod = { pa with BayerGroth.pa_svp = { sv with BayerGroth.svp_r = coq_Fadd sv.BayerGroth.svp_r fone } } } cs';
    if m = 1 then
      tamper "wrong re-encryption of C'[0]" arg (reenc_ins (bi l) g2 (vector_of_list c.pk) fone (List.hd cs') :: List.tl cs'))
    (parse_file (Filename.concat dir "verify-shuffle-argument.json") Parser.shuffle_cases)

let run_product dir =
  Printf.printf "verify-product-argument.json (Algorithm 9.19)\n";
  List.iter (fun t ->
    let c, l = context t in
    let (st, arg) = t.input in
    let cA = st.p_ca and b = st.p_b in
    let n = List.length c.gs in
    let o = oracles c l [] [] in
    let ok, ms = time_it (fun () -> product_verify_fs_ins (bi l) o c.h c.gs (bi n) cA b arg) in
    record (desc t) ok (expected t) ms;
    let ok, ms = time_it (fun () -> product_verify_fs_ins (bi l) o c.h c.gs (bi n) cA (coq_Fadd b fone) arg) in
    record "  tamper: statement b + 1" ok false ms)
    (parse_file (Filename.concat dir "verify-product-argument.json") Parser.product_cases)

let run_hadamard dir =
  Printf.printf "verify-hadamard-argument.json (Algorithm 9.21)\n";
  List.iter (fun t ->
    let c, l = context t in
    let (st, arg) = t.input in
    let cA = st.h_ca and cb = st.h_cb in
    let n = List.length c.gs in
    let o = oracles c l [] [] in
    let x = o.BayerGrothVerifier.o_xh cA cb arg.BayerGroth.ha_cB and y = o.BayerGrothVerifier.o_yh cA cb arg.BayerGroth.ha_cB in
    let sx = same t.output.out_x x and sy = same t.output.out_y y in
    results := (desc t ^ " challenges", sx && sy) :: !results;
    let ok, ms = time_it (fun () -> hadamard_verify_fs_ins (bi l) o c.h c.gs (bi n) cA cb arg) in
    record (Printf.sprintf "%s (x, y match: %b %b)" (desc t) sx sy) ok (expected t) ms;
    let za = arg.BayerGroth.ha_zero in
    let ok, ms = time_it (fun () -> hadamard_verify_fs_ins (bi l) o c.h c.gs (bi n) cA cb
      { arg with BayerGroth.ha_zero = { za with BayerGroth.za_t = coq_Fadd za.BayerGroth.za_t fone } }) in
    record "  tamper: zero argument response t + 1" ok false ms)
    (parse_file (Filename.concat dir "verify-hadamard-argument.json") Parser.hadamard_cases)

let run_zero dir =
  Printf.printf "verify-zero-argument.json (Algorithm 9.23)\n";
  List.iter (fun t ->
    let c, l = context t in
    let (st, arg) = t.input in
    let cA = st.z_ca and cB = st.z_cb and y = st.z_y in
    let o = oracles c l [] [] in
    let x = o.BayerGrothVerifier.o_xz arg.BayerGroth.za_cA0 arg.BayerGroth.za_cBm arg.BayerGroth.za_cd cB cA in
    let samex = same t.output.out_x x in
    results := (desc t ^ " challenge", samex) :: !results;
    let ok, ms = time_it (fun () -> zero_verify_fs_ins (bi l) o c.h c.gs cA cB y arg) in
    record (Printf.sprintf "%s (x matches: %b)" (desc t) samex) ok (expected t) ms;
    let ok, ms = time_it (fun () -> zero_verify_fs_ins (bi l) o c.h c.gs cA cB (coq_Fadd y fone) arg) in
    record "  tamper: statement y + 1" ok false ms)
    (parse_file (Filename.concat dir "verify-zero-argument.json") Parser.zero_cases)

let run_svp dir =
  Printf.printf "verify-single-value-product-argument.json (Algorithm 9.26)\n";
  List.iter (fun t ->
    let c, l = context t in
    let (st, arg) = t.input in
    let ca = st.s_ca and b = st.s_b in
    let o = oracles c l [] [] in
    let x = o.BayerGrothVerifier.o_xs arg.BayerGroth.svp_cDelta arg.BayerGroth.svp_cdelta arg.BayerGroth.svp_cd b ca in
    let samex = same t.output.out_x x in
    results := (desc t ^ " challenge", samex) :: !results;
    let ok, ms = time_it (fun () -> svp_verify_fs_ins (bi l) o c.h c.gs ca b arg) in
    record (Printf.sprintf "%s (x matches: %b)" (desc t) samex) ok (expected t) ms;
    let ok, ms = time_it (fun () -> svp_verify_fs_ins (bi l) o c.h c.gs ca b { arg with BayerGroth.svp_s = coq_Fadd arg.BayerGroth.svp_s fone }) in
    record "  tamper: response s~ + 1" ok false ms)
    (parse_file (Filename.concat dir "verify-single-value-product-argument.json") Parser.svp_cases)

let run_multiexp dir =
  Printf.printf "verify-multiexp-argument.json (Algorithm 9.16)\n";
  List.iter (fun t ->
    let c, l = context t in
    let (st, ma) = t.input in
    let rows = st.m_rows and cc = st.m_product and cA = st.m_ca in
    let arg = to_mexp l ma in
    let o = oracles c l [] [] in
    let x = o.BayerGrothVerifier.o_xm rows cc cA arg.BayerGroth.me_cA0 arg.BayerGroth.me_cB arg.BayerGroth.me_E in
    let samex = same t.output.out_x x in
    results := (desc t ^ " challenge", samex) :: !results;
    let g2 = elem (Z.of_int 2) in
    let ok, ms = time_it (fun () -> multiexp_verify_fs_ins (bi l) o c.h c.gs g2 (vector_of_list c.pk) rows cc cA arg) in
    record (Printf.sprintf "%s (x matches: %b)" (desc t) samex) ok (expected t) ms;
    let ok, ms = time_it (fun () -> multiexp_verify_fs_ins (bi l) o c.h c.gs g2 (vector_of_list c.pk) rows
      (reenc_ins (bi l) g2 (vector_of_list c.pk) fone cc) cA arg) in
    record "  tamper: statement C re-encrypted" ok false ms)
    (parse_file (Filename.concat dir "verify-multiexp-argument.json") Parser.mexp_cases)

(* ---- the extracted honest prover on fresh ciphertexts ---- *)

let rng = Cryptokit.Random.device_rng "/dev/urandom"
let rnd_z (bytes : int) : Z.t = let buf = Bytes.create bytes in rng#random_bytes buf 0 bytes; z_of_bytes (Bytes.to_string buf)
let rnd_scalar () : f = of_Z (Z.rem (rnd_z 448) q)
let rnd_scalars k = List.init k (fun _ -> rnd_scalar ())
let g2 : g = elem (Z.of_int 2)
let rnd_elem () : g = coq_Gpow g2 (rnd_scalar ())
(* Fisher–Yates *)
let rnd_perm (n : int) : int list =
  let a = Array.init n (fun i -> i) in
  for i = n - 1 downto 1 do
    let j = Z.to_int (Z.rem (rnd_z 8) (Z.of_int (i + 1))) in
    let t = a.(i) in a.(i) <- a.(j); a.(j) <- t
  done; Array.to_list a

let demo (m : int) (n : int) (l : int) =
  let nn = m * n in
  let pk = List.init l (fun _ -> rnd_elem ()) and h = rnd_elem () and gs = List.init n (fun _ -> rnd_elem ()) in
  let c = { c_p = p; c_q = q; c_g = Z.of_int 2; pk; h; gs } in
  let pkv = vector_of_list pk in
  let cs = List.init nn (fun _ -> enc_ins (bi l) g2 pkv (vector_of_list (List.init l (fun _ -> rnd_elem ()))) (rnd_scalar ())) in
  let perm = rnd_perm nn in
  let rhos = rnd_scalars nn in
  let cs' = List.mapi (fun i pi -> reenc_ins (bi l) g2 pkv (List.nth rhos i) (List.nth cs pi)) perm in
  let o = oracles c l cs cs' in
  let arg, tprove = time_it (fun () ->
    shuffle_prove_fs_ins (bi l) o h gs g2 pkv (bi m) (bi n) cs cs' (List.map bi perm) rhos
      (rnd_scalars m) (rnd_scalars m) (rnd_scalar ()) (rnd_scalars (max 0 (m - 2)))
      (rnd_scalars n) (rnd_scalars n) (rnd_scalar ()) (rnd_scalar ()) (rnd_scalars (m + 1)) (rnd_scalars (m - 1))
      (rnd_scalars n) (rnd_scalar ()) (rnd_scalars (max 0 (n - 2))) (rnd_scalar ()) (rnd_scalar ())
      (rnd_scalars n) (rnd_scalar ()) (rnd_scalars (2 * m)) (rnd_scalars (2 * m)) (rnd_scalars (2 * m))) in
  let ok, tver = time_it (fun () -> shuffle_verify_fs_ins (bi l) o h gs g2 pkv (bi m) (bi n) cs cs' arg) in
  Printf.printf "  m=%d, n=%d, l=%d: extracted prover %.1f ms, certified verifier %s in %.1f ms\n" m n l tprove
    (if ok then "accepted" else "rejected") tver;
  results := (Printf.sprintf "demo m=%d n=%d l=%d" m n l, ok) :: !results;
  let bad = List.mapi (fun i pi -> reenc_ins (bi l) g2 pkv (List.nth rhos i) (List.nth cs (if i = 0 then List.nth perm 1 else if i = 1 then List.nth perm 0 else pi))) perm in
  let ok', _ = time_it (fun () -> shuffle_verify_fs_ins (bi l) (oracles c l cs bad) h gs g2 pkv (bi m) (bi n) cs bad arg) in
  Printf.printf "  tamper: argument replayed on a different shuffle: %s\n" (if ok' then "accepted" else "rejected");
  results := ("demo tamper", not ok') :: !results

(* ---- cases from the extracted prover, for differential testing ---- *)

(* Java BigInteger.toByteArray: minimal two's complement, 0 as one zero byte *)
let b64_of_z (z : Z.t) : string =
  let b = bytes_of_z z in
  let b = if b = "" || Char.code b.[0] >= 0x80 then "\000" ^ b else b in
  "\"" ^ Cryptokit.transform_string (Cryptokit.Base64.encode_compact_pad ()) b ^ "\""

let js_list f xs = "[" ^ String.concat "," (List.map f xs) ^ "]"
let js_e (x : g) = b64_of_z (elem_to_Z x)
let js_f (x : f) = b64_of_z (to_Z x)
let js_ct (c : g VectorDef.t) = match list_of_vector c with
  | gamma :: phis -> Printf.sprintf "{\"gamma\":%s,\"phis\":%s}" (js_e gamma) (js_list js_e phis)
  | [] -> failwith "empty ciphertext"

let js_shuffle (a : (f, g) BayerGroth.shuffle_argument) : string =
  let open BayerGroth in
  let svp = a.sh_prod.pa_svp and me = a.sh_mexp in
  let svp_s = Printf.sprintf "{\"c_d\":%s,\"c_lower_delta\":%s,\"c_upper_delta\":%s,\"a_tilde\":%s,\"b_tilde\":%s,\"r_tilde\":%s,\"s_tilde\":%s}"
      (js_e svp.svp_cd) (js_e svp.svp_cdelta) (js_e svp.svp_cDelta) (js_list js_f svp.svp_a) (js_list js_f svp.svp_b)
      (js_f svp.svp_r) (js_f svp.svp_s) in
  let had = match a.sh_prod.pa_had with
    | None -> ""
    | Some h -> let z = h.ha_zero in
      Printf.sprintf "\"c_b\":%s,\"hadamard_argument\":{\"cUpperB\":%s,\"zero_argument\":{\"c_a0\":%s,\"c_bm\":%s,\"c_d\":%s,\"a\":%s,\"b\":%s,\"r\":%s,\"s\":%s,\"t\":%s}},"
        (js_e a.sh_prod.pa_cb) (js_list js_e h.ha_cB) (js_e z.za_cA0) (js_e z.za_cBm) (js_list js_e z.za_cd)
        (js_list js_f z.za_a) (js_list js_f z.za_b) (js_f z.za_r) (js_f z.za_s) (js_f z.za_t) in
  Printf.sprintf "{\"ca\":%s,\"cb\":%s,\"product_argument\":{%s\"single_vpa\":%s},\"multi_exp_argument\":{\"c_a_0\":%s,\"c_b\":%s,\"a\":%s,\"e\":%s,\"r\":%s,\"b\":%s,\"s\":%s,\"tau\":%s}}"
    (js_list js_e a.sh_cA) (js_list js_e a.sh_cB) had svp_s (js_e me.me_cA0) (js_list js_e me.me_cB) (js_list js_f me.me_a)
    (js_list js_ct me.me_E) (js_f me.me_r) (js_f me.me_b) (js_f me.me_s) (js_f me.me_tau)

let js_case (desc : string) (c : ctx) (cs : ct list) (cs' : ct list) (arg : (f, g) BayerGroth.shuffle_argument) : string =
  Printf.sprintf "{\"description\":%S,\"context\":{\"p\":%s,\"q\":%s,\"g\":%s,\"pk\":%s,\"ck\":{\"h\":%s,\"g\":%s}},\"input\":{\"statement\":{\"ciphertexts\":%s,\"shuffled_ciphertexts\":%s},\"argument\":%s},\"output\":{\"result\":true}}"
    desc (b64_of_z p) (b64_of_z q) (b64_of_z (Z.of_int 2)) (js_list js_e c.pk) (js_e c.h) (js_list js_e c.gs)
    (js_list js_ct cs) (js_list js_ct cs') (js_shuffle arg)

(* the prover's random values (21 groups, as in demo) from [r k], a list of k exponents *)
let prove_with c l m n cs cs' perm rhos (r : int -> f list) =
  let r1 () = List.hd (r 1) in
  shuffle_prove_fs_ins (bi l) (oracles c l cs cs') c.h c.gs g2 (vector_of_list c.pk) (bi m) (bi n) cs cs' (List.map bi perm) rhos
    (r m) (r m) (r1 ()) (r (max 0 (m - 2)))
    (r n) (r n) (r1 ()) (r1 ()) (r (m + 1)) (r (m - 1))
    (r n) (r1 ()) (r (max 0 (n - 2))) (r1 ()) (r1 ())
    (r n) (r1 ()) (r (2 * m)) (r (2 * m)) (r (2 * m))

(* for each shape: honest arguments (the statement is a shuffle and the witness
   a permutation: both verifiers must accept), with degenerate randomness or
   statements, and cheating ones (the prover runs on a witness that does not
   explain the statement; every challenge is still derived from the
   transcript, so verification reaches the algebraic checks: both must
   reject); the description ends with the expected verdict *)
let gen_cases (m : int) (n : int) (l : int) : string list =
  let nn = m * n in
  let fzero = of_Z Z.zero in
  let c = { c_p = p; c_q = q; c_g = Z.of_int 2; pk = List.init l (fun _ -> rnd_elem ()); h = rnd_elem (); gs = List.init n (fun _ -> rnd_elem ()) } in
  let pkv = vector_of_list c.pk in
  let enc msg r = enc_ins (bi l) g2 pkv (vector_of_list msg) r in
  let rnd_cts () = List.init nn (fun _ -> enc (List.init l (fun _ -> rnd_elem ())) (rnd_scalar ())) in
  let shuffle cs perm rhos = List.mapi (fun i pi -> reenc_ins (bi l) g2 pkv (List.nth rhos i) (List.nth cs pi)) perm in
  let case kind ?(r = rnd_scalars) ?(cs = rnd_cts ()) ?(perm = rnd_perm nn) ?(rhos = rnd_scalars nn) ?stmt_perm ?stmt_rhos ?(edit = Fun.id) expect =
    (* the statement is shuffled with stmt_perm/stmt_rhos (default: the witness) and edited *)
    let cs' = edit (shuffle cs (Option.value stmt_perm ~default:perm) (Option.value stmt_rhos ~default:rhos)) in
    let arg = prove_with c l m n cs cs' perm rhos r in
    Printf.eprintf "generated m=%d n=%d l=%d %s\n%!" m n l kind;
    js_case (Printf.sprintf "3072-bits, m=%d, n=%d, l=%d, ocaml %s, expect %s" m n l kind expect) c cs cs' arg in
  let perm = rnd_perm nn in
  let not_perm = List.mapi (fun i x -> if i = 0 then List.nth perm 1 else x) perm in
  let one_ct = enc (List.init l (fun _ -> rnd_elem ())) (rnd_scalar ()) in
  let times_g_phi0 cs' = match cs' with
    | c0 :: rest -> (match list_of_vector c0 with
        | gamma :: phi :: phis -> vector_of_list (gamma :: coq_Gmul g2 phi :: phis) :: rest | _ -> cs')
    | [] -> cs' in
  [ case "honest" "accept";
    case "honest, prover randomness 0" ~r:(fun k -> List.init k (fun _ -> fzero)) "accept";
    case "honest, prover randomness 1" ~r:(fun k -> List.init k (fun _ -> fone)) "accept";
    case "honest, identity permutation" ~perm:(List.init nn Fun.id) "accept";
    case "honest, no re-encryption" ~rhos:(List.init nn (fun _ -> fzero)) "accept";
    case "honest, identity ciphertexts" ~cs:(List.init nn (fun _ -> enc (List.init l (fun _ -> coq_Gone)) fzero)) "accept";
    case "honest, all ciphertexts equal" ~cs:(List.init nn (fun _ -> one_ct)) "accept";
    case "cheat, witness not a permutation" ~perm:not_perm "reject";
    (let rhos = rnd_scalars nn in
     case "cheat, statement re-encrypted with rho_0 + 1" ~perm ~rhos
       ~stmt_rhos:(List.mapi (fun i r -> if i = 0 then coq_Fadd r fone else r) rhos) "reject");
    case "cheat, plaintext of C'_0 times g" ~edit:times_g_phi0 "reject";
    (let rec other () = let p' = rnd_perm nn in if p' = perm then other () else p' in
     case "cheat, statement is another shuffle" ~perm ~stmt_perm:(other ()) "reject");
    case "non-permutation witness of a true statement (all ciphertexts equal)" ~cs:(List.init nn (fun _ -> one_ct)) ~perm:not_perm "either" ]

let run_gen file shapes =
  let cases = List.concat_map (fun s -> match List.map int_of_string (String.split_on_char ',' s) with
    | [m; n; l] -> gen_cases m n l | _ -> failwith ("not M,N,L: " ^ s)) shapes in
  let oc = open_out_bin file in
  output_string oc ("[\n" ^ String.concat ",\n" cases ^ "\n]\n"); close_out oc;
  exit 0

(* the same for the sub-arguments (bench/swisspost-diff/forge.py), on files
   in the format of verify-KIND-argument.json; the commitment key is used
   whole, as in the run_* functions above *)
let run_diff_sub kind file =
  let bad = ref 0 in
  let report i t ok =
    let agree = ok = expected t in
    if not agree then incr bad;
    Printf.printf "%d\t%b\t%b\t%s\t%s\n%!" i ok (expected t) (if agree then "agree" else "DISAGREE") (desc t) in
  let go start verify = List.iteri (fun i t -> let c, l = context t in report i t (verify c l (oracles c l [] []) (fst t.input) (snd t.input)))
      (parse_file file start) in
  (match kind with
   | "zero" -> go Parser.zero_cases (fun c l o st arg -> zero_verify_fs_ins (bi l) o c.h c.gs st.z_ca st.z_cb st.z_y arg)
   | "svp" -> go Parser.svp_cases (fun c l o st arg -> svp_verify_fs_ins (bi l) o c.h c.gs st.s_ca st.s_b arg)
   | "hadamard" -> go Parser.hadamard_cases (fun c l o st arg ->
       hadamard_verify_fs_ins (bi l) o c.h c.gs (bi (List.length c.gs)) st.h_ca st.h_cb arg)
   | "product" -> go Parser.product_cases (fun c l o st arg ->
       product_verify_fs_ins (bi l) o c.h c.gs (bi (List.length c.gs)) st.p_ca st.p_b arg)
   | "multiexp" -> go Parser.mexp_cases (fun c l o st ma ->
       multiexp_verify_fs_ins (bi l) o c.h c.gs g2 (vector_of_list c.pk) st.m_rows st.m_product st.m_ca (to_mexp l ma))
   | _ -> failwith ("unknown kind " ^ kind));
  exit (if !bad = 0 then 0 else 1)

(* differential testing (bench/swisspost-diff): every case of a file in the
   format of verify-shuffle-argument.json, whose output.result is the verdict
   of the Swiss Post verifier, is verified and the verdicts are compared; the
   challenges are compared when the file records them *)
let run_diff file =
  let cases = parse_file file Parser.shuffle_cases in
  let bad = ref 0 in
  List.iteri (fun i t ->
    let c, k = context t in
    let (st, sa) = t.input in
    let cs = st.ciphertexts and cs' = st.shuffled in
    (* the shapes the extracted verifier relies on (its ciphertexts are
       vectors of length l + 1); the key may be longer than the ciphertexts
       (l <= k): all of it is hashed, its first l elements encrypt, as in
       MultiExponentiationArgumentService *)
    let len (v : ct) = List.length (list_of_vector v) in
    let l = match cs with x :: _ -> len x - 1 | [] -> 0 in
    let m = List.length sa.sh_ca and nn = List.length cs in
    let shape_error =
      if l < 1 || l > k then Some "ciphertext size not in [1, k]"
      else if List.exists (fun x -> len x <> l + 1) (cs @ cs' @ sa.sh_mexp.me_e) then Some "ciphertexts of different sizes"
      else if List.length cs' <> nn then Some "|C'| <> |C|"
      else if m < 1 || nn mod m <> 0 then Some "N is not a multiple of m"
      else if nn / m < 2 || nn / m > List.length c.gs then Some "n not in [2, |ck|]"
      else None in
    match shape_error with
    | Some e ->
      if expected t then incr bad;
      Printf.printf "%d\tfalse\t%b\t%s\t%s (shape: %s)\n%!" i (expected t) (if expected t then "DISAGREE" else "agree") (desc t) e
    | None ->
    let arg = to_shuffle l sa in
    let n = nn / m in
    let o = oracles c l cs cs' in
    let pkl = List.filteri (fun j _ -> j < l) c.pk in
    let chal = match t.output.out_x with
      | None -> true
      | Some _ ->
        let cA = sa.sh_ca and cB = sa.sh_cb in
        same t.output.out_x (o.BayerGrothVerifier.o_x cA) && same t.output.out_y (o.BayerGrothVerifier.o_y cA cB)
        && same t.output.out_z (o.BayerGrothVerifier.o_z cA cB) in
    let gs = List.filteri (fun i _ -> i < n) c.gs in
    let ok = shuffle_verify_fs_ins (bi l) o c.h gs (elem (Z.of_int 2)) (vector_of_list pkl) (bi m) (bi n) cs cs' arg in
    let agree = ok = expected t && chal in
    if not agree then incr bad;
    Printf.printf "%d\t%b\t%b\t%s\t%s\n%!" i ok (expected t)
      (if agree then "agree" else if chal then "DISAGREE" else "CHALLENGE-MISMATCH") (desc t))
    cases;
  exit (if !bad = 0 then 0 else 1)

let () =
  if Array.length Sys.argv > 2 && Sys.argv.(1) = "--diff" then run_diff Sys.argv.(2);
  if Array.length Sys.argv > 3 && Sys.argv.(1) = "--diff-sub" then run_diff_sub Sys.argv.(2) Sys.argv.(3);
  if Array.length Sys.argv > 2 && Sys.argv.(1) = "--gen" then
    run_gen Sys.argv.(2) (List.tl (List.tl (List.tl (Array.to_list Sys.argv))));
  let dir = if Array.length Sys.argv > 1 then Sys.argv.(1) else "data" in
  Printf.printf "Bayer–Groth shuffle argument, Swiss Post crypto-primitives fixtures, 3072-bit group\n";
  run_shuffle dir; run_product dir; run_hadamard dir; run_zero dir; run_svp dir; run_multiexp dir;
  Printf.printf "extracted honest prover (Fiat–Shamir) and certified verifier on fresh shuffles\n";
  demo 1 2 1; demo 2 3 2; demo 4 4 1;
  let bad = List.filter (fun (_, ok) -> not ok) !results in
  Printf.printf "%d checks, %d unexpected\n" (List.length !results) (List.length bad);
  List.iter (fun (n, _) -> Printf.printf "  UNEXPECTED: %s\n" n) bad;
  exit (if bad = [] then 0 else 1)
