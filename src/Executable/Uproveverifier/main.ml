(* Driver for the certified U-Prove verifier (Examples/UProveIns.v) at
   P-256 with SHA-256. Reads the test-vector files of Microsoft's U-Prove C#
   SDK (data/testvectors_EC_*_doc.txt, spec V1.1 Revision 3, the vectors
   Revision 5 of March 2023 still refers to), rebuilds the
   Issuer parameters and the token, and runs the extracted verifier on the
   token signature (Figure 4) and the presentation proof (Figure 10),
   including the scope-exclusive pseudonym, the attribute commitments and
   Device-protected tokens. The hash formatting of spec section 2.2 lives
   here and is handed to the certified code as oracles; the group
   arithmetic, the reconstruction of the announcements and the comparisons
   are extracted from Rocq.

   usage: main.exe [--tamper] FILE...   (default: every file in data/) *)
open UProvelib
open UProvelib.UProveIns

type f = P256.P256.Zn.coq_F
type g = P256.P256.Wp.coq_G

(* ---- parameters of the recommended P-256 profile ---- *)

let q = Z.of_string_base 16 "FFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551"
let p = Z.of_string_base 16 "FFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF"
let a_curve = Z.sub p (Z.of_int 3)
let b_curve = Z.of_string_base 16 "5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B"
let gx = Z.of_string_base 16 "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296"
let gy = Z.of_string_base 16 "4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5"

let point (x : Z.t) (y : Z.t) : g =
  match mk_G x y with
  | Some pt -> pt
  | None -> failwith ("not a point of the P-256 group: " ^ Z.format "%x" x)

let hex_point (s : string) : g =
  (* uncompressed SEC1 point 04 | x | y *)
  let s = String.lowercase_ascii s in
  assert (String.length s = 130 && String.sub s 0 2 = "04");
  point (Z.of_string_base 16 (String.sub s 2 64)) (Z.of_string_base 16 (String.sub s 66 64))

(* ---- byte strings and the U-Prove hash formatting (spec 2.2) ---- *)

let bytes_of_hex (s : string) : string =
  let n = String.length s / 2 in
  String.init n (fun i -> Char.chr (int_of_string ("0x" ^ String.sub s (2 * i) 2)))

let z_of_bytes (s : string) : Z.t =
  String.fold_left (fun acc c -> Z.add (Z.shift_left acc 8) (Z.of_int (Char.code c))) Z.zero s

let bytes_of_z_fixed (z : Z.t) (len : int) : string =
  let s = Bytes.make len '\000' in
  let rec go z i = if i >= 0 && Z.sign z > 0 then begin
      Bytes.set s i (Char.chr (Z.to_int (Z.logand z (Z.of_int 255)))); go (Z.shift_right z 8) (i - 1) end in
  go z (len - 1); Bytes.to_string s

let enc_int (n : int) : string = bytes_of_z_fixed (Z.of_int n) 4
let enc_os (s : string) : string = enc_int (String.length s) ^ s
(* an element of Zq (or p, q, a, b): minimal big-endian bytes, 0 as one byte *)
let enc_z (z : Z.t) : string =
  let len = max 1 ((Z.numbits z + 7) / 8) in enc_os (bytes_of_z_fixed z len)
let enc_null = enc_int 0
let sec1 (pt : g) : string =
  match point_to_Z pt with
  | Some (x, y) -> "\004" ^ bytes_of_z_fixed x 32 ^ bytes_of_z_fixed y 32
  | None -> failwith "point at infinity"
let enc_pt (pt : g) : string = enc_os (sec1 pt)

let sha256 (s : string) : string = Cryptokit.hash_string (Cryptokit.Hash.sha256 ()) s
let digest (parts : string list) : Z.t = z_of_bytes (sha256 (String.concat "" parts))
let digest_q (parts : string list) : f = of_Z (Z.rem (digest parts) q)

let enc_group () : string =
  enc_z p ^ enc_z a_curve ^ enc_z b_curve ^ enc_pt (point gx gy) ^ enc_z q ^ enc_os "\001"

(* ---- the recommended generators g_1..g_50, g_t, g_d (OID ...75.1.2.1) ---- *)

let gens = Array.map hex_point Params.g_i
let g_t = hex_point Params.g_t
let g_d = hex_point Params.g_d

(* GenerateScopeElement as the C# SDK computes it (ECGroupBCImpl.DeriveElement
   with index 0): x = SHA-256(scope || "0" || counter || "0") mod p with
   counter, index and iteration as decimal strings, y the smaller square
   root of x^3 + ax + b (p = 3 mod 4), counter increased until a root exists. *)
let scope_element (scope : string) : g =
  let rec go counter =
    let x = Z.rem (z_of_bytes (sha256 (scope ^ "0" ^ string_of_int counter ^ "0"))) p in
    let alpha = Z.rem (Z.add (Z.add (Z.mul x (Z.mul x x)) (Z.mul a_curve x)) b_curve) p in
    if Z.sign alpha = 0 then point x Z.zero
    else begin
      let y = Z.powm alpha (Z.div (Z.add p Z.one) (Z.of_int 4)) p in
      if Z.equal (Z.rem (Z.mul y y) p) alpha then point x (Z.min y (Z.sub p y))
      else go (counter + 1)
    end in
  go 0

(* ---- vectors ---- *)

let bi = Big_int_Z.big_int_of_int

let rec vector_of_list (xs : 'a list) : 'a VectorDef.t =
  match xs with
  | [] -> VectorDef.Coq_nil
  | h :: t -> VectorDef.Coq_cons (h, Big_int_Z.big_int_of_int (List.length t), vector_of_list t)

let fin (k : int) (p : int) : Fin.t =
  match coord_ins (Big_int_Z.big_int_of_int k) (Big_int_Z.big_int_of_int p) with
  | Some f -> f
  | None -> failwith "coordinate out of range"

(* ---- the test-vector files ---- *)

let load (file : string) : (string, string) Hashtbl.t =
  let tbl = Hashtbl.create 200 in
  let ic = open_in file in
  (try while true do
      let line = String.trim (input_line ic) in
      if line <> "" && not (String.length line >= 2 && String.sub line 0 2 = "//") then
        match String.index_opt line '=' with
        | Some i ->
          Hashtbl.replace tbl (String.trim (String.sub line 0 i))
            (String.trim (String.sub line (i + 1) (String.length line - i - 1)))
        | None -> ()
    done with End_of_file -> ());
  close_in ic; tbl

let get tbl k = try Hashtbl.find tbl k with Not_found -> failwith ("missing field " ^ k)
let has tbl k = Hashtbl.mem tbl k && Hashtbl.find tbl k <> ""
let hexz tbl k = Z.of_string_base 16 (get tbl k)
let scalar tbl k : f = of_Z (hexz tbl k)
let bytes tbl k = if has tbl k then bytes_of_hex (get tbl k) else ""
let pt tbl k = point (hexz tbl (k ^ ".x")) (hexz tbl (k ^ ".y"))
let ints tbl k = if has tbl k then List.map int_of_string (String.split_on_char ',' (get tbl k)) else []

(* ---- verification of one file ---- *)

type tamper = NoTamper | TamperResponse | TamperAttribute | TamperSignature | TamperCommitment

let verify_file ?(tamper = NoTamper) (file : string) : bool =
  let tbl = load file in
  let n = 5 in
  let e = List.init n (fun i -> int_of_string ("0x" ^ get tbl (Printf.sprintf "e%d" (i + 1)))) in
  let device = has tbl "xd" in
  let g0 = pt tbl "g0" in
  let generators = [g0] @ Array.to_list (Array.sub gens 0 n) @ [g_t] @ (if device then [g_d] else []) in
  (* the Issuer parameters digest P and x_t (Figure 2) *)
  let pdig = sha256 (String.concat "" ([enc_os (bytes tbl "UIDp"); enc_group (); enc_int (List.length generators)]
    @ List.map enc_pt generators @ [enc_int n] @ List.map (fun b -> String.make 1 (Char.chr b)) e
    @ [enc_os (bytes tbl "S")])) in
  assert (z_of_bytes pdig = hexz tbl "P");
  let xt = digest_q ["\001"; enc_os pdig; enc_os (bytes tbl "TI")] in
  (* x_i (Figure 3) *)
  let xi i =
    let ai = bytes tbl (Printf.sprintf "A%d" i) in
    if List.nth e (i - 1) = 1 then (if ai = "" then of_Z Z.zero else digest_q [enc_os ai])
    else of_Z (z_of_bytes ai) in
  (* the token *)
  let h = pt tbl "h" and sz = pt tbl "sigmaZPrime" in
  let sc = scalar tbl "sigmaCPrime" in
  let sr = scalar tbl "sigmaRPrime" in
  let sr = if tamper = TamperSignature then of_Z (Z.add (to_Z sr) Z.one) else sr in
  let pi = bytes tbl "PI" in
  let hs a1 a2 = digest_q [enc_pt h; enc_os pi; enc_pt sz; enc_pt a1; enc_pt a2] in
  let sig_ok = verify_signature_ins hs g0 h sz sc sr in
  (* the presentation proof *)
  let d = ints tbl "D" and u = ints tbl "U" and cset = ints tbl "C" in
  let pidx = if has tbl "p" then (if get tbl "p" = "d" then -1 else int_of_string (get tbl "p")) else 0 in
  let xd i = if tamper = TamperAttribute && i = List.hd d then of_Z (Z.add (to_Z (xi i)) Z.one) else xi i in
  let target = target_ins (bi (List.length d)) g0 g_t xt (vector_of_list (List.map (fun i -> gens.(i - 1)) d))
      (vector_of_list (List.map xd d)) in
  let rest = List.map (fun i -> gens.(i - 1)) u @ (if device then [g_d] else []) in
  let r0 = scalar tbl "r0" in
  let r0 = if tamper = TamperResponse then of_Z (Z.add (to_Z r0) Z.one) else r0 in
  let rs_core = r0 :: List.map (fun i -> scalar tbl (Printf.sprintf "r%d" i)) u
      @ (if device then [scalar tbl "rd"] else []) in
  let uidt = sha256 (enc_pt h ^ enc_pt sz ^ enc_z (to_Z sc) ^ enc_z (to_Z sr)) in
  let m = bytes tbl "m" and md = bytes tbl "md" in
  let ha (x : g) : Z.t = digest [enc_pt x] in
  let a = hexz tbl "a" in
  let has_nym = pidx <> 0 && has tbl "ap" in
  let ctil i = pt tbl (Printf.sprintf "tildeC%d" i) in
  let ctil i = if tamper = TamperCommitment && i = List.hd cset then g0 else ctil i in
  (* c_p and c (Figure 10), from the digests a, [a_p], ã_i in that order *)
  let challenge (digests : Z.t list) : f =
    let a, digests = List.hd digests, List.tl digests in
    let ap, atil = if has_nym then Some (List.hd digests), List.tl digests else None, digests in
    let dbytes z = bytes_of_z_fixed z 32 in
    let parts = [enc_os uidt; enc_os (dbytes a); enc_int (List.length d)] @ List.map enc_int d
      @ [enc_int (List.length d)] @ List.map (fun i -> enc_z (to_Z (xd i))) d
      @ (if cset = [] then [enc_null; enc_null; enc_null]
         else [enc_int (List.length cset)] @ List.map enc_int cset
              @ [enc_int (List.length cset)] @ List.map (fun i -> enc_pt (ctil i)) cset
              @ [enc_int (List.length cset)] @ List.map (fun z -> enc_os (dbytes z)) atil)
      @ [enc_int (if pidx = -1 then 0 else pidx)]
      @ (match ap with Some z -> [enc_os (dbytes z); enc_pt (pt tbl "Ps")] | None -> [enc_null; enc_null])
      @ [enc_os m] in
    let cp = sha256 (String.concat "" parts) in
    digest_q [enc_int 2; enc_os cp; enc_os md] in
  let pres_ok =
    if not has_nym && cset = [] then
      verify_presentation_ins (bi (List.length rest)) ha (fun a -> challenge [a]) h (vector_of_list rest) target a (vector_of_list rs_core)
    else begin
      (* coordinates: 0 = α⁻¹, 1.. = hidden bases, then one opening per commitment *)
      let k = List.length rest in
      let ncom = List.length cset in
      let kk = 1 + k + ncom in
      let hidden i = if i = -1 then k else 1 + (let rec idx j = function [] -> failwith "p not in U" | x :: t -> if x = i then j else idx (j + 1) t in idx 0 u) in
      let nym = if has_nym then begin
          let gs = scope_element (bytes tbl "s") in
          if has tbl "gs.x" && P256.P256.Wp.coq_Gdec gs (pt tbl "gs") = false then failwith "scope element differs from the test vector";
          Some (((fin kk (hidden pidx), gs), pt tbl "Ps"), hexz tbl "ap") end else None in
      let coms = List.mapi (fun j i ->
        (((fin kk (hidden i), fin kk (1 + k + j)), ctil i), hexz tbl (Printf.sprintf "tildeA%d" i))) cset in
      let cs = components_ins (bi k) (bi ncom) h (vector_of_list rest) target a nym coms gens.(0) in
      let rs = rs_core @ List.map (fun i -> scalar tbl (Printf.sprintf "tildeR%d" i)) cset in
      verify_uprove_ins (bi kk) ha challenge cs (vector_of_list rs)
    end in
  let name = Filename.basename file in
  Printf.printf "%-40s signature %-5b presentation %-5b  (D=%s U=%s C=%s p=%s device=%b)\n" name sig_ok pres_ok
    (get tbl "D") (get tbl "U") (if has tbl "C" then get tbl "C" else "-")
    (if has tbl "p" then get tbl "p" else "-") device;
  sig_ok && pres_ok

let () =
  let args = List.tl (Array.to_list Sys.argv) in
  let tamper = List.mem "--tamper" args in
  let files = List.filter (fun s -> s <> "--tamper") args in
  let files = if files = [] then
      let dir = Filename.concat (Filename.dirname Sys.executable_name) "data" in
      let dir = if Sys.file_exists dir then dir else "src/Executable/Uproveverifier/data" in
      Sys.readdir dir |> Array.to_list |> List.filter (fun f -> String.length f > 15 && String.sub f 0 15 = "testvectors_EC_")
      |> List.sort compare |> List.map (Filename.concat dir)
    else files in
  let t0 = Unix.gettimeofday () in
  let ok = List.for_all (fun f -> verify_file f) files in
  Printf.printf "%d files, all accepted: %b, %.0f ms\n" (List.length files) ok ((Unix.gettimeofday () -. t0) *. 1000.);
  if tamper then begin
    print_endline "--- tampered inputs (every line must show false) ---";
    let f = List.hd (List.filter (fun f -> Filename.check_suffix f "EC_D2_doc.txt") files) in
    let results = List.map (fun (name, t) ->
      Printf.printf "%s: " name; (name, verify_file ~tamper:t f))
      [ "response r0 + 1", TamperResponse; "disclosed attribute x_D + 1", TamperAttribute;
        "signature sigma_r' + 1", TamperSignature; "commitment c~ replaced by g0", TamperCommitment ] in
    let rejected = List.for_all (fun (_, r) -> not r) results in
    Printf.printf "all tampered inputs rejected: %b\n" rejected;
    if not (ok && rejected) then exit 1
  end else if not ok then exit 1
