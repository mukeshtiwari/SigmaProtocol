(* A certified-code front-end for a Belenios shuffle: it runs the extracted
   Terelius-Wikström verifier of this repository (Crypto/ShuffleTW.v's
   tw_verify, from Verificatumlib) at the Ed25519 group (Belenioslib's
   Ed25519 instance) on the proof of a shuffle produced by Belenios.

   This is the genuine "Belenios input on the Rocq code" test: the group
   operations are the extracted Ed25519 arithmetic, and the verifier is the
   extracted tw_verify, the same term whose completeness, special soundness
   and zero knowledge are proved in Coq.

   Usage: main.exe SHUFFLE.dat   (the flat file written by export_tw.py)

   Note on the trusted boundary. In Coq the Ed25519 group type is the
   order-l subgroup, so a point off it cannot be formed; under extraction
   that proof is erased and the type is a bare pair of coordinates, so this
   driver *can* feed tw_verify a point outside the subgroup. The certified
   pipeline's real driver (Executable/Beleniosverifier/parsing/ast.ml)
   rejects such a point at parse time (the order-l check); here we decode
   without that check, on purpose, to see what the verified algebra alone
   does with a torsion-tampered Belenios shuffle. The driver reports the
   subgroup status of each output so the two can be told apart. *)

open Belenioslib
module V = Verificatumlib
module List = Stdlib.List

let bi = Big_int_Z.big_int_of_int

(* ---- Ed25519 field constants, for decoding compressed points ---- *)
let p = Z.sub (Z.shift_left Z.one 255) (Z.of_int 19)
let l = Z.add (Z.shift_left Z.one 252) (Z.of_string "27742317777372353535851937790883648493")
let d = Z.erem (Z.mul (Z.neg (Z.of_int 121665)) (Z.invert (Z.of_int 121666) p)) p
let mask255 = Z.sub (Z.shift_left Z.one 255) Z.one

(* uncompress a 64-hex Belenios point to its affine coordinates, WITHOUT the
   subgroup check (so torsion points decode) *)
let uncompress (hex : string) : Z.t * Z.t =
  let z = Z.of_string_base 16 hex in
  let y = Z.logand z mask255 in
  let sign = Z.shift_right z 255 in
  let y2 = Z.erem (Z.mul y y) p in
  let x2 = Z.erem (Z.mul (Z.sub y2 Z.one) (Z.invert (Z.add (Z.mul d y2) Z.one) p)) p in
  let e = Z.div (Z.sub p (Z.of_int 5)) (Z.of_int 8) in
  let v = Z.powm (Z.shift_left x2 1) e p in
  let i = Z.erem (Z.shift_left (Z.mul (Z.mul x2 v) v) 1) p in
  let x = Z.erem (Z.mul (Z.mul x2 v) (Z.sub i Z.one)) p in
  let x = if Z.equal (Z.erem (Z.mul x x) p) x2 then x else failwith ("not on curve: " ^ hex) in
  let x = if Z.equal (Z.logand x Z.one) sign then x else Z.sub p x in
  (x, y)

(* a point is exactly the extracted coq_G = (Zmod * Zmod) = (Z.t * Z.t) *)
let point_of_hex (hex : string) : Ed25519.Ed25519.Ed.coq_G = uncompress hex
let scalar_of_dec (s : string) : Ed25519.Ed25519.Zl.coq_F = Ed25519Ins.of_Z (Z.of_string s)

(* l * P = 0 ?  (the subgroup test, for reporting only) *)
let in_subgroup (pt : Ed25519.Ed25519.Ed.coq_G) : bool =
  Ed25519.Ed25519.Ed.fast_smul l pt = (Z.zero, Z.one)

(* ---- list -> extracted Vector.t ---- *)
let rec vec_of_list = function
  | [] -> V.VectorDef.Coq_nil
  | h :: t -> V.VectorDef.Coq_cons (h, bi (List.length t), vec_of_list t)

(* ---- read the .dat ---- *)
let () =
  if Array.length Sys.argv < 2 then (prerr_endline "usage: main.exe SHUFFLE.dat"; exit 2);
  let tbl = Hashtbl.create 32 in
  let ic = open_in Sys.argv.(1) in
  (try while true do
     let line = input_line ic in
     match String.index_opt line ' ' with
     | Some k -> Hashtbl.replace tbl (String.sub line 0 k)
                   (String.sub line (k + 1) (String.length line - k - 1))
     | None -> ()
   done with End_of_file -> ());
  close_in ic;
  let get k = Hashtbl.find tbl k in
  let pts k = List.map point_of_hex (String.split_on_char ' ' (get k)) in
  let scs k = List.map scalar_of_dec (String.split_on_char ' ' (get k)) in
  let n = int_of_string (get "n") in
  let pair_list a b = List.map2 (fun x y -> (x, y)) (pts a) (pts b) in

  let g = point_of_hex (get "g") and pk = point_of_hex (get "pk") in
  let h0 = point_of_hex (get "h0") in
  let hs = pts "hs" and us = pts "us" and bs = pts "Bs" in
  let es = scs "es" in
  let ws = pair_list "ws_a" "ws_b" and ws' = pair_list "wsp_a" "wsp_b" in
  let a' = point_of_hex (get "Ap") and c' = point_of_hex (get "Cp")
  and d' = point_of_hex (get "Dp") in
  let b' = pts "Bp" in
  let f1 = point_of_hex (get "F1") and f2 = point_of_hex (get "F2") in
  let c = scalar_of_dec (get "c") in
  let resp = scs "resp" in

  (* the statement V = (A',(C',(D',(B',(F1,F2))))) *)
  let ann : Ed25519.Ed25519.Ed.coq_G V.ShuffleTW.coq_V =
    (a', (c', (d', (vec_of_list b', (f1, f2))))) in
  let public : (Ed25519.Ed25519.Zl.coq_F, Ed25519.Ed25519.Ed.coq_G) V.ShuffleTW.public =
    { V.ShuffleTW.g; h0; hs = vec_of_list hs; pk; us = vec_of_list us;
      es = vec_of_list es; coq_Bs = vec_of_list bs;
      ws = vec_of_list ws; ws' = vec_of_list ws' } in
  let transcript : (Ed25519.Ed25519.Zl.coq_F, Ed25519.Ed25519.Ed.coq_G V.ShuffleTW.coq_V) V.Sigma.sigma_proto =
    { V.Sigma.announcement = vec_of_list [ann];
      challenge = vec_of_list [c]; response = vec_of_list resp } in

  (* the extracted verified tw_verify, at the extracted Ed25519 group *)
  let module E = Ed25519.Ed25519.Ed in
  let verdict =
    V.ShuffleTW.tw_verify
      Ed25519.Ed25519.Zl.one Ed25519.Ed25519.Zl.mul
      E.gid E.ginv E.gop E.gpow_fast E.coq_Gdec
      (bi (n - 1)) public transcript in

  let all_sub = List.for_all (fun (a, b) -> in_subgroup a && in_subgroup b) ws' in
  Printf.printf "certified tw_verify (extracted ShuffleTW.v at Ed25519): %b\n" verdict;
  Printf.printf "every output ciphertext in the prime-order subgroup: %b\n" all_sub;
  exit (if verdict then 0 else 1)
