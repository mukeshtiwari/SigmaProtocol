open Compilerlib.CompilerIns

let big = Big_int_Z.big_int_of_int
let str = Big_int_Z.string_of_big_int

(* demo randomness only; a deployment should use a CSPRNG as in the
   other executables *)
let rnd_field () : coq_F =
  mk_field (big (Random.int 2963))

let print_run name (ok, (((a1, r1), (a2, r2)), c1)) =
  Printf.printf
    "%s\n  branch 1: announcement = %s, responses = [%s]\n  branch 2: announcement = %s, responses = [%s]\n  left-branch challenge = %s\n  verified: %b\n"
    name
    (str a1) (String.concat ", " (List.map str r1))
    (str a2) (String.concat ", " (List.map str r2))
    (str c1) ok

let () =
  Random.self_init ();
  Printf.printf "p = %s, q = %s\n" (str p) (str q);
  let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
  and s2 = rnd_field () and cs = rnd_field () and c = rnd_field () in
  print_run "OR proof (interactive), left witness (knows dlog of H1):"
    (or_run_left u1 u2 s1 s2 cs c);
  let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
  and s2 = rnd_field () and cs = rnd_field () and c = rnd_field () in
  print_run "OR proof (interactive), right witness (knows dlog of H2):"
    (or_run_right u1 u2 s1 s2 cs c);
  let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
  and s2 = rnd_field () and cs = rnd_field () in
  print_run "OR NIZK (strong Fiat-Shamir, SHA-256), left witness:"
    (or_nizk_run_left u1 u2 s1 s2 cs);
  let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
  and s2 = rnd_field () and cs = rnd_field () in
  print_run "OR NIZK (strong Fiat-Shamir, SHA-256), right witness:"
    (or_nizk_run_right u1 u2 s1 s2 cs)

let () =
  (* H4: throughput benchmark of the extracted verified protocol *)
  let iters = 2000 in
  let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
  and s2 = rnd_field () and cs = rnd_field () in
  let t0 = Unix.gettimeofday () in
  let ok = ref true in
  for _ = 1 to iters do
    let (v, _) = or_nizk_run_left u1 u2 s1 s2 cs in
    ok := !ok && v
  done;
  let dt = Unix.gettimeofday () -. t0 in
  Printf.printf
    "\nbenchmark: %d verified NIZK prove+verify in %.3fs = %.0f/s (all ok: %b)\n"
    iters dt (float_of_int iters /. dt) !ok
