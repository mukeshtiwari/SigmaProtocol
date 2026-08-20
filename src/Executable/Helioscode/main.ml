open Helioslib.CompilerHelios

let str = Big_int_Z.string_of_big_int
let mk z = mk_field (Big_int_Z.big_int_of_int z)
let rnd_field () : coq_F = mk (Random.int 1000000)

let () =
  Random.self_init ();
  Printf.printf "Production group: 2048-bit Helios safe prime (q has %d digits)\n"
    (String.length (str q));
  (* interactive protocol at the production group (no Fiat-Shamir hash) *)
  let interactive name w =
    let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
    and s2 = rnd_field () and cs = rnd_field () and c = rnd_field () in
    let t0 = Unix.gettimeofday () in
    let t = or_prove w (or_rand u1 u2 s1 s2 cs) c in
    let ok = or_verify c t in
    let dt = Unix.gettimeofday () -. t0 in
    Printf.printf "%s verified: %b  (%.3fs)\n" name ok dt
  in
  interactive "interactive OR, left witness (dlog H1): "
    (or_witness_left xval fzero);
  interactive "interactive OR, right witness (dlog H2):"
    (or_witness_right fzero yval);
  (* one Fiat-Shamir NIZK to exercise the full pipeline *)
  let u1 = rnd_field () and u2 = rnd_field () and s1 = rnd_field ()
  and s2 = rnd_field () and cs = rnd_field () in
  let t0 = Unix.gettimeofday () in
  let (ok, _) = or_nizk_run_left u1 u2 s1 s2 cs in
  Printf.printf "NIZK (strong FS, SHA-256) left: verified %b  (%.3fs)\n"
    ok (Unix.gettimeofday () -. t0)
