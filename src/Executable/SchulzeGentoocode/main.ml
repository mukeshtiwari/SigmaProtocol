(* The verifier's and the trustees' side of a real election through the
   extracted Schulze verifier and prover at the 2048-bit Helios parameters.

     main.exe ballots-file

   reads the bulletin board written by encrypt.exe, verifies every ballot
   under its voter's oracle, checks that a ballot replayed under another
   credential is rejected, aggregates the accepted ballots, decrypts the
   margins with the trustee key, certifies the Schulze winner and verifies
   the certificate. *)
open SchulzeBenchlib.SchulzeBenchIns
open Board

let () =
  match Array.to_list Sys.argv with
  | _ :: ballots_file :: _ ->
    let ((m, names, ballots), tr) = time_it (fun () -> read_board ballots_file) in
    let nb = List.length ballots in
    let n = big (m - 1) and n' = big (nb - 1) in
    Printf.printf "%s: m = %d candidates, N = %d ballots read in %.1f s\n%!"
      (Filename.basename ballots_file) m nb tr;
    let ver_times = ref [] and ver_cpu = ref [] in
    let accepted = List.filter (fun (vid, _, b) ->
      let (ok, tv, cv) = time_it2 (fun () -> nizk_verify_ballot_bench n (hash_oracle_for vid) b) in
      ver_times := tv :: !ver_times; ver_cpu := cv :: !ver_cpu; ok) ballots in
    Printf.printf "ballots: verify median %.1f s, total %.0f s, accepted %d of %d, cpu median %.1f s, cpu total %.0f s\n%!"
      (median !ver_times) (sum !ver_times) (List.length accepted) nb (median !ver_cpu) (sum !ver_cpu);
    let (v0, _, b0) = List.hd ballots in
    Printf.printf "ballot of %s replayed under another credential verifies: %b\n%!" v0
      (nizk_verify_ballot_bench n (hash_oracle_for "voter-replay") b0);
    let (encD, ta) = time_it (fun () -> aggregate_bench n (List.map (fun (_, _, b) -> b) accepted)) in
    let (d, td) = time_it (fun () -> decrypt_margins_bench n n' encD) in
    Printf.printf "aggregation %.2f s, decryption of the margins %.1f s\n" ta td;
    List.iter (fun row -> print_endline ("  " ^ String.concat " " (List.map z (vector_to_list row))))
      (vector_to_list d);
    let w = match winner_bench n d with Some w -> w | None -> failwith "no winner" in
    Printf.printf "Schulze winner: %s\n%!" names.(fin_to_int w);
    let (pf, tg, cg) = time_it2 (fun () ->
      nizk_generate_tally_bench n n' tally_hash_oracle encD w (memo_random_field ())) in
    Printf.printf "certificate generated in %.0f s (cpu %.0f s)\n%!" tg cg;
    let (ok, tv, cv) = time_it2 (fun () -> nizk_verify_tally_bench n n' tally_hash_oracle encD w pf) in
    Printf.printf "certificate: generation %.0f s, verification %.0f s, verified %b, transcript entries %s, cpu generation %.0f s, cpu verification %.0f s\n%!"
      tg tv ok (z (tally_board_size n n' encD w pf)) cg cv
  | _ -> prerr_endline "usage: main.exe ballots-file"; exit 2
