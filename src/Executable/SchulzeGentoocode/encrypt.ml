(* The voters' side of a real election through the extracted Schulze
   client at the 2048-bit Helios parameters.

     encrypt.exe positions-file ballots-file

   reads the position vectors of a Gentoo election
   (bench/gentoo-votes/positions-*.txt, from bench/gentoo_leak.py
   --positions), gives voter k the credential voter-k, encrypts every
   ballot with its NIZK proofs under the voter-bound random oracle
   H_v = SHAKE-256(v || transcript) with fresh randomness from
   /dev/urandom, and appends it to the bulletin board ballots-file, which
   main.exe then verifies and tallies. Ballots are written as they are
   produced, so an interrupted run can be resumed: existing ballots in
   ballots-file are kept and only the missing voters are encrypted. *)
open SchulzeBenchlib.SchulzeBenchIns
open Board

let () =
  match Array.to_list Sys.argv with
  | _ :: positions_file :: ballots_file :: _ ->
    let (m, names, rankings) = read_positions positions_file in
    let n = big (m - 1) in
    let election = Filename.basename positions_file in
    (* voters already on the board *)
    let done_ids =
      if Sys.file_exists ballots_file then begin
        let ic = open_in ballots_file in
        let _ = input_line ic in
        let rec read acc = match input_line ic with
          | l -> let vid = List.nth (String.split_on_char ' ' l) 1 in read (vid :: acc)
          | exception End_of_file -> close_in ic; acc in
        read []
      end else [] in
    let oc = open_out_gen [Open_append; Open_creat; Open_wronly] 0o644 ballots_file in
    if done_ids = [] then write_header oc election m (List.length rankings) names;
    Printf.printf "%s: m = %d candidates, %d ballots, %d already on the board\n%!"
      election m (List.length rankings) (List.length done_ids);
    let times = List.concat (List.mapi (fun k s ->
      let vid = Printf.sprintf "voter-%d" k in
      if List.mem vid done_ids then [] else begin
        let (b, te) = time_it (fun () ->
          nizk_encrypt_ballot_bench n (hash_oracle_for vid) (vector_of_list (List.map big s)) random_field) in
        write_ballot oc vid m b; flush oc;
        Printf.printf "  %s encrypted and proved in %.1f s\n%!" vid te;
        [te]
      end) rankings) in
    close_out oc;
    Printf.printf "%s: %d ballots encrypted, median %.1f s per ballot, total %.0f s, board %s\n%!"
      election (List.length times) (median times) (sum times) ballots_file
  | _ -> prerr_endline "usage: encrypt.exe positions-file ballots-file"; exit 2
