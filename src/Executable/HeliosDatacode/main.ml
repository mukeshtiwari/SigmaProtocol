open Lwt.Infix

(* Helper: fetch a URL and return its body as string *)
let fetch_url (url : string) : string Lwt.t =
  let open Cohttp_lwt_unix in
  Client.get (Uri.of_string url) >>= fun (resp, body) ->
  let code = resp |> Response.status |> Cohttp.Code.code_of_status in
  if code = 200 then
    body |> Cohttp_lwt.Body.to_string
  else
    Lwt.fail_with (Printf.sprintf "HTTP error %d fetching %s" code url)

(* Extract list of voter_uuid strings from the ballots JSON array *)
let extract_voter_uuids (json_str : string) : string list =
  let open Yojson.Basic.Util in
  let json = Yojson.Basic.from_string json_str in
  match json with
  | `List lst ->
      List.filter_map
        (fun obj ->
           try Some (obj |> member "voter_uuid" |> to_string)
           with _ -> None)
        lst
  | _ ->
      failwith "Expected a JSON array of ballots"

(* Fetch and print last vote JSON for each voter_uuid *)
let fetch_votes_for_voters base_url (voters : string list) : unit Lwt.t =
  Lwt_list.iter_s
    (fun voter_uuid ->
       let url = Printf.sprintf "%s/ballots/%s/last" base_url voter_uuid in
       fetch_url url >>= fun vote_json ->
       Printf.printf "%s\n%!" vote_json;
       Lwt.return_unit)
    voters


let _ = 
  let uuid = read_line () in
  let base_url = Printf.sprintf "https://vote.heliosvoting.org/helios/elections/%s" uuid in
  Lwt_main.run (
    (* --- 1. Download ballots list --- *)
    let ballots_url = base_url ^ "/ballots/" in
    fetch_url ballots_url >>= fun ballots_json ->
    let uuids = extract_voter_uuids ballots_json in
    fetch_votes_for_voters base_url uuids >>= fun _ -> 
    (* --- 2. Download trustees JSON --- *)
    let trustees_url = base_url ^ "/trustees/" in
    fetch_url trustees_url >>= fun trustees_json ->
    Printf.printf ";%s\n%!" trustees_json;
    (* --- 3. Download result JSON --- *)
    let result_url = base_url ^ "/result" in
    fetch_url result_url >>= fun result_json ->
    Printf.printf ";%s\n%!" result_json;
    Lwt.return_unit)
