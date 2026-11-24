(* Running an array of independent tasks in forked worker processes (the
   same code as par_run in ../SchulzeBenchcode/par.ml). Worker t computes the
   tasks with index t, t + workers, ... and writes each result to its own
   file; the parent waits for all workers and reads the files back. Only
   this scheduling is outside the proofs: the tasks are extracted
   functions. *)
(* Worker t computes the tasks with index t, t + workers, t + 2 workers, ...
   and writes each result to its own file as it is ready. The parent waits
   for all workers and reads the files back. *)
let par_run (workers : int) (tasks : (unit -> 'a) array) : 'a array =
  let nt = Array.length tasks in
  if workers <= 1 || nt = 0 then Array.map (fun f -> f ()) tasks
  else begin
    let files = Array.init workers (fun _ -> Filename.temp_file "schulze-par-" ".bin") in
    flush_all ();
    let pids = Array.init workers (fun t ->
      match Unix.fork () with
      | 0 ->
        (try
           let oc = open_out_bin files.(t) in
           let i = ref t in
           while !i < nt do
             Marshal.to_channel oc (!i, tasks.(!i) ()) [];
             i := !i + workers
           done;
           close_out oc;
           Unix._exit 0
         with e ->
           prerr_endline ("worker " ^ string_of_int t ^ ": " ^ Printexc.to_string e);
           Unix._exit 1)
      | pid -> pid) in
    let ok = ref true in
    Array.iter (fun pid ->
      match Unix.waitpid [] pid with
      | (_, Unix.WEXITED 0) -> ()
      | _ -> ok := false) pids;
    if not !ok then begin
      Array.iter (fun f -> try Sys.remove f with _ -> ()) files;
      failwith "a worker failed"
    end;
    let res : 'a option array = Array.make nt None in
    Array.iteri (fun t f ->
      let ic = open_in_bin f in
      let i = ref t in
      while !i < nt do
        let (j, v) : int * 'a = Marshal.from_channel ic in
        if j <> !i then failwith "worker output out of order";
        res.(j) <- Some v;
        i := !i + workers
      done;
      close_in ic;
      Sys.remove f) files;
    Array.map (function Some v -> v | None -> failwith "missing worker output") res
  end

