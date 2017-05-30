
(* Types for solvers *)
(* ************************************************************************ *)

exception Sigint
exception Out_of_time
exception Out_of_space

type status =
  | Sat
  | Unsat
  | Memory
  | Timeout

type 'a sat = {
  name : string;
  package : string;
  pre : int list list -> 'a;
  solve : 'a -> status;
}

type solver = S : _ sat -> solver

type 'a res = {
  solver : solver;
  status : ('a, exn) result;
  cpu_time : int64;
  realtime : int64;
}

(* Sat solvers *)
(* ************************************************************************ *)

(* mSAT *)
let msat =
  let pre clauses = List.map (List.map Msat.Sat.Expr.make) clauses in
  let solve clauses =
    let module M = Msat.Sat.Make () in
    let () = M.assume clauses in
    match M.solve () with
    | M.Sat _ -> Sat
    | M.Unsat _ -> Unsat
  in {
    name = "msat";
    package = "mSAT";
    pre; solve;
  }

(* minisat (minisat) *)
let minisat simpl =
  let name = Format.sprintf "minisat%s" (if simpl then " (simpl)" else "") in
  let make i =
    if i < 0 then Minisat.Lit.neg @@ Minisat.Lit.make ~-i else Minisat.Lit.make i
  in
  let pre clauses = List.map (List.map make) clauses in
  let solve clauses =
    let state = Minisat.create () in
    try
      let () = List.iter (Minisat.add_clause_l state) clauses in
      let () = if simpl then Minisat.simplify state in
      let () = Minisat.solve state in
      Sat
    with Minisat.Unsat ->
      Unsat
  in {
    package = "minisat";
    name; pre; solve;
  }

(* sattools *)
let sattools solver_name sattools_name =
  let pre clauses = clauses in
  let solve clauses =
    let module M = (val (Sattools.Libs.get_solver sattools_name)) in
    let state = M.create () in
    try
      let () = List.iter (M.add_clause state) clauses in
      let res = match M.solve state with
        | `sat _ -> Sat
        | `unsat -> Unsat
      in
      let () = M.destroy state in
      res
    with exn ->
      let () = M.destroy state in
      raise exn
  in {
    name = solver_name;
    package = "sattools";
    pre; solve;
  }

(* Wrapper for timing *)
(* ************************************************************************ *)

(* This function analyze the current size of the heap *)
let check size_limit = function () ->
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if s > size_limit then
    raise Out_of_space

(* There are two kinds of limits we want to enforce:
   - a size limit: we use the Gc's alarm function to enforce the limit
     on the size of the RAM used
   - a time limit: the Gc alarm is not reliable to enforce this, so instead
     we use the Unix.timer facilities *)
let setup_alarm t s =
  let _ = Unix.setitimer Unix.ITIMER_REAL
      Unix.{it_value = t; it_interval = 0.01 } in
  Gc.create_alarm (check s)

let delete_alarm alarm =
  let _ = Unix.setitimer Unix.ITIMER_REAL
      Unix.{it_value = 0.; it_interval = 0. } in
  Gc.delete_alarm alarm

(* The Unix.timer works by sending a Sys.sigalrm, so in order to use it,
   we catch it and raise the Out_of_time exception. *)
let () =
  Sys.set_signal Sys.sigalrm (
    Sys.Signal_handle (fun _ -> raise Out_of_time)
  )

(* Raising an exception will only interrupt the current solver, not
   the whole program, so we disable the raising of the `Break` exception. *)
let () =
  Sys.catch_break false

let realtime () =
  Oclock.gettime Oclock.realtime

let cpu_time () =
  match Oclock.process_cputime with
  | None -> 0L
  | Some clock -> Oclock.gettime clock

let call ~timeout ~memory input (S solver) =
  let clauses = solver.pre input in
  let realstart = realtime () in
  let cpu_start = cpu_time () in
  let al = setup_alarm timeout memory in
  let status =
    match solver.solve clauses with
    | res -> Ok res
    | exception Out_of_time -> Ok Timeout
    | exception Out_of_space -> Ok Memory
    | exception exn -> Error exn
  in
  let () = delete_alarm al in
  Gc.major ();
  { solver = (S solver); status;
    cpu_time = Int64.sub (cpu_time()) cpu_start;
    realtime = Int64.sub (realtime()) realstart;
  }


(* Printing results *)
(* ************************************************************************ *)

let mk_grid lines columns f =
  Array.init lines (fun i ->
      Array.init columns (fun j -> f (i, j)))

let pp_res out l =
  let g = mk_grid (1 + List.length l) 4 (function
      | (0, 0) -> PrintBox.text "solver"
      | (0, 1) -> PrintBox.text "status"
      | (0, 2) -> PrintBox.text "CPU time"
      | (0, 3) -> PrintBox.text "Realtime"
      | (i, 0) ->
        let { solver = S s; _ } = List.nth l (i - 1) in
        PrintBox.sprintf "%s (%s)" s.name s.package
      | (i, 1) ->
        let r = List.nth l (i - 1) in
        begin match r.status with
          | Ok Sat -> PrintBox.sprintf "sat"
          | Ok Unsat -> PrintBox.sprintf "unsat"
          | Ok Memory -> PrintBox.sprintf "memory"
          | Ok Timeout -> PrintBox.sprintf "timeout"
          | Error _ -> PrintBox.sprintf "exn"
        end
      | (i, 2) ->
        let r = List.nth l (i - 1) in
        let f = Int64.to_float r.cpu_time /. (10. ** 9.) in
        PrintBox.sprintf "%.3f" f
      | (i, 3) ->
        let r = List.nth l (i - 1) in
        let f = Int64.to_float r.realtime /. (10. ** 9.) in
        PrintBox.sprintf "%.3f" f
      | _ -> assert false
    ) in
  let g' = PrintBox.grid ~pad:(PrintBox.hpad 1) ~bars:true g in
  let () = PrintBox_text.output ~indent:1 out g' in
  Printf.fprintf out "\n%!"


(* Parsing *)
(* ************************************************************************ *)

module P = Dolmen.Dimacs.Make
    (Dolmen.ParseLocation)
    (struct
      type t = int
      let atom ?loc i = i
    end)
    (struct
      type t = int list option
      let p_cnf ?loc _ _ = None
      let clause ?loc l = Some l
    end)

let s_msat = S msat
let s_minisat = S (minisat false)
let s_minisat_simpl = S (minisat true)
let s_sattools_mini = S (sattools "minisat" "mini")
let s_sattools_crypto = S (sattools "cryptominisat" "crypto")

let file_list = ref []
let solver_list = ref []

let set_solver_list = function
  | "msat" -> solver_list := [ s_msat ]
  | "minisat" -> solver_list := [ s_minisat ]
  | "minisat_s" -> solver_list := [ s_minisat_simpl ]
  | "mini" -> solver_list := [ s_sattools_mini ]
  | "crypto" -> solver_list := [ s_sattools_crypto ]
  | "all" -> solver_list := [ s_msat; s_minisat; s_sattools_mini; s_sattools_crypto]
  | _ -> assert false

let args = [
  "-s", Arg.String set_solver_list, " set solver(s) to use (available: all, msat, minisat, mini, crypto)";
]

let anon file =
  file_list := file :: !file_list

let usage = "./sat-bench [-s solver] file [file [file [...]]]"

let rec filter_map f acc = function
  | [] -> List.rev acc
  | x :: r ->
    begin match f x with
      | None -> filter_map f acc r
      | Some y -> filter_map f (y :: acc) r
    end

let () =
  let () = Arg.parse args anon usage in
  if !file_list = [] then (
    Format.printf "ERROR: empty file list";
    exit 1
  ) else if !solver_list = [] then (
    Format.printf "ERROR: empty solver list";
    exit 1
  ) else
    List.iter (fun file ->
        Format.printf "@\nProcessing file '%s': parsing...@?" file;
        let l = P.parse_file file in
        Format.printf " solving..@\n@.";
        let input = filter_map (fun x -> x) [] l in
        let res = List.map (call ~timeout:600. ~memory:1_000_000_000. input) !solver_list in
        pp_res stdout res
      ) !file_list

