
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

type 'a solver = {
  name : string;
  package : string;
  pre : int list list -> 'a;
  solve : 'a -> status;
}

type 'a res = {
  status : ('a, exn) result;
  cpu_time : int64;
  real_time : int64;
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
  let pre clauses = List.map (List.map Minisat.Lit.make) clauses in
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

(* minisat (sattools) *)
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

let minisat_sattools = sattools "minisat" "mini"
let cryptominisat_sattools = sattools "cryptominisat" "cryptominisat"


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

(* We also want to catch user interruptions *)
let () =
  Sys.set_signal Sys.sigint (
    Sys.Signal_handle (fun _ -> raise Sigint)
  )

let realtime () =
  Oclock.gettime Oclock.realtime

let cputime () =
  match Oclock.process_cputime with
  | None -> 0L
  | Some clock -> Oclock.gettime clock

let wrap ~timeout ~memory f arg =
  let real_start = realtime () in
  let cpu_start = cputime () in
  let al = setup_alarm timeout memory in
  let status =
    match f arg with
    | res -> Ok res
    | exception Out_of_time -> Ok Timeout
    | exception Out_of_space -> Ok Memory
    | exception exn -> Error exn
  in
  let () = delete_alarm al in
  { status;
    cpu_time = Int64.sub (cputime()) cpu_start;
    real_time = Int64.sub (realtime()) real_start;
  }


