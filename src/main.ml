
(* Types for solvers *)
(* ************************************************************************ *)

exception Out_of_time
exception Out_of_space
exception Failure of string

module Status = struct
  type t =
    | Sat
    | Unsat
    | Memory
    | Timeout
end
include Status

type 'a sat = {
  name : string;
  package : string;
  pre : int list list -> 'a;
  solve : 'a -> Status.t;
}

type solver = S : _ sat -> solver

type 'a res = {
  solver : solver;
  status : ('a, exn) result;
  number : int;
  cpu_time : int64;
  realtime : int64;
}

(* Convenience functions *)
(* ************************************************************************ *)

let map f l = List.rev @@ List.rev_map f l

(* Sat solvers *)
(* ************************************************************************ *)

(* mSAT *)
let mk_msat ~store_proof =
  let module M = Msat_sat in
  let pre clauses = map (map M.Int_lit.make) clauses in
  let solve clauses =
    let s = M.create ~store_proof ~size:`Big () in
    let () = M.assume s clauses () in
    match M.solve s with
    | M.Sat _ -> Sat
    | M.Unsat _ -> Unsat
  in {
    name = "msat" ^ (if store_proof then "" else "-no-proof");
    package = "mSAT";
    pre; solve;
  }

let msat = mk_msat ~store_proof:true
let msat_no_proof = mk_msat ~store_proof:false

(* mc² *)
let mc2 =
  let open Mc2_core in
  let pre clauses =
    let solver = Solver.create ~plugins:[Mc2_dimacs.Plugin_sat.plugin] () in
    let mk_atom = Solver.get_service_exn solver Mc2_dimacs.Plugin_sat.k_atom in
    solver, map (map mk_atom) clauses
  in
  let solve (solver,clauses) =
    Solver.assume solver clauses;
    match Solver.solve solver with
      | Solver.Sat _ -> Status.Sat
      | Solver.Unsat _ -> Status.Unsat
  in {
    name = "mc2";
    package = "mc2.core, mc2.dimacs";
    pre; solve;
  }

(* aez *)
let aez =
  let () = Aez.Smt.set_cc false in
  let pred = Aez.Hstring.make "p" in
  let () = Aez.Smt.Symbol.declare pred [ Aez.Smt.Type.type_int ] Aez.Smt.Type.type_bool in
  let mk_abs i =
    assert (i > 0);
    Aez.Smt.Term.make_app pred [ Aez.Smt.Term.make_int (Num.Int i) ]
  in
  let mk_pred i =
    assert (i <> 0);
    let t = mk_abs (abs i) in
    let t' = if i > 0 then Aez.Smt.Term.t_true else Aez.Smt.Term.t_false in
    Aez.Smt.Formula.(make_lit Eq [t; t'])
  in
  let mk_clause l =
    let l' = map mk_pred l in
    Aez.Smt.Formula.(make Or l')
  in
  let pre l =
    let l' = map mk_clause l in
    Aez.Smt.Formula.(make And l')
  in
  let solve clauses =
    let module M = Aez.Smt.Make() in
    try
      let () = M.assume ~id:0 clauses in
      let () = M.check () in
      Sat
    with Aez.Smt.Unsat _ ->
      Unsat
  in {
    name = "aez";
    package = "aez";
    pre; solve;
  }

(* minisat (minisat) *)
let minisat simpl =
  let name = Format.sprintf "minisat%s" (if simpl then " (simpl)" else "") in
  let make i =
    if i < 0 then Minisat.Lit.neg @@ Minisat.Lit.make ~-i else Minisat.Lit.make i
  in
  let pre clauses = map (map make) clauses in
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

(*
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
   *)

(* ocaml-sat-solvers *)
let ocaml_sat_solvers solver_name =
  let pre clauses = map Array.of_list clauses in
  let solve clauses =
    let f = Satsolvers.find_solver solver_name in
    let s = f#new_instance in
    let () = List.iter s#add_clause clauses in
    let res = match s#solve with
      | Satwrapper.SolveSatisfiable -> Sat
      | Satwrapper.SolveUnsatisfiable -> Unsat
      | Satwrapper.SolveFailure msg ->
        let () = s#dispose in
        raise (Failure msg)
    in
    let () = s#dispose in
    res
  in {
    name = solver_name;
    package = "ocaml-sat-solvers";
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

let call ~timeout ~memory input ((S solver) as s) =
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
  { solver = s; status; number = 1;
    cpu_time = Int64.sub (cpu_time()) cpu_start;
    realtime = Int64.sub (realtime()) realstart;
  }


(* Printing results *)
(* ************************************************************************ *)

let mk_grid lines columns f =
  Array.init lines (fun i ->
      Array.init columns (fun j -> f (i, j)))

let pp_full out r =
  ()

let pp_res ~full out l =
  let g = mk_grid (1 + List.length l) 5 (function
      | (0, 0) -> PrintBox.text "solver"
      | (0, 1) -> PrintBox.text "status"
      | (0, 2) -> PrintBox.text "number"
      | (0, 3) -> PrintBox.text "CPU time"
      | (0, 4) -> PrintBox.text "Realtime"
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
          | Error exn ->
            PrintBox.sprintf "%s"
              (if full then (Printexc.to_string exn) else "exn")
        end
      | (i, 2) ->
        let r = List.nth l (i - 1) in
        PrintBox.sprintf "%d" r.number
      | (i, 3) ->
        let r = List.nth l (i - 1) in
        let f = Int64.to_float r.cpu_time /. (10. ** 9.) in
        PrintBox.sprintf "%.3f" f
      | (i, 4) ->
        let r = List.nth l (i - 1) in
        let f = Int64.to_float r.realtime /. (10. ** 9.) in
        PrintBox.sprintf "%.3f" f
      | _ -> assert false
    ) in
  let g' = PrintBox.grid ~pad:(PrintBox.hpad 1) ~bars:true g in
  let () = PrintBox_text.output ~indent:1 out g' in
  Printf.fprintf out "\n%!"

(* Aggregating results *)
(* ************************************************************************ *)

exception Dummy

module M = Map.Make(struct
    type t = (Status.t, unit) result
    let compare = compare
  end)

let get_r = function
  | Ok s -> Ok s
  | Error _ -> Error ()

let to_r = function
  | Ok s -> Ok s
  | Error () -> Error Dummy

let part_s l s =
  match List.partition (fun (s', _) -> s == s') l with
  | [] , _ -> M.empty, l
  | [ _, m ], l' -> m, l'
  | _ -> assert false

let add_res l r =
  let m, l' = part_s l r.solver in
  let t = get_r r.status in
  let (n, total) = try M.find t m with Not_found -> (0, Int64.of_int 0) in
  let m' = M.add t (n + 1, Int64.add total r.cpu_time) m in
  (r.solver, m') :: l'

let mean l =
  let l' = List.fold_left (fun acc (s, l') ->
      List.fold_left add_res acc l') [] l in
  List.flatten @@ List.map (fun (solver, m) ->
      List.map (fun (status, (number, total)) ->
          let time = Int64.div total (Int64.of_int number) in
          { solver; number; status = to_r status;
            cpu_time = time; realtime = time; })
        (M.bindings m)) l'

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

let solver_list = [
  S aez;
  S msat;
  S msat_no_proof;
  S mc2;
  S (minisat false);
  S (ocaml_sat_solvers "minisat");
(*
  S (sattools "minisat" "mini");
  S (sattools "cryptominisat" "crypto");
*)
]

let file_list = ref []
let name_list = ref []
let package_list = ref []
let aggregate = ref false
let full_output = ref false
let timeout = ref 600
let memory = ref 1000

let add_solver_name s = name_list := s :: !name_list
let add_package_name s = package_list := s :: !package_list

let args = [
  "-a", Arg.Set aggregate, " agregate all results into one";
  "-s", Arg.String add_solver_name, " filter the solvers to use by name";
  "-p", Arg.String add_package_name, " filter the solvers to use by package";
  "-f", Arg.Set full_output, " output full exception information";
  "-t", Arg.Set_int timeout, " timeout (in seconds)";
  "-m", Arg.Set_int memory, " timeout (in MB)";
] |> Arg.align

let anon file =
  file_list := file :: !file_list

let usage = "./sat-bench [-s solver] file+"

let rec filter_map f acc = function
  | [] -> List.rev acc
  | x :: r ->
    begin match f x with
      | None -> filter_map f acc r
      | Some y -> filter_map f (y :: acc) r
    end

let mem s l =
  if l = [] then true
  else List.mem s l

let () =
  let () = Arg.parse args anon usage in
  if !file_list = [] then begin
    Format.printf "ERROR: empty file list";
    exit 1
  end else begin
    let timeout = float_of_int !timeout in
    let memory = float_of_int !memory *. 1_000_000. in
    let solvers = List.filter (fun (S s) ->
        mem s.name !name_list && mem s.package !package_list
      ) solver_list in
    let l = List.map (fun file ->
        Format.printf "@\nProcessing file '%s': parsing...@?" file;
        let l = P.parse_file file in
        Format.printf " solving..@\n@.";
        let input = filter_map (fun x -> x) [] l in
        let res = List.map (call ~timeout ~memory input) solvers in
        pp_res ~full:!full_output stdout res;
        file, res)
        (List.rev !file_list)
    in
    if !aggregate then
      Printf.printf "Aggregate (mean):\n%a" (pp_res ~full:!full_output) (mean l)
  end

