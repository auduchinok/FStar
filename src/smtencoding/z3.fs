﻿(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
#light "off"

module FStar.SMTEncoding.Z3
open FStar
open FStar.SMTEncoding.Term
open FStar.Util

(****************************************************************************)
(* Fuel Traces (private)                                                    *)
(****************************************************************************)

type fuel_trace_identity =
    {
      module_digest:string;
      transitive_digest:option<string>;
    }

type fuel_trace_state =
    {
      identity:fuel_trace_identity;
      fuels:list<(int * int)>
    }

type fuel_trace_status =
    | FuelTraceUnavailable
    | RecordFuelTrace of list<(int * int)>
    | ReplayFuelTrace of (string * list<(int * int)>)

let fuel_trace : ref<fuel_trace_status> = Util.mk_ref <| FuelTraceUnavailable

let format_fuel_trace_file_name src_fn =
    Util.format_value_file_name <| Util.format1 "%s.fuel" src_fn

let compute_transitive_digest src_fn deps = 
    (* todo: it would be more robust to obtain the dependencies for `src_fn` directly from `Parser.Dep.collect` here, rather than reply upon the caller to provide them. *)   
    let digests = List.map digest_of_file <| [src_fn] @ deps in
    let s = Util.concat_l "," <| List.sortWith String.compare digests in
    digest_of_string s

let is_replaying_fuel_trace () =
  match !fuel_trace with 
  | ReplayFuelTrace _ ->
    true
  | _ ->
    false

(****************************************************************************)
(* Z3 Specifics                                                             *)
(****************************************************************************)
type z3version =
| Z3V_Unknown
| Z3V of int * int * int

let z3v_compare known (w1, w2, w3) =
    match known with
    | Z3V_Unknown -> None
    | Z3V (k1, k2, k3) -> Some(
        if k1 <> w1 then w1 - k1 else
        if k2 <> w2 then w2 - k2 else
        w3 - k3
    )

let z3v_le known wanted =
    match z3v_compare known wanted with
    | None   -> false
    | Some i -> i >= 0

let _z3version : ref<option<z3version>> = Util.mk_ref None

let get_z3version () =
    let prefix = "Z3 version " in

    match !_z3version with
    | Some version -> version
    | None ->
        let _, out, _ = Util.run_proc !Options.z3_exe "-version" "" in
        let out =
            match splitlines out with
            | x :: _ when starts_with x prefix -> begin
                let x = trim_string (substring_from x (String.length prefix)) in
                let x = try List.map int_of_string (split x ".") with _ -> [] in
                match x with
                | [i1; i2; i3] -> Z3V (i1, i2, i3)
                | _ -> Z3V_Unknown
            end
            | _ -> Z3V_Unknown
        in
            _z3version := Some out; out

let ini_params opt_timeout =
  let timeout =
    begin match opt_timeout with
    | Some n ->
      let t =
        if z3v_le (get_z3version ()) (4, 3, 1)
        then n
        else n * 1000
      in
      format1 "-t:%s" (string_of_int t) 
    | None ->
      ""
    end
  in
  let relevancy =
    if   z3v_le (get_z3version ()) (4, 3, 1)
    then "RELEVANCY"
    else "SMT.RELEVANCY"
  in
  format2 "-smt2 -in %s \
    AUTO_CONFIG=false \
    MODEL=true \
    %s=2"
    timeout relevancy

type z3status =
    | SAT
    | UNSAT
    | UNKNOWN
    | TIMEOUT

let status_to_string = function
    | SAT  -> "sat"
    | UNSAT -> "unsat"
    | UNKNOWN -> "unknown"
    | TIMEOUT -> "timeout"

let tid () = Util.current_tid() |> Util.string_of_int
let new_z3proc id timeout =
    let cond pid (s:string) =
        (let x = Util.trim_string s = "Done!" in
//     Util.print5 "On thread %s, Z3 %s (%s) says: %s\n\t%s\n" (tid()) id pid s (if x then "finished" else "waiting for more output");
         x) in
    let args = ini_params timeout in
    (* we log the following information with `--print_fuels` because lack of a timeout is only associated with fuel tracing *)
    if !Options.print_fuels then
        match timeout with
        | Some n ->
            Util.print2 "Starting z3 process `%s` with a timeout of %s.\n" id <| string_of_int n
        | None ->
            Util.print1 "Starting z3 process `%s` without a timeout.\n" id
    else
        ();
    Util.start_process id (!Options.z3_exe) args cond

type bgproc = {
    grab:unit -> proc;
    release:unit -> unit;
    refresh:unit -> unit;
}


let queries_dot_smt2 : ref<option<file_handle>> = Util.mk_ref None

let get_qfile =
    let ctr = Util.mk_ref 0 in
    fun fresh ->
        if fresh
        then (incr ctr;
              Util.open_file_for_writing (Util.format1 "queries-%s.smt2" (Util.string_of_int !ctr)))
        else match !queries_dot_smt2 with
                | None -> let fh = Util.open_file_for_writing "queries-bg-0.smt2" in  queries_dot_smt2 := Some fh; fh
                | Some fh -> fh

 let log_query fresh i =
    let fh = get_qfile fresh in
    Util.append_to_file fh i;
    if fresh then Util.close_file fh

let the_z3proc =
  ref None

let ctr = Util.mk_ref (-1)

let new_proc () =
  let timeout = 
    if is_replaying_fuel_trace () then
      None
    else
      Some !Options.z3timeout
  in
  new_z3proc (Util.format1 "bg-%s" (incr ctr; !ctr |> string_of_int)) timeout

let z3proc () =
  if !the_z3proc = None then
    the_z3proc := Some (new_proc ());
  must (!the_z3proc)

let bg_z3_proc =
    let x = [] in
    let grab () = Util.monitor_enter x; z3proc () in
    let release () = Util.monitor_exit(x) in
    let refresh () =
        let proc = grab() in
        Util.kill_process proc;
        the_z3proc := Some (new_proc ());
        begin match !queries_dot_smt2 with
            | None -> ()
            | Some fh ->
                Util.close_file fh;
                let fh = Util.open_file_for_writing (Util.format1 "queries-bg-%s.smt2" (!ctr |> string_of_int)) in
                queries_dot_smt2 := Some fh
        end;
        release() in
    {grab=grab;
     release=release;
     refresh=refresh}

let doZ3Exe' (input:string) (z3proc:proc) =
  let parse (z3out:string) =
    let lines = String.split ['\n'] z3out |> List.map Util.trim_string in
    let rec lblnegs lines = match lines with
      | lname::"false"::rest -> lname::lblnegs rest
      | lname::_::rest -> lblnegs rest
      | _ -> [] in
    let rec result x = match x with
      | "timeout"::tl -> TIMEOUT, []
      | "unknown"::tl -> UNKNOWN, lblnegs tl
      | "sat"::tl -> SAT, lblnegs tl
      | "unsat"::tl -> UNSAT, []
      | _::tl -> result tl
      | _ -> failwith <| format1 "Got output lines: %s\n" (String.concat "\n" (List.map (fun (l:string) -> format1 "<%s>" (Util.trim_string l)) lines)) in
      result lines in
  let stdout = Util.ask_process z3proc input in
  parse (Util.trim_string stdout)

let doZ3Exe =
    let ctr = Util.mk_ref 0 in
    fun (fresh:bool) (input:string) ->
        let z3proc = if fresh then (incr ctr; new_z3proc (Util.string_of_int !ctr) (Some !Options.z3timeout)) else bg_z3_proc.grab() in
        let res = doZ3Exe' input z3proc in
        //Printf.printf "z3-%A says %s\n"  (get_z3version()) (status_to_string (fst res));
        if fresh then Util.kill_process z3proc else bg_z3_proc.release();
        res

let z3_options () =
  let mbqi =
    if   z3v_le (get_z3version ()) (4, 3, 1)
    then "mbqi"
    else "smt.mbqi" in
  let model_on_timeout =
    if   z3v_le (get_z3version ()) (4, 3, 1)
    then "(set-option :model-on-timeout true)\n"
    else ""
  in "(set-option :global-decls false)\n" ^
     "(set-option :" ^ mbqi ^ " false)\n" ^
     model_on_timeout

type job<'a> = {
    job:unit -> 'a;
    callback: 'a -> unit
}
type z3job = job<(bool * list<error_label>)>

let job_queue : ref<list<z3job>> = Util.mk_ref []
//    let x = Util.mk_ref [{job=(fun () -> (false, [(("", Term_sort), "", Range.mk_range "" 0 0)])); callback=(fun a -> ())}] in
//    x:=[]; x

let pending_jobs = Util.mk_ref 0
let with_monitor m f =
    Util.monitor_enter(m);
    let res = f () in
    Util.monitor_exit(m);
    res

let z3_job fresh label_messages input () =
  let status, lblnegs = doZ3Exe fresh input in
  let result = match status with
    | UNSAT -> true, []
    | _ ->
        if !Options.debug <> [] then print_string <| format1 "Z3 says: %s\n" (status_to_string status);
        let failing_assertions = lblnegs |> List.collect (fun l ->
        match label_messages |> List.tryFind (fun (m, _, _) -> fst m = l) with
            | None -> []
            | Some (lbl, msg, r) -> [(lbl, msg, r)]) in
        false, failing_assertions in
    result

let rec dequeue' () =
    let j = match !job_queue with
        | [] -> failwith "Impossible"
        | hd::tl ->
          job_queue := tl;
          hd in
    incr pending_jobs;
    Util.monitor_exit job_queue;
    run_job j;
    with_monitor job_queue (fun () -> decr pending_jobs);
    dequeue(); ()

and dequeue () =
    Util.monitor_enter (job_queue);
    let rec aux () = match !job_queue with
        | [] ->
          Util.monitor_wait(job_queue);
          aux ()
        | _ -> dequeue'() in
    aux()

and run_job j = j.callback <| j.job ()

let init () =
    let n_runners = !Options.n_cores - 1 in
    let rec aux n =
        if n = 0 then ()
        else (spawn dequeue; aux (n - 1)) in
    aux n_runners

let enqueue fresh j =
 //   Util.print1 "Enqueue fresh is %s\n" (if fresh then "true" else "false");
    if not fresh
    then run_job j
    else begin
        Util.monitor_enter job_queue;
        job_queue := !job_queue@[j];
        Util.monitor_pulse job_queue;
        Util.monitor_exit job_queue
    end

let finish () =
    let bg = bg_z3_proc.grab() in
    Util.kill_process bg;
    bg_z3_proc.release();
    let rec aux () =
        let n, m = with_monitor job_queue (fun () -> !pending_jobs,  List.length !job_queue)  in
        //Printf.printf "In finish: pending jobs = %d, job queue len = %d\n" n m;
        if n+m=0
        then TypeChecker.Errors.report_all() |> ignore
        else let _ = Util.sleep(500) in
             aux() in
    aux()

type scope_t = list<list<decl>>
let fresh_scope : ref<scope_t> = Util.mk_ref [[]]
let bg_scope : ref<list<decl>> = Util.mk_ref []
let push msg    =
    fresh_scope := [Term.Caption msg]::!fresh_scope;
    bg_scope := [Term.Caption msg; Term.Push]@ !bg_scope
let pop msg      =
    fresh_scope := List.tl !fresh_scope;
    bg_scope := [Term.Caption msg; Term.Pop]@ !bg_scope
let giveZ3 decls =
   let _  = match !fresh_scope with
    | hd::tl -> fresh_scope := (hd@decls)::tl
    | _ -> failwith "Impossible" in
   bg_scope := List.rev decls @ !bg_scope
let bgtheory fresh =
    if fresh
    then List.rev !fresh_scope |> List.flatten
    else let bg = !bg_scope in
         bg_scope := [];
         List.rev bg
let refresh () =
    bg_z3_proc.refresh();
    let theory = bgtheory true in
    bg_scope := List.rev theory
let mark msg =
    push msg
let reset_mark msg =
    pop msg;
    refresh ()
let commit_mark msg =
    begin match !fresh_scope with
        | hd::s::tl -> fresh_scope := (hd@s)::tl
        | _ -> failwith "Impossible"
    end
let ask fresh label_messages qry (cb: (bool * error_labels) -> unit) =
  let fresh = fresh && !Options.n_cores > 1 in
  let theory = bgtheory fresh in
  let theory =
    if fresh
    then theory@qry
    else theory@[Term.Push]@qry@[Term.Pop] in
  let input = List.map (declToSmt (z3_options ())) theory |> String.concat "\n" in
  if !Options.logQueries then log_query fresh input;
  enqueue fresh ({job=z3_job fresh label_messages input; callback=cb})

(****************************************************************************)
(* Fuel Traces (public)                                                     *)
(****************************************************************************)

let initialize_fuel_trace src_fn deps : unit =
    let norm_src_fn = Util.normalize_file_path src_fn in
    let val_fn = format_fuel_trace_file_name norm_src_fn in
    begin match Util.load_value_from_file val_fn with
    | Some state ->
        let means, validated = 
            if !Options.explicit_deps then
                (* we're unable to compute the transitive digest when `--explicit_deps` is specified. *)
                let expected = Util.digest_of_file norm_src_fn in
                ("Module", state.identity.module_digest = expected)
            else 
                ("Transitive",
                    begin
                        match state.identity.transitive_digest with
                        | None ->
                            false
                        | Some d ->
                            let expected = compute_transitive_digest norm_src_fn deps in
                            d = expected
                    end)
        in
        if validated then
            begin if !Options.print_fuels then
                    Util.print2 "(%s) %s digest is valid.\n" norm_src_fn means
                else
                    ();
                fuel_trace := ReplayFuelTrace (val_fn, state.fuels)
            end
        else
            begin if !Options.print_fuels then
                  Util.print2 "(%s) %s digest is invalid.\n" norm_src_fn means
              else
                  ();
              fuel_trace := RecordFuelTrace []
            end
    | None ->
        if !Options.print_fuels then
            Util.print1 "(%s) Unable to read cached fuel trace.\n" norm_src_fn
        else
            ();
        fuel_trace := RecordFuelTrace []
    end;
    refresh ()

let finalize_fuel_trace src_fn deps : unit =
    begin match !fuel_trace with
    | ReplayFuelTrace _ 
    (* failure to verify *)
    | FuelTraceUnavailable 
    (* verification not performed *)
    | RecordFuelTrace [] ->
        ()
    (* verification successful *)
    | RecordFuelTrace l ->
        let val_fn = format_fuel_trace_file_name src_fn in
        let xd = 
            (* we're unable to compute the transitive digest when `--explicit_deps` is specified. *)
            if !Options.explicit_deps then
                None
            else
                Some <| compute_transitive_digest src_fn deps
        in
        let state = {
            identity = {
                module_digest = Util.digest_of_file src_fn;
                transitive_digest = xd 
            };
            fuels = l
        }
        in
        Util.save_value_to_file val_fn state
    end;
    fuel_trace := FuelTraceUnavailable