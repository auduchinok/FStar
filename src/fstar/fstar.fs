(*
   Copyright 2008-2016 Nikhil Swamy and Microsoft Research

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
module FStar.FStar

open FStar
open FStar.Util
open FStar.Getopt
open FStar.Ident
open FStar.Interactive

(* cleanup: kills background Z3 processes; relevant when --n_cores > 1; restore comand line args *)
let cleanup () = Util.kill_all () //Options.clear(); Options.init (); Options.parse_cmd_line () |> ignore

(* printing total error count *)
let report_errors () =
  let errs =
      if Options.universes ()
      then FStar.TypeChecker.Errors.get_err_count ()
      else FStar.Tc.Errors.get_err_count () in
  if errs > 0 then begin
    Util.print1_error "%s errors were reported (see above)\n" (string_of_int errs);
    exit 1
  end

(* printing a finished message *)
let finished_message fmods =
  if not (Options.silent ()) then begin
    fmods |> List.iter (fun (iface, name) ->
                let tag = if iface then "i'face" else "module" in
                if Options.should_print_message name.str
                then Util.print_string (Util.format2 "Verifying %s: %s\n" tag (Ident.text_of_lid name)));
    print_string (Util.format1 "%s\n" (Util.colorize_bold "All verification conditions discharged successfully"))
  end

(* Extraction to OCaml, F# or Kremlin *)
let codegen uf_mods_env =
  let opt = Options.codegen () in
  if opt <> None then
    let mllibs = match uf_mods_env with
        | Inl (fmods, env) -> snd <| Util.fold_map Extraction.ML.ExtractMod.extract (Extraction.ML.Env.mkContext env) fmods
        | Inr (umods, env) -> snd <| Util.fold_map Extraction.ML.Modul.extract (Extraction.ML.UEnv.mkContext env) umods in
    let mllibs = List.flatten mllibs in
    let ext = match opt with
      | Some "FSharp" -> ".fs"
      | Some "OCaml" -> ".ml"
      | Some "Kremlin" -> ".krml"
    in
    match opt with
    | Some "FSharp" | Some "OCaml" ->
        let newDocs = List.collect Extraction.ML.Code.doc_of_mllib mllibs in
        List.iter (fun (n,d) ->
          Util.write_file (Options.prepend_output_dir (n ^ ext)) (FStar.Format.pretty 120 d)
        ) newDocs
    | Some "Kremlin" ->
        let programs = List.flatten (List.map Extraction.Kremlin.translate mllibs) in
        let bin: Extraction.Kremlin.binary_format = Extraction.Kremlin.current_version, programs in
        save_value_to_file "out.krml" bin

module F_Util = FStar.Absyn.Util
module U_Util = FStar.Syntax.Util

let batch_check filenames =
    match Options.print_deps_only () with
    | Some _ -> Parser.Dep.print (Parser.Dep.collect Parser.Dep.VerifyAll filenames)
    | None ->
        if List.length filenames >= 1 then begin
          let verify_mode =
            match Options.verify_all (), Options.verify_module () with
            | true, [] -> Parser.Dep.VerifyAll
            | true, _  -> Util.print_error "--verify_module is incompatible with --verify_all"; exit 1
            | _, []    -> Parser.Dep.VerifyFigureItOut
            | _, _     -> Parser.Dep.VerifyUserList in

          if Options.universes () then
            let fmods, _, env = Universal.batch_mode_tc verify_mode filenames in
            report_errors ();
            codegen (Inr (fmods, env));
            finished_message (fmods |> List.map Universal.module_or_interface_name);
          else
            let fmods, dsenv, env = Stratified.batch_mode_tc verify_mode filenames in
            report_errors ();
            codegen (Inl (fmods, env));
            finished_message (fmods |> List.map Stratified.module_or_interface_name)
        end else
          Util.print_error "no file provided\n"

let interactive filenames =
    let filenames =
        if Options.explicit_deps () then begin
            if List.length filenames = 0 then
            Util.print_error "--explicit_deps was provided without a file list!\n";
            filenames
            end
        else begin
            if List.length filenames > 0 then
            Util.print_warning "ignoring the file list (no --explicit_deps)\n";
            detect_dependencies_with_first_interactive_chunk ()
            end in
    if Options.universes ()
    then let fmods, dsenv, env = Universal.batch_mode_tc Parser.Dep.VerifyUserList filenames in //check all the dependences in batch mode
        interactive_mode (dsenv, env) None Universal.interactive_tc //and then start checking chunks from the current buffer
    else let fmods, dsenv, env = Stratified.batch_mode_tc Parser.Dep.VerifyUserList filenames in //check all the dependences in batch mode
        interactive_mode (dsenv, env) None Stratified.interactive_tc //and then start checking chunks from the current buffer

let main () =
  try
    match Options.parse_cmd_line () with
    | Help, _            -> Options.display_usage (); exit 0
    | Error message, _   -> Util.print_string message
    | Success, filenames ->
        if Options.interactive ()
        then interactive filenames
        else batch_check filenames; cleanup (); batch_check filenames;

    cleanup ();
    exit 0
  with | e ->
    (begin
        if F_Util.handleable e then F_Util.handle_err false () e;
        if U_Util.handleable e then U_Util.handle_err false e;
        if (Options.trace_error()) then
          Util.print2_error "Unexpected error\n%s\n%s\n" (Util.message_of_exn e) (Util.trace_of_exn e)
        else if not (F_Util.handleable e || U_Util.handleable e) then
          Util.print1_error "Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.\n%s\n" (Util.message_of_exn e)
     end;
     cleanup ();
     FStar.TypeChecker.Errors.report_all () |> ignore;
     report_errors ();
     exit 1)
