
open Prims

type z3version =
| Z3V_Unknown of Prims.string
| Z3V of (Prims.int * Prims.int * Prims.int)


let is_Z3V_Unknown = (fun _discr_ -> (match (_discr_) with
| Z3V_Unknown (_) -> begin
true
end
| _ -> begin
false
end))


let is_Z3V = (fun _discr_ -> (match (_discr_) with
| Z3V (_) -> begin
true
end
| _ -> begin
false
end))


let ___Z3V_Unknown____0 = (fun projectee -> (match (projectee) with
| Z3V_Unknown (_82_7) -> begin
_82_7
end))


let ___Z3V____0 = (fun projectee -> (match (projectee) with
| Z3V (_82_10) -> begin
_82_10
end))


let z3version_as_string : z3version  ->  Prims.string = (fun _82_1 -> (match (_82_1) with
| Z3V_Unknown (s) -> begin
(FStar_Util.format1 "unknown version: %s" s)
end
| Z3V (i, j, k) -> begin
(let _174_33 = (FStar_Util.string_of_int i)
in (let _174_32 = (FStar_Util.string_of_int j)
in (let _174_31 = (FStar_Util.string_of_int k)
in (FStar_Util.format3 "%s.%s.%s" _174_33 _174_32 _174_31))))
end))


let z3v_compare : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.int Prims.option = (fun known _82_23 -> (match (_82_23) with
| (w1, w2, w3) -> begin
(match (known) with
| Z3V_Unknown (_82_25) -> begin
None
end
| Z3V (k1, k2, k3) -> begin
Some (if (k1 <> w1) then begin
(w1 - k1)
end else begin
if (k2 <> w2) then begin
(w2 - k2)
end else begin
(w3 - k3)
end
end)
end)
end))


let z3v_le : z3version  ->  (Prims.int * Prims.int * Prims.int)  ->  Prims.bool = (fun known wanted -> (match ((z3v_compare known wanted)) with
| None -> begin
false
end
| Some (i) -> begin
(i >= 0)
end))


let _z3version : z3version Prims.option FStar_ST.ref = (FStar_Util.mk_ref None)


let get_z3version : Prims.unit  ->  z3version = (fun _82_37 -> (match (()) with
| () -> begin
(

let prefix = "Z3 version "
in (match ((FStar_ST.read _z3version)) with
| Some (version) -> begin
version
end
| None -> begin
(

let _82_47 = (let _174_44 = (FStar_Options.z3_exe ())
in (FStar_Util.run_proc _174_44 "-version" ""))
in (match (_82_47) with
| (_82_43, out, _82_46) -> begin
(

let out = (match ((FStar_Util.splitlines out)) with
| (x)::_82_49 when (FStar_Util.starts_with x prefix) -> begin
(

let x = (let _174_45 = (FStar_Util.substring_from x (FStar_String.length prefix))
in (FStar_Util.trim_string _174_45))
in (

let x = try
(match (()) with
| () -> begin
(FStar_List.map FStar_Util.int_of_string (FStar_Util.split x "."))
end)
with
| _82_57 -> begin
[]
end
in (match (x) with
| (i1)::(i2)::(i3)::[] -> begin
Z3V (((i1), (i2), (i3)))
end
| _82_66 -> begin
Z3V_Unknown (out)
end)))
end
| _82_68 -> begin
Z3V_Unknown (out)
end)
in (

let _82_70 = (FStar_ST.op_Colon_Equals _z3version (Some (out)))
in out))
end))
end))
end))


let ini_params : Prims.unit  ->  Prims.string = (fun _82_72 -> (match (()) with
| () -> begin
(

let z3_v = (get_z3version ())
in (

let _82_74 = if (let _174_50 = (get_z3version ())
in (z3v_le _174_50 ((4), (4), (0)))) then begin
(let _174_53 = (let _174_52 = (let _174_51 = (z3version_as_string z3_v)
in (FStar_Util.format1 "Z3 v4.4.1 is required; got %s\n" _174_51))
in FStar_Util.Failure (_174_52))
in (FStar_All.pipe_left Prims.raise _174_53))
end else begin
()
end
in "-smt2 -in AUTO_CONFIG=false MODEL=true SMT.RELEVANCY=2"))
end))


type label =
Prims.string


type unsat_core =
Prims.string Prims.list Prims.option


type z3status =
| UNSAT of unsat_core
| SAT of label Prims.list
| UNKNOWN of label Prims.list
| TIMEOUT of label Prims.list


let is_UNSAT = (fun _discr_ -> (match (_discr_) with
| UNSAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_SAT = (fun _discr_ -> (match (_discr_) with
| SAT (_) -> begin
true
end
| _ -> begin
false
end))


let is_UNKNOWN = (fun _discr_ -> (match (_discr_) with
| UNKNOWN (_) -> begin
true
end
| _ -> begin
false
end))


let is_TIMEOUT = (fun _discr_ -> (match (_discr_) with
| TIMEOUT (_) -> begin
true
end
| _ -> begin
false
end))


let ___UNSAT____0 = (fun projectee -> (match (projectee) with
| UNSAT (_82_78) -> begin
_82_78
end))


let ___SAT____0 = (fun projectee -> (match (projectee) with
| SAT (_82_81) -> begin
_82_81
end))


let ___UNKNOWN____0 = (fun projectee -> (match (projectee) with
| UNKNOWN (_82_84) -> begin
_82_84
end))


let ___TIMEOUT____0 = (fun projectee -> (match (projectee) with
| TIMEOUT (_82_87) -> begin
_82_87
end))


let status_to_string : z3status  ->  Prims.string = (fun _82_2 -> (match (_82_2) with
| SAT (_82_90) -> begin
"sat"
end
| UNSAT (_82_93) -> begin
"unsat"
end
| UNKNOWN (_82_96) -> begin
"unknown"
end
| TIMEOUT (_82_99) -> begin
"timeout"
end))


let tid : Prims.unit  ->  Prims.string = (fun _82_101 -> (match (()) with
| () -> begin
(let _174_114 = (FStar_Util.current_tid ())
in (FStar_All.pipe_right _174_114 FStar_Util.string_of_int))
end))


let new_z3proc : Prims.string  ->  FStar_Util.proc = (fun id -> (

let cond = (fun pid s -> (

let x = ((FStar_Util.trim_string s) = "Done!")
in x))
in (let _174_122 = (FStar_Options.z3_exe ())
in (let _174_121 = (ini_params ())
in (FStar_Util.start_process id _174_122 _174_121 cond)))))


type bgproc =
{grab : Prims.unit  ->  FStar_Util.proc; release : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit}


let is_Mkbgproc : bgproc  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkbgproc"))))


type query_log =
{set_module_name : Prims.string  ->  Prims.unit; append_to_log : Prims.string  ->  Prims.unit; close_log : Prims.unit  ->  Prims.unit; log_file_name : Prims.unit  ->  Prims.string}


let is_Mkquery_log : query_log  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkquery_log"))))


let query_logging : query_log = (

let log_file_opt = (FStar_Util.mk_ref None)
in (

let used_file_names = (FStar_Util.mk_ref [])
in (

let current_module_name = (FStar_Util.mk_ref None)
in (

let current_file_name = (FStar_Util.mk_ref None)
in (

let set_module_name = (fun n -> (FStar_ST.op_Colon_Equals current_module_name (Some (n))))
in (

let new_log_file = (fun _82_123 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_module_name)) with
| None -> begin
(FStar_All.failwith "current module not set")
end
| Some (n) -> begin
(

let file_name = (match ((let _174_193 = (FStar_ST.read used_file_names)
in (FStar_List.tryFind (fun _82_130 -> (match (_82_130) with
| (m, _82_129) -> begin
(n = m)
end)) _174_193))) with
| None -> begin
(

let _82_132 = (let _174_195 = (let _174_194 = (FStar_ST.read used_file_names)
in (((n), (0)))::_174_194)
in (FStar_ST.op_Colon_Equals used_file_names _174_195))
in n)
end
| Some (_82_135, k) -> begin
(

let _82_139 = (let _174_197 = (let _174_196 = (FStar_ST.read used_file_names)
in (((n), ((k + 1))))::_174_196)
in (FStar_ST.op_Colon_Equals used_file_names _174_197))
in (let _174_198 = (FStar_Util.string_of_int (k + 1))
in (FStar_Util.format2 "%s-%s" n _174_198)))
end)
in (

let file_name = (FStar_Util.format1 "queries-%s.smt2" file_name)
in (

let _82_143 = (FStar_ST.op_Colon_Equals current_file_name (Some (file_name)))
in (

let fh = (FStar_Util.open_file_for_writing file_name)
in (

let _82_146 = (FStar_ST.op_Colon_Equals log_file_opt (Some (fh)))
in fh)))))
end)
end))
in (

let get_log_file = (fun _82_149 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
(new_log_file ())
end
| Some (fh) -> begin
fh
end)
end))
in (

let append_to_log = (fun str -> (let _174_203 = (get_log_file ())
in (FStar_Util.append_to_file _174_203 str)))
in (

let close_log = (fun _82_156 -> (match (()) with
| () -> begin
(match ((FStar_ST.read log_file_opt)) with
| None -> begin
()
end
| Some (fh) -> begin
(

let _82_160 = (FStar_Util.close_file fh)
in (FStar_ST.op_Colon_Equals log_file_opt None))
end)
end))
in (

let log_file_name = (fun _82_163 -> (match (()) with
| () -> begin
(match ((FStar_ST.read current_file_name)) with
| None -> begin
(FStar_All.failwith "no log file")
end
| Some (n) -> begin
n
end)
end))
in {set_module_name = set_module_name; append_to_log = append_to_log; close_log = close_log; log_file_name = log_file_name}))))))))))


let bg_z3_proc : bgproc = (

let the_z3proc = (FStar_Util.mk_ref None)
in (

let new_proc = (

let ctr = (FStar_Util.mk_ref (- (1)))
in (fun _82_169 -> (match (()) with
| () -> begin
(let _174_212 = (let _174_211 = (

let _82_170 = (FStar_Util.incr ctr)
in (let _174_210 = (FStar_ST.read ctr)
in (FStar_All.pipe_right _174_210 FStar_Util.string_of_int)))
in (FStar_Util.format1 "bg-%s" _174_211))
in (new_z3proc _174_212))
end)))
in (

let z3proc = (fun _82_174 -> (match (()) with
| () -> begin
(

let _82_175 = if ((FStar_ST.read the_z3proc) = None) then begin
(let _174_216 = (let _174_215 = (new_proc ())
in Some (_174_215))
in (FStar_ST.op_Colon_Equals the_z3proc _174_216))
end else begin
()
end
in (let _174_217 = (FStar_ST.read the_z3proc)
in (FStar_Util.must _174_217)))
end))
in (

let x = []
in (

let grab = (fun _82_179 -> (match (()) with
| () -> begin
(

let _82_180 = (FStar_Util.monitor_enter x)
in (z3proc ()))
end))
in (

let release = (fun _82_183 -> (match (()) with
| () -> begin
(FStar_Util.monitor_exit x)
end))
in (

let refresh = (fun _82_185 -> (match (()) with
| () -> begin
(

let proc = (grab ())
in (

let _82_187 = (FStar_Util.kill_process proc)
in (

let _82_189 = (let _174_225 = (let _174_224 = (new_proc ())
in Some (_174_224))
in (FStar_ST.op_Colon_Equals the_z3proc _174_225))
in (

let _82_191 = (query_logging.close_log ())
in (release ())))))
end))
in {grab = grab; release = release; refresh = refresh})))))))


let doZ3Exe' : Prims.string  ->  FStar_Util.proc  ->  z3status = (fun input z3proc -> (

let parse = (fun z3out -> (

let lines = (FStar_All.pipe_right (FStar_String.split (('\n')::[]) z3out) (FStar_List.map FStar_Util.trim_string))
in (

let unsat_core = (fun lines -> (

let parse_core = (fun s -> (

let s = (FStar_Util.trim_string s)
in (

let s = (FStar_Util.substring s 1 ((FStar_String.length s) - 2))
in if (FStar_Util.starts_with s "error") then begin
None
end else begin
(let _174_237 = (FStar_All.pipe_right (FStar_Util.split s " ") (FStar_Util.sort_with FStar_String.compare))
in (FStar_All.pipe_right _174_237 (fun _174_236 -> Some (_174_236))))
end)))
in (match (lines) with
| ("<unsat-core>")::(core)::("</unsat-core>")::rest -> begin
(let _174_238 = (parse_core core)
in ((_174_238), (lines)))
end
| _82_212 -> begin
((None), (lines))
end)))
in (

let rec lblnegs = (fun lines -> (match (lines) with
| (lname)::("false")::rest -> begin
(let _174_241 = (lblnegs rest)
in (lname)::_174_241)
end
| (lname)::(_82_222)::rest -> begin
(lblnegs rest)
end
| _82_227 -> begin
[]
end))
in (

let rec unsat_core_and_lblnegs = (fun lines -> (

let _82_232 = (unsat_core lines)
in (match (_82_232) with
| (core_opt, rest) -> begin
(let _174_244 = (lblnegs rest)
in ((core_opt), (_174_244)))
end)))
in (

let rec result = (fun x -> (match (x) with
| ("timeout")::tl -> begin
TIMEOUT ([])
end
| ("unknown")::tl -> begin
(let _174_248 = (let _174_247 = (unsat_core_and_lblnegs tl)
in (Prims.snd _174_247))
in UNKNOWN (_174_248))
end
| ("sat")::tl -> begin
(let _174_250 = (let _174_249 = (unsat_core_and_lblnegs tl)
in (Prims.snd _174_249))
in SAT (_174_250))
end
| ("unsat")::tl -> begin
(let _174_252 = (let _174_251 = (unsat_core tl)
in (Prims.fst _174_251))
in UNSAT (_174_252))
end
| (_82_249)::tl -> begin
(result tl)
end
| _82_252 -> begin
(let _174_256 = (let _174_255 = (let _174_254 = (FStar_List.map (fun l -> (FStar_Util.format1 "<%s>" (FStar_Util.trim_string l))) lines)
in (FStar_String.concat "\n" _174_254))
in (FStar_Util.format1 "Got output lines: %s\n" _174_255))
in (FStar_All.pipe_left FStar_All.failwith _174_256))
end))
in (result lines)))))))
in (

let stdout = (FStar_Util.ask_process z3proc input)
in (parse (FStar_Util.trim_string stdout)))))


let doZ3Exe : Prims.bool  ->  Prims.string  ->  z3status = (

let ctr = (FStar_Util.mk_ref 0)
in (fun fresh input -> (

let z3proc = if fresh then begin
(

let _82_258 = (FStar_Util.incr ctr)
in (let _174_262 = (let _174_261 = (FStar_ST.read ctr)
in (FStar_Util.string_of_int _174_261))
in (new_z3proc _174_262)))
end else begin
(bg_z3_proc.grab ())
end
in (

let res = (doZ3Exe' input z3proc)
in (

let _82_262 = if fresh then begin
(FStar_Util.kill_process z3proc)
end else begin
(bg_z3_proc.release ())
end
in res)))))


let z3_options : Prims.unit  ->  Prims.string = (fun _82_264 -> (match (()) with
| () -> begin
"(set-option :global-decls false)(set-option :smt.mbqi false)(set-option :produce-unsat-cores true)\n"
end))


type 'a job =
{job : Prims.unit  ->  'a; callback : 'a  ->  Prims.unit}


let is_Mkjob = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkjob"))))


type z3job =
((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) job


let job_queue : z3job Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let pending_jobs : Prims.int FStar_ST.ref = (FStar_Util.mk_ref 0)


let with_monitor = (fun m f -> (

let _82_271 = (FStar_Util.monitor_enter m)
in (

let res = (f ())
in (

let _82_274 = (FStar_Util.monitor_exit m)
in res))))


let z3_job : Prims.bool  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  Prims.string  ->  Prims.unit  ->  ((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int) = (fun fresh label_messages input _82_279 -> (match (()) with
| () -> begin
(

let start = (FStar_Util.now ())
in (

let status = (doZ3Exe fresh input)
in (

let _82_285 = (let _174_298 = (FStar_Util.now ())
in (FStar_Util.time_diff start _174_298))
in (match (_82_285) with
| (_82_283, elapsed_time) -> begin
(

let result = (match (status) with
| UNSAT (core) -> begin
((FStar_Util.Inl (core)), (elapsed_time))
end
| (TIMEOUT (lblnegs)) | (SAT (lblnegs)) | (UNKNOWN (lblnegs)) -> begin
(

let _82_292 = if (FStar_Options.debug_any ()) then begin
(let _174_299 = (FStar_Util.format1 "Z3 says: %s\n" (status_to_string status))
in (FStar_All.pipe_left FStar_Util.print_string _174_299))
end else begin
()
end
in (

let failing_assertions = (FStar_All.pipe_right lblnegs (FStar_List.collect (fun l -> (match ((FStar_All.pipe_right label_messages (FStar_List.tryFind (fun _82_300 -> (match (_82_300) with
| (m, _82_297, _82_299) -> begin
((Prims.fst m) = l)
end))))) with
| None -> begin
[]
end
| Some (lbl, msg, r) -> begin
(((lbl), (msg), (r)))::[]
end))))
in ((FStar_Util.Inr (failing_assertions)), (elapsed_time))))
end)
in result)
end))))
end))


let rec dequeue' : Prims.unit  ->  Prims.unit = (fun _82_309 -> (match (()) with
| () -> begin
(

let j = (match ((FStar_ST.read job_queue)) with
| [] -> begin
(FStar_All.failwith "Impossible")
end
| (hd)::tl -> begin
(

let _82_314 = (FStar_ST.op_Colon_Equals job_queue tl)
in hd)
end)
in (

let _82_317 = (FStar_Util.incr pending_jobs)
in (

let _82_319 = (FStar_Util.monitor_exit job_queue)
in (

let _82_321 = (run_job j)
in (

let _82_324 = (with_monitor job_queue (fun _82_323 -> (match (()) with
| () -> begin
(FStar_Util.decr pending_jobs)
end)))
in (

let _82_326 = (dequeue ())
in ()))))))
end))
and dequeue : Prims.unit  ->  Prims.unit = (fun _82_328 -> (match (()) with
| () -> begin
(

let _82_329 = (FStar_Util.monitor_enter job_queue)
in (

let rec aux = (fun _82_332 -> (match (()) with
| () -> begin
(match ((FStar_ST.read job_queue)) with
| [] -> begin
(

let _82_334 = (FStar_Util.monitor_wait job_queue)
in (aux ()))
end
| _82_337 -> begin
(dequeue' ())
end)
end))
in (aux ())))
end))
and run_job : z3job  ->  Prims.unit = (fun j -> (let _174_311 = (j.job ())
in (FStar_All.pipe_left j.callback _174_311)))


let init : Prims.unit  ->  Prims.unit = (fun _82_339 -> (match (()) with
| () -> begin
(

let n_runners = ((FStar_Options.n_cores ()) - 1)
in (

let rec aux = (fun n -> if (n = 0) then begin
()
end else begin
(

let _82_343 = (FStar_Util.spawn dequeue)
in (aux (n - 1)))
end)
in (aux n_runners)))
end))


let enqueue : Prims.bool  ->  z3job  ->  Prims.unit = (fun fresh j -> if (not (fresh)) then begin
(run_job j)
end else begin
(

let _82_347 = (FStar_Util.monitor_enter job_queue)
in (

let _82_349 = (let _174_321 = (let _174_320 = (FStar_ST.read job_queue)
in (FStar_List.append _174_320 ((j)::[])))
in (FStar_ST.op_Colon_Equals job_queue _174_321))
in (

let _82_351 = (FStar_Util.monitor_pulse job_queue)
in (FStar_Util.monitor_exit job_queue))))
end)


let finish : Prims.unit  ->  Prims.unit = (fun _82_353 -> (match (()) with
| () -> begin
(

let bg = (bg_z3_proc.grab ())
in (

let _82_355 = (FStar_Util.kill_process bg)
in (

let _82_357 = (bg_z3_proc.release ())
in (

let rec aux = (fun _82_360 -> (match (()) with
| () -> begin
(

let _82_364 = (with_monitor job_queue (fun _82_361 -> (match (()) with
| () -> begin
(let _174_329 = (FStar_ST.read pending_jobs)
in (let _174_328 = (let _174_327 = (FStar_ST.read job_queue)
in (FStar_List.length _174_327))
in ((_174_329), (_174_328))))
end)))
in (match (_82_364) with
| (n, m) -> begin
if ((n + m) = 0) then begin
(let _174_330 = (FStar_TypeChecker_Errors.report_all ())
in (FStar_All.pipe_right _174_330 Prims.ignore))
end else begin
(

let _82_365 = (FStar_Util.sleep 500)
in (aux ()))
end
end))
end))
in (aux ())))))
end))


type scope_t =
FStar_SMTEncoding_Term.decl Prims.list Prims.list


let fresh_scope : FStar_SMTEncoding_Term.decl Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let bg_scope : FStar_SMTEncoding_Term.decl Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push : Prims.string  ->  Prims.unit = (fun msg -> (

let _82_368 = (let _174_334 = (let _174_333 = (FStar_ST.read fresh_scope)
in ((FStar_SMTEncoding_Term.Caption (msg))::[])::_174_333)
in (FStar_ST.op_Colon_Equals fresh_scope _174_334))
in (let _174_336 = (let _174_335 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Push)::[]) _174_335))
in (FStar_ST.op_Colon_Equals bg_scope _174_336))))


let pop : Prims.string  ->  Prims.unit = (fun msg -> (

let _82_371 = (let _174_340 = (let _174_339 = (FStar_ST.read fresh_scope)
in (FStar_List.tl _174_339))
in (FStar_ST.op_Colon_Equals fresh_scope _174_340))
in (let _174_342 = (let _174_341 = (FStar_ST.read bg_scope)
in (FStar_List.append ((FStar_SMTEncoding_Term.Caption (msg))::(FStar_SMTEncoding_Term.Pop)::[]) _174_341))
in (FStar_ST.op_Colon_Equals bg_scope _174_342))))


let giveZ3 : FStar_SMTEncoding_Term.decl Prims.list  ->  Prims.unit = (fun decls -> (

let _82_379 = (match ((FStar_ST.read fresh_scope)) with
| (hd)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd decls))::tl))
end
| _82_378 -> begin
(FStar_All.failwith "Impossible")
end)
in (let _174_346 = (let _174_345 = (FStar_ST.read bg_scope)
in (FStar_List.append (FStar_List.rev decls) _174_345))
in (FStar_ST.op_Colon_Equals bg_scope _174_346))))


let bgtheory : Prims.bool  ->  FStar_SMTEncoding_Term.decl Prims.list = (fun fresh -> if fresh then begin
(let _174_350 = (let _174_349 = (FStar_ST.read fresh_scope)
in (FStar_List.rev _174_349))
in (FStar_All.pipe_right _174_350 FStar_List.flatten))
end else begin
(

let bg = (FStar_ST.read bg_scope)
in (

let _82_383 = (FStar_ST.op_Colon_Equals bg_scope [])
in (FStar_List.rev bg)))
end)


let refresh : Prims.unit  ->  Prims.unit = (fun _82_385 -> (match (()) with
| () -> begin
(

let _82_386 = (bg_z3_proc.refresh ())
in (

let theory = (bgtheory true)
in (FStar_ST.op_Colon_Equals bg_scope (FStar_List.rev theory))))
end))


let mark : Prims.string  ->  Prims.unit = (fun msg -> (push msg))


let reset_mark : Prims.string  ->  Prims.unit = (fun msg -> (

let _82_391 = (pop msg)
in (refresh ())))


let commit_mark = (fun msg -> (match ((FStar_ST.read fresh_scope)) with
| (hd)::(s)::tl -> begin
(FStar_ST.op_Colon_Equals fresh_scope (((FStar_List.append hd s))::tl))
end
| _82_400 -> begin
(FStar_All.failwith "Impossible")
end))


let ask : unsat_core  ->  ((label * FStar_SMTEncoding_Term.sort) * Prims.string * FStar_Int64.int64) Prims.list  ->  FStar_SMTEncoding_Term.decl Prims.list  ->  (((unsat_core, FStar_SMTEncoding_Term.error_labels) FStar_Util.either * Prims.int)  ->  Prims.unit)  ->  Prims.unit = (fun core label_messages qry cb -> (

let filter_assertions = (fun theory -> (match (core) with
| None -> begin
((theory), (false))
end
| Some (core) -> begin
(

let _82_428 = (FStar_List.fold_right (fun d _82_414 -> (match (_82_414) with
| (theory, n_retained, n_pruned) -> begin
(match (d) with
| FStar_SMTEncoding_Term.Assume (_82_416, _82_418, Some (name)) -> begin
if (FStar_List.contains name core) then begin
(((d)::theory), ((n_retained + 1)), (n_pruned))
end else begin
if (FStar_Util.starts_with name "@") then begin
(((d)::theory), (n_retained), (n_pruned))
end else begin
((theory), (n_retained), ((n_pruned + 1)))
end
end
end
| _82_424 -> begin
(((d)::theory), (n_retained), (n_pruned))
end)
end)) theory (([]), (0), (0)))
in (match (_82_428) with
| (theory', n_retained, n_pruned) -> begin
(

let missed_assertions = (fun th core -> (

let missed = (let _174_382 = (FStar_All.pipe_right core (FStar_List.filter (fun nm -> (let _174_381 = (FStar_All.pipe_right th (FStar_Util.for_some (fun _82_3 -> (match (_82_3) with
| FStar_SMTEncoding_Term.Assume (_82_435, _82_437, Some (nm')) -> begin
(nm = nm')
end
| _82_443 -> begin
false
end))))
in (FStar_All.pipe_right _174_381 Prims.op_Negation)))))
in (FStar_All.pipe_right _174_382 (FStar_String.concat ", ")))
in (

let included = (let _174_384 = (FStar_All.pipe_right th (FStar_List.collect (fun _82_4 -> (match (_82_4) with
| FStar_SMTEncoding_Term.Assume (_82_447, _82_449, Some (nm)) -> begin
(nm)::[]
end
| _82_455 -> begin
[]
end))))
in (FStar_All.pipe_right _174_384 (FStar_String.concat ", ")))
in (FStar_Util.format2 "missed={%s}; included={%s}" missed included))))
in (

let _82_459 = if ((FStar_Options.hint_info ()) && (FStar_Options.debug_any ())) then begin
(

let n = (FStar_List.length core)
in (

let missed = if (n <> n_retained) then begin
(missed_assertions theory' core)
end else begin
""
end
in (let _174_388 = (FStar_Util.string_of_int n_retained)
in (let _174_387 = if (n <> n_retained) then begin
(let _174_385 = (FStar_Util.string_of_int n)
in (FStar_Util.format2 " (expected %s (%s); replay may be inaccurate)" _174_385 missed))
end else begin
""
end
in (let _174_386 = (FStar_Util.string_of_int n_pruned)
in (FStar_Util.print3 "Hint-info: Retained %s assertions%s and pruned %s assertions using recorded unsat core\n" _174_388 _174_387 _174_386))))))
end else begin
()
end
in (let _174_393 = (let _174_392 = (let _174_391 = (let _174_390 = (let _174_389 = (FStar_All.pipe_right core (FStar_String.concat ", "))
in (Prims.strcat "UNSAT CORE: " _174_389))
in FStar_SMTEncoding_Term.Caption (_174_390))
in (_174_391)::[])
in (FStar_List.append theory' _174_392))
in ((_174_393), (true)))))
end))
end))
in (

let theory = (bgtheory false)
in (

let theory = (FStar_List.append theory (FStar_List.append ((FStar_SMTEncoding_Term.Push)::[]) (FStar_List.append qry ((FStar_SMTEncoding_Term.Pop)::[]))))
in (

let _82_465 = (filter_assertions theory)
in (match (_82_465) with
| (theory, used_unsat_core) -> begin
(

let cb = (fun _82_469 -> (match (_82_469) with
| (uc_errs, time) -> begin
if used_unsat_core then begin
(match (uc_errs) with
| FStar_Util.Inl (_82_471) -> begin
(cb ((uc_errs), (time)))
end
| FStar_Util.Inr (_82_474) -> begin
(cb ((FStar_Util.Inr ([])), (time)))
end)
end else begin
(cb ((uc_errs), (time)))
end
end))
in (

let input = (let _174_396 = (FStar_List.map (FStar_SMTEncoding_Term.declToSmt (z3_options ())) theory)
in (FStar_All.pipe_right _174_396 (FStar_String.concat "\n")))
in (

let _82_477 = if (FStar_Options.log_queries ()) then begin
(query_logging.append_to_log input)
end else begin
()
end
in (enqueue false {job = (z3_job false label_messages input); callback = cb}))))
end))))))




