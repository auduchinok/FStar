
open Prims
let new_uvar : FStar_Range.range  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.typ  ->  (FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.typ) = (fun r binders k -> (let binders = (FStar_All.pipe_right binders (FStar_List.filter (fun x -> (let _194_8 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _194_8 Prims.op_Negation)))))
in (let uv = (FStar_Unionfind.fresh FStar_Syntax_Syntax.Uvar)
in (match (binders) with
| [] -> begin
(let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (uv, uv))
end
| _91_37 -> begin
(let args = (FStar_Syntax_Util.args_of_non_null_binders binders)
in (let k' = (let _194_9 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.arrow binders _194_9))
in (let uv = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ((uv, k'))) None r)
in (let _194_10 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((uv, args))) (Some (k.FStar_Syntax_Syntax.n)) r)
in (_194_10, uv)))))
end))))

type uvi =
| TERM of ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term)
| UNIV of (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe)

let is_TERM : uvi  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| TERM (_) -> begin
true
end
| _ -> begin
false
end))

let is_UNIV : uvi  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UNIV (_) -> begin
true
end
| _ -> begin
false
end))

let ___TERM____0 : uvi  ->  ((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.term) = (fun projectee -> (match (projectee) with
| TERM (_91_43) -> begin
_91_43
end))

let ___UNIV____0 : uvi  ->  (FStar_Syntax_Syntax.universe_uvar * FStar_Syntax_Syntax.universe) = (fun projectee -> (match (projectee) with
| UNIV (_91_46) -> begin
_91_46
end))

type worklist =
{attempting : FStar_TypeChecker_Common.probs; wl_deferred : (Prims.int * Prims.string * FStar_TypeChecker_Common.prob) Prims.list; ctr : Prims.int; defer_ok : Prims.bool; smt_ok : Prims.bool; tcenv : FStar_TypeChecker_Env.env}

let is_Mkworklist : worklist  ->  Prims.bool = (Obj.magic ((fun _ -> (FStar_All.failwith "Not yet implemented:is_Mkworklist"))))

type solution =
| Success of FStar_TypeChecker_Common.deferred
| Failed of (FStar_TypeChecker_Common.prob * Prims.string)

let is_Success : solution  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Success (_) -> begin
true
end
| _ -> begin
false
end))

let is_Failed : solution  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| Failed (_) -> begin
true
end
| _ -> begin
false
end))

let ___Success____0 : solution  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| Success (_91_56) -> begin
_91_56
end))

let ___Failed____0 : solution  ->  (FStar_TypeChecker_Common.prob * Prims.string) = (fun projectee -> (match (projectee) with
| Failed (_91_59) -> begin
_91_59
end))

type variance =
| COVARIANT
| CONTRAVARIANT
| INVARIANT

let is_COVARIANT : variance  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| COVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_CONTRAVARIANT : variance  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| CONTRAVARIANT -> begin
true
end
| _ -> begin
false
end))

let is_INVARIANT : variance  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| INVARIANT -> begin
true
end
| _ -> begin
false
end))

type tprob =
(FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem

type cprob =
(FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem

type ('a, 'b) problem_t =
('a, 'b) FStar_TypeChecker_Common.problem

let rel_to_string : FStar_TypeChecker_Common.rel  ->  Prims.string = (fun _91_1 -> (match (_91_1) with
| FStar_TypeChecker_Common.EQ -> begin
"="
end
| FStar_TypeChecker_Common.SUB -> begin
"<:"
end
| FStar_TypeChecker_Common.SUBINV -> begin
":>"
end))

let term_to_string = (fun env t -> (FStar_Syntax_Print.term_to_string t))

let prob_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun env _91_2 -> (match (_91_2) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _194_109 = (let _194_108 = (term_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _194_107 = (let _194_106 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.lhs)
in (let _194_105 = (let _194_104 = (let _194_103 = (term_to_string env p.FStar_TypeChecker_Common.rhs)
in (let _194_102 = (let _194_101 = (FStar_Syntax_Print.tag_of_term p.FStar_TypeChecker_Common.rhs)
in (let _194_100 = (let _194_99 = (FStar_TypeChecker_Normalize.term_to_string env (Prims.fst p.FStar_TypeChecker_Common.logical_guard))
in (let _194_98 = (let _194_97 = (FStar_All.pipe_right p.FStar_TypeChecker_Common.reason (FStar_String.concat "\n\t\t\t"))
in (_194_97)::[])
in (_194_99)::_194_98))
in (_194_101)::_194_100))
in (_194_103)::_194_102))
in ((rel_to_string p.FStar_TypeChecker_Common.relation))::_194_104)
in (_194_106)::_194_105))
in (_194_108)::_194_107))
in (FStar_Util.format "\t%s (%s)\n\t\t%s\n\t%s (%s) (guard %s)\n\t\t<Reason>\n\t\t\t%s\n\t\t</Reason>" _194_109))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _194_111 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.lhs)
in (let _194_110 = (FStar_TypeChecker_Normalize.comp_to_string env p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format3 "\t%s \n\t\t%s\n\t%s" _194_111 (rel_to_string p.FStar_TypeChecker_Common.relation) _194_110)))
end))

let uvi_to_string : FStar_TypeChecker_Env.env  ->  uvi  ->  Prims.string = (fun env _91_3 -> (match (_91_3) with
| UNIV (u, t) -> begin
(let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _194_116 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _194_116 FStar_Util.string_of_int))
end
in (let _194_117 = (FStar_Syntax_Print.univ_to_string t)
in (FStar_Util.format2 "UNIV %s %s" x _194_117)))
end
| TERM ((u, _91_83), t) -> begin
(let x = if (FStar_ST.read FStar_Options.hide_uvar_nums) then begin
"?"
end else begin
(let _194_118 = (FStar_Unionfind.uvar_id u)
in (FStar_All.pipe_right _194_118 FStar_Util.string_of_int))
end
in (let _194_119 = (FStar_TypeChecker_Normalize.term_to_string env t)
in (FStar_Util.format2 "TERM %s %s" x _194_119)))
end))

let uvis_to_string : FStar_TypeChecker_Env.env  ->  uvi Prims.list  ->  Prims.string = (fun env uvis -> (let _194_124 = (FStar_List.map (uvi_to_string env) uvis)
in (FStar_All.pipe_right _194_124 (FStar_String.concat ", "))))

let names_to_string : (FStar_Syntax_Syntax.bv Prims.list * (FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.bv  ->  Prims.bool))  ->  Prims.string = (fun nms -> (let _194_134 = (let _194_133 = (FStar_Util.set_elements nms)
in (FStar_All.pipe_right _194_133 (FStar_List.map FStar_Syntax_Print.bv_to_string)))
in (FStar_All.pipe_right _194_134 (FStar_String.concat ", "))))

let args_to_string = (fun args -> (let _194_137 = (FStar_All.pipe_right args (FStar_List.map (fun _91_96 -> (match (_91_96) with
| (x, _91_95) -> begin
(FStar_Syntax_Print.term_to_string x)
end))))
in (FStar_All.pipe_right _194_137 (FStar_String.concat " "))))

let empty_worklist : FStar_TypeChecker_Env.env  ->  worklist = (fun env -> {attempting = []; wl_deferred = []; ctr = 0; defer_ok = true; smt_ok = true; tcenv = env})

let singleton : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist = (fun env prob -> (let _91_100 = (empty_worklist env)
in {attempting = (prob)::[]; wl_deferred = _91_100.wl_deferred; ctr = _91_100.ctr; defer_ok = _91_100.defer_ok; smt_ok = _91_100.smt_ok; tcenv = _91_100.tcenv}))

let wl_of_guard = (fun env g -> (let _91_104 = (empty_worklist env)
in (let _194_146 = (FStar_List.map Prims.snd g)
in {attempting = _194_146; wl_deferred = _91_104.wl_deferred; ctr = _91_104.ctr; defer_ok = false; smt_ok = _91_104.smt_ok; tcenv = _91_104.tcenv})))

let defer : Prims.string  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  worklist = (fun reason prob wl -> (let _91_109 = wl
in {attempting = _91_109.attempting; wl_deferred = ((wl.ctr, reason, prob))::wl.wl_deferred; ctr = _91_109.ctr; defer_ok = _91_109.defer_ok; smt_ok = _91_109.smt_ok; tcenv = _91_109.tcenv}))

let attempt : FStar_TypeChecker_Common.prob Prims.list  ->  worklist  ->  worklist = (fun probs wl -> (let _91_113 = wl
in {attempting = (FStar_List.append probs wl.attempting); wl_deferred = _91_113.wl_deferred; ctr = _91_113.ctr; defer_ok = _91_113.defer_ok; smt_ok = _91_113.smt_ok; tcenv = _91_113.tcenv}))

let giveup : FStar_TypeChecker_Env.env  ->  Prims.string  ->  FStar_TypeChecker_Common.prob  ->  solution = (fun env reason prob -> (let _91_118 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_163 = (prob_to_string env prob)
in (FStar_Util.print2 "Failed %s:\n%s\n" reason _194_163))
end else begin
()
end
in Failed ((prob, reason))))

let invert_rel : FStar_TypeChecker_Common.rel  ->  FStar_TypeChecker_Common.rel = (fun _91_4 -> (match (_91_4) with
| FStar_TypeChecker_Common.EQ -> begin
FStar_TypeChecker_Common.EQ
end
| FStar_TypeChecker_Common.SUB -> begin
FStar_TypeChecker_Common.SUBINV
end
| FStar_TypeChecker_Common.SUBINV -> begin
FStar_TypeChecker_Common.SUB
end))

let invert = (fun p -> (let _91_125 = p
in {FStar_TypeChecker_Common.pid = _91_125.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = p.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.relation = (invert_rel p.FStar_TypeChecker_Common.relation); FStar_TypeChecker_Common.rhs = p.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.element = _91_125.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_125.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_125.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_125.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_125.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_125.FStar_TypeChecker_Common.rank}))

let maybe_invert = (fun p -> if (p.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.SUBINV) then begin
(invert p)
end else begin
p
end)

let maybe_invert_p : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _91_5 -> (match (_91_5) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _194_170 -> FStar_TypeChecker_Common.TProb (_194_170)))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_right (maybe_invert p) (fun _194_171 -> FStar_TypeChecker_Common.CProb (_194_171)))
end))

let vary_rel : FStar_TypeChecker_Common.rel  ->  variance  ->  FStar_TypeChecker_Common.rel = (fun rel _91_6 -> (match (_91_6) with
| INVARIANT -> begin
FStar_TypeChecker_Common.EQ
end
| CONTRAVARIANT -> begin
(invert_rel rel)
end
| COVARIANT -> begin
rel
end))

let p_pid : FStar_TypeChecker_Common.prob  ->  Prims.int = (fun _91_7 -> (match (_91_7) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.pid
end))

let p_rel : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.rel = (fun _91_8 -> (match (_91_8) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.relation
end))

let p_reason : FStar_TypeChecker_Common.prob  ->  Prims.string Prims.list = (fun _91_9 -> (match (_91_9) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.reason
end))

let p_loc : FStar_TypeChecker_Common.prob  ->  FStar_Range.range = (fun _91_10 -> (match (_91_10) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.loc
end))

let p_guard : FStar_TypeChecker_Common.prob  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term) = (fun _91_11 -> (match (_91_11) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.logical_guard
end))

let p_scope : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.binders = (fun _91_12 -> (match (_91_12) with
| FStar_TypeChecker_Common.TProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end
| FStar_TypeChecker_Common.CProb (p) -> begin
p.FStar_TypeChecker_Common.scope
end))

let p_invert : FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun _91_13 -> (match (_91_13) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(FStar_All.pipe_left (fun _194_190 -> FStar_TypeChecker_Common.TProb (_194_190)) (invert p))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(FStar_All.pipe_left (fun _194_191 -> FStar_TypeChecker_Common.CProb (_194_191)) (invert p))
end))

let is_top_level_prob : FStar_TypeChecker_Common.prob  ->  Prims.bool = (fun p -> ((FStar_All.pipe_right (p_reason p) FStar_List.length) = 1))

let next_pid : Prims.unit  ->  Prims.int = (let ctr = (FStar_ST.alloc 0)
in (fun _91_175 -> (match (()) with
| () -> begin
(let _91_176 = (FStar_Util.incr ctr)
in (FStar_ST.read ctr))
end)))

let mk_problem = (fun scope orig lhs rel rhs elt reason -> (let _194_204 = (next_pid ())
in (let _194_203 = (new_uvar (p_loc orig) scope FStar_Syntax_Util.ktype0)
in {FStar_TypeChecker_Common.pid = _194_204; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _194_203; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None})))

let new_problem = (fun env lhs rel rhs elt loc reason -> (let scope = (FStar_TypeChecker_Env.all_binders env)
in (let _194_214 = (next_pid ())
in (let _194_213 = (let _194_212 = (FStar_TypeChecker_Env.get_range env)
in (new_uvar _194_212 scope FStar_Syntax_Util.ktype0))
in {FStar_TypeChecker_Common.pid = _194_214; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = _194_213; FStar_TypeChecker_Common.scope = scope; FStar_TypeChecker_Common.reason = (reason)::[]; FStar_TypeChecker_Common.loc = loc; FStar_TypeChecker_Common.rank = None}))))

let problem_using_guard = (fun orig lhs rel rhs elt reason -> (let _194_221 = (next_pid ())
in {FStar_TypeChecker_Common.pid = _194_221; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = rel; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = elt; FStar_TypeChecker_Common.logical_guard = (p_guard orig); FStar_TypeChecker_Common.scope = (p_scope orig); FStar_TypeChecker_Common.reason = (reason)::(p_reason orig); FStar_TypeChecker_Common.loc = (p_loc orig); FStar_TypeChecker_Common.rank = None}))

let guard_on_element = (fun problem x phi -> (match (problem.FStar_TypeChecker_Common.element) with
| None -> begin
(FStar_Syntax_Util.mk_forall x phi)
end
| Some (e) -> begin
(FStar_Syntax_Subst.subst ((FStar_Syntax_Syntax.NT ((x, e)))::[]) phi)
end))

let explain : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  Prims.string  ->  Prims.string = (fun env d s -> (let _194_233 = (FStar_All.pipe_left FStar_Range.string_of_range (p_loc d))
in (let _194_232 = (prob_to_string env d)
in (let _194_231 = (FStar_All.pipe_right (p_reason d) (FStar_String.concat "\n\t>"))
in (FStar_Util.format4 "(%s) Failed to solve the sub-problem\n%s\nWhich arose because:\n\t%s\nFailed because:%s\n" _194_233 _194_232 _194_231 s)))))

let commit : uvi Prims.list  ->  Prims.unit = (fun uvis -> (FStar_All.pipe_right uvis (FStar_List.iter (fun _91_14 -> (match (_91_14) with
| UNIV (u, t) -> begin
(match (t) with
| FStar_Syntax_Syntax.U_unif (u') -> begin
(FStar_Unionfind.union u u')
end
| _91_217 -> begin
(FStar_Unionfind.change u (Some (t)))
end)
end
| TERM ((u, _91_220), t) -> begin
(FStar_Syntax_Util.set_uvar u t)
end)))))

let find_term_uvar : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax FStar_Syntax_Syntax.uvar_basis FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.term Prims.option = (fun uv s -> (FStar_Util.find_map s (fun _91_15 -> (match (_91_15) with
| UNIV (_91_229) -> begin
None
end
| TERM ((u, _91_233), t) -> begin
if (FStar_Unionfind.equivalent uv u) then begin
Some (t)
end else begin
None
end
end))))

let find_univ_uvar : FStar_Syntax_Syntax.universe Prims.option FStar_Unionfind.uvar  ->  uvi Prims.list  ->  FStar_Syntax_Syntax.universe Prims.option = (fun u s -> (FStar_Util.find_map s (fun _91_16 -> (match (_91_16) with
| UNIV (u', t) -> begin
if (FStar_Unionfind.equivalent u u') then begin
Some (t)
end else begin
None
end
end
| _91_246 -> begin
None
end))))

let whnf : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _194_252 = (let _194_251 = (FStar_Syntax_Util.unmeta t)
in (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.WHNF)::[]) env _194_251))
in (FStar_Syntax_Subst.compress _194_252)))

let sn : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun env t -> (let _194_257 = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env t)
in (FStar_Syntax_Subst.compress _194_257)))

let norm_arg = (fun env t -> (let _194_260 = (sn env (Prims.fst t))
in (_194_260, (Prims.snd t))))

let sn_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list = (fun env binders -> (FStar_All.pipe_right binders (FStar_List.map (fun _91_257 -> (match (_91_257) with
| (x, imp) -> begin
(let _194_267 = (let _91_258 = x
in (let _194_266 = (sn env x.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _91_258.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_258.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _194_266}))
in (_194_267, imp))
end)))))

let norm_univ : worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe = (fun wl u -> (let rec aux = (fun u -> (let u = (FStar_Syntax_Subst.compress_univ u)
in (match (u) with
| FStar_Syntax_Syntax.U_succ (u) -> begin
(let _194_274 = (aux u)
in FStar_Syntax_Syntax.U_succ (_194_274))
end
| FStar_Syntax_Syntax.U_max (us) -> begin
(let _194_275 = (FStar_List.map aux us)
in FStar_Syntax_Syntax.U_max (_194_275))
end
| _91_270 -> begin
u
end)))
in (let _194_276 = (aux u)
in (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv _194_276))))

let normalize_refinement = (fun steps env wl t0 -> (let _194_281 = (whnf env t0)
in (FStar_TypeChecker_Normalize.normalize_refinement steps env _194_281)))

let base_and_refinement = (fun env wl t1 -> (let rec aux = (fun norm t1 -> (match (t1.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_refine (x, phi) -> begin
if norm then begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end else begin
(match ((normalize_refinement [] env wl t1)) with
| {FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x, phi); FStar_Syntax_Syntax.tk = _91_290; FStar_Syntax_Syntax.pos = _91_288; FStar_Syntax_Syntax.vars = _91_286} -> begin
(x.FStar_Syntax_Syntax.sort, Some ((x, phi)))
end
| tt -> begin
(let _194_291 = (let _194_290 = (FStar_Syntax_Print.term_to_string tt)
in (let _194_289 = (FStar_Syntax_Print.tag_of_term tt)
in (FStar_Util.format2 "impossible: Got %s ... %s\n" _194_290 _194_289)))
in (FStar_All.failwith _194_291))
end)
end
end
| (FStar_Syntax_Syntax.Tm_uinst (_)) | (FStar_Syntax_Syntax.Tm_fvar (_)) | (FStar_Syntax_Syntax.Tm_app (_)) -> begin
if norm then begin
(t1, None)
end else begin
(let _91_308 = (let _194_292 = (normalize_refinement [] env wl t1)
in (aux true _194_292))
in (match (_91_308) with
| (t2', refinement) -> begin
(match (refinement) with
| None -> begin
(t1, None)
end
| _91_311 -> begin
(t2', refinement)
end)
end))
end
end
| (FStar_Syntax_Syntax.Tm_type (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_name (_)) | (FStar_Syntax_Syntax.Tm_bvar (_)) | (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) | (FStar_Syntax_Syntax.Tm_uvar (_)) -> begin
(t1, None)
end
| (FStar_Syntax_Syntax.Tm_let (_)) | (FStar_Syntax_Syntax.Tm_match (_)) -> begin
(FStar_All.failwith "Unhandled cases!")
end
| (FStar_Syntax_Syntax.Tm_meta (_)) | (FStar_Syntax_Syntax.Tm_ascribed (_)) | (FStar_Syntax_Syntax.Tm_delayed (_)) | (FStar_Syntax_Syntax.Tm_unknown) -> begin
(let _194_295 = (let _194_294 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_293 = (FStar_Syntax_Print.tag_of_term t1)
in (FStar_Util.format2 "impossible (outer): Got %s ... %s\n" _194_294 _194_293)))
in (FStar_All.failwith _194_295))
end))
in (let _194_296 = (whnf env t1)
in (aux false _194_296))))

let unrefine : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun env t -> (let _194_301 = (base_and_refinement env (empty_worklist env) t)
in (FStar_All.pipe_right _194_301 Prims.fst)))

let trivial_refinement : FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun t -> (let _194_304 = (FStar_Syntax_Syntax.null_bv t)
in (_194_304, FStar_Syntax_Util.t_true)))

let as_refinement = (fun env wl t -> (let _91_357 = (base_and_refinement env wl t)
in (match (_91_357) with
| (t_base, refinement) -> begin
(match (refinement) with
| None -> begin
(trivial_refinement t_base)
end
| Some (x, phi) -> begin
(x, phi)
end)
end)))

let force_refinement = (fun _91_365 -> (match (_91_365) with
| (t_base, refopt) -> begin
(let _91_373 = (match (refopt) with
| Some (y, phi) -> begin
(y, phi)
end
| None -> begin
(trivial_refinement t_base)
end)
in (match (_91_373) with
| (y, phi) -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_refine ((y, phi))) None t_base.FStar_Syntax_Syntax.pos)
end))
end))

let wl_prob_to_string : worklist  ->  FStar_TypeChecker_Common.prob  ->  Prims.string = (fun wl _91_17 -> (match (_91_17) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _194_317 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _194_316 = (let _194_313 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (FStar_Syntax_Print.term_to_string _194_313))
in (let _194_315 = (let _194_314 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Syntax_Print.term_to_string _194_314))
in (FStar_Util.format4 "%s: %s  (%s)  %s" _194_317 _194_316 (rel_to_string p.FStar_TypeChecker_Common.relation) _194_315))))
end
| FStar_TypeChecker_Common.CProb (p) -> begin
(let _194_320 = (FStar_Util.string_of_int p.FStar_TypeChecker_Common.pid)
in (let _194_319 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _194_318 = (FStar_TypeChecker_Normalize.comp_to_string wl.tcenv p.FStar_TypeChecker_Common.rhs)
in (FStar_Util.format4 "%s: %s  (%s)  %s" _194_320 _194_319 (rel_to_string p.FStar_TypeChecker_Common.relation) _194_318))))
end))

let wl_to_string : worklist  ->  Prims.string = (fun wl -> (let _194_326 = (let _194_325 = (let _194_324 = (FStar_All.pipe_right wl.wl_deferred (FStar_List.map (fun _91_386 -> (match (_91_386) with
| (_91_382, _91_384, x) -> begin
x
end))))
in (FStar_List.append wl.attempting _194_324))
in (FStar_List.map (wl_prob_to_string wl) _194_325))
in (FStar_All.pipe_right _194_326 (FStar_String.concat "\n\t"))))

let u_abs : (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun x y -> (FStar_Syntax_Util.abs x y None))

let solve_prob' : Prims.bool  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun resolve_ok prob logical_guard uvis wl -> (let phi = (match (logical_guard) with
| None -> begin
FStar_Syntax_Util.t_true
end
| Some (phi) -> begin
phi
end)
in (let _91_401 = (p_guard prob)
in (match (_91_401) with
| (_91_399, uv) -> begin
(let _91_414 = (match ((let _194_341 = (FStar_Syntax_Subst.compress uv)
in _194_341.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uvar, k) -> begin
(let bs = (p_scope prob)
in (let bs = (FStar_All.pipe_right bs (FStar_List.filter (fun x -> (let _194_343 = (FStar_Syntax_Syntax.is_null_binder x)
in (FStar_All.pipe_right _194_343 Prims.op_Negation)))))
in (let phi = (u_abs bs phi)
in (let _91_410 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("Rel"))) then begin
(let _194_346 = (FStar_Util.string_of_int (p_pid prob))
in (let _194_345 = (FStar_Syntax_Print.term_to_string uv)
in (let _194_344 = (FStar_Syntax_Print.term_to_string phi)
in (FStar_Util.print3 "Solving %s (%s) with formula %s\n" _194_346 _194_345 _194_344))))
end else begin
()
end
in (FStar_Syntax_Util.set_uvar uvar phi)))))
end
| _91_413 -> begin
if (not (resolve_ok)) then begin
(FStar_All.failwith "Impossible: this instance has already been assigned a solution")
end else begin
()
end
end)
in (let _91_416 = (commit uvis)
in (let _91_418 = wl
in {attempting = _91_418.attempting; wl_deferred = _91_418.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _91_418.defer_ok; smt_ok = _91_418.smt_ok; tcenv = _91_418.tcenv})))
end))))

let extend_solution : Prims.int  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun pid sol wl -> (let _91_423 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _194_355 = (FStar_Util.string_of_int pid)
in (let _194_354 = (let _194_353 = (FStar_List.map (uvi_to_string wl.tcenv) sol)
in (FStar_All.pipe_right _194_353 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _194_355 _194_354)))
end else begin
()
end
in (let _91_425 = (commit sol)
in (let _91_427 = wl
in {attempting = _91_427.attempting; wl_deferred = _91_427.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _91_427.defer_ok; smt_ok = _91_427.smt_ok; tcenv = _91_427.tcenv}))))

let solve_prob : FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term Prims.option  ->  uvi Prims.list  ->  worklist  ->  worklist = (fun prob logical_guard uvis wl -> (let conj_guard = (fun t g -> (match ((t, g)) with
| (_91_437, FStar_TypeChecker_Common.Trivial) -> begin
t
end
| (None, FStar_TypeChecker_Common.NonTrivial (f)) -> begin
Some (f)
end
| (Some (t), FStar_TypeChecker_Common.NonTrivial (f)) -> begin
(let _194_368 = (FStar_Syntax_Util.mk_conj t f)
in Some (_194_368))
end))
in (let _91_449 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug wl.tcenv) (FStar_Options.Other ("RelCheck"))) then begin
(let _194_371 = (FStar_All.pipe_left FStar_Util.string_of_int (p_pid prob))
in (let _194_370 = (let _194_369 = (FStar_List.map (uvi_to_string wl.tcenv) uvis)
in (FStar_All.pipe_right _194_369 (FStar_String.concat ", ")))
in (FStar_Util.print2 "Solving %s: with %s\n" _194_371 _194_370)))
end else begin
()
end
in (solve_prob' false prob logical_guard uvis wl))))

let rec occurs = (fun wl uk t -> (let _194_381 = (let _194_379 = (FStar_Syntax_Free.uvars t)
in (FStar_All.pipe_right _194_379 FStar_Util.set_elements))
in (FStar_All.pipe_right _194_381 (FStar_Util.for_some (fun _91_458 -> (match (_91_458) with
| (uv, _91_457) -> begin
(FStar_Unionfind.equivalent uv (Prims.fst uk))
end))))))

let occurs_check = (fun env wl uk t -> (let occurs_ok = (not ((occurs wl uk t)))
in (let msg = if occurs_ok then begin
None
end else begin
(let _194_388 = (let _194_387 = (FStar_Syntax_Print.uvar_to_string (Prims.fst uk))
in (let _194_386 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format2 "occurs-check failed (%s occurs in %s)" _194_387 _194_386)))
in Some (_194_388))
end
in (occurs_ok, msg))))

let occurs_and_freevars_check = (fun env wl uk fvs t -> (let fvs_t = (FStar_Syntax_Free.names t)
in (let _91_473 = (occurs_check env wl uk t)
in (match (_91_473) with
| (occurs_ok, msg) -> begin
(let _194_420 = (FStar_Util.set_is_subset_of fvs_t fvs)
in (occurs_ok, _194_420, (msg, fvs, fvs_t)))
end))))

let intersect_vars = (fun v1 v2 -> (let as_set = (fun v -> (FStar_All.pipe_right v (FStar_List.fold_left (fun out x -> (FStar_Util.set_add (Prims.fst x) out)) FStar_Syntax_Syntax.no_names)))
in (let v1_set = (as_set v1)
in (let _91_491 = (FStar_All.pipe_right v2 (FStar_List.fold_left (fun _91_483 _91_486 -> (match ((_91_483, _91_486)) with
| ((isect, isect_set), (x, imp)) -> begin
if (let _194_429 = (FStar_Util.set_mem x v1_set)
in (FStar_All.pipe_left Prims.op_Negation _194_429)) then begin
(isect, isect_set)
end else begin
(let fvs = (FStar_Syntax_Free.names x.FStar_Syntax_Syntax.sort)
in if (FStar_Util.set_is_subset_of fvs isect_set) then begin
(let _194_430 = (FStar_Util.set_add x isect_set)
in (((x, imp))::isect, _194_430))
end else begin
(isect, isect_set)
end)
end
end)) ([], FStar_Syntax_Syntax.no_names)))
in (match (_91_491) with
| (isect, _91_490) -> begin
(FStar_List.rev isect)
end)))))

let binders_eq = (fun v1 v2 -> (((FStar_List.length v1) = (FStar_List.length v2)) && (FStar_List.forall2 (fun _91_497 _91_501 -> (match ((_91_497, _91_501)) with
| ((a, _91_496), (b, _91_500)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)) v1 v2)))

let pat_var_opt = (fun env seen arg -> (let hd = (norm_arg env arg)
in (match ((Prims.fst hd).FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (a) -> begin
if (FStar_All.pipe_right seen (FStar_Util.for_some (fun _91_511 -> (match (_91_511) with
| (b, _91_510) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end)))) then begin
None
end else begin
Some ((a, (Prims.snd hd)))
end
end
| _91_513 -> begin
None
end)))

let rec pat_vars : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.arg_qualifier Prims.option) Prims.list  ->  FStar_Syntax_Syntax.binders Prims.option = (fun env seen args -> (match (args) with
| [] -> begin
Some ((FStar_List.rev seen))
end
| hd::rest -> begin
(match ((pat_var_opt env seen hd)) with
| None -> begin
(let _91_522 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_445 = (FStar_All.pipe_left FStar_Syntax_Print.term_to_string (Prims.fst hd))
in (FStar_Util.print1 "Not a pattern: %s\n" _194_445))
end else begin
()
end
in None)
end
| Some (x) -> begin
(pat_vars env ((x)::seen) rest)
end)
end))

let destruct_flex_t = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, k) -> begin
(t, uv, k, [])
end
| FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (uv, k); FStar_Syntax_Syntax.tk = _91_536; FStar_Syntax_Syntax.pos = _91_534; FStar_Syntax_Syntax.vars = _91_532}, args) -> begin
(t, uv, k, args)
end
| _91_546 -> begin
(FStar_All.failwith "Not a flex-uvar")
end))

let destruct_flex_pattern = (fun env t -> (let _91_553 = (destruct_flex_t t)
in (match (_91_553) with
| (t, uv, k, args) -> begin
(match ((pat_vars env [] args)) with
| Some (vars) -> begin
((t, uv, k, args), Some (vars))
end
| _91_557 -> begin
((t, uv, k, args), None)
end)
end)))

type match_result =
| MisMatch
| HeadMatch
| FullMatch

let is_MisMatch : match_result  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| MisMatch -> begin
true
end
| _ -> begin
false
end))

let is_HeadMatch : match_result  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| HeadMatch -> begin
true
end
| _ -> begin
false
end))

let is_FullMatch : match_result  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| FullMatch -> begin
true
end
| _ -> begin
false
end))

let head_match : match_result  ->  match_result = (fun _91_18 -> (match (_91_18) with
| MisMatch -> begin
MisMatch
end
| _91_561 -> begin
HeadMatch
end))

let rec head_matches : FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  match_result = (fun t1 t2 -> (match ((let _194_461 = (let _194_458 = (FStar_Syntax_Util.unmeta t1)
in _194_458.FStar_Syntax_Syntax.n)
in (let _194_460 = (let _194_459 = (FStar_Syntax_Util.unmeta t2)
in _194_459.FStar_Syntax_Syntax.n)
in (_194_461, _194_460)))) with
| (FStar_Syntax_Syntax.Tm_name (x), FStar_Syntax_Syntax.Tm_name (y)) -> begin
if (FStar_Syntax_Syntax.bv_eq x y) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
if (FStar_Syntax_Syntax.fv_eq f g) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uinst (f, _91_576), FStar_Syntax_Syntax.Tm_uinst (g, _91_581)) -> begin
(let _194_462 = (head_matches f g)
in (FStar_All.pipe_right _194_462 head_match))
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
if (c = d) then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_uvar (uv, _91_592), FStar_Syntax_Syntax.Tm_uvar (uv', _91_597)) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
FullMatch
end else begin
MisMatch
end
end
| (FStar_Syntax_Syntax.Tm_refine (x, _91_603), FStar_Syntax_Syntax.Tm_refine (y, _91_608)) -> begin
(let _194_463 = (head_matches x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _194_463 head_match))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _91_614), _91_618) -> begin
(let _194_464 = (head_matches x.FStar_Syntax_Syntax.sort t2)
in (FStar_All.pipe_right _194_464 head_match))
end
| (_91_621, FStar_Syntax_Syntax.Tm_refine (x, _91_624)) -> begin
(let _194_465 = (head_matches t1 x.FStar_Syntax_Syntax.sort)
in (FStar_All.pipe_right _194_465 head_match))
end
| ((FStar_Syntax_Syntax.Tm_type (_), FStar_Syntax_Syntax.Tm_type (_))) | ((FStar_Syntax_Syntax.Tm_arrow (_), FStar_Syntax_Syntax.Tm_arrow (_))) -> begin
HeadMatch
end
| (FStar_Syntax_Syntax.Tm_app (head, _91_644), FStar_Syntax_Syntax.Tm_app (head', _91_649)) -> begin
(head_matches head head')
end
| (FStar_Syntax_Syntax.Tm_app (head, _91_655), _91_659) -> begin
(head_matches head t2)
end
| (_91_662, FStar_Syntax_Syntax.Tm_app (head, _91_665)) -> begin
(head_matches t1 head)
end
| _91_670 -> begin
MisMatch
end))

let head_matches_delta = (fun env wl t1 t2 -> (let success = (fun d r t1 t2 -> (r, if (d > 0) then begin
Some ((t1, t2))
end else begin
None
end))
in (let fail = (fun _91_681 -> (match (()) with
| () -> begin
(MisMatch, None)
end))
in (let rec aux = (fun d t1 t2 -> (match ((head_matches t1 t2)) with
| MisMatch -> begin
if (d = 2) then begin
(fail ())
end else begin
if (d = 1) then begin
(let t1' = (normalize_refinement ((FStar_TypeChecker_Normalize.Unfold)::[]) env wl t1)
in (let t2' = (normalize_refinement ((FStar_TypeChecker_Normalize.Unfold)::[]) env wl t2)
in (aux 2 t1' t2')))
end else begin
(let t1 = (normalize_refinement ((FStar_TypeChecker_Normalize.Inline)::[]) env wl t1)
in (let t2 = (normalize_refinement ((FStar_TypeChecker_Normalize.Inline)::[]) env wl t2)
in (aux (d + 1) t1 t2)))
end
end
end
| r -> begin
(success d r t1 t2)
end))
in (aux 0 t1 t2)))))

type tc =
| T of FStar_Syntax_Syntax.term
| C of FStar_Syntax_Syntax.comp

let is_T : tc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| T (_) -> begin
true
end
| _ -> begin
false
end))

let is_C : tc  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| C (_) -> begin
true
end
| _ -> begin
false
end))

let ___T____0 : tc  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| T (_91_694) -> begin
_91_694
end))

let ___C____0 : tc  ->  FStar_Syntax_Syntax.comp = (fun projectee -> (match (projectee) with
| C (_91_697) -> begin
_91_697
end))

type tcs =
tc Prims.list

let rec decompose = (fun env t -> (let t = (FStar_Syntax_Util.unmeta t)
in (let matches = (fun t' -> ((head_matches t t') <> MisMatch))
in (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_app (hd, args) -> begin
(let rebuild = (fun args' -> (let args = (FStar_List.map2 (fun x y -> (match ((x, y)) with
| ((_91_712, imp), T (t)) -> begin
(t, imp)
end
| _91_719 -> begin
(FStar_All.failwith "Bad reconstruction")
end)) args args')
in (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((hd, args))) None t.FStar_Syntax_Syntax.pos)))
in (let tcs = (FStar_All.pipe_right args (FStar_List.map (fun _91_724 -> (match (_91_724) with
| (t, _91_723) -> begin
(None, INVARIANT, T (t))
end))))
in (rebuild, matches, tcs)))
end
| FStar_Syntax_Syntax.Tm_arrow (bs, c) -> begin
(let fail = (fun _91_731 -> (match (()) with
| () -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (let _91_734 = (FStar_Syntax_Subst.open_comp bs c)
in (match (_91_734) with
| (bs, c) -> begin
(let rebuild = (fun tcs -> (let rec aux = (fun out bs tcs -> (match ((bs, tcs)) with
| ((x, imp)::bs, T (t)::tcs) -> begin
(aux ((((let _91_751 = x
in {FStar_Syntax_Syntax.ppname = _91_751.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_751.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t}), imp))::out) bs tcs)
end
| ([], C (c)::[]) -> begin
(FStar_Syntax_Util.arrow (FStar_List.rev out) c)
end
| _91_759 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (aux [] bs tcs)))
in (let rec decompose = (fun out _91_19 -> (match (_91_19) with
| [] -> begin
(FStar_List.rev (((None, COVARIANT, C (c)))::out))
end
| hd::rest -> begin
(let bopt = if (FStar_Syntax_Syntax.is_null_binder hd) then begin
None
end else begin
Some (hd)
end
in (decompose (((bopt, CONTRAVARIANT, T ((Prims.fst hd).FStar_Syntax_Syntax.sort)))::out) rest))
end))
in (let _194_559 = (decompose [] bs)
in (rebuild, matches, _194_559))))
end)))
end
| _91_769 -> begin
(let rebuild = (fun _91_20 -> (match (_91_20) with
| [] -> begin
t
end
| _91_773 -> begin
(FStar_All.failwith "Bad reconstruction")
end))
in (rebuild, (fun t -> true), []))
end))))

let un_T : tc  ->  FStar_Syntax_Syntax.term = (fun _91_21 -> (match (_91_21) with
| T (t) -> begin
t
end
| _91_780 -> begin
(FStar_All.failwith "Impossible")
end))

let arg_of_tc : tc  ->  FStar_Syntax_Syntax.arg = (fun _91_22 -> (match (_91_22) with
| T (t) -> begin
(FStar_Syntax_Syntax.as_arg t)
end
| _91_785 -> begin
(FStar_All.failwith "Impossible")
end))

let imitation_sub_probs = (fun orig env scope ps qs -> (let r = (p_loc orig)
in (let rel = (p_rel orig)
in (let sub_prob = (fun scope args q -> (match (q) with
| (_91_798, variance, T (ti)) -> begin
(let k = (let _91_806 = (FStar_Syntax_Util.type_u ())
in (match (_91_806) with
| (t, _91_805) -> begin
(let _194_581 = (new_uvar r scope t)
in (Prims.fst _194_581))
end))
in (let _91_810 = (new_uvar r scope k)
in (match (_91_810) with
| (gi_xs, gi) -> begin
(let gi_ps = (match (args) with
| [] -> begin
gi
end
| _91_813 -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_app ((gi, args))) None r)
end)
in (let _194_584 = (let _194_583 = (mk_problem scope orig gi_ps (vary_rel rel variance) ti None "type subterm")
in (FStar_All.pipe_left (fun _194_582 -> FStar_TypeChecker_Common.TProb (_194_582)) _194_583))
in (T (gi_xs), _194_584)))
end)))
end
| (_91_816, _91_818, C (_91_820)) -> begin
(FStar_All.failwith "impos")
end))
in (let rec aux = (fun scope args qs -> (match (qs) with
| [] -> begin
([], [], FStar_Syntax_Util.t_true)
end
| q::qs -> begin
(let _91_898 = (match (q) with
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Total (ti); FStar_Syntax_Syntax.tk = _91_838; FStar_Syntax_Syntax.pos = _91_836; FStar_Syntax_Syntax.vars = _91_834})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _194_593 = (let _194_592 = (FStar_Syntax_Syntax.mk_Total gi_xs)
in (FStar_All.pipe_left (fun _194_591 -> C (_194_591)) _194_592))
in (_194_593, (prob)::[]))
end
| _91_849 -> begin
(FStar_All.failwith "impossible")
end)
end
| (bopt, variance, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.GTotal (ti); FStar_Syntax_Syntax.tk = _91_857; FStar_Syntax_Syntax.pos = _91_855; FStar_Syntax_Syntax.vars = _91_853})) -> begin
(match ((sub_prob scope args (bopt, variance, T (ti)))) with
| (T (gi_xs), prob) -> begin
(let _194_596 = (let _194_595 = (FStar_Syntax_Syntax.mk_GTotal gi_xs)
in (FStar_All.pipe_left (fun _194_594 -> C (_194_594)) _194_595))
in (_194_596, (prob)::[]))
end
| _91_868 -> begin
(FStar_All.failwith "impossible")
end)
end
| (_91_870, _91_872, C ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Comp (c); FStar_Syntax_Syntax.tk = _91_878; FStar_Syntax_Syntax.pos = _91_876; FStar_Syntax_Syntax.vars = _91_874})) -> begin
(let components = (FStar_All.pipe_right c.FStar_Syntax_Syntax.effect_args (FStar_List.map (fun t -> (None, INVARIANT, T ((Prims.fst t))))))
in (let components = ((None, COVARIANT, T (c.FStar_Syntax_Syntax.result_typ)))::components
in (let _91_889 = (let _194_598 = (FStar_List.map (sub_prob scope args) components)
in (FStar_All.pipe_right _194_598 FStar_List.unzip))
in (match (_91_889) with
| (tcs, sub_probs) -> begin
(let gi_xs = (let _194_603 = (let _194_602 = (let _194_599 = (FStar_List.hd tcs)
in (FStar_All.pipe_right _194_599 un_T))
in (let _194_601 = (let _194_600 = (FStar_List.tl tcs)
in (FStar_All.pipe_right _194_600 (FStar_List.map arg_of_tc)))
in {FStar_Syntax_Syntax.effect_name = c.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = _194_602; FStar_Syntax_Syntax.effect_args = _194_601; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags}))
in (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp _194_603))
in (C (gi_xs), sub_probs))
end))))
end
| _91_892 -> begin
(let _91_895 = (sub_prob scope args q)
in (match (_91_895) with
| (ktec, prob) -> begin
(ktec, (prob)::[])
end))
end)
in (match (_91_898) with
| (tc, probs) -> begin
(let _91_911 = (match (q) with
| (Some (b), _91_902, _91_904) -> begin
(let _194_605 = (let _194_604 = (FStar_Syntax_Util.arg_of_non_null_binder b)
in (_194_604)::args)
in (Some (b), (b)::scope, _194_605))
end
| _91_907 -> begin
(None, scope, args)
end)
in (match (_91_911) with
| (bopt, scope, args) -> begin
(let _91_915 = (aux scope args qs)
in (match (_91_915) with
| (sub_probs, tcs, f) -> begin
(let f = (match (bopt) with
| None -> begin
(let _194_608 = (let _194_607 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (f)::_194_607)
in (FStar_Syntax_Util.mk_conj_l _194_608))
end
| Some (b) -> begin
(let _194_612 = (let _194_611 = (FStar_Syntax_Util.mk_forall (Prims.fst b) f)
in (let _194_610 = (FStar_All.pipe_right probs (FStar_List.map (fun prob -> (FStar_All.pipe_right (p_guard prob) Prims.fst))))
in (_194_611)::_194_610))
in (FStar_Syntax_Util.mk_conj_l _194_612))
end)
in ((FStar_List.append probs sub_probs), (tc)::tcs, f))
end))
end))
end))
end))
in (aux scope ps qs))))))

let rec eq_tm : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  Prims.bool = (fun t1 t2 -> (let t1 = (FStar_Syntax_Subst.compress t1)
in (let t2 = (FStar_Syntax_Subst.compress t2)
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
(FStar_Syntax_Syntax.bv_eq a b)
end
| (FStar_Syntax_Syntax.Tm_fvar (f), FStar_Syntax_Syntax.Tm_fvar (g)) -> begin
(FStar_Syntax_Syntax.fv_eq f g)
end
| (FStar_Syntax_Syntax.Tm_constant (c), FStar_Syntax_Syntax.Tm_constant (d)) -> begin
(c = d)
end
| (FStar_Syntax_Syntax.Tm_uvar (u1, _91_943), FStar_Syntax_Syntax.Tm_uvar (u2, _91_948)) -> begin
(FStar_Unionfind.equivalent u1 u2)
end
| (FStar_Syntax_Syntax.Tm_app (h1, args1), FStar_Syntax_Syntax.Tm_app (h2, args2)) -> begin
((eq_tm h1 h2) && (eq_args args1 args2))
end
| _91_962 -> begin
false
end))))
and eq_args : FStar_Syntax_Syntax.args  ->  FStar_Syntax_Syntax.args  ->  Prims.bool = (fun a1 a2 -> (((FStar_List.length a1) = (FStar_List.length a2)) && (FStar_List.forall2 (fun _91_968 _91_972 -> (match ((_91_968, _91_972)) with
| ((a1, _91_967), (a2, _91_971)) -> begin
(eq_tm a1 a2)
end)) a1 a2)))

type flex_t =
(FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ * FStar_Syntax_Syntax.args)

type im_or_proj_t =
((FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.typ) * FStar_Syntax_Syntax.arg Prims.list * FStar_Syntax_Syntax.binders * ((tc Prims.list  ->  FStar_Syntax_Syntax.typ) * (FStar_Syntax_Syntax.typ  ->  Prims.bool) * (FStar_Syntax_Syntax.binder Prims.option * variance * tc) Prims.list))

let rigid_rigid : Prims.int = 0

let flex_rigid_eq : Prims.int = 1

let flex_refine_inner : Prims.int = 2

let flex_refine : Prims.int = 3

let flex_rigid : Prims.int = 4

let rigid_flex : Prims.int = 5

let refine_flex : Prims.int = 6

let flex_flex : Prims.int = 7

let compress_tprob = (fun wl p -> (let _91_975 = p
in (let _194_634 = (whnf wl.tcenv p.FStar_TypeChecker_Common.lhs)
in (let _194_633 = (whnf wl.tcenv p.FStar_TypeChecker_Common.rhs)
in {FStar_TypeChecker_Common.pid = _91_975.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _194_634; FStar_TypeChecker_Common.relation = _91_975.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _194_633; FStar_TypeChecker_Common.element = _91_975.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_975.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_975.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_975.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_975.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_975.FStar_TypeChecker_Common.rank}))))

let compress_prob : worklist  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.prob = (fun wl p -> (match (p) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(let _194_640 = (compress_tprob wl p)
in (FStar_All.pipe_right _194_640 (fun _194_639 -> FStar_TypeChecker_Common.TProb (_194_639))))
end
| FStar_TypeChecker_Common.CProb (_91_982) -> begin
p
end))

let rank : worklist  ->  FStar_TypeChecker_Common.prob  ->  (Prims.int * FStar_TypeChecker_Common.prob) = (fun wl pr -> (let prob = (let _194_645 = (compress_prob wl pr)
in (FStar_All.pipe_right _194_645 maybe_invert_p))
in (match (prob) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(let _91_992 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_91_992) with
| (lh, _91_991) -> begin
(let _91_996 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.rhs)
in (match (_91_996) with
| (rh, _91_995) -> begin
(let _91_1052 = (match ((lh.FStar_Syntax_Syntax.n, rh.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_uvar (_91_998), FStar_Syntax_Syntax.Tm_uvar (_91_1001)) -> begin
(flex_flex, tp)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uvar (_))) when (tp.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(flex_rigid_eq, tp)
end
| (FStar_Syntax_Syntax.Tm_uvar (_91_1017), _91_1020) -> begin
(let _91_1024 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.rhs)
in (match (_91_1024) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(flex_rigid, tp)
end
| _91_1027 -> begin
(let rank = if (is_top_level_prob prob) then begin
flex_refine
end else begin
flex_refine_inner
end
in (let _194_647 = (let _91_1029 = tp
in (let _194_646 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _91_1029.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_1029.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _91_1029.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _194_646; FStar_TypeChecker_Common.element = _91_1029.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_1029.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_1029.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_1029.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_1029.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_1029.FStar_TypeChecker_Common.rank}))
in (rank, _194_647)))
end)
end))
end
| (_91_1032, FStar_Syntax_Syntax.Tm_uvar (_91_1034)) -> begin
(let _91_1039 = (base_and_refinement wl.tcenv wl tp.FStar_TypeChecker_Common.lhs)
in (match (_91_1039) with
| (b, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(rigid_flex, tp)
end
| _91_1042 -> begin
(let _194_649 = (let _91_1043 = tp
in (let _194_648 = (force_refinement (b, ref_opt))
in {FStar_TypeChecker_Common.pid = _91_1043.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _194_648; FStar_TypeChecker_Common.relation = _91_1043.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _91_1043.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_1043.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_1043.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_1043.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_1043.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_1043.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_1043.FStar_TypeChecker_Common.rank}))
in (refine_flex, _194_649))
end)
end))
end
| (_91_1046, _91_1048) -> begin
(rigid_rigid, tp)
end)
in (match (_91_1052) with
| (rank, tp) -> begin
(let _194_651 = (FStar_All.pipe_right (let _91_1053 = tp
in {FStar_TypeChecker_Common.pid = _91_1053.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_1053.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _91_1053.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _91_1053.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_1053.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_1053.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_1053.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_1053.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_1053.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rank)}) (fun _194_650 -> FStar_TypeChecker_Common.TProb (_194_650)))
in (rank, _194_651))
end))
end))
end))
end
| FStar_TypeChecker_Common.CProb (cp) -> begin
(let _194_653 = (FStar_All.pipe_right (let _91_1057 = cp
in {FStar_TypeChecker_Common.pid = _91_1057.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_1057.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _91_1057.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _91_1057.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_1057.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_1057.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_1057.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_1057.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_1057.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = Some (rigid_rigid)}) (fun _194_652 -> FStar_TypeChecker_Common.CProb (_194_652)))
in (rigid_rigid, _194_653))
end)))

let next_prob : worklist  ->  (FStar_TypeChecker_Common.prob Prims.option * FStar_TypeChecker_Common.prob Prims.list * Prims.int) = (fun wl -> (let rec aux = (fun _91_1064 probs -> (match (_91_1064) with
| (min_rank, min, out) -> begin
(match (probs) with
| [] -> begin
(min, out, min_rank)
end
| hd::tl -> begin
(let _91_1072 = (rank wl hd)
in (match (_91_1072) with
| (rank, hd) -> begin
if (rank <= flex_rigid_eq) then begin
(match (min) with
| None -> begin
(Some (hd), (FStar_List.append out tl), rank)
end
| Some (m) -> begin
(Some (hd), (FStar_List.append out ((m)::tl)), rank)
end)
end else begin
if (rank < min_rank) then begin
(match (min) with
| None -> begin
(aux (rank, Some (hd), out) tl)
end
| Some (m) -> begin
(aux (rank, Some (hd), (m)::out) tl)
end)
end else begin
(aux (min_rank, min, (hd)::out) tl)
end
end
end))
end)
end))
in (aux ((flex_flex + 1), None, []) wl.attempting)))

let is_flex_rigid : Prims.int  ->  Prims.bool = (fun rank -> ((flex_refine_inner <= rank) && (rank <= flex_rigid)))

type univ_eq_sol =
| UDeferred of worklist
| USolved of worklist
| UFailed of Prims.string

let is_UDeferred : univ_eq_sol  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UDeferred (_) -> begin
true
end
| _ -> begin
false
end))

let is_USolved : univ_eq_sol  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| USolved (_) -> begin
true
end
| _ -> begin
false
end))

let is_UFailed : univ_eq_sol  ->  Prims.bool = (fun _discr_ -> (match (_discr_) with
| UFailed (_) -> begin
true
end
| _ -> begin
false
end))

let ___UDeferred____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| UDeferred (_91_1082) -> begin
_91_1082
end))

let ___USolved____0 : univ_eq_sol  ->  worklist = (fun projectee -> (match (projectee) with
| USolved (_91_1085) -> begin
_91_1085
end))

let ___UFailed____0 : univ_eq_sol  ->  Prims.string = (fun projectee -> (match (projectee) with
| UFailed (_91_1088) -> begin
_91_1088
end))

let rec solve_universe_eq : Prims.int  ->  worklist  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  univ_eq_sol = (fun orig wl u1 u2 -> (let u1 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u1)
in (let u2 = (FStar_TypeChecker_Normalize.normalize_universe wl.tcenv u2)
in (let rec occurs_univ = (fun v1 u -> (match (u) with
| FStar_Syntax_Syntax.U_max (us) -> begin
(FStar_All.pipe_right us (FStar_Util.for_some (fun u -> (let _91_1104 = (FStar_Syntax_Util.univ_kernel u)
in (match (_91_1104) with
| (k, _91_1103) -> begin
(match (k) with
| FStar_Syntax_Syntax.U_unif (v2) -> begin
(FStar_Unionfind.equivalent v1 v2)
end
| _91_1108 -> begin
false
end)
end)))))
end
| _91_1110 -> begin
(occurs_univ v1 (FStar_Syntax_Syntax.U_max ((u)::[])))
end))
in (let try_umax_components = (fun u1 u2 msg -> (match ((u1, u2)) with
| (FStar_Syntax_Syntax.U_max (_91_1116), FStar_Syntax_Syntax.U_max (_91_1119)) -> begin
(let _194_725 = (let _194_724 = (FStar_Syntax_Print.univ_to_string u1)
in (let _194_723 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format2 "Unable to unify universes: %s and %s" _194_724 _194_723)))
in UFailed (_194_725))
end
| ((FStar_Syntax_Syntax.U_max (us), u')) | ((u', FStar_Syntax_Syntax.U_max (us))) -> begin
(let rec aux = (fun wl us -> (match (us) with
| [] -> begin
USolved (wl)
end
| u::us -> begin
(match ((solve_universe_eq orig wl u u')) with
| USolved (wl) -> begin
(aux wl us)
end
| failed -> begin
failed
end)
end))
in (aux wl us))
end
| _91_1139 -> begin
(let _194_732 = (let _194_731 = (FStar_Syntax_Print.univ_to_string u1)
in (let _194_730 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Unable to unify universes: %s and %s (%s)" _194_731 _194_730 msg)))
in UFailed (_194_732))
end))
in (match ((u1, u2)) with
| ((FStar_Syntax_Syntax.U_bvar (_), _)) | ((FStar_Syntax_Syntax.U_unknown, _)) | ((_, FStar_Syntax_Syntax.U_bvar (_))) | ((_, FStar_Syntax_Syntax.U_unknown)) -> begin
(FStar_All.failwith "Impossible: locally nameless")
end
| (FStar_Syntax_Syntax.U_unif (v1), FStar_Syntax_Syntax.U_unif (v2)) -> begin
if (FStar_Unionfind.equivalent v1 v2) then begin
USolved (wl)
end else begin
(let wl = (extend_solution orig ((UNIV ((v1, u2)))::[]) wl)
in USolved (wl))
end
end
| ((FStar_Syntax_Syntax.U_unif (v1), u)) | ((u, FStar_Syntax_Syntax.U_unif (v1))) -> begin
(let u = (norm_univ wl u)
in if (occurs_univ v1 u) then begin
(let _194_735 = (let _194_734 = (FStar_Syntax_Print.univ_to_string (FStar_Syntax_Syntax.U_unif (v1)))
in (let _194_733 = (FStar_Syntax_Print.univ_to_string u)
in (FStar_Util.format2 "Failed occurs check: %s occurs in %s" _194_734 _194_733)))
in (try_umax_components u1 u2 _194_735))
end else begin
(let _194_736 = (extend_solution orig ((UNIV ((v1, u)))::[]) wl)
in USolved (_194_736))
end)
end
| (FStar_Syntax_Syntax.U_zero, FStar_Syntax_Syntax.U_zero) -> begin
USolved (wl)
end
| (FStar_Syntax_Syntax.U_succ (u1), FStar_Syntax_Syntax.U_succ (u2)) -> begin
(solve_universe_eq orig wl u1 u2)
end
| ((FStar_Syntax_Syntax.U_succ (_), _)) | ((FStar_Syntax_Syntax.U_zero, _)) | ((_, FStar_Syntax_Syntax.U_succ (_))) | ((_, FStar_Syntax_Syntax.U_zero)) -> begin
UFailed ("Incompatible universes")
end
| (FStar_Syntax_Syntax.U_name (x), FStar_Syntax_Syntax.U_name (y)) when (x.FStar_Ident.idText = y.FStar_Ident.idText) -> begin
USolved (wl)
end
| ((FStar_Syntax_Syntax.U_max (_), _)) | ((_, FStar_Syntax_Syntax.U_max (_))) -> begin
if wl.defer_ok then begin
UDeferred (wl)
end else begin
(let u1 = (norm_univ wl u1)
in (let u2 = (norm_univ wl u2)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
USolved (wl)
end else begin
(try_umax_components u1 u2 "")
end))
end
end
| ((FStar_Syntax_Syntax.U_name (_), _)) | ((_, FStar_Syntax_Syntax.U_name (_))) -> begin
UFailed ("Incompatible universes")
end))))))

let rec solve : FStar_TypeChecker_Env.env  ->  worklist  ->  solution = (fun env probs -> (let _91_1234 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _194_779 = (wl_to_string probs)
in (FStar_Util.print1 "solve:\n\t%s\n" _194_779))
end else begin
()
end
in (match ((next_prob probs)) with
| (Some (hd), tl, rank) -> begin
(let probs = (let _91_1241 = probs
in {attempting = tl; wl_deferred = _91_1241.wl_deferred; ctr = _91_1241.ctr; defer_ok = _91_1241.defer_ok; smt_ok = _91_1241.smt_ok; tcenv = _91_1241.tcenv})
in (match (hd) with
| FStar_TypeChecker_Common.CProb (cp) -> begin
(solve_c env (maybe_invert cp) probs)
end
| FStar_TypeChecker_Common.TProb (tp) -> begin
if (((not (probs.defer_ok)) && (flex_refine_inner <= rank)) && (rank <= flex_rigid)) then begin
(match ((solve_flex_rigid_join env tp probs)) with
| None -> begin
(solve_t' env (maybe_invert tp) probs)
end
| Some (wl) -> begin
(solve env wl)
end)
end else begin
(solve_t' env (maybe_invert tp) probs)
end
end))
end
| (None, _91_1253, _91_1255) -> begin
(match (probs.wl_deferred) with
| [] -> begin
Success ([])
end
| _91_1259 -> begin
(let _91_1268 = (FStar_All.pipe_right probs.wl_deferred (FStar_List.partition (fun _91_1265 -> (match (_91_1265) with
| (c, _91_1262, _91_1264) -> begin
(c < probs.ctr)
end))))
in (match (_91_1268) with
| (attempt, rest) -> begin
(match (attempt) with
| [] -> begin
(let _194_782 = (FStar_List.map (fun _91_1274 -> (match (_91_1274) with
| (_91_1271, x, y) -> begin
(x, y)
end)) probs.wl_deferred)
in Success (_194_782))
end
| _91_1276 -> begin
(let _194_785 = (let _91_1277 = probs
in (let _194_784 = (FStar_All.pipe_right attempt (FStar_List.map (fun _91_1284 -> (match (_91_1284) with
| (_91_1280, _91_1282, y) -> begin
y
end))))
in {attempting = _194_784; wl_deferred = rest; ctr = _91_1277.ctr; defer_ok = _91_1277.defer_ok; smt_ok = _91_1277.smt_ok; tcenv = _91_1277.tcenv}))
in (solve env _194_785))
end)
end))
end)
end)))
and solve_one_universe_eq : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  worklist  ->  solution = (fun env orig u1 u2 wl -> (match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(let _194_791 = (solve_prob orig None [] wl)
in (solve env _194_791))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "" orig wl))
end))
and solve_maybe_uinsts : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term  ->  worklist  ->  univ_eq_sol = (fun env orig t1 t2 wl -> (let rec aux = (fun wl us1 us2 -> (match ((us1, us2)) with
| ([], []) -> begin
USolved (wl)
end
| (u1::us1, u2::us2) -> begin
(match ((solve_universe_eq (p_pid orig) wl u1 u2)) with
| USolved (wl) -> begin
(aux wl us1 us2)
end
| failed_or_deferred -> begin
failed_or_deferred
end)
end
| _91_1319 -> begin
UFailed ("Unequal number of universes")
end))
in (match ((let _194_806 = (let _194_803 = (whnf env t1)
in _194_803.FStar_Syntax_Syntax.n)
in (let _194_805 = (let _194_804 = (whnf env t2)
in _194_804.FStar_Syntax_Syntax.n)
in (_194_806, _194_805)))) with
| (FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (f); FStar_Syntax_Syntax.tk = _91_1325; FStar_Syntax_Syntax.pos = _91_1323; FStar_Syntax_Syntax.vars = _91_1321}, us1), FStar_Syntax_Syntax.Tm_uinst ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar (g); FStar_Syntax_Syntax.tk = _91_1337; FStar_Syntax_Syntax.pos = _91_1335; FStar_Syntax_Syntax.vars = _91_1333}, us2)) -> begin
(let b = (FStar_Syntax_Syntax.fv_eq f g)
in (let _91_1346 = ()
in (aux wl us1 us2)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) -> begin
(FStar_All.failwith "Impossible: expect head symbols to match")
end
| _91_1361 -> begin
USolved (wl)
end)))
and giveup_or_defer : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  Prims.string  ->  solution = (fun env orig wl msg -> if wl.defer_ok then begin
(let _91_1366 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_811 = (prob_to_string env orig)
in (FStar_Util.print2 "\n\t\tDeferring %s\n\t\tBecause %s\n" _194_811 msg))
end else begin
()
end
in (solve env (defer msg orig wl)))
end else begin
(giveup env msg orig)
end)
and solve_flex_rigid_join : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.typ, FStar_Syntax_Syntax.term) FStar_TypeChecker_Common.problem  ->  worklist  ->  worklist Prims.option = (fun env tp wl -> (let _91_1371 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _194_815 = (FStar_Util.string_of_int tp.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Trying to solve by joining refinements:%s\n" _194_815))
end else begin
()
end
in (let _91_1375 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_91_1375) with
| (u, args) -> begin
(let _91_1381 = (0, 1, 2, 3, 4)
in (match (_91_1381) with
| (ok, head_match, partial_match, fallback, failed_match) -> begin
(let max = (fun i j -> if (i < j) then begin
j
end else begin
i
end)
in (let base_types_match = (fun t1 t2 -> (let _91_1390 = (FStar_Syntax_Util.head_and_args t1)
in (match (_91_1390) with
| (h1, args1) -> begin
(let _91_1394 = (FStar_Syntax_Util.head_and_args t2)
in (match (_91_1394) with
| (h2, _91_1393) -> begin
(match ((h1.FStar_Syntax_Syntax.n, h2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_fvar (tc1), FStar_Syntax_Syntax.Tm_fvar (tc2)) -> begin
if (FStar_Syntax_Syntax.fv_eq tc1 tc2) then begin
if ((FStar_List.length args1) = 0) then begin
Some ([])
end else begin
(let _194_827 = (let _194_826 = (let _194_825 = (new_problem env t1 FStar_TypeChecker_Common.EQ t2 None t1.FStar_Syntax_Syntax.pos "joining refinements")
in (FStar_All.pipe_left (fun _194_824 -> FStar_TypeChecker_Common.TProb (_194_824)) _194_825))
in (_194_826)::[])
in Some (_194_827))
end
end else begin
None
end
end
| (FStar_Syntax_Syntax.Tm_name (a), FStar_Syntax_Syntax.Tm_name (b)) -> begin
if (FStar_Syntax_Syntax.bv_eq a b) then begin
Some ([])
end else begin
None
end
end
| _91_1406 -> begin
None
end)
end))
end)))
in (let conjoin = (fun t1 t2 -> (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.Tm_refine (x, phi1), FStar_Syntax_Syntax.Tm_refine (y, phi2)) -> begin
(let m = (base_types_match x.FStar_Syntax_Syntax.sort y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
(let x = (FStar_Syntax_Syntax.freshen_bv x)
in (let subst = (let _194_834 = (let _194_833 = (let _194_832 = (FStar_Syntax_Syntax.bv_to_name x)
in (0, _194_832))
in FStar_Syntax_Syntax.DB (_194_833))
in (_194_834)::[])
in (let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let _194_837 = (let _194_836 = (let _194_835 = (FStar_Syntax_Util.mk_conj phi1 phi2)
in (FStar_Syntax_Util.refine x _194_835))
in (_194_836, m))
in Some (_194_837))))))
end))
end
| (_91_1428, FStar_Syntax_Syntax.Tm_refine (y, _91_1431)) -> begin
(let m = (base_types_match t1 y.FStar_Syntax_Syntax.sort)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t2, m))
end))
end
| (FStar_Syntax_Syntax.Tm_refine (x, _91_1441), _91_1445) -> begin
(let m = (base_types_match x.FStar_Syntax_Syntax.sort t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end
| _91_1452 -> begin
(let m = (base_types_match t1 t2)
in (match (m) with
| None -> begin
None
end
| Some (m) -> begin
Some ((t1, m))
end))
end))
in (let tt = u
in (match (tt.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_uvar (uv, _91_1460) -> begin
(let _91_1485 = (FStar_All.pipe_right wl.attempting (FStar_List.partition (fun _91_23 -> (match (_91_23) with
| FStar_TypeChecker_Common.TProb (tp) -> begin
(match (tp.FStar_TypeChecker_Common.rank) with
| Some (rank) when (is_flex_rigid rank) -> begin
(let _91_1471 = (FStar_Syntax_Util.head_and_args tp.FStar_TypeChecker_Common.lhs)
in (match (_91_1471) with
| (u', _91_1470) -> begin
(match ((let _194_839 = (whnf env u')
in _194_839.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_uvar (uv', _91_1474) -> begin
(FStar_Unionfind.equivalent uv uv')
end
| _91_1478 -> begin
false
end)
end))
end
| _91_1480 -> begin
false
end)
end
| _91_1482 -> begin
false
end))))
in (match (_91_1485) with
| (upper_bounds, rest) -> begin
(let rec make_upper_bound = (fun _91_1489 tps -> (match (_91_1489) with
| (bound, sub_probs) -> begin
(match (tps) with
| [] -> begin
Some ((bound, sub_probs))
end
| FStar_TypeChecker_Common.TProb (hd)::tl -> begin
(match ((let _194_844 = (whnf env hd.FStar_TypeChecker_Common.rhs)
in (conjoin bound _194_844))) with
| Some (bound, sub) -> begin
(make_upper_bound (bound, (FStar_List.append sub sub_probs)) tl)
end
| None -> begin
None
end)
end
| _91_1502 -> begin
None
end)
end))
in (match ((let _194_846 = (let _194_845 = (whnf env tp.FStar_TypeChecker_Common.rhs)
in (_194_845, []))
in (make_upper_bound _194_846 upper_bounds))) with
| None -> begin
(let _91_1504 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(FStar_Util.print_string "No upper bounds\n")
end else begin
()
end
in None)
end
| Some (rhs_bound, sub_probs) -> begin
(let eq_prob = (new_problem env tp.FStar_TypeChecker_Common.lhs FStar_TypeChecker_Common.EQ rhs_bound None tp.FStar_TypeChecker_Common.loc "joining refinements")
in (let _91_1514 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let wl' = (let _91_1511 = wl
in {attempting = (FStar_TypeChecker_Common.TProb (eq_prob))::sub_probs; wl_deferred = _91_1511.wl_deferred; ctr = _91_1511.ctr; defer_ok = _91_1511.defer_ok; smt_ok = _91_1511.smt_ok; tcenv = _91_1511.tcenv})
in (let _194_847 = (wl_to_string wl')
in (FStar_Util.print1 "After joining refinements: %s\n" _194_847)))
end else begin
()
end
in (match ((solve_t env eq_prob (let _91_1516 = wl
in {attempting = sub_probs; wl_deferred = _91_1516.wl_deferred; ctr = _91_1516.ctr; defer_ok = _91_1516.defer_ok; smt_ok = _91_1516.smt_ok; tcenv = _91_1516.tcenv}))) with
| Success (_91_1519) -> begin
(let wl = (let _91_1521 = wl
in {attempting = rest; wl_deferred = _91_1521.wl_deferred; ctr = _91_1521.ctr; defer_ok = _91_1521.defer_ok; smt_ok = _91_1521.smt_ok; tcenv = _91_1521.tcenv})
in (let wl = (solve_prob' false (FStar_TypeChecker_Common.TProb (tp)) None [] wl)
in (let _91_1527 = (FStar_List.fold_left (fun wl p -> (solve_prob' true p None [] wl)) wl upper_bounds)
in Some (wl))))
end
| _91_1530 -> begin
None
end)))
end))
end))
end
| _91_1532 -> begin
(FStar_All.failwith "Impossible: Not a flex-rigid")
end)))))
end))
end))))
and solve_binders : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.binders  ->  FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Common.prob  ->  worklist  ->  (FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.subst_elt Prims.list  ->  FStar_TypeChecker_Common.prob)  ->  solution = (fun env bs1 bs2 orig wl rhs -> (let rec aux = (fun scope env subst xs ys -> (match ((xs, ys)) with
| ([], []) -> begin
(let rhs_prob = (rhs (FStar_List.rev scope) env subst)
in (let _91_1549 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_875 = (prob_to_string env rhs_prob)
in (FStar_Util.print1 "rhs_prob = %s\n" _194_875))
end else begin
()
end
in (let formula = (FStar_All.pipe_right (p_guard rhs_prob) Prims.fst)
in FStar_Util.Inl (((rhs_prob)::[], formula)))))
end
| ((hd1, imp)::xs, (hd2, imp')::ys) when (imp = imp') -> begin
(let hd1 = (let _91_1563 = hd1
in (let _194_876 = (FStar_Syntax_Subst.subst subst hd1.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _91_1563.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_1563.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _194_876}))
in (let hd2 = (let _91_1566 = hd2
in (let _194_877 = (FStar_Syntax_Subst.subst subst hd2.FStar_Syntax_Syntax.sort)
in {FStar_Syntax_Syntax.ppname = _91_1566.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_1566.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = _194_877}))
in (let prob = (let _194_880 = (let _194_879 = (FStar_All.pipe_left invert_rel (p_rel orig))
in (mk_problem scope orig hd1.FStar_Syntax_Syntax.sort _194_879 hd2.FStar_Syntax_Syntax.sort None "Formal parameter"))
in (FStar_All.pipe_left (fun _194_878 -> FStar_TypeChecker_Common.TProb (_194_878)) _194_880))
in (let hd1 = (FStar_Syntax_Syntax.freshen_bv hd1)
in (let subst = (let _194_884 = (let _194_882 = (let _194_881 = (FStar_Syntax_Syntax.bv_to_name hd1)
in (0, _194_881))
in FStar_Syntax_Syntax.DB (_194_882))
in (let _194_883 = (FStar_Syntax_Subst.shift_subst 1 subst)
in (_194_884)::_194_883))
in (let env = (FStar_TypeChecker_Env.push_bv env hd1)
in (match ((aux (((hd1, imp))::scope) env subst xs ys)) with
| FStar_Util.Inl (sub_probs, phi) -> begin
(let phi = (let _194_886 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (let _194_885 = (FStar_Syntax_Util.close_forall (((hd1, imp))::[]) phi)
in (FStar_Syntax_Util.mk_conj _194_886 _194_885)))
in (let _91_1578 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_888 = (FStar_Syntax_Print.term_to_string phi)
in (let _194_887 = (FStar_Syntax_Print.bv_to_string hd1)
in (FStar_Util.print2 "Formula is %s\n\thd1=%s\n" _194_888 _194_887)))
end else begin
()
end
in FStar_Util.Inl (((prob)::sub_probs, phi))))
end
| fail -> begin
fail
end)))))))
end
| _91_1582 -> begin
FStar_Util.Inr ("arity mismatch")
end))
in (let scope = (p_scope orig)
in (match ((aux scope env [] bs1 bs2)) with
| FStar_Util.Inr (msg) -> begin
(giveup env msg orig)
end
| FStar_Util.Inl (sub_probs, phi) -> begin
(let wl = (solve_prob orig (Some (phi)) [] wl)
in (solve env (attempt sub_probs wl)))
end))))
and solve_t : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let _194_892 = (compress_tprob wl problem)
in (solve_t' env _194_892 wl)))
and solve_t' : FStar_TypeChecker_Env.env  ->  tprob  ->  worklist  ->  solution = (fun env problem wl -> (let giveup_or_defer = (fun orig msg -> (giveup_or_defer env orig wl msg))
in (let imitate = (fun orig env wl p -> (let _91_1615 = p
in (match (_91_1615) with
| ((u, k), ps, xs, (h, _91_1612, qs)) -> begin
(let xs = (sn_binders env xs)
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let _91_1621 = (imitation_sub_probs orig env xs ps qs)
in (match (_91_1621) with
| (sub_probs, gs_xs, formula) -> begin
(let im = (let _194_910 = (h gs_xs)
in (u_abs xs _194_910))
in (let _91_1623 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_915 = (FStar_Syntax_Print.term_to_string im)
in (let _194_914 = (FStar_Syntax_Print.tag_of_term im)
in (let _194_913 = (let _194_911 = (FStar_List.map (prob_to_string env) sub_probs)
in (FStar_All.pipe_right _194_911 (FStar_String.concat ", ")))
in (let _194_912 = (FStar_TypeChecker_Normalize.term_to_string env formula)
in (FStar_Util.print4 "Imitating %s (%s)\nsub_probs = %s\nformula=%s\n" _194_915 _194_914 _194_913 _194_912)))))
end else begin
()
end
in (let wl = (solve_prob orig (Some (formula)) ((TERM (((u, k), im)))::[]) wl)
in (solve env (attempt sub_probs wl)))))
end))))
end)))
in (let project = (fun orig env wl i p -> (let _91_1639 = p
in (match (_91_1639) with
| (u, ps, xs, (h, matches, qs)) -> begin
(let r = (FStar_TypeChecker_Env.get_range env)
in (let _91_1644 = (FStar_List.nth ps i)
in (match (_91_1644) with
| (pi, _91_1643) -> begin
(let _91_1648 = (FStar_List.nth xs i)
in (match (_91_1648) with
| (xi, _91_1647) -> begin
(let rec gs = (fun k -> (let _91_1653 = (FStar_Syntax_Util.arrow_formals k)
in (match (_91_1653) with
| (bs, k) -> begin
(let rec aux = (fun subst bs -> (match (bs) with
| [] -> begin
([], [])
end
| (a, _91_1661)::tl -> begin
(let k_a = (FStar_Syntax_Subst.subst subst a.FStar_Syntax_Syntax.sort)
in (let _91_1667 = (new_uvar r xs k_a)
in (match (_91_1667) with
| (gi_xs, gi) -> begin
(let gi_xs = (FStar_TypeChecker_Normalize.eta_expand env gi_xs)
in (let gi_ps = (FStar_Syntax_Syntax.mk_Tm_app gi ps (Some (k_a.FStar_Syntax_Syntax.n)) r)
in (let subst = if (FStar_Syntax_Syntax.is_null_bv a) then begin
subst
end else begin
(FStar_Syntax_Syntax.NT ((a, gi_xs)))::subst
end
in (let _91_1673 = (aux subst tl)
in (match (_91_1673) with
| (gi_xs', gi_ps') -> begin
(let _194_937 = (let _194_934 = (FStar_Syntax_Syntax.as_arg gi_xs)
in (_194_934)::gi_xs')
in (let _194_936 = (let _194_935 = (FStar_Syntax_Syntax.as_arg gi_ps)
in (_194_935)::gi_ps')
in (_194_937, _194_936)))
end)))))
end)))
end))
in (aux [] bs))
end)))
in if (let _194_938 = (matches pi)
in (FStar_All.pipe_left Prims.op_Negation _194_938)) then begin
None
end else begin
(let _91_1677 = (gs xi.FStar_Syntax_Syntax.sort)
in (match (_91_1677) with
| (g_xs, _91_1676) -> begin
(let xi = (FStar_Syntax_Syntax.bv_to_name xi)
in (let proj = (let _194_939 = (FStar_Syntax_Syntax.mk_Tm_app xi g_xs None r)
in (u_abs xs _194_939))
in (let sub = (let _194_945 = (let _194_944 = (FStar_Syntax_Syntax.mk_Tm_app proj ps None r)
in (let _194_943 = (let _194_942 = (FStar_List.map (fun _91_1685 -> (match (_91_1685) with
| (_91_1681, _91_1683, y) -> begin
y
end)) qs)
in (FStar_All.pipe_left h _194_942))
in (mk_problem (p_scope orig) orig _194_944 (p_rel orig) _194_943 None "projection")))
in (FStar_All.pipe_left (fun _194_940 -> FStar_TypeChecker_Common.TProb (_194_940)) _194_945))
in (let _91_1687 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_947 = (FStar_Syntax_Print.term_to_string proj)
in (let _194_946 = (prob_to_string env sub)
in (FStar_Util.print2 "Projecting %s\n\tsubprob=%s\n" _194_947 _194_946)))
end else begin
()
end
in (let wl = (let _194_949 = (let _194_948 = (FStar_All.pipe_left Prims.fst (p_guard sub))
in Some (_194_948))
in (solve_prob orig _194_949 ((TERM ((u, proj)))::[]) wl))
in (let _194_951 = (solve env (attempt ((sub)::[]) wl))
in (FStar_All.pipe_left (fun _194_950 -> Some (_194_950)) _194_951)))))))
end))
end)
end))
end)))
end)))
in (let solve_t_flex_rigid = (fun orig lhs t2 wl -> (let _91_1701 = lhs
in (match (_91_1701) with
| ((t1, uv, k, args_lhs), maybe_pat_vars) -> begin
(let subterms = (fun ps -> (let xs = (let _194_978 = (FStar_Syntax_Util.arrow_formals k)
in (FStar_All.pipe_right _194_978 Prims.fst))
in (let _194_983 = (decompose env t2)
in ((uv, k), ps, xs, _194_983))))
in (let rec imitate_or_project = (fun n st i -> if (i >= n) then begin
(giveup env "flex-rigid case failed all backtracking attempts" orig)
end else begin
(let tx = (FStar_Unionfind.new_transaction ())
in if (i = (- (1))) then begin
(match ((imitate orig env wl st)) with
| Failed (_91_1711) -> begin
(let _91_1713 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| sol -> begin
sol
end)
end else begin
(match ((project orig env wl i st)) with
| (None) | (Some (Failed (_))) -> begin
(let _91_1721 = (FStar_Unionfind.rollback tx)
in (imitate_or_project n st (i + 1)))
end
| Some (sol) -> begin
sol
end)
end)
end)
in (let check_head = (fun fvs1 t2 -> (let _91_1731 = (FStar_Syntax_Util.head_and_args t2)
in (match (_91_1731) with
| (hd, _91_1730) -> begin
(match (hd.FStar_Syntax_Syntax.n) with
| (FStar_Syntax_Syntax.Tm_arrow (_)) | (FStar_Syntax_Syntax.Tm_constant (_)) | (FStar_Syntax_Syntax.Tm_abs (_)) -> begin
true
end
| _91_1742 -> begin
(let fvs_hd = (FStar_Syntax_Free.names hd)
in if (FStar_Util.set_is_subset_of fvs_hd fvs1) then begin
true
end else begin
(let _91_1744 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_994 = (names_to_string fvs_hd)
in (FStar_Util.print1 "Free variables are %s" _194_994))
end else begin
()
end
in false)
end)
end)
end)))
in (let imitate_ok = (fun t2 -> (let fvs_hd = (let _194_998 = (let _194_997 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _194_997 Prims.fst))
in (FStar_All.pipe_right _194_998 FStar_Syntax_Free.names))
in if (FStar_Util.set_is_empty fvs_hd) then begin
(- (1))
end else begin
0
end))
in (match (maybe_pat_vars) with
| Some (vars) -> begin
(let t1 = (sn env t1)
in (let t2 = (sn env t2)
in (let fvs1 = (FStar_Syntax_Free.names t1)
in (let fvs2 = (FStar_Syntax_Free.names t2)
in (let _91_1757 = (occurs_check env wl (uv, k) t2)
in (match (_91_1757) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(let _194_1000 = (let _194_999 = (FStar_Option.get msg)
in (Prims.strcat "occurs-check failed: " _194_999))
in (giveup_or_defer orig _194_1000))
end else begin
if (FStar_Util.set_is_subset_of fvs2 fvs1) then begin
if ((FStar_Syntax_Util.is_function_typ t2) && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(let _194_1001 = (subterms args_lhs)
in (imitate orig env wl _194_1001))
end else begin
(let _91_1758 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1004 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_1003 = (names_to_string fvs1)
in (let _194_1002 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s succeeded fvar check: %s\n" _194_1004 _194_1003 _194_1002))))
end else begin
()
end
in (let sol = (match (vars) with
| [] -> begin
t2
end
| _91_1762 -> begin
(let _194_1005 = (sn_binders env vars)
in (u_abs _194_1005 t2))
end)
in (let wl = (solve_prob orig None ((TERM (((uv, k), sol)))::[]) wl)
in (solve env wl))))
end
end else begin
if wl.defer_ok then begin
(solve env (defer "flex pattern/rigid: occurs or freevar check" orig wl))
end else begin
if (check_head fvs1 t2) then begin
(let _91_1765 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1008 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_1007 = (names_to_string fvs1)
in (let _194_1006 = (names_to_string fvs2)
in (FStar_Util.print3 "Pattern %s with fvars=%s failed fvar check: %s ... imitating\n" _194_1008 _194_1007 _194_1006))))
end else begin
()
end
in (let _194_1009 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _194_1009 (- (1)))))
end else begin
(giveup env "free-variable check failed on a non-redex" orig)
end
end
end
end
end))))))
end
| None -> begin
if wl.defer_ok then begin
(solve env (defer "not a pattern" orig wl))
end else begin
if (let _194_1010 = (FStar_Syntax_Free.names t1)
in (check_head _194_1010 t2)) then begin
(let im_ok = (imitate_ok t2)
in (let _91_1769 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1011 = (FStar_Syntax_Print.term_to_string t1)
in (FStar_Util.print2 "Not a pattern (%s) ... %s\n" _194_1011 (if (im_ok < 0) then begin
"imitating"
end else begin
"projecting"
end)))
end else begin
()
end
in (let _194_1012 = (subterms args_lhs)
in (imitate_or_project (FStar_List.length args_lhs) _194_1012 im_ok))))
end else begin
(giveup env "head-symbol is free" orig)
end
end
end)))))
end)))
in (let flex_flex = (fun orig lhs rhs -> if (wl.defer_ok && ((p_rel orig) <> FStar_TypeChecker_Common.EQ)) then begin
(solve env (defer "flex-flex deferred" orig wl))
end else begin
(let force_quasi_pattern = (fun xs_opt _91_1781 -> (match (_91_1781) with
| (t, u, k, args) -> begin
(let _91_1785 = (FStar_Syntax_Util.arrow_formals k)
in (match (_91_1785) with
| (all_formals, _91_1784) -> begin
(let _91_1786 = ()
in (let rec aux = (fun pat_args pattern_vars pattern_var_set formals args -> (match ((formals, args)) with
| ([], []) -> begin
(let pat_args = (FStar_All.pipe_right (FStar_List.rev pat_args) (FStar_List.map (fun _91_1799 -> (match (_91_1799) with
| (x, imp) -> begin
(let _194_1034 = (FStar_Syntax_Syntax.bv_to_name x)
in (_194_1034, imp))
end))))
in (let pattern_vars = (FStar_List.rev pattern_vars)
in (let kk = (let _91_1805 = (FStar_Syntax_Util.type_u ())
in (match (_91_1805) with
| (t, _91_1804) -> begin
(let _194_1035 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars t)
in (Prims.fst _194_1035))
end))
in (let _91_1809 = (new_uvar t.FStar_Syntax_Syntax.pos pattern_vars kk)
in (match (_91_1809) with
| (t', tm_u1) -> begin
(let _91_1816 = (destruct_flex_t t')
in (match (_91_1816) with
| (_91_1811, u1, k1, _91_1815) -> begin
(let sol = (let _194_1037 = (let _194_1036 = (u_abs all_formals t')
in ((u, k), _194_1036))
in TERM (_194_1037))
in (let t_app = (FStar_Syntax_Syntax.mk_Tm_app tm_u1 pat_args None t.FStar_Syntax_Syntax.pos)
in (sol, (t_app, u1, k1, pat_args))))
end))
end)))))
end
| (formal::formals, hd::tl) -> begin
(match ((pat_var_opt env pat_args hd)) with
| None -> begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end
| Some (y) -> begin
(let maybe_pat = (match (xs_opt) with
| None -> begin
true
end
| Some (xs) -> begin
(FStar_All.pipe_right xs (FStar_Util.for_some (fun _91_1835 -> (match (_91_1835) with
| (x, _91_1834) -> begin
(FStar_Syntax_Syntax.bv_eq x (Prims.fst y))
end))))
end)
in if (not (maybe_pat)) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let fvs = (FStar_Syntax_Free.names (Prims.fst y).FStar_Syntax_Syntax.sort)
in if (not ((FStar_Util.set_is_subset_of fvs pattern_var_set))) then begin
(aux pat_args pattern_vars pattern_var_set formals tl)
end else begin
(let _194_1039 = (FStar_Util.set_add (Prims.fst formal) pattern_var_set)
in (aux ((y)::pat_args) ((formal)::pattern_vars) _194_1039 formals tl))
end)
end)
end)
end
| _91_1839 -> begin
(FStar_All.failwith "Impossible")
end))
in (let _194_1040 = (FStar_Syntax_Syntax.new_bv_set ())
in (aux [] [] _194_1040 all_formals args))))
end))
end))
in (let solve_both_pats = (fun wl _91_1845 _91_1849 r -> (match ((_91_1845, _91_1849)) with
| ((u1, k1, xs), (u2, k2, ys)) -> begin
if ((FStar_Unionfind.equivalent u1 u2) && (binders_eq xs ys)) then begin
(let _194_1049 = (solve_prob orig None [] wl)
in (solve env _194_1049))
end else begin
(let xs = (sn_binders env xs)
in (let ys = (sn_binders env ys)
in (let zs = (intersect_vars xs ys)
in (let _91_1854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1052 = (FStar_Syntax_Print.binders_to_string ", " xs)
in (let _194_1051 = (FStar_Syntax_Print.binders_to_string ", " ys)
in (let _194_1050 = (FStar_Syntax_Print.binders_to_string ", " zs)
in (FStar_Util.print3 "Flex-flex patterns: intersected %s and %s; got %s\n" _194_1052 _194_1051 _194_1050))))
end else begin
()
end
in (let _91_1867 = (let _91_1859 = (FStar_Syntax_Util.type_u ())
in (match (_91_1859) with
| (t, _91_1858) -> begin
(let _91_1863 = (new_uvar r zs t)
in (match (_91_1863) with
| (k, _91_1862) -> begin
(new_uvar r zs k)
end))
end))
in (match (_91_1867) with
| (u_zs, _91_1866) -> begin
(let sub1 = (u_abs xs u_zs)
in (let _91_1871 = (occurs_check env wl (u1, k1) sub1)
in (match (_91_1871) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occcurs check")
end else begin
(let sol1 = TERM (((u1, k1), sub1))
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let wl = (solve_prob orig None ((sol1)::[]) wl)
in (solve env wl))
end else begin
(let sub2 = (u_abs ys u_zs)
in (let _91_1877 = (occurs_check env wl (u2, k2) sub2)
in (match (_91_1877) with
| (occurs_ok, msg) -> begin
if (not (occurs_ok)) then begin
(giveup_or_defer orig "flex-flex: failed occurs check")
end else begin
(let sol2 = TERM (((u2, k2), sub2))
in (let wl = (solve_prob orig None ((sol1)::(sol2)::[]) wl)
in (solve env wl)))
end
end)))
end)
end
end)))
end))))))
end
end))
in (let solve_one_pat = (fun _91_1885 _91_1890 -> (match ((_91_1885, _91_1890)) with
| ((t1, u1, k1, xs), (t2, u2, k2, args2)) -> begin
(let _91_1891 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1058 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_1057 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "Trying flex-flex one pattern (%s) with %s\n" _194_1058 _194_1057)))
end else begin
()
end
in if (FStar_Unionfind.equivalent u1 u2) then begin
(let sub_probs = (FStar_List.map2 (fun _91_1896 _91_1900 -> (match ((_91_1896, _91_1900)) with
| ((a, _91_1895), (t2, _91_1899)) -> begin
(let _194_1063 = (let _194_1061 = (FStar_Syntax_Syntax.bv_to_name a)
in (mk_problem (p_scope orig) orig _194_1061 FStar_TypeChecker_Common.EQ t2 None "flex-flex index"))
in (FStar_All.pipe_right _194_1063 (fun _194_1062 -> FStar_TypeChecker_Common.TProb (_194_1062))))
end)) xs args2)
in (let guard = (let _194_1065 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _194_1065))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))
end else begin
(let t2 = (sn env t2)
in (let rhs_vars = (FStar_Syntax_Free.names t2)
in (let _91_1910 = (occurs_check env wl (u1, k1) t2)
in (match (_91_1910) with
| (occurs_ok, _91_1909) -> begin
(let lhs_vars = (FStar_Syntax_Free.names_of_binders xs)
in if (occurs_ok && (FStar_Util.set_is_subset_of rhs_vars lhs_vars)) then begin
(let sol = (let _194_1067 = (let _194_1066 = (u_abs xs t2)
in ((u1, k1), _194_1066))
in TERM (_194_1067))
in (let wl = (solve_prob orig None ((sol)::[]) wl)
in (solve env wl)))
end else begin
if (occurs_ok && (FStar_All.pipe_left Prims.op_Negation wl.defer_ok)) then begin
(let _91_1921 = (force_quasi_pattern (Some (xs)) (t2, u2, k2, args2))
in (match (_91_1921) with
| (sol, (_91_1916, u2, k2, ys)) -> begin
(let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (let _91_1923 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _194_1068 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (2): %s\n" _194_1068))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _91_1928 -> begin
(giveup env "impossible" orig)
end)))
end))
end else begin
(giveup_or_defer orig "flex-flex constraint")
end
end)
end))))
end)
end))
in (let _91_1933 = lhs
in (match (_91_1933) with
| (t1, u1, k1, args1) -> begin
(let _91_1938 = rhs
in (match (_91_1938) with
| (t2, u2, k2, args2) -> begin
(let maybe_pat_vars1 = (pat_vars env [] args1)
in (let maybe_pat_vars2 = (pat_vars env [] args2)
in (let r = t2.FStar_Syntax_Syntax.pos
in (match ((maybe_pat_vars1, maybe_pat_vars2)) with
| (Some (xs), Some (ys)) -> begin
(solve_both_pats wl (u1, k1, xs) (u2, k2, ys) t2.FStar_Syntax_Syntax.pos)
end
| (Some (xs), None) -> begin
(solve_one_pat (t1, u1, k1, xs) rhs)
end
| (None, Some (ys)) -> begin
(solve_one_pat (t2, u2, k2, ys) lhs)
end
| _91_1956 -> begin
if wl.defer_ok then begin
(giveup_or_defer orig "flex-flex: neither side is a pattern")
end else begin
(let _91_1960 = (force_quasi_pattern None (t1, u1, k1, args1))
in (match (_91_1960) with
| (sol, _91_1959) -> begin
(let wl = (extend_solution (p_pid orig) ((sol)::[]) wl)
in (let _91_1962 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("QuasiPattern"))) then begin
(let _194_1069 = (uvi_to_string env sol)
in (FStar_Util.print1 "flex-flex quasi pattern (1): %s\n" _194_1069))
end else begin
()
end
in (match (orig) with
| FStar_TypeChecker_Common.TProb (p) -> begin
(solve_t env p wl)
end
| _91_1967 -> begin
(giveup env "impossible" orig)
end)))
end))
end
end))))
end))
end)))))
end)
in (let orig = FStar_TypeChecker_Common.TProb (problem)
in if (FStar_Util.physical_equality problem.FStar_TypeChecker_Common.lhs problem.FStar_TypeChecker_Common.rhs) then begin
(let _194_1070 = (solve_prob orig None [] wl)
in (solve env _194_1070))
end else begin
(let t1 = problem.FStar_TypeChecker_Common.lhs
in (let t2 = problem.FStar_TypeChecker_Common.rhs
in if (FStar_Util.physical_equality t1 t2) then begin
(let _194_1071 = (solve_prob orig None [] wl)
in (solve env _194_1071))
end else begin
(let _91_1971 = if (FStar_TypeChecker_Env.debug env (FStar_Options.Other ("RelCheck"))) then begin
(let _194_1072 = (FStar_Util.string_of_int problem.FStar_TypeChecker_Common.pid)
in (FStar_Util.print1 "Attempting %s\n" _194_1072))
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let match_num_binders = (fun _91_1976 _91_1979 -> (match ((_91_1976, _91_1979)) with
| ((bs1, mk_cod1), (bs2, mk_cod2)) -> begin
(let curry = (fun n bs mk_cod -> (let _91_1986 = (FStar_Util.first_N n bs)
in (match (_91_1986) with
| (bs, rest) -> begin
(let _194_1102 = (mk_cod rest)
in (bs, _194_1102))
end)))
in (let l1 = (FStar_List.length bs1)
in (let l2 = (FStar_List.length bs2)
in if (l1 = l2) then begin
(let _194_1106 = (let _194_1103 = (mk_cod1 [])
in (bs1, _194_1103))
in (let _194_1105 = (let _194_1104 = (mk_cod2 [])
in (bs2, _194_1104))
in (_194_1106, _194_1105)))
end else begin
if (l1 > l2) then begin
(let _194_1109 = (curry l2 bs1 mk_cod1)
in (let _194_1108 = (let _194_1107 = (mk_cod2 [])
in (bs2, _194_1107))
in (_194_1109, _194_1108)))
end else begin
(let _194_1112 = (let _194_1110 = (mk_cod1 [])
in (bs1, _194_1110))
in (let _194_1111 = (curry l1 bs2 mk_cod2)
in (_194_1112, _194_1111)))
end
end)))
end))
in (match ((t1.FStar_Syntax_Syntax.n, t2.FStar_Syntax_Syntax.n)) with
| ((FStar_Syntax_Syntax.Tm_bvar (_), _)) | ((_, FStar_Syntax_Syntax.Tm_bvar (_))) -> begin
(FStar_All.failwith "Only locally nameless! We should never see a de Bruijn variable")
end
| (FStar_Syntax_Syntax.Tm_type (u1), FStar_Syntax_Syntax.Tm_type (u2)) -> begin
(solve_one_universe_eq env orig u1 u2 wl)
end
| (FStar_Syntax_Syntax.Tm_arrow (bs1, c1), FStar_Syntax_Syntax.Tm_arrow (bs2, c2)) -> begin
(let mk_c = (fun c _91_24 -> (match (_91_24) with
| [] -> begin
c
end
| bs -> begin
(let _194_1117 = (FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_arrow ((bs, c))) None c.FStar_Syntax_Syntax.pos)
in (FStar_Syntax_Syntax.mk_Total _194_1117))
end))
in (let _91_2029 = (match_num_binders (bs1, (mk_c c1)) (bs2, (mk_c c2)))
in (match (_91_2029) with
| ((bs1, c1), (bs2, c2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let c1 = (FStar_Syntax_Subst.subst_comp subst c1)
in (let c2 = (FStar_Syntax_Subst.subst_comp subst c2)
in (let rel = if (FStar_ST.read FStar_Options.use_eq_at_higher_order) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in (let _194_1124 = (mk_problem scope orig c1 rel c2 None "function co-domain")
in (FStar_All.pipe_left (fun _194_1123 -> FStar_TypeChecker_Common.CProb (_194_1123)) _194_1124)))))))
end)))
end
| (FStar_Syntax_Syntax.Tm_abs (bs1, tbody1, _91_2039), FStar_Syntax_Syntax.Tm_abs (bs2, tbody2, _91_2045)) -> begin
(let mk_t = (fun t _91_25 -> (match (_91_25) with
| [] -> begin
t
end
| bs -> begin
(FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_abs ((bs, t, None))) None t.FStar_Syntax_Syntax.pos)
end))
in (let _91_2060 = (match_num_binders (bs1, (mk_t tbody1)) (bs2, (mk_t tbody2)))
in (match (_91_2060) with
| ((bs1, tbody1), (bs2, tbody2)) -> begin
(solve_binders env bs1 bs2 orig wl (fun scope env subst -> (let _194_1137 = (let _194_1136 = (FStar_Syntax_Subst.subst subst tbody1)
in (let _194_1135 = (FStar_Syntax_Subst.subst subst tbody2)
in (mk_problem scope orig _194_1136 problem.FStar_TypeChecker_Common.relation _194_1135 None "lambda co-domain")))
in (FStar_All.pipe_left (fun _194_1134 -> FStar_TypeChecker_Common.TProb (_194_1134)) _194_1137))))
end)))
end
| (FStar_Syntax_Syntax.Tm_refine (_91_2065), FStar_Syntax_Syntax.Tm_refine (_91_2068)) -> begin
(let _91_2073 = (as_refinement env wl t1)
in (match (_91_2073) with
| (x1, phi1) -> begin
(let _91_2076 = (as_refinement env wl t2)
in (match (_91_2076) with
| (x2, phi2) -> begin
(let base_prob = (let _194_1139 = (mk_problem (p_scope orig) orig x1.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.relation x2.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "refinement base type")
in (FStar_All.pipe_left (fun _194_1138 -> FStar_TypeChecker_Common.TProb (_194_1138)) _194_1139))
in (let x1 = (FStar_Syntax_Syntax.freshen_bv x1)
in (let subst = (let _194_1142 = (let _194_1141 = (let _194_1140 = (FStar_Syntax_Syntax.bv_to_name x1)
in (0, _194_1140))
in FStar_Syntax_Syntax.DB (_194_1141))
in (_194_1142)::[])
in (let phi1 = (FStar_Syntax_Subst.subst subst phi1)
in (let phi2 = (FStar_Syntax_Subst.subst subst phi2)
in (let env = (FStar_TypeChecker_Env.push_bv env x1)
in (let mk_imp = (fun imp phi1 phi2 -> (let _194_1159 = (imp phi1 phi2)
in (FStar_All.pipe_right _194_1159 (guard_on_element problem x1))))
in (let fallback = (fun _91_2088 -> (match (()) with
| () -> begin
(let impl = if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(mk_imp FStar_Syntax_Util.mk_iff phi1 phi2)
end else begin
(mk_imp FStar_Syntax_Util.mk_imp phi1 phi2)
end
in (let guard = (let _194_1162 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _194_1162 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
in if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(let ref_prob = (let _194_1164 = (mk_problem (p_scope orig) orig phi1 FStar_TypeChecker_Common.EQ phi2 None "refinement formula")
in (FStar_All.pipe_left (fun _194_1163 -> FStar_TypeChecker_Common.TProb (_194_1163)) _194_1164))
in (match ((solve env (let _91_2093 = wl
in {attempting = (ref_prob)::[]; wl_deferred = []; ctr = _91_2093.ctr; defer_ok = false; smt_ok = _91_2093.smt_ok; tcenv = _91_2093.tcenv}))) with
| Failed (_91_2096) -> begin
(fallback ())
end
| Success (_91_2099) -> begin
(let guard = (let _194_1167 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (let _194_1166 = (let _194_1165 = (FStar_All.pipe_right (p_guard ref_prob) Prims.fst)
in (FStar_All.pipe_right _194_1165 (guard_on_element problem x1)))
in (FStar_Syntax_Util.mk_conj _194_1167 _194_1166)))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (let wl = (let _91_2103 = wl
in {attempting = _91_2103.attempting; wl_deferred = _91_2103.wl_deferred; ctr = (wl.ctr + 1); defer_ok = _91_2103.defer_ok; smt_ok = _91_2103.smt_ok; tcenv = _91_2103.tcenv})
in (solve env (attempt ((base_prob)::[]) wl)))))
end))
end else begin
(fallback ())
end))))))))
end))
end))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_uvar (_))) | ((FStar_Syntax_Syntax.Tm_uvar (_), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
(let _194_1169 = (destruct_flex_t t1)
in (let _194_1168 = (destruct_flex_t t2)
in (flex_flex orig _194_1169 _194_1168)))
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(let _194_1170 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid orig _194_1170 t2 wl))
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) when (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) -> begin
(solve_t env (invert problem) wl)
end
| ((FStar_Syntax_Syntax.Tm_uvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _), _)) -> begin
if wl.defer_ok then begin
(solve env (defer "flex-rigid subtyping deferred" orig wl))
end else begin
(let new_rel = if (FStar_ST.read FStar_Options.no_slack) then begin
FStar_TypeChecker_Common.EQ
end else begin
problem.FStar_TypeChecker_Common.relation
end
in if (let _194_1171 = (is_top_level_prob orig)
in (FStar_All.pipe_left Prims.op_Negation _194_1171)) then begin
(let _194_1174 = (FStar_All.pipe_left (fun _194_1172 -> FStar_TypeChecker_Common.TProb (_194_1172)) (let _91_2248 = problem
in {FStar_TypeChecker_Common.pid = _91_2248.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_2248.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _91_2248.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_2248.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2248.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2248.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2248.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2248.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2248.FStar_TypeChecker_Common.rank}))
in (let _194_1173 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _194_1174 _194_1173 t2 wl)))
end else begin
(let _91_2252 = (base_and_refinement env wl t2)
in (match (_91_2252) with
| (t_base, ref_opt) -> begin
(match (ref_opt) with
| None -> begin
(let _194_1177 = (FStar_All.pipe_left (fun _194_1175 -> FStar_TypeChecker_Common.TProb (_194_1175)) (let _91_2254 = problem
in {FStar_TypeChecker_Common.pid = _91_2254.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_2254.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = new_rel; FStar_TypeChecker_Common.rhs = _91_2254.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_2254.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2254.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2254.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2254.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2254.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2254.FStar_TypeChecker_Common.rank}))
in (let _194_1176 = (destruct_flex_pattern env t1)
in (solve_t_flex_rigid _194_1177 _194_1176 t_base wl)))
end
| Some (y, phi) -> begin
(let y' = (let _91_2260 = y
in {FStar_Syntax_Syntax.ppname = _91_2260.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = _91_2260.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = t1})
in (let impl = (guard_on_element problem y' phi)
in (let base_prob = (let _194_1179 = (mk_problem problem.FStar_TypeChecker_Common.scope orig t1 new_rel y.FStar_Syntax_Syntax.sort problem.FStar_TypeChecker_Common.element "flex-rigid: base type")
in (FStar_All.pipe_left (fun _194_1178 -> FStar_TypeChecker_Common.TProb (_194_1178)) _194_1179))
in (let guard = (let _194_1180 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _194_1180 impl))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt ((base_prob)::[]) wl)))))))
end)
end))
end)
end
end
| ((_, FStar_Syntax_Syntax.Tm_uvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app ({FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar (_); FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _; FStar_Syntax_Syntax.vars = _}, _))) -> begin
if wl.defer_ok then begin
(solve env (defer "rigid-flex subtyping deferred" orig wl))
end else begin
(let _91_2293 = (base_and_refinement env wl t1)
in (match (_91_2293) with
| (t_base, _91_2292) -> begin
(solve_t env (let _91_2294 = problem
in {FStar_TypeChecker_Common.pid = _91_2294.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t_base; FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ; FStar_TypeChecker_Common.rhs = _91_2294.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_2294.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2294.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2294.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2294.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2294.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2294.FStar_TypeChecker_Common.rank}) wl)
end))
end
end
| (FStar_Syntax_Syntax.Tm_refine (_91_2297), _91_2300) -> begin
(let t2 = (let _194_1181 = (base_and_refinement env wl t2)
in (FStar_All.pipe_left force_refinement _194_1181))
in (solve_t env (let _91_2303 = problem
in {FStar_TypeChecker_Common.pid = _91_2303.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_2303.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _91_2303.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _91_2303.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2303.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2303.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2303.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2303.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2303.FStar_TypeChecker_Common.rank}) wl))
end
| (_91_2306, FStar_Syntax_Syntax.Tm_refine (_91_2308)) -> begin
(let t1 = (let _194_1182 = (base_and_refinement env wl t1)
in (FStar_All.pipe_left force_refinement _194_1182))
in (solve_t env (let _91_2312 = problem
in {FStar_TypeChecker_Common.pid = _91_2312.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _91_2312.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _91_2312.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_2312.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2312.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2312.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2312.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2312.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2312.FStar_TypeChecker_Common.rank}) wl))
end
| ((FStar_Syntax_Syntax.Tm_abs (_), _)) | ((_, FStar_Syntax_Syntax.Tm_abs (_))) -> begin
(let maybe_eta = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_abs (_91_2329) -> begin
t
end
| _91_2332 -> begin
(FStar_TypeChecker_Normalize.eta_expand wl.tcenv t)
end))
in (let _194_1187 = (let _91_2333 = problem
in (let _194_1186 = (maybe_eta t1)
in (let _194_1185 = (maybe_eta t2)
in {FStar_TypeChecker_Common.pid = _91_2333.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _194_1186; FStar_TypeChecker_Common.relation = _91_2333.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _194_1185; FStar_TypeChecker_Common.element = _91_2333.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2333.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2333.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2333.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2333.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2333.FStar_TypeChecker_Common.rank})))
in (solve_t env _194_1187 wl)))
end
| ((FStar_Syntax_Syntax.Tm_uinst (_), _)) | ((FStar_Syntax_Syntax.Tm_name (_), _)) | ((FStar_Syntax_Syntax.Tm_constant (_), _)) | ((FStar_Syntax_Syntax.Tm_fvar (_), _)) | ((FStar_Syntax_Syntax.Tm_app (_), _)) | ((_, FStar_Syntax_Syntax.Tm_uinst (_))) | ((_, FStar_Syntax_Syntax.Tm_name (_))) | ((_, FStar_Syntax_Syntax.Tm_constant (_))) | ((_, FStar_Syntax_Syntax.Tm_fvar (_))) | ((_, FStar_Syntax_Syntax.Tm_app (_))) -> begin
(let _91_2397 = (head_matches_delta env wl t1 t2)
in (match (_91_2397) with
| (m, o) -> begin
(match ((m, o)) with
| (MisMatch, _91_2400) -> begin
(let head1 = (let _194_1188 = (FStar_Syntax_Util.head_and_args t1)
in (FStar_All.pipe_right _194_1188 Prims.fst))
in (let head2 = (let _194_1189 = (FStar_Syntax_Util.head_and_args t2)
in (FStar_All.pipe_right _194_1189 Prims.fst))
in (let may_equate = (fun head -> (match (head.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_name (_91_2407) -> begin
true
end
| FStar_Syntax_Syntax.Tm_fvar (tc, _91_2411) -> begin
(FStar_TypeChecker_Env.is_projector env tc.FStar_Syntax_Syntax.v)
end
| _91_2415 -> begin
false
end))
in if (((may_equate head1) || (may_equate head2)) && wl.smt_ok) then begin
(let _194_1195 = (let _194_1194 = (let _194_1193 = (FStar_Syntax_Util.mk_eq FStar_Syntax_Syntax.tun FStar_Syntax_Syntax.tun t1 t2)
in (FStar_All.pipe_left (fun _194_1192 -> Some (_194_1192)) _194_1193))
in (solve_prob orig _194_1194 [] wl))
in (solve env _194_1195))
end else begin
(giveup env "head mismatch" orig)
end)))
end
| (_91_2417, Some (t1, t2)) -> begin
(solve_t env (let _91_2423 = problem
in {FStar_TypeChecker_Common.pid = _91_2423.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _91_2423.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _91_2423.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2423.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2423.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2423.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2423.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2423.FStar_TypeChecker_Common.rank}) wl)
end
| (_91_2426, None) -> begin
(let _91_2429 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1199 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_1198 = (FStar_Syntax_Print.tag_of_term t1)
in (let _194_1197 = (FStar_Syntax_Print.term_to_string t2)
in (let _194_1196 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.print4 "Head matches: %s (%s) and %s (%s)\n" _194_1199 _194_1198 _194_1197 _194_1196)))))
end else begin
()
end
in (let _91_2433 = (FStar_Syntax_Util.head_and_args t1)
in (match (_91_2433) with
| (head, args) -> begin
(let _91_2436 = (FStar_Syntax_Util.head_and_args t2)
in (match (_91_2436) with
| (head', args') -> begin
(let nargs = (FStar_List.length args)
in if (nargs <> (FStar_List.length args')) then begin
(let _194_1204 = (let _194_1203 = (FStar_Syntax_Print.term_to_string head)
in (let _194_1202 = (args_to_string args)
in (let _194_1201 = (FStar_Syntax_Print.term_to_string head')
in (let _194_1200 = (args_to_string args')
in (FStar_Util.format4 "unequal number of arguments: %s[%s] and %s[%s]" _194_1203 _194_1202 _194_1201 _194_1200)))))
in (giveup env _194_1204 orig))
end else begin
if ((nargs = 0) || (eq_args args args')) then begin
(match ((solve_maybe_uinsts env orig head head' wl)) with
| USolved (wl) -> begin
(let _194_1205 = (solve_prob orig None [] wl)
in (solve env _194_1205))
end
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end)
end else begin
(let _91_2446 = (base_and_refinement env wl t1)
in (match (_91_2446) with
| (base1, refinement1) -> begin
(let _91_2449 = (base_and_refinement env wl t2)
in (match (_91_2449) with
| (base2, refinement2) -> begin
(match ((refinement1, refinement2)) with
| (None, None) -> begin
(match ((solve_maybe_uinsts env orig base1 base2 wl)) with
| UFailed (msg) -> begin
(giveup env msg orig)
end
| UDeferred (wl) -> begin
(solve env (defer "universe constraints" orig wl))
end
| USolved (wl) -> begin
(let subprobs = (FStar_List.map2 (fun _91_2462 _91_2466 -> (match ((_91_2462, _91_2466)) with
| ((a, _91_2461), (a', _91_2465)) -> begin
(let _194_1209 = (mk_problem (p_scope orig) orig a FStar_TypeChecker_Common.EQ a' None "index")
in (FStar_All.pipe_left (fun _194_1208 -> FStar_TypeChecker_Common.TProb (_194_1208)) _194_1209))
end)) args args')
in (let formula = (let _194_1211 = (FStar_List.map (fun p -> (Prims.fst (p_guard p))) subprobs)
in (FStar_Syntax_Util.mk_conj_l _194_1211))
in (let wl = (solve_prob orig (Some (formula)) [] wl)
in (solve env (attempt subprobs wl)))))
end)
end
| _91_2472 -> begin
(let lhs = (force_refinement (base1, refinement1))
in (let rhs = (force_refinement (base2, refinement2))
in (solve_t env (let _91_2475 = problem
in {FStar_TypeChecker_Common.pid = _91_2475.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = lhs; FStar_TypeChecker_Common.relation = _91_2475.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = rhs; FStar_TypeChecker_Common.element = _91_2475.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2475.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2475.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2475.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2475.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2475.FStar_TypeChecker_Common.rank}) wl)))
end)
end))
end))
end
end)
end))
end)))
end)
end))
end
| (FStar_Syntax_Syntax.Tm_ascribed (t1, _91_2479, _91_2481), _91_2485) -> begin
(solve_t' env (let _91_2487 = problem
in {FStar_TypeChecker_Common.pid = _91_2487.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = t1; FStar_TypeChecker_Common.relation = _91_2487.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _91_2487.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_2487.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2487.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2487.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2487.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2487.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2487.FStar_TypeChecker_Common.rank}) wl)
end
| (_91_2490, FStar_Syntax_Syntax.Tm_ascribed (t2, _91_2493, _91_2495)) -> begin
(solve_t' env (let _91_2499 = problem
in {FStar_TypeChecker_Common.pid = _91_2499.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_2499.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _91_2499.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = t2; FStar_TypeChecker_Common.element = _91_2499.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2499.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2499.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2499.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2499.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2499.FStar_TypeChecker_Common.rank}) wl)
end
| ((FStar_Syntax_Syntax.Tm_let (_), _)) | ((FStar_Syntax_Syntax.Tm_meta (_), _)) | ((FStar_Syntax_Syntax.Tm_delayed (_), _)) | ((_, FStar_Syntax_Syntax.Tm_meta (_))) | ((_, FStar_Syntax_Syntax.Tm_delayed (_))) | ((_, FStar_Syntax_Syntax.Tm_let (_))) -> begin
(let _194_1214 = (let _194_1213 = (FStar_Syntax_Print.tag_of_term t1)
in (let _194_1212 = (FStar_Syntax_Print.tag_of_term t2)
in (FStar_Util.format2 "Impossible: %s and %s" _194_1213 _194_1212)))
in (FStar_All.failwith _194_1214))
end
| _91_2538 -> begin
(giveup env "head mismatch" orig)
end))))
end))
end)))))))
and solve_c : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.comp, Prims.unit) FStar_TypeChecker_Common.problem  ->  worklist  ->  solution = (fun env problem wl -> (let c1 = problem.FStar_TypeChecker_Common.lhs
in (let c2 = problem.FStar_TypeChecker_Common.rhs
in (let orig = FStar_TypeChecker_Common.CProb (problem)
in (let sub_prob = (fun t1 rel t2 reason -> (mk_problem (p_scope orig) orig t1 rel t2 None reason))
in (let solve_eq = (fun c1_comp c2_comp -> (let _91_2555 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("EQ"))) then begin
(FStar_Util.print_string "solve_c is using an equality constraint\n")
end else begin
()
end
in (let sub_probs = (FStar_List.map2 (fun _91_2560 _91_2564 -> (match ((_91_2560, _91_2564)) with
| ((a1, _91_2559), (a2, _91_2563)) -> begin
(let _194_1229 = (sub_prob a1 FStar_TypeChecker_Common.EQ a2 "effect arg")
in (FStar_All.pipe_left (fun _194_1228 -> FStar_TypeChecker_Common.TProb (_194_1228)) _194_1229))
end)) c1_comp.FStar_Syntax_Syntax.effect_args c2_comp.FStar_Syntax_Syntax.effect_args)
in (let guard = (let _194_1231 = (FStar_List.map (fun p -> (FStar_All.pipe_right (p_guard p) Prims.fst)) sub_probs)
in (FStar_Syntax_Util.mk_conj_l _194_1231))
in (let wl = (solve_prob orig (Some (guard)) [] wl)
in (solve env (attempt sub_probs wl)))))))
in if (FStar_Util.physical_equality c1 c2) then begin
(let _194_1232 = (solve_prob orig None [] wl)
in (solve env _194_1232))
end else begin
(let _91_2569 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1234 = (FStar_Syntax_Print.comp_to_string c1)
in (let _194_1233 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print3 "solve_c %s %s %s\n" _194_1234 (rel_to_string problem.FStar_TypeChecker_Common.relation) _194_1233)))
end else begin
()
end
in (let r = (FStar_TypeChecker_Env.get_range env)
in (let _91_2574 = (c1, c2)
in (match (_91_2574) with
| (c1_0, c2_0) -> begin
(match ((c1.FStar_Syntax_Syntax.n, c2.FStar_Syntax_Syntax.n)) with
| (FStar_Syntax_Syntax.GTotal (_91_2576), FStar_Syntax_Syntax.Total (_91_2579)) -> begin
(giveup env "incompatible monad ordering: GTot </: Tot" orig)
end
| ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.Total (t2))) | ((FStar_Syntax_Syntax.GTotal (t1), FStar_Syntax_Syntax.GTotal (t2))) | ((FStar_Syntax_Syntax.Total (t1), FStar_Syntax_Syntax.GTotal (t2))) -> begin
(let _194_1235 = (problem_using_guard orig t1 problem.FStar_TypeChecker_Common.relation t2 None "result type")
in (solve_t env _194_1235 wl))
end
| ((FStar_Syntax_Syntax.GTotal (_), FStar_Syntax_Syntax.Comp (_))) | ((FStar_Syntax_Syntax.Total (_), FStar_Syntax_Syntax.Comp (_))) -> begin
(let _194_1237 = (let _91_2607 = problem
in (let _194_1236 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c1))
in {FStar_TypeChecker_Common.pid = _91_2607.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _194_1236; FStar_TypeChecker_Common.relation = _91_2607.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _91_2607.FStar_TypeChecker_Common.rhs; FStar_TypeChecker_Common.element = _91_2607.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2607.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2607.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2607.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2607.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2607.FStar_TypeChecker_Common.rank}))
in (solve_c env _194_1237 wl))
end
| ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.GTotal (_))) | ((FStar_Syntax_Syntax.Comp (_), FStar_Syntax_Syntax.Total (_))) -> begin
(let _194_1239 = (let _91_2623 = problem
in (let _194_1238 = (FStar_All.pipe_left FStar_Syntax_Syntax.mk_Comp (FStar_Syntax_Util.comp_to_comp_typ c2))
in {FStar_TypeChecker_Common.pid = _91_2623.FStar_TypeChecker_Common.pid; FStar_TypeChecker_Common.lhs = _91_2623.FStar_TypeChecker_Common.lhs; FStar_TypeChecker_Common.relation = _91_2623.FStar_TypeChecker_Common.relation; FStar_TypeChecker_Common.rhs = _194_1238; FStar_TypeChecker_Common.element = _91_2623.FStar_TypeChecker_Common.element; FStar_TypeChecker_Common.logical_guard = _91_2623.FStar_TypeChecker_Common.logical_guard; FStar_TypeChecker_Common.scope = _91_2623.FStar_TypeChecker_Common.scope; FStar_TypeChecker_Common.reason = _91_2623.FStar_TypeChecker_Common.reason; FStar_TypeChecker_Common.loc = _91_2623.FStar_TypeChecker_Common.loc; FStar_TypeChecker_Common.rank = _91_2623.FStar_TypeChecker_Common.rank}))
in (solve_c env _194_1239 wl))
end
| (FStar_Syntax_Syntax.Comp (_91_2626), FStar_Syntax_Syntax.Comp (_91_2629)) -> begin
if (((FStar_Syntax_Util.is_ml_comp c1) && (FStar_Syntax_Util.is_ml_comp c2)) || ((FStar_Syntax_Util.is_total_comp c1) && ((FStar_Syntax_Util.is_total_comp c2) || (FStar_Syntax_Util.is_ml_comp c2)))) then begin
(let _194_1240 = (problem_using_guard orig (FStar_Syntax_Util.comp_result c1) problem.FStar_TypeChecker_Common.relation (FStar_Syntax_Util.comp_result c2) None "result type")
in (solve_t env _194_1240 wl))
end else begin
(let c1_comp = (FStar_Syntax_Util.comp_to_comp_typ c1)
in (let c2_comp = (FStar_Syntax_Util.comp_to_comp_typ c2)
in if ((problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) && (FStar_Ident.lid_equals c1_comp.FStar_Syntax_Syntax.effect_name c2_comp.FStar_Syntax_Syntax.effect_name)) then begin
(solve_eq c1_comp c2_comp)
end else begin
(let c1 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c1)
in (let c2 = (FStar_TypeChecker_Normalize.unfold_effect_abbrev env c2)
in (let _91_2636 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print2 "solve_c for %s and %s\n" c1.FStar_Syntax_Syntax.effect_name.FStar_Ident.str c2.FStar_Syntax_Syntax.effect_name.FStar_Ident.str)
end else begin
()
end
in (match ((FStar_TypeChecker_Env.monad_leq env c1.FStar_Syntax_Syntax.effect_name c2.FStar_Syntax_Syntax.effect_name)) with
| None -> begin
(let _194_1243 = (let _194_1242 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _194_1241 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "incompatible monad ordering: %s </: %s" _194_1242 _194_1241)))
in (giveup env _194_1243 orig))
end
| Some (edge) -> begin
if (problem.FStar_TypeChecker_Common.relation = FStar_TypeChecker_Common.EQ) then begin
(let _91_2654 = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (wp1, _91_2647)::(wlp1, _91_2643)::[] -> begin
(wp1, wlp1)
end
| _91_2651 -> begin
(let _194_1245 = (let _194_1244 = (FStar_Range.string_of_range (FStar_Ident.range_of_lid c1.FStar_Syntax_Syntax.effect_name))
in (FStar_Util.format1 "Unexpected number of indices on a normalized effect (%s)" _194_1244))
in (FStar_All.failwith _194_1245))
end)
in (match (_91_2654) with
| (wp, wlp) -> begin
(let c1 = (let _194_1251 = (let _194_1250 = (let _194_1246 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wp)
in (FStar_Syntax_Syntax.as_arg _194_1246))
in (let _194_1249 = (let _194_1248 = (let _194_1247 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wlp)
in (FStar_Syntax_Syntax.as_arg _194_1247))
in (_194_1248)::[])
in (_194_1250)::_194_1249))
in {FStar_Syntax_Syntax.effect_name = c2.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = c1.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = _194_1251; FStar_Syntax_Syntax.flags = c1.FStar_Syntax_Syntax.flags})
in (solve_eq c1 c2))
end))
end else begin
(let is_null_wp_2 = (FStar_All.pipe_right c2.FStar_Syntax_Syntax.flags (FStar_Util.for_some (fun _91_26 -> (match (_91_26) with
| (FStar_Syntax_Syntax.TOTAL) | (FStar_Syntax_Syntax.MLEFFECT) | (FStar_Syntax_Syntax.SOMETRIVIAL) -> begin
true
end
| _91_2661 -> begin
false
end))))
in (let _91_2682 = (match ((c1.FStar_Syntax_Syntax.effect_args, c2.FStar_Syntax_Syntax.effect_args)) with
| ((wp1, _91_2667)::_91_2664, (wp2, _91_2674)::_91_2671) -> begin
(wp1, wp2)
end
| _91_2679 -> begin
(let _194_1255 = (let _194_1254 = (FStar_Syntax_Print.lid_to_string c1.FStar_Syntax_Syntax.effect_name)
in (let _194_1253 = (FStar_Syntax_Print.lid_to_string c2.FStar_Syntax_Syntax.effect_name)
in (FStar_Util.format2 "Got effects %s and %s, expected normalized effects" _194_1254 _194_1253)))
in (FStar_All.failwith _194_1255))
end)
in (match (_91_2682) with
| (wpc1, wpc2) -> begin
if (FStar_Util.physical_equality wpc1 wpc2) then begin
(let _194_1256 = (problem_using_guard orig c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ None "result type")
in (solve_t env _194_1256 wl))
end else begin
(let c2_decl = (FStar_TypeChecker_Env.get_effect_decl env c2.FStar_Syntax_Syntax.effect_name)
in (let g = if is_null_wp_2 then begin
(let _91_2684 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(FStar_Util.print_string "Using trivial wp ... \n")
end else begin
()
end
in (let _194_1264 = (let _194_1263 = (let _194_1262 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.trivial)
in (let _194_1261 = (let _194_1260 = (FStar_Syntax_Syntax.as_arg c1.FStar_Syntax_Syntax.result_typ)
in (let _194_1259 = (let _194_1258 = (let _194_1257 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _194_1257))
in (_194_1258)::[])
in (_194_1260)::_194_1259))
in (_194_1262, _194_1261)))
in FStar_Syntax_Syntax.Tm_app (_194_1263))
in (FStar_Syntax_Syntax.mk _194_1264 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end else begin
(let wp2_imp_wp1 = (let _194_1277 = (let _194_1276 = (let _194_1275 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.wp_binop)
in (let _194_1274 = (let _194_1273 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _194_1272 = (let _194_1271 = (FStar_Syntax_Syntax.as_arg wpc2)
in (let _194_1270 = (let _194_1269 = (let _194_1265 = (FStar_Syntax_Syntax.fvar None FStar_Syntax_Const.imp_lid r)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _194_1265))
in (let _194_1268 = (let _194_1267 = (let _194_1266 = (edge.FStar_TypeChecker_Env.mlift c1.FStar_Syntax_Syntax.result_typ wpc1)
in (FStar_All.pipe_left FStar_Syntax_Syntax.as_arg _194_1266))
in (_194_1267)::[])
in (_194_1269)::_194_1268))
in (_194_1271)::_194_1270))
in (_194_1273)::_194_1272))
in (_194_1275, _194_1274)))
in FStar_Syntax_Syntax.Tm_app (_194_1276))
in (FStar_Syntax_Syntax.mk _194_1277 None r))
in (let _194_1284 = (let _194_1283 = (let _194_1282 = (FStar_TypeChecker_Env.inst_effect_fun env c2_decl c2_decl.FStar_Syntax_Syntax.wp_as_type)
in (let _194_1281 = (let _194_1280 = (FStar_Syntax_Syntax.as_arg c2.FStar_Syntax_Syntax.result_typ)
in (let _194_1279 = (let _194_1278 = (FStar_Syntax_Syntax.as_arg wp2_imp_wp1)
in (_194_1278)::[])
in (_194_1280)::_194_1279))
in (_194_1282, _194_1281)))
in FStar_Syntax_Syntax.Tm_app (_194_1283))
in (FStar_Syntax_Syntax.mk _194_1284 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) r)))
end
in (let base_prob = (let _194_1286 = (sub_prob c1.FStar_Syntax_Syntax.result_typ problem.FStar_TypeChecker_Common.relation c2.FStar_Syntax_Syntax.result_typ "result type")
in (FStar_All.pipe_left (fun _194_1285 -> FStar_TypeChecker_Common.TProb (_194_1285)) _194_1286))
in (let wl = (let _194_1290 = (let _194_1289 = (let _194_1288 = (FStar_All.pipe_right (p_guard base_prob) Prims.fst)
in (FStar_Syntax_Util.mk_conj _194_1288 g))
in (FStar_All.pipe_left (fun _194_1287 -> Some (_194_1287)) _194_1289))
in (solve_prob orig _194_1290 [] wl))
in (solve env (attempt ((base_prob)::[]) wl))))))
end
end)))
end
end))))
end))
end
end)
end))))
end))))))

let print_pending_implicits : FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun g -> (let _194_1294 = (FStar_All.pipe_right g.FStar_TypeChecker_Env.implicits (FStar_List.map (fun _91_2700 -> (match (_91_2700) with
| (_91_2692, u, _91_2695, _91_2697, _91_2699) -> begin
(FStar_Syntax_Print.uvar_to_string u)
end))))
in (FStar_All.pipe_right _194_1294 (FStar_String.concat ", "))))

let guard_to_string : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.string = (fun env g -> (match ((g.FStar_TypeChecker_Env.guard_f, g.FStar_TypeChecker_Env.deferred)) with
| (FStar_TypeChecker_Common.Trivial, []) -> begin
"{}"
end
| _91_2707 -> begin
(let form = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
"trivial"
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) || (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Implicits")))) then begin
(FStar_TypeChecker_Normalize.term_to_string env f)
end else begin
"non-trivial"
end
end)
in (let carry = (let _194_1300 = (FStar_List.map (fun _91_2715 -> (match (_91_2715) with
| (_91_2713, x) -> begin
(prob_to_string env x)
end)) g.FStar_TypeChecker_Env.deferred)
in (FStar_All.pipe_right _194_1300 (FStar_String.concat ",\n")))
in (let imps = (print_pending_implicits g)
in (FStar_Util.format3 "\n\t{guard_f=%s;\n\t deferred={\n%s};\n\t implicits={%s}}\n" form carry imps))))
end))

let guard_of_guard_formula : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Env.guard_t = (fun g -> {FStar_TypeChecker_Env.guard_f = g; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})

let guard_form : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun g -> g.FStar_TypeChecker_Env.guard_f)

let is_trivial : FStar_TypeChecker_Env.guard_t  ->  Prims.bool = (fun g -> (match (g) with
| {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _91_2724; FStar_TypeChecker_Env.implicits = _91_2722} -> begin
true
end
| _91_2729 -> begin
false
end))

let trivial_guard : FStar_TypeChecker_Env.guard_t = {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []}

let abstract_guard : FStar_Syntax_Syntax.bv  ->  FStar_TypeChecker_Env.guard_t Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun x g -> (match (g) with
| (None) | (Some ({FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _; FStar_TypeChecker_Env.univ_ineqs = _; FStar_TypeChecker_Env.implicits = _})) -> begin
g
end
| Some (g) -> begin
(let f = (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
f
end
| _91_2747 -> begin
(FStar_All.failwith "impossible")
end)
in (let _194_1316 = (let _91_2749 = g
in (let _194_1315 = (let _194_1314 = (let _194_1313 = (let _194_1312 = (FStar_Syntax_Syntax.mk_binder x)
in (_194_1312)::[])
in (u_abs _194_1313 f))
in (FStar_All.pipe_left (fun _194_1311 -> FStar_TypeChecker_Common.NonTrivial (_194_1311)) _194_1314))
in {FStar_TypeChecker_Env.guard_f = _194_1315; FStar_TypeChecker_Env.deferred = _91_2749.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _91_2749.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _91_2749.FStar_TypeChecker_Env.implicits}))
in Some (_194_1316)))
end))

let apply_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_Syntax_Syntax.term  ->  FStar_TypeChecker_Env.guard_t = (fun g e -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _91_2756 = g
in (let _194_1327 = (let _194_1326 = (let _194_1325 = (let _194_1324 = (let _194_1323 = (let _194_1322 = (FStar_Syntax_Syntax.as_arg e)
in (_194_1322)::[])
in (f, _194_1323))
in FStar_Syntax_Syntax.Tm_app (_194_1324))
in (FStar_Syntax_Syntax.mk _194_1325 (Some (FStar_Syntax_Util.ktype0.FStar_Syntax_Syntax.n)) f.FStar_Syntax_Syntax.pos))
in (FStar_All.pipe_left (fun _194_1321 -> FStar_TypeChecker_Common.NonTrivial (_194_1321)) _194_1326))
in {FStar_TypeChecker_Env.guard_f = _194_1327; FStar_TypeChecker_Env.deferred = _91_2756.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _91_2756.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _91_2756.FStar_TypeChecker_Env.implicits}))
end))

let trivial : FStar_TypeChecker_Common.guard_formula  ->  Prims.unit = (fun t -> (match (t) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (_91_2761) -> begin
(FStar_All.failwith "impossible")
end))

let conj_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| ((FStar_TypeChecker_Common.Trivial, g)) | ((g, FStar_TypeChecker_Common.Trivial)) -> begin
g
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let _194_1334 = (FStar_Syntax_Util.mk_conj f1 f2)
in FStar_TypeChecker_Common.NonTrivial (_194_1334))
end))

let check_trivial : (FStar_Syntax_Syntax.term', FStar_Syntax_Syntax.term') FStar_Syntax_Syntax.syntax  ->  FStar_TypeChecker_Common.guard_formula = (fun t -> (match (t.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_fvar (tc, _91_2778) when (FStar_Ident.lid_equals tc.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _91_2782 -> begin
FStar_TypeChecker_Common.NonTrivial (t)
end))

let imp_guard_f : FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula = (fun g1 g2 -> (match ((g1, g2)) with
| (FStar_TypeChecker_Common.Trivial, g) -> begin
g
end
| (g, FStar_TypeChecker_Common.Trivial) -> begin
FStar_TypeChecker_Common.Trivial
end
| (FStar_TypeChecker_Common.NonTrivial (f1), FStar_TypeChecker_Common.NonTrivial (f2)) -> begin
(let imp = (FStar_Syntax_Util.mk_imp f1 f2)
in (check_trivial imp))
end))

let binop_guard : (FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula  ->  FStar_TypeChecker_Common.guard_formula)  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun f g1 g2 -> (let _194_1357 = (f g1.FStar_TypeChecker_Env.guard_f g2.FStar_TypeChecker_Env.guard_f)
in {FStar_TypeChecker_Env.guard_f = _194_1357; FStar_TypeChecker_Env.deferred = (FStar_List.append g1.FStar_TypeChecker_Env.deferred g2.FStar_TypeChecker_Env.deferred); FStar_TypeChecker_Env.univ_ineqs = (FStar_List.append g1.FStar_TypeChecker_Env.univ_ineqs g2.FStar_TypeChecker_Env.univ_ineqs); FStar_TypeChecker_Env.implicits = (FStar_List.append g1.FStar_TypeChecker_Env.implicits g2.FStar_TypeChecker_Env.implicits)}))

let conj_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard conj_guard_f g1 g2))

let imp_guard : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g1 g2 -> (binop_guard imp_guard_f g1 g2))

let close_guard : FStar_Syntax_Syntax.binders  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun binders g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _91_2809 = g
in (let _194_1372 = (let _194_1371 = (FStar_Syntax_Util.close_forall binders f)
in (FStar_All.pipe_right _194_1371 (fun _194_1370 -> FStar_TypeChecker_Common.NonTrivial (_194_1370))))
in {FStar_TypeChecker_Env.guard_f = _194_1372; FStar_TypeChecker_Env.deferred = _91_2809.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _91_2809.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _91_2809.FStar_TypeChecker_Env.implicits}))
end))

let new_t_problem = (fun env lhs rel rhs elt loc -> (let reason = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _194_1380 = (FStar_TypeChecker_Normalize.term_to_string env lhs)
in (let _194_1379 = (FStar_TypeChecker_Normalize.term_to_string env rhs)
in (FStar_Util.format3 "Top-level:\n%s\n\t%s\n%s" _194_1380 (rel_to_string rel) _194_1379)))
end else begin
"TOP"
end
in (let p = (new_problem env lhs rel rhs elt loc reason)
in p)))

let new_t_prob : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Common.rel  ->  FStar_Syntax_Syntax.term  ->  (FStar_TypeChecker_Common.prob * FStar_Syntax_Syntax.bv) = (fun env t1 rel t2 -> (let x = (let _194_1391 = (let _194_1390 = (FStar_TypeChecker_Env.get_range env)
in (FStar_All.pipe_left (fun _194_1389 -> Some (_194_1389)) _194_1390))
in (FStar_Syntax_Syntax.new_bv _194_1391 t1))
in (let env = (FStar_TypeChecker_Env.push_bv env x)
in (let p = (let _194_1395 = (let _194_1393 = (FStar_Syntax_Syntax.bv_to_name x)
in (FStar_All.pipe_left (fun _194_1392 -> Some (_194_1392)) _194_1393))
in (let _194_1394 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 rel t2 _194_1395 _194_1394)))
in (FStar_TypeChecker_Common.TProb (p), x)))))

let solve_and_commit : FStar_TypeChecker_Env.env  ->  worklist  ->  ((FStar_TypeChecker_Common.prob * Prims.string)  ->  FStar_TypeChecker_Common.deferred Prims.option)  ->  FStar_TypeChecker_Common.deferred Prims.option = (fun env probs err -> (let probs = if (FStar_ST.read FStar_Options.eager_inference) then begin
(let _91_2829 = probs
in {attempting = _91_2829.attempting; wl_deferred = _91_2829.wl_deferred; ctr = _91_2829.ctr; defer_ok = false; smt_ok = _91_2829.smt_ok; tcenv = _91_2829.tcenv})
end else begin
probs
end
in (let tx = (FStar_Unionfind.new_transaction ())
in (let sol = (solve env probs)
in (match (sol) with
| Success (deferred) -> begin
(let _91_2836 = (FStar_Unionfind.commit tx)
in Some (deferred))
end
| Failed (d, s) -> begin
(let _91_2842 = (FStar_Unionfind.rollback tx)
in (let _91_2844 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("ExplainRel"))) then begin
(let _194_1407 = (explain env d s)
in (FStar_All.pipe_left FStar_Util.print_string _194_1407))
end else begin
()
end
in (err (d, s))))
end)))))

let simplify_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
g
end
| FStar_TypeChecker_Common.NonTrivial (f) -> begin
(let _91_2851 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _194_1412 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplifying guard %s\n" _194_1412))
end else begin
()
end
in (let f = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Simplify)::[]) env f)
in (let _91_2854 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Simplification"))) then begin
(let _194_1413 = (FStar_Syntax_Print.term_to_string f)
in (FStar_Util.print1 "Simplified guard to %s\n" _194_1413))
end else begin
()
end
in (let f = (match ((let _194_1414 = (FStar_Syntax_Util.unmeta f)
in _194_1414.FStar_Syntax_Syntax.n)) with
| FStar_Syntax_Syntax.Tm_fvar (fv, _91_2858) when (FStar_Ident.lid_equals fv.FStar_Syntax_Syntax.v FStar_Syntax_Const.true_lid) -> begin
FStar_TypeChecker_Common.Trivial
end
| _91_2862 -> begin
FStar_TypeChecker_Common.NonTrivial (f)
end)
in (let _91_2864 = g
in {FStar_TypeChecker_Env.guard_f = f; FStar_TypeChecker_Env.deferred = _91_2864.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _91_2864.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _91_2864.FStar_TypeChecker_Env.implicits})))))
end))

let with_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Common.prob  ->  FStar_TypeChecker_Common.deferred Prims.option  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env prob dopt -> (match (dopt) with
| None -> begin
None
end
| Some (d) -> begin
(let _194_1426 = (let _194_1425 = (let _194_1424 = (let _194_1423 = (FStar_All.pipe_right (p_guard prob) Prims.fst)
in (FStar_All.pipe_right _194_1423 (fun _194_1422 -> FStar_TypeChecker_Common.NonTrivial (_194_1422))))
in {FStar_TypeChecker_Env.guard_f = _194_1424; FStar_TypeChecker_Env.deferred = d; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = []})
in (simplify_guard env _194_1425))
in (FStar_All.pipe_left (fun _194_1421 -> Some (_194_1421)) _194_1426))
end))

let try_teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (let _91_2875 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1434 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_1433 = (FStar_Syntax_Print.term_to_string t2)
in (FStar_Util.print2 "try_teq of %s and %s\n" _194_1434 _194_1433)))
end else begin
()
end
in (let prob = (let _194_1437 = (let _194_1436 = (FStar_TypeChecker_Env.get_range env)
in (new_t_problem env t1 FStar_TypeChecker_Common.EQ t2 None _194_1436))
in (FStar_All.pipe_left (fun _194_1435 -> FStar_TypeChecker_Common.TProb (_194_1435)) _194_1437))
in (let g = (let _194_1439 = (solve_and_commit env (singleton env prob) (fun _91_2878 -> None))
in (FStar_All.pipe_left (with_guard env prob) _194_1439))
in g))))

let teq : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t = (fun env t1 t2 -> (match ((try_teq env t1 t2)) with
| None -> begin
(let _194_1449 = (let _194_1448 = (let _194_1447 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _194_1446 = (FStar_TypeChecker_Env.get_range env)
in (_194_1447, _194_1446)))
in FStar_Syntax_Syntax.Error (_194_1448))
in (Prims.raise _194_1449))
end
| Some (g) -> begin
(let _91_2887 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1452 = (FStar_Syntax_Print.term_to_string t1)
in (let _194_1451 = (FStar_Syntax_Print.term_to_string t2)
in (let _194_1450 = (guard_to_string env g)
in (FStar_Util.print3 "teq of %s and %s succeeded with guard %s\n" _194_1452 _194_1451 _194_1450))))
end else begin
()
end
in g)
end))

let try_subtype : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env t1 t2 -> (let _91_2892 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1460 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _194_1459 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (FStar_Util.print2 "try_subtype of %s and %s\n" _194_1460 _194_1459)))
end else begin
()
end
in (let _91_2896 = (new_t_prob env t1 FStar_TypeChecker_Common.SUB t2)
in (match (_91_2896) with
| (prob, x) -> begin
(let g = (let _194_1462 = (solve_and_commit env (singleton env prob) (fun _91_2897 -> None))
in (FStar_All.pipe_left (with_guard env prob) _194_1462))
in (let _91_2900 = if ((FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) && (FStar_Util.is_some g)) then begin
(let _194_1466 = (FStar_TypeChecker_Normalize.term_to_string env t1)
in (let _194_1465 = (FStar_TypeChecker_Normalize.term_to_string env t2)
in (let _194_1464 = (let _194_1463 = (FStar_Util.must g)
in (guard_to_string env _194_1463))
in (FStar_Util.print3 "try_subtype succeeded: %s <: %s\n\tguard is %s\n" _194_1466 _194_1465 _194_1464))))
end else begin
()
end
in (abstract_guard x g)))
end))))

let subtype_fail = (fun env t1 t2 -> (let _194_1473 = (let _194_1472 = (let _194_1471 = (FStar_TypeChecker_Errors.basic_type_error env None t2 t1)
in (let _194_1470 = (FStar_TypeChecker_Env.get_range env)
in (_194_1471, _194_1470)))
in FStar_Syntax_Syntax.Error (_194_1472))
in (Prims.raise _194_1473)))

let sub_comp : FStar_TypeChecker_Env.env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp  ->  FStar_TypeChecker_Env.guard_t Prims.option = (fun env c1 c2 -> (let _91_2908 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1481 = (FStar_Syntax_Print.comp_to_string c1)
in (let _194_1480 = (FStar_Syntax_Print.comp_to_string c2)
in (FStar_Util.print2 "sub_comp of %s and %s\n" _194_1481 _194_1480)))
end else begin
()
end
in (let rel = if env.FStar_TypeChecker_Env.use_eq then begin
FStar_TypeChecker_Common.EQ
end else begin
FStar_TypeChecker_Common.SUB
end
in (let prob = (let _194_1484 = (let _194_1483 = (FStar_TypeChecker_Env.get_range env)
in (new_problem env c1 rel c2 None _194_1483 "sub_comp"))
in (FStar_All.pipe_left (fun _194_1482 -> FStar_TypeChecker_Common.CProb (_194_1482)) _194_1484))
in (let _194_1486 = (solve_and_commit env (singleton env prob) (fun _91_2912 -> None))
in (FStar_All.pipe_left (with_guard env prob) _194_1486))))))

let solve_universe_inequalities' : FStar_Unionfind.tx  ->  FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun tx env ineqs -> (let fail = (fun msg u1 u2 -> (let _91_2921 = (FStar_Unionfind.rollback tx)
in (let msg = (match (msg) with
| None -> begin
""
end
| Some (s) -> begin
(Prims.strcat ": " s)
end)
in (let _194_1504 = (let _194_1503 = (let _194_1502 = (let _194_1500 = (FStar_Syntax_Print.univ_to_string u1)
in (let _194_1499 = (FStar_Syntax_Print.univ_to_string u2)
in (FStar_Util.format3 "Universe %s and %s are incompatible%s" _194_1500 _194_1499 msg)))
in (let _194_1501 = (FStar_TypeChecker_Env.get_range env)
in (_194_1502, _194_1501)))
in FStar_Syntax_Syntax.Error (_194_1503))
in (Prims.raise _194_1504)))))
in (let rec insert = (fun uv u1 groups -> (match (groups) with
| [] -> begin
((uv, (u1)::[]))::[]
end
| hd::tl -> begin
(let _91_2937 = hd
in (match (_91_2937) with
| (uv', lower_bounds) -> begin
if (FStar_Unionfind.equivalent uv uv') then begin
((uv', (u1)::lower_bounds))::tl
end else begin
(let _194_1511 = (insert uv u1 tl)
in (hd)::_194_1511)
end
end))
end))
in (let rec group_by = (fun out ineqs -> (match (ineqs) with
| [] -> begin
Some (out)
end
| (u1, u2)::rest -> begin
(let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u2) with
| FStar_Syntax_Syntax.U_unif (uv) -> begin
(let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in if (FStar_Syntax_Util.eq_univs u1 u2) then begin
(group_by out rest)
end else begin
(let _194_1516 = (insert uv u1 out)
in (group_by _194_1516 rest))
end)
end
| _91_2952 -> begin
None
end))
end))
in (let ad_hoc_fallback = (fun _91_2954 -> (match (()) with
| () -> begin
(match (ineqs) with
| [] -> begin
()
end
| _91_2957 -> begin
(let wl = (let _91_2958 = (empty_worklist env)
in {attempting = _91_2958.attempting; wl_deferred = _91_2958.wl_deferred; ctr = _91_2958.ctr; defer_ok = true; smt_ok = _91_2958.smt_ok; tcenv = _91_2958.tcenv})
in (let _91_2998 = (FStar_All.pipe_right ineqs (FStar_List.iter (fun _91_2963 -> (match (_91_2963) with
| (u1, u2) -> begin
(let u1 = (FStar_TypeChecker_Normalize.normalize_universe env u1)
in (let u2 = (FStar_TypeChecker_Normalize.normalize_universe env u2)
in (match (u1) with
| FStar_Syntax_Syntax.U_zero -> begin
()
end
| _91_2968 -> begin
(match ((solve_universe_eq (- (1)) wl u1 u2)) with
| (UDeferred (_)) | (UFailed (_)) -> begin
(let us1 = (match (u1) with
| FStar_Syntax_Syntax.U_max (us1) -> begin
us1
end
| _91_2978 -> begin
(u1)::[]
end)
in (let us2 = (match (u2) with
| FStar_Syntax_Syntax.U_max (us2) -> begin
us2
end
| _91_2983 -> begin
(u2)::[]
end)
in if (FStar_All.pipe_right us1 (FStar_Util.for_all (fun _91_27 -> (match (_91_27) with
| FStar_Syntax_Syntax.U_zero -> begin
true
end
| u -> begin
(let _91_2990 = (FStar_Syntax_Util.univ_kernel u)
in (match (_91_2990) with
| (k_u, n) -> begin
(FStar_All.pipe_right us2 (FStar_Util.for_some (fun u' -> (let _91_2994 = (FStar_Syntax_Util.univ_kernel u')
in (match (_91_2994) with
| (k_u', n') -> begin
((FStar_Syntax_Util.eq_univs k_u k_u') && (n <= n'))
end)))))
end))
end)))) then begin
()
end else begin
(fail None u1 u2)
end))
end
| USolved (_91_2996) -> begin
()
end)
end)))
end))))
in (FStar_TypeChecker_Errors.warn FStar_Range.dummyRange "Universe inequality check not fully implemented")))
end)
end))
in (match ((group_by [] ineqs)) with
| Some (groups) -> begin
(let wl = (let _91_3002 = (empty_worklist env)
in {attempting = _91_3002.attempting; wl_deferred = _91_3002.wl_deferred; ctr = _91_3002.ctr; defer_ok = false; smt_ok = _91_3002.smt_ok; tcenv = _91_3002.tcenv})
in (let rec solve_all_groups = (fun wl groups -> (match (groups) with
| [] -> begin
()
end
| (u, lower_bounds)::groups -> begin
(match ((solve_universe_eq (- (1)) wl (FStar_Syntax_Syntax.U_max (lower_bounds)) (FStar_Syntax_Syntax.U_unif (u)))) with
| USolved (wl) -> begin
(solve_all_groups wl groups)
end
| _91_3017 -> begin
(ad_hoc_fallback ())
end)
end))
in (solve_all_groups wl groups)))
end
| None -> begin
(ad_hoc_fallback ())
end))))))

let solve_universe_inequalities : FStar_TypeChecker_Env.env  ->  (FStar_Syntax_Syntax.universe * FStar_Syntax_Syntax.universe) Prims.list  ->  Prims.unit = (fun env ineqs -> (let tx = (FStar_Unionfind.new_transaction ())
in (let _91_3022 = (solve_universe_inequalities' tx env ineqs)
in (FStar_Unionfind.commit tx))))

let rec solve_deferred_constraints : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (let fail = (fun _91_3029 -> (match (_91_3029) with
| (d, s) -> begin
(let msg = (explain env d s)
in (Prims.raise (FStar_Syntax_Syntax.Error ((msg, (p_loc d))))))
end))
in (let wl = (wl_of_guard env g.FStar_TypeChecker_Env.deferred)
in (let _91_3032 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _194_1537 = (wl_to_string wl)
in (let _194_1536 = (FStar_Util.string_of_int (FStar_List.length g.FStar_TypeChecker_Env.implicits))
in (FStar_Util.print2 "Trying to solve carried problems: begin\n\t%s\nend\n and %s implicits\n" _194_1537 _194_1536)))
end else begin
()
end
in (let g = (match ((solve_and_commit env wl fail)) with
| Some ([]) -> begin
(let _91_3036 = g
in {FStar_TypeChecker_Env.guard_f = _91_3036.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = []; FStar_TypeChecker_Env.univ_ineqs = _91_3036.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _91_3036.FStar_TypeChecker_Env.implicits})
end
| _91_3039 -> begin
(FStar_All.failwith "impossible: Unexpected deferred constraints remain")
end)
in (let _91_3041 = (solve_universe_inequalities env g.FStar_TypeChecker_Env.univ_ineqs)
in (let _91_3043 = g
in {FStar_TypeChecker_Env.guard_f = _91_3043.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _91_3043.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = []; FStar_TypeChecker_Env.implicits = _91_3043.FStar_TypeChecker_Env.implicits})))))))

let discharge_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun env g -> (let g = (solve_deferred_constraints env g)
in (let _91_3057 = if (not ((FStar_Options.should_verify env.FStar_TypeChecker_Env.curmodule.FStar_Ident.str))) then begin
()
end else begin
(match (g.FStar_TypeChecker_Env.guard_f) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(let vc = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Inline)::(FStar_TypeChecker_Normalize.Beta)::(FStar_TypeChecker_Normalize.Eta)::(FStar_TypeChecker_Normalize.Simplify)::[]) env vc)
in (match ((check_trivial vc)) with
| FStar_TypeChecker_Common.Trivial -> begin
()
end
| FStar_TypeChecker_Common.NonTrivial (vc) -> begin
(let _91_3055 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("Rel"))) then begin
(let _194_1544 = (FStar_TypeChecker_Env.get_range env)
in (let _194_1543 = (let _194_1542 = (FStar_Syntax_Print.term_to_string vc)
in (FStar_Util.format1 "Checking VC=\n%s\n" _194_1542))
in (FStar_TypeChecker_Errors.diag _194_1544 _194_1543)))
end else begin
()
end
in (env.FStar_TypeChecker_Env.solver.FStar_TypeChecker_Env.solve env vc))
end))
end)
end
in (let _91_3059 = g
in {FStar_TypeChecker_Env.guard_f = FStar_TypeChecker_Common.Trivial; FStar_TypeChecker_Env.deferred = _91_3059.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _91_3059.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _91_3059.FStar_TypeChecker_Env.implicits}))))

let resolve_implicits : FStar_TypeChecker_Env.guard_t  ->  FStar_TypeChecker_Env.guard_t = (fun g -> (let unresolved = (fun u -> (match ((FStar_Unionfind.find u)) with
| FStar_Syntax_Syntax.Uvar -> begin
true
end
| _91_3066 -> begin
false
end))
in (let rec until_fixpoint = (fun _91_3070 implicits -> (match (_91_3070) with
| (out, changed) -> begin
(match (implicits) with
| [] -> begin
if (not (changed)) then begin
out
end else begin
(until_fixpoint ([], false) out)
end
end
| hd::tl -> begin
(let _91_3081 = hd
in (match (_91_3081) with
| (env, u, tm, k, r) -> begin
if (unresolved u) then begin
(until_fixpoint ((hd)::out, changed) tl)
end else begin
(let env = (FStar_TypeChecker_Env.set_expected_typ env k)
in (let tm = (FStar_TypeChecker_Normalize.normalize ((FStar_TypeChecker_Normalize.Beta)::[]) env tm)
in (let _91_3084 = if (FStar_All.pipe_left (FStar_TypeChecker_Env.debug env) (FStar_Options.Other ("RelCheck"))) then begin
(let _194_1555 = (FStar_Syntax_Print.uvar_to_string u)
in (let _194_1554 = (FStar_Syntax_Print.term_to_string tm)
in (let _194_1553 = (FStar_Syntax_Print.term_to_string k)
in (FStar_Util.print3 "Checking uvar %s resolved to %s at type %s\n" _194_1555 _194_1554 _194_1553))))
end else begin
()
end
in (let _91_3091 = (env.FStar_TypeChecker_Env.type_of (let _91_3086 = env
in {FStar_TypeChecker_Env.solver = _91_3086.FStar_TypeChecker_Env.solver; FStar_TypeChecker_Env.range = _91_3086.FStar_TypeChecker_Env.range; FStar_TypeChecker_Env.curmodule = _91_3086.FStar_TypeChecker_Env.curmodule; FStar_TypeChecker_Env.gamma = _91_3086.FStar_TypeChecker_Env.gamma; FStar_TypeChecker_Env.gamma_cache = _91_3086.FStar_TypeChecker_Env.gamma_cache; FStar_TypeChecker_Env.modules = _91_3086.FStar_TypeChecker_Env.modules; FStar_TypeChecker_Env.expected_typ = _91_3086.FStar_TypeChecker_Env.expected_typ; FStar_TypeChecker_Env.sigtab = _91_3086.FStar_TypeChecker_Env.sigtab; FStar_TypeChecker_Env.is_pattern = _91_3086.FStar_TypeChecker_Env.is_pattern; FStar_TypeChecker_Env.instantiate_imp = _91_3086.FStar_TypeChecker_Env.instantiate_imp; FStar_TypeChecker_Env.effects = _91_3086.FStar_TypeChecker_Env.effects; FStar_TypeChecker_Env.generalize = _91_3086.FStar_TypeChecker_Env.generalize; FStar_TypeChecker_Env.letrecs = _91_3086.FStar_TypeChecker_Env.letrecs; FStar_TypeChecker_Env.top_level = _91_3086.FStar_TypeChecker_Env.top_level; FStar_TypeChecker_Env.check_uvars = _91_3086.FStar_TypeChecker_Env.check_uvars; FStar_TypeChecker_Env.use_eq = _91_3086.FStar_TypeChecker_Env.use_eq; FStar_TypeChecker_Env.is_iface = _91_3086.FStar_TypeChecker_Env.is_iface; FStar_TypeChecker_Env.admit = _91_3086.FStar_TypeChecker_Env.admit; FStar_TypeChecker_Env.default_effects = _91_3086.FStar_TypeChecker_Env.default_effects; FStar_TypeChecker_Env.type_of = _91_3086.FStar_TypeChecker_Env.type_of; FStar_TypeChecker_Env.use_bv_sorts = true}) tm)
in (match (_91_3091) with
| (_91_3089, g) -> begin
(let g' = (discharge_guard env g)
in (until_fixpoint ((FStar_List.append g'.FStar_TypeChecker_Env.implicits out), true) tl))
end)))))
end
end))
end)
end))
in (let _91_3093 = g
in (let _194_1556 = (until_fixpoint ([], false) g.FStar_TypeChecker_Env.implicits)
in {FStar_TypeChecker_Env.guard_f = _91_3093.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _91_3093.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = _91_3093.FStar_TypeChecker_Env.univ_ineqs; FStar_TypeChecker_Env.implicits = _194_1556})))))

let force_trivial_guard : FStar_TypeChecker_Env.env  ->  FStar_TypeChecker_Env.guard_t  ->  Prims.unit = (fun env g -> (let g = (let _194_1561 = (solve_deferred_constraints env g)
in (FStar_All.pipe_right _194_1561 resolve_implicits))
in (match (g.FStar_TypeChecker_Env.implicits) with
| [] -> begin
(let _194_1562 = (discharge_guard env g)
in (FStar_All.pipe_left Prims.ignore _194_1562))
end
| (_91_3102, _91_3104, _91_3106, _91_3108, r)::_91_3100 -> begin
(Prims.raise (FStar_Syntax_Syntax.Error (("Failed to resolve implicit argument", r))))
end)))

let universe_inequality : FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.universe  ->  FStar_TypeChecker_Env.guard_t = (fun u1 u2 -> (let _91_3114 = trivial_guard
in {FStar_TypeChecker_Env.guard_f = _91_3114.FStar_TypeChecker_Env.guard_f; FStar_TypeChecker_Env.deferred = _91_3114.FStar_TypeChecker_Env.deferred; FStar_TypeChecker_Env.univ_ineqs = ((u1, u2))::[]; FStar_TypeChecker_Env.implicits = _91_3114.FStar_TypeChecker_Env.implicits}))



