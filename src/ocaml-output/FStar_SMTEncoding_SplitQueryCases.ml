
open Prims

let rec get_next_n_ite : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.term) = (fun n t negs f -> if (n <= 0) then begin
(let _175_14 = (f FStar_SMTEncoding_Term.mkTrue)
in ((true), (_175_14), (negs), (t)))
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, (g)::(t)::(e)::_83_7) -> begin
(let _175_19 = (let _175_16 = (let _175_15 = (FStar_SMTEncoding_Term.mkNot g)
in ((negs), (_175_15)))
in (FStar_SMTEncoding_Term.mkAnd _175_16))
in (get_next_n_ite (n - 1) e _175_19 (fun x -> (let _175_18 = (FStar_SMTEncoding_Term.mkITE ((g), (t), (x)))
in (f _175_18)))))
end
| FStar_SMTEncoding_Term.FreeV (_83_18) -> begin
(let _175_20 = (f FStar_SMTEncoding_Term.mkTrue)
in ((true), (_175_20), (negs), (t)))
end
| _83_21 -> begin
((false), (FStar_SMTEncoding_Term.mkFalse), (FStar_SMTEncoding_Term.mkFalse), (FStar_SMTEncoding_Term.mkFalse))
end)
end)


let rec is_ite_all_the_way : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (Prims.bool * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term) = (fun n t negs l -> if (n <= 0) then begin
(Prims.raise FStar_Util.Impos)
end else begin
(match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.FreeV (_83_27) -> begin
(let _175_31 = (let _175_30 = (let _175_29 = (FStar_SMTEncoding_Term.mkNot t)
in ((negs), (_175_29)))
in (FStar_SMTEncoding_Term.mkAnd _175_30))
in ((true), (l), (_175_31)))
end
| _83_30 -> begin
(

let _83_36 = (get_next_n_ite n t negs (fun x -> x))
in (match (_83_36) with
| (b, t, negs', rest) -> begin
if b then begin
(let _175_34 = (let _175_33 = (FStar_SMTEncoding_Term.mkImp ((negs), (t)))
in (_175_33)::l)
in (is_ite_all_the_way n rest negs' _175_34))
end else begin
((false), ([]), (FStar_SMTEncoding_Term.mkFalse))
end
end))
end)
end)


let rec parse_query_for_split_cases : Prims.int  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n t f -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, l, opt, l', t) -> begin
(parse_query_for_split_cases n t (fun x -> (let _175_61 = (FStar_SMTEncoding_Term.mkForall'' ((l), (opt), (l'), (x)))
in (f _175_61))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Imp, (t1)::(t2)::_83_50) -> begin
(

let r = (match (t2.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.Quant (FStar_SMTEncoding_Term.Forall, _83_59, _83_61, _83_63, _83_65) -> begin
(parse_query_for_split_cases n t2 (fun x -> (let _175_69 = (FStar_SMTEncoding_Term.mkImp ((t1), (x)))
in (f _175_69))))
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _83_71) -> begin
(

let _83_77 = (is_ite_all_the_way n t2 FStar_SMTEncoding_Term.mkTrue [])
in (match (_83_77) with
| (b, l, negs) -> begin
((b), ((((fun x -> (let _175_78 = (FStar_SMTEncoding_Term.mkImp ((t1), (x)))
in (f _175_78)))), (l), (negs))))
end))
end
| _83_80 -> begin
((false), ((((fun _83_81 -> FStar_SMTEncoding_Term.mkFalse)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end)
in r)
end
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.ITE, _83_86) -> begin
(

let _83_92 = (is_ite_all_the_way n t FStar_SMTEncoding_Term.mkTrue [])
in (match (_83_92) with
| (b, l, negs) -> begin
((b), (((f), (l), (negs))))
end))
end
| _83_94 -> begin
((false), ((((fun _83_95 -> FStar_SMTEncoding_Term.mkFalse)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end))


let strip_not : FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term = (fun t -> (match (t.FStar_SMTEncoding_Term.tm) with
| FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Not, (hd)::_83_100) -> begin
hd
end
| _83_106 -> begin
t
end))


let rec check_split_cases : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term Prims.list  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f l check -> (FStar_List.iter (fun t -> (let _175_117 = (let _175_116 = (let _175_115 = (let _175_114 = (f t)
in (FStar_SMTEncoding_Term.mkNot _175_114))
in ((_175_115), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_175_116))
in (check _175_117))) (FStar_List.rev l)))


let check_exhaustiveness : (FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term)  ->  FStar_SMTEncoding_Term.term  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun f negs check -> (let _175_138 = (let _175_137 = (let _175_136 = (let _175_135 = (let _175_134 = (FStar_SMTEncoding_Term.mkNot negs)
in (f _175_134))
in (FStar_SMTEncoding_Term.mkNot _175_135))
in ((_175_136), (None), (None)))
in FStar_SMTEncoding_Term.Assume (_175_137))
in (check _175_138)))


let can_handle_query : Prims.int  ->  FStar_SMTEncoding_Term.decl  ->  (Prims.bool * ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)) = (fun n q -> (match (q) with
| FStar_SMTEncoding_Term.Assume (q', _83_118, _83_120) -> begin
(parse_query_for_split_cases n (strip_not q') (fun x -> x))
end
| _83_125 -> begin
((false), ((((fun x -> x)), ([]), (FStar_SMTEncoding_Term.mkFalse))))
end))


let handle_query : ((FStar_SMTEncoding_Term.term  ->  FStar_SMTEncoding_Term.term) * FStar_SMTEncoding_Term.term Prims.list * FStar_SMTEncoding_Term.term)  ->  (FStar_SMTEncoding_Term.decl  ->  Prims.unit)  ->  Prims.unit = (fun _83_130 check -> (match (_83_130) with
| (f, l, negs) -> begin
(

let l = (check_split_cases f l check)
in (check_exhaustiveness f negs check))
end))




