(*--build-config
    options:--admit_fsi FStar.Set --admit_fsi FStar.OrdSet --admit_fsi FStar.OrdSetProps;
    other-files:ext.fst set.fsi heap.fst st.fst all.fst listTot.fst ordset.fsi ordsetproperties.fst
  --*)
(*
   Copyright 2008-2015 Nikhil Swamy and Microsoft Research

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

(* 
   An implementation of first-order unification, based on 
     Ana Bove's Licentiate Thesis
     Programming in Martin-L�f Type Theory Unification - A non-trivial Example
     Department of Computer Science, Chalmers University of Technology
     1999
     http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.40.3532
*)   

(* STILL INCOMPLETE *)
module Unification

open FStar.List.Tot

val union : list 'a -> list 'a -> Tot (list 'a)
let rec union l m = match l with
  | [] -> m
  | hd::tl ->
    if mem hd m
    then union tl m
    else union tl (hd::m)

val no_dups_union: l:list 'a -> m:list 'a ->
  Lemma (requires (noRepeats m))
        (ensures (noRepeats (union l m)))
let rec no_dups_union l m = match l with
  | [] -> ()
  | hd::tl ->
    if mem hd m
    then no_dups_union tl m
    else no_dups_union tl (hd::m)

type term = 
  | V : i:nat -> term
  | F : t1:term -> t2:term -> term

val nat_order : OrdSet.cmp nat
let nat_order x y = x <= y

type varset = OrdSet.ordset nat nat_order
val empty_vars : varset
let empty_vars = OrdSet.empty

type eqns  = list (term * term) 

val vars : term -> Tot varset
let rec vars = function 
  | V i -> OrdSet.singleton i
  | F t1 t2 -> OrdSet.union (vars t1) (vars t2) 

val evars : eqns -> Tot varset
let rec evars = function
  | [] -> empty_vars
  | (x, y)::tl -> OrdSet.union (OrdSet.union (vars x) (vars y)) (evars tl)
  
val n_evars : eqns -> Tot nat
let n_evars eqns = OrdSet.size (evars eqns)

val evars_permute_hd : x:term -> y:term -> tl:eqns -> Lemma 
  (ensures (evars ((x, y)::tl) = evars ((y, x)::tl)))
let evars_permute_hd x y tl = OrdSet.eq_lemma (evars ((x,y)::tl)) (evars ((y,x)::tl))

val evars_unfun : x:term -> y:term -> x':term -> y':term -> tl:eqns -> Lemma
  (ensures (evars ((F x y, F x' y')::tl) = evars ((x, x')::(y, y')::tl)))
let evars_unfun x y x' y' tl = OrdSet.eq_lemma (evars ((F x y, F x' y')::tl)) (evars ((x, x')::(y, y')::tl))

val funs : term -> Tot nat
let rec funs = function 
  | V _ -> 0
  | F t1 t2 -> 1 + funs t1 + funs t2

val efuns : eqns -> Tot nat
let rec efuns = function 
  | [] -> 0
  | (x,y)::tl -> funs x + funs y + efuns tl

val efuns_smaller: t1:term -> t2:term -> tl:eqns -> Lemma
  (ensures (efuns tl <= efuns ((t1, t2)::tl)))
let efuns_smaller t1 t2 tl = ()

val efuns_permute_hd : x:term -> y:term -> tl:eqns -> Lemma
  (ensures (efuns ((x,y)::tl) = efuns ((y,x)::tl)))
let efuns_permute_hd x y tl = ()  

val n_flex_rhs : eqns -> Tot nat
let rec n_flex_rhs = function
  | [] -> 0
  | (V _, V _)::tl
  | (_  , V _)::tl -> 1 + n_flex_rhs tl
  | _::tl -> n_flex_rhs tl
  
type subst = (nat * term)

val subst_term : subst -> term -> Tot term 
let rec subst_term s t = match t with 
  | V x -> if x = fst s then snd s else V x
  | F t1 t2 -> F (subst_term s t1) (subst_term s t2)

val lsubst_term : list subst -> term -> Tot term
let lsubst_term s t = fold_right subst_term s t

type subst_ok s = ~ (OrdSet.mem (fst s) (vars (snd s)))

val lemma_vars_decrease: s:subst -> t':term -> Lemma 
  (requires (subst_ok s))
  (ensures (OrdSet.subset (vars (subst_term s t'))
 			  (OrdSet.remove (fst s) (OrdSet.union (vars (snd s)) (vars t')))))
let rec lemma_vars_decrease s t' = match t' with 
  | V x -> ()
  | F t1 t2 -> 
    lemma_vars_decrease s t1;
    lemma_vars_decrease s t2

val subst_subst : subst -> subst -> Tot subst
let subst_subst s1 (x, t) = (x, subst_term s1 t)

val subst_lsubst: subst -> list subst -> Tot (list subst)
let subst_lsubst s1 s2 = map (subst_subst s1) s2

let occurs x t = OrdSet.mem x (vars t)
let ok s = not (occurs (fst s) (snd s))

val lsubst_eqns: list subst -> eqns -> Tot eqns
let rec lsubst_eqns l = function 
  | [] -> []
  | (x,y)::tl -> (lsubst_term l x, lsubst_term l y)::lsubst_eqns l tl

val vars_decrease_eqns: x:nat -> t:term -> e:eqns -> Lemma
  (requires (subst_ok (x, t)))
  (ensures (OrdSet.subset (evars (lsubst_eqns [x,t] e))
			  (OrdSet.remove x (evars ((V x, t)::e)))))
let rec vars_decrease_eqns x t e = match e with 
  | [] -> ()
  | hd::tl -> lemma_vars_decrease (x,t) (fst hd); 
	    lemma_vars_decrease (x,t) (snd hd); 
	    vars_decrease_eqns x t tl

<<<<<<< 331769ded7af34efc1c417f74011f0692e4e9fa0
=======
assume val subset_size: #a:Type -> #f:OrdSet.cmp a -> x:OrdSet.ordset a f -> y:OrdSet.ordset a f -> 
  Lemma (requires (OrdSet.subset x y))
	(ensures (OrdSet.size x <= OrdSet.size y))
	[SMTPat (OrdSet.subset x y)]
 
>>>>>>> checkpoint correctness proof
val unify : e:eqns -> list subst -> Tot (option (list subst))
  (decreases %[n_evars e; efuns e; n_flex_rhs e])
let rec unify e s = match e with
  | [] -> Some s

  | (V x, t)::tl -> 
    if is_V t && V.i t = x
    then unify tl s //t is a flex-rhs
    else if occurs x t
    then None
    else (vars_decrease_eqns x t tl;
          unify (lsubst_eqns [x,t] tl) ((x,t)::s))

 | (t, V x)::tl -> //flex-rhs
   evars_permute_hd t (V x) tl;
   unify ((V x, t)::tl) s

 | (F t1 t2, F t1' t2')::tl -> //efuns reduces
   evars_unfun t1 t2 t1' t2' tl;
   unify ((t1, t1')::(t2, t2')::tl) s

val solved : eqns -> Tot bool 
let rec solved = function
  | [] -> true
  | (x,y)::tl -> x=y && solved tl 

val lsubst_distributes: l:list subst -> t1:term -> t2:term -> Lemma
       (requires (True))
       (ensures (lsubst_term l (F t1 t2) = F (lsubst_term l t1) (lsubst_term l t2)))
       [SMTPat (lsubst_term l (F t1 t2))]
let rec lsubst_distributes l t1 t2 = match l with 
  | [] -> ()
  | hd::tl -> lsubst_distributes tl t1 t2

let op_At = append
let lsubst_lsubst = fold_right subst_lsubst

let extend_subst s l = s::l
let extend_lsubst l l' = l @ l'

 
val lemma_extend_lsubst_term_distributes: l:list subst -> l':list subst -> e:term -> Lemma
       (requires True)
       (ensures (lsubst_term (extend_lsubst l l') e = lsubst_term l (lsubst_term l' e)))
let rec lemma_extend_lsubst_term_distributes l l' e = match l with 
  | [] -> ()
  | hd::tl -> lemma_extend_lsubst_term_distributes tl l' e

val lemma_extend_lsubst_distributes_eqns: l:list subst -> l':list subst -> e:eqns -> Lemma
       (requires True)
       (ensures (lsubst_eqns (extend_lsubst l l') e = lsubst_eqns l (lsubst_eqns l' e)))
       [SMTPat (lsubst_eqns (extend_lsubst l l') e)]
let rec lemma_extend_lsubst_distributes_eqns l l' e = match e with 
  | [] -> ()
  | (t1, t2)::tl -> 
    lemma_extend_lsubst_term_distributes l l' t1;
    lemma_extend_lsubst_term_distributes l l' t2;
    lemma_extend_lsubst_distributes_eqns l l' tl

val lemma_subst_id: x:nat -> z:term -> y:term -> Lemma
  (requires (not (occurs x y)))
  (ensures (subst_term (x,z) y = y))
let rec lemma_subst_id x z y = match y with 
  | V x' -> ()
  | F t1 t2 -> lemma_subst_id x z t1; lemma_subst_id x z t2

let neutral s (x, t)   = subst_term s (V x) = V x  && subst_term s t = t  && ok (x, t)
let neutral_l l (x, t) = lsubst_term l (V x) = V x && lsubst_term l t = t && ok (x, t)

val lemma_lsubst_term_commutes: s:subst -> l:list subst -> e:term -> Lemma 
  (requires (neutral_l l s))
  (ensures (lsubst_term [s] (lsubst_term l (subst_term s e)) = 
	    lsubst_term [s] (lsubst_term l e)))		
let rec lemma_lsubst_term_commutes s l e = match e with
  | V y -> lemma_subst_id (fst s) (snd s) (snd s)
    
  | F t1 t2 -> lemma_lsubst_term_commutes s l t1;
	      lemma_lsubst_term_commutes s l t2

val lemma_subst_term_commutes: s1:subst -> s2:subst -> t:term -> Lemma
  (requires (neutral s2 s1))
  (ensures (subst_term s1 (subst_term s2 (subst_term s1 t)) =
	    subst_term s1 (subst_term s2 t)))
let lemma_subst_term_commutes s1 s2 t = lemma_lsubst_term_commutes s1 [s2] t
  
val lemma_lsubst_eqns_commutes: s:subst -> l:list subst -> e:eqns -> Lemma 
  (requires (neutral_l l s))
  (ensures (lsubst_eqns [s] (lsubst_eqns l (lsubst_eqns [s] e)) = 
	    lsubst_eqns [s] (lsubst_eqns l e)))		
let rec lemma_lsubst_eqns_commutes s l = function 
  | [] -> ()
  | (t1,t2)::tl -> lemma_lsubst_term_commutes s l t1;
		 lemma_lsubst_term_commutes s l t2;
		 lemma_lsubst_eqns_commutes s l tl

val lemma_subst_term_idem: s:subst -> t:term -> Lemma
  (requires (ok s))
  (ensures (subst_term s (subst_term s t) = subst_term s t))
let rec lemma_subst_term_idem s t = match t with 
  | V x -> lemma_subst_id (fst s) (snd s) (snd s)
  | F t1 t2 -> lemma_subst_term_idem s t1; lemma_subst_term_idem s t2
 
val key_lemma: x:nat -> y:term -> tl:eqns -> l:list subst -> lpre:list subst -> l'':list subst -> Lemma
  (requires (l'' = extend_lsubst lpre (extend_lsubst [(x, y)] l)
	     /\ not (occurs x y)
 	     /\ lsubst_eqns l ((V x, y)::tl) = (V x, y)::tl
 	     /\ solved (lsubst_eqns l'' (lsubst_eqns [x, y] tl))))
  (ensures (solved (lsubst_eqns l'' ((V x,y)::tl))))
let key_lemma x y tl l lpre l'' = 
  lemma_lsubst_eqns_commutes (x,y) l tl;
  lemma_subst_id x y y;
  assert (lsubst_eqns l'' [V x, y] = 
  	  lsubst_eqns lpre (lsubst_eqns [x,y] (lsubst_eqns l [V x, y])));
  assert (lsubst_eqns [x,y] (lsubst_eqns l [V x, y]) = 
  	  lsubst_eqns [x,y] [V x, y]);
  assert (lsubst_eqns [x,y] [V x, y] = 
	  [y,y])

val lemma_shift_append: l:list 'a -> x:'a -> m:list 'a -> Lemma
  (ensures ((l@(x::m)) = ((l@[x])@m)))
let rec lemma_shift_append l x m = match l with 
  | [] -> ()
  | hd::tl -> lemma_shift_append tl x m

val lemma_subst_eqns_idem: s:subst -> e:eqns -> Lemma
  (requires (ok s))
  (ensures (lsubst_eqns [s] (lsubst_eqns [s] e) = lsubst_eqns [s] e))
let rec lemma_subst_eqns_idem s = function
  | [] -> ()
  | (x, y)::tl -> lemma_subst_eqns_idem s tl;
	        lemma_subst_term_idem s x;
	        lemma_subst_term_idem s y

val subst_funs_monotone: s:subst -> t:term -> Lemma 
  (ensures (funs (subst_term s t) >= funs t))
let rec subst_funs_monotone s = function 
  | V x -> ()
  | F t1 t2 -> subst_funs_monotone s t1; subst_funs_monotone s t2

val lemma_occurs_not_solveable: x:nat -> t:term -> s:subst -> Lemma
  (requires (occurs x t /\ not (is_V t)))
  (ensures  (funs (subst_term s t) >= (funs t + funs (subst_term s (V x)))))
let rec lemma_occurs_not_solveable x t s = match t with 
  | F t1 t2 -> 
    if occurs x t1 
    then let _ = subst_funs_monotone s t2 in
	 match t1 with 
	   | V y -> ()
 	   | _ -> lemma_occurs_not_solveable x t1 s 
    else if occurs x t2
    then let _ = subst_funs_monotone s t1 in 
	 match t2 with 
	   | V y -> ()
 	   | _ -> lemma_occurs_not_solveable x t2 s 
    else ()

val unify_correct: l:list subst -> e:eqns -> Ghost (list subst)
 (requires (lsubst_eqns l e = e))
 (ensures (fun m ->
	    is_Some (unify e l) ==> 
	      Let (Some.v (unify e l)) (fun l' -> 
	            l' = (m @ l)
		 /\ solved (lsubst_eqns l' e))))
 (decreases %[n_evars e; efuns e; n_flex_rhs e])
let rec unify_correct l = function 
  | [] -> []
  | hd::tl -> 
    begin match hd with 
      | (V x, y) ->
	if is_V y && V.i y=x
	then unify_correct l tl
	else if occurs x y
	then []
	else begin 
	     let s = (x,y) in
	     let l' = extend_subst s l in
	     vars_decrease_eqns x y tl;
	     let tl' = lsubst_eqns [s] tl in 
	     lemma_extend_lsubst_distributes_eqns [s] l tl;
	     assert (lsubst_eqns l' tl' = lsubst_eqns [s] (lsubst_eqns l (lsubst_eqns [s] tl)));
	     lemma_lsubst_eqns_commutes s l tl;
	     lemma_subst_eqns_idem s tl;
	     let lpre = unify_correct l' tl' in
	     begin match unify tl' l' with 
	       | None -> []
	       | Some l'' -> 
		 key_lemma x y tl l lpre l'';
		 lemma_shift_append lpre s l;
		 lpre@[s]
	     end
	 end

      | (y, V x) -> 
	evars_permute_hd y (V x) tl; 
	unify_correct l ((V x, y)::tl)

      | F t1 t2, F s1 s2 -> 
	evars_unfun t1 t2 s1 s2 tl;
 	unify_correct l ((t1, s1)::(t2, s2)::tl)
     end


// l = hd::tl
// s = x, t
// ------------------------------------------------------
// subst_term s (lsubst_term (subst_lsubst s l) t)
// = {def}
// subst_term s (subst_term (subst_subst s hd) (lsubst_term (subst_lsubst s tl) t))
// = {lemma_cancel_subst_subst s hd ...}
// subst_term s (subst_term hd                 (lsubst_term (subst_lsubst s tl) t))
// = {subst_term_commutes} (ok s; subst_term hd (V x) = (V x); subst_term hd t = t)
// subst_term s (subst_term hd (subst_term s  (lsubst_term (subst_lsubst s tl) t)))
// = {IH}
// subst_term s (subst_term hd (subst_term s (lsubst_term tl t)))
// = {subst_term_commutes}  (ok s; subst_term hd (V x) = (V x); subst_term hd t = t)
// subst_term s (subst_term hd (lsubst_term tl t))
// = {def}
// subst_term s (lsubst_term l tl)


// val lemma_cancel_subst_subst: s1:subst -> s2:subst -> t:term -> Lemma
//   (requires (ok s1))
//   (ensures (subst_term s1 (subst_term (subst_subst s1 s2) t) =
//             subst_term s1 (subst_term s2 t)))
// let rec lemma_cancel_subst_subst s1 s2 t = match t with 
//   | V x -> 
//     if x = fst s2
//     then begin assert (subst_term (subst_subst s1 s2) t = 
// 		       subst_term s1 (subst_term s2 t));
// 	       lemma_subst_term_idem s1 (subst_term s2 t)
//          end
//     else begin assert (subst_term s2 t = t); 
// 	       assert (subst_term (subst_subst s1 s2) t = t)
// 	 end

//   | F t1 t2 -> lemma_cancel_subst_subst s1 s2 t1;
// 	      lemma_cancel_subst_subst s1 s2 t2

// val lemma_cancel_subst_lsubst: s:subst -> l:list subst -> t:term -> Lemma
//     (requires (neutral_l l s))
//     (ensures (subst_term s (lsubst_term (subst_lsubst s l) t) = 
// 	      subst_term s (lsubst_term l t)))
// let rec lemma_cancel_subst_lsubst s l t = match l with 
//   | [] -> ()
//   | hd::tl -> 
//     assert (subst_lsubst s l = subst_subst s hd::subst_lsubst s tl); 
//     assert (lsubst_term (subst_lsubst s l) t = 
// 	    subst_term (subst_subst s hd) (lsubst_term (subst_lsubst s tl) t));
//     lemma_cancel_subst_subst s hd (lsubst_term (subst_lsubst s tl) t);

//     assert (subst_term s (lsubst_term (subst_lsubst s l) t) = 
// 	    subst_term s (subst_term hd (lsubst_term (subst_lsubst s tl) t)));

//     lemma_cancel_subst_lsubst s tl t; 
//     assert (subst_term s (lsubst_term (subst_lsubst s l) t) = 
// 	    subst_term s (subst_term hd (subst_term s (lsubst_term tl t))));
//     admit()


//     assert (subst_term s (lsubst_term (subst_lsubst s tl) t) = 
// 	    subst_term s (lsubst_term tl t))
// 	    ;
//     admit()
