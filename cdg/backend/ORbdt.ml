(** * Ordered-Reduced Binary Decision Trees 
*)

open Printf


type 'a bdd = Leaf of 'a | Node of int *'a bdd* 'a bdd

let rec bdd_eq bdd1 bdd2 =
 match bdd1, bdd2 with
 | Leaf x1, Leaf x2 -> x1=x2
 | Node (v1, l1, r1), Node (v2, l2, r2) ->
    v1=v2 && bdd_eq l1 l2 && bdd_eq r1 r2
 | _, _ -> false

let chkN v bdd1 bdd2 =
 if bdd_eq bdd1 bdd2 then bdd1 else Node (v,bdd1,bdd2)

(** ** Path-Conditions
  PadthConditions are stored as BDDs with boolean leafs
 *)
type pcond = bool bdd

(* building BDDs *)
let bdd_lit v = Node (v,Leaf true,Leaf false)
let bdd_lit_neg v = Node (v,Leaf false,Leaf true)

let rec bdd_not bdd =
 match bdd with
 | Leaf x -> Leaf (not x)
 | Node (v,l,r) -> Node (v,bdd_not l,bdd_not r)

let rec bdd_and bdd1 bdd2 =
 match bdd1, bdd2 with
 | Leaf true, _ -> bdd2
 | Leaf false, _ -> Leaf false
 | _, Leaf true -> bdd1
 | _, Leaf false -> Leaf false
 | Node (v1,l1,r1), Node (v2,l2,r2) ->
    if v1=v2
    then chkN v1 (bdd_and l1 l2) (bdd_and r1 r2)
    else if v1 > v2
         then chkN v1 (bdd_and l1 bdd2) (bdd_and r1 bdd2)
         else chkN v2 (bdd_and bdd1 l2) (bdd_and bdd1 r2)

let rec bdd_or bdd1 bdd2 =
 match bdd1, bdd2 with
 | Leaf true, _ -> Leaf true
 | Leaf false, _ -> bdd2
 | _, Leaf true -> Leaf true
 | _, Leaf false -> bdd1
 | Node (v1,l1,r1), Node (v2,l2,r2) ->
    if v1=v2
    then chkN v1 (bdd_or l1 l2) (bdd_or r1 r2)
    else if v1 > v2
         then chkN v1 (bdd_or l1 bdd2) (bdd_or r1 bdd2)
         else chkN v2 (bdd_or bdd1 l2) (bdd_or bdd1 r2)

(* quering BDDs *)

(* check of two path-conditions are disjoint *)
let rec bdd_disjoint bdd1 bdd2 = (bdd_and bdd1 bdd2 = Leaf false)

(* check for implication *)
let rec bdd_leq bdd1 bdd2 = (bdd_or (bdd_not bdd1) bdd2 = Leaf true)

(* pretty-printing of path-conditions *)
let rec pcond_pp pp bdd =
 match bdd with
 | Leaf true -> fprintf pp "T"
 | Leaf false -> fprintf pp "F"
 | Node (v,l,r) -> fprintf pp "(%d?%a:%a)" v pcond_pp l pcond_pp r

(** ** BDDs for phi-nodes
  Phi-nodes are represented as BDDs whose leafs are variable identifiers.

  Remark: when leafs point to variable identifiers that are constants, we
  also store the constant in the phi-node. It will allow us to recognize
  when a variable is an alternative of different constants, in which case
  we might be interested in distribute those different constants with
  certain operations (e.g. in indexes of array accesses)
*)

type phi_node = int bdd

(* adds the association path-condition/identifier+constval to an existing
  phi_node *)
let rec phi_add i c pcond phi =
 match phi, pcond with
 | _, Leaf true -> Leaf (i,c)
 | _, Leaf false -> phi
 | Leaf x, Node (v',l',r') ->
    chkN v' (phi_add i c l' phi) (phi_add i c r' phi)
 | Node (v,l,r), Node (v',l',r') ->
    if v = v'
    then chkN v (phi_add i c l' l) (phi_add i c r' r)
    else if v > v'
         then chkN v (phi_add i c pcond l) (phi_add i c pcond r)
         else chkN v' (phi_add i c l' phi) (phi_add i c r' phi)

(* returns the list of constants (for phi_nodes that are indeed
 an alternative of constants...) *)
let rec phi_constants phi =
 match phi with
 | Leaf (_, Some c) -> Some [c]
 | Leaf (_, None) -> None
 | Node (_, l, r) -> match phi_constants l, phi_constants r with
		     | None, _ -> None
		     | _, None -> None
		     | Some l1, Some l2 -> Some (l1@l2)

(* returns the specialization of a phi-node for a given path-condition 
  remark: we assume the path-condition is satisfiable (i.e. is not "F")
*)
let rec phi_slice pcond phi =
 match phi, pcond with
 | _, Leaf false -> assert false
 | _, Leaf true -> phi
 | Leaf x, _ -> Leaf x
 | Node (v,l,r), Node (v',Leaf false,r') ->
    if v = v'
    then phi_slice r' r
    else if v > v'
         then chkN v (phi_slice pcond l) (phi_slice pcond r)
         else phi_slice r' phi
 | Node (v,l,r), Node (v',l',Leaf false) ->
    if v = v'
    then phi_slice l' l
    else if v > v'
         then chkN v (phi_slice pcond l) (phi_slice pcond r)
         else phi_slice l' phi
 | Node (v,l,r), Node (v',l',r') ->
    if v = v'
    then chkN v (phi_slice l' l) (phi_slice r' r)
    else if v > v'
         then chkN v (phi_slice pcond l) (phi_slice pcond r)
         else chkN v' (phi_slice l' phi) (phi_slice r' phi)

(* pretty-printing of phi-nodes *)
let rec phi_pp pp bdd =
 match bdd with
 | Leaf (n,None) -> fprintf pp "@%d" n
 | Leaf (n,Some x) -> fprintf pp "@%d[=%d]" n x
 | Node (v,l,r) -> fprintf pp "(%d?%a:%a)" v phi_pp l phi_pp r

let max_bdd bdd =
  let rec max_aux n bdd = 
   match bdd with
   | Leaf (x,_) -> if x > n then x else n
   | Node (_,l,r) -> let v1 = (max_aux n l) and v2 = (max_aux n r) in
                     if v1 > v2 then v1 else v2
 in max_aux 0 bdd

let paths_bdd dbb =
  let rec aux_paths li bdd =
    match bdd with
     | Leaf(i,_) -> [(i,li)]
     | Node(p, l, r) -> (aux_paths ((p,false)::li) l)@(aux_paths ((p,true)::li) r) 
  in aux_paths [] dbb

let bdd_leaf v = Leaf (v,None)
