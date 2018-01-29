(** * High-level circuit definitions
*)
open Clflags

(*open Camlcoq*)
let internal_error str =
  Printf.fprintf stderr "Unexpected internal error!\n  %s\n" str;
  assert false

let fatal_error str =
  Printf.fprintf stderr "Fatal error!\n  %s\n" str;
  exit 1

let dbg_msg lvl str =
  if lvl <= !Clflags.option_dbglevel
  then Printf.fprintf stderr "dbg[%d]: %s\n" lvl str
  else ()

let msg = Printf.sprintf




(** ** Auxiliary functions...
 *)
let rec split_at n l =
 if n>0
 then match l with
      | [] -> ([],[])
      | x::xs -> let (a,b) = split_at (n-1) xs in (x::a,b)
 else ([],l)

let rec split_sizes (sizes: int list) l =
  match l, sizes with
    | [], [] -> []
    | _, x::xs -> if List.length l < x
		  then internal_error "split_sizes: not enough input!"
		  else let (a,b) = split_at x l
		       in a::split_sizes xs b
    | _, _ -> internal_error "split_sizes: too much input!\n"

let rec combine l =
  match l with
  | [] -> []
  | [x] -> x
  | x::xs -> let res = combine xs in 
	     List.concat (List.map (fun x->List.map (fun y->x@y) res) x)

let rec take_dfl dfl n l =
 if n>0
 then match l with
      | [] -> dfl::take_dfl dfl (n-1) []
      | x::xs -> x::take_dfl dfl (n-1) xs
 else []

let rec ins_ord_norep fcmp y l =
  match l with
  | [] -> [y]
  | x::xs -> if fcmp y < fcmp x
	     then y::x::xs 
	     else if fcmp x = fcmp y then x::xs else x::ins_ord_norep fcmp y xs

let rec list_pp sep a_pp pp l =
 match l with
 | [] -> ()
 | [x] -> a_pp pp x
 | x::xs -> Printf.fprintf pp "%a%s%a" a_pp x sep (list_pp sep a_pp) xs

let bits_pp pp l = list_pp "" (fun pp b->Printf.fprintf pp "%d" (if b then 1 else 0)) pp l




(** utility functions *)

let bits_of_str str =
 let acc = ref [] in
 for i = String.length(str)-1 downto 0 do
   if String.get str i = '0'
   then acc := false::!acc;
   if String.get str i = '1'
   then acc := true::!acc
 done;
 !acc

let rec rnd_bits n = 
 let acc = ref [] in
 for i = 1 downto n do
   acc := (Random.bool ())::!acc
 done;
 !acc

let rec uint_of_bits (v: bool list) : int =
  match v with
  | [] -> 0
  | x::xs -> let rest = uint_of_bits xs in (if x then 1 else 0) + 2*rest

(* We assume we are not interested in word sizes greater than 32 *)
let bits_of_int (size:int) (n:int) : bool list =
 let acc = ref [] in
 for i = size-1 downto 0 do
   acc := not (((1 lsl i) land n) = 0)::!acc
 done;
 !acc

let sint_of_bits (v: bool list) : int =
  let rec aux (n:int) (acc:int) (l:bool list) : int =
    match l with
    | [] -> internal_error "read_sint: there's no sign bit!"
    | [false] -> acc
    | [true] -> acc - (1 lsl n)
    | x::xs -> aux (n+1) (acc + if x then (1 lsl n) else 0) xs
  in aux 0 0 v

let rec all_bits n =
  if n=0 then [[]] else let aux = all_bits (n-1) in 
		      List.map (fun l->false::l) aux @ List.map (fun l->true::l) aux





(**
    Gates have a name; input and output arity; and a list of parameters
*)
type hlgate = { hlgname : string
	      ; hlgargs : int list
	      ; hlgin : int
	      ; hlgout : int
	      ; hlgsem : (bool list -> bool list) option
	      }

let mkhlgate name args inps outs =
 { hlgname = name
 ; hlgargs = args
 ; hlgin = inps
 ; hlgout = outs
 ; hlgsem = None
 }

let hlgate_cmp g = (g.hlgname,g.hlgargs)

(** Connectors are lists of wires (gate-number + position) *)
type hlconn = (int*int) list

(** Circuits specify a list of input-gates; circuit gates and their connections;
  and the output wires *)
type hlcirc = { hlcin : int list
	      ; hlcgates : (hlgate*hlconn) list
	      ; hlcout : hlconn
	      }

(** * ELEMENTARY GATES 
  Elementary circuits are built from just AND and XOR gates.
*)
let g_AND = mkhlgate "AND" [] 2 1

let g_XOR = mkhlgate "XOR" [] 2 1

(** 
    Connector operations
    ====================
*)

(* [sub_conn] picks a sublist from the original connector *)
let rec sub_conn g start size =
 if size > 0
 then (g,start)::sub_conn g (start+1) (size-1)
 else []

(* [rep_conn_n] produce a connector with [size] repetitions of [wire] *)
let rec rep_conn_n wire size =
 if size > 0
 then wire::rep_conn_n wire (size-1)
 else []

let rec zero_conn_n size = rep_conn_n (0,0) size

let rec conn_zero_ext size conn =
  take_dfl (0,0) size conn

let conn_sign_ext size conn =
 let rec sign_ext n d c =
   if n <= 0
   then []
   else (match c with
	 | (x::xs) -> x :: sign_ext (n-1) x xs
	 | _ -> d :: sign_ext (n-1) d []
	)
 in sign_ext size (0,0) conn
 
(* [offset_wires] shifts the positions of wires in a connector *)
let rec offset_wires off l =
 match l with
 | [] -> []
 | ((0,p)::xs) -> (0,p)::(offset_wires off xs)
 | ((w,p)::xs) -> (w+off,p)::(offset_wires off xs)

(* [offset_gates] shifts the position of wires on a list of gates *)
let rec offset_gates off l =
 match l with
 | [] -> []
 | ((g,c)::xs) -> (g,offset_wires off c)::(offset_gates off xs)

(* number of input-gates *)
let gc_ninputs gc = List.length gc.hlcin
(* number of input-wires *)
let gc_input_wires gc = List.fold_left (+) 0 gc.hlcin
(* number of output-wires *)
let gc_output_wires gc = List.length gc.hlcout
(* number of (normal) gates *)
let gc_ngates gc = List.length gc.hlcgates
(* index of last gate *)
let gc_lastg gc = gc_ninputs gc + gc_ngates gc


let wire_pp pp (g,p) = Printf.fprintf pp "(%d,%d)" g p

let hlconn_pp pp = 
 Printf.fprintf pp "[%a]" (list_pp ";" wire_pp)

let gate_pp pp gate =
  Printf.fprintf pp "%s(%a)" gate.hlgname
		 (list_pp ";" (fun pp i->Printf.fprintf pp "%d" i)) gate.hlgargs

let entry_pp pp (gate,conn) =
  Printf.fprintf pp "%a <- %a\n" gate_pp gate hlconn_pp conn

let hlcirc_pp pp circ =
  Printf.fprintf pp "INPUTS: [%a]\n%a\nOUTPUTS: %a"
		 (list_pp ";" (fun pp i->Printf.fprintf pp "%d" i))
		 circ.hlcin (list_pp "" entry_pp) circ.hlcgates
		 hlconn_pp circ.hlcout

(**
    Variable Size Arrays
    ====================
 *)

type 'a gArray = { mutable gAsize : int
		 ; mutable gAdata : ('a option) array
		 }

(* doubles the size of a gArray *)
let gArray_double x = x.gAdata <- Array.init (2*Array.length(x.gAdata))
					     (fun n -> if n < x.gAsize
						       then x.gAdata.(n)
						       else None)

(* initialises a gArray (FIXME: increase initial size) *)
let gArray_init () = 
  let init_size = 32
  in { gAsize = 0; gAdata = Array.make init_size None }

(* adds a new entry to the end of a gArray (increases size if needed) *)
let gArray_add' a entry =
 if a.gAsize >= Array.length (a.gAdata)
 then gArray_double a;
 a.gAdata.(a.gAsize) <- entry;
 a.gAsize <- a.gAsize + 1;
 a
let gArray_add a entry = gArray_add' a (Some entry)
let gArray_add_list a lentry = List.fold_left gArray_add a lentry

(* accesses an entry of a gArray *)
let gArray_get a pos =
 if (pos < 0) || (pos >= a.gAsize)
 then internal_error (msg "gArray_get: index %d out of range (size=%d)" pos a.gAsize)
 else match a.gAdata.(pos) with
      | Some x -> x
      | _ -> internal_error (msg "gArray_get: no data at position %d" pos)

(* removes an entry of a gArray *)
let gArray_del a pos =
 if (pos < 0) || (pos >= a.gAsize)
 then internal_error "gArray_del: index out of range"
 else a.gAdata.(pos) <- None

(* accesses consecutive entries of a gArray *)
let rec gArray_get_range a pos size =
 if size = 0
 then []
 else gArray_get a pos :: gArray_get_range a (pos+1) (size-1)

let gArray_pp a_pp pp a =
  Printf.fprintf pp "{| ";
  for i = 0 to a.gAsize-1 do
    match a.gAdata.(i) with
    | Some x -> Printf.fprintf pp "%a;" a_pp x
    | _ -> Printf.fprintf pp "*;"
  done;
  Printf.fprintf pp " |}"




(*
  Circuit Evaluation
  ==================
 *)

type evalSt = (bool list) gArray

let evalSt_init (inps: int list) (inval: bool list) : evalSt =
  let inps_val = split_sizes inps inval in
  let newSt = gArray_init ()
  in gArray_add newSt [false; true];
     List.iter (fun l -> gArray_add newSt l; ()) inps_val;
     newSt

let eval_entry (st: evalSt) (gate,conn) =
 try
  match gate.hlgname, conn with
  | "AND", [(g1,p1);(g2,p2)] ->
     gArray_add st
		[List.nth (gArray_get st g1) p1
		 && List.nth (gArray_get st g2) p2]; ()
  | "XOR", [(g1,p1);(g2,p2)] ->
     gArray_add st
		[if List.nth (gArray_get st g1) p1
		 then not (List.nth (gArray_get st g2) p2)
		 else List.nth (gArray_get st g2) p2]; ()
  | name, _ ->
     internal_error (msg "eval_entry: \"%s\" is not a valid (elementary) gate entry!" name)
 with exn ->
      Printf.fprintf stderr "Gate entry: %a \n" entry_pp (gate,conn);
      Printf.fprintf stderr "Eval State:\n%a\n" (gArray_pp bits_pp) st;
      raise exn

let gc_eval (gc: hlcirc) (input: bool list) : bool list =
 try
  if not (gc_input_wires gc = List.length input)
  then (internal_error "gc_eval: wrong number of inputs!");
  let st = evalSt_init gc.hlcin input in
  List.iter (eval_entry st) gc.hlcgates;
  List.map (fun (g,p) -> List.nth (gArray_get st g) p) gc.hlcout
 with exn ->
  Printf.fprintf stderr "Inputs: %a \n" bits_pp input;
  Printf.fprintf stderr "Circuit:\n%a \n" hlcirc_pp gc;
  raise exn

let gc_eval_test (gc: hlcirc) inp out : unit =
  if gc_input_wires gc <> List.length inp
  then fatal_error "unit-testing FAILURE! (input size mismatch)\n";
  if gc_output_wires gc <> List.length out
  then fatal_error "unit-testing FAILURE! (output size mismatch)\n";  
  let evout =  gc_eval gc inp in
  if gc_eval gc inp <> out
  then
    begin
      Printf.fprintf stderr "unit-testing FAILURE!\n";
      Printf.fprintf stderr " input:    %a\n" bits_pp inp;
      Printf.fprintf stderr " obtained: %a\n" bits_pp evout;
      Printf.fprintf stderr " expected: %a\n" bits_pp out;
      assert false
    end
  else
      Printf.fprintf stderr "unit-test OK!\n";
  ()

(*
  output wire SUBSTITUTIONS
  =========================
*)
type subst = ((int*int) array) gArray

let subst_entry_pp pp a =
  Printf.fprintf pp "[[(%d) " (Array.length a);
  for i = 0 to Array.length a-1 do
    Printf.fprintf pp "%a " wire_pp a.(i);
  done;
  Printf.fprintf pp "]]"
 

let subst_pp pp = gArray_pp subst_entry_pp pp

(* new substitution
   if wire information is given, it initializes inputs to the given wires.
   If not, ID input associations are added *)
let subst_new inps wires =
(*
  let rec subst_inps s wires inps =
    match wires, inps with
    | [], [] -> s
    | _, x::xs -> if List.length wires < x
		  then assert false
		  else let (a,b) = split_at x wires
		       in subst_inps (gArray_add s a) b xs
    | _, _ -> assert false in *)
  let s = gArray_init () in
  gArray_add s (Array.of_list [(0,0);(0,1)]); (* truth-values *)
(*Printf.printf "SUBST=%a\n" subst_pp s;*)
  match wires with
  | None -> List.fold_left (fun s n-> gArray_add s (Array.of_list (sub_conn s.gAsize 0 n))) s inps
  | Some l ->
     let inps_wires = split_sizes inps l in
     assert (List.length inps_wires = List.length inps);
     List.iter (fun idata->
(*Printf.printf "%d " (List.length idata);*)
	         gArray_add s (Array.of_list idata); ()) inps_wires;
(*Printf.printf "SUBST=%a\n" subst_pp s;*)
     s
  
(* applies a substitution to a wire *)
let subst_ap_wire s (g,pos) : int*int = (*(gArray_get s g).(pos)*)
  let subst = gArray_get s g in
  if pos >= Array.length subst
  then 
    begin
      (*Printf.fprintf stderr "SUBST=%a\n" subst_entry_pp subst;*)
      fatal_error (msg "Out-of-bounds access (%d@%d >= %d)\n" pos g (Array.length subst));
      (0,0)
    end
  else subst.(pos)

(* applies a substitution to a connector *)
let subst_ap (s:subst) (l:hlconn) : hlconn = 
(*  Printf.printf "S=%a\nC=%a\n" subst_pp s hlconn_pp l;*)
  List.map (subst_ap_wire s) l

(*
  circuit descriptions
  ====================
 *)
type circST = { cinps : int list (* input gates *)
	      ; mutable cdata : (hlgate * hlconn) gArray
	      }

let circ_add circ gate conn = 
  if (gate.hlgin != List.length conn)
  then internal_error (msg "circ_add: mismatch on circuit entry %s\n" gate.hlgname);
  gArray_add circ.cdata (gate,conn)

let circ_new inps =
  let newcirc = { cinps = inps; cdata = gArray_init () }
  in List.iter (fun n -> newcirc.cdata <- gArray_add' newcirc.cdata None) (2::inps);
     newcirc

let circ_lastg circ = circ.cdata.gAsize-1

let circST_pp pp circ =
  Printf.fprintf pp "INPUTS: [%a]\n%a" (list_pp ";" (fun pp i->Printf.fprintf pp "%d" i))
		 circ.cinps (gArray_pp entry_pp) circ.cdata

(* [circ_acc] remove entries that are inacessible (from the output)
  obs: only meaningful for elementary circuits (all gates have 1-out-arity)
*)
let circ_acc circ outs =
  let odeg = Array.make circ.cdata.gAsize 0 in
  for i = List.length circ.cinps + 1 to circ.cdata.gAsize - 1 do
    match circ.cdata.gAdata.(i) with
    | Some (_,conn) -> List.iter (fun (g,_)->odeg.(g) <- 1 + odeg.(g)) conn
    | None -> ()
  done;
  List.iter (fun (g,_) -> odeg.(g) <- 1+odeg.(g)) outs;
  for i = circ.cdata.gAsize - 1 downto List.length circ.cinps + 1 do
    if odeg.(i) = 0
    then
      begin
	match circ.cdata.gAdata.(i) with
	| Some (_,conn) -> List.iter (fun (g,_)->odeg.(g) <- odeg.(g)-1) conn;
			   gArray_del circ.cdata i
	| None -> ()
      end;
  done;
  odeg,circ

let test_circ_acc () = 
 let test_circ =
   let c = circ_new [2;1;2] in
   circ_add c g_XOR [(0,1);(2,0)];
     (*gArray_add' c.cdata None;*)
     circ_add c g_XOR [(1,1);(3,0)];
     circ_add c g_AND [(5,0);(4,0)];
   circ_add c g_AND [(3,1);(4,0)];
     (*gArray_add' c.cdata None;*)
     circ_add c g_XOR [(1,1);(2,0)];
     circ_add c g_XOR [(1,0);(8,0)];
   circ_add c g_XOR [(7,0);(4,0)];
   c
 in circ_acc test_circ [(10,0);(7,0);(4,0)]

(* [circ_dump] extracts a [hlcirc] from [circST] data.
  It performs reindexing in order to handle removed entries from the circuit data
 *)
let circ_dump circ outs =
  let gmap = gArray_add_list (gArray_init()) (List.mapi (fun i _->i) (2::circ.cinps))
  and gmap_ap s (g,p) = (gArray_get s g, p)
  and acc = ref [] 
  and acc_n = ref (List.length circ.cinps + 1) in
  (* check initial EMPTY entries (inputs) *)
  for i = 0 to List.length circ.cinps do
    assert (circ.cdata.gAdata.(i)=None)
  done;
  (* remove inaccessible gates *)
  circ_acc circ outs;
  (* process gates *)
  for i = gmap.gAsize to circ.cdata.gAsize-1 do
    match circ.cdata.gAdata.(i) with
    | Some (gate,conn) -> 
       gArray_add gmap !acc_n;
       acc := (gate,List.map (gmap_ap gmap) conn)::!acc;
       acc_n := 1 + !acc_n
    | _ -> gArray_add' gmap None; ()
  done;
  { hlcin = circ.cinps
  ; hlcgates = List.rev !acc
  ; hlcout = List.map (gmap_ap gmap) outs
  }

let test_circ_dump () = 
 let test_circ =
   let c = circ_new [2;1;2] in
   circ_add c g_XOR [(0,1);(2,0)];
     (*gArray_add' c.cdata None;*)
     circ_add c g_XOR [(1,1);(3,0)];
     circ_add c g_AND [(5,0);(4,0)];
   circ_add c g_AND [(3,1);(4,0)];
     (*gArray_add' c.cdata None;*)
     circ_add c g_XOR [(1,1);(2,0)];
     circ_add c g_XOR [(1,0);(8,0)];
   circ_add c g_XOR [(7,0);(4,0)];
   c
 in circ_dump test_circ [(10,0);(7,0);(4,0)]


(** GATE SIMPLIFICATION... 
 *)

let g_simpl_rule circ gate conn = 
 if !Clflags.option_nosimpl
 then None
 else
   match gate.hlgname with
   | "AND" -> (match conn with
	       | [(0,0);x] -> Some (0,0)
	       | [(0,1);x] -> Some x
	       | [w1; w2] -> if w1=w2 then Some w1 else None)
   | "XOR" -> (match conn with
	       | [(0,0);x] -> Some x
	       | [(0,1);(0,1)] -> Some (0,0)
	       | [(0,1);(g2,0)] ->
		  (match circ.cdata.gAdata.(g2) with
		   | Some (g,c) -> (match g.hlgname, c with
				    | "XOR", [(0,1);w] -> Some w
				    | _ -> None)
		   | _ -> None)
	       | [w1; w2] -> if w1=w2 then Some (0,0) else None)
   | name -> internal_error (msg "g_simpl_rule: unknown gate %s" name)

(** STATS
  summarises statitics for a circuits (number os ANDs/XORs/TTs/FFs)
 *)
type statsST = { mutable stats_and : int
	       ; mutable stats_xor : int
	       ; mutable stats_tt : int
	       ; mutable stats_ff : int
	       }
let gc_stats gc =
 let rec count_01 l =
   match l with
   | [] -> (0,0)
   | (0,0)::xs -> let (a,b) = count_01 xs in (a+1,b)
   | (0,1)::xs -> let (a,b) = count_01 xs in (a,b+1)
   | _::xs -> count_01 xs
 in
 let rec stats_aux stats l =
   match l with
   | [] -> stats
   | (gate,conn)::xs -> stats_aux stats xs;
			let (a,b) = count_01 conn in
			match gate.hlgname with
			| "AND" -> stats.stats_and <- 1 + stats.stats_and;
				   stats.stats_ff <- a + stats.stats_ff;
				   stats.stats_tt <- b + stats.stats_tt;
				   stats
			| "XOR" -> stats.stats_xor <- 1 + stats.stats_xor;
				   stats.stats_ff <- a + stats.stats_ff;
				   stats.stats_tt <- b + stats.stats_tt;
				   stats
			| name -> Printf.fprintf stdout 
				    "gc_stats: unknown gate %s\n" name;
				  assert false
 in stats_aux {stats_and=0; stats_xor=0; stats_tt=0; stats_ff=0} gc.hlcgates


let gc_stats_pp pp gc =
 let stats = gc_stats gc in
 Printf.fprintf pp "Input wires: %d\n" (gc_input_wires gc);
 Printf.fprintf pp "AND gates: %d\n" stats.stats_and;
 Printf.fprintf pp "XOR gates: %d\n" stats.stats_xor;
 Printf.fprintf pp "TT gates: %d\n" stats.stats_tt;
 if stats.stats_ff > 0
 then Printf.fprintf pp "FF gates: %d\n" stats.stats_ff;
 Printf.fprintf pp "Output wires: %d\n" (gc_output_wires gc)


(*
   indexes for the memoization table are [bool*wire*wire].
 *)
let gate_memo = (Hashtbl.create 179 : (bool*int*int*int*int, int) Hashtbl.t)
(*let gate_memo_enable = ref false*)

let gate_memo_get (g,l) =
  if false (*!gate_memo_enable*)
  then
    let entry =
      match g.hlgname, l with
      | "AND", [(g1,p1);(g2,p2)] -> 
	 dbg_msg 15 (msg "memo_get false,%d,%d" g1 g2);
	 (false, g1, p1, g2, p2)
      | "XOR", [(g1,p1);(g2,p2)] ->
	 dbg_msg 15 (msg "memo_get true,%d,%d" g1 g2);
	 (true, g1, p1, g2, p2)
      | _, _ ->
	 internal_error "gate_memo_get: non-elementary gate!"
    in
    try
      let x = Hashtbl.find gate_memo entry in Some x
    with Not_found ->
      dbg_msg 15 (msg "memo_get FAIL");
      None
  else None

let gate_memo_set (g,l) index =
  if true (*!gate_memo_enable*)
  then
    let entry =
      match g.hlgname, l with
      | "AND", [(g1,p1);(g2,p2)] -> 
	 (*       Printf.printf "memo_set false,%d,%d\n" g1 g2;*)
	 (false, g1, p1, g2, p2)
      | "XOR", [(g1,p1);(g2,p2)] ->
	 (*       Printf.printf "memo_set true,%d,%d\n" g1 g2;*)
	 (true, g1, p1, g2, p2)
      | _, _ ->
	 internal_error "gate_memo_set: non-elementary gate!"
    in Hashtbl.add gate_memo entry index
  

let rec xpnd_gc_aux xpnd_rule circ subst gates outs =
 let norm_conn conn =
   match conn with
   | [(g1,p1);(g2,p2)] -> if g1<g2 || g1=g2 && p1<p2
			  then conn
			  else [(g2,p2);(g1,p1)]
   | _ -> conn
 in
 match gates with
 | [] -> Timing.time2 "  subst AP" subst_ap subst outs
 | (gate,conn)::xs ->
    if (gate.hlgin != List.length conn)
    then internal_error (msg "malformed circuit at gate %s (in_arity=%d != conn_size=%d)\n" gate.hlgname gate.hlgin (List.length conn));	
     match xpnd_rule gate with
     | None ->
	let conn' = norm_conn (Timing.time2 "  subst AP" subst_ap subst conn) in
	begin
	  match g_simpl_rule circ gate conn' with
	  | Some w -> 
	     gArray_add subst (Array.of_list [w]);
	     xpnd_gc_aux xpnd_rule circ subst xs outs
	  | None -> 
	     (* CHECK MEMOIZATION... *)
	     match gate_memo_get (gate, conn') with
	     | Some n -> 
		gArray_add subst (Array.of_list [(n,0)]);
		xpnd_gc_aux xpnd_rule circ subst xs outs
	     | None -> 
		circ_add circ gate conn';
		gate_memo_set (gate,conn') (circ_lastg circ);
		gArray_add subst (Array.of_list (sub_conn (circ_lastg circ) 0 gate.hlgout));
		xpnd_gc_aux xpnd_rule circ subst xs outs
	end
     | Some gc -> 
	if (gate.hlgin != gc_input_wires gc)
	then internal_error (msg "xpnd_table error: in_arity of gate %s (%d != %d)\n" gate.hlgname gate.hlgin (gc_input_wires gc));
	if (gate.hlgout != gc_output_wires gc)
	then internal_error (msg "xpnd_table error: output_arity of gate %s (%d != %d)\n" gate.hlgname gate.hlgout (gc_output_wires gc));
(*
        (* Testing xpnd procedure... *)
	begin match gate.hlgsem with
	| None -> ()
	| Some fsem ->
	   if !Clflags.option_selftest > 0
	   then 
	     begin
	       (* during test, we need to disable the memoization mechanism *)
	       gate_memo_enable := false;
	       let tcirc = circ_new gc.hlcin
	       and s = subst_new gc.hlcin None in
	       let gout = xpnd_gc_aux xpnd_rule tcirc s gc.hlcgates gc.hlcout in
	       (*Printf.printf "%a CIRCUIT = %a\n" gate_pp gate circST_pp tcirc; *)
	       gc_test gate (circ_dump tcirc gout);
	       gate_memo_enable := not !Clflags.option_nomemo;
	     end
	end;
 *)
	let conn' = Timing.time2 "  subst AP" subst_ap subst conn in
(*Printf.printf "SIZE=%d " (List.length conn');*)
	let news = subst_new gc.hlcin (Some conn') in
	let gout = xpnd_gc_aux xpnd_rule circ news gc.hlcgates gc.hlcout in
	gArray_add subst (Array.of_list gout);
	xpnd_gc_aux xpnd_rule circ subst xs outs

let xpnd_gc xpnd_rule gc =
  (* initialize memo mechanism... *)
  Hashtbl.reset gate_memo;
  (*gate_memo_enable := not !Clflags.option_nomemo;*)
  (* inicialize working circuit and substitution... *)
  let circ = circ_new gc.hlcin in
  let subst = subst_new gc.hlcin None in
  (* Printf.printf "initial CIRCUIT = %a\n" circST_pp circ; *)
  (* compute the circuit expansion... *)
  let outc = Timing.time5 "  llcirc generation" xpnd_gc_aux xpnd_rule circ subst gc.hlcgates gc.hlcout in
  (* Printf.printf "final CIRCUIT = %a\nOUTS = %a\n" circST_pp circ hlconn_pp outc; *)
  (* compose the final circuit *)
  Timing.time2 "  llcirc simplification" circ_dump circ outc







(** TESTS
  perform random tests on a circuit
 *)
let rec rnd_blist n =
 let rec int_to_blist n x =
   if n>0
   then ((x land 1)>0)::int_to_blist (n-1) (x lsr 1) 
   else []
 and nb = ref n
 and rnd = ref []
 in while !nb > 30 do
      rnd := int_to_blist 30 (Random.bits ()) @ !rnd;
      nb := !nb - 30
    done;
    int_to_blist !nb (Random.bits ()) @ !rnd

let gc_test gate gc =
  match gate.hlgsem with
  | Some fsem ->
   dbg_msg 10 (msg "testing gate %s" gate.hlgname);
(*
Printf.fprintf stderr "G: %a\n" gate_pp gate;
Printf.fprintf stderr "GC: %a\n" hlcirc_pp gc;
 *)
   for i = 0 to !Clflags.option_selftest do
     let rnd_inp = rnd_blist (gc_input_wires gc) in
     let ev_res = gc_eval gc rnd_inp 
     and fsem_res = take_dfl false (gc_output_wires gc) (fsem rnd_inp) in
     if ev_res <> fsem_res
     then
       begin
	 let inps = split_sizes gc.hlcin rnd_inp in
	 Printf.fprintf stderr "Test failed on gate \"%a\"\n" gate_pp gate;
	 Printf.fprintf stderr "Inputs:   %a\n" (list_pp " " bits_pp) (split_sizes gc.hlcin rnd_inp);
	 Printf.fprintf stderr "Expected: %a\n" bits_pp fsem_res;
	 Printf.fprintf stderr "Computed: %a\n" bits_pp ev_res;
	 Printf.fprintf stderr "CIRCUIT:\n%a\n" hlcirc_pp gc;
	 assert false
       end
     else ()
   done;
   dbg_msg 10 (msg "end testing gate %s" gate.hlgname);
  | None -> ()
  

