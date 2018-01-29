(** Pretty-printers for HLCirc code *)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open Integers

open ORbdt
open HLCirc
open OpGates
open Mlcirc
open Mlcirc_gates



(* UNIT testing *)
let char_to_bits = function
  | '0' -> [false;false;false;false]
  | '1' -> [true;false;false;false]
  | '2' -> [false;true;false;false]
  | '3' -> [true;true;false;false]
  | '4' -> [false;false;true;false]
  | '5' -> [true;false;true;false]
  | '6' -> [false;true;true;false]
  | '7' -> [true;true;true;false]
  | '8' -> [false;false;false;true]
  | '9' -> [true;false;false;true]
  | 'a' | 'A' -> [false;true;false;true]
  | 'b' | 'B' -> [true;true;false;true]
  | 'c' | 'C' -> [false;false;true;true]
  | 'd' | 'D' -> [true;false;true;true]
  | 'e' | 'E' -> [false;true;true;true]
  | 'f' | 'F' -> [true;true;true;true]
  | _ -> assert false

(*
let rec bits_to_chars l =
  match l with
  | false::false::false::false::xs -> '0'::bits_to_chars xs
  | true::false::false::false::xs -> '1'::bits_to_chars xs
  | false::true::false::false::xs -> '2'::bits_to_chars xs
  | true::true::false::false::xs -> '3'::bits_to_chars xs
  | false::false::true::false::xs -> '4'::bits_to_chars xs
  | true::false::true::false::xs -> '5'::bits_to_chars xs
  | false::true::true::false::xs -> '6'::bits_to_chars xs
  | true::true::true::false::xs -> '7'::bits_to_chars xs
  | false::false::false::true::xs -> '8'::bits_to_chars xs
  | true::false::false::true::xs -> '9'::bits_to_chars xs
  | false::true::false::true::xs -> 'a'::bits_to_chars xs
  | true::true::false::true::xs -> 'b'::bits_to_chars xs
  | false::false::true::true::xs -> 'c'::bits_to_chars xs
  | true::false::true::true::xs -> 'd'::bits_to_chars xs
  | false::true::true::true::xs -> 'e'::bits_to_chars xs
  | true::true::true::true::xs -> 'f'::bits_to_chars xs
  | _ -> assert false

let hexbits_pp pp l = list_pp "" (fun pp c->Printf.fprintf pp "%c" c) pp (bits_to_chars l)
 *)

let conv_hexstr str =
  let strlen = String.length str
  and res = ref [] in
  if strlen mod 2 <> 0
  then (Printf.fprintf stderr "Malformed hex-string (odd size)\n"; assert false);
  for i = strlen / 2 - 1 downto 0 do
    res := char_to_bits str.[2*i+1] @ (char_to_bits str.[2*i] @ !res)
  done;
  !res

let read_file filename = 
  let lines = ref [] in
  try
    let chan = open_in filename in
    try
      while true; do
	lines := (conv_hexstr (input_line chan),
		  conv_hexstr (input_line chan)) :: !lines
      done; !lines
    with
    | End_of_file ->
       close_in chan;
    List.rev !lines
  with _ -> 
     begin
       Printf.fprintf stderr "Warning: Could read test file \"%s\"!  (skipping...)\n" filename;
       []
     end

let unittest_file = ref (None: string option)

let llcirc_unittest_if circ =
  match !unittest_file with
  | None -> ()
  | Some f -> 
     let ltests = read_file f in
     List.iter (fun (out,inp) -> 
(*Printf.fprintf stdout "inp[%d]=%a\nout[%d]=%a\n" (List.length inp) bits_pp inp (List.length out) bits_pp out;*)
	 gc_eval_test circ inp out) ltests




(* 
   convert between Coq's HLCirc and OCaml's hlcirc types
*)
let rec conv_gate gate = 
 let camlgate name args = { hlgin = N.to_int (gateInfo gate).gate_in_arity
			  ; hlgargs = args
			  ; hlgname = name
			  ; hlgout = N.to_int (gateInfo gate).gate_out_arity
			  ; hlgsem = Some (gateInfo gate).gate_ev
			  } in
 match gate with
 | G_AND -> camlgate "AND" []
 | G_XOR -> camlgate "XOR" []
 | Geq32 -> camlgate "eq32" []
 | Gneq32 -> camlgate "neq32" []
 | Gslt32 -> camlgate "slt32" []
 | Gsle32 -> camlgate "sle32" []
 | Gsgt32 -> camlgate "sgt32" []
 | Gsge32 -> camlgate "sge32" []
 | Gult32 -> camlgate "ult32" []
 | Gule32 -> camlgate "ule32" []
 | Gugt32 -> camlgate "ugt32" []
 | Guge32 -> camlgate "uge32" []
 | Geq32i n -> camlgate "eq32i" [Z.to_int n]
 | Gneq32i n -> camlgate "neq32i" [Z.to_int n]
 | Gslt32i n -> camlgate "slt32i" [Z.to_int n]
 | Gsle32i n -> camlgate "sle32i" [Z.to_int n]
 | Gsgt32i n -> camlgate "sgt32i" [Z.to_int n]
 | Gsge32i n -> camlgate "sge32i" [Z.to_int n]
 | Gult32i n -> camlgate "ult32i" [Z.to_int n]
 | Gule32i n -> camlgate "ule32i" [Z.to_int n]
 | Gugt32i n -> camlgate "ugt32i" [Z.to_int n]
 | Guge32i n -> camlgate "uge32i" [Z.to_int n]
 | Gmaskzero n -> camlgate "maskzero" [Z.to_int n]
 | Gnotmaskzero n -> camlgate "notmaskzero" [Z.to_int n]
 | Gconst32 n -> camlgate "const32" [Z.to_int n]
 | Gsint_cast size -> camlgate "sint_cast" [N.to_int size]
 | Guint_cast size -> camlgate "uint_cast" [N.to_int size]
 | Gadd32 -> camlgate "add32" []
 | Gadd32i n -> camlgate "add32i" [Z.to_int n]
 | Gaddadd32i n -> camlgate "addadd32i" [Z.to_int n]
 | Gmuladd32i (n1,n2) -> camlgate "muladd32i" [Z.to_int n1; Z.to_int n2]
 | Gmuladdadd32i (n1,n2) -> camlgate "muladdadd32i" [Z.to_int n1; Z.to_int n2]
 | Gneg32 -> camlgate "neg32" []
 | Gsub32 -> camlgate "sub32" []
 | Gmul32 -> camlgate "mul32" []
 | Gmul32i n -> camlgate "mul32i" [Z.to_int n]
 | Gmulhs -> camlgate "mul32hs" []
 | Gmulhu -> camlgate "mul32hu" []
 | Gand32 -> camlgate "and32" []
 | Gand32i n -> camlgate "and32i" [Z.to_int n]
 | Gor32 -> camlgate "or32" []
 | Gor32i n -> camlgate "or32i" [Z.to_int n]
 | Gxor32 -> camlgate "xor32" []
 | Gxor32i n -> camlgate "xor32i" [Z.to_int n]
 | Gnot32 -> camlgate "not32" []
 | Gshl32 -> camlgate "shl32" []
 | Gshl32i n -> camlgate "shl32i" [Z.to_int n]
 | Gshr32 -> camlgate "shr32" []
 | Gshr32i n -> camlgate "shr32i" [Z.to_int n]
 | Gshrx32i n -> camlgate "shrx32i" [Z.to_int n]
 | Gshru32 -> camlgate "shru32" []
 | Gshru32i n -> camlgate "shru32i" [Z.to_int n]
 | Gror32i n -> camlgate "ror32i" [Z.to_int n]
 | Gshld32i n -> camlgate "shld32i" [Z.to_int n]
 | Gint64 -> camlgate "int64" []
 | Gint64low -> camlgate "int64low" []
 | Gint64hi -> camlgate "int64hi" []
 | Gid n -> camlgate "id" [N.to_int n]
 | Gcmp_uint g -> let cg = conv_gate g in
		  { cg with hlgout = 32; hlgname = "cmp_" ^ cg.hlgname }
 | Gcond -> camlgate "cond" []
 | GxorN n -> camlgate "xorN" [N.to_int n]
 | GcondN n -> camlgate "condN" [N.to_int n]
 | GbarrierN n -> camlgate "barrierN" [N.to_int n]
 | Gconstbytes l -> camlgate "constbytes" (List.map Z.to_int l)
 | Gguard cond -> camlgate "guard" (pcond_to_list cond)
 | Gselk ((width,size),ofs) -> camlgate "selk" [N.to_int width; N.to_int size; N.to_int ofs]
 | Gdsel (width,size) -> camlgate "dsel" [N.to_int width; N.to_int size]
 | Gsel (width,size) -> camlgate "sel" [N.to_int width; N.to_int size]
 | Gupdk ((width,size),ofs) -> camlgate "updk" [N.to_int width; N.to_int size; N.to_int ofs]
 | Gdupd (width,size) -> camlgate "dupd" [N.to_int width; N.to_int size]
 | Gupd (width,size) -> camlgate "upd" [N.to_int width; N.to_int size]

let rec conv_conn conn = List.map (fun (a,b) -> (N.to_int a,N.to_int b)) conn

let convert_circ hlcirc =
  let conv_gentries l = List.fold_left (fun r x -> (conv_gate x.gate
						   ,conv_conn x.conn)::r)
				       [] hlcirc.gates
  and inps = N.to_int hlcirc.inputs
  and globs = List.map (fun l -> mkhlgate "constbytes" (List.map Z.to_int l)
					  0 (8*List.length l), [])
		       hlcirc.initconsts
  and outs = conv_conn hlcirc.outputs in
  let hlcirc_gates = globs @ List.rev (conv_gentries hlcirc.gates)
  in { hlcin = [inps]
     ; hlcgates = hlcirc_gates
     ; hlcout = outs
     }


(* Circuit expansion *)

let circ_memo = (Hashtbl.create 179 : (bool*int*int*int*int, int) Hashtbl.t)
let circ_memo_enable = ref false
let circ_memo_get (g,l) =
  if !circ_memo_enable
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
	 internal_error "circ_memo_get: non-elementary gate!"
    in
    try
      let x = Hashtbl.find circ_memo entry in Some x
    with Not_found ->
      dbg_msg 15 (msg "memo_get FAIL");
      None
  else None

let circ_memo_set (g,l) index =
  if !circ_memo_enable
  then
    let entry =
      match g.hlgname, l with
      | "AND", [(g1,p1);(g2,p2)] -> 
	        (*Printf.printf "memo_set false,%d,%d\n" g1 g2;*)
	 (false, g1, p1, g2, p2)
      | "XOR", [(g1,p1);(g2,p2)] ->
	        (*Printf.printf "memo_set true,%d,%d\n" g1 g2;*)
	 (true, g1, p1, g2, p2)
      | _, _ ->
	 internal_error "circ_memo_set: non-elementary gate!"
    in Hashtbl.add circ_memo entry index

let rec xpnd_circ_aux circ subst gates outs =
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
(* Printf.printf "processing %s\n" gate.hlgname;*)
    if (gate.hlgin != List.length conn)
    then internal_error (msg "malformed circuit at gate %s (in_arity=%d != conn_size=%d)\n" gate.hlgname gate.hlgin (List.length conn));	
     match compcert_xpnd_rule gate with
     | None ->
	let conn' = norm_conn (subst_ap subst conn) in
	begin
	  match g_simpl_rule circ gate conn' with
	  | Some w -> 
	     ignore (gArray_add subst (Array.of_list [w]));
	     xpnd_circ_aux circ subst xs outs
	  | None -> 
	     match circ_memo_get (gate, conn') with
	     | Some n -> 
		ignore (gArray_add subst (Array.of_list [(n,0)]));
		xpnd_circ_aux circ subst xs outs
	     | None -> 
		ignore (circ_add circ gate conn');
		circ_memo_set (gate,conn') (circ_lastg circ);
		ignore (gArray_add subst (Array.of_list (sub_conn (circ_lastg circ) 0 gate.hlgout)));
		xpnd_circ_aux circ subst xs outs
	end
     | Some gc -> 
(*Printf.printf "GATE = %s\n" gate.hlgname;*)
	if (gate.hlgin != gc_input_wires gc)
	then internal_error (msg "xpnd_table error: in_arity of gate %s (%d != %d)\n" gate.hlgname gate.hlgin (gc_input_wires gc));
	if (gate.hlgout != gc_output_wires gc)
	then internal_error (msg "xpnd_table error: output_arity of gate %s (%d != %d)\n" gate.hlgname gate.hlgout (gc_output_wires gc));
        (* Testing xpnd procedure... *)
	begin match gate.hlgsem with
	| None -> ()
	| Some fsem ->
	   if !Clflags.option_selftest > 0
	   then 
	     begin
	       (* during test, we need to disable the memoization mechanism *)
	       circ_memo_enable := false;
	       let tcirc = circ_new gc.hlcin
	       and s = subst_new gc.hlcin None in
	       let gout = xpnd_gc_aux g_xpnd_rule tcirc s gc.hlcgates gc.hlcout in
	       (*Printf.printf "%a CIRCUIT = %a\n" gate_pp gate circST_pp tcirc; *)
	       gc_test gate (circ_dump tcirc gout);
	       circ_memo_enable := not !Clflags.option_nomemo;
	     end
	end;
	(* end of self-testing *)
	let gc_circ = gc_xpnd gc in
	let conn' = Timing.time2 " subst AP" subst_ap subst conn in
	let news = subst_new gc_circ.hlcin (Some conn') in
	let gout = xpnd_circ_aux circ news gc_circ.hlcgates gc_circ.hlcout in
	ignore (gArray_add subst (Array.of_list gout));
(*Printf.printf "OUTS = %a\n" hlconn_pp gout;*)
	xpnd_circ_aux circ subst xs outs


let circ_xpnd gc =
  (* initialize memo mechanism... *)
  Hashtbl.reset circ_memo;
  circ_memo_enable := not !Clflags.option_nomemo;
  (* inicialize working circuit and substitution... *)
  let circ = circ_new gc.hlcin in
  let subst = subst_new gc.hlcin None in
(*Printf.printf "initial CIRCUIT = %a\n" circST_pp circ; *)
  (* compute the circuit expansion... *)
  let outc = Timing.time4 "  llcirc generation" xpnd_circ_aux circ subst gc.hlcgates gc.hlcout in
(*Printf.printf "final CIRCUIT = %a\nOUTS = %a\n" circST_pp circ hlconn_pp outc; *)
  (* generate the final circuit *)
  Timing.time2 "  llcirc simplification" circ_dump circ outc



(*
let gate_map g l =
  match g.hlgname, g.hlgargs with
  | _ -> ins_ord_norep hlgate_cmp g l

let proc_entry (gate,conn) l =
  if not (gate.hlgin = List.length conn)
  then fatal_error "gate_in_arity mismatch!"
  else gate_map gate l

let rec proc_circ l =
  match l with
  | [] -> []
  | x::xs -> proc_entry x (proc_circ xs)
 *)

let show_gc_stats circ =
 gc_stats_pp stdout circ

let process_circuit circ =
  let circ = convert_circ circ in
  if !Clflags.option_dllc || !Clflags.option_bristolsmc
  then
    begin
      let llcirc = Timing.time "Low-level circuit (total)" circ_xpnd circ in
      PrintLLCirc.print_if llcirc;
      PrintBristolCirc.print_if llcirc;
      if !Clflags.option_showstats 
      then show_gc_stats llcirc;
      llcirc_unittest_if llcirc
    end

(* processes the first Internal function on the program (should be just 1!) *)
let rec process_globdef l = 
 match l with
 | (_,Gfun(Internal f))::_ -> process_circuit f.fn_code
 | _ :: xs -> process_globdef xs
 | [] -> assert false

let process_program prog =
 process_globdef prog.prog_defs

