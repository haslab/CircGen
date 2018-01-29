(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printers for HLCirc code *)


open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open Integers

open ORbdt
open OpGates


(** Printing of Gates 

 GNAME(args)[out_arity]
*)

let rec str_of_list x_str  = function
  | [] -> assert false
  | [x] -> x_str x
  | (x::xs) -> sprintf "%s,%s" (x_str x) (str_of_list x_str xs)


let rec pcond_str bdd =
 match bdd with
 | Leaf s -> if Obj.magic s then "T" else "F"
 | Node (v, Leaf b1, Leaf b2) ->
    if Obj.magic b1
    then sprintf "%d" (P.to_int v)
    else sprintf "~%d" (P.to_int v)
 | Node (v, Leaf b1, r) ->
    if Obj.magic b1
    then sprintf "(%d + %s)" (P.to_int v) (pcond_str r)
    else sprintf "~%d & %s" (P.to_int v) (pcond_str r)
 | Node (v, l, Leaf b2) ->
    if Obj.magic b2
    then sprintf "(~%d + %s)" (P.to_int v) (pcond_str l)
    else sprintf "%d & %s" (P.to_int v) (pcond_str l)
 | Node (v,l,r) -> sprintf "(%d & %s + ~%d & %s)" (P.to_int v) (pcond_str l) (P.to_int v) (pcond_str r)

let rec gate_str = function
| G_AND -> "AND"
| G_XOR -> "XOR"
| Geq32 -> "eq32"
| Gneq32 -> "neq32"
| Gslt32 -> "slt32"
| Gsle32 -> "sle32"
| Gsgt32 -> "sgt32"
| Gsge32 -> "sge32"
| Gult32 -> "ult32"
| Gule32 -> "ule32"
| Gugt32 -> "ugt32"
| Guge32 -> "uge32"
| Geq32i n -> sprintf "eq32i(%ld)" (camlint_of_coqint n)
| Gneq32i n -> sprintf "neq32i(%ld)" (camlint_of_coqint n)
| Gslt32i n -> sprintf "slt32i(%ld)" (camlint_of_coqint n)
| Gsle32i n -> sprintf "sle32i(%ld)" (camlint_of_coqint n)
| Gsgt32i n -> sprintf "sgt32i(%ld)" (camlint_of_coqint n)
| Gsge32i n -> sprintf "sge32i(%ld)" (camlint_of_coqint n)
| Gult32i n -> sprintf "ult32i(%ld)" (camlint_of_coqint n)
| Gule32i n -> sprintf "ule32i(%ld)" (camlint_of_coqint n)
| Gugt32i n -> sprintf "ugt32i(%ld)" (camlint_of_coqint n)
| Guge32i n -> sprintf "uge32i(%ld)" (camlint_of_coqint n)
| Gmaskzero n -> "maskzero"
| Gnotmaskzero n -> "notmakszero"
| Gconst32 n -> sprintf "const32(%ld)" (camlint_of_coqint n)
| Gsint_cast n -> sprintf "sint_cast(%ld)" (N.to_int32 n)
| Guint_cast n -> sprintf "uint_cast(%ld)" (N.to_int32 n)
| Gadd32 -> "add32"
| Gadd32i n -> sprintf "add32i(%ld)" (camlint_of_coqint n)
| Gaddadd32i n -> sprintf "addadd32i(%ld)" (camlint_of_coqint n)
| Gmuladd32i (n1,n2) -> sprintf "muladd32i(%ld,%ld)" (camlint_of_coqint n1) (camlint_of_coqint n2)
| Gmuladdadd32i (n1,n2) -> sprintf "muladdadd32i(%ld,%ld)" (camlint_of_coqint n1) (camlint_of_coqint n2)
| Gneg32 -> "neg32"
| Gsub32 -> "sub32"
| Gmul32 -> "mul32"
| Gmul32i n -> sprintf "mul32i(%ld)" (camlint_of_coqint n)
| Gmulhs -> "mulhs"
| Gmulhu -> "mulhu"
| Gand32 -> "and32"
| Gand32i n -> sprintf "and32i(%ld)" (camlint_of_coqint n)
| Gor32 -> "or32"
| Gor32i n -> sprintf "or32i(%ld)" (camlint_of_coqint n)
| Gxor32 -> "xor32"
| Gxor32i n -> sprintf "xor32i(%ld)" (camlint_of_coqint n)
| Gnot32 -> "not32"
| Gshl32 -> "shl32"
| Gshl32i n -> sprintf "shl32i(%ld)" (camlint_of_coqint n)
| Gshr32 -> "shr32"
| Gshr32i n -> sprintf "shr32i(%ld)" (camlint_of_coqint n)
| Gshrx32i n -> sprintf "shrx32i(%ld)" (camlint_of_coqint n)
| Gshru32 -> "shru32"
| Gshru32i n -> sprintf "shru32i(%ld)" (camlint_of_coqint n)
| Gror32i n -> sprintf "ror32i(%ld)" (camlint_of_coqint n)
| Gshld32i n -> sprintf "shld32i(%ld)" (camlint_of_coqint n)
| Gint64 -> "int64"
| Gint64low -> "int64low"
| Gint64hi -> "int64hi"
| Gid n -> sprintf "id(%ld)" (N.to_int32 n)
| Gcmp_uint g -> sprintf "cmp_%s" (gate_str g)
| Gcond -> "cond"
| GxorN n -> sprintf "xorN(%ld)" (N.to_int32 n)
| GcondN n -> sprintf "condN(%ld)" (N.to_int32 n)
| GbarrierN n -> sprintf "barrierN(%ld)" (N.to_int32 n)
| Gconstbytes l -> sprintf "constbytes(%s)" (str_of_list (fun x->sprintf "%ld" (camlint_of_coqint x)) l)
| Gguard cond -> sprintf "guard(%s)" (pcond_str cond)
| Gselk ((size,width),ofs) -> sprintf "selk(%d,%d,%d)" (N.to_int size) (N.to_int width) (N.to_int ofs)
| Gdsel (size,width) -> sprintf "dsel(%d,%d)" (N.to_int size) (N.to_int width)
| Gsel (size,width) -> sprintf "sel(%d,%d)" (N.to_int size) (N.to_int width)
| Gupdk ((size,width),ofs) -> sprintf "updk(%d,%d,%d)" (N.to_int size) (N.to_int width) (N.to_int ofs)
| Gdupd (size,width) -> sprintf "dupd(%d,%d)" (N.to_int size) (N.to_int width)
| Gupd (size,width) -> sprintf "upd(%d,%d)" (N.to_int size) (N.to_int width)


let gate_pp pp gate =
  fprintf pp "%s[%d]"
	  (gate_str gate)
          (N.to_int (gateInfo gate).gate_out_arity)


(*


(** Printing of Conn *)


(* (gate,start,n) denotes:

   1) gate=0 : repetition of truth-value wire (e.g. (0,1,32) is wire_TT (0,1)
 repeated 32 times;
   2) gate>0 : sequential wires in gate (e.g. (3,0,32) denotes [(3,0), (3,1), ...]
 *)
let rec groupConn gate start n conn =
 match conn with
 | [] -> if n=0 then [] else [(gate,start,n)]
 | (g,w)::xs -> if n = 0
                then groupConn (N.to_int g) (N.to_int w) 1 xs
                else (if (N.to_int g = gate
                          && (if gate = 0
			      then N.to_int w = start
			      else N.to_int w = start+n))
                      then groupConn gate start (n+1) xs
                      else (gate,start,n)::groupConn (N.to_int g) (N.to_int w) 1 xs)
(*
if (N.to_int g,N.to_int w) = (gate,start+n)
                     then groupConn gate start (n+1) xs
		     else (gate,start,n)::groupConn (N.to_int g) (N.to_int w) 1 xs
 *)

let gconn_pp pp = function
  | (gate,start,n) ->
      if gate = 0
      then
	begin
	  assert (start=0 || start = 1);
          if start = 0
	  then if n = 1
	       then fprintf pp "FF"
	       else fprintf pp "FF*%d" n
	  else if n = 1
	       then fprintf pp "TT"
	       else fprintf pp "TT*%d" n
	end
      else if n = 1
           then fprintf pp "(%d,%d)" gate start
           else fprintf pp "(%d,%d..%d)" gate start (start+n-1)

let rec gconnL_pp pp = function
  | [] -> ()
  | [x] -> gconn_pp pp x
  | x::xs -> fprintf pp "%a;%a" gconn_pp x gconnL_pp xs

let conn_pp pp conn = fprintf pp "[%a]" gconnL_pp (groupConn 0 0 0 conn)

(** Printing of GEntry

 n: GATE(args)[oarity] <- connector
*)

let gentry_pp pp gentry n =
 if (N.to_int gentry.gate.gate_in_arity != List.length gentry.conn);
 then (fprintf stderr "Mismatch on gate (%a@%d) input arity\n" gate_pp gentry.gate n;
       fprintf stderr "%d != %d\n" (N.to_int gentry.gate.gate_in_arity) (List.length gentry.conn);
       assert ((*true||*) false));
 fprintf pp "%3d : %a <- %a\n"
	 n gate_pp gentry.gate conn_pp gentry.conn

let rec gentryL_pp pp n = function
  | [] -> ()
  | (x::xs) -> gentry_pp pp x n; gentryL_pp pp (n+1) xs

(** Printing of Inputs *)

let rec inputs_pp pp n = function
  | [] -> ()
  | (x::xs) -> fprintf pp "%3d : %d-wire INPUT\n" n (8*N.to_int x); inputs_pp pp (n+1) xs

(** Printing of Outputs *)

let outputs_pp pp conn =
  fprintf pp "OUTPUT = %a\n" conn_pp conn


(** Printing of Circuit *)

let circuit_pp pp circ =
 inputs_pp pp 1 circ.inputs;
 gentryL_pp pp (List.length circ.inputs + 1) circ.gates;
 outputs_pp pp circ.outputs
 



let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      circuit_pp oc prog;
      close_out oc

 *)
