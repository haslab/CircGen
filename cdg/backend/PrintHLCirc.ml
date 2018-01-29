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

open OpGates
open HLCirc

open PrintGates

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
 if (N.to_int (gateInfo gentry.gate).gate_in_arity != List.length gentry.conn);
 then (fprintf stderr "Mismatch on gate (%a@%d) input arity\n" gate_pp gentry.gate n;
       fprintf stderr "%d != %d\n" (N.to_int (gateInfo gentry.gate).gate_in_arity) (List.length gentry.conn);
       assert ((*true||*) false));
 fprintf pp "%3d : %a <- %a\n"
	 n gate_pp gentry.gate conn_pp gentry.conn

let rec gentryL_pp pp n = function
  | [] -> ()
  | (x::xs) -> gentry_pp pp x n; gentryL_pp pp (n+1) xs

(** Printing of Globals *)

let rec intlist_pp pp = function
  | [] -> ()
  | [x] -> fprintf pp "%0lx" (Camlcoq.Z.to_int32 x)
  | (x::xs) -> fprintf pp "%0lx," (Camlcoq.Z.to_int32 x);
	       intlist_pp pp xs

let rec globv_pp pp n = function
  | [] -> ()
  | (x::xs) -> fprintf pp "%3d : %d-bit GLOBAL - [%a]\n"
		       n (8*(List.length x)) intlist_pp x;
	       globv_pp pp (n+1) xs

(** Printing of Outputs *)

let outputs_pp pp conn =
  fprintf pp "OUTPUT = %a\n" conn_pp conn


(** Printing of Circuit *)
let circuit_pp pp circ =
 fprintf pp "%3d : %d-wire INPUT\n" 1 (N.to_int circ.inputs);
 globv_pp pp 2 circ.initconsts;
 gentryL_pp pp (List.length circ.initconsts + 2) circ.gates;
 outputs_pp pp circ.outputs


let print_function pp id f =
  fprintf pp "%s() {\n" (extern_atom id)(* regs f.fn_params*);
(*
  fprintf pp "INPUTS: %a\n" print_globals f.fn_inputs;
  fprintf pp "OUTPUTS: %a\n\n" print_globals f.fn_outputs;
  GLOBVARS:
 *)
  circuit_pp pp f.fn_code;
  fprintf pp "}\n\n"


let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | _ -> ()

let print_program pp (prog: HLCirc.program) =
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program oc prog;
      close_out oc

