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

(** Pretty-printers for RTL code *)

open Printf
open Camlcoq
open Datatypes
open Maps
open AST
open Integers
open RTL
open PrintAST
open PrintOp

open Globalenvs

open RTLC
open ORbdt

(** Printing of PhiNodes (for debugging) *)

let rec fprint_phi pp phi =
 match phi with
 | Leaf x -> begin match Obj.magic x with
             | (i,None) -> Printf.fprintf pp "%d" (Camlcoq.P.to_int i)
             | (i,Some _) -> Printf.fprintf pp "K%d" (Camlcoq.P.to_int i)
             | _ -> assert false
             end
 | Node (v,l,r) -> Printf.fprintf pp "(%d?%a:%a)" (Camlcoq.P.to_int v) fprint_phi l fprint_phi r

let print_phi phi = Printf.printf "φ="; fprint_phi stdout phi

let dbg_phi phi = print_phi phi; Printf.printf "\n"; phi

(** Printing of Path-Conditions *)

let rec pcond_pp pp bdd =
 match bdd with
 | Leaf s -> fprintf pp (if Obj.magic s then "T" else "F")
 | Node (v,l,r) -> fprintf pp "(%d?%a:%a)" (P.to_int v) pcond_pp l pcond_pp r
(*
 match bdd with
 | Leaf true -> fprintf pp "T"
 | Leaf false -> fprintf pp "F"
 | Node (v,l,r) -> fprintf pp "(%d?%a:%a)" (P.to_int v) pcond_pp l pcond_pp r
 *)

let rec pcond2_pp pp bdd =
 match bdd with
 | Leaf s -> fprintf pp (if Obj.magic s then "T" else "F")
 | Node (v, Leaf b1, Leaf b2) ->
    if Obj.magic b1
    then fprintf pp "%d" (P.to_int v)
    else fprintf pp "~%d" (P.to_int v)
 | Node (v, Leaf b1, r) ->
    if Obj.magic b1
    then fprintf pp "(%d + %a)" (P.to_int v) pcond2_pp r
    else fprintf pp "~%d & %a" (P.to_int v) pcond2_pp r
 | Node (v, l, Leaf b2) ->
    if Obj.magic b2
    then fprintf pp "(~%d + %a)" (P.to_int v) pcond2_pp l
    else fprintf pp "%d & %a" (P.to_int v) pcond2_pp l
 | Node (v,l,r) -> fprintf pp "(%d & %a + ~%d & %a)" (P.to_int v) pcond2_pp l (P.to_int v) pcond2_pp r

(* Printing of RTLC code *)

let regcond pp r =
  fprintf pp "b%d" (P.to_int r)

let reg pp r =
  fprintf pp "x%d" (P.to_int r)

let rec regs pp = function
  | [] -> ()
  | [r] -> reg pp r
  | r1::rl -> fprintf pp "%a, %a" reg r1 regs rl

let ros pp = function
  | Coq_inl r -> reg pp r
  | Coq_inr s -> fprintf pp "\"%s\"" (extern_atom s)

let print_succ pp s dfl =
  let s = P.to_int s in
  if s <> dfl then fprintf pp "\tgoto %d\n" s

let rec print_phi pp = function
  | [] -> ()
  | [(c,r)] -> fprintf pp "%a: %a" pcond2_pp c reg r
  | ((c,r)::l) -> fprintf pp "%a: %a, %a" pcond2_pp c reg r print_phi l

let print_instruction pp (pc, i) =
  (match i with
  | Itest(b,cond,args) -> fprintf pp "test %a = %a" regcond b
		 		  (PrintOp.print_condition reg) (cond,args)
(*
  | Ictest(b,pc') -> fprintf pp "ctest %a == %a" regcond b
		 	    pcond2_pp pc'
  | Iphi(v,l) -> fprintf pp "%a = φ(%a)" reg v print_phi l
 *)
  | Iop(op, args, res) ->
      fprintf pp "%a = %a"
         reg res (PrintOp.print_operation reg) (op, args)
  | Iload(chunk, addr, args, dst) ->
      fprintf pp "%a = %s[%a]"
         reg dst (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
  | Istore(chunk, addr, args, src) ->
      fprintf pp "%s[%a] = %a"
         (name_of_chunk chunk)
         (PrintOp.print_addressing reg) (addr, args)
         reg src
(*
  | Ihalt -> fprintf pp "HALT"
  | Ibuiltin(ef, args, res) ->
      fprintf pp "%a = %s(%a)\n"
        (print_builtin_res reg) res
        (name_of_external ef)
        (print_builtin_args reg) args
 *)
  ); fprintf pp " | %a\n" pcond_pp pc

let print_global pp ((x, o), _) =
  fprintf pp "%s[%d] " (extern_atom x) (Camlcoq.Z.to_int o)

let print_globals pp =
  List.iter (print_global pp)

let print_function pp id f =
  fprintf pp "%s() {\n" (extern_atom id)(* regs f.fn_params*);
  fprintf pp "INPUTS: %a\n" print_globals f.fn_inputs;
  fprintf pp "OUTPUTS: %a\n\n" print_globals f.fn_outputs;
  List.iter (print_instruction pp) f.fn_code;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | Gvar(gv) -> let sz = camlint_of_coqint (Globalenvs.Genv.size_globvar gv)
                in
(*		fprintf pp "GVAR %s[%ld]\n" (extern_atom id) sz;*)
		add_globvar_size id sz
  | _ -> ()

let print_program pp (prog: RTLC.program) =
  reset_globvar_sizes;
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if passno prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out (f ^ "." ^ Z.to_string passno) in
      print_program oc prog;
      close_out oc

