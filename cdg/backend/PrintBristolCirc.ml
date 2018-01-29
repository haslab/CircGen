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

(** Pretty-printers for LLCirc code *)


open Printf
open Camlcoq
open Mlcirc

let destination : string option ref = ref None

let list_init n f =
  Array.to_list (Array.init n f)

(* Concersion to BRISTOL SMC format 

  - add FALSE and TRUE gates
  - readjust indexes
  - add output gates (XOR 0 out)
*)
let g_INV = mkhlgate "INV" [] 1 1

let ll_to_bristol circ =
  let bcirc = gArray_init ()
  and (subst:subst) = gArray_init () 
  and ninps = gc_input_wires circ in
  let bpos () = ninps+bcirc.gAsize-1 in
(*  and bconn l = List.map (fun g->g,0) l in*)
  (* FALSE and TRUE gates *)
  gArray_add bcirc (g_XOR, [(0,0);(0,0)]);
  gArray_add bcirc (g_INV, [(ninps,0)]);
  gArray_add subst (Array.of_list [(ninps,0); (ninps+1,0)]);
  (* inputs wires *)
  List.iter (fun l -> gArray_add subst (Array.of_list l); ())
	    (split_sizes circ.hlcin (list_init ninps (fun x->(x,0))));
  List.iter (fun (g,c) -> gArray_add bcirc (g,(*bconn*) (subst_ap subst c));
			  gArray_add subst (Array.of_list [bpos (),0]); ()) circ.hlcgates;
  List.iter (fun o -> gArray_add bcirc (g_XOR,(ninps,0)::(*bconn*) (subst_ap subst [o])); ())
	    circ.hlcout;
  { hlcin = list_init ninps (fun x->1)
  ; hlcgates =
      begin
	let acc = ref [] in
        for i = bcirc.gAsize-1 downto 0 do
	  acc := gArray_get bcirc i :: !acc
	done;
	!acc
      end
  ; hlcout = let nouts = gc_output_wires circ in
	     list_init nouts (fun x -> bcirc.gAsize - nouts + x, 0)
  }
		      
  
  

(* pretty-printing BRISTOL SMC format 

 - n_gates n_wires
 - ninput1 ninput2 nout
 - (blank)
 - gates (gin gout i1 i2 .. o1 NAME)
*)
let bristol_pp pp circ =
  let ninps = gc_input_wires circ 
  and p1inps = !Clflags.option_p1inputs
  and nouts = gc_output_wires circ 
  and ngates = List.length circ.hlcgates in
  if p1inps > ninps || p1inps < 0
  then fatal_error (msg "not enough inputs for Party 1 (%d < %d)"
			ninps p1inps);
  (* PREAMBLE *)
  Printf.fprintf pp "%d %d\n" ngates (ninps+ngates);
  Printf.fprintf pp "%d %d  %d\n\n" (ninps-p1inps) p1inps nouts;
  (* GATES *)  
  List.iteri (fun n (g,c) -> Printf.fprintf pp "%d %d %a %d %s\n"
					    g.hlgin g.hlgout
					    (list_pp " "
						     (fun pp (i,_)->
						       Printf.fprintf pp "%d"
								      i)) c
					    (ninps+n) g.hlgname)
	     circ.hlcgates
      

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
     let bcirc = Timing.time "Bristol-SMC format translation" ll_to_bristol prog
     and oc = open_out f in
     bristol_pp oc bcirc;
     close_out oc

