(** Pretty-printers for ValCirc code *)

open Printf
open Camlcoq
open AST
open PrintAST
open ORbdt
open ValCirc

let reg pp n =
  fprintf pp "w%d" (N.to_int n)

let rec fprint_phi pp =
  function
  | Leaf x -> begin match Obj.magic x with
      | None -> Printf.fprintf pp "⊥"
      | Some i -> Printf.fprintf pp "w%d" (Camlcoq.P.to_int i - 1)
    end
  | Node (v,l,r) -> Printf.fprintf pp "(c%d?%a:%a)" (Camlcoq.P.to_int v) fprint_phi l fprint_phi r

let print_gate pp args =
  function
  | Gop op -> fprintf pp "%a\n" (PrintOp.print_operation reg) (op, args)
  | Gload (ch, ad) ->
    fprintf pp "%s[%a]\n"
      (name_of_chunk ch)
      (PrintOp.print_addressing reg) (ad, args);
  | Gstore (g, ch, ad) ->
    let src :: args = args in
    fprintf pp "<%a>: %s[%a] := %a\n"
      PrintRTLC.pcond_pp g
      (name_of_chunk ch)
      (PrintOp.print_addressing reg) (ad, args)
      reg src
  | Gtest (g, cnd) ->
     fprintf pp "<%a>: %a\n"
             PrintRTLC.pcond_pp g
             (PrintOp.print_condition reg) (cnd, args)
  | G__U03c6_ ph -> fprintf pp "%a\n" fprint_phi ph

let print_gentry pp n { ggate ; gwires } =
  fprintf pp "%4d: " n;
  print_gate pp gwires ggate

let print_cw pp cw =
  Maps.PTree.elements cw |>
  List.sort (fun (x, _) (y, _) -> compare (P.to_int x) (P.to_int y)) |>
  List.iter (fun (x, y) -> fprintf pp "[%d ⟼ %d]" (P.to_int y) (P.to_int x - 1))

let print_globals = PrintRTLC.print_globals

let print_function pp id f =
  fprintf pp "%s() {\n" (extern_atom id);
  fprintf pp "INPUTS: %a\n" print_globals f.fn_inputs;
  fprintf pp "OUTPUTS: %a\n" print_globals f.fn_outputs;
  fprintf pp "Conditions: %a\n\n" print_cw f.fn_conditions;
  List.iteri (print_gentry pp) f.fn_body;
  fprintf pp "}\n\n"

let print_globdef pp (id, gd) =
  match gd with
  | Gfun(Internal f) -> print_function pp id f
  | Gvar(gv) -> let sz = camlint_of_coqint (Globalenvs.Genv.size_globvar gv)
    in
    (* fprintf pp "GVAR %s[%ld]\n" (extern_atom id) sz; *)
    add_globvar_size id sz
  | _ -> ()

let print_program pp (prog: ValCirc.program) =
  reset_globvar_sizes;
  List.iter (print_globdef pp) prog.prog_defs

let destination : string option ref = ref None

let print_if prog =
  match !destination with
  | None -> ()
  | Some f ->
    let oc = open_out f in
    print_program oc prog;
    close_out oc
