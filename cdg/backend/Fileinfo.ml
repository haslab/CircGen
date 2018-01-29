(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*          Bernhard Schommer, AbsInt Angewandte Informatik GmbH       *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

open Printf

(* Printing annotations in asm syntax *)

let filename_info : (string, int * Printlines.filebuf option) Hashtbl.t
                  = Hashtbl.create 7

let last_file = ref ""

let reset_filenames () =
  Hashtbl.clear filename_info; last_file := ""

let close_filenames () =
  Hashtbl.iter
    (fun file (num, fb) ->
       match fb with Some b -> Printlines.close b | None -> ())
    filename_info;
  reset_filenames()

let enter_filename f =
  let num = Hashtbl.length filename_info + 1 in
  let filebuf = None in
  Hashtbl.add filename_info f (num, filebuf);
  (num, filebuf)

(* Add file and line debug location, using GNU assembler-style DWARF2
   directives *)
let print_file oc file =
  try
    Hashtbl.find filename_info file
  with Not_found ->
    let (filenum, filebuf as res) = enter_filename file in
    fprintf oc "	.file	%d %S\n" filenum file;
    res

let print_file_line oc pref file line = ()

(* Add file and line debug location, using DWARF2 directives in the style
   of Diab C 5 *)

let print_file_line_d2 oc pref file line = ()
