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

(* Command-line flags *)

let prepro_options = ref ([]: string list)
let linker_options = ref ([]: string list)
let assembler_options = ref ([]: string list)
let option_flongdouble = ref false
let option_fstruct_passing = ref false
let option_fbitfields = ref false
let option_fvararg_calls = ref true
let option_funprototyped = ref true
let option_fpacked_structs = ref false
let option_ffpu = ref true
let option_ffloatconstprop = ref 2
let option_floop_unroll = ref 0
let option_floop_unroll_infer = ref false
let pragma_loop_unroll = ref (None: (int list) option)
let option_fconstprop = ref true
let option_fcse = ref true
let option_fredundancy = ref true
let option_falignfunctions = ref (None: int option)
let option_falignbranchtargets = ref 0
let option_faligncondbranchs = ref 0
let option_finline_asm = ref false
(*let option_mthumb = ref (Configuration.model = "armv7m")*)
let option_Osize = ref false
let option_dparse = ref false
let option_dcmedium = ref false
let option_dclight = ref false
let option_dcminor = ref false
let option_drtl = ref false
let option_drtl = ref false
let option_fce = ref false

(* Outputs RTLC intermediate language *)
let option_drtlc = ref false
let option_dvalcirc = ref false

(* Outputs high-level in standard format *)
let option_dhlc = ref false

(* Outputs low-level in standard format *)
let option_dllc = ref false

(* Outputs low-level in bristol SMC format *)
let option_bristolsmc = ref false

(* Number of inputs *)
let option_p1inputs = ref 0

(* Show statistics *)
let option_showstats = ref false

(* Disable constant expansion *)
let option_noxpnd = ref false

(* Disable memoization *)
let option_nomemo = ref false

(* Disable gate simplification *)
let option_nosimpl = ref false

(* Random-testing generated gate circuits *)
let option_selftest = ref 0

(* Unit-testing generated circuit *)
let option_unittest = ref false

(* Debug level *)
let option_dbglevel = ref 0

let option_g = ref false
let option_gdwarf = ref 2
let option_gdepth = ref 3
let option_o = ref (None: string option)
let option_E = ref false
let option_S = ref false
let option_c = ref false
let option_v = ref false
let option_interp = ref false
let option_small_data =
  ref 0 (*(if Configuration.arch = "powerpc"
       && Configuration.abi = "eabi"
       && Configuration.system = "diab"
       then 8 else 0)*)
let option_small_const = ref (!option_small_data)
let option_timings = ref false
let option_rename_static = ref false
