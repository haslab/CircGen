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

(** Loop-unrolling. *)

Require Import Coqlib.
Require Import Errors.
Require Import Maps.
Require Import Compopts.
Require Import AST.
Require Import Integers.
Require Import Globalenvs.
Require Import Switch.
Require Import Op.
Require Import Registers.
Require Cminor.
Require Import CminorSel.
Require Compopts.

Local Open Scope error_monad_scope.

(** * iterated sequence *)

Fixpoint iterseq (count: nat) (s1 s2:stmt) : stmt :=
 match count with
 | 0%nat => s2
 | S n => Sseq s1 (iterseq n s1 s2)
 end.


(** * Loop-unrolling

We perform loop-unrolling based on an external oracle that assigns
the number of loop-unfolds for each loop. The transformation fails
whenever one attempts to unfold a loop whose body has any label (but
succeeds if the oracle leave those loop untouched).
*)

Definition unroll_flag n := andb (NPeano.Nat.eqb n O).

Fixpoint unroll_stmt b (guess: positive -> nat) (s: stmt) (pos:positive): res stmt:=
  match s with
  | Sseq s1 s2 => do s1' <- unroll_stmt b guess s1 (xO pos);
                  do s2' <- unroll_stmt b guess s2 (xI pos);
                  OK (Sseq s1' s2')
  | Sifthenelse c s1 s2 => do s1' <- unroll_stmt b guess s1 (xO pos);
                           do s2' <- unroll_stmt b guess s2 (xI pos);
                           OK (Sifthenelse c s1' s2')
  | Sloop s => let guess_pos := guess pos in
               do s' <- unroll_stmt (unroll_flag guess_pos b) guess s (xO pos);
               OK (iterseq guess_pos s' (Sloop s'))
  | Sblock s => do s' <- unroll_stmt b guess s pos;
                OK (Sblock s')
  | Slabel i s => if b
                  then (do s' <- unroll_stmt b guess s pos;
                        OK (Slabel i s'))
                  else Error (msg "LoopUnroll: trying to unfold loop body with labels")
  | _ => OK s
  end.

(* [optim_loop_unroll_estimates] is the external oracle that assigns the
  number of unfolds for each loop (declared in [Compopts.v])             *)

Definition unroll_function (ge: genv) (f: function) : res function :=
  do body' <- unroll_stmt true (optim_loop_unroll_estimates f.(fn_body))
                          f.(fn_body) xH;
  OK (mkfunction
        f.(fn_sig)
        f.(fn_params)
        f.(fn_vars)
        f.(fn_stackspace)
        body').

Definition unroll_fundef (ge: genv) (f: fundef) : res fundef :=
  transf_partial_fundef (unroll_function ge) f.

(** Conversion of programs. *)

Definition unroll_program (p: program) : res program :=
  let ge := Genv.globalenv p in
  transform_partial_program (unroll_fundef ge) p.

