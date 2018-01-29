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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import String.
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require RTLC.
Require HLCirc.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require LoopUnroll.
Require RTLgen.
Require Inlining.
Require Renumber.
Require Constprop.
Require CSE.
Require Deadcode.
Require Unusedglob.
(** Proofs of semantic preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require LoopUnrollproof.
Require RTLgenproof.
Require Inliningproof.
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Deadcodeproof.
Require Unusedglobproof.
Require NoNop.
Require Guarded.
Require ConstantExpansion.
Require ValCircGen.
Require HLCircGen.
Require HLCircGenProof.

(** Command-line flags. *)
Require Import Compopts.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: Z -> RTL.program -> unit.
Parameter print_RTLC: Z -> RTLC.program -> unit.
Parameter print_ValCirc: ValCirc.program -> unit.
Parameter print_HLC: HLCirc.program -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

Definition time {A B: Type} (name: string) (f: A -> B) : A -> B := f.

Definition total_if {A: Type}
          (flag: unit -> bool) (f: A -> A) (prog: A) : A :=
  if flag tt then f prog else prog.

Definition partial_if {A: Type}
          (flag: unit -> bool) (f: A -> res A) (prog: A) : res A :=
  if flag tt then f prog else OK prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling. *)

Definition transf_rtl_program (f: RTL.program) : res HLCirc.program :=
   OK f
   @@ print (print_RTL 0)
  @@@ time "Inlining" Inlining.transf_program
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 2)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 3)
   @@ total_if Compopts.optim_constprop (time "Constant propagation" Constprop.transf_program)
   @@ print (print_RTL 4)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL (-1))
   @@ total_if Compopts.optim_constprop (time "Renumbering" Renumber.transf_program)
   @@ print (print_RTL 5)
  @@@ partial_if Compopts.optim_CSE (time "CSE" CSE.transf_program)
   @@ print (print_RTL 6)
  @@@ partial_if Compopts.optim_redundancy (time "Redundancy elimination" Deadcode.transf_program)
   @@ print (print_RTL 7)
  @@@ time "Unused globals" Unusedglob.transform_program
   @@ print (print_RTL 8)
   @@ time "No nop" NoNop.transf_program
   @@ print (print_RTL 9)
   @@ time "Renumbering" Renumber.transf_program
   @@ print (print_RTL 10)
  @@@ time "RTLC generation" Guarded.transf_program
   @@ print (print_RTLC 0)
   @@ total_if Compopts.optim_constexp (time "Constant expansion" ConstantExpansion.transf_program)
   @@ print (print_RTLC 1)
  @@@ time "ValCirc generation" ValCircGen.check_and_translate_program
   @@ print print_ValCirc
  @@@ time "HL Circ generation" HLCircGen.translate_program
   @@ print print_HLC.

Definition transf_cminor_program (p: Cminor.program) : res HLCirc.program :=
   OK p
   @@ print print_Cminor
  @@@ time "Instruction selection" Selection.sel_program
  @@@ time "Loop unrolling" LoopUnroll.unroll_program
(*   @@ print print_CminorUnroll *)
  @@@ time "RTL generation" RTLgen.transl_program
  @@@ transf_rtl_program.

Definition transf_clight_program (p: Clight.program) : res HLCirc.program :=
  OK p
   @@ print print_Clight
  @@@ time "Simplification of locals" SimplLocals.transf_program
  @@@ time "C#minor generation" Cshmgen.transl_program
  @@@ time "Cminor generation" Cminorgen.transl_program
  @@@ transf_cminor_program.

Definition transf_c_program (p: Csyntax.program) : res HLCirc.program :=
  OK p
  @@@ time "Clight generation" SimplExpr.transl_program
  @@@ transf_clight_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto.
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit),
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto.
Qed.

Remark forward_simulation_identity:
  forall sem, forward_simulation sem sem.
Proof.
  intros. apply forward_simulation_step with (fun s1 s2 => s2 = s1); intros.
- auto.
- exists s1; auto.
- subst s2; auto.
- subst s2. exists s1'; auto.
Qed.

Lemma total_if_simulation:
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (f: A -> A) (prog: A),
  (forall p, forward_simulation (sem p) (sem (f p))) ->
  forward_simulation (sem prog) (sem (total_if flag f prog)).
Proof.
  intros. unfold total_if. destruct (flag tt). auto. apply forward_simulation_identity.
Qed.

Lemma partial_if_simulation:
  forall (A: Type) (sem: A -> semantics) (flag: unit -> bool) (f: A -> res A) (prog tprog: A),
  partial_if flag f prog = OK tprog ->
  (forall p tp, f p = OK tp -> forward_simulation (sem p) (sem tp)) ->
  forward_simulation (sem prog) (sem tprog).
Proof.
  intros. unfold partial_if in *. destruct (flag tt). eauto. inv H. apply forward_simulation_identity.
Qed.

(** * Semantic preservation *)

(** We prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Cminor] / [RTL] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Asm]).
- Backward simulation from [Csem] to [Asm]
  (composition of two backward simulations).

These results establish the correctness of the whole compiler! *)

Theorem transf_rtl_program_correct:
  forall p tp,
  transf_rtl_program p = OK tp ->
  forward_simulation (RTL.semantics p) (HLCirc.semantics tp)
  * backward_simulation (RTL.semantics p) (HLCirc.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (RTL.semantics p) (HLCirc.semantics tp)).
  unfold transf_rtl_program, time in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.
  destruct (Inlining.transf_program p) as [p11|] eqn:?; simpl in H; try discriminate.
  apply compose_forward_simulation with (RTL.semantics p11).
    apply Inliningproof.transf_program_correct; auto.
  clear Heqr.
  destruct (Unusedglob.transform_program p11) as [p12|] eqn:?; simpl in H; try discriminate.
  apply compose_forward_simulation with (RTL.semantics p12).
    apply Unusedglobproof.transf_program_correct; auto.
  clear Heqr.

  set (p13 := Renumber.transf_program p12) in *.
  set (p2 := total_if optim_constprop Constprop.transf_program p13) in *.
  destruct (partial_if optim_redundancy Deadcode.transf_program p2) as [p20|] eqn:?; simpl in H; try discriminate.
  set (p21 := total_if optim_constprop Renumber.transf_program p20) in *.
  destruct (partial_if optim_CSE CSE.transf_program p21) as [p3|] eqn:?; simpl in H; try discriminate.
  destruct (partial_if optim_redundancy Deadcode.transf_program p3) as [p31|] eqn:?; simpl in H; try discriminate.
  destruct (Unusedglob.transform_program p31) as [p32|] eqn:?; simpl in H; try discriminate.
  set (p33 := NoNop.transf_program p32) in *.
  set (p34 := Renumber.transf_program p33) in *.
  destruct (Guarded.transf_program p34) as [ p35 | ] eqn: ?; simpl in H; try discriminate.
  set (p36 := total_if optim_constexp ConstantExpansion.transf_program p35) in *.
  destruct (ValCircGen.check_and_translate_program p36) as [ p37 | ] eqn: ?; simpl in H; try discriminate.

  apply compose_forward_simulation with (RTL.semantics p13).
    apply Renumberproof.transf_program_correct.
  apply compose_forward_simulation with (RTL.semantics p2).
    apply total_if_simulation. apply Constpropproof.transf_program_correct.
  apply compose_forward_simulation with (RTL.semantics p20).
    eapply partial_if_simulation; eauto. apply Deadcodeproof.transf_program_correct.
  apply compose_forward_simulation with (RTL.semantics p21).
    apply total_if_simulation. apply Renumberproof.transf_program_correct.
  apply compose_forward_simulation with (RTL.semantics p3).
    eapply partial_if_simulation; eauto.  apply CSEproof.transf_program_correct.  apply compose_forward_simulation with (RTL.semantics p31).
    eapply partial_if_simulation; eauto. apply Deadcodeproof.transf_program_correct.
  apply compose_forward_simulation with (RTL.semantics p32).
    inv H; apply Unusedglobproof.transf_program_correct; auto.
  apply compose_forward_simulation with (RTL.semantics p33).
    apply NoNop.simulation.
  apply compose_forward_simulation with (RTL.semantics p34).
    apply Renumberproof.transf_program_correct.
  apply compose_forward_simulation with (RTLC.semantics p35).
    apply Guarded.simulation; auto.
  apply compose_forward_simulation with (RTLC.semantics p36).
    apply total_if_simulation. apply ConstantExpansion.simulation; auto.
  apply compose_forward_simulation with (ValCirc.semantics p37).
    apply ValCircGen.simulation_with_check; auto.
    apply HLCircGenProof.simulation; auto.

  split. auto.
  apply forward_to_backward_simulation. auto.
  apply RTL.semantics_receptive.
  apply HLCirc.semantics_determinate.
Qed.

Theorem transf_cminor_program_correct:
  forall p tp,
  transf_cminor_program p = OK tp ->
  forward_simulation (Cminor.semantics p) (HLCirc.semantics tp)
  * backward_simulation (Cminor.semantics p) (HLCirc.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cminor.semantics p) (HLCirc.semantics tp)).
  unfold transf_cminor_program, time in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.
  destruct (Selection.sel_program p) as [p1|] eqn:?; simpl in H; try discriminate.
  destruct (LoopUnroll.unroll_program p1) as [p1'|] eqn:?; simpl in H; try discriminate.
  destruct (RTLgen.transl_program p1') as [p2|] eqn:?; simpl in H; try discriminate.
  eapply compose_forward_simulation. apply Selectionproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply LoopUnrollproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply RTLgenproof.transf_program_correct. eassumption.
  exact (fst (transf_rtl_program_correct _ _ H)).

  split. auto.
  apply forward_to_backward_simulation. auto.
  apply Cminor.semantics_receptive.
  apply HLCirc.semantics_determinate.
Qed.

Theorem transf_clight_program_correct:
  forall p tp,
  transf_clight_program p = OK tp ->
  forward_simulation (Clight.semantics1 p) (HLCirc.semantics tp)
  * backward_simulation (Clight.semantics1 p) (HLCirc.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Clight.semantics1 p) (HLCirc.semantics tp)).
  revert H; unfold transf_clight_program, time; simpl.
  rewrite print_identity.
  caseEq (SimplLocals.transf_program p); simpl; try congruence; intros p0 EQ0.
  caseEq (Cshmgen.transl_program p0); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply SimplLocalsproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_program_correct _ _ EQ3)).

  split. auto.
  apply forward_to_backward_simulation. auto.
  apply Clight.semantics_receptive.
  apply HLCirc.semantics_determinate.
Qed.

Theorem transf_cstrategy_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (HLCirc.semantics tp)
  * backward_simulation (atomic (Cstrategy.semantics p)) (HLCirc.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cstrategy.semantics p) (HLCirc.semantics tp)).
  revert H; unfold transf_c_program, time; simpl.
  caseEq (SimplExpr.transl_program p); simpl; try congruence; intros p0 EQ0.
  intros EQ1.
  eapply compose_forward_simulation. apply SimplExprproof.transl_program_correct. eauto.
  exact (fst (transf_clight_program_correct _ _ EQ1)).

  split. auto.
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. 
  apply HLCirc.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply HLCirc.semantics_determinate.
Qed.

Theorem transf_c_program_correct:
  forall p tp,
  transf_c_program p = OK tp ->
  backward_simulation (Csem.semantics p) (HLCirc.semantics tp).
Proof.
  intros.
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces.
  apply HLCirc.semantics_determinate.
  apply factor_backward_simulation.
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (snd (transf_cstrategy_program_correct _ _ H)).
Qed.
