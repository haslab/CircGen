(** BoolCircuit.v - Low-level boolean circuits

 Low-level boolean circuits are described directly at the "wire-level"
 with elementary gates (such as AND, XOR, etc.).
 The circuit pattern is similar (but simpler) to high-level circuits:

 0: INPUT					| INPUT SECTION
 ...						-------
 n: <elem-op> [ <wire1> ; <wire2> ]		| GATE SECTION
 ...						-------
 m: OUTPUT <wire>				| OUPUT SECTION
 ...

Each elementary gate (op) has a fixed in-arity (often 2), and a single
output wire. Output wires are replicated at the end of the circuit
description.
*)

Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype tuple.
Require Import BinPos.

Inductive ElemGate :=
 | egate_T : ElemGate
 | egate_F : ElemGate
 | egate_INV : N -> ElemGate
 | egate_AND : N -> N -> ElemGate
 | egate_XOR : N -> N -> ElemGate.

Record LLCircuit := { ll_inputs: N
                    ; ll_gates: seq ElemGate
                    ; ll_outputs: seq N
                    }.
