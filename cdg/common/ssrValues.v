Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple.


Require Import Coqlib ssrlib.

Require Intv.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Values.
Require Import Memtype.
Require Import Memory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(** [eqType] canonical structures for some compcert types *)
Canonical Structure ident_eqMixin := EqMixin zint.eqpP.
Canonical Structure ident_eqType := Eval hnf in @EqType ident ident_eqMixin.

Canonical Structure block_eqMixin := EqMixin zint.eqpP.
Canonical Structure block_eqType := Eval hnf in @EqType block block_eqMixin.

(* value types *)

Canonical Structure byte_eqMixin := EqMixin (EqDecEqAxiom Byte.eq_dec).
Canonical Structure byte_eqType := Eval hnf in @EqType byte byte_eqMixin.

Canonical Structure int_eqMixin := EqMixin (EqDecEqAxiom Int.eq_dec).
Canonical Structure int_eqType := Eval hnf in @EqType int int_eqMixin.

Canonical Structure int64_eqMixin := EqMixin (EqDecEqAxiom Int64.eq_dec).
Canonical Structure int64_eqType := Eval hnf in @EqType int64 int64_eqMixin.

Canonical Structure float_eqMixin := EqMixin (EqDecEqAxiom Float.eq_dec).
Canonical Structure float_eqType := Eval hnf in @EqType float float_eqMixin.

Definition val_eq (x y: val) : {x=y} + {x<>y}.
generalize Int.eq_dec Int64.eq_dec (*int128.eq_dec*) Float32.eq_dec Float.eq_dec eq_block.
decide equality.
Defined.
Global Opaque val_eq.

Canonical Structure val_eqMixin := EqMixin (EqDecEqAxiom val_eq).
Canonical Structure val_eqType := Eval hnf in @EqType val val_eqMixin.

Corollary val_eq_refl: forall (x:val), x == x = true.
Proof. apply eq_refl. Qed.

Definition quantity_eq: forall (x y: quantity), {x=y}+{x<>y}.
refine (fun x y => match x, y with Q32, Q32 | Q64, Q64 => _ | _,_ => _ end).
- left; apply erefl.
- right; discriminate.
- right; discriminate.
- left; apply erefl.
Defined.
Global Opaque quantity_eq.

Canonical Structure quantity_eqMixin := EqMixin (EqDecEqAxiom quantity_eq).
Canonical Structure quantity_eqType := Eval hnf in @EqType quantity quantity_eqMixin.

Definition memval_eq (x y: memval) : {x=y} + {x<>y}.
generalize Byte.eq_dec val_eq NPeano.Nat.eq_dec quantity_eq.
decide equality.
Defined.
Global Opaque memval_eq.

Canonical Structure memval_eqMixin := EqMixin (EqDecEqAxiom memval_eq).
Canonical Structure memval_eqType := Eval hnf in @EqType memval memval_eqMixin.


Canonical Structure chunk_eqMixin := EqMixin (EqDecEqAxiom chunk_eq).
Canonical Structure chunk_eqType :=
  Eval hnf in @EqType memory_chunk chunk_eqMixin.
