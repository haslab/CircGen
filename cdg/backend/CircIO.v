Require Import Utf8.
Require Events.
Import String.
Import Coqlib.
Import AST Events.
Import Integers Values.

Unset Elimination Schemes.

Definition slot : Type := (ident * int)%type.

Definition slot_dec (x y: slot) : { x = y } + { x ≠ y } :=
  EquivDec.prod_eqdec Pos.eq_dec Int.eq_dec x y.

Definition fence_ident : string := "__circgen_fence"%string.

Definition fence_sig : signature :=
  {| sig_args := nil ; sig_res := None ; sig_cc := cc_default |}.

(* This axiom states that calling the “void fence(void)” external function
preserves the memory and does not emit any visible event.

This function is used to delimit the circuit from the input and output sequences. *)
Axiom fence_sem :
  ∀ ge m tr v m',
    external_functions_sem fence_ident fence_sig ge nil m tr v m' →
    tr = E0 ∧ m' = m.
