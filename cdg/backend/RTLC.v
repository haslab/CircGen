(** RTLC is a variant of the RTL language where control-flow is replaced by
  guards on instructions.

An other notable difference is that all operations (as well as memory loads)
 are well defined.
This is a natural relaxation of the RTL semantics when targeting Boolean circuits,
 as Boolean gates have well defined semantics.
*)

Require Smallstep.
Require Registers.
Require Op.
Require CircIO.
Import Utf8.
Import Coqlib.
Import Maps.
Import AST.
Import Integers.
Import Values.
Import Events.
Import Memory.
Import Globalenvs.
Import Smallstep.
Import Op.
Import Registers.
Import CircIO.

Require Import zint ORbdt.

Unset Elimination Schemes.

(** * Abstract syntax *)

(** Control-decision conditions are stored on a distinct environment (for
  the sake of simplicity, they keep that same node-id of the original [Icond]
  instruction). *)

Inductive instruction: Type :=
  | Itest: ident -> condition -> list reg -> instruction
      (** a branching instruction *)
  | Iop: operation -> list reg -> reg -> instruction
      (** [Iop op args dest succ] performs the arithmetic operation [op]
          over the values of registers [args], stores the result in [dest] *)
  | Iload: memory_chunk -> addressing -> list reg -> reg -> instruction
      (** [Iload chunk addr args dest succ] loads a [chunk] quantity from
          the address determined by the addressing mode [addr] and the
          values of the [args] registers, stores the quantity just read
          into [dest] *)
  | Istore: memory_chunk -> addressing -> list reg -> reg -> instruction.
      (** [Istore chunk addr args src succ] stores the value of register
          [src] in the [chunk] quantity at the
          the address determined by the addressing mode [addr] and the
          values of the [args] registers  *)

Definition code := list (pcond*instruction).

Record function: Type := mkfunction {
  fn_stacksize: Z;
  fn_inputs: list (slot * ident);
  fn_outputs: list (slot * ident);
  fn_code: code
}.

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.
Definition regset := Regmap.t val.
Definition pc_model := list ident.

(** The dynamic semantics of RTLC is given in small-step style, as a
  set of transitions between states.
*)

Inductive state : Type :=
| InitState `(function) `(mem)
| InputState `(option (slot * val))	(**r input value *)
        `(list (slot * ident))	(**r input locations *)
        `(val)		(**r stack pointer *)
        `(Z)		(**r stack size *)
        `(code)		(**r instructions *)
        `(mem)		(**r memory *)
        `(list (slot * ident))	(**r output locations *)
| InputFenceState `(val) `(Z) `(code) `(mem) `(list (slot * ident))
| PostInputState `(val) `(Z) `(code) `(mem) `(list (slot * ident))
| State
        `(val)		(**r stack pointer *)
        `(Z)		(**r stack size *)
        `(code)		(**r instructions *)
        `(pc_model)	(**r path conditions *)
        `(regset)	(**r register state *)
        `(mem)		(**r memory *)
        `(list (slot * ident))	(**r output locations *)
| OutputFenceState `(val) `(Z) `(mem) `(list (slot * ident))
| PreOutputState `(val) `(Z) `(mem) `(list (slot * ident))
| OutputState `(option (val * ident))	(**r output value *)
        `(list (slot * ident))	(** output locations *)
        `(val)		(**r stack pointer *)
        `(Z)		(**r stack size *)
        `(mem)		(**r memory *)
| FinishingState `(val) `(Z) `(mem)
| FinalState.

Section RELAXED.
Context {F V: Type} (ge: Genv.t F V).

Definition oval : Type := option val.
Definition obool : Type := option bool.

Definition X_of_oX {X} (x: X) (o: option X) : X :=
  match o with
  | None => x
  | Some v => v
  end.

Definition val_of_oval : oval → val := X_of_oX Vundef.
Definition bool_of_obool : obool → bool := X_of_oX false.

Coercion val_of_oval : oval >-> val.
Coercion bool_of_obool : obool >-> bool.

Definition eval_operation sp op args m : val :=
  Op.eval_operation ge sp op args m :oval.

Definition eval_condition cond args m : bool :=
  Op.eval_condition cond args m :obool.

Definition eval_addressing sp addr args : val :=
  Op.eval_addressing ge sp addr args :oval.

Definition mem_loadv ϰ m ptr : val :=
  Mem.loadv ϰ m ptr :oval.

Definition None_neq_Some {X: Type} {P: Prop} {x: X} (H: None = Some x) : P :=
  let 'Logic.eq_refl := H in I.

Definition Some_eq_inv {X: Type} {x x': X} (H: Some x = Some x') : x = x' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition oX_eq {X: Type} {d: X} {o: option X} {x: X} (H: o = Some x) : X_of_oX d o = x :=
    match eq_sym H in _ = a return X_of_oX d a = x with
    | Logic.eq_refl => Logic.eq_refl
    end.

Lemma eval_condition_w {cond args m b} :
  Op.eval_condition cond args m = Some b →
  eval_condition cond args m = b.
Proof.
  destruct cond;
    repeat (destruct args as [ | ? args ]; try exact None_neq_Some);
  apply oX_eq.
Qed.

Lemma eval_addressing_w {sp addr args v} :
  Op.eval_addressing ge sp addr args = Some v →
  eval_addressing sp addr args = v.
Proof.
  destruct addr;
    repeat (destruct args as [ | ? args ]; try exact None_neq_Some);
  apply oX_eq.
Qed.

Lemma eval_operation_w {sp op args m v} :
  Op.eval_operation ge sp op args m = Some v →
  eval_operation sp op args m = v.
Proof.
  destruct op; try apply Some_eq_inv;
  repeat (apply oX_eq || (destruct args as [ | ? args ]; try exact None_neq_Some)).
Qed.

Lemma mem_loadv_w {ϰ ptr m v} :
  Mem.loadv ϰ m ptr = Some v →
  mem_loadv ϰ m ptr = v.
Proof.
  Transparent Mem.load.
  destruct ptr; try exact None_neq_Some.
  unfold mem_loadv. simpl. unfold Mem.load.
  case Mem.valid_access_dec; intros _.
  exact Some_eq_inv.
  exact None_neq_Some.
  Opaque Mem.load.
Qed.

Lemma eval_operation_lessdef {sp op args m args' m'} :
  Val.lessdef_list args args' →
  Mem.extends m m' →
  Val.lessdef (eval_operation sp op args m) (eval_operation sp op args' m').
Proof.
  intros LD M.
  generalize (λ v, Op.eval_operation_lessdef ge sp op (v1 := v) LD M).
  unfold eval_operation.
  destruct (Op.eval_operation _ _ _ _ m). 2: right.
  intros H; specialize (H _ eq_refl).
  destruct H as (? & -> & H). exact H.
Qed.

Lemma mem_loadv_lessdef {ϰ m ptr m' ptr'} :
  Val.lessdef ptr ptr' →
  Mem.extends m m' →
  Val.lessdef (mem_loadv ϰ m ptr) (mem_loadv ϰ m' ptr').
Proof.
  intros LD M.
  unfold mem_loadv, Mem.loadv.
  destruct ptr; try right.
  destruct (Mem.load _ m _ _) eqn: H. 2: right.
  inv LD.
  destruct (Mem.load_extends ϰ m m' _ _ _ M H) as (? & -> & X).
  exact X.
Qed.

Lemma eval_addressing_lessdef {sp addr args args'} :
  Val.lessdef_list args args' →
  Val.lessdef (eval_addressing sp addr args) (eval_addressing sp addr args').
Proof.
  intros LD.
  unfold eval_addressing.
  destruct (Op.eval_addressing _ _ _ args) eqn: EQ. 2: right.
  destruct (Op.eval_addressing_lessdef ge sp addr LD EQ) as (? & -> & H). exact H.
Qed.

End RELAXED.

Section RELSEM.

Variable ge: genv.

(** The transitions are presented as an inductive predicate
  [step ge st1 t st2], where [ge] is the global environment,
  [st1] the initial state, [st2] the final state, and [t] the trace
  of system calls performed during this transition. *)

Require RTL.

Definition step (s1: state) (tr:trace) (s2:state) :=
 match s1 with
 | InitState f m =>
   let '(m', sp) := Mem.alloc m 0 (fn_stacksize f) in
   tr = E0 ∧
   s2 = InputState None (fn_inputs f)
                   (Vptr sp Int.zero) (fn_stacksize f)
                   (fn_code f) m'
                   (fn_outputs f)
 | InputState None ((x, src) :: ins) sp ssz stmts m outs =>
   ∃ b ev v,
   Senv.block_is_volatile ge b = true ∧
   Senv.find_symbol ge src = Some b ∧
   tr = Event_vload Mint8unsigned src Int.zero ev :: nil ∧
   eventval_valid ge ev ∧
   eventval_match ge ev Tint v ∧
  s2 = InputState (Some (x, Val.load_result Mint8unsigned v)) ins sp ssz stmts m outs
| InputState (Some ((x, o), v)) ins sp ssz stmts m outs =>
  tr = E0 ∧
  ∃ m',
    let ptr := Genv.symbol_address ge x o in
    Mem.storev Mint8unsigned m ptr v = Some m' ∧
    s2 = InputState None ins sp ssz stmts m' outs
| InputState None nil sp ssz stmts m outs =>
  tr = E0 ∧
  s2 = InputFenceState sp ssz stmts m outs
| InputFenceState sp ssz stmts m outs =>
  tr = E0 ∧
  s2 = PostInputState sp ssz stmts m outs
| PostInputState sp ssz stmts m outs =>
  tr = E0 ∧
  s2 = State sp ssz stmts nil (Regmap.init Vundef) m outs
| State sp ssz ((g, j) :: stmts) pcm rs m outs =>
  tr = E0 ∧
  if eval_bdd pcm g
  then match j with
       | Iop op args res =>
         let v := eval_operation ge sp op (rs ## args) m in
         s2 = State sp ssz stmts pcm (rs # res <- v) m outs
       | Iload chunk addr args res =>
         let ptr := eval_addressing ge sp addr (rs ## args) in
         let v := mem_loadv chunk m ptr in
         s2 = State sp ssz stmts pcm (rs # res <- v) m outs
       | Istore chunk addr args source =>
         ∃ m',
           let ptr := eval_addressing ge sp addr (rs ## args) in
           Mem.storev chunk m ptr (rs # source)= Some m' ∧
           s2 = State sp ssz stmts pcm rs m' outs
       | Itest res cond args =>
         ∃ b,
          Op.eval_condition cond (rs ## args) m = Some b ∧
         s2 = State sp ssz stmts (if b then res :: pcm else pcm) rs m outs
       end
  else s2 = State sp ssz stmts pcm rs m outs
| State sp ssz nil pcm rs m outs =>
  tr = E0 ∧
  s2 = OutputFenceState sp ssz m outs
| OutputFenceState sp ssz m outs =>
  tr = E0 ∧
  s2 = PreOutputState sp ssz m outs
| PreOutputState sp ssz m outs =>
  tr = E0 ∧
  s2 = OutputState None outs sp ssz m
| OutputState None (((x, o), dst) :: outs) sp ssz m =>
  tr = E0 ∧
  ∃ v,
  let ptr := Genv.symbol_address ge x o in
  Mem.loadv Mint8unsigned m ptr = Some v ∧
  s2 = OutputState (Some (v, dst)) outs sp ssz m
| OutputState (Some (v, dst)) outs sp ssz m =>
  ∃ b ev,
   Senv.block_is_volatile ge b = true ∧
   Senv.find_symbol ge dst = Some b ∧
   tr = Event_vstore Mint8unsigned dst Int.zero ev :: nil ∧
   eventval_match ge ev Tint v ∧
  s2 = OutputState None outs sp ssz m
| OutputState None nil sp ssz m =>
  tr = E0 ∧
  s2 = FinishingState sp ssz m
| FinishingState sp ssz m =>
  tr = E0 ∧
  ∃ b, sp = Vptr b Int.zero ∧
  ∃ m',
    Mem.free m b 0 ssz = Some m' ∧ s2 = FinalState
 | FinalState => False
 end.

End RELSEM.

(** Execution of whole programs are described as sequences of transitions
  from an initial state to a final state.  *)

Definition initial_state (p: program) (s: state) : Prop :=
  let ge := Genv.globalenv p in
  ∃ m0 b f,
      Genv.init_mem p = Some m0 ∧
      Genv.find_symbol ge p.(prog_main) = Some b ∧
      Genv.find_funct_ptr ge b = Some (Internal f) ∧
      s = InitState f m0.

Definition final_state (st: state) (res: int) : Prop :=
  res = Int.zero ∧ st = FinalState.

(** The small-step semantics for a program. *)

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(** This semantics is receptive to changes in events. *)

(*
Lemma fence_call_receptive {F V} {ge: Genv.t F V} {m t v t' m'} :
  external_functions_sem "__circgen_fence" fence_sig ge nil m t v m' →
  match_traces ge t t' →
  ∃ v' m'',
  external_functions_sem "__circgen_fence" fence_sig ge nil m t' v' m''.
Proof.
  apply (external_call_receptive (EF_external _ _)).
Qed.

Lemma fence_call_determinate {F V} {ge: Genv.t F V} {m t1 t2 v1 v2 m1 m2} :
  external_functions_sem "__circgen_fence" fence_sig ge nil m t1 v1 m1 →
  external_functions_sem "__circgen_fence" fence_sig ge nil m t2 v2 m2 →
  match_traces ge t1 t2 ∧
  (t1 = t2 → v1 = v2 ∧ m1 = m2).
Proof.
  apply (external_call_determ (EF_external _ _)).
Qed.

Lemma fence_call_length {F V} {ge: Genv.t F V} {m t v m'} :
  external_functions_sem "__circgen_fence" fence_sig ge nil m t v m' →
  (length t ≤ 1)%nat.
Proof.
  apply (external_call_trace_length (EF_external _ _)).
Qed.
*)

Lemma semantics_receptive p :
  receptive (semantics p).
Proof.
  split;
    intros (); simpl; intros;
    repeat match goal with
           | H : False |- _ => destruct H
           | H : ?a = ?b |- _ => subst a || subst b
           | H : _ /\ _ |- _ => let K := fresh H in destruct H as [ H K ]
           | H : exists a, _ |- _ => let b := fresh a in destruct H as [ b H ]
           | H : external_call _ _ _ _ _ _ _, K : match_traces _ _ _ |- _ =>
             generalize (external_call_receptive _ _ _ _ _ H K); clear H K; intros H
           | H : match_traces _ E0 _ |- _ => inversion H; clear H
           | H : match_traces _ (_ :: _) _ |- _ => inversion H; clear H
           | H : _ :: _ = _ |- _ => inversion H; clear H
           | H : eventval_match _ _ _ _,
                 V1 : eventval_valid _ _,
                 V2 : eventval_valid _ _,
                 EQ : eventval_type _ = eventval_type _
             |- _ =>
             destruct (eventval_match_receptive _ H V1 V2 EQ); clear H
           | H : let (u, v) := ?a in _ |- _ => destruct a
           | H : match ?a with _ => _ end |- _ => destruct a
           end; eauto 10 using external_call_trace_length.
Qed.

Lemma semantics_determinate p :
  determinate (semantics p).
Proof.
  split; try apply semantics_receptive;
    intros (); simpl; intros;
    repeat match goal with
           | H : False |- _ => destruct H
           | H : ?a = ?b |- _ => subst a || subst b
           | H : _ /\ _ |- _ => let K := fresh H in destruct H as [ H K ]
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H
           | H : exists a, _ |- _ => let b := fresh a in destruct H as [ b H ]
           | H : let (u, v) := ?a in _ |- _ => destruct a
           | H : match ?a with _ => _ end |- _ => destruct a
           | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K; inversion K; clear K
           | H : initial_state _ _ |- _ => unfold initial_state in H
           | H : final_state _ _ |- _ => unfold final_state in H
           | H : _ = FinalState |- _ => inversion H; clear H
           | H : eventval_match _ _ _ _, K: eventval_match _ _ _ _ |- _ =>
             generalize (eventval_match_determ_1 H K); clear H K;
               intro
           | H : eventval_match _ _ _ _, K: eventval_match _ _ _ _ |- _ =>
             generalize (eventval_match_determ_2 H K); clear H K;
               intro
           | |- nostep _ _ _ => intros ? (); intros
           | H : external_call _ _ _ _ _ _ _, K : external_call _ _ _ _ _ _ _ |- _ =>
             generalize (external_call_determ _ _ _ _ _ _ _ _ _ _ H K); clear H K;
               intros [H K]
           | |- _ ∧ _ => split
           | |- _ → _ => intro
           | H : ?a = ?a → _ |- _ => specialize (H Logic.eq_refl)
           end; eauto using match_traces_E0.
  constructor; eauto using eventval_match_same_type.
  constructor.
Qed.
