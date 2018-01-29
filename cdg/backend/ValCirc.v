Require RTLC.
Import Utf8.
Import Coqlib.
Import Maps.
Import AST.
Import Events.
Import Integers.
Import Values.
Import Globalenvs.
Import Memory.
Import Smallstep.
Import ORbdt.
Import CircIO.

Unset Elimination Schemes.

Section NTH.
Context {A: Type} (d: A).

Local Open Scope N_scope.

Fixpoint nth (n: N) (m: list A) : A :=
  match m with
  | nil => d
  | a :: m' =>
    match n with
    | N0 => a
    | Npos p => nth (Pos.pred_N p) m'
    end
  end.

  Definition nlen (m: list A) := N.of_nat (length m).

  Lemma nlen_nil : nlen nil = 0.
  Proof. reflexivity. Qed.

  Lemma nlen_cons x y :
    nlen (x :: y) = N.succ (nlen y).
  Proof.
    apply Nnat.Nat2N.inj_succ.
  Qed.

  Lemma nlen_app (x y: list A) :
    nlen (x ++ y) = nlen x + nlen y.
  Proof.
    unfold nlen.
    rewrite app_length.
    apply Nnat.Nat2N.inj_add.
  Qed.

Lemma nth_app n (m m': list A) :
  nth n (m ++ m') =
  if n <? nlen m
  then nth n m
  else nth (n - nlen m) m'.
Proof.
  revert n m'. elim m; clear.
  - intros n m'. simpl. rewrite nlen_nil, (proj2 (N.ltb_ge n 0)), N.sub_0_r. reflexivity. Psatz.lia.
  - intros a m IH n m'. simpl. case N.ltb_spec.
    + intros LT. destruct n as [ | n ]; auto.
      rewrite IH. rewrite (proj2 (N.ltb_lt _ _)); auto.
      clear -LT. rewrite N.pos_pred_spec.
      rewrite nlen_cons, <- N.add_1_l in LT.
      rewrite N.pred_sub. Psatz.lia.
    + intros LE.
      destruct n as [ | n ]. rewrite nlen_cons in LE. Psatz.lia.
      rewrite N.pos_pred_spec, N.pred_sub, IH.
      rewrite (proj2 (N.ltb_ge _ _)). apply f_equal2; auto.
      rewrite nlen_cons. Psatz.lia.
      rewrite nlen_cons in LE. Psatz.lia.
Qed.

Corollary nth_skip n (m m': list A) :
  nlen m <= n →
  nth n (m ++ m') = nth (n - nlen m) m'.
Proof.
  intros LE. rewrite nth_app.
  rewrite (proj2 (N.ltb_ge _ _)); auto.
Qed.

End NTH.

Inductive gate : Type :=
| Gop `(Op.operation)
| Gload `(memory_chunk) `(Op.addressing)
| Gstore `(pcond) `(memory_chunk) `(Op.addressing)
| Gtest `(pcond) `(Op.condition)
| Gφ `(phiNode)
.

Definition wire : Type := N.

Record gentry : Type :=
  Gentry {
      ggate :> gate; (* body *)
      gwires : list wire (* arguments *)
    }.

Definition code : Type := list gentry.

(* A condition_wires maps (shifted) wire names to the condition they represent (if any). *)
Definition condition_wires : Type :=
  PTree.t ident.

Definition condition_of_wire (cw: condition_wires) (w: wire) : option ident :=
  cw ! (N.succ_pos w).

Record function : Type :=
  Function {
    fn_inputs: list (slot * ident);
    fn_stacksize: Z;
    fn_conditions:  condition_wires;
    fn_body: code;
    fn_outputs: list (slot * ident)
  }.

Definition program : Type := program (fundef function) unit.

Definition grid : Type := list val.

Definition read_wire (g: grid) (w: wire) : val :=
  nth Vundef w g.

Definition read_wires (g: grid) (ws: list wire) : list val :=
  List.map (read_wire g) ws.

Definition get_path_model' {V: Type} (g: list V) (val_is_true: V → bool) (cow: wire → option ident) : pEnv * wire :=
  fold_left (λ pcm_i v, let '(pcm, i) := pcm_i in
                        (match cow i with
                         | None => pcm
                         | Some c => if val_is_true v then c :: pcm else pcm
                         end, N.succ i)) g (nil, N0).

Definition val_is_true (v: val) : bool :=
  if Val.eq v Vtrue then true else false.

Definition get_path_model (g: grid) (cw: condition_wires) : pEnv :=
  fst (get_path_model' g val_is_true (condition_of_wire cw)).

Lemma get_path_model'_nlen {V} (g: list V) ev cow :
  let '(pcm, n) := get_path_model' g ev cow in
  n = nlen g.
Proof.
  elim g using rev_ind; clear.
  reflexivity.
  intros v g IH. unfold get_path_model'. rewrite fold_left_app.
  simpl. fold (get_path_model' g ev cow). destruct (get_path_model' _ _).
  rewrite nlen_app, nlen_cons. simpl. subst. symmetry. apply N.add_1_r.
Qed.

Infix ":::" := (λ x y, x ++ y :: nil) (at level 40).

Inductive state : Type :=
| InitState `(function) `(mem)
| InputState
        `(option (slot * val))	(**r input value *)
        `(list (slot * ident))	(**r input locations *)
        `(val)		(**r stack pointer *)
        `(Z)		(**r stack size *)
        `(condition_wires)	(**r wires that hold conditions *)
        `(list gentry)	(**r instructions *)
        `(mem)		(**r memory *)
        `(list (slot * ident))	(**r output locations *)
| InputFenceState `(val) `(Z) `(condition_wires) `(list gentry)
                  `(mem) `(list (slot * ident))
| PostInputState `(val) `(Z) `(condition_wires) `(list gentry)
                 `(mem) `(list (slot * ident))
| State
        `(val)	(**r stack pointer *)
        `(Z)	(**r stack size *)
        `(condition_wires)	(**r wires that hold conditions *)
        `(list gentry)	(**r instructions *)
        `(grid)	(**r wire values *)
        `(mem)	(**r memory *)
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

Section EVAL_GATE.
Import eqtype zint.

Context {F V: Type} (ge: Genv.t F V).

Definition eval_gate (sp: Values.val) pcm grd (ga: gate) (args: list Values.val) (m: mem) (res: Values.val) (m': mem) : Prop :=
  match ga with
  | Gop op => RTLC.eval_operation ge sp op args m = res ∧ m' = m
  | Gload ϰ addr =>
    let ptr := RTLC.eval_addressing ge sp addr args in
    RTLC.mem_loadv ϰ m ptr = res ∧ m' = m
  | Gstore g ϰ addr =>
    if eval_pcond pcm g
    then
      ∃ src dst, args = src :: dst ∧
      let ptr := RTLC.eval_addressing ge sp addr dst in
      Mem.storev ϰ m ptr src= Some m' ∧
      res = Vundef
    else res = Vundef ∧ m' = m
  | Gtest g cnd =>
    if eval_pcond pcm g
    then
      ∃ b,
      Op.eval_condition cnd args m = Some b ∧
      res = (if b then Vtrue else Vfalse) ∧ m' = m
    else res = Vundef ∧ m' = m
  | Gφ φ =>
    args = nil ∧
    res = match eval_phiNode pcm φ with
          | Some w => read_wire grd (Pos.pred_N w)
          | None => Vundef end ∧
    m' = m
  end.

End EVAL_GATE.

Section STEP.

Context (ge: Genv.t (fundef function) unit).

Definition step (s1: state) (tr: trace) (s2: state) :=
 match s1 with
 | InitState f m =>
   let '(m', sp) := Mem.alloc m 0 (fn_stacksize f) in
   tr = E0 ∧
   s2 = InputState None (fn_inputs f)
              (Vptr sp Int.zero) (fn_stacksize f)
              (fn_conditions f) (fn_body f) m'
              (fn_outputs f)
 | InputState None ((x, src) :: ins) sp ssz cw body m outs =>
   ∃ b ev v,
   Senv.block_is_volatile ge b = true ∧
   Senv.find_symbol ge src = Some b ∧
   tr = Event_vload Mint8unsigned src Int.zero ev :: nil ∧
   eventval_valid ge ev ∧
   eventval_match ge ev Tint v ∧
  s2 = InputState (Some (x, Val.load_result Mint8unsigned v)) ins sp ssz cw body m outs
| InputState (Some ((x, o), v)) ins sp ssz cw body m outs =>
  tr = E0 ∧
  ∃ m',
    let ptr := Genv.symbol_address ge x o in
    Mem.storev Mint8unsigned m ptr v = Some m' ∧
    s2 = InputState None ins sp ssz cw body m' outs
| InputState None nil sp ssz cw body m outs =>
  tr = E0 ∧
  s2 = InputFenceState sp ssz cw body m outs
| InputFenceState sp ssz cw body m outs =>
  tr = E0 ∧
  s2 = PostInputState sp ssz cw body m outs
| PostInputState sp ssz cw body m outs =>
  tr = E0 ∧
  s2 = State sp ssz cw body nil m outs
 | State sp ssz cw (Gentry j args :: body) g m outs =>
  let pcm := get_path_model g cw in
  tr = E0 ∧
  ∃ v m',
    eval_gate ge sp pcm g j (read_wires g args) m v m' ∧
    s2 = State sp ssz cw body (g ::: v) m' outs
| State sp ssz _ nil _ m outs =>
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

End STEP.

Definition initial_state (p: program) (s: state) : Prop :=
  let ge := Genv.globalenv p in
  ∃ m0 b f,
      Genv.init_mem p = Some m0 ∧
      Genv.find_symbol ge p.(prog_main) = Some b ∧
      Genv.find_funct_ptr ge b = Some (Internal f) ∧
      s = InitState f m0.

Definition final_state (st: state) (res: int) : Prop :=
  res = Int.zero ∧ st = FinalState.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).
