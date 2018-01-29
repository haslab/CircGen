Require
  RTL
  RTLC.
Require MoreBDD.
Import Utf8.
Import Relations.
Import String.
Import Coqlib.
Import Integers.
Import Errors.
Import AST.
Import Registers.
Import Maps.
Import ORbdt.
Import MoreBDD.
Import eqtype.
Import zint.
Import CircIO.

Unset Elimination Schemes.

Ltac rw :=
  repeat match goal with
         | H : _ = _ |- _ => rewrite H
         end.

Lemma findP {A} (f: A → bool) (m: list A) :
  match find f m with
  | None => ∀ a, In a m → f a = false
  | Some a =>
    ∃ pre post, m = pre ++ a :: post ∧ f a = true ∧ ∀ a, In a pre → f a = false
  end.
Proof.
  elim m; clear.
  intros _ ().
  intros a m IH. simpl.
  destruct (f _) eqn: H.
  - exists nil, m. refine (conj Logic.eq_refl (conj H _)). intros _ ().
  - destruct (find _ _) as [ b | ].
    + destruct IH as (pre & post & -> & Hb & Hpre).
      exists (a :: pre), post.
      refine (conj Logic.eq_refl (conj Hb _)).
      intros a' [ -> | Ha' ]; auto.
    + intros a' [ -> | Ha' ]; auto.
Qed.

Lemma rev'P {A} (m n: list A) :
  rev' m = n → m = rev n.
Proof.
  unfold rev'. rewrite <- rev_alt.
  intros <-. symmetry. apply rev_involutive.
Qed.

Definition pos_pred_intro (P: positive → positive → Prop) :
  P xH xH →
  (∀ p, P (p + 1) p)%positive →
  ∀ p, P p (Pos.pred p).
Proof.
  intros H1 Hsucc p.
  case (Pos.succ_pred_or p).
  intros ->. exact H1.
  intros H.
  rewrite <- H, <- Pos.add_1_r at 1.
  auto.
Qed.

Lemma eval_pcond_then {pc pcm bdd} :
  bounded_bdd bdd pc →
  eval_pcond pcm bdd = true →
  eval_pcond (pc :: pcm) (pcond_and bdd (pcond_lit pc)) = true.
Proof.
  intros BND H.
  rewrite pcond_andP, andb_true_iff. split.
  rewrite <- H. symmetry. auto using eval_bounded.
  rewrite pcond_litP. apply ssrlib.InE; left; reflexivity.
Qed.

Lemma eval_pcond_else {pc pcm bdd} :
  (∀ q, In q pcm → (pc < q)%positive) →
  eval_pcond pcm bdd = true →
  eval_pcond pcm (pcond_and bdd (pcond_litN pc)) = true.
Proof.
  intros PLT H.
  rewrite pcond_andP, H, pcond_litNP.
  generalize (ssrlib.InE pc pcm).
  destruct (ssrbool.in_mem _ _). 2: reflexivity.
  intros [K _]. specialize (PLT _ (K Logic.eq_refl)). Psatz.lia.
Qed.

Lemma pos_pred_le x : (Pos.pred x <= x)%positive.
Proof. apply pos_pred_intro; intros; Psatz.lia. Qed.

Lemma pos_ge_pred x y :
  (Pos.pred x < y → y <= x → x = y)%positive.
Proof. apply pos_pred_intro; intros; Psatz.lia. Qed.

(** Path conditions *)
(** The crucial data structure in the transformation from RTL to RTLC is the set of path conditions:
each node is mapped to a “condition” representing the union of all paths that may lead there. *)
Definition path_conditions : Type :=
  PTree.t pcond.

Definition path_at n (path: path_conditions) : pcond :=
  match path ! n with
  | None => pcondF
  | Some cp => cp
  end.

Definition path_conditions_le (π π': path_conditions) : Prop :=
  ∀ x, pcond_implE (path_at x π) (path_at x π').

Lemma path_conditions_le_refl π : path_conditions_le π π.
Proof. intros x m. exact id. Qed.

Lemma path_conditions_le_trans π' π π'' :
  path_conditions_le π π' →
  path_conditions_le π' π'' →
  path_conditions_le π π''.
Proof.
  intros H H' x m L.
  specialize (H x m L).
  exact (H' _ _ H).
Qed.

Definition successors (p: RTL.code) (x: RTL.node) : list RTL.node :=
  match p ! x with
  | Some i => RTL.successors_instr i
  | None => nil
  end.

Definition successor (p: RTL.code) (x y: RTL.node) : Prop :=
  (y < x)%positive ∧
    match successors p x with
    | k :: nil => y = k
    | k :: k' :: nil => y = k ∨ y = k'
    | _ => False (* Boolean conditions only, so no more than two successors *)
    end.

Definition reachable p : relation RTL.node :=
  clos_refl_trans _ (successor p).

Remark reachable_refl p x : reachable p x x.
Proof. apply rt_refl. Qed.

Lemma reachable_n1 y p x z :
  reachable p x y →
  successor p y z →
  reachable p x z.
Proof.
  intros R S.
  apply clos_rtn1_rt.
  econstructor. exact S.
  apply clos_rt_rtn1. exact R.
Qed.

Lemma reachable_le p x y :
  reachable p x y →
  (y <= x)%positive.
Proof.
  intros H. elim H using clos_refl_trans_ind_left; clear.
  Psatz.lia.
  intros y z _ Hxy [ LT _ ]. Psatz.lia.
Qed.

Record wf_path_conditions p (ep: RTL.node) (path: path_conditions) : Prop :=
  WFPC {
      wfpc_ep : ∀ m, eval_pcond m (path_at ep path) = true;
      wfpc_unreach : ∀ z, ¬ reachable p ep z → path_at z path = pcondF;
      wfpc_bounded: ∀ pc, bounded_bdd (path_at pc path) pc
    }.

Definition eloquent_path_conditions (f: RTL.code) (path: path_conditions) (lo hi: RTL.node) : Prop :=
  (∀ x : RTL.node,
    lo < x → x <= hi →
    match successors f x with
    | nil => True
    | z :: nil =>
      bdd_leq (path_at x path) (path_at z path) = true ∧
      ∀ y, z < y → y < x → pcond_disjoint (path_at x path) (path_at y path) = true
    | z1 :: z2 :: nil =>
      let p := path_at x path in
      let p1 := pcond_and p (pcond_lit x) in
      let p2 := pcond_and p (pcond_litN x) in
      bdd_leq p1 (path_at z1 path) = true ∧
      bdd_leq p2 (path_at z2 path) = true ∧
      (∀ y, z1 < y → y < x → pcond_disjoint p1 (path_at y path) = true) ∧
      ∀ y, z2 < y → y < x → pcond_disjoint p2 (path_at y path) = true
    | _ => False
    end
  )%positive ∧
  (path_at lo path == pcondT) = true.

Section DEFS.
  Context (defs: list (ident * globdef RTL.fundef unit)).

(** Specification of the compilation from RTL to RTLC. *)
(** There are tree phases in this translation:
 1. recognize input variables;
 2. translate the body;
 3. recognize output variables (and the final return).
*)

(** These propositions relate a program point in a RTL control-flow-graph
  and a triple made of a sequence of input variables, a sequence of guarded RTLC instructions, and a seqence of output variables.
*)
Section SPEC.

  Context (p: RTL.code).
  Context (path: path_conditions).

  Let pcond_at (pc: RTL.node) : pcond :=
    match path ! pc with
    | Some p => p
    | None => pcondF
    end.

  Definition guarded_at_end : Prop :=
    ∃ r,
      p ! 2 = Some (RTL.Iop (Op.Ointconst Int.zero) nil r 1)%positive ∧
      p ! 1 = Some (RTL.Ireturn (Some r)).

  Context (blacklist: PTree.t unit).
  Definition is_blacklisted (r: reg) : bool :=
    match blacklist ! r with
    | None => false
    | Some _ => true
    end.

  Definition are_not_blacklisted : list reg → bool :=
    forallb (λ r, negb (is_blacklisted r)).

  Definition declared_volatile (n: ident) : Prop :=
    ∃ pre gv post,
      ¬ In n (map fst (rev pre)) ∧
      gvar_volatile gv = true ∧
      defs = pre ++ (n, Gvar gv) :: post.

  Fixpoint guarded_at_input (pc: RTL.node) (out: list (slot * ident)) (pcf: RTL.node) : Prop :=
    match out with
    | nil => pc = pcf
    | ((x, o), src) :: out =>
      ∃ pc1 r pc2,
    p ! pc = Some (RTL.Ibuiltin (EF_vload Mint8unsigned) (BA_addrglobal src Int.zero :: nil) (BR r) pc1)
    ∧ p ! pc1 = Some (RTL.Istore Mint8unsigned (Op.Aglobal x o) nil r pc2)
    ∧ is_blacklisted r = true
    ∧ ¬ In (x, o) (map fst out)
    ∧ declared_volatile src
    ∧ (1 < pc2)%positive
    ∧ guarded_at_input pc2 out pcf
    end.

  Fixpoint guarded_at_output (pc: RTL.node) (out: list (slot * ident)) (pcf: RTL.node) : Prop :=
    match out with
    | nil => pc = pcf
    | ((x, o), dst) :: out =>
      ∃ pc1 r pc2,
    p ! pc = Some (RTL.Iload Mint8unsigned (Op.Aglobal x o) nil r pc1)
    ∧ p ! pc1 = Some (RTL.Ibuiltin (EF_vstore Mint8unsigned) (BA_addrglobal dst Int.zero :: BA r :: nil) BR_none pc2)
    (* ∧ ¬ In (x, o) out *)
    ∧ declared_volatile dst
    ∧ (1 < pc2)%positive
    ∧ guarded_at_output pc2 out pcf
    end.

  Definition guarded_instruction (pc: RTL.node) (i: RTL.instruction) (j: RTLC.instruction) : Prop :=
    match i with
    | RTL.Iop op args dst pc' => pc' < pc ∧ j = RTLC.Iop op args dst ∧ are_not_blacklisted args = true
    | RTL.Iload ϰ addr args dst pc' => pc' < pc ∧ j = RTLC.Iload ϰ addr args dst ∧ are_not_blacklisted args = true
    | RTL.Istore ϰ addr args src pc' => pc' < pc ∧ j = RTLC.Istore ϰ addr args src ∧ are_not_blacklisted (src:: args) = true
    | RTL.Icond cond args ifso ifnot => ifso < pc ∧ ifnot < pc ∧ j = RTLC.Itest pc cond args ∧ are_not_blacklisted args = true
    | _ => False
    end%positive.

  Fixpoint guarded_at_body (pc: RTL.node) (code: RTLC.code) (pc': RTL.node) : Prop :=
    match code with
    | nil => pc = pc'
    | (g, j) :: code =>
      g = path_at pc path ∧
      (∃ i, p ! pc = Some i ∧ guarded_instruction pc i j) ∧
      guarded_at_body (Pos.pred pc) code pc'
    end.

  Lemma guarded_at_body_app pc code pc' code' pc'' :
    guarded_at_body pc code pc' →
    guarded_at_body pc' code' pc'' →
    guarded_at_body pc (code ++ code') pc''.
  Proof.
    intros H. revert pc pc' H code' pc''.
    elim code; clear.
    - simpl. congruence.
    - intros (g, j) code IH pc pc' (-> & (i & Hpc & Hi) & REC) code' cp'' TL.
      simpl. eauto 6.
  Qed.

  Definition fence_at (pc: RTL.node) : Prop :=
    ∃ name pre post r,
    is_blacklisted r = true ∧
    p ! (pc + 1) = Some (RTL.Icall fence_sig (inr name) nil r pc) ∧
    ¬ In name (map fst (rev pre)) ∧
    defs = pre ++ (name, Gfun (External (EF_external fence_ident fence_sig))) :: post.

End SPEC.

Definition guarded_function (path: path_conditions) (f: RTL.function) (f': RTLC.function) :=
  RTL.fn_sig f = signature_main ∧
  RTL.fn_params f = nil ∧
  RTL.fn_stacksize f = RTLC.fn_stacksize f' ∧
  ∃ blacklist pc blacklist' pc',
    let c := RTL.fn_code f in
    guarded_at_input c blacklist (RTL.fn_entrypoint f) (RTLC.fn_inputs f') (pc + 1)%positive ∧
    fence_at c blacklist pc ∧
    guarded_at_body c path blacklist pc (RTLC.fn_code f') (pc' + 1)%positive ∧
    fence_at c blacklist' pc' ∧
    wf_path_conditions c pc path ∧
    eloquent_path_conditions c path (pc' + 1)%positive pc ∧
    guarded_at_output c pc' (RTLC.fn_outputs f') 2%positive ∧
    guarded_at_end c.

Definition bl_le (x y: PTree.t unit) : Prop :=
  ∀ n,
    is_blacklisted x n = true →
    is_blacklisted y n = true.

Definition bl_le_refl x : bl_le x x :=
  λ n, id.

Definition bl_le_trans y x z :
  bl_le x y → bl_le y z → bl_le x z :=
  λ p q n Hxn, q n (p n Hxn).

Lemma bl_le_ext (x y: PTree.t unit) :
  (∀ n, is_blacklisted x n = is_blacklisted y n) →
  bl_le x y.
Proof.
  intros EXT n H. eauto.
Qed.

Lemma bl_le_set x n :
  bl_le x (PTree.set n tt x).
Proof.
  intros r H. unfold is_blacklisted.
  rewrite PTree.gsspec. case peq; auto.
Qed.

Definition bl_union (x y: PTree.t unit) : PTree.t unit :=
  PTree.combine
    (λ a b,
     match a with
     | None => b
     | Some _ => a
     end) x y.

Lemma bl_union_le x y :
  (bl_le x (bl_union x y)) ∧ (bl_le y (bl_union x y)).
Proof.
  unfold bl_union.
  split;
  intros n Hn; unfold is_blacklisted in *;
    rewrite PTree.gcombine by reflexivity;
    destruct (x ! _); auto.
Qed.

Lemma bl_union_singleton x n :
  ∀ m,
    is_blacklisted (bl_union x (PTree.set n tt (PTree.empty _))) m =
    is_blacklisted (PTree.set n tt x) m.
Proof.
  intros m.
  unfold is_blacklisted, bl_union.
  rewrite PTree.gcombine by reflexivity.
  rewrite ! PTree.gsspec.
  case peq; intros; subst; case (_ ! _); auto.
  rewrite PTree.gempty; reflexivity.
Qed.

Lemma guarded_at_input_w bl {f bl' ep ins pc} :
  bl_le bl bl' →
  guarded_at_input f bl ep ins pc →
  guarded_at_input f bl' ep ins pc.
Proof.
  intros LE.
  revert ep.
  elim ins; clear ins. intros ?; exact id.
  intros ((x, o), src) ins IH ep.
  intros (pc1 & r & pc2 & Hep & Hpc1 & Hbl & ND & V & LT & REC).
  simpl. eauto 12.
Qed.

Lemma guarded_at_input_app f bl ep ins pc bl' ins' pc' :
  list_disjoint (map fst ins) (map fst ins') →
  guarded_at_input f bl ep ins pc →
  guarded_at_input f bl' pc ins' pc' →
  guarded_at_input f (bl_union bl bl') ep (ins ++ ins') pc'.
Proof.
  intros DIS H. revert ep H ins' DIS pc'.
  elim ins; clear.
  - simpl. intros ? -> ins _ pc'.
    apply guarded_at_input_w, bl_union_le.
  - intros ((x, o), src) ins IH ep (pc1 & r & pc2 & Hep & Hpc1 & Hg & ND & V & LT & G) ins' DIS pc' G'.
    exists pc1, r, pc2.
    apply (conj Hep).
    apply (conj Hpc1).
    split. revert Hg. apply bl_union_le.
    split.
    intros K. rewrite map_app, in_app in K. destruct K as [ K | K ]. auto.
    apply (DIS _ _ (or_introl _ Logic.eq_refl) K Logic.eq_refl).
    apply list_disjoint_cons_left in DIS. auto.
Qed.

Lemma guarded_at_output_app f ep ins pc ins' pc' :
  guarded_at_output f ep ins pc →
  guarded_at_output f pc ins' pc' →
  guarded_at_output f ep (ins ++ ins') pc'.
Proof.
  intros H. revert ep H ins' pc'.
  elim ins; clear.
  - simpl. congruence.
  - intros ((x, o), dst) ins IH ep (pc1 & r & pc2 & Hep & Hpc1 & V & LT & G) ins' pc' G'.
    exists pc1, r, pc2.
    auto 6.
Qed.

Inductive exn : Type :=
| NoInstrAt `(RTL.node)
| BackEdge (_ _: RTL.node)
| BlacklistedRegister
| IllegalInstruction `(RTL.node) `(RTL.instruction)
| InstructionAfterOutput `(RTL.node)
| NoReturn
| WrongSig
| WrongParams
| TooManyFunctions
| DuplicateIONames `(ident)
| NotEloquent
.

Definition pred pc : { n | Pos.succ n = pc } + { pc = xH } :=
  match pc with
  | xH => inright Logic.eq_refl
  | xI n => inleft (exist _ (Pos.pred (xI n)) Logic.eq_refl)
  | xO n => inleft (exist _ (Pos.pred (xO n)) (Pos.succ_pred_double n))
  end.

Inductive proof (P: Prop) : Set :=
| Proof `(P).

Arguments Proof {P} _.
Notation "[ P ]" := (proof P).

Definition pf {P: Prop} (H: [P]) : P :=
  let 'Proof x := H in x.

Section TR_CODE.
  Context (entrypoint: RTL.node) (f: RTL.code).

  Definition is_forward_edge (pc pc': RTL.node) : ({ pc' < pc } + { pc <= pc' })%positive.
    refine (
        match (pc' ?= pc)%positive as b return CompareSpec _ _ _ b → _ with
        | Lt => λ K, left _
        | _ => λ K, right _
        end (Pos.compare_spec _ _)
      );
      clear -K; abstract (inversion K; Psatz.lia).
  Defined.

  Definition check_forward_edge {X} (pc pc': RTL.node) (k: [pc' < pc]%positive → X + exn) : X + exn :=
    match is_forward_edge pc pc' with
    | right _ => inr (BackEdge pc pc')
    | left FWD => k (Proof FWD)
    end.

  Definition check_volatile (n: ident) : bool :=
    match List.find (λ d, let '(name, _) := d in Pos.eqb name n) defs with
    | Some (_, Gvar gv) => gvar_volatile gv
    | _ => false
    end.

  Lemma check_volatile_true n :
    check_volatile n = true →
    declared_volatile n.
  Proof.
    unfold check_volatile.
    match goal with
    | |- appcontext[ find ?f ?m ] => set (q:= f)
    end.
    generalize (findP q defs).
    destruct (find _ _) as [ (?, [ [|] | gv ]) | ]; try discriminate.
    intros (pre & post & H & EQ & NE) V.
    exists pre, gv, post.
    split.
    intros K. rewrite in_map_iff in K. destruct K as ((n' & m) & Hm & K).
    rewrite <- in_rev in K.
    specialize (NE _ K). unfold q in NE. simpl in Hm. subst n'.
    rewrite Pos.eqb_refl in NE. discriminate.
    unfold q in EQ. apply Pos.eqb_eq in EQ. subst i.
    auto.
  Qed.

  Fixpoint translate_inputs pc (acc: list (slot * ident) * PTree.t unit) (WF: Acc Pos.lt pc) :
    RTL.node * list (slot * ident) * PTree.t unit + exn :=
    let 'Acc_intro REC := WF in
    let '(acc, blacklist) := acc in
    match f ! pc with
    | None => inr (NoInstrAt pc)
    | Some i =>
      match i with
      | RTL.Ibuiltin (EF_vload Mint8unsigned) (BA_addrglobal name ofs :: nil) (BR r) pc1 =>
        match f ! pc1 with
        | None => inr (NoInstrAt pc1)
        | Some j => match j with
        | RTL.Istore Mint8unsigned (Op.Aglobal x o) nil r' pc2 =>
        if if Int.eq ofs Int.zero
        then if Pos.eqb r' r
        then check_volatile name
        else false else false
        then
          if in_dec slot_dec (x, o) (map fst acc)
          then inr (DuplicateIONames x) else
          if match pc2 with xH => true | _ => false end
          then inr (IllegalInstruction pc i) else
          check_forward_edge pc pc2 (λ FWD,
            translate_inputs pc2 (((x, o), name) :: acc, PTree.set r tt blacklist) (REC _ (pf FWD))
          )
          else inr (IllegalInstruction pc i)
        | _ => inr (IllegalInstruction pc1 j)
                    end
        end
      | RTL.Ibuiltin _ _ _ _ => inr (IllegalInstruction pc i)
      | _ => inl (pc, List.rev' acc, blacklist)
      end
    end.

  Lemma check_forward_edge_correct {X} {u v} {k: [_] → X + exn} {w} :
    check_forward_edge u v k = inl w →
    ∃ H: (v < u)%positive, k (Proof H) = inl w.
  Proof.
    unfold check_forward_edge. case (is_forward_edge _ _); eauto.
    discriminate.
  Qed.

  Lemma if_it_is_true {b b': bool} :
    (if b then b' else false) = true → b = true ∧ b' = true.
  Proof.
    case b. 2: discriminate. case b'. 2: discriminate. auto.
  Qed.

  Lemma int_eq_true {i j: int} :
    Int.eq i j = true → i = j.
  Proof.
    intros H.
    generalize (Int.eq_spec i j). rewrite H. exact id.
  Qed.

  Fixpoint translate_inputs_correct ep pc acc bl WF pc' ins bl' :
    guarded_at_input f bl ep (rev' acc) pc →
    translate_inputs pc (acc, bl) WF = inl (pc', ins, bl') →
    guarded_at_input f bl' ep ins pc' ∧
    bl_le bl bl'.
  Proof.
    intros G.
    destruct WF as [ REC ].
    simpl. intros H.
    repeat match goal with
           | H: false = true |- _ => inversion H
           | H: true = true |- _ => clear H
           | H: Int.eq _ _ = true |- _ => apply int_eq_true in H
           | H: check_volatile _ = true |- _ => apply check_volatile_true in H
           | H: _ ∧ _ |- _ => let K := fresh H in destruct H as [ H K ]
           | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
           | H: (if ?b then _ else false) = true |- _ => apply if_it_is_true in H || destruct b
           | H: check_forward_edge _ _ _ = inl _ |- _ => apply check_forward_edge_correct in H
           | H: inr _ = inl _ |- _ => inversion H
           | H: inl _ = inl _ |- _ => inversion H; clear H
           | H: ?a = ?b |- _ => subst a || subst b
           | H: match ?a with _ => _ end = inl _ |- _ => destruct a eqn:?
           | H: (_ =? _)%positive = true |- _ => apply Pos.eqb_eq in H
           end; auto using bl_le_refl.
    edestruct translate_inputs_correct. 2: eassumption.
    2: split; [ eassumption | eauto using bl_le_trans, bl_le_set ].
    revert G.
    unfold rev'. rewrite <- ! rev_alt. simpl.
    intros G.
    eapply guarded_at_input_w.
    2: eapply guarded_at_input_app; eauto.
    apply bl_le_ext, bl_union_singleton.
    clear -n1.
    intros x y K [ <- | () ]. intros ->. rewrite map_rev, <- in_rev in K. auto.

    eexists _, _, _.
    split. eassumption. split. eassumption.
    split. unfold is_blacklisted. rewrite PTree.gss. reflexivity.
    split. exact Datatypes.id.
    split. assumption.
    split.
    clear -Heqb. destruct n0; try Psatz.lia. discriminate.
    reflexivity.
  Qed.

  Definition with_condition (path: path_conditions) (pc': RTL.node) (g: pcond) : path_conditions :=
    let cp := path_at pc' path in
    PTree.set pc' (pcond_or g cp) path.

  Lemma with_condition_le path pc' g :
    path_conditions_le path (with_condition path pc' g).
  Proof.
    intros π m.
    unfold with_condition, path_at.
    rewrite PTree.gsspec. case peq.
    - intros ->. rewrite pcond_orP.
      case (eval_pcond m g); easy.
    - intros _. exact id.
  Qed.

  Lemma wf_path_with_condition ep path pc' g :
    (¬ reachable f ep pc' → g = pcondF) →
    bounded_bdd g pc' →
    wf_path_conditions f ep path →
    wf_path_conditions f ep (with_condition path pc' g).
  Proof.
    intros H G [EP WF BND]. unfold with_condition.
    split; unfold path_at.
    - intros m.
      rewrite PTree.gsspec. case peq. 2: auto.
      intros ->. rewrite pcond_orP, EP. apply orb_true_r.
    - intros z NR. rewrite PTree.gsspec. case peq. 2: eauto.
      intros ->. specialize (H NR). rewrite H.
      fold (path_at pc' path). rewrite (WF _ NR).
      reflexivity.
    - intros pc. rewrite PTree.gsspec. case peq. 2: intros; apply BND.
      intros ->. apply bounded_pcond_or; auto. apply BND.
  Qed.

  Lemma translate_body_obligation {pc pc'} :
    [ pc' < pc ]%positive →
    (Pos.pred pc < pc)%positive.
  Proof.
    intros [ LT ]. revert LT.
    apply pos_pred_intro; intros; Psatz.lia.
  Qed.

  Section TR_BODY.
  Context (blacklist: PTree.t unit).

  Fixpoint translate_body (pc: RTL.node) (path: path_conditions) (acc: RTLC.code) (WF: Acc Pos.lt pc) : RTL.node * path_conditions * RTLC.code + exn :=
    let 'Acc_intro REC := WF in
    match f ! pc with
    | None => inr (NoInstrAt pc)
    | Some i =>
      let cp := path_at pc path in
      match i with
      | RTL.Inop pc' => inr (IllegalInstruction pc i)
      | RTL.Iop op args dst pc' =>
        if are_not_blacklisted blacklist args then
        check_forward_edge pc pc' (λ H,
        translate_body (Pos.pred pc) (with_condition path pc' cp)
          ((cp, RTLC.Iop op args dst) :: acc)
          (REC _ (translate_body_obligation H))
        )
        else inr BlacklistedRegister
      | RTL.Iload ϰ addr args dst pc' =>
        if are_not_blacklisted blacklist args then
        check_forward_edge pc pc' (λ H,
        translate_body (Pos.pred pc) (with_condition path pc' cp)
          ((cp, RTLC.Iload ϰ addr args dst) :: acc)
          (REC _ (translate_body_obligation H))
        )
        else inr BlacklistedRegister
      | RTL.Istore ϰ addr args src pc' =>
        if are_not_blacklisted blacklist (src :: args) then
        check_forward_edge pc pc' (λ H,
        translate_body (Pos.pred pc) (with_condition path pc' cp)
          ((cp, RTLC.Istore ϰ addr args src) :: acc)
          (REC _ (translate_body_obligation H))
        )
        else inr BlacklistedRegister
      | RTL.Icond cond args if_so if_not =>
        if are_not_blacklisted blacklist args then
        check_forward_edge pc if_so (λ Ht,
        check_forward_edge pc if_not (λ Hf,
        translate_body (Pos.pred pc)
          (with_condition (with_condition path
                                          if_so (pcond_and (pcond_lit pc) cp))
                          if_not (pcond_and (pcond_litN pc) cp))
          ((cp, RTLC.Itest pc cond args) :: acc)
          (REC _ (translate_body_obligation Ht))
        ))
        else inr BlacklistedRegister
      | RTL.Ireturn _
      | RTL.Icall _ _ _ _ _
        => inl (pc, path, rev' acc)
      | RTL.Itailcall _ _ _
      | RTL.Ijumptable _ _
      | RTL.Ibuiltin _ _ _ _
        => inr (IllegalInstruction pc i)
      end
    end.

  Lemma guarded_at_body_le path ep code pc :
    guarded_at_body f path blacklist ep code pc →
    (pc <= ep)%positive.
  Proof.
    revert ep.
    elim code; clear.
    - intros ep ->. Psatz.lia.
    - intros (g, j) code IH ep (-> & (i & Hi & Hij) & REC).
      specialize (IH _ REC).
      eapply Pos.le_trans. exact IH.
      apply pos_pred_le.
  Qed.

  Lemma path_at_pc_with_condition pc path n q :
    (n < pc)%positive →
    path_at pc path = path_at pc (with_condition path n q).
  Proof.
    intros LT.
    unfold path_at, with_condition.
    rewrite PTree.gso; auto. Psatz.lia.
  Qed.

  Lemma guarded_at_body_with_condition path ep code pc n q :
    (n < pc)%positive →
    guarded_at_body f path blacklist ep code pc →
    guarded_at_body f (with_condition path n q) blacklist ep code pc.
  Proof.
    revert ep.
    elim code; clear code.
    - intros ep LT. exact id.
    - intros (g, j) code IH ep LT (-> & (i & Hi & Hij) & REC).
      split. 2: eauto.
      apply path_at_pc_with_condition.
      apply guarded_at_body_le in REC. clear -LT REC.
      generalize (pos_pred_le ep). Psatz.lia.
  Qed.

  Fixpoint translate_body_correct path ep pc acc WF pc' path' body :
    guarded_at_body f path blacklist ep (rev' acc) pc →
    translate_body pc path acc WF = inl (pc', path', body) →
    guarded_at_body f path' blacklist ep body pc'
    ∧ path_conditions_le path path'
    ∧ (wf_path_conditions f ep path → wf_path_conditions f ep path').
  Proof.
    Opaque pcond_and pcond_lit pcond_litN pcond_or.
    intros G.
    destruct WF as [ REC ].
    simpl. intros H.
    repeat match goal with
           | H: translate_body _ _ _ _ = inl _ |- _ =>
             specialize (λ ep X, translate_body_correct _ ep _ _ _ _ _ _ X H); clear H
           | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
           | H: check_forward_edge _ _ _ = inl _ |- _ => apply check_forward_edge_correct in H
           | H: inr _ = inl _ |- _ => inversion H
           | H: inl _ = inl _ |- _ => inversion H; clear H
           | H: ?a = ?b |- _ => subst a || subst b
           | H: match ?a with _ => _ end = inl _ |- _ => destruct a eqn:?
           end; auto.
    - { edestruct translate_body_correct as ( L & L' & L'').
        unfold rev'. rewrite <- rev_alt. simpl.
        eapply guarded_at_body_app. rewrite rev_alt.
        eapply guarded_at_body_with_condition; eassumption.
        eauto using guarded_at_body_with_condition.
        split. auto using path_at_pc_with_condition.
        refine (conj _ Logic.eq_refl).
        eexists. split. eauto. simpl. auto.
        intuition eauto using path_conditions_le_trans, with_condition_le.
        apply L'', wf_path_with_condition; auto.
        intros NR. apply H. intros R. apply NR.
        apply (reachable_n1 pc); auto.
        split. assumption. unfold successors. rw. reflexivity.
        apply (bounded_lt pc); auto. apply H. }

    - { edestruct translate_body_correct as ( L & L' & L'').
        unfold rev'. rewrite <- rev_alt. simpl.
        eapply guarded_at_body_app. rewrite rev_alt.
        eapply guarded_at_body_with_condition; eassumption.
        eauto using guarded_at_body_with_condition.
        split. auto using path_at_pc_with_condition.
        refine (conj _ Logic.eq_refl).
        eexists. split. eauto. simpl. auto.
        intuition eauto using path_conditions_le_trans, with_condition_le.
        apply L'', wf_path_with_condition; auto.
        intros NR. apply H. intros R. apply NR.
        apply (reachable_n1 pc); auto.
        split. assumption. unfold successors. rw. reflexivity.
        apply (bounded_lt pc); auto. apply H. }

    - { edestruct translate_body_correct as ( L & L' & L'').
        unfold rev'. rewrite <- rev_alt. simpl.
        eapply guarded_at_body_app. rewrite rev_alt.
        eapply guarded_at_body_with_condition; eassumption.
        eauto using guarded_at_body_with_condition.
        split. auto using path_at_pc_with_condition.
        refine (conj _ Logic.eq_refl).
        eexists. split. eauto. simpl. auto.
        intuition eauto using path_conditions_le_trans, with_condition_le.
        apply L'', wf_path_with_condition; auto.
        intros NR. apply H. intros R. apply NR.
        apply (reachable_n1 pc); auto.
        split. assumption. unfold successors. rw. reflexivity.
        apply (bounded_lt pc); auto. apply H. }

    - refine (conj G (conj (path_conditions_le_refl _) _)). exact id.

    - { edestruct translate_body_correct as ( L & L' & L'').
        unfold rev'. rewrite <- rev_alt. simpl.
        eapply guarded_at_body_app. rewrite rev_alt.
        eauto using guarded_at_body_with_condition.
        split.
        etransitivity. eapply path_at_pc_with_condition.
        2: eapply path_at_pc_with_condition.
        assumption. assumption.
        refine (conj _ Logic.eq_refl).
        eexists. split. eauto. simpl. auto.
        intuition eauto using path_conditions_le_trans, with_condition_le.
        apply L'', (wf_path_with_condition).
        intros NR.
        replace (path_at pc path) with pcondF. reflexivity. symmetry.
        apply H. intros R. apply NR.
        apply (reachable_n1 pc); auto.
        split. assumption. unfold successors. rw. simpl; auto.
        apply bounded_pcond_and.
        apply bounded_pcond_litN; auto.
        apply (bounded_lt pc); auto. apply H.
        apply (wf_path_with_condition); auto.
        intros NR.
        replace (path_at pc path) with pcondF. reflexivity. symmetry.
        apply H. intros R. apply NR.
        apply (reachable_n1 pc); auto.
        split. assumption. unfold successors. rw. simpl; auto.
        apply bounded_pcond_and.
        apply bounded_pcond_lit; auto.
        apply (bounded_lt pc); auto. apply H. }

    - refine (conj G (conj (path_conditions_le_refl _) _)). exact id.
  Qed.

  End TR_BODY.

  Fixpoint translate_outputs pc (acc: list (slot * ident)) (WF: Acc Pos.lt pc) :
    RTL.node * list (slot * ident) + exn :=
    let 'Acc_intro REC := WF in
    match f ! pc with
    | None => inr (NoInstrAt pc)
    | Some i =>
      match i with
      | RTL.Iload Mint8unsigned (Op.Aglobal x o) nil r pc1 =>
        match f ! pc1 with
        | None => inr (NoInstrAt pc1)
        | Some j => match j with
        | RTL.Ibuiltin (EF_vstore Mint8unsigned) (BA_addrglobal name ofs :: BA r' :: nil) BR_none pc2 =>
        if if Int.eq ofs Int.zero
        then if Pos.eqb r' r
        then check_volatile name
        else false else false
        then
          if match pc2 with xH => true | _ => false end
          then inr (IllegalInstruction pc i) else
          check_forward_edge pc pc2 (λ FWD,
            translate_outputs pc2 (((x, o), name) :: acc) (REC _ (pf FWD))
          )
          else inr (IllegalInstruction pc i)
        | _ => inr (IllegalInstruction pc1 j)
                    end
        end
      | _ => inl (pc, List.rev' acc)
      end
    end.

  Fixpoint translate_outputs_correct ep pc acc WF pc' ins :
    guarded_at_output f ep (rev' acc) pc →
    translate_outputs pc acc WF = inl (pc', ins) →
    guarded_at_output f ep ins pc'.
  Proof.
    intros G.
    destruct WF as [ REC ].
    simpl. intros H.
    repeat match goal with
           | H: false = true |- _ => inversion H
           | H: true = true |- _ => clear H
           | H: Int.eq _ _ = true |- _ => apply int_eq_true in H
           | H: check_volatile _ = true |- _ => apply check_volatile_true in H
           | H: _ ∧ _ |- _ => let K := fresh H in destruct H as [ H K ]
           | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
           | H: (if ?b then _ else false) = true |- _ => apply if_it_is_true in H || destruct b
           | H: check_forward_edge _ _ _ = inl _ |- _ => apply check_forward_edge_correct in H
           | H: inr _ = inl _ |- _ => inversion H
           | H: inl _ = inl _ |- _ => inversion H; clear H
           | H: ?a = ?b |- _ => subst a || subst b
           | H: match ?a with _ => _ end = inl _ |- _ => destruct a eqn:?
           | H: (_ =? _)%positive = true |- _ => apply Pos.eqb_eq in H
           end; auto.
    eapply translate_outputs_correct. 2: eassumption.
    revert G.
    unfold rev'. rewrite <- ! rev_alt. simpl.
    intros G. eapply guarded_at_output_app; eauto.

    eexists _, _, _.
    split. eassumption. split. eassumption.
    split. assumption.
    split.
    clear -Heqb. destruct n0; try Psatz.lia. discriminate.
    reflexivity.
  Qed.

  Definition check_fence (n: ident) : bool :=
    match List.find (λ d, let '(name, _) := d in Pos.eqb name n) defs with
    | Some (_, Gfun (External (EF_external q sg))) =>
      if string_dec q fence_ident then
      if signature_eq sg fence_sig then
      true
      else false else false
    | _ => false
    end.

  Definition translate_fence blacklist (pc: RTL.node) : _ + exn :=
    match f ! pc with
    | None => inr (NoInstrAt pc)
    | Some i =>
      match i with
      | RTL.Icall sg (inr n) nil r pc' =>
        if
        if signature_eq sg fence_sig then
        if check_fence n then
        Pos.eqb (pc' + 1) pc
        else false else false
        then inl (pc', PTree.set r tt blacklist)
        else inr (IllegalInstruction pc i)
      | _ => inr (IllegalInstruction pc i)
      end
    end.

  Definition translate_code : _ + exn :=
    match translate_inputs entrypoint (nil, PTree.empty _) (Plt_wf _) with
    | inr e => inr e
    | inl (pc, ins, bl) =>
    match translate_fence bl pc with
    | inr e => inr e
    | inl (pcf, bl) =>
    match translate_body bl pcf (PTree.set pcf pcondT (PTree.empty _)) nil (Plt_wf _) with
    | inr e => inr e
    | inl (pc', path, code) =>
    match translate_fence bl pc' with
    | inr e => inr e
    | inl (pcf', bl) =>
    match translate_outputs pcf' nil (Plt_wf _) with
    | inr e => inr e
    | inl (2, outs)%positive =>
      match f ! 2, f ! 1 with
      | Some (RTL.Iop (Op.Ointconst z) nil ret xH), Some (RTL.Ireturn (Some ret')) =>
        if if Int.eq z Int.zero
        then Pos.eqb ret ret' else false
        then inl (pcf, pc', path, ins, outs, code)
        else inr NoReturn
      | _, _ => inr NoReturn
      end
    | inl (pc'', _) => inr (InstructionAfterOutput pc'')
    end end end end end.

End TR_CODE.

Section ALL_POS_IN_RANGE.
  Local
  Open Scope positive_scope.
  Context (f: positive → bool) (lo: positive).

  Lemma apir_obligation p : lo < Pos.pred p → Pos.pred p < p.
  Proof. apply pos_pred_intro; intros; Psatz.lia. Qed.

  Fixpoint all_pos_in_range_rec (hi: positive) (H: Acc Pos.lt hi) : bool :=
    let 'Acc_intro REC := H in
    let p := Pos.pred hi in
    match is_forward_edge p lo with
    | left LT =>
      if f p
      then all_pos_in_range_rec p (REC _ (apir_obligation _ LT))
      else false
    | right LE => true
    end.

  Fixpoint all_pos_in_range_rec_correct hi H :
    all_pos_in_range_rec hi H = true →
    ∀ x, lo < x → x < hi → f x = true.
  Proof.
    destruct H as [ REC ].
    simpl. case (is_forward_edge _ _).
    - intros LT.
      destruct (f _) eqn: H. 2: discriminate.
      intros IH. generalize (all_pos_in_range_rec_correct _ _ IH). clear IH. intros IH.
      intros x Hlo Hhi.
      case (Pos.ltb_spec x (Pos.pred hi)). auto.
      intros LE.
      cut (x = Pos.pred hi). congruence.
      revert Hhi LE. clear. apply pos_pred_intro; intros; Psatz.lia.
    - intros GE _ x Hlo Hhi. exfalso. revert GE Hlo Hhi. clear.
      apply pos_pred_intro; intros; Psatz.lia.
  Qed.

  Definition all_pos_in_range hi : bool :=
    all_pos_in_range_rec hi (Plt_wf _).

  Lemma all_pos_in_range_correct hi :
    all_pos_in_range hi = true →
    ∀ x, lo < x → x < hi → f x = true.
  Proof. apply all_pos_in_range_rec_correct. Qed.

End ALL_POS_IN_RANGE.

Definition check_eloquence_at (f: RTL.code) (path: path_conditions) (x: RTL.node) : bool :=
  match successors f x with
  | nil => true
  | z :: nil =>
    let p := path_at x path in
    if bdd_leq p (path_at z path) then
    all_pos_in_range (λ y, pcond_disjoint p (path_at y path)) z x
    else false
  | z1 :: z2 :: nil =>
    let p := path_at x path in
    let p1 := pcond_and p (pcond_lit x) in
    let p2 := pcond_and p (pcond_litN x) in
    if bdd_leq p1 (path_at z1 path) then
    if bdd_leq p2 (path_at z2 path) then
    if all_pos_in_range (λ y, pcond_disjoint p1 (path_at y path)) z1 x then
    all_pos_in_range (λ y, pcond_disjoint p2 (path_at y path)) z2 x
    else false else false else false
  | _ => false
  end.

Definition check_eloquence (f: RTL.code) (path: path_conditions) (lo hi: RTL.node) : bool :=
  if all_pos_in_range (check_eloquence_at f path) lo (Pos.succ hi)
  then path_at lo path == pcondT
  else false.

Lemma check_eloquence_correct f path lo hi :
    check_eloquence f path lo hi = true →
    eloquent_path_conditions f path lo hi.
Proof.
  unfold check_eloquence.
  destruct (all_pos_in_range _ _ _) eqn: H. 2: discriminate.
  generalize (all_pos_in_range_correct _ _ _ H). clear H. intros H.
  refine (conj _).
  intros x Hlo Hhi.
  generalize (H x Hlo (proj2 (Pos.lt_succ_r _ _) Hhi)). clear.
  unfold check_eloquence_at.
  destruct (successors _ _) as [ | z1 [ | z2 [ | ? ? ] ] ].
  easy.
  case (bdd_leq _ _). 2: discriminate.
  intros H. split. reflexivity. apply all_pos_in_range_correct, H.
  case (bdd_leq _ _). 2: discriminate.
  case (bdd_leq _ _). 2: discriminate.
  case (all_pos_in_range _ z1 _) eqn: H. 2: discriminate.
  intros H'. repeat (split; [ reflexivity | ]).
  split. apply all_pos_in_range_correct, H.
  apply all_pos_in_range_correct, H'.
  discriminate.
Qed.

Definition translate_function (f: RTL.function) : RTLC.function + exn :=
    let 'RTL.mkfunction sg params ssz code ep := f in
    match signature_eq sg signature_main with
    | right _ => inr WrongSig
    | left Hsg =>
    match params with
    | _ :: _ => inr WrongParams
    | nil =>
    match translate_code ep code with
    | inr e => inr e
    | inl (anfang, ende, path, ins, outs, gcode) =>
      if check_eloquence code path ende anfang
      then inl (RTLC.mkfunction ssz ins outs gcode)
      else inr NotEloquent
    end
    end
    end.

Lemma check_fence_true n :
  check_fence n = true →
  ∃ pre post,
    ¬ In n (map fst (rev pre)) ∧
    defs = pre ++ (n, Gfun (External (EF_external fence_ident fence_sig))) :: post.
Proof.
  unfold check_fence.
  match goal with
  | |- appcontext[ find ?f ?m ] => set (q:= f)
  end.
  generalize (findP q defs).
  destruct (find _ _) as [ (?, [ [| ef ] | ?]) | ]; try discriminate.
  intros (pre & post & H & EQ & NE).
  destruct ef; try discriminate.
  destruct string_dec. 2: discriminate.
  destruct signature_eq. 2: discriminate.
  intros _.
  exists pre, post.
  split.
  intros K. rewrite in_map_iff in K. destruct K as ((n' & m) & Hm & K).
  rewrite <- in_rev in K.
  specialize (NE _ K). unfold q in NE. simpl in Hm. subst n'.
  rewrite Pos.eqb_refl in NE. discriminate.
  unfold q in EQ. apply Pos.eqb_eq in EQ.
  rewrite H. repeat f_equal; assumption.
Qed.

Lemma translate_fence_correct {f bl pc pc' bl'} :
  translate_fence f bl pc = inl (pc', bl') →
  pc = (pc' + 1)%positive ∧
  fence_at f bl' pc' ∧
  bl_le bl bl'.
Proof.
  unfold translate_fence.
  repeat match goal with
  | H : ∃ a, _ |- _ => let b := fresh a in destruct H as [b H]
  | |- appcontext[ signature_eq _ _ ] =>
    case signature_eq; [ intros -> | discriminate ]
  | |- appcontext[ Pos.eqb _ _ ] =>
    case (Pos.eqb_spec _ _); [ intros ? | discriminate ]
  | |- appcontext[ check_fence ?n ] =>
    generalize (check_fence_true n);
      destruct (check_fence _); [ intros [ ef ? ]; auto | discriminate ]
  | |- match ?x with _ => _ end = inl _ → _ =>
    destruct x eqn:?; try discriminate
  end.
  intros X; inversion X; clear X.
  repeat match goal with H : ?a = ?b |- _ => subst a || subst b end.
  apply (conj Logic.eq_refl). split.
  eexists _, _, _, _. split. 2: eauto.
  unfold is_blacklisted. rewrite PTree.gss. reflexivity.
  apply bl_le_set.
Qed.

Lemma fence_at_w bl {f bl' pc}:
  fence_at f bl pc →
  bl_le bl bl' →
  fence_at f bl' pc.
Proof.
  intros (pre & ef & post & r & BL & H & IN) LE.
  exists pre, ef, post, r; split; eauto.
Qed.

Lemma translate_function_correct f f' :
  translate_function f = inl f' →
  ∃ pth, guarded_function pth f f'.
Proof.
  unfold translate_function.
  destruct f as [ sg params ssz code ep ].
  case signature_eq. 2: discriminate. intros Hg.
  case params. 2: discriminate.
  destruct (translate_code _ _) as [ (((((anfang & ende) & path) & ins) & outs) & cod) | e ] eqn: H.
  2: discriminate.
  generalize (check_eloquence_correct code path ende anfang).
  case (check_eloquence _ _). 2: discriminate.
  intros Helo. specialize (Helo Logic.eq_refl).
  intros K. inv K.
  exists path.
  red.
  repeat refine (conj Logic.eq_refl _). simpl.
  unfold translate_code in H.
  repeat match goal with
         | H: ?a = ?b |- _ => subst a || subst b
         | H: Int.eq _ _ = true |- _ => apply int_eq_true in H
         | H: Pos.eqb _ _ = true |- _ => apply Pos.eqb_eq in H
         | H: translate_fence _ _ _ = inl _ |- _ =>
           apply translate_fence_correct in H
         | H: translate_inputs _ _ _ _ = inl _ |- _ =>
           eapply translate_inputs_correct in H; [ | reflexivity]
         | H: _ ∧ _ |- _ => let K := fresh H in destruct H as [ H K ]
         | H: (if ?b then _ else false) = true |- _ => apply if_it_is_true in H
         | H: inr _ = inl _ |- _ => inversion H
         | H: inl _ = inl _ |- _ => inversion H; clear H
         | H: match ?b with _ => _ end = inl _ |- _ => destruct b eqn:?
         end.
  match goal with
  | H : translate_body _ _ _ _ _ _ = inl _ |- _ =>
    generalize (translate_body_correct code _ _ _ _ nil _ _ _ _ Logic.eq_refl H)
  end.
  intros (G & LE & WF).
  eexists _, _, _, _.
  split. eapply guarded_at_input_w. 2: eassumption. eassumption.
  split. eassumption.
  split. apply G.
  split. eassumption.
  split. apply WF.
    split.
      intros m. unfold path_at. rewrite PTree.gss. reflexivity.
      intros z NR. unfold path_at. rewrite PTree.gso, PTree.gempty.
        reflexivity. intros ->. apply NR. apply rt_refl.
      intros pc. unfold path_at. rewrite PTree.gsspec.
      case peq. intros ? ? (). intros _. rewrite PTree.gempty. intros ? ().
  split. exact Helo.
  split. eapply translate_outputs_correct; eauto. reflexivity.
  red. eauto.
Qed.

Definition errmsg_of_exn (e: exn) : errmsg :=
  match e with
  | NoInstrAt n => MSG "No instruction at " :: POS n :: nil
  | BackEdge x y => MSG "Back edge from " :: POS x :: MSG " to " :: POS y :: nil
  | BlacklistedRegister => msg "Blacklisted register"
  | IllegalInstruction n _ => MSG "Illegal instruction at " :: POS n :: nil
  | InstructionAfterOutput n => MSG "Instruction after output at " :: POS n :: nil
  | NoReturn => msg "No return"
  | WrongSig => msg "Wrong signature"
  | WrongParams => msg "Wrong parameter list"
  | TooManyFunctions => msg "Too many functions"
  | DuplicateIONames x => MSG "Redundant IO name " :: POS x :: nil
  | NotEloquent => msg "Not eloquent"
  end.

Definition translate_fundef (fd: RTL.fundef) : res (fundef RTLC.function) :=
  match fd with
  | External ef => OK (External ef)
  | Internal fn =>
    match translate_function fn with
    | inr e => Error (errmsg_of_exn e)
    | inl fn' => OK (Internal fn')
    end
  end.

End DEFS.

Definition transf_program (p: RTL.program) : res (RTLC.program) :=
  let defs := rev' (prog_defs p) in
  match List.find (λ d, let '(name, gd) := d in Pos.eqb name (prog_main p)) defs with
  | None => Error (msg "No main function")
  | Some (_, Gvar _) => Error (msg "The main function is a variable")
  | Some (_, Gfun (External _)) => Error (msg "Main function is external")
  | Some (_, Gfun (Internal mainf)) =>
    transform_partial_program (translate_fundef defs) p
  end.

Section SIMULATION.
  Import Globalenvs.
  Import Memory.
  Import Values.
  Import Smallstep.

  Context (p: RTL.program) (p': RTLC.program).
  Hypothesis TR': transf_program p = OK p'.
  Let defs := rev' (prog_defs p).

  Corollary TR :
    transform_partial_program (translate_fundef defs) p = OK p'.
  Proof.
    revert TR'. unfold transf_program.
    case find. 2: discriminate.
    intros (_, [ [ ? | ? ] | ? ] ); auto; discriminate.
  Qed.

  Lemma public_symbol_preserved s :
   Genv.public_symbol (Genv.globalenv p') s =
   Genv.public_symbol (Genv.globalenv p) s.
  Proof.
    eauto using Genv.public_symbol_transf_partial, TR.
  Qed.

  Lemma symbol_address_preserved s o :
    Senv.symbol_address (Genv.globalenv p) s o = Senv.symbol_address (Genv.globalenv p') s o.
  Proof.
    unfold Senv.symbol_address. simpl.
    erewrite <- Genv.find_symbol_transf_partial by apply TR.
    reflexivity.
  Qed.

  Lemma genv_symbol_address_preserved s o :
    Genv.symbol_address (Genv.globalenv p) s o = Genv.symbol_address (Genv.globalenv p') s o.
  Proof.
    unfold Genv.symbol_address. simpl.
    erewrite <- Genv.find_symbol_transf_partial by apply TR.
    reflexivity.
  Qed.

  Section MATCH_REGS.
    Context (blacklist: PTree.t unit).

    Definition match_regs (rs rs': RTL.regset) : Prop :=
      ∀ r,
        is_blacklisted blacklist r = false →
        Val.lessdef (rs # r) (rs' # r).

    Definition match_regs_refl rs : match_regs rs rs :=
      λ r _, Val.lessdef_refl _.

    Lemma match_regs_set_bl rs rs' r v :
      is_blacklisted blacklist r = true →
      match_regs rs rs' →
      match_regs (rs # r <- v) rs'.
    Proof.
      intros BL M r' Hr'.
      rewrite Regmap.gso. apply M, Hr'.
      congruence.
    Qed.

    Lemma match_regs_set rs rs' r v  v':
      match_regs rs rs' →
      Val.lessdef v v' →
      match_regs (rs # r <- v) (rs' # r <- v').
    Proof.
      intros M V r' Hr'.
      rewrite ! Regmap.gsspec.
      case peq; auto.
    Qed.

    Lemma lessdef_not_blacklisted args rs rs' :
      match_regs rs rs' →
      are_not_blacklisted blacklist args = true →
      Val.lessdef_list rs ## args rs' ## args.
    Proof.
      intros LE.
      unfold are_not_blacklisted. rewrite forallb_forall.
      elim args; clear args. constructor.
      intros r args IH BL. constructor.
      apply LE. specialize (BL _ (or_introl Logic.eq_refl)).
      apply negb_true_iff in BL. exact BL.
      apply IH. simpl in *. eauto.
    Qed.

  End MATCH_REGS.

  Definition match_state (x: RTL.state) (x': RTLC.state) : Prop :=
    match x with
    | RTL.State stk f sp pc rs m =>
      stk = nil ∧
        match x' with
        | RTLC.InitState _ _ => False
        | RTLC.InputState io ins sp' ssz body m' outs =>
          ∃ pth,
          sp' = sp ∧
          ssz = RTL.fn_stacksize f ∧
          Mem.extends m m' ∧
          ∃ ep, wf_path_conditions (RTL.fn_code f) ep pth ∧
          ∃ bl bl' π',
          match io with
          | Some ((x, o), v) =>
            ∃ r pc2,
    (RTL.fn_code f) ! pc = Some (RTL.Istore Mint8unsigned (Op.Aglobal x o) nil r pc2) ∧
    is_blacklisted bl r = true ∧
    ¬ In (x, o) (map fst ins) ∧
    1 < pc2 ∧
    guarded_at_input defs (RTL.fn_code f) bl pc2 ins (ep + 1) ∧
    rs # r = v
            | None => guarded_at_input defs (RTL.fn_code f) bl pc ins (ep + 1)
            end ∧
            fence_at defs (RTL.fn_code f) bl ep ∧
            match_regs bl rs (Regmap.init Vundef) ∧
            eloquent_path_conditions (RTL.fn_code f) pth (π' + 1) ep ∧
            guarded_at_body (RTL.fn_code f) pth bl ep body (π' + 1) ∧
            fence_at defs (RTL.fn_code f) bl' π' ∧
            guarded_at_output defs (RTL.fn_code f) π' outs 2 ∧
            guarded_at_end (RTL.fn_code f)

        | RTLC.State sp' ssz body pcm rs' m' outs =>
          ∃ pth,
          sp' = sp ∧
          ssz = RTL.fn_stacksize f ∧
          Mem.extends m m' ∧
          ∃ ep, wf_path_conditions (RTL.fn_code f) ep pth ∧
          ∃ bl bl' π',
            match body with
            | nil => True
            | (g, _) :: _ => eval_pcond pcm g = true ∧
                             match_regs bl rs rs' ∧
                             reachable (RTL.fn_code f) ep pc
                          ∧ eloquent_path_conditions (RTL.fn_code f) pth (π' + 1) ep
                          ∧ ∀ q, In q pcm → pc < q
            end ∧
            guarded_at_body (RTL.fn_code f) pth bl pc body (π' + 1) ∧
            fence_at defs (RTL.fn_code f) bl' π' ∧
            guarded_at_output defs (RTL.fn_code f) π' outs 2 ∧
            guarded_at_end (RTL.fn_code f)

        | RTLC.OutputState io outs sp' ssz m' =>
          sp' = sp ∧
          ssz = RTL.fn_stacksize f ∧
          Mem.extends m m' ∧
          match io with
          | None => guarded_at_output defs (RTL.fn_code f) pc outs 2
          | Some (v, dst) =>
             ∃ r pc2,
             Val.lessdef (Val.load_result Mint8unsigned (rs # r)) v ∧
             declared_volatile defs dst ∧
             (RTL.fn_code f) ! pc = Some (RTL.Ibuiltin (EF_vstore Mint8unsigned)
                                         (BA_addrglobal dst Int.zero :: BA r :: nil) BR_none pc2) ∧
             1 < pc2 ∧
             guarded_at_output defs (RTL.fn_code f) pc2 outs 2
           end ∧
          guarded_at_end (RTL.fn_code f)

        | RTLC.FinishingState sp' ssz m' =>
          sp' = sp ∧
          ssz = RTL.fn_stacksize f ∧
          Mem.extends m m' ∧
          pc = xH ∧
          ∃ r, (RTL.fn_code f) ! xH = Some (RTL.Ireturn (Some r)) ∧ rs # r = Vint Int.zero
        | RTLC.InputFenceState _ _ _ _ _
        | RTLC.PostInputState _ _ _ _ _
        | RTLC.PreOutputState _ _ _ _
        | RTLC.OutputFenceState _ _ _ _
        | RTLC.FinalState => False
        end

    | RTL.Callstate stk (Internal f) args m =>
      stk = nil ∧
      ∃ f' pth, guarded_function defs pth f f' ∧ x' = RTLC.InitState f' m
    | RTL.Callstate stk (External ef) args m =>
      ∃ dst f sp pc rs,
      stk = RTL.Stackframe dst f sp pc rs :: nil ∧
      args = nil ∧
      match x' with
      | RTLC.InputFenceState sp' ssz body m' outs =>
        sp' = sp ∧
        ssz = RTL.fn_stacksize f ∧
        Mem.extends m m' ∧
        ∃ pth bl bl' π',
          is_blacklisted bl dst = true ∧
          match_regs bl rs (Regmap.init Vundef) ∧
          wf_path_conditions (RTL.fn_code f) pc pth ∧
          eloquent_path_conditions (RTL.fn_code f) pth (π' + 1) pc ∧
          guarded_at_body (RTL.fn_code f) pth bl pc body (π' + 1) ∧
          fence_at defs (RTL.fn_code f) bl' π' ∧
          guarded_at_output defs (RTL.fn_code f) π' outs 2 ∧
          guarded_at_end (RTL.fn_code f) ∧
          ef = EF_external fence_ident fence_sig
      | RTLC.OutputFenceState sp' ssz m' outs =>
        sp' = sp ∧
        ssz = RTL.fn_stacksize f ∧
        Mem.extends m m' ∧
        guarded_at_output defs (RTL.fn_code f) pc outs 2 ∧
        guarded_at_end (RTL.fn_code f) ∧
        ef = EF_external fence_ident fence_sig
      | _ => False
      end

    | RTL.Returnstate stk v m =>
      match x' with
      | RTLC.FinalState => stk = nil ∧ v = Vint Int.zero
      | RTLC.PostInputState sp ssz body m' outs =>
        Mem.extends m m' ∧
        ∃ dst f pc rs,
          ssz = RTL.fn_stacksize f ∧
          stk = RTL.Stackframe dst f sp pc rs :: nil ∧
        ∃ pth bl bl' π',
          is_blacklisted bl dst = true ∧
          match_regs bl rs (Regmap.init Vundef) ∧
          wf_path_conditions (RTL.fn_code f) pc pth ∧
          eloquent_path_conditions (RTL.fn_code f) pth (π' + 1) pc ∧
          guarded_at_body (RTL.fn_code f) pth bl pc body (π' + 1) ∧
          fence_at defs (RTL.fn_code f) bl' π' ∧
          guarded_at_output defs (RTL.fn_code f) π' outs 2 ∧
          guarded_at_end (RTL.fn_code f)
      | RTLC.PreOutputState sp ssz m' outs =>
        Mem.extends m m' ∧
        ∃ dst f pc rs,
          ssz = RTL.fn_stacksize f ∧
          stk = RTL.Stackframe dst f sp pc rs :: nil ∧
          guarded_at_output defs (RTL.fn_code f) pc outs 2 ∧
          guarded_at_end (RTL.fn_code f)
      | _ => False
      end
    end%positive.

  Lemma guarded_function_stacksize pth f f' :
    guarded_function defs pth f f' →
    RTLC.fn_stacksize f' = RTL.fn_stacksize f.
  Proof. intros H; symmetry; apply H. Qed.

  Lemma run_disabled_steps f path bl ep body pc pcm :
    guarded_at_body f path bl ep body pc →
    ∃ body' pc',
      guarded_at_body f path bl pc' body' pc ∧
      (pc' <= ep)%positive ∧
      match body' with
      | nil => True
      | (g, _) :: body' => eval_pcond pcm g = true
      end ∧
      (∀ q, pc' < q → q <= ep → eval_pcond pcm (path_at q path) = false)%positive ∧
      ∀ sp ssz rs m outs,
        star RTLC.step (Genv.globalenv p')
             (RTLC.State sp ssz body pcm rs m outs)
             nil
             (RTLC.State sp ssz body' pcm rs m outs).
  Proof.
    revert ep.
    elim body; clear body.
    - intros ? ->. exists nil, pc. simpl. intuition eauto using star_refl, Pos.le_refl; Psatz.lia.
    - intros (g, j) body IH ep Hg.
      destruct (eval_pcond pcm g) eqn: H.
      + exists ((g, j) :: body), ep.
        intuition eauto using star_refl, Pos.le_refl; Psatz.lia.
      + destruct Hg as (Hg & (i & Hi & Hij) & REC).
        specialize (IH _ REC).
        destruct IH as (body' & pc' & REC' & REACH & Hlast & Hfalse & STEPS).
        exists body', pc'.
        split. exact REC'.
        split. eapply Pos.le_trans. eassumption. apply pos_pred_le.
        split. exact Hlast.
        split. intros q Hq Hq'.
        case (Pos.leb_spec q (Pos.pred ep)). auto.
        intros LT. generalize (pos_ge_pred ep q LT Hq'). intros <-. congruence.
        intros sp ssz rs m outs.
        eapply star_step. 2: eauto.
        simpl. rw. eauto. reflexivity.
  Qed.

  Theorem simulation :
    forward_simulation (RTL.semantics p) (RTLC.semantics p').
  Proof.
    Opaque PTree.get.
    refine (forward_simulation_plus
              (RTL.semantics p) (RTLC.semantics p')
              public_symbol_preserved
              match_state
              _
              _
              _).
    - intros s INIT; inv INIT.
      generalize TR'.
      unfold transf_program.
      match goal with
      | |- appcontext[ find ?f ?m ] => set (q:= f)
      end.
      fold defs.
      generalize (findP q defs).
      destruct (find q defs) as [ (n, [ [ef | fn ] | gv ]) | ];
        try discriminate.
    intros (pre & post & Q & K & L). apply Pos.eqb_eq in K. subst n.
    unfold defs in Q.
    apply rev'P in Q. rewrite rev_app_distr in Q. simpl in Q.
    rewrite <- app_assoc in Q.
    generalize (Genv.find_funct_ptr_exists_2 p _ _ _ _ Q).
    intros (b' & Hb' & Hf).
    { clear -L. rewrite in_map_iff. intros ((n, gd) & X & Y).
      simpl in  X. subst n. apply in_rev in Y.
      specialize (L _ Y). simpl in L. rewrite Pos.eqb_refl in L. discriminate. }
    intros _.
    unfold ge in *.
      repeat
      match goal with
      | H : ?a = ?b |- _ => subst a || subst b
      | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K; inversion K; clear K
      | H : Genv.init_mem _ = _ |- _ =>
        eapply Genv.init_mem_transf_partial in H; [ | apply TR ]
      | H : Genv.find_symbol _ _ = _ |- _ =>
        erewrite <- Genv.find_symbol_transf_partial in H; [ | apply TR ]
      | H : Genv.find_funct_ptr _ _ = _ |- _ =>
        generalize (Genv.find_funct_ptr_transf_partial _ _ TR _ H);
          clear H;
          intros (f' & H & ?)
      end.
      simpl in *.
      destruct (translate_function _ _) eqn: Htr; inversion H1; clear H1. subst f'.
      eexists. split.
      eexists m0, _, _. split. eauto.
      split. erewrite transform_partial_program_main by (apply TR). eauto.
      eauto.
      split. reflexivity.
      destruct (translate_function_correct _ _ _ Htr). eauto.

    - simpl.
      intros s s' r M K; inv K.
      destruct s'; simpl in M;
      repeat match goal with
             | H : False |- _ => destruct H
             | H : ?a = ?b |- _ => subst a || subst b
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
             | H : nil = _ :: _ |- _ => discriminate
             | H : Vint _ = Vint _ |- _ => inversion H; clear H
             end;
      red; eauto.

    - simpl.
      intros s1 tr s1' STEP s2 M.
      destruct s1 as [ stk f sp pc rs m | stk [f | ef] sp m | stk v m ];
      simpl in M;
      repeat match goal with
             | H : False |- _ => destruct H
             | H : ?a = ?b |- _ => subst a || subst b
             | H : Some _ = Some _ |- _ => inversion H; clear H
             | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
             | H : _ :: _ = nil |- _ => discriminate
             end.

      Focus 2.
      (* Callstate / Internal *)
      inv STEP.
      eexists. split.
      apply plus_one. simpl. erewrite guarded_function_stacksize by eauto.
      rw. eauto.
      unfold guarded_function in *.
      repeat match goal with
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
             end.
      red. rw. eauto 18 using match_regs_refl, Mem.extends_refl.

      Focus 2.
      (* Callstate / External *)
      inv STEP.
      destruct s2;
      repeat match goal with
             | H : False |- _ => destruct H
             | H : ?a = ?b |- _ => subst a || subst b
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
             | H : Events.external_call _ _ _ _ _ _ _ |- _ =>
               eapply Events.external_call_symbols_preserved in H;
                 [ | eapply Genv.find_symbol_transf_partial, TR
                   | eapply public_symbol_preserved
                   | eapply Genv.find_var_info_transf_partial, TR ]
      | H : Events.external_call _ _ _ _ _ _ _ |- _ =>
        apply fence_sem in H
             end.
      eexists. split. apply plus_one. simpl. eauto.
      simpl. eauto 19.
      eexists. split. apply plus_one. simpl. eauto.
      simpl. eauto 9.

      Focus 2.
      (* Returnstate *)
      inversion STEP; clear STEP; subst.
      destruct s2;
      repeat match goal with
             | H : False |- _ => destruct H
             | H : ?a = ?b |- _ => subst a || subst b
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
             | H : _ :: _ = _ :: _ |- _ => inversion H; clear H
             | H : _ :: _ = nil |- _ => inversion H
             end.
      eexists. split. apply plus_one. simpl. eauto.
      apply (conj Logic.eq_refl).
      eexists.
      repeat apply (conj Logic.eq_refl).
      split. eassumption.
      eexists. split. eassumption.
      eexists _, _, _.
      split. 2: eauto.
      match goal with |- match ?x with _ => _ end => destruct x as [| (?, ?) ?] end.
      easy.
      split. destruct M6 as (-> & ?). apply M4.
      split. apply match_regs_set_bl; auto.
      split. apply reachable_refl.
      split. assumption.
      intros ? ().
      
      eexists. split. apply plus_one. simpl. eauto.
      simpl. eauto 7.

      (* State *)
      destruct s2 as
          [
          | io ins sp' ssz body m' outs
          | |
          | sp' ssz body pcm rs' m' outs
          | |
          | io outs sp' ssz m' | sp' ssz m' | ];
      simpl in M;
      repeat match goal with
             | H : guarded_at_input _ _ _ _ _ |- _ => red in H; simpl in H
             | H : False |- _ => destruct H
             | H : ?a = ?b |- _ => subst a || subst b
             | H : Some _ = Some _ |- _ => inversion H; clear H
             | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [ b H ]
             | H : _ :: _ = nil |- _ => discriminate
             | H : _ ! xH = Some _ |- _ => inv STEP
             end.
      (* Last step *)
      Focus 4.
      match goal with
      | M: Mem.free _ _ _ _ = Some _,
        E: Mem.extends _ _ |- _ =>
        generalize (Mem.free_parallel_extends _ _ _ _ _ _ E M); clear E M;
          intros (? & M & E)
      end.
      eexists. split. apply plus_one. simpl. eauto 6. simpl. eauto.

      destruct io as [ ((x, o), v) | ].
      (* Running input *)
      {
        repeat match goal with
        | H : ∃ a, _ |- _ => let b := fresh a in destruct H as (b, H)
        | H : _ ∧ _ |- _ => destruct H
        end.
        inv STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : Some _ = Some _ |- _ => inversion H; clear H
                 | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
                 | H : Op.eval_addressing _ _ _ _ = Some _ |- _ => simpl in H
                 | H : appcontext[ Genv.symbol_address (Genv.globalenv p) ?x ?o ] |- _ =>
                   rewrite (genv_symbol_address_preserved x o) in H
        | H: Mem.extends _ _,
           K: Mem.storev _ _ _ _ = Some _ |- _ =>
          generalize
        (Mem.storev_extends _ _ _ _ _ _ _ _ H K (Val.lessdef_refl _) (Val.lessdef_refl _)); clear H K; intros (? & H & K)
                 end.
        eexists. split. apply plus_one. simpl.
        destruct ins as [ | (?, ?) ]; eauto.
        simpl. eauto 18.
      }

      destruct ins as [ | ((x, o), src) ins ].
      (* Fence after inputs *)
      {
        simpl in *. subst pc.
        repeat
        match goal with
        | H : fence_at _ _ _ ep |- _ => unfold fence_at in H
        | H : ∃ a, _ |- _ => let b := fresh a in destruct H as (b, H)
        | H : _ ∧ _ |- _ => destruct H
        end.
        match goal with
        | H : defs = _, K : ¬ In _ _ |- _ =>
          unfold defs in H; apply rev'P in H;
            rewrite rev_app_distr in H;
            simpl in H; rewrite <- app_assoc in H;
              generalize (Genv.find_funct_ptr_exists_2 p _ _ _ _ H K)
        end.
        intros (b & Hb & Hef).
        inversion STEP; clear STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : Some _ = Some _ |- _ => inversion H; clear H
                 | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
                 | H : RTL.find_function _ _ _ = _ |- _ =>
                   simpl in H;
                     rewrite Hb, Hef in H
                 end.
        destruct (Genv.find_funct_ptr_transf_partial _ _ TR _ Hef)
          as (ef' & Hef' & K).
        erewrite <- Genv.find_symbol_transf_partial in Hb by exact TR.
        inv K.
        eexists. split. apply plus_one. simpl. eauto.
        simpl. eauto 25.
      }

        { (* Some input *)
          match goal with
          | M : guarded_at_input _ _ _ _ _ _ |- _ => destruct M as (pc1 & r & pc2 & Hi & Hpc1 & BL & NR & V & LT & Hins)
          end.
          destruct V as (pre & gv & post & Hgv & V & Hdefs).
          unfold defs in Hdefs.
          apply rev'P in Hdefs.
          rewrite rev_app_distr in Hdefs.
          simpl in Hdefs.
          rewrite <- app_assoc in Hdefs.
          generalize (Genv.find_var_exists_2 _ _ _ _ _ Hdefs Hgv).
          intros (b' & Hb' & Hgv').
          erewrite <- Genv.find_symbol_transf_partial in Hb' by exact TR.
          erewrite <- Genv.find_var_info_transf_partial in Hgv' by exact TR.
          inv STEP;
            repeat match goal with
             | H : ?a = ?b |- _ => subst a || subst b
             | H : Some _ = Some _ |- _ => inversion H; clear H
             | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
             | H : Events.volatile_load _ _ _ _ _ _ _ |- _ => inversion H; clear H
             | H : appcontext[ Senv.symbol_address _ _] |- _ =>
               rewrite symbol_address_preserved in H
             | H : Events.external_call _ _ _ _ _ _ _ |- _ =>
               eapply Events.external_call_symbols_preserved in H;
                 [ | eapply Genv.find_symbol_transf_partial, TR
                   | eapply public_symbol_preserved
                   | eapply Genv.find_var_info_transf_partial, TR ];
                 inversion H; clear H
             | H : Events.eval_builtin_arg _ _ _ _ _ _ |- _ => inversion H; clear H
             | H : list_forall2 _ _ _ |- _ => inversion H; clear H
             | H : Events.eval_builtin_args _ _ _ _ _ _ |- _ => inversion H; clear H
             end;
          match goal with
          | H : Senv.symbol_address _ ?x _ = Vptr _ _ |- _ =>
            unfold Senv.symbol_address in H;
              destruct (Senv.find_symbol _ x) eqn: ?; inversion H; clear H; subst
          end.
          match goal with
          | X: Senv.find_symbol _ _ = Some _,
               Y: Senv.find_symbol _ _ = Some _ |- _ =>
            generalize (Senv.find_symbol_injective _ _ _ X Y); clear Y; intro; subst
          end.
          eexists. split. apply plus_one.
          eexists _, _, _.
          repeat (split; [ eassumption | ]). split. reflexivity.
          split. inv H2; easy. eauto.
          simpl.
          apply (conj Logic.eq_refl).
          eexists.
          repeat apply (conj Logic.eq_refl).
          split. assumption.
          eexists. split. eassumption.
          eexists _, _, _. split.
          eexists _, _.
          repeat (split; [ eassumption | ]). apply Regmap.gss.
          split. assumption.
          split. apply match_regs_set_bl; auto.
          eauto.

          exfalso.
          match goal with
          | X: Genv.find_symbol _ _ = Some _,
               Y: Senv.find_symbol _ _ = Some _ |- _ =>
            simpl in Y; unfold RTLC.fundef in *; rewrite Y in X; inversion X; clear X;
              subst
          end.
          match goal with
          | H : appcontext[ Senv.block_is_volatile ] |- _ => revert H
          end.
          simpl. unfold Genv.block_is_volatile. rewrite Hgv'. congruence.
        }

      Focus 2.
      destruct io as [ (v, dst) | ].
      { (* Running output *)
        repeat
        match goal with
        | H: ∃ a, _ |- _ => let b := fresh a in destruct H as [b H]
        | H: _ ∧ _ |- _ => destruct H
        end.
        inv STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : Some _ = Some _ |- _ => inversion H; clear H
                 | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
             | H : Events.volatile_store _ _ _ _ _ _ _ _ |- _ => inversion H; clear H
             | H : Events.eval_builtin_args _ _ _ _ _ _ |- _ => inversion H; clear H
             | H : list_forall2 _ nil _ |- _ => inversion H; clear H
             | H : list_forall2 _ (_ :: _) _ |- _ => inversion H; clear H
             | H : Events.eval_builtin_arg _ _ _ _ _ _ |- _ => inversion H; clear H
             | H : appcontext[ Senv.symbol_address _ _ ] |- _ => rewrite symbol_address_preserved in H
             | H : Events.external_call _ _ _ _ _ _ _ |- _ =>
               eapply Events.external_call_symbols_preserved in H;
                 [ | eapply Genv.find_symbol_transf_partial, TR
                   | eapply public_symbol_preserved
                   | eapply Genv.find_var_info_transf_partial, TR ];
                 inversion H; clear H
             end;
          match goal with
          | H : Vptr _ _ = Senv.symbol_address _ ?x _ |- _ =>
            unfold Senv.symbol_address in H;
              destruct (Senv.find_symbol _ x) eqn: ?; inversion H; clear H; subst
          end.
          match goal with
          | X: Senv.find_symbol _ _ = Some _,
               Y: Senv.find_symbol _ _ = Some _ |- _ =>
            generalize (Senv.find_symbol_injective _ _ _ X Y); clear Y; intro; subst
          end.
          eexists. split. apply plus_one.
        eexists _, _.
        repeat (split; [ eassumption || reflexivity | ]). split. 2: reflexivity.
        inv H; eauto.
        destruct (rs # _); try discriminate; inv H7.
        simpl. eauto 7.

        exfalso.
        match goal with H: declared_volatile _ _ |- _ =>
                        destruct H as (pre & gv & post & Hgv & V & Hdefs)
        end.
        unfold defs in Hdefs.
        apply rev'P in Hdefs.
        rewrite rev_app_distr in Hdefs.
        simpl in Hdefs.
        rewrite <- app_assoc in Hdefs.
        generalize (Genv.find_var_exists_2 _ _ _ _ _ Hdefs Hgv).
        intros (b' & Hb' & Hgv').
        erewrite <- Genv.find_symbol_transf_partial in Hb' by exact TR.
        erewrite <- Genv.find_var_info_transf_partial in Hgv' by exact TR.
          match goal with
          | X: Genv.find_symbol _ _ = Some _,
               Y: Senv.find_symbol _ _ = Some _ |- _ =>
            simpl in Y; unfold RTLC.fundef in *; rewrite Y in X; inversion X; clear X;
              subst
          end.
          match goal with
          | H : appcontext[ Senv.block_is_volatile ] |- _ => revert H
          end.
          simpl. unfold Genv.block_is_volatile. rewrite Hgv'. congruence.
      }

      destruct outs as [ | ((x, o), dst) outs ].
      { (* No output *)
        unfold guarded_at_output in  *. subst pc.
        destruct M as (r & Hr & Hret).
        inv STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : Some _ = Some _ |- _ => inversion H; clear H
                 | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
                 | H : Op.eval_operation _ _ _ _ _ = _ |- _ => simpl in H
                 end.
        eexists. split. apply plus_one. simpl. eauto.
        simpl. eauto 8 using Regmap.gss.
      }

      { (* Ready for an output *)
        match goal with
        | M : guarded_at_output _ _ _ _ _ |- _ => destruct M as (pc1 & r & pc2 & Hr & Ho & V & LT & Hout)
        end.
        inv STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : Some _ = Some _ |- _ => inversion H; clear H
                 | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
             | H : Op.eval_addressing _ _ _ _ = Some _ |- _ => simpl in H
             | H : appcontext[ Genv.symbol_address (Genv.globalenv p) ?x ?o ] |- _ =>
               rewrite (genv_symbol_address_preserved x o) in H
        | H: Mem.extends _ _, L: Mem.loadv _ _ _ = Some _ |- _ =>
            generalize (Mem.loadv_extends _ _ _ _ _ _ H L (Val.lessdef_refl _));
              clear L; intros (? & L & ?)
                 end.
        eexists. split. apply plus_one. simpl. eauto.
        repeat (split; [ reflexivity | ]).
        split; auto.
        split; auto.
        eexists _, _.
        split; eauto.
        rewrite Regmap.gss.
        destruct (Genv.symbol_address _ _ _); try discriminate.
        apply Mem.load_result in H9.
        inv H. 2: constructor.
        simpl. unfold decode_val. simpl.
        destruct (ZMap.get _ _); try right.
        rewrite Int.zero_ext_widen by Psatz.lia. left.
      }

      Unfocus.
      destruct body as [ | (g, j) body ].
      { (* No statement *)
        simpl in *. subst pc.
        repeat
        match goal with
        | H : fence_at _ _ _ _ |- _ => unfold fence_at in H
        | H : ∃ a, _ |- _ => let b := fresh a in destruct H as (b, H)
        | H : _ ∧ _ |- _ => destruct H
        end.
        match goal with
        | H : defs = _, K : ¬ In _ _ |- _ =>
          unfold defs in H; apply rev'P in H;
            rewrite rev_app_distr in H;
            simpl in H; rewrite <- app_assoc in H;
              generalize (Genv.find_funct_ptr_exists_2 p _ _ _ _ H K)
        end.
        intros (b & Hb & Hef).
        inversion STEP; clear STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : Some _ = Some _ |- _ => inversion H; clear H
                 | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
                 | H : RTL.find_function _ _ _ = _ |- _ =>
                   simpl in H;
                     rewrite Hb, Hef in H
                 end.
        destruct (Genv.find_funct_ptr_transf_partial _ _ TR _ Hef)
          as (ef' & Hef' & K).
        erewrite <- Genv.find_symbol_transf_partial in Hb by exact TR.
        inv K.
        eexists. split. apply plus_one. simpl. eauto.
        simpl. eauto 16.
      }

            { (* Some statement *)
              match goal with
              | M : guarded_at_body _ _ _ _ _ _ |- _ => destruct M as (Hg' & (i & Hi & M') & Hbody)
              end.
                inv STEP;
                repeat match goal with
                       | H: False |- _ => destruct H
             | H : ?a = ?b |- _ => subst a || subst b; simpl in * |-
             | H : Some _ = Some _ |- _ => inversion H; clear H
             | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K
             | H : _ ∧ _ |- _ => let K := fresh H in destruct H as [ K H ]
             | H : Op.eval_operation _ _ _ _ _ = Some _ |- _ =>
               rewrite <- (Op.eval_operation_preserved _ _ (Genv.find_symbol_transf_partial _ p TR)) in H;
                 apply RTLC.eval_operation_w in H
             | H : Op.eval_addressing _ _ _ _ = Some _ |- _ =>
               rewrite <- (Op.eval_addressing_preserved _ _ (Genv.find_symbol_transf_partial _ p TR)) in H;
                 apply RTLC.eval_addressing_w in H
             | H : Mem.loadv _ _ _ = Some _ |- _ => apply RTLC.mem_loadv_w in H
                       end.

                {
                destruct (run_disabled_steps _ _ _ _ _ _ pcm Hbody)
                         as (body' & pc'' & Hbody' & LE & Hlast & Hfalse & STEPS).
                eexists. split.
                econstructor. simpl. rw. eauto. apply STEPS. reflexivity.
                split. reflexivity.
                exists pth.
                repeat (split; [ reflexivity | ]).
                split. assumption.
                eexists. split. eassumption.
                eexists _, _, _.
                split. destruct body' as [ | (?, ?) ?] . auto.
                split. auto.
                split. apply match_regs_set; eauto.
                apply RTLC.eval_operation_lessdef.
                eauto using lessdef_not_blacklisted. assumption.
                split.
                eapply reachable_n1. eauto.
                split. assumption.
                unfold successors. rw. reflexivity.
                split. eauto.
                intros q Hq. apply Pos.lt_trans with pc; auto.
                split. 2: eauto.
                cut (pc'' = pc'). congruence.
                destruct M8 as [ E E' ].
                generalize (E pc).
                unfold successors. rw. intros [ Hpc' Hfalse' ].
                apply guarded_at_body_le in Hbody'.
                revert Hbody' LE M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                eauto using reachable_le.
                generalize (@bdd_leq_w _ _ _ Hpc' M3). clear Hpc'. intros Hpc'.
                assert (pc' <= Pos.pred pc)%positive as LE'.
                revert M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                assert (pc'' < pc)%positive as LT.
                revert LE M'0. clear. apply pos_pred_intro; intros; Psatz.lia.
                destruct (Pos.ltb_spec pc'' pc') as [ LT' | GE ].
                specialize (Hfalse _ LT' LE'). congruence.
                assert (eval_pcond pcm (path_at pc'' pth) = true) as Hpc''.
                destruct body' as [| (?, ?) body']; simpl in Hbody'.
                subst pc''. revert E'. clear.
                case eqP. intros -> _. reflexivity. discriminate.
                intuition congruence.
                destruct (Pos.ltb_spec pc' pc'') as [ LT' | GE' ].
                specialize (Hfalse' _ LT' LT). eapply pcond_disjoint_w in Hfalse'. 2: eassumption.
                congruence.
                clear -GE GE'. eauto using Pos.le_antisym.
                }

                {
                destruct (run_disabled_steps _ _ _ _ _ _ pcm Hbody)
                         as (body' & pc'' & Hbody' & LE & Hlast & Hfalse & STEPS).
                eexists. split.
                econstructor. simpl. rw. eauto 6. apply STEPS. reflexivity.
                split. reflexivity.
                exists pth.
                repeat (split; [ reflexivity | ]).
                split. assumption.
                eexists. split. eassumption.
                eexists _, _, _.
                split.
                destruct body' as [| (?, ?) ]. easy.
                split. assumption.
                split. apply match_regs_set; eauto.
                apply RTLC.mem_loadv_lessdef.
                apply RTLC.eval_addressing_lessdef.
                eauto using lessdef_not_blacklisted.
                assumption.
                split.
                eapply reachable_n1; eauto.
                split. assumption.
                unfold successors. rw. reflexivity.
                split. eauto.
                intros q Hq. apply Pos.lt_trans with pc; auto.
                split. 2: eauto.
                cut (pc'' = pc'). congruence.
                destruct M8 as [ E E' ].
                generalize (E pc).
                unfold successors. rw. intros [ Hpc' Hfalse' ].
                apply guarded_at_body_le in Hbody'.
                revert Hbody' LE M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                eauto using reachable_le.
                generalize (@bdd_leq_w _ _ _ Hpc' M3). clear Hpc'. intros Hpc'.
                assert (pc' <= Pos.pred pc)%positive as LE'.
                revert M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                assert (pc'' < pc)%positive as LT.
                revert LE M'0. clear. apply pos_pred_intro; intros; Psatz.lia.
                destruct (Pos.ltb_spec pc'' pc') as [ LT' | GE ].
                specialize (Hfalse _ LT' LE'). congruence.
                assert (eval_pcond pcm (path_at pc'' pth) = true) as Hpc''.
                destruct body' as [| (?, ?) body']; simpl in Hbody'.
                subst pc''. revert E'. clear.
                case eqP. intros -> _. reflexivity. discriminate.
                intuition congruence.
                destruct (Pos.ltb_spec pc' pc'') as [ LT' | GE' ].
                specialize (Hfalse' _ LT' LT). eapply pcond_disjoint_w in Hfalse'. 2: eassumption.
                congruence.
                clear -GE GE'. eauto using Pos.le_antisym.
                }

                {
                destruct (run_disabled_steps _ _ _ _ _ _ pcm Hbody)
                         as (body' & pc'' & Hbody' & LE & Hlast & Hfalse & STEPS).
                repeat
                match goal with
                | H: _ && _ = true |- _ => apply andb_prop in H; destruct H
                | H: negb _ = true |- _ => apply negb_true_iff in H
                end.
                edestruct Mem.storev_extends as (? & ? & ?); try eassumption.
                eapply RTLC.eval_addressing_lessdef, lessdef_not_blacklisted; eauto.
                apply M6; assumption.
                eexists. split.
                econstructor. simpl. rw. eauto. apply STEPS. reflexivity.
                split. reflexivity.
                exists pth.
                repeat (split; [ reflexivity | ]).
                split. assumption.
                eexists. split. eassumption.
                eexists _, _, _.
                split.
                destruct body' as [| (?, ?)]. easy.
                repeat (split; [ eassumption |]).
                split.
                eapply reachable_n1; eauto.
                split. assumption.
                unfold successors. rw. reflexivity.
                split. eauto.
                intros q Hq. apply Pos.lt_trans with pc; auto.
                split. 2: eauto.
                cut (pc'' = pc'). congruence.
                destruct M8 as [ E E' ].
                generalize (E pc).
                unfold successors. rw. intros [ Hpc' Hfalse' ].
                apply guarded_at_body_le in Hbody'.
                revert Hbody' LE M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                eauto using reachable_le.
                generalize (@bdd_leq_w _ _ _ Hpc' M3). clear Hpc'. intros Hpc'.
                assert (pc' <= Pos.pred pc)%positive as LE'.
                revert M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                assert (pc'' < pc)%positive as LT.
                revert LE M'0. clear. apply pos_pred_intro; intros; Psatz.lia.
                destruct (Pos.ltb_spec pc'' pc') as [ LT' | GE ].
                specialize (Hfalse _ LT' LE'). congruence.
                assert (eval_pcond pcm (path_at pc'' pth) = true) as Hpc''.
                destruct body' as [| (?, ?) body']; simpl in Hbody'.
                subst pc''. revert E'. clear.
                case eqP. intros -> _. reflexivity. discriminate.
                intuition congruence.
                destruct (Pos.ltb_spec pc' pc'') as [ LT' | GE' ].
                specialize (Hfalse' _ LT' LT). eapply pcond_disjoint_w in Hfalse'. 2: eassumption.
                congruence.
                clear -GE GE'. eauto using Pos.le_antisym.
                }

                {
                destruct (run_disabled_steps _ _ _ _ _ _ (if b then pc :: pcm else pcm) Hbody)
                         as (body' & pc'' & Hbody' & LE & Hlast & Hfalse & STEPS).
                match goal with
                | M: Mem.extends _ _
                , R: match_regs _ _ _
                , BL: are_not_blacklisted _ _ = true
                , H: Op.eval_condition _ _ _ = Some _ |- _ =>
                  generalize (Op.eval_condition_lessdef _ (lessdef_not_blacklisted _ _ _ _ R BL) M H);
                    clear H; intros H
                end.
                eexists. split.
                econstructor. simpl. rw. eauto. apply STEPS. reflexivity.
                split. reflexivity.
                exists pth.
                repeat (split; [ reflexivity | ]).
                split. assumption.
                eexists. split. eassumption.
                eexists _, _, _.
                split.
                destruct body' as [ | (?, ?)]. easy.
                split. assumption.
                split. eassumption.
                split.
                eapply reachable_n1; eauto.
                split. case b; assumption.
                unfold successors. rw. case b; simpl; auto.
                split. eauto.
                intros q H.
                destruct b.
                destruct H as [ <- | H ]. auto.
                apply Pos.lt_trans with pc; auto.
                apply Pos.lt_trans with pc; auto.
                split. 2: eauto.
                cut (pc'' = if b then ifso else ifnot). congruence.
                destruct M8 as [ E E' ].
                generalize (E pc).
                unfold successors. rw. intros ( Hifso & Hifnot & Hfalseso & Hfalsenot ).
                apply guarded_at_body_le in Hbody'.
                revert Hbody' LE M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                eauto using reachable_le.
                assert (ifso <= Pos.pred pc)%positive as LEso.
                revert M'0; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                assert (ifnot <= Pos.pred pc)%positive as LEnot.
                revert M'1; clear.
                apply pos_pred_intro; intros; Psatz.lia.
                assert (pc'' < pc)%positive as LT.
                revert LE M'0 M'1. clear. apply pos_pred_intro; intros; Psatz.lia.
                generalize (@bdd_leq_w _ _ (pc :: pcm) Hifso (eval_pcond_then (wfpc_bounded _ _ _ M1 _) M3)).
                clear Hifso. intros Hifso.
                generalize (@bdd_leq_w _ _ pcm Hifnot (eval_pcond_else M2 M3)).
                clear Hifnot. intros Hifnot.
                destruct (Pos.ltb_spec pc'' (if b then ifso else ifnot)) as [ LT' | GE ].
                destruct b. specialize (Hfalse _ LT' LEso). congruence.
                specialize (Hfalse _ LT' LEnot). congruence.
                assert (eval_pcond (if b then pc :: pcm else pcm) (path_at pc'' pth) = true) as Hpc''.
                destruct body' as [| (?, ?) body']; simpl in Hbody'.
                subst pc''. revert E'. clear.
                case eqP. intros -> _. reflexivity. discriminate.
                intuition congruence.
                destruct (Pos.ltb_spec (if b then ifso else ifnot) pc'') as [ LT' | GE' ].
                destruct b.
                specialize (Hfalseso _ LT' LT). eapply pcond_disjoint_w in Hfalseso.
                2: eapply eval_pcond_then; eauto; apply M1.
                clear -Hpc'' Hfalseso. unfold ident, RTL.node in *. congruence.
                specialize (Hfalsenot _ LT' LT). eapply pcond_disjoint_w in Hfalsenot.
                2: eauto using eval_pcond_else.
                clear -Hpc'' Hfalsenot. congruence.
                clear -GE GE'. eauto using Pos.le_antisym.
                }
            }
  Qed.

  Corollary simulation' :
    backward_simulation (RTL.semantics p) (RTLC.semantics p').
  Proof.
    apply forward_to_backward_simulation. apply simulation.
    apply RTL.semantics_receptive.
    apply RTLC.semantics_determinate.
  Qed.

End SIMULATION.
