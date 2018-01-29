Require ValCirc.
Require MoreBDD.
Import Utf8.
Import Coqlib.
Import Maps.
Import AST.
Import Values.
Import Registers.
Import ORbdt.
Import ExtraLib.
Import MoreBDD.
Import CircIO.
Import ValCirc.

Import eqtype zint.

Local
Open Scope N_scope.

Unset Elimination Schemes.

Section ON_RTLC.
Import RTLC.

Definition condition_names (body: code) : list ident :=
  fold_right
    (λ gi tl,
     let '(_, i) := gi in
     match i with
     | Itest c _ _ => c :: tl
     | _ => tl
     end)
    nil
    body.

Fixpoint sorted_names_below (n: ident) (ns: list ident) : bool :=
  match ns with
  | nil => true
  | n' :: ns' => if n' <? n then sorted_names_below n' ns' else false
  end%positive.

Definition sorted_names (ns: list ident) : bool :=
  match ns with
  | nil => true
  | n :: ns => sorted_names_below n ns
  end.

Lemma sorted_names_tail n ns :
  sorted_names (n :: ns) = true → sorted_names ns = true.
Proof.
  destruct ns as [ | n' ns ]. exact id.
  simpl. case Pos.ltb_spec. auto. discriminate.
Qed.

Fixpoint first_condition (body: code) : option ident :=
  match body with
  | nil => None
  | (_, Itest c _ _) :: _ => Some c
  | _ :: body' => first_condition body'
  end.

Remark first_condition_name body :
  first_condition body = hd_error (condition_names body).
Proof.
  elim body; clear. reflexivity.
  intros (g, ()) body IH; auto.
Qed.

Definition name_ltb (x y: option ident) : bool :=
  match x with
  | None => true
  | Some x' => match y with
               | None => true
               | Some y' => Pos.ltb x' y'
               end
  end.

Remark bounded_bdd_iff {A: eqType} n (g: bdd A) :
  name_ltb n (min_name (literal_of_bdd g)) =
  match n with None => true | Some n => check_bounded_bdd g n end.
Proof.
  destruct n as [ n | ]. 2: reflexivity.
  generalize (min_name_iff (literal_of_bdd g)).
  case (check_bounded_bdd_iff); intros H; simpl;
    destruct (min_name _) as [ m | ]; auto; intros X.
  3: elim H; intro; destruct (literal_of_bdd g); [ intros () | discriminate ].
  apply Pos.ltb_lt. exact (H _ (proj1 X)).
  apply Pos.ltb_ge.
  destruct (not_bounded_bdd_ex _ _ H) as (x & Hx & LE).
  etransitivity. apply (proj2 X), Hx. exact LE.
Qed.

Fixpoint guards_refer_to_past_conditions (body: code) : bool :=
  match body with
  | nil => true
  | (g, _) :: body' =>
    if name_ltb (first_condition body) (min_name (literal_of_bdd g))
    then guards_refer_to_past_conditions body'
    else false
  end.

Lemma guards_refer_to_past_conditions_bounded g i body :
  guards_refer_to_past_conditions ((g, i) :: body) = true →
  bounded_bdd' g (first_condition ((g, i) :: body)).
Proof.
  unfold bounded_bdd'.
  unfold guards_refer_to_past_conditions.
  fold guards_refer_to_past_conditions.
  generalize (bounded_bdd_iff (first_condition ((g, i) :: body)) g).
  destruct first_condition. 2: easy. intros ->.
  case check_bounded_bdd_iff. auto.
  discriminate.
Qed.

End ON_RTLC.

Lemma n_succ_pos_inj {x y} :
  N.succ_pos x = N.succ_pos y →
  x = y.
Proof.
  intros H. apply (f_equal Npos) in H. revert H.
  rewrite ! N.succ_pos_spec.
  apply N.succ_inj.
Qed.

Section EXTRA.
  Context {A : Type}.
  Lemma empty_list_nil (m: list A) :
    (∀ x, ¬ In x m) →
    m = nil.
  Proof.
    case m. reflexivity.
    intros a ? K; elim (K a); left; reflexivity.
  Qed.

  Definition cons_not_nil (P: Prop) {a: A} {m: list A} (H: a :: m = nil) : P :=
    match H in _ = x return match x with nil => P | _ => True end with Logic.eq_refl => I end.

  Definition rev_nil_inv (m: list A) : rev m = nil → m = nil :=
    match m return rev m = nil → m = nil with
    | nil => λ _, Logic.eq_refl
    | _ :: _ => λ K, cons_not_nil _ (proj2 (app_eq_nil _ _ K))
    end.

  Lemma rev_inj (x y: list A) :
    x = rev y →
    rev x = y.
  Proof.
    revert x. elim y using rev_ind; clear.
    simpl. intros ? ->; reflexivity.
    intros a y IH x. rewrite rev_app_distr. simpl. intros ->. simpl. rewrite rev_involutive. reflexivity.
  Qed.

  Lemma rev_is_app (x y z: list A) :
    rev x = y ++ z →
    x = rev z ++ rev y.
  Proof.
    rewrite <- (rev_involutive (y ++ z)).
    intros H. apply rev_inj in H. rewrite rev_involutive in H. subst x.
    apply rev_app_distr.
  Qed.

  Lemma lessdef_list_map (f: A → Values.val) p q:
    Forall2 (λ x y, Val.lessdef x (f y)) p q ↔
    Val.lessdef_list p (map f q).
  Proof.
    split.
    induction 1; constructor; auto.
    remember (map f q) as r eqn: X. intros H.
    revert q X. elim H; clear.
    intros q EQ. symmetry in EQ. apply map_eq_nil in EQ. subst q. constructor.
    intros x y p q H REC IH [ | a b ] X; inv X.
    constructor; auto.
  Qed.

  Lemma forall2_weaken {B: Type} (P Q: A → B → Prop) p q :
    (∀ a b, P a b → Q a b) →
    Forall2 P p q →
    Forall2 Q p q.
  Proof.
    intros LE; induction 1; constructor; auto.
  Qed.

  Lemma forall2_cons_inv {B: Type} (P: A → B → Prop) p a q :
    Forall2 P (a :: p) q →
    ∃ b q',
      q = b :: q' ∧ P a b ∧ Forall2 P p q'.
  Proof.
    intros H.
    set (diag p q :=
           match p with nil => True | a :: p => ∃ b q', q = b :: q' ∧ P a b ∧ Forall2 P p q' end).
    change (diag (a :: p) q). case H; simpl; eauto.
  Qed.

End EXTRA.

(* Collect all leaves of a φ-node *)
Fixpoint leaves (bdd: phiNode) : list ident :=
  match bdd with
  | Leaf None => nil
  | Leaf (Some p) => p :: nil
  | Node _ ℓ r => leaves ℓ ++ leaves r
  end.

(* If a φ node evaluates to some wire under some path model,
 then it is a leaf of this node; the converse does not hold. *)
Lemma eval_phiNode_leaf bdd n pcm :
  eval_phiNode pcm bdd = Some n → In n (leaves bdd).
Proof.
  revert n pcm; elim bdd; clear.
  intros [ n | ] n'; simpl. left. congruence. discriminate.
  intros p ℓ IHℓ r IHr n; simpl.
  intros pcm H. apply in_app. destruct (ssrbool.in_mem _ _).
  left; eapply IHℓ, H. right; eapply IHr, H.
Qed.

Lemma leaves_chkN n p q :
  incl (leaves (chkN n p q)) (leaves p ++ leaves q).
Proof.
  unfold chkN. case bdd_eqP.
  intros -> w H. apply in_app; left; apply H.
  intros _ ?; exact id.
Qed.

Lemma leaves_chkN_slice n p a q b :
  incl (leaves (chkN_slice n p a q b)) (leaves p ++ leaves q).
Proof.
  unfold chkN_slice.
  destruct a as [()|].
  destruct b as [()|].
  apply leaves_chkN. intros w ?; apply in_app; auto.
  apply leaves_chkN. intros w ?; apply in_app; auto.
  destruct b as [()|].
  apply leaves_chkN. intros w ?; apply in_app; auto.
  apply leaves_chkN.
Qed.

Lemma leaves_phi_slice φ g :
  incl (leaves (phi_slice φ g)) (leaves φ).
Proof.
  revert g. elim φ; clear.
  simpl. intros [p|] [()|] w H; auto. destruct H.
  intros p ℓ IHℓ r IHr g.
  elim g; clear g.
  intros () w. exact id. intros ().
  intros p' ℓ' IHℓ' r' IHr' w.
  simpl. case eqP.
  intros -> H. apply leaves_chkN_slice in H. apply in_app in H.
  apply in_app. destruct H as [ H | H ].
  left; eapply IHℓ, H. right; eapply IHr, H.
  intros NE.
  case Pos.ltb_spec.
  intros LT H. apply leaves_chkN in H. apply in_app in H.
  apply in_app. destruct H as [ H | H ].
  left; eapply IHℓ, H. right; eapply IHr, H.
  intros LE H. apply leaves_chkN_slice in H. apply in_app in H.
  destruct H as [ H | H ].
  eapply IHℓ', H. eapply IHr', H.
Qed.

Corollary phi_slice_free φ g w :
  phi_slice φ g = phi_single w →
  In w (leaves φ).
Proof.
  intros H. apply (leaves_phi_slice φ g w). rewrite H. left; reflexivity.
Qed.

Lemma leaves_of_phi_add g w (φ: phiNode) :
  incl (leaves (phi_add g w φ)) (w :: leaves φ).
Proof.
  revert w φ; elim g; clear.
  intros () w φ. intros ? [ -> | () ]; left; reflexivity. intros ?; apply or_intror.
  intros p ℓ IHℓ r IHr w φ. elim φ; clear φ.
  intros n.
  intros w' H. simpl in H. apply leaves_chkN in H. apply in_app in H.
  destruct H as [ H | H ]. exact (IHℓ _ _ _ H). exact (IHr _ _ _ H).
  intros n ℓ' IHℓ' r' IHr' w'. simpl.
  case eqP.
  intros -> H. apply leaves_chkN in H. apply in_app in H.
  rewrite in_app.
  destruct H as [ H | H ]. destruct (IHℓ _ _ _ H); auto. destruct (IHr _ _ _ H); auto.
  intros NE. case Pos.ltb_spec.
  intros LT H. apply leaves_chkN in H. apply in_app in H.
  destruct H as [ H | H ]. destruct (IHℓ _ _ _ H); auto. destruct (IHr _ _ _ H); auto.
  intros LE H. apply leaves_chkN in H. apply in_app in H.
  rewrite in_app.
  destruct H as [ H | H ]. destruct (IHℓ' _ H); auto. destruct (IHr' _ H); auto.
Qed.

(* A φ state maps every register to the wires at which it has been defined
   (for all possible path conditions).
   Under some path conditions, a register may be mapped to None,
   which means that said register is not initialized.
*)
Definition φ_state : Type := PTree.t phiNode.

Definition φ_of_reg (info: φ_state) (r: reg) : phiNode :=
  match info ! r with
  | None => Leaf None
  | Some φ => φ
  end.

Lemma fold_φ_of_reg {info r φ} :
  info ! r = Some φ →
  φ = φ_of_reg info r.
Proof.
  unfold φ_of_reg. intros ->. reflexivity.
Qed.

(* A φ node is bounded by n when all wires that appear at the BDD leaves
are smaller than .n *)
Definition bounded_phiNode (bdd: phiNode) (n: N) : Prop :=
  ∀ w, In w (leaves bdd) → Pos.pred_N w < n.

(* A φ state is bounded by n when for all register,
  the BDD corresponding to this register is bounded by n. *)
Definition bounded_φ_state (info: φ_state) (n: N) : Prop :=
  ∀ r, bounded_phiNode (φ_of_reg info r) n.

(* A condition_wires mapping is bounded by n when no wire larger than n is bound. *)
Definition bounded_condition_wires (cw: condition_wires) (n: wire) : Prop :=
  ∀ w, n <= w → condition_of_wire cw w = None.

Record state : Type :=
  {
    st_phi_info: φ_state;
    st_next_wire: wire;
    st_code: ValCirc.code;
    st_conditions: condition_wires;
    st_wfnw:  nlen st_code =? st_next_wire = true;
    st_wfpi: bounded_φ_state st_phi_info st_next_wire;
    st_wfcnd: bounded_condition_wires st_conditions st_next_wire
  }.

Definition mon A : Type :=
  state → A * state.

Definition ret {A} (a: A) : mon A :=
  λ s, (a, s).

Definition bind {A B} (f: A → mon B) (m: mon A) : mon B :=
  λ s, let '(a, s) := m s in f a s.

(*
Definition seq {unit A} (f: mon A) (m: mon unit) : mon A :=
  λ s, let '(_, s) := m s in f s.
*)

Section MON.
  Context {A B: Type}.
  Context (f: A → mon B).

  Definition mon_map (x: list A) : mon (list B) :=
    fold_right (λ a, bind (λ r, bind (λ b, ret (b :: r)) (f a))) (ret nil) x.

End MON.

Lemma add_gentry_obligation {A} (x: A) {y: list A} {w: wire} :
  nlen y =? w = true →
  nlen (x :: y) =? Npos (N.succ_pos w) = true.
Proof.
  intros H; apply N.eqb_eq in H; subst w.
  apply N.eqb_eq. rewrite nlen_cons.
  symmetry. apply N.succ_pos_spec.
Qed.

Lemma add_gentry_obligation_2 {gr: option (pcond * reg)} {s: state} :
  let w' := N.succ_pos (st_next_wire s) in
  bounded_φ_state
    match gr with
    | Some (g, r) =>
      let info := st_phi_info s in
      PTree.set r (phi_add g w' (φ_of_reg info r)) info
    | None => st_phi_info s
    end
   (Npos w').
Proof.
  simpl. rewrite N.succ_pos_spec. intros r' w.
  case gr; clear.
  - intros (g, r). unfold φ_of_reg at 1. rewrite PTree.gsspec. case peq.
    + intros -> IN. apply leaves_of_phi_add in IN.
      destruct IN as [ <- | IN ].
      * rewrite N.pos_pred_succ. Psatz.lia.
      * generalize (st_wfpi s _ _ IN). Psatz.lia.
    + intros NE H. generalize (st_wfpi s _ _ H). Psatz.lia.
  - intros H. generalize (st_wfpi _ _ _ H). Psatz.lia.
Qed.

Lemma add_gentry_obligation_3 {oc: option ident} {s: state} :
  let w' := N.succ_pos (st_next_wire s) in
  bounded_condition_wires
    match oc with
    | Some c => PTree.set w' c (st_conditions s)
    | None => st_conditions s
    end (N.pos w').
Proof.
  simpl. intros x LE.
  assert (st_next_wire s <= x) as LE'.
  { rewrite N.succ_pos_spec in LE. Psatz.lia. }
  pose proof (st_wfcnd s x LE') as H.
  destruct oc as [ c | ]. 2: exact H.
  unfold condition_of_wire. rewrite PTree.gso. apply H.
  intros K. rewrite <- K in LE. rewrite N.succ_pos_spec in LE.
  Psatz.lia.
Qed.

Definition add_gentry (gr: option (pcond * reg)) (oc: option ident) (ge: gentry) : mon wire :=
  λ s,
  let w := st_next_wire s in
  let w' := N.succ_pos w in
  (w,
  {|
    st_phi_info :=
      match gr with
      | Some (g, r) =>
        let info := st_phi_info s in
        PTree.set r (phi_add g w' (φ_of_reg info r)) info
      | None => st_phi_info s
      end;
    st_next_wire := Npos w';
    st_code := ge :: st_code s;
    st_conditions :=
      match oc with
      | Some c => PTree.set w' c (st_conditions s)
      | None => st_conditions s
      end;
    st_wfnw := add_gentry_obligation ge (st_wfnw s);
    st_wfpi := add_gentry_obligation_2;
    st_wfcnd := add_gentry_obligation_3
  |}).

Definition φ_entry (φ: phiNode) : gentry :=
  {| ggate := Gφ φ; gwires := nil |}.

Definition add_φ (g: pcond) (r: reg) (φ: phiNode) : mon wire :=
  add_gentry (Some (g, r)) None (φ_entry φ).

Definition get_reg (g: pcond) (r: reg) : mon wire :=
  λ s,
  match (st_phi_info s) ! r with
  | None => ret N0
  | Some φ =>
    match phi_slice φ g with
    | Leaf x => ret match x with None => N0 | Some r => Pos.pred_N r end
    | φ' => add_φ g r φ'
    end
  end s.

Definition get_regs (g: pcond) (rs: list reg) : mon (list wire) :=
  mon_map (get_reg g) rs.

Definition translate_instruction (gi: pcond * RTLC.instruction) : mon _ :=
  let '(g, i) := gi in
  match i with
  | RTLC.Iop op args dst =>
    bind
      (λ wargs, add_gentry (Some (g, dst)) None (Gentry (Gop op) wargs))
      (get_regs g args)
  | RTLC.Itest c op args =>
    bind
      (λ wargs, add_gentry None (Some c) (Gentry (Gtest g op) wargs))
      (get_regs g args)
  | RTLC.Iload ϰ addr args dst =>
    bind
      (λ wargs, add_gentry (Some (g, dst)) None (Gentry (Gload ϰ addr) wargs))
      (get_regs g args)
  | RTLC.Istore ϰ addr args src =>
    bind
      (λ wargs, add_gentry None None (Gentry (Gstore g ϰ addr) wargs))
      (get_regs g (src :: args))
  end.

Definition translate_code (c: RTLC.code) : mon wire :=
  λ s, fold_left (λ ws i, translate_instruction i (snd ws)) c (N0, s).

(*
Definition translate_code (c: RTLC.code) : mon _ :=
  fold_left (λ s i, seq (translate_instruction i) s) c (ret N0).
*)

Lemma initial_state_obligation : bounded_φ_state (PTree.empty _) 0.
Proof.
  intros r w.
  unfold φ_of_reg. rewrite PTree.gempty. intros ().
Qed.

Lemma initial_state_obligation_2 : bounded_condition_wires (PTree.empty _) 0.
Proof.
  intros x _. unfold condition_of_wire. apply PTree.gempty.
Qed.

Definition initial_state : state :=
  {|
    st_phi_info := PTree.empty _;
    st_next_wire := N0;
    st_code := nil;
    st_conditions := PTree.empty _;
    st_wfnw := Logic.eq_refl;
    st_wfpi := initial_state_obligation;
    st_wfcnd := initial_state_obligation_2
  |}.

Definition translate_function (f: RTLC.function) : function :=
  let '(_, s) := translate_code (RTLC.fn_code f) initial_state in
  {|
    fn_inputs := RTLC.fn_inputs f;
    fn_stacksize := RTLC.fn_stacksize f;
    fn_conditions := st_conditions s;
    fn_body := rev' (st_code s);
    fn_outputs := RTLC.fn_outputs f
  |}.

Definition translate_fundef (fd: fundef RTLC.function) : fundef function :=
  match fd with
  | Internal fn => Internal (translate_function fn)
  | External ef => External ef
  end.

Definition translate_program : RTLC.program → program :=
  transform_program translate_fundef.

Record wf_body (body: RTLC.code) : Prop :=
  WFB {
      wfb_conditions : sorted_names (condition_names body) = true
      ;
      wfb_guards : guards_refer_to_past_conditions body = true
  }.

Lemma wf_body_tail g i body :
  wf_body ((g, i) :: body) → wf_body body.
Proof.
  intros [ X Y ]. constructor.
  simpl in X. destruct i; eauto using sorted_names_tail.
  simpl in Y. destruct (name_ltb _ _). exact Y. discriminate.
Qed.

Definition check_and_translate_program (p: RTLC.program) : Errors.res program :=
  if forallb (λ def,
              match snd def with
              | (Gvar _ | Gfun (External _)) => true
              | Gfun (Internal fn) =>
                let c := RTLC.fn_code fn in
                if sorted_names (condition_names c)
                then guards_refer_to_past_conditions c
                else false
              end) (prog_defs p)
  then Errors.OK (translate_program p)
  else Errors.Error (Errors.msg "ValCircGen: RTLC program is not well-formed").

Lemma check_and_translate_program_OK p p' :
  check_and_translate_program p = Errors.OK p' →
  translate_program p = p' ∧
  ∀ x fn, In (x, Gfun (Internal fn)) (prog_defs p) → wf_body (RTLC.fn_code fn).
Proof.
  unfold check_and_translate_program.
  destruct (forallb _ _) eqn: H; intros X; inv X.
  apply (conj Logic.eq_refl).
  intros x fn IN. rewrite forallb_forall in H.
  specialize (H _ IN). simpl in H.
  destruct (sorted_names _) eqn: A. 2: discriminate.
  split; auto.
Qed.

Section SIMULATION.

Import Globalenvs.

Definition condition_wires_agree (n: wire) (cw cw': condition_wires) : Prop :=
  ∀ w, w < n → condition_of_wire cw w = condition_of_wire cw' w.

Remark condition_wires_agree_refl n cw : condition_wires_agree n cw cw.
Proof. intros ?. reflexivity. Qed.

Remark condition_wires_agree_trans n m y x z :
  condition_wires_agree n x y →
  condition_wires_agree m y z →
  condition_wires_agree (N.min n m) x z.
Proof.
  unfold condition_wires_agree.
  intros Hxy Hyz w Hw.
  etransitivity.
  apply Hxy, (proj1 (N.min_glb_lt_iff n m _)), Hw.
  apply Hyz, (proj1 (N.min_glb_lt_iff n m _)), Hw.
Qed.

Corollary condition_wires_agree_w n m x y:
  m <= n →
  condition_wires_agree n x y →
  condition_wires_agree m x y.
Proof.
  intros LE H.
  erewrite <- (N.min_l m) by exact LE.
  eauto using condition_wires_agree_trans, condition_wires_agree_refl.
Qed.

Definition match_add_gentry (gr: option (pcond * reg)) (oc: option ident) (ge: gentry)
           (before: φ_state) (w: wire) (after: φ_state) (cw: condition_wires) : Prop :=
  match gr with
  | None => after = before
  | Some (g, r) =>
    after = PTree.set r (phi_add g (N.succ_pos w) (φ_of_reg before r)) before
  end ∧
  condition_of_wire cw w = oc.

Lemma match_add_gentry_cwle sz cw gr oc ge before w after cw' :
  w < sz →
  condition_wires_agree sz cw cw' →
  match_add_gentry gr oc ge before w after cw →
  match_add_gentry gr oc ge before w after cw'.
Proof.
  intros LT H [ X Y ]. apply (conj X). clear X.
  rewrite <- (H w); auto.
Qed.

Lemma add_gentry_matches gr oc ge s :
  let (w, s') := add_gentry gr oc ge s in
  match_add_gentry gr oc ge (st_phi_info s) w (st_phi_info s') (st_conditions s') ∧
  st_code s' = ge :: st_code s ∧
  st_next_wire s' = st_next_wire s + 1 ∧
  w = st_next_wire s ∧
  condition_wires_agree (st_next_wire s) (st_conditions s) (st_conditions s').
Proof.
  refine (conj _ (conj Logic.eq_refl (conj _ (conj Logic.eq_refl _)))).
  split.
  - destruct gr as [ (g, r) | ]; reflexivity.
  - destruct oc as [ c | ].
    apply PTree.gss.
    apply s, N.le_refl.
  - etransitivity.
    apply N.succ_pos_spec.
    symmetry. apply N.add_1_r.
  - destruct oc as [ c | ].
    intros w H. unfold condition_of_wire. simpl. rewrite PTree.gso. reflexivity.
    intros K. apply n_succ_pos_inj in K. Psatz.lia.
    apply condition_wires_agree_refl.
Qed.

Ltac add_gentry :=
  match goal with
  | |- appcontext[ add_gentry ?gr ?oc ?ge ?s ] =>
    generalize (add_gentry_matches gr oc ge s);
    case (add_gentry gr oc ge s)
  end.

Definition match_get_reg (g: pcond) (r: reg) (sz: N) (before: φ_state) (φs: option gentry) (w: wire) (after: φ_state) (cw: condition_wires) : Prop :=
  match before ! r with
  | None => φs = None ∧ w = N0 ∧ after = before
  | Some φ =>
    match phi_slice φ g with
    | Leaf None => φs = None ∧ w = N0 ∧ after = before
    | Leaf (Some r) => φs = None ∧ w = Pos.pred_N r ∧ w < sz ∧ after = before
    | φ' =>
      match_add_gentry (Some (g, r)) None (φ_entry φ') before w after cw ∧
      φs = Some (φ_entry φ') ∧
      w = sz
    end
  end.

Definition olen {A: Type} (o: option A) : N :=
  match o with None => 0 | Some _ => 1 end.

Definition ocons {A: Type} (o: option A) (m: list A) : list A :=
  match o with
  | None => m
  | Some a => a :: m
  end.

Lemma ocons_app {A: Type} (o: option A) (m m': list A) :
  ocons o (m ++ m') = ocons o m ++ m'.
Proof. now case o. Qed.

Lemma rev_ocons_app {A: Type} (o: option A) (m m': list A) :
  rev (ocons o m) ++ m' = rev m ++ ocons o m'.
Proof.
  destruct o. simpl. rewrite <- app_assoc. reflexivity.
  reflexivity.
Qed.

Lemma nlen_ocons {A: Type} (o: option A) m :
  nlen (ocons o m) = olen o + nlen m.
Proof.
  case o.
  intros a. unfold ocons. rewrite nlen_cons. symmetry. apply N.add_1_l.
  reflexivity.
Qed.

Fixpoint match_get_regs (g: pcond) (rs: list reg) (sz: N) (before: φ_state) (φs: list gentry) (ws: list wire) (after: φ_state) (cw: condition_wires) : Prop :=
  match rs with
  | nil => φs = nil ∧ ws = nil ∧ after = before
  | r :: rs' =>
    ∃ φL w mid φR ws',
    φs = ocons φL φR ∧
    ws = w :: ws' ∧
    match_get_reg g r (sz + nlen φR) mid φL w after cw ∧
    match_get_regs g rs' sz before φR ws' mid cw
  end.

Remark match_get_regs_length g rs sz before φs ws after cw :
  match_get_regs g rs sz before φs ws after cw →
  length rs = length ws.
Proof.
  revert sz φs ws after. elim rs; clear.
  simpl. intuition subst. reflexivity.
  intros r rs IH sz φs ws after (? & ? & ? & ? & ? & -> & -> & ? & ?).
  simpl. eauto.
Qed.

Lemma get_reg_matches g r s :
  let '(w, s') := get_reg g r s in
  ∃ φs,
  match_get_reg g r (st_next_wire s) (st_phi_info s) φs w (st_phi_info s') (st_conditions s') ∧
  st_code s' = ocons φs (st_code s) ∧
  st_next_wire s' = st_next_wire s + olen φs ∧
  st_conditions s = st_conditions s'.
Proof.
  generalize (st_wfpi s r).
  unfold get_reg, match_get_reg, φ_of_reg.
  destruct ((st_phi_info s) ! _) as [ φ | ] eqn: Hφ.
  - intros R.
    destruct (phi_slice _ _) as [ [ w' | ] | a b c ] eqn: Hw';
      try (pose proof (phi_slice_free _ _ _ Hw') as X; specialize (R _ X));
      simpl; eauto 8 using condition_wires_agree_refl, N.add_0_r.
    exists (Some (φ_entry (Node a b c))).
    unfold match_add_gentry.
    unfold φ_of_reg. rewrite Hφ.
    split. split. split. reflexivity.
    apply s, N.le_refl.
    split; reflexivity.
    split. reflexivity.
    split; auto.
    simpl.
    rewrite N.succ_pos_spec. symmetry. apply N.add_1_r.
  - simpl; eauto 7 using condition_wires_agree_refl, N.add_0_r.
Qed.

Ltac get_reg :=
  match goal with
  | |- appcontext[ get_reg ?g ?r ?s ] =>
    generalize (get_reg_matches g r s);
    case (get_reg g r s)
  end.

Lemma get_regs_matches g rs s :
  let '(ws, s') := get_regs g rs s in
  ∃ φs,
  match_get_regs g rs (st_next_wire s) (st_phi_info s) φs ws (st_phi_info s') (st_conditions s') ∧
  st_code s' = φs ++ st_code s ∧
  st_next_wire s' = st_next_wire s + nlen φs ∧
  st_conditions s = st_conditions s'.
Proof.
  elim rs; clear.
  - simpl. eauto 7 using condition_wires_agree_refl, N.add_0_r.
  - intros r rs. simpl. unfold bind. case (get_regs _ _).
    intros ws s' (φs & IH & Hcode & Hnw & LE).
    get_reg. intros w s'' (φs' & IH' & Hcode' & Hnw' & LE').
    exists (ocons φs' φs). split; [ | split ]. 2: rewrite Hcode', Hcode; apply ocons_app.
    rewrite Hnw in IH'.
    rewrite LE' in IH.
    eauto 9.
    split. 2: congruence.
    rewrite Hnw', Hnw, nlen_ocons, <- N.add_assoc.
    f_equal. apply N.add_comm.
Qed.

Ltac get_regs :=
  match goal with
  | |- appcontext[ get_regs ?g ?rs ?s ] =>
    generalize (get_regs_matches g rs s);
    case (get_regs g rs s)
  end.

Definition match_gate (i: RTLC.instruction)
           (ins: list reg) (out: option reg) (cnd: option ident)
           (g: pcond)
           (ga: gate) : Prop :=
  match i with
  | RTLC.Iop op args dst => ins = args ∧ out = Some dst ∧ cnd = None ∧ ga = Gop op
  | RTLC.Itest c op args => ins = args ∧ out = None ∧ cnd = Some c ∧ ga = Gtest g op
  | RTLC.Iload ϰ addr args dst => ins = args ∧ out = Some dst ∧ cnd = None ∧ ga = Gload ϰ addr
  | RTLC.Istore ϰ addr args src => ins = src :: args ∧ out = None ∧ cnd = None ∧ ga = Gstore g ϰ addr
  end.

Definition match_instruction (gi: pcond * RTLC.instruction) (sz: N) (before: φ_state)
           (ges : list gentry)  (after: φ_state) (cw: condition_wires) : Prop :=
  let '(g, i) := gi in
  ∃ ga φs args out cnd wargs mid,
    match_gate i args out cnd g ga ∧
    match_get_regs g args sz before φs wargs mid cw ∧
    match_add_gentry (option_map (pair g) out) cnd (Gentry ga wargs) mid (sz + nlen φs) after cw ∧
    ges = Gentry ga wargs :: φs.

Lemma bounded_condition_wires_le cw n n' :
  n <= n' →
  bounded_condition_wires cw n →
  bounded_condition_wires cw n'.
Proof.
  intros LE H w c.
  apply H. eauto using N.le_trans.
Qed.

Lemma match_get_reg_cwle cw g r sz before ges w after cw' :
  condition_wires_agree (sz + olen ges) cw cw' →
  match_get_reg g r sz before ges w after cw →
  match_get_reg g r sz before ges w after cw'.
Proof.
  intros LE. unfold match_get_reg.
  destruct (_ ! _) eqn: ?. 2: exact id.
  destruct (phi_slice _ _) eqn: ?. exact id.
  intros (X & -> & ->). split; auto.
  generalize X.
  eapply match_add_gentry_cwle; eauto.
  simpl. Psatz.lia.
Qed.

Lemma match_get_regs_cwle cw g rs sz before ges ws after cw' :
  condition_wires_agree (sz + nlen ges) cw cw' →
  match_get_regs g rs sz before ges ws after cw →
  match_get_regs g rs sz before ges ws after cw'.
Proof.
  revert ges ws after.
  elim rs; clear rs. intros ges ws after LE; exact id.
  intros r rs IH.
  intros ges ws after LE (φL & w & mid & φR & ws' & -> & -> & M & REC).
  rewrite nlen_ocons, (N.add_comm (olen φL)), N.add_assoc in LE.
  eexists _, _, _, _, _.
  split. reflexivity.
  split. reflexivity.
  split. eapply match_get_reg_cwle; eauto.
  eapply IH; eauto.
  eapply condition_wires_agree_w; eauto. Psatz.lia.
Qed.

Lemma match_instruction_cwle cw gi sz before ges after cw' :
  condition_wires_agree (sz + nlen ges) cw cw' →
  match_instruction gi sz before ges after cw →
  match_instruction gi sz before ges after cw'.
Proof.
  Opaque match_get_regs.
  assert (∀ φs (ge: gentry), sz + nlen φs < sz + nlen (ge :: φs)) as hint.
  { intros; rewrite nlen_cons; Psatz.lia. }
  intros LE. destruct gi as (g, i).
  simpl.
  intros (ga & φs & args & out & cnd & wargs & mid & M & Ma & Mge & ->).
  exists ga, φs, args, out, cnd, wargs, mid.
  refine (conj M (conj _ (conj _ Logic.eq_refl))).
  eauto using match_get_regs_cwle, condition_wires_agree_w, N.lt_le_incl.
  eapply match_add_gentry_cwle; eauto.
Qed.

Lemma translate_instruction_matches gi s :
  let (_, s') := translate_instruction gi s in
  ∃ ges,
  match_instruction gi (st_next_wire s) (st_phi_info s) ges (st_phi_info s') (st_conditions s') ∧
  st_code s' = ges ++ st_code s ∧
  st_next_wire s' = st_next_wire s + nlen ges ∧
  condition_wires_agree (st_next_wire s) (st_conditions s) (st_conditions s').
Proof.
  Opaque get_regs.
  case gi; clear gi. intros g (); simpl; unfold bind; simpl.
  - intros c cnd args.
    get_regs. intros wargs s' (φs & Hargs & Hcode & Hnw & LE).
    add_gentry. intros w s'' (Hentry & Hcode' & Hnw' & -> & LE').
    eexists. split; [ | split ]. 2: rewrite Hcode', Hcode, app_comm_cons; reflexivity.
    rewrite Hnw in *.
    eauto 17 using match_get_regs_cwle.
    split. rewrite Hnw', Hnw, nlen_cons, <- N.add_1_r, N.add_assoc; reflexivity.
    rewrite LE.
    eapply condition_wires_agree_w; eauto. rewrite Hnw. Psatz.lia.
  - intros op args dst.
    get_regs. intros wargs s' (φs & Hargs & Hcode & Hnw & LE).
    add_gentry. intros w s'' (Hentry & Hcode' & Hnw' & -> & LE').
    eexists. split; [ | split ]. 2: rewrite Hcode', Hcode, app_comm_cons; reflexivity.
    rewrite Hnw in *.
    eauto 17 using match_get_regs_cwle.
    split. rewrite Hnw', Hnw, nlen_cons, <- N.add_1_r, N.add_assoc; reflexivity.
    rewrite LE.
    eapply condition_wires_agree_w; eauto. rewrite Hnw. Psatz.lia.
  - intros ϰ addr args dst.
    get_regs. intros wargs s' (φs & Hargs & Hcode & Hnw & LE).
    add_gentry. intros w s'' (Hentry & Hcode' & Hnw' & -> & LE').
    eexists. split; [ | split ]. 2: rewrite Hcode', Hcode, app_comm_cons; reflexivity.
    rewrite Hnw in *.
    eauto 17 using match_get_regs_cwle.
    split. rewrite Hnw', Hnw, nlen_cons, <- N.add_1_r, N.add_assoc; reflexivity.
    rewrite LE.
    eapply condition_wires_agree_w; eauto. rewrite Hnw. Psatz.lia.
  - intros ϰ addr args src.
    get_regs. intros wargs s' (φs & Hargs & Hcode & Hnw & LE).
    add_gentry. intros w s'' (Hentry & Hcode' & Hnw' & -> & LE').
    eexists. split; [ | split ]. 2: rewrite Hcode', Hcode, app_comm_cons; reflexivity.
    rewrite Hnw in *.
    eauto 17 using match_get_regs_cwle.
    split. rewrite Hnw', Hnw, nlen_cons, <- N.add_1_r, N.add_assoc; reflexivity.
    rewrite LE.
    eapply condition_wires_agree_w; eauto. rewrite Hnw. Psatz.lia.
Qed.

Fixpoint match_code (body: RTLC.code) (sz: N) (before: φ_state) (ges: list gentry) (after: φ_state) (cw: condition_wires) : Prop :=
  match body with
  | nil => ges = nil ∧ after = before
  | gi :: body' =>
    ∃ gesL mid gesR,
    ges = gesR ++ gesL ∧
    match_instruction gi sz before gesL mid cw ∧
    match_code body' (sz + nlen gesL) mid gesR after cw
  end.

Lemma match_code_app mid cwi body body' sz before ges ges' after cw :
  condition_wires_agree (sz + nlen ges) cwi cw →
  match_code body sz before ges mid cwi →
  match_code body' (sz + nlen ges) mid ges' after cw →
  match_code (body ++ body') sz before (ges' ++ ges) after cw.
Proof.
  revert body' sz before ges ges' after cw mid cwi.
  elim body; clear.
  - intros ? ? ? ? ? ? ? ? ? ? (-> & ->). rewrite app_nil_r, app_nil_l, N.add_0_r. exact id.
  - intros gi body IH body' sz before ges ges' after cw mid cwi LE (gesL & mid' & gesR & -> & Hmid & Hcode) Hbody'.
    specialize (IH body' (sz + nlen gesL) mid' gesR ges').
    rewrite nlen_app, (N.add_comm (nlen gesR)), N.add_assoc in Hbody'.
    exists gesL, mid'.
    eexists. split. rewrite <- app_assoc. reflexivity.
    rewrite nlen_app, (N.add_comm (nlen gesR)), N.add_assoc in LE.
    split; eauto.
    eapply match_instruction_cwle; eauto.
    erewrite <- (N.min_l (sz + nlen gesL)).
    eauto using condition_wires_agree_trans, condition_wires_agree_refl.
    Psatz.lia.
Qed.

Lemma translate_code_matches body s :
  let '(_, s') := translate_code body s in
  ∃ ges,
    match_code body (st_next_wire s) (st_phi_info s) ges (st_phi_info s') (st_conditions s') ∧
    st_code s' = ges ++ st_code s ∧
    st_next_wire s' = st_next_wire s + nlen ges ∧
    condition_wires_agree (st_next_wire s) (st_conditions s) (st_conditions s').
Proof.
  unfold translate_code.
  elim body using rev_ind; clear.
  - simpl; eauto 6 using condition_wires_agree_refl, N.add_0_r.
  - intros gi body IH.
    rewrite fold_left_app. simpl.
    destruct (fold_left _ _ _) as (w, s'). simpl. clear w.
    destruct IH as (ges & Hges & Hcode & Hnw & LE).
    generalize (translate_instruction_matches gi s').
    case (translate_instruction _ _).
    intros _ s'' (ges' & Hges' & Hcode' & Hnw' & LE').
    exists (ges' ++ ges). split; [ | split ].
    2: rewrite Hcode', Hcode, app_assoc; reflexivity.
    rewrite Hnw in LE'.
    eapply match_code_app; eauto.
    exists ges', (st_phi_info s''), nil.
    apply (conj Logic.eq_refl).
    rewrite <- Hnw. split; eauto.
    rewrite <- Hnw'. red; eauto.
    split. rewrite nlen_app.
    etransitivity. exact Hnw'. rewrite Hnw, <- N.add_assoc.
    f_equal. apply N.add_comm.
    erewrite <- (N.min_l (st_next_wire s)).
    eauto using condition_wires_agree_trans.
    rewrite Hnw. Psatz.lia.
Qed.

Ltac translate_code :=
  match goal with
  | |- appcontext[ translate_code ?body ?s ] =>
    generalize (translate_code_matches body s);
    case (translate_code body s)
  end.

Definition Φ (s: φ_state) (pcm: RTLC.pc_model) (rs: RTLC.regset) (grd: grid) (nc: option ident) : Prop :=
  (∀ r, name_ltb nc (min_name (literal_of_bdd (φ_of_reg s r))) = true) ∧
  bounded_φ_state s (nlen grd) ∧
  ∀ r,
    Val.lessdef (rs # r)
    match eval_phiNode pcm (φ_of_reg s r) with
    | None => Vundef
    | Some w => read_wire grd (Pos.pred_N w)
    end.

Definition match_pcm (pcm: pEnv) (grd: grid) (cw: condition_wires) : Prop :=
  (* ∀ c, In c (get_path_model grd cw) ↔ In c pcm. *)
  pcm = get_path_model grd cw.

Lemma match_pcm_eval_bdd pcm grd cw :
  match_pcm pcm grd cw →
  ∀ {A} (bdd: bdd A), eval_bdd (get_path_model grd cw) bdd = eval_bdd pcm bdd.
Proof.
  intros M A bdd.
  (* apply eval_bdd_m, M. *)
  red in M. congruence.
Qed.

Lemma match_pcm_app_vundef pcm grd cw :
  match_pcm pcm grd cw →
  match_pcm pcm (grd ++ Vundef :: nil) cw.
Proof.
  unfold match_pcm. intros ->.
  unfold get_path_model, get_path_model'. generalize (@nil ident, 0).
  elim grd; clear.
  intros (c, w); simpl. case (condition_of_wire _ _); reflexivity.
  simpl. auto.
Qed.

Lemma match_pcm_add_ncw pcm grd v cw :
  match_pcm pcm grd cw →
  condition_of_wire cw (nlen grd) = None →
  match_pcm pcm (grd ++ v :: nil) cw.
Proof.
  unfold match_pcm. intros ->.
  unfold get_path_model, get_path_model'.
  rewrite fold_left_app. simpl.
  fold (get_path_model' grd val_is_true (condition_of_wire cw)).
  generalize (get_path_model'_nlen grd val_is_true (condition_of_wire cw)).
  destruct (get_path_model' _ _). simpl. intros -> ->. reflexivity.
Qed.

Lemma read_wire_app_vundef grd w :
  read_wire grd w = read_wire (grd ++ Vundef :: nil) w.
Proof.
  rewrite <- (app_nil_r grd) at 1.
  unfold read_wire. rewrite ! nth_app.
  case N.ltb_spec. reflexivity.
  intros LE. case (_ - _); reflexivity.
Qed.

Lemma read_wire_inbounds_or_vundef grd w :
  w < nlen grd ∨ read_wire grd w = Vundef.
Proof.
  case (N.ltb_spec w (nlen grd)). auto.
  intros LE. right. unfold read_wire.
  rewrite <- (app_nil_r grd), nth_skip. reflexivity. exact LE.
Qed.

Import Smallstep.
Import Memory.

Definition input_lessdef (io io': option (slot * Values.val)) : Prop :=
  match io with
  | None => io' = None
  | Some (x, v) => ∃ v', Val.lessdef v v' ∧ io' = Some (x, v')
  end.

Definition output_lessdef (io io': option (Values.val * ident)) : Prop :=
  match io with
  | None => io' = None
  | Some (v, x) => ∃ v', Val.lessdef v v' ∧ io' = Some (v', x)
  end.

Definition match_state (s: RTLC.state) (s': ValCirc.state) : Prop :=
  match s with
  | RTLC.InitState fn m =>
    wf_body (RTLC.fn_code fn) ∧
    s' = ValCirc.InitState (translate_function fn) m
  | RTLC.InputState io ins sp ssz body m outs =>
    wf_body body ∧
    ∃ cw body' m' io',
    s' = ValCirc.InputState io' ins sp ssz cw body' m' outs ∧
    input_lessdef io io' ∧
    Mem.extends m m' ∧
    ∃ after,
    match_code body 0 (PTree.empty _) (rev body') after cw
  | RTLC.InputFenceState sp ssz body m outs =>
    wf_body body ∧
    ∃ cw body' m',
    s' = ValCirc.InputFenceState sp ssz cw body' m' outs ∧
    Mem.extends m m' ∧
    ∃ after,
    match_code body 0 (PTree.empty _) (rev body') after cw
  | RTLC.PostInputState sp ssz body m outs =>
    wf_body body ∧
    ∃ cw body' m',
    s' = ValCirc.PostInputState sp ssz cw body' m' outs ∧
    Mem.extends m m' ∧
    ∃ after,
    match_code body 0 (PTree.empty _) (rev body') after cw
  | RTLC.OutputFenceState sp ssz m outs =>
    ∃ m', Mem.extends m m' ∧ s' = ValCirc.OutputFenceState sp ssz m' outs
  | RTLC.PreOutputState sp ssz m outs =>
    ∃ m', Mem.extends m m' ∧ s' = ValCirc.PreOutputState sp ssz m' outs
  | RTLC.OutputState io outs sp ssz m =>
    ∃ io' m',
    output_lessdef io io' ∧
    Mem.extends m m' ∧
    s' = ValCirc.OutputState io' outs sp ssz m'
  | RTLC.FinishingState sp ssz m =>
    ∃ m', Mem.extends m m' ∧ s' = ValCirc.FinishingState sp ssz m'
  | RTLC.FinalState => s' = ValCirc.FinalState
  | RTLC.State sp ssz body pcm rs m outs =>
    wf_body body ∧
    ∃ cw body' grd m',
    s' = ValCirc.State sp ssz cw body' grd m' outs ∧
    Mem.extends m m' ∧
    match_pcm pcm grd cw ∧
    ∃ before after,
    match_code body (nlen grd) before (rev body') after cw ∧
    Φ before pcm rs grd (first_condition body)
  end.

Context (p: RTLC.program).

Lemma fn_inputs_preserved {fn} :
  fn_inputs (translate_function fn) = RTLC.fn_inputs fn.
Proof. unfold translate_function. case translate_code. reflexivity. Qed.

Lemma fn_stacksize_preserved {fn} :
  fn_stacksize (translate_function fn) = RTLC.fn_stacksize fn.
Proof. unfold translate_function. case translate_code. reflexivity. Qed.

Lemma fn_outputs_preserved {fn} :
  fn_outputs (translate_function fn) = RTLC.fn_outputs fn.
Proof. unfold translate_function. case translate_code. reflexivity. Qed.

Lemma bounded_φ_state_add s r g w n :
  Pos.pred_N w < n + 1 →
  bounded_φ_state s n →
  bounded_φ_state (PTree.set r (phi_add g w (φ_of_reg s r)) s) (n + 1).
Proof.
  intros LT.
  intros H r' w'.
  unfold φ_of_reg. rewrite PTree.gsspec. case peq.
  - intros -> IN. apply leaves_of_phi_add in IN.
    destruct IN as [ -> | IN ]. exact LT.
    generalize (H _ _ IN). Psatz.lia.
  - intros NE IN. generalize (H _ _ IN). clear. Psatz.lia.
Qed.

Lemma bounded_φ_state_w n {s m}:
  n <= m →
  bounded_φ_state s n →
  bounded_φ_state s m.
Proof.
  intros LE. intros H r' w' F.
  specialize (H _ _ F). Psatz.lia.
Qed.

Lemma val_lessdef_of_undef v :
  Val.lessdef v Vundef → v = Vundef.
Proof. now inversion 1. Qed.

Lemma name_ltb_add g r s nc w :
  bounded_bdd' g nc →
  (∀ r', name_ltb nc (min_name (literal_of_bdd (φ_of_reg s r'))) = true) →
  ∀ r',
    name_ltb nc
             (min_name
                (literal_of_bdd
                   (φ_of_reg
                      (PTree.set r (phi_add g w (φ_of_reg s r)) s) r'))) = true.
Proof.
  intros NC A.
  intros r'. specialize (A r').
  rewrite bounded_bdd_iff. destruct nc as [ nc | ]; auto.
  rewrite bounded_bdd_iff in A.
  rewrite <- (reflect_iff _ _ (check_bounded_bdd_iff _ _)).
  rewrite <- (reflect_iff _ _ (check_bounded_bdd_iff _ _)) in A.
  unfold φ_of_reg. rewrite PTree.gsspec. case peq. 2: auto.
  intros ->. intros w' Hw. 
  rewrite <- ssrlib.InE in Hw.
  generalize (@literal_of_phi_add _ g w (match s!r with Some φ => φ | None => Leaf None end) w' Hw).
  clear Hw; rewrite ssrlib.InE; intros Hw.
  rewrite in_app in Hw.
  destruct Hw as [ Hw | Hw ].
  exact (NC _ Hw). apply A, Hw.
Qed.

Opaque eval_bdd.

Lemma lessdef_readwire_add v grd w v' :
  Val.lessdef v (read_wire grd w) →
  Val.lessdef v (read_wire (grd ++ v' :: nil) w).
Proof.
  case (read_wire_inbounds_or_vundef grd w).
  intros LT H.
  unfold read_wire. rewrite nth_app, (proj2 (N.ltb_lt _ _) LT). exact H.
  intros -> H. apply val_lessdef_of_undef in H. subst. constructor.
Qed.

Lemma run_φ_node pcm rs g r before nc φs w after sp ssz cw tl grd m outs :
  bounded_bdd' g nc →
  match_pcm pcm grd cw →
  Φ before pcm rs grd nc →
  match_get_reg g r (nlen grd) before φs w after cw →
  ∃ grd',
    star ValCirc.step (Genv.globalenv (translate_program p))
         (State sp ssz cw (ocons φs tl) grd m outs)
         Events.E0
         (State sp ssz cw tl (grd ++ grd') m outs) ∧
    nlen grd' = olen φs ∧
    (if eval_pcond pcm g then Val.lessdef (rs # r) (read_wire (grd ++ grd') w) else True) ∧
    match_pcm pcm (grd ++ grd') cw ∧
    Φ after pcm rs (grd ++ grd') nc.
Proof.
  intros NC M X.
  generalize (proj2 (proj2 X) r).
  unfold match_get_reg, match_add_gentry, φ_of_reg.
  destruct (_ ! _) as [ φ | ] eqn: H;
    [ destruct (phi_slice _ _) as [ [ x | ] | a b c ] eqn: H' | ];
    intros LD;
    intros;
    repeat match goal with
           | H : ?a = ?b |- _ => subst a || subst b
           | H : _ ∧ _ |- _ => destruct H
           end;
    try (exists nil; rewrite app_nil_r; split; [ apply star_refl | split; [ reflexivity | split; auto ] ]).
  destruct (eval_pcond _ _) eqn: G; auto.
  rewrite <- (phi_sliceP φ G), H' in LD. assumption.
  destruct (eval_pcond _ _) eqn: G; auto.
  rewrite <- (phi_sliceP φ G), H' in LD. apply val_lessdef_of_undef in LD.
  rewrite LD. right.
  Focus 2.
  destruct (eval_pcond _ _) eqn: G; auto.
  apply val_lessdef_of_undef in LD. rewrite LD. right.

  eexists; (split; [ eapply star_one; (split; [ reflexivity | ]) | ] );
    try rewrite <- M, G;
    try (rewrite <- H', phi_sliceP by apply G; clear a b c H').
  simpl; eauto 6.
  split. reflexivity.
  destruct X as ( A & B & X ).
  simpl in H'. rewrite <- H'. clear a b c H'.
  split.
  red in M. rewrite M in *.
  destruct (eval_bdd _ g) eqn: G. 2: exact I.
  rewrite phi_sliceP by apply G.
  unfold read_wire. rewrite nth_skip by apply N.le_refl.
  rewrite N.sub_diag. exact LD.
  split. auto using match_pcm_add_ncw.
  split. rewrite (fold_φ_of_reg H). apply name_ltb_add; assumption.
  split.
  rewrite nlen_app, nlen_cons.
  generalize (λ x, bounded_φ_state_add before r g (N.succ_pos (nlen grd)) (nlen grd) x B).
  unfold φ_of_reg. rewrite H. refine (λ X, X _).
  rewrite N.pos_pred_succ, N.add_1_r.
  apply N.lt_succ_diag_r.

  red in M. rewrite M in *.
  intros r'; generalize (X r'); unfold φ_of_reg at 2; rewrite PTree.gsspec.
  case peq. intros ->. rewrite phi_addP.
  destruct (eval_bdd _ g) eqn: G.
  unfold read_wire. rewrite N.pos_pred_succ.
  rewrite nth_skip by apply N.le_refl.
  unfold φ_of_reg.
  rewrite N.sub_diag, H. simpl.
  rewrite phi_sliceP by exact G. exact id.
  unfold φ_of_reg. rewrite H.
  destruct (eval_phiNode _ _). 2: exact id.
  apply lessdef_readwire_add.
  intros NE.
  change (bdd (option_eqType eqp_eqType)) with phiNode.
  fold (φ_of_reg before r').
  destruct (eval_phiNode _ (φ_of_reg _ r')). 2: exact id.
  apply lessdef_readwire_add.
Qed.

Lemma lessdef_list_extend vs grd grd' ws :
  Val.lessdef_list vs (read_wires grd ws) →
  Val.lessdef_list vs (read_wires (grd ++ grd') ws).
Proof.
  intros H.
  apply lessdef_list_map.
  apply (lessdef_list_map (read_wire grd)) in H. revert H.
  apply forall2_weaken. clear.
  intros v w.
  unfold read_wire. rewrite <- (app_nil_r grd) at 1.
  rewrite ! nth_app.
  case (N.ltb_spec). auto. intros _.
  intros H. apply val_lessdef_of_undef in H.
  subst v. constructor.
Qed.

Lemma run_φ_nodes sp ssz cw tl m outs {pcm rx g rs before nc φs ws after grd}:
  bounded_bdd' g nc →
  match_pcm pcm grd cw →
  Φ before pcm rx grd nc →
  match_get_regs g rs (nlen grd) before φs ws after cw →
  ∃ grd',
    star ValCirc.step (Genv.globalenv (translate_program p))
         (State sp ssz cw (rev φs ++ tl) grd m outs) Events.E0
         (State sp ssz cw tl (grd ++ grd') m outs) ∧
    nlen grd' = nlen φs ∧
    (if eval_pcond pcm g then Val.lessdef_list (rx ## rs) (read_wires (grd ++ grd') ws) else True) ∧
    match_pcm pcm (grd ++ grd') cw ∧
    Φ after pcm rx (grd ++ grd') nc.
Proof.
  intros NC Hpcm X.
  revert φs ws after tl.
  elim rs; clear - NC Hpcm X.
  simpl. intros ? ? ? ? (-> & -> & ->). exists nil. rewrite app_nil_r.
  split. apply star_refl. split. reflexivity. split; auto. case eval_pcond; constructor.
  intros r rs IH φs ws after tl (φL & w & mid & φR & ws' & -> & -> & M & REC).
  specialize (IH _ _ _ (ocons φL tl) REC). clear REC.
  destruct IH as (grd' & IH & Hlen & LD & Hpcm' & X').
  rewrite rev_ocons_app.
  destruct (run_φ_node pcm rx g r mid nc φL w after sp ssz cw tl (grd ++ grd') m outs NC Hpcm' X')
    as (grdφ & STEPS & Hlen' & LD' & H & Y).
  rewrite nlen_app, Hlen. exact M.
  exists (grd' ++ grdφ). split.
  eapply star_trans. exact IH.
  rewrite app_assoc. exact STEPS. reflexivity.
  split. rewrite ! nlen_app, Hlen, nlen_ocons, N.add_comm. congruence.
  split. 2: rewrite app_assoc; auto.
  destruct eval_pcond; auto.
  simpl. constructor.
  rewrite app_assoc. auto.
  revert ws' LD. clear.
  rewrite app_assoc.
  apply lessdef_list_extend.
Qed.

Lemma match_get_reg_read_wire {g r grd before nc φs w after cw pcm rs} :
  eval_pcond pcm g = true →
  match_get_reg g r (nlen grd) before φs w after cw →
  Φ before pcm rs grd nc →
  Val.lessdef (rs # r) (read_wire (grd ++ match φs with None => nil | _ => rs # r :: nil end) w).
Proof.
  intros G.
  unfold match_get_reg.
  destruct (_ ! _) as [ φ | ] eqn: H.
  - generalize (phi_sliceP φ G).
    destruct (phi_slice _ _) as [ [ x | ] | a b c ]; intros EV.
    + intros (-> & -> & LT & ->).
      intros (_ & _ & L). specialize (L r). unfold φ_of_reg in L. rewrite H, <- EV in L. simpl in L.
      unfold read_wire. rewrite nth_app. rewrite (proj2 (N.ltb_lt _ _) LT). exact L.
    + intros (-> & -> & ->).
      intros (_ & _ & L). specialize (L r). unfold φ_of_reg in L. rewrite H, <- EV in L. simpl in L.
      apply val_lessdef_of_undef in L; rewrite L; right.
    + intros (M & -> & ->).
      destruct M as (-> & M).
      intros _.
      unfold read_wire. rewrite nth_skip, N.sub_diag by apply N.le_refl. left.
  - intros (-> & -> & ->).
    intros (_ & _ & L). specialize (L r). unfold φ_of_reg in L. rewrite H in L. simpl in L.
    apply val_lessdef_of_undef in L; rewrite L; right.
Qed.

Lemma get_path_model_app_ncw cw grd v :
  condition_of_wire cw (nlen grd) = None →
  get_path_model grd cw = get_path_model (grd ::: v) cw.
Proof.
  intros H.
  unfold get_path_model, get_path_model'.
  rewrite fold_left_app. simpl.
  fold (get_path_model' grd val_is_true (condition_of_wire cw)).
  generalize (get_path_model'_nlen grd val_is_true (condition_of_wire cw)).
  destruct (get_path_model' _ _) as (pcm, n). intros ->.
  rewrite H. reflexivity.
Qed.

Lemma get_path_model_app_cw cw grd (b: bool) c :
  condition_of_wire cw (nlen grd) = Some c →
  let pcm := get_path_model grd cw in
  (if b then c :: pcm else pcm) = get_path_model (grd ++ (if b then Vtrue else Vfalse) :: nil) cw.
Proof.
  intros H.
  unfold get_path_model, get_path_model'.
  rewrite fold_left_app. simpl.
  fold (get_path_model' grd val_is_true (condition_of_wire cw)).
  generalize (get_path_model'_nlen grd val_is_true (condition_of_wire cw)).
  destruct (get_path_model' _ _) as (pcm, n). intros ->.
  rewrite H.
  case b; simpl; unfold val_is_true; case Val.eq; intuition discriminate.
Qed.

Lemma name_ltb_tail g i body y :
  sorted_names (condition_names ((g, i) :: body)) = true →
  name_ltb (first_condition ((g, i) :: body)) y = true →
  name_ltb (first_condition body) y = true.
Proof.
  destruct i; auto. simpl.
  rewrite first_condition_name.
  destruct (condition_names _) as [ | z names ] eqn: Hz. reflexivity.
  destruct y as [ y | ]; simpl. 2: easy.
  intros X Y. apply Pos.ltb_lt. apply Pos.ltb_lt in Y.
  revert X.
  case (Pos.ltb_spec z _). 2: discriminate. Psatz.lia.
Qed.

Lemma bounded_bdd'_tail {A: eqType} g i body (φ: bdd A) :
  sorted_names (condition_names ((g, i) :: body)) = true →
  bounded_bdd' φ (first_condition ((g, i) :: body)) →
  bounded_bdd' φ (first_condition body).
Proof.
  destruct i; auto. simpl.
  rewrite first_condition_name.
  destruct (condition_names _) as [ | z names ] eqn: Hz. easy.
  simpl.
  case (Pos.ltb_spec z _). 2: discriminate.
  intros LT _ H q IN. specialize (H _ IN).
  Psatz.lia.
Qed.

Lemma eventval_valid_transf {ev} :
  Events.eventval_valid (Genv.globalenv p) ev →
  Events.eventval_valid (Genv.globalenv (translate_program p)) ev.
Proof.
  destruct ev; auto.
  simpl. intros <-.
  apply Genv.public_symbol_transf.
Qed.

Lemma eventval_match_transf {ev ty v} :
  Events.eventval_match (Genv.globalenv p) ev ty v →
  Events.eventval_match (Genv.globalenv (translate_program p)) ev ty v.
Proof.
  unfold translate_program.
  intros H; inv H; constructor.
  simpl. rewrite Genv.public_symbol_transf. assumption.
  simpl. rewrite Genv.find_symbol_transf. assumption.
Qed.

Lemma symbol_address_lessdef x o :
  Val.lessdef (Genv.symbol_address (globalenv (RTLC.semantics p)) x o) (Genv.symbol_address (Genv.globalenv (translate_program p)) x o).
Proof.
  simpl.
  unfold Genv.symbol_address, translate_program.
  rewrite Genv.find_symbol_transf. left.
Qed.

Theorem simulation :
  (∀ x fn, In (x, Gfun (Internal fn)) (prog_defs p) → wf_body (RTLC.fn_code fn)) →
  forward_simulation (RTLC.semantics p) (ValCirc.semantics (translate_program p)).
Proof.
  intros WFB.
  refine (forward_simulation_plus (RTLC.semantics p) (ValCirc.semantics (translate_program p)) _ match_state _ _ _).
  - apply Genv.public_symbol_transf.
  - intros ? (m & b & fn & Hm & Hb & Hfn & ->).
    eexists. split.
    + exists m, b, (translate_function fn).
      split. apply Genv.init_mem_transf, Hm.
      split. unfold translate_program. rewrite Genv.find_symbol_transf. exact Hb.
      split. exact (Genv.find_funct_ptr_transf translate_fundef _ _ Hfn).
      reflexivity.
    + split.
      pose proof (Genv.find_funct_ptr_symbol_inversion _ _ Hb Hfn) as IN.
      exact (WFB _ _ IN).
      reflexivity.
  - simpl. unfold RTLC.final_state.
    intros ? ? ? M [ -> -> ]. split; auto.
  - intros ().
    + intros fn m tr s'. simpl.
      destruct (Mem.alloc _ _ _) as (m', sp) eqn: Hm.
      intros (-> & ->) ? (Hwfb & ->).
      eexists. split. apply plus_one. simpl. rewrite fn_stacksize_preserved, Hm.
      apply (conj Logic.eq_refl).
      rewrite fn_inputs_preserved, fn_outputs_preserved.
      reflexivity.
      split. assumption.
      eexists _, _, _, _.
      apply (conj Logic.eq_refl).
      apply (conj Logic.eq_refl).
      apply (conj (Mem.extends_refl _)).
      unfold translate_function.
      translate_code. intros _ s (ges & M & Hcode & LE).
      simpl. unfold rev'; rewrite <- rev_alt, rev_involutive.
      rewrite app_nil_r in Hcode. subst ges.
      eauto.

    + intros [ ((x, o), v) | ] ins sp ssz body m outs.
      * (* Running input *)
        intros tr s H'.
        simpl in H'.
        assert (tr = Events.E0 ∧
                ∃ m', Mem.storev Mint8unsigned m (Genv.symbol_address (Genv.globalenv p) x o) v = Some m' ∧
                      s = RTLC.InputState None ins sp ssz body m' outs
               ) as H.
        { destruct ins as [ | (?, ?) ]; auto. }
        clear H'.
        destruct H as (-> & m' & Hm' & ->).
        intros ? (Hwfb & cw & body' & m'' & ? & -> & (v' & Hv' & ->) & Mm & M).
        destruct (Mem.storev_extends _ _ _ _ _ _ _ _ Mm Hm' (symbol_address_lessdef _ _) Hv') as (q & Hq & Q).
        eexists. split. apply plus_one.
        simpl. destruct ins as [ | (?, ?) ]; eauto.
        simpl. eauto 9.

      * destruct ins as [ | (?, ?) ? ].
        (* After last input *)
        intros ? ? (-> & ->).
        intros ? (Hwfb & cw & body' & m' & ? & -> & -> & Mm & M).
        eexists. split. apply plus_one.
        simpl. eauto.
        simpl. eauto 7.

        (* Input *)
        intros ? ? (b & ev & v & V & Hb & -> & Hev & Hv & ->).
        intros ? (Hwfb & cw & body' & m' & ? & -> & -> & Mm & M).
        eexists. split. apply plus_one.
        eexists _, _, _. split.
        unfold translate_program. simpl. rewrite Genv.block_is_volatile_transf. exact V.
        split. unfold translate_program. simpl. rewrite Genv.find_symbol_transf. exact Hb.
        apply (conj Logic.eq_refl).
        split. apply eventval_valid_transf; assumption.
        split. eapply eventval_match_transf; eassumption.
        reflexivity.
        simpl. eauto 11.

    + (* After last input *)
      intros sp ssz body m outs.
      intros ? ? (-> & ->).
      intros ? (Hwfb & cw & body' & q & -> & Q & after & M).
      eexists. split. apply plus_one. simpl. eauto.
      simpl. eauto 8.

    + (* After input fence *)
      intros sp ssz body m outs.
      intros ? ? (-> & ->).
      intros ? (Hwfb & cw & body' & q & -> & Q & after & M).
      eexists. split. apply plus_one. simpl. eauto.
      apply (conj Hwfb).
      exists cw, body', nil, q.
      split. reflexivity.
      split. exact Q.
      split. reflexivity.
      eexists _, after.
      split. exact M.
      split. intros r. simpl. unfold φ_of_reg. rewrite PTree.gempty.
      destruct (first_condition _); reflexivity.
      split.
      intros r w. unfold φ_of_reg. rewrite PTree.gempty. intros ().
      intros r. rewrite Regmap.gi. unfold φ_of_reg. simpl. rewrite PTree.gempty. left.

    + simpl.
      intros sp ssz [ | (g, i) body ] pcm rs m outs.
      * (* After last instruction *)
        intros ? ? (-> & ->).
        intros ? (Hwfb & cw & body' & grd & m' & -> & Hm' & M).
        eexists. split. apply plus_one.
        cut (body' = nil). intros ->. simpl. auto.
        destruct M as (M & before & after & (H & ->) & _).
        apply (rev_nil_inv _ H).
        simpl. eauto.

        (* Body step *)
      * {
          intros ? s' [ -> STEP ].
          intros ? (Hwfb & cw & body' & grd & q & -> & Q & M).
          destruct M as (Hpcm & before & after & M & MR).
          destruct M as (gesL & mid & gesR & Hbody' & MI & Hbody).
          apply rev_is_app in Hbody'. subst body'.
          simpl in MI.
          destruct MI as (ga & φs & ins & out & cnd & wargs & mid' & Mg & Margs & Mge & ->).
          simpl. rewrite <- app_assoc. simpl.
          match goal with
          | |- appcontext[ _ ++ ?a ] => set (tl := a)
          end.
          pose proof (guards_refer_to_past_conditions_bounded _ _ _ (wfb_guards _ Hwfb)) as G'.
          destruct (run_φ_nodes sp ssz cw tl q outs G' Hpcm MR Margs) as (grd' & STEPS & Hlen & Hargs' & Hpcm' & MR').
          assert (eval_pcond (get_path_model (grd ++ grd') cw) g = eval_pcond (get_path_model grd cw) g)
            as EVPC.
          erewrite match_pcm_eval_bdd; eauto. unfold match_pcm in *. congruence.
          destruct Mge as (Mge & <-).
          subst tl.

          destruct (eval_pcond pcm g) eqn: G.
          Focus 2.
          subst s'.
          assert (∃ v m', eval_gate (Genv.globalenv (translate_program p)) sp
                                    (get_path_model (grd ++ grd') cw) (grd ++ grd') ga
                                    (read_wires (grd ++ grd') wargs) q v m'
                          ∧ Mem.extends m m'
                          ∧ match_pcm pcm ((grd ++ grd') ++ v :: nil) cw) as X.
          {
            rewrite <- Hlen, <- nlen_app in Mg.
            destruct i; simpl in Mg;
            repeat match goal with
                   | H : ?a = ?b |- _ => subst a || subst b
                   | H : _ ∧ _ |- _ => destruct H
                   end;
            simpl;
            eauto 7 using match_pcm_add_ncw.
            eexists _, _.
            rewrite EVPC, (match_pcm_eval_bdd _ _ _ Hpcm), G.
            eauto using match_pcm_app_vundef.
            eexists _, _.
            rewrite EVPC, (match_pcm_eval_bdd _ _ _ Hpcm), G.
            eauto using match_pcm_app_vundef. }
          destruct X as (v & m' & X & Q' & M').
          eexists. split.
          eapply star_plus_trans. exact STEPS.
          apply plus_one. split. reflexivity. eauto. reflexivity.
          split. eauto using wf_body_tail.
          eexists _, _, _, _.
          apply (conj Logic.eq_refl).
          apply (conj Q').
          apply (conj M').
          eexists _, _. split.
          rewrite ! nlen_app, nlen_cons. simpl.
          rewrite nlen_cons, <- N.add_1_r, N.add_assoc in Hbody.
          rewrite Hlen, rev_involutive. exact Hbody.
          destruct out as [ out | ]; simpl in Mge; subst mid.
          split.
          generalize ((proj1 MR')).
          clear -Hwfb G'. intros H r.
          apply name_ltb_add.
          eapply bounded_bdd'_tail, G'; apply Hwfb.
          intros r'; eapply name_ltb_tail, H; apply Hwfb.
          split.
          rewrite nlen_app, nlen_cons. simpl.
          apply bounded_φ_state_add, MR'.
          rewrite <- Hlen, N.pos_pred_succ, nlen_app. Psatz.lia.
          intros r; generalize (proj2 (proj2 MR') r).
          unfold φ_of_reg at 2. rewrite PTree.gsspec. case peq.
          intros ->. rewrite phi_addP, G.
          destruct (eval_phiNode _ _).
          apply lessdef_readwire_add.
          exact id.
          intros NE. fold (φ_of_reg mid' r).
          destruct (eval_phiNode _ _).
          apply lessdef_readwire_add.
          exact id.
          split. intros r'; eapply name_ltb_tail, MR'; apply Hwfb.
          split.
          rewrite nlen_app, nlen_cons. simpl.
          eapply bounded_φ_state_w, MR'; Psatz.lia.
          intros r; generalize (proj2 (proj2 MR') r). clear.
          destruct (eval_phiNode _ _).
          apply lessdef_readwire_add.
          exact id.

          destruct i as [ c cond args | op args dst | ϰ addr args dst | ϰ addr args src ];
            simpl in Mg;
          repeat
            match goal with
            | H : ?a = ?b |- _ => subst a || subst b; simpl in *
            | H : _ ∧ _ |- _ => destruct H as [? H]
            end; simpl in *.
          - {
          destruct STEP as (b & Hb & ->).
          pose proof (Op.eval_condition_lessdef _ Hargs' Q Hb) as Hb'.
          eexists. split.
          eapply star_plus_trans. exact STEPS.
          apply plus_one. split. reflexivity.
          eexists _, _. split.
          simpl.
          rewrite EVPC, (match_pcm_eval_bdd _ _ _ Hpcm), G. eauto.
          reflexivity. reflexivity.
          split. eauto using wf_body_tail.
          eexists _, _, _, _.
          apply (conj Logic.eq_refl).
          apply (conj Q).
          split.
          etransitivity. 2: apply get_path_model_app_cw.
          case b; f_equal; exact Hpcm'.
          rewrite nlen_app, Hlen. assumption.
          eexists _, _. split.
          rewrite ! nlen_app, nlen_cons. simpl.
          rewrite nlen_cons, <- N.add_1_r, N.add_assoc in Hbody.
          rewrite Hlen, rev_involutive. exact Hbody.

          split. intros r'; eapply name_ltb_tail. eapply Hwfb. exact (proj1 MR' r').
          split.
          rewrite nlen_app, nlen_cons.
          eapply bounded_φ_state_w, MR'. Psatz.lia.
          intros r. generalize (proj2 (proj2 MR') r).
          assert (eval_phiNode (if b then c :: pcm else pcm) (φ_of_reg mid' r) =
                  eval_phiNode pcm (φ_of_reg mid' r)) as Hcut.
          { destruct b. 2: reflexivity.
            symmetry. apply eval_bounded.
            generalize (proj1 MR' r).
            rewrite bounded_bdd_iff.
            apply (reflect_iff _ _ (check_bounded_bdd_iff _ _)). }
          unfold RTLC.pc_model, pEnv in *. rewrite Hcut. clear Hcut.
          destruct (eval_phiNode _ _) as [ w | ] eqn: Hw.
          2: clear; intros H; apply val_lessdef_of_undef in H; rewrite H; right.
          pose proof (proj1 (proj2 MR') _ _ (eval_phiNode_leaf _ _ _ Hw)) as LT.
          unfold read_wire at 2. rewrite nth_app.
          rewrite (proj2 (N.ltb_lt _ _) LT). exact id.
          }

          - {
          eexists. split.
          eapply star_plus_trans. exact STEPS.
          apply plus_one. split. reflexivity.
          eexists _, q. split. simpl. eauto.
          reflexivity. reflexivity.
          split. eauto using wf_body_tail.
          eexists _, _, _, _.
          apply (conj Logic.eq_refl).
          apply (conj Q).
          split.
          etransitivity. 2: apply get_path_model_app_ncw.
          exact Hpcm'. rewrite nlen_app, Hlen. assumption.
          eexists _, _. split.
          rewrite ! nlen_app, nlen_cons. simpl.
          rewrite nlen_cons, <- N.add_1_r, N.add_assoc in Hbody.
          rewrite Hlen, rev_involutive. exact Hbody.

          split. intros r'. apply name_ltb_add. auto.
          clear r'. intros r'. eapply name_ltb_tail. apply Hwfb. apply MR'.
          split.
          rewrite nlen_app, nlen_cons.
          apply bounded_φ_state_add, MR'.
          rewrite <- Hlen, N.pos_pred_succ, nlen_app. Psatz.lia.
          intros r; rewrite Regmap.gsspec.
          unfold φ_of_reg. rewrite PTree.gsspec.
          case peq.
          intros ->. rewrite phi_addP, G, <- Hlen.
          rewrite N.pos_pred_succ.
          unfold read_wire. rewrite nth_skip by (rewrite nlen_app; Psatz.lia).
          rewrite nlen_app, N.sub_diag.
          unfold RTLC.eval_operation at 2.
          erewrite Op.eval_operation_preserved by (apply Genv.find_symbol_transf).
          eapply RTLC.eval_operation_lessdef; eauto.
          fold (φ_of_reg mid' r). intros NE.
          generalize (proj2 (proj2 MR') r). generalize (proj1 (proj2 MR') r). clear.
          intros H.
          destruct (eval_phiNode _ _) as [ w | ] eqn: Hw. 2: exact id.
          specialize (H _ (eval_phiNode_leaf _ _ _ Hw)).
          unfold read_wire at 2. rewrite nth_app.
          rewrite (proj2 (N.ltb_lt _ _) H). exact id.
          }

          - {
          eexists. split.
          eapply star_plus_trans. exact STEPS.
          apply plus_one. split. reflexivity.
          simpl. eauto. reflexivity.
          split. eauto using wf_body_tail.
          eexists _, _, _, _.
          apply (conj Logic.eq_refl).
          apply (conj Q).
          split.
          etransitivity. 2: apply get_path_model_app_ncw.
          exact Hpcm'. rewrite nlen_app, Hlen. assumption.
          eexists _, _. split.
          rewrite ! nlen_app, nlen_cons. simpl.
          rewrite nlen_cons, <- N.add_1_r, N.add_assoc in Hbody.
          rewrite Hlen, rev_involutive. exact Hbody.
          split.
          intros r'. apply name_ltb_add. exact G'. clear r'.
          intros r'. eapply name_ltb_tail. apply Hwfb. apply MR'.
          split.
          rewrite nlen_app, nlen_cons.

          apply bounded_φ_state_add, MR'.
          rewrite <- Hlen, N.pos_pred_succ, nlen_app. Psatz.lia.
          intros r; rewrite Regmap.gsspec.
          unfold φ_of_reg. rewrite PTree.gsspec.
          case peq.
          intros ->. rewrite phi_addP, G, <- Hlen.
          rewrite N.pos_pred_succ.
          unfold read_wire. rewrite nth_skip by (rewrite nlen_app; Psatz.lia).
          rewrite nlen_app, N.sub_diag. simpl.
          unfold RTLC.eval_addressing at 2.
          erewrite Op.eval_addressing_preserved by apply Genv.find_symbol_transf.
          eauto using RTLC.mem_loadv_lessdef, RTLC.eval_addressing_lessdef.
          fold (φ_of_reg mid' r). intros NE.
          generalize (proj2 (proj2 MR') r). generalize (proj1 (proj2 MR') r). clear.
          intros H.
          destruct (eval_phiNode _ _) as [ w | ] eqn: Hw. 2: exact id.
          specialize (H _ (eval_phiNode_leaf _ _ _ Hw)).
          unfold read_wire at 2. rewrite nth_app.
          rewrite (proj2 (N.ltb_lt _ _) H). exact id.
          }

          - {
          destruct STEP as (m' & Hm' & ->).
          unfold read_wires in Hargs'. apply lessdef_list_map in Hargs'.
          apply forall2_cons_inv in Hargs'.
          destruct Hargs' as (wsrc & wargs' & -> & Hsrc & Hargs').
          apply lessdef_list_map in Hargs'.
          pose proof (@RTLC.eval_addressing_lessdef _ _ (Genv.globalenv p) sp addr _ _ Hargs') as Hptr'.

          destruct (Mem.storev_extends _ _ _ _ _ _ _ _ Q Hm' Hptr' Hsrc) as (q' & Hq' & Q').

          eexists. split.
          eapply star_plus_trans. exact STEPS.
          apply plus_one. split. reflexivity.
          simpl.
          rewrite EVPC, (match_pcm_eval_bdd _ _ _ Hpcm), G.
          exists Vundef, q'. split.
          eexists _, _. apply (conj Logic.eq_refl).
          unfold translate_program, RTLC.eval_addressing.
          rewrite (Op.eval_addressing_preserved _ _ (Genv.find_symbol_transf _ p)).
          auto. reflexivity. reflexivity.
          split. eauto using wf_body_tail.
          eexists _, _, _, _.
          apply (conj Logic.eq_refl).
          apply (conj Q').
          split.
          etransitivity. 2: apply get_path_model_app_ncw.
          exact Hpcm'. rewrite nlen_app, Hlen. assumption.
          eexists _, _. split.
          rewrite ! nlen_app, nlen_cons. simpl.
          rewrite nlen_cons, <- N.add_1_r, N.add_assoc in Hbody.
          rewrite Hlen, rev_involutive. exact Hbody.
          split.
          intros r'. eapply name_ltb_tail. apply Hwfb. apply MR'.
          split.
          rewrite nlen_app, nlen_cons. simpl.
          eapply bounded_φ_state_w, MR'; Psatz.lia.
          intros r; generalize (proj2 (proj2 MR') r). clear.
          destruct (eval_phiNode _ _).
          rewrite read_wire_app_vundef; exact id. exact id.
          }
        }

    + (* Output fence *)
      intros sp ssz m outs.
      intros ? ? (-> & ->).
      intros ? (q & Q & ->).
      eexists. split. apply plus_one. simpl. eauto.
      simpl. eauto.

    + (* After output fence *)
      intros sp ssz m outs ? ? (-> & ->).
      intros ? (q & Q & ->).
      eexists. split. apply plus_one. simpl. eauto.
      simpl. eauto.

    + intros [ (v, x) | ].
      * (* Output *)
        intros outs sp ssz m.
        intros ? ? (b & ev & V & Hb & -> & Hev & ->).
        intros ? (? & m' & (v' & Hv' & ->) & Q & ->).
        eexists. split. apply plus_one.
        eexists _, _. split.
        unfold translate_program. simpl. rewrite Genv.block_is_volatile_transf. exact V.
        split. unfold translate_program. simpl. rewrite Genv.find_symbol_transf. exact Hb.
        apply (conj Logic.eq_refl).
        split. eapply eventval_match_transf, Events.eventval_match_lessdef; eassumption.
        reflexivity.
        simpl. eauto.

      * intros [ | ((x, o), dst) ] sp ssz m.
        (* After last output *)
        intros ? ? (-> & ->).
        intros ? (? & m' & -> & Hm' & ->).
        eexists. split. apply plus_one. simpl. eauto.
        simpl. eauto.

        (* Next output *)
        intros ? ? (-> & v & Hv & ->).
        intros ? (? & m' & -> & Mm & ->).
        destruct (Mem.loadv_extends _ _ _ _ _ _ Mm Hv (symbol_address_lessdef _ _)) as (v' & Hv' & LD).
        eexists. split. apply plus_one. simpl. eauto.
        simpl. eauto 7.

    + intros sp ssz m tr ? (-> & (b & -> & m' & Hm' & ->)) ? (q & Q & ->).
      destruct (Mem.free_parallel_extends _ _ _ _ _ _ Q Hm') as (q' & Hq' & Q').
      eexists. split. apply plus_one. simpl. eauto 6. reflexivity.
    + intros ? ? ().
Qed.

Corollary simulation_with_check p' :
  check_and_translate_program p = Errors.OK p' →
  forward_simulation (RTLC.semantics p) (ValCirc.semantics p').
Proof.
  intros H. apply check_and_translate_program_OK in H.
  destruct H as [ <- H ]. revert H.
  exact simulation.
Qed.

End SIMULATION.
