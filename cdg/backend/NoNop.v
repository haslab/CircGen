Require RTL.
Require Import Utf8.
Import Coqlib.
Import Maps.
Import Globalenvs.
Import AST.
Import Smallstep.
Import RTL.

Unset Elimination Schemes.

Section TUNNEL.

  Context (f: code) (entrypoint: node).

  Definition height (pc: node) : nat :=
    (S (Pos.to_nat entrypoint) - Pos.to_nat pc)%nat.

  Definition lt (x y: node) : Prop :=
    (height x < height y)%nat.

  Remark lt_wf : well_founded lt.
  Proof. apply well_founded_ltof. Qed.

  Fixpoint tunnel (pc: node) (m: PTree.t node) (WF: Acc lt pc) : PTree.t node.
  Proof.
    refine (
    let 'Acc_intro REC := WF in
    match plt entrypoint pc with
    | left LT => m
    | right GE =>
      tunnel (Pos.succ pc)
      match f ! pc with
      | Some (Inop pc') =>
        let dst := match m ! pc' with Some q => q | None => pc' end in
        PTree.set pc dst m
      | _ => m
      end
      (REC _ _)
    end).
  Proof.
    clear -GE;
    abstract (unfold Plt in GE; unfold lt, height; Psatz.lia).
  Defined.

  Fixpoint nop_sequence (n: nat) i o : Prop :=
    match n with
    | O => i = o
    | S n' =>
      ∃ p, f ! i = Some (Inop p) ∧ nop_sequence n' p o
    end.

  Definition tunnel_spec (m: PTree.t node) : Prop :=
    ∀ i o,
      m ! i = Some o → ∃ n, nop_sequence (S n) i o.

  Remark empty_tunnel_correct : tunnel_spec (PTree.empty _).
  Proof. intros i o. rewrite PTree.gempty. discriminate. Qed.

  Fixpoint tunnel_correct (pc: node) (m: PTree.t node) (WF: Acc lt pc) :
    tunnel_spec m → tunnel_spec (tunnel pc m WF).
  Proof.
    intros H.
    destruct WF as [ REC ].
    simpl. case plt. auto.
    intros GE.
    apply tunnel_correct. clear tunnel_correct.
    intros i o.
    destruct (f ! pc) as [ () | ] eqn: Hi; auto.
    rewrite PTree.gsspec. case peq; auto.
    intros ->. intros Ho; inv Ho.
    destruct (m ! _) as [ q | ] eqn: Hq.
    destruct (H _ _ Hq) as [ len Hlen ].
    exists (S len). simpl. eauto.
    exists O. simpl. eauto.
  Qed.

  Definition get_dest m pc : node :=
    match m ! pc with
    | Some pc' => pc'
    | None => pc
    end.

  Definition skip_nops s (i: instruction) : instruction :=
    match i with
    | Inop pc => Inop (s pc)
    | Iop op args dst pc => Iop op args dst (s pc)
    | Iload ϰ addr args dst pc => Iload ϰ addr args dst (s pc)
    | Istore ϰ addr args src pc => Istore ϰ addr args src (s pc)
    | Icall sg ros args dst pc => Icall sg ros args dst (s pc)
    | Ibuiltin ef args dst pc => Ibuiltin ef args dst (s pc)
    | Icond cond args a b => Icond cond args (s a) (s b)
    | Ijumptable b tgt => Ijumptable b (map s tgt)
    | Itailcall _ _ _
    | Ireturn _
      => i
    end.

  Definition skip_the_nops (m: PTree.t node) : code :=
    let s pc := get_dest m pc in
    PTree.map (λ _, skip_nops s) f.

End TUNNEL.

Definition transf_function (f: function) : function :=
  let 'mkfunction sg params sz c ep := f in
  let m := tunnel c ep xH (PTree.empty _) (lt_wf ep _) in
  mkfunction sg params sz (skip_the_nops c m) (get_dest m ep).

Lemma transf_function_at {f pc i} :
  (fn_code f) ! pc = Some i →
  (fn_code (transf_function f)) ! pc = Some (skip_nops (get_dest (
                                                            tunnel (fn_code f) (fn_entrypoint f) xH (PTree.empty _) (lt_wf (fn_entrypoint f) _))) i).
Proof.
  intros H.
  destruct f; simpl in *.
  unfold skip_the_nops. rewrite PTree.gmap, H. reflexivity.
Qed.

Lemma get_dest_tunnel f pc :
  ∃ n,
    nop_sequence (fn_code f) n pc
    (get_dest
     (tunnel (fn_code f) (fn_entrypoint f) 1%positive
             (PTree.empty node) (lt_wf _ _)) pc).
Proof.
  unfold get_dest.
  generalize (tunnel_correct (fn_code f) (fn_entrypoint f) xH (PTree.empty _) (lt_wf _ _) (empty_tunnel_correct _) pc).
  destruct (_ ! pc).
  - intros H. destruct (H _ eq_refl) as (idx & NOPS). eauto.
  - exists O. reflexivity.
Qed.

Definition transf_fundef (fd: fundef) : fundef :=
  match fd with
  | Internal fn => Internal (transf_function fn)
  | External ef => fd
  end.

Definition transf_program : program → program :=
  transform_program transf_fundef.

Definition match_stackframe (sf sf': stackframe) : Prop :=
  let 'Stackframe dst f sp pc rs := sf in
  let 'Stackframe dst' f' sp' pc' rs' := sf' in
  dst' = dst ∧ f' = transf_function f ∧ sp' = sp ∧ rs' = rs ∧
  ∃ idx, nop_sequence (fn_code f) idx pc pc'.

Definition match_stack := list_forall2 match_stackframe.

Definition match_state (idx: nat) (s s': state) : Prop :=
  match s with
  | State stk f sp pc rs m =>
    ∃ pc' stk',
    nop_sequence (fn_code f) idx pc pc' ∧
    match_stack stk stk' ∧
    s' = State stk' (transf_function f) sp pc' rs m
  | Callstate stk fd args m =>
    ∃ stk',
    match_stack stk stk' ∧
    s' = Callstate stk' (transf_fundef fd) args m
  | Returnstate stk v m =>
    idx = O ∧
    ∃ stk',
    match_stack stk stk' ∧
    s' = Returnstate stk' v m
  end.

Lemma find_function_preserved p ros rs fd :
  find_function (Genv.globalenv p) ros rs = Some fd →
  find_function (Genv.globalenv (transf_program p)) ros rs = Some (transf_fundef fd).
Proof.
  destruct ros as [ r | s ].
  - simpl. eauto using Genv.find_funct_transf.
  - simpl. unfold transf_program. rewrite (Genv.find_symbol_transf).
    case Genv.find_symbol. 2: discriminate.
    eauto using Genv.find_funct_ptr_transf.
Qed.

Lemma funsig_preserved fd :
  funsig (transf_fundef fd) = funsig fd.
Proof. destruct fd as [ () | ]; auto. Qed.

Lemma stack_size_preserved f :
  fn_stacksize (transf_function f) = fn_stacksize f.
Proof. destruct f. reflexivity. Qed.

Lemma entry_point_transf_function f :
  fn_entrypoint (transf_function f) =
  get_dest (tunnel (fn_code f) (fn_entrypoint f) xH (PTree.empty _) (lt_wf _ _))
           (fn_entrypoint f).
Proof. destruct f; reflexivity. Qed.

Inductive tag {A: Type} : A → Prop := Tag a : tag a.

Theorem simulation p :
  forward_simulation (semantics p) (semantics (transf_program p)).
Proof.
  refine
    (Forward_simulation
       (semantics p) (semantics (transf_program p))
       Wf_nat.lt_wf
       match_state
       _ _ _ _
    )
  .

  - simpl. intros s ().
    unfold transf_program. simpl.
    intros b f m0 H H0 H1 H2.
    exists O, (Callstate nil (transf_fundef f) nil m0).
    split. econstructor.
    eauto using Genv.init_mem_transf.
    erewrite Genv.find_symbol_transf; eauto.
    erewrite Genv.find_funct_ptr_transf; eauto.
    rewrite funsig_preserved; eauto.
    unfold match_stack. eauto using list_forall2_nil.

  - simpl. intros idx s1 s2 r M F.
    revert M. case F. clear. simpl.
    intros r m (-> & stk' & H & ->). inv H. constructor.

  - simpl.
    Hint Unfold match_stack.
    Hint Unfold match_stackframe.
    Hint Resolve funsig_preserved.
    intros s1 tr s1' STEP idx s2 M.
    destruct s1 as [ stk f sp pc rs m | stk fd args m | stk r m ];
    simpl in M.
    + destruct M as (pc' & stk' & NOPS & STK & ->).
      destruct idx as [ | idx ].
      * simpl in NOPS. subst pc'.
        inv STEP;
          repeat
          match goal with
          | H : Op.eval_operation _ _ _ _ _ = _ |- _ =>
            rewrite <- (Op.eval_operation_preserved _ _ (Genv.find_symbol_transf transf_fundef p)) in H
          | H : Op.eval_addressing _ _ _ _ = _ |- _ =>
            rewrite <- (Op.eval_addressing_preserved _ _ (Genv.find_symbol_transf transf_fundef p)) in H
          | H : find_function _ _ _  = _ |- _ =>
            apply (find_function_preserved p) in H
          | H : Events.eval_builtin_args _ _ _ _ _ _ |- _ =>
            apply (Events.eval_builtin_args_preserved _ (Genv.find_symbol_transf transf_fundef p))
                  in H
          | H : Events.external_call _ _ _ _ _ _ _ |- _ =>
            generalize (Events.external_call_symbols_preserved _ _ _ _ _ _ _ _
                                                               H
                                                               (Genv.find_symbol_transf transf_fundef p)
                                                               (Genv.public_symbol_transf _ _)
                                                               (Genv.find_var_info_transf _ _)
                       );
              clear H; intros H
          | H : appcontext[ fn_stacksize _ ] |- _ =>
            rewrite <- (stack_size_preserved f) in H
          | H : (fn_code f) ! _ = Some _ |- _ =>
            apply transf_function_at in H; simpl in H
          | H : appcontext[ get_dest ?m ?pc ], K: tag ?pc |- _ => idtac
          | H : appcontext[ get_dest ?m ?pc ] |- _ =>
            pose proof (Tag pc);
              let nop := fresh nop in
              let Hnop := fresh Hnop in
            destruct (get_dest_tunnel f pc) as (nop & Hnop)
          end;
          try (
              eexists nop, _; split;
              [ left; apply plus_one; econstructor (eauto; fail)
              | simpl; eauto;
                try (eexists (Stackframe _ _ _ _ _ :: _); eauto 14 using list_forall2_cons)
              ];
              fail
            ).
        eexists O, _. split. left. apply plus_one. econstructor (eauto; fail).
        simpl. eauto.
        destruct (get_dest_tunnel f ifnot) as (nop' & Hnop').
        eexists (if b then nop else nop'), _. split.
        left. apply plus_one. econstructor (eauto; fail).
        simpl. destruct b; eauto.
        destruct (get_dest_tunnel f pc') as (nop & Hnop).
        eexists nop, _. split. left. apply plus_one.
        eapply exec_Ijumptable; eauto.
        rewrite list_nth_z_map, H9. reflexivity.
        simpl. eauto.
        eexists _, _. split. left. apply plus_one. econstructor (eauto; fail).
        simpl. eauto.
      * destruct NOPS as (n & Hn & NOPS).
        inv STEP;
          repeat match goal with
                 | H : ?a = ?b |- _ => subst a || subst b
                 | H : ?a = Some _, K : ?a = Some _ |- _ =>
                   rewrite H in K; inversion K; clear K
                 end.
        eexists idx, _.
        split. right. split. apply star_refl.
        Psatz.lia. simpl. eauto.
    + destruct M as (stk' & STK & ->).
      inv STEP.
      * destruct (get_dest_tunnel f (fn_entrypoint f)) as (nop & Hnop).
        eexists nop, _. split.
        left. apply plus_one.
        rewrite <- (stack_size_preserved f) in *.
        econstructor (eauto; fail).
        eexists _, _. split. eauto.
        split. eauto. rewrite entry_point_transf_function.
        f_equal. destruct f; reflexivity.
      * eexists O, _. split.
        left. apply plus_one.
        generalize (Events.external_call_symbols_preserved _ _ _ _ _ _ _ _
                                                           H5
                                                           (Genv.find_symbol_transf transf_fundef p)
                                                           (Genv.public_symbol_transf _ _)
                                                           (Genv.find_var_info_transf _ _)
                   ); clear H5; intros H5.
        econstructor (eauto; fail).
        simpl. eauto.
    + destruct M as (-> & stk' & STK & ->).
      inv STEP.
      destruct stk' as [ | () stk' ]; inv STK.
      destruct H2 as ( -> & -> & -> & -> & nop & Hnop).
      eexists nop, _. split.
      left. apply plus_one. constructor.
      simpl; eauto.
  - simpl. apply Genv.public_symbol_transf.
Qed.
