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
Require Import AST.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Smallstep.
Require Import Globalenvs.
Require Import CminorSel.
Require Import LoopUnroll.

Local Open Scope error_monad_scope.

(** * iterated sequence facts *)

Lemma iterseq_neq: forall s1 s2 s3 n,
 iterseq n s1 s2 = s3 -> ~s2=s3 -> (forall sa sb, ~Sseq sa sb=s3) -> False.
Proof.
induction n; intros; auto.
eapply H1.
simpl in H; apply H.
Qed.

(****
Lemma iterseq_seq: forall n s1 s2 sa sb,
 iterseq n s1 (Sloop s2) = Sseq sa sb ->
 exists n', n=S n' /\ sa = s1 /\ sb = iterseq n' s1 (Sloop s2).
Proof.
induction n.
 simpl; intros. inv H.
simpl; intros. inv H.
exists n.
split; auto.
Qed.
*)

Inductive suffix: stmt -> stmt -> Prop :=
| suffix0 : forall s, suffix s s
| suffixS : forall s1 s2 s3, suffix s1 s2 ->
                             suffix (Sseq s3 s1) s2.

Lemma suffix_trans: forall s1 s2 s3,
 suffix s1 s2 -> suffix s2 s3 -> suffix s1 s3.
intros s1 s2 s3 H; elim H; clear H; auto. 
intros; auto.
constructor 2; auto.
Qed.

Lemma suffix_seq: forall s1 s2 s3,
 suffix s1 (Sseq s2 s3) -> suffix s1 s3.
Proof.
intros s1 s2 s3.
generalize (eq_refl (Sseq s2 s3)).
generalize (Sseq s2 s3) at 1 3; intros.
generalize s2 s3 H; clear s2 s3 H. elim H0; clear H0; auto.
 intros; subst; constructor; constructor.
intros; constructor. eapply H0; eauto.
Qed.

(*
Lemma suffix_iterseq: forall n s1 s2 s3,
 suffix s1 (iterseq n s2 s3) -> suffix s1 s3.
Proof.
induction n; auto.
simpl; intros.
eapply IHn; eapply suffix_seq; eauto.
Qed.
*)

Lemma iterseq_loop_suffix: forall n s1 s2 s3,
 suffix (iterseq n s1 (Sloop s2)) s3 ->
  exists n', iterseq n' s1 (Sloop s2) = s3.
Proof.
induction n.
 simpl.
 intros.
 inv H. exists O; auto.
simpl; intros. inv H.
 exists (S n); auto.
exploit IHn; auto.
apply H3.
Qed.

Lemma iterseq_suffix: forall n s1 s2,
 suffix (iterseq n s1 s2) s2.
Proof.
induction n; simpl; intros.
 constructor.
constructor; apply IHn.
Qed.

(*
Lemma iterseq_suffix_seq: forall n s1 s2 s3 s4,
 suffix (iterseq n s1 (Sloop s2)) (Sseq s3 s4) -> s1=s3.
Proof.
induction n; simpl; intros. inv H.
inv H; auto.
eapply IHn; eauto.
Qed.

Lemma suffix_tail: forall s1 s2 sl,
 suffix s1 s2 -> suffix s1 (Sloop sl) -> suffix s2 (Sloop sl).
Proof.
induction 1; auto.
intros H1; inv H1.
apply IHsuffix; auto.
Qed.
*)

(** loop-unroll facts *)

Definition unroll_flag n := andb (NPeano.Nat.eqb n O).

Lemma unroll_flag_0: forall b, unroll_flag O b = b.
Proof. unfold unroll_flag; rewrite NPeano.Nat.eqb_refl; auto. Qed.

Lemma unroll_flag_S: forall n b, unroll_flag (S n) b = false.
Proof. auto. Qed.

Lemma unroll_flag_false: forall n, unroll_flag n false = false.
Proof. unfold unroll_flag; intros; rewrite andb_comm; auto. Qed.

(*
Lemma unroll_flag_true: forall n, unroll_flag n true = NPeano.Nat.eqb n O.
Proof. unfold unroll_flag; intros; rewrite andb_comm; auto. Qed.
*)

Inductive unroll: stmt -> stmt -> Prop :=
 | unroll_0: forall b guess l s s',
     unroll_stmt b guess s l = OK s' ->
     unroll s s'
 | unroll_S: forall guess l s s' s'',
     unroll_stmt false guess s (xO l) = OK s' ->
     suffix (iterseq (guess l) s' (Sloop s')) s'' ->
     unroll (Sloop s) s''.

Lemma unrollE: forall b s s' guess x,
  unroll_stmt b guess s x = OK s' -> unroll s s'.
Proof. induction s; intros; econstructor 1; eauto. Qed.

Lemma loop_unroll_inv: forall s s',
 unroll (Sloop s) s' ->
 exists sl, unroll s sl /\
   (s'=Sloop sl \/ exists n, s'=iterseq n sl (Sloop sl)).
Proof.
intros; inv H.
 monadInv H0; destruct (guess l); apply unrollE in EQ;
 exists x; split; auto.
 right; exists (S n); auto.
apply unrollE in H1.
exists s'0; split; auto.
apply iterseq_loop_suffix in H2; destruct H2 as [n Hn].
right; exists n; symmetry; auto.
Qed.

Tactic Notation "iterseq_discriminate" hyp(H) :=
 eelim iterseq_neq; [apply H|discriminate|discriminate].

(*
Lemma unroll_skip: forall s,
 unroll s Sskip -> s=Sskip.
Proof.
destruct s; simpl; intros; inv H; try reflexivity;
try solve[monadInv H0].
 monadInv H0.
 iterseq_discriminate H0.
apply iterseq_loop_suffix in H2; inv H2.
iterseq_discriminate H.
Qed.

Lemma unroll_assign: forall s i e ,
 unroll s (Sassign i e) -> s=Sassign i e.
Proof.
destruct s; simpl; intros; inv H; try reflexivity;
try solve[monadInv H0].
  monadInv H0; auto.
 monadInv H0.
 iterseq_discriminate H0.
apply iterseq_loop_suffix in H2; inv H2.
iterseq_discriminate H.
Qed.

Lemma unroll_if: forall c s s1' s2',
 unroll s (Sifthenelse c s1' s2') ->
 exists s1 s2,
   s= Sifthenelse c s1 s2 /\ unroll s1 s1' /\ unroll s2 s2'.
Proof.
destruct s; intros; inv H; try reflexivity; try monadInv H0.
  exists s1; exists s2; split; [|split]; auto; eapply unrollE; eauto.
 destruct (guess l); inv H0.
apply iterseq_loop_suffix in H2; inv H2.
iterseq_discriminate H.
Qed.

Lemma unroll_seq_inv: forall s s1' s2',
 unroll s (Sseq s1' s2') ->
 (exists s1 s2, s=Sseq s1 s2 /\ unroll s1 s1' /\ unroll s2 s2')
 \/ (exists sl,
       s=Sloop sl /\ unroll sl s1' /\
       exists n, s2'=iterseq n s1' (Sloop s1')).
Proof.
destruct s; simpl; intros; inv H; try reflexivity; try monadInv H0.
  left; exists s1; exists s2; split; [|split]; auto; eapply unrollE; eauto.
 right; exists s; split; [|split]; auto.
  destruct (guess l); simpl in H0; inv H0.
  eapply unrollE; apply EQ.
 destruct (guess l); inv H0.
 exists n; auto.
right; exists s; split; [|split]; auto.
 apply iterseq_loop_suffix in H2; inv H2.
 destruct x; inv H.
 eapply unrollE; apply H1.
apply iterseq_loop_suffix in H2; inv H2.
destruct x; inv H.
exists x; auto.
Qed.

Lemma unroll_loop: forall s s1',
 unroll s (Sloop s1') ->
 exists s1,
   s= Sloop s1 /\ unroll s1 s1'.
Proof.
destruct s; intros; inv H; try reflexivity; try monadInv H0.
 destruct (guess l); inv H0.
 exists s; split; auto; eapply unrollE; eauto.
destruct (guess l); inv H2.
 exists s; split; auto; eapply unrollE; eauto.
assert (suffix (iterseq n s' (Sloop s')) (Sloop s')).
 apply iterseq_suffix.
apply (suffix_tail _ _ _ H) in H4.
inv H4.
exists s; split; auto; eapply unrollE; apply H1.
Qed.

Lemma unroll_block: forall s s1',
 unroll s (Sblock s1') ->
 exists s1,
   s= Sblock s1 /\ unroll s1 s1'.
Proof.
destruct s; intros; inv H; try reflexivity; try monadInv H0.
  destruct (guess l); inv H0.
 apply iterseq_loop_suffix in H2; inv H2.
 iterseq_discriminate H.
exists s; split; auto; eapply unrollE; eauto.
Qed.

Lemma unroll_label: forall s lbl s1',
 unroll s (Slabel lbl s1') ->
 exists s1, s=Slabel lbl s1 /\ unroll s1 s1'
  /\ (forall guess l s'', unroll_stmt false guess s l = OK s'' -> False).
Proof.
destruct s; simpl; intros; inv H; try reflexivity;
try solve[monadInv H0].
  monadInv H0.
  iterseq_discriminate H0.
 apply iterseq_loop_suffix in H2; inv H2.
 iterseq_discriminate H.
monadInv H0.
exists s; split; [|split]; auto; try (eapply unrollE; eauto).
intros; destruct (unroll_stmt false guess0 s l); simpl in H; inv H.
Qed.
*)

Lemma unroll_suffix: forall s s1 s2, 
  suffix s1 s2 ->
  unroll (Sloop s) s1 ->
  unroll (Sloop s) s2.
Proof.
intros; inv H.
 inv H0.
  econstructor 1; apply H.
 econstructor 2; eauto.
inv H0.
 generalize H; intro H'; monadInv H.
 case_eq (guess l); [intros Hn'|intros n' Hn'].
  rewrite Hn' in H0; inv H0.
 rewrite Hn', unroll_flag_S in EQ.
 rewrite Hn' in H0; inv H0.
 econstructor 2; [apply EQ|].
 rewrite Hn'; simpl.
 apply suffix_trans with (iterseq n' s4 (Sloop s4)); auto.
 constructor; constructor.
apply suffix_seq in H3.
apply (suffix_trans _ _ _ H3) in H1.
econstructor 2; eauto.
Qed.

Lemma unroll_seq: forall s s1 s2,
  unroll (Sloop s) (Sseq s1 s2) ->
  unroll (Sloop s) s2.
Proof.
intros.
apply unroll_suffix with (Sseq s1 s2); auto.
constructor; constructor.
Qed.

(*
Lemma unroll_iterseq: forall n s s1 s2,
  unroll (Sloop s) (iterseq n s1 s2) ->
  unroll (Sloop s) s2.
(*  /\ unroll_stmt guess s (xO l) = OK s1.*)
Proof.
intros; apply unroll_suffix with (iterseq n s1 s2); auto.
apply iterseq_suffix.
Qed.
*)

Section PRESERVATION.

Variable prog: program.
Variable tprog: program.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis TRANSFPROG: transform_partial_program
                         (unroll_fundef ge) prog = OK tprog.

Lemma symbols_preserved:
  forall (s: ident), Genv.find_symbol tge s = Genv.find_symbol ge s.
Proof. intros; eapply Genv.find_symbol_transf_partial; eauto. Qed.

Lemma symbol_address_preserved:
  forall (s: ident) o, Genv.symbol_address tge s o = Genv.symbol_address ge s o.
Proof.
unfold Genv.symbol_address; intros.
rewrite symbols_preserved; auto.
Qed.

Lemma public_symbols_preserved:
  forall (s: ident), Genv.public_symbol tge s = Genv.public_symbol ge s.
Proof. intros; eapply Genv.public_symbol_transf_partial; eauto. Qed.

Lemma function_ptr_translated:
  forall (b: block) (f: fundef),
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf
             /\ unroll_fundef ge f = OK tf.
Proof. intros; eapply Genv.find_funct_ptr_transf_partial; eauto. Qed.

Lemma functions_translated:
  forall (v v': val) (f: fundef),
  Genv.find_funct ge v = Some f ->
  Val.lessdef v v' ->
  exists tf, Genv.find_funct tge v' = Some tf /\ unroll_fundef ge f = OK tf.
Proof.  
intros. inv H0.
eapply Genv.find_funct_transf_partial; eauto.
simpl in H. discriminate.
Qed.

Lemma sig_function_translated:
  forall f tf, unroll_fundef ge f = OK tf -> funsig tf = funsig f.
Proof.
intros; destruct f; monadInv H; auto.
monadInv EQ; auto. 
Qed.

Lemma stackspace_function_translated:
  forall f tf, unroll_function ge f = OK tf -> fn_stackspace tf = fn_stackspace f.
Proof. intros. monadInv H; auto. Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof. intros; eapply Genv.find_var_info_transf_partial; eauto. Qed.

Inductive match_cont: cont -> cont -> Prop :=
  | match_cont_stop:
      match_cont Kstop Kstop
  | match_cont_seq: forall s s' k k',
      unroll s s' ->
      match_cont k k' ->
      match_cont (Kseq s k) (Kseq s' k')
  | match_cont_block: forall k k',
      match_cont k k' ->
      match_cont (Kblock k) (Kblock k')
  | match_cont_call: forall id f sp e k f' k',
      unroll_function ge f = OK f' ->
      match_cont k k' ->
      match_cont (Kcall id f sp e k) (Kcall id f' sp e k').

Inductive match_states: CminorSel.state -> CminorSel.state -> Prop :=
  | match_state: forall f f' s k s' k' sp e m
        (TF: unroll_function ge f = OK f')
        (TS: unroll s s')
        (MC: match_cont k k'),
      match_states
        (State f s k sp e m)
        (State f' s' k' sp e m)
  | match_callstate: forall f f' args k k' m
        (TF: unroll_fundef ge f = OK f')
        (MC: match_cont k k'),
      match_states
        (Callstate f args k m)
        (Callstate f' args k' m)
  | match_returnstate: forall v  k k' m
        (MC: match_cont k k'),
      match_states
        (Returnstate v k m)
        (Returnstate v k' m).

Remark call_cont_commut:
  forall k k', match_cont k k' -> match_cont (call_cont k) (call_cont k').
Proof.
induction 1; simpl; auto. constructor. 
constructor; auto.
Qed.

Lemma find_label_unroll: forall guess lbl s s' k l,
 unroll_stmt false guess s l = OK s' ->
 find_label lbl s k = None.
Proof.
induction s; intros; simpl; auto.
(* seq *)
monadInv H; erewrite IHs1; eauto.
(* if *)
monadInv H; erewrite IHs1; eauto.
(* loop *)
monadInv H.
rewrite unroll_flag_false in EQ.
erewrite IHs; eauto.
(* block *)
monadInv H; erewrite IHs; eauto.
(* label *)
simpl in H; inv H.
Qed.

Lemma find_label_loop: forall lbl s k',
 (forall k, find_label lbl s k = None) -> find_label lbl (Sloop s) k' = None.
Proof. intros; simpl; rewrite H; auto. Qed.

(*
Lemma find_label_seq: forall lbl s1 s2 k',
 (forall k, find_label lbl s1 k = None) ->
 (forall k, find_label lbl s2 k = None) ->
 find_label lbl (Sseq s1 s2) k' = None.
Proof. intros; simpl; rewrite H, H0; auto. Qed.
*)

Lemma find_label_iterseq: forall lbl s1 s2 n k',
 (forall k, find_label lbl s1 k = None) ->
 (forall k, find_label lbl s2 k = None) ->
 find_label lbl (iterseq n s1 s2) k' = None.
Proof. induction n; intros; simpl; auto; rewrite H, IHn; auto. Qed.

Lemma find_label_suffix: forall lbl s1 s2,
 suffix s1 s2 ->
 (forall k, find_label lbl s1 k = None) ->
 (forall k, find_label lbl s2 k = None).
Proof. 
induction 1; intros; simpl; auto.
apply IHsuffix; intros.
specialize (H0 k0); simpl in H0.
destruct (find_label lbl s3 (Kseq s1 k0)); inv H0; auto.
Qed.

Lemma unroll_find_label: forall lbl s s' k k',
 unroll s s' ->
 find_label lbl s k = None -> find_label lbl s' k' = None.
Proof.
induction s; intros; inv H; try monadInv H1; simpl; auto.
- (* seq *)
simpl in H0.
apply unrollE in EQ.
apply unrollE in EQ1.
assert (find_label lbl s2 k = None
        /\ find_label lbl s1 (Kseq s2 k) = None) as [H1 H2].
 destruct (find_label lbl s1 (Kseq s2 k))
 ; destruct (find_label lbl s2 k); split; auto; inv H0.
rewrite IHs1 with _ (Kseq s2 k) _; auto.
erewrite IHs2; eauto.
- (* if *)
simpl in H0.
apply unrollE in EQ.
apply unrollE in EQ1.
assert (find_label lbl s1 k = None
        /\ find_label lbl s2 k = None) as [H1 H2].
 destruct (find_label lbl s1 k)
 ; destruct (find_label lbl s2 k); split; auto; inv H0.
rewrite IHs1 with _ k _; auto.
rewrite IHs2 with _ k _; auto.
- (* iterseq loop *)
case_eq (guess l); [intros Hn| intros n Hn].
 simpl in H0.
 simpl; apply IHs with (Kseq (Sloop s) k); auto.
 eapply unrollE; apply EQ.
rewrite Hn, unroll_flag_S in EQ.
assert (forall k, find_label lbl x k = None).
 intro kk; apply IHs with (Kseq (Sloop s) k).
 eapply unrollE; apply EQ.
 simpl in H0; destruct (find_label lbl s k); auto.
apply find_label_iterseq; auto.
intro kk; apply find_label_loop; auto.
- (* loop suffix *)
assert (forall k, find_label lbl s'0 k = None).
 intro kk; apply IHs with (Kseq (Sloop s) k).
 eapply unrollE; apply H2.
 simpl in H0; destruct (find_label lbl s k); auto.
eapply find_label_suffix.
 apply H3.
intros ?; apply find_label_iterseq; auto.
intros ?; apply find_label_loop; auto.
- (* block *)
simpl in H0.
apply unrollE in EQ.
rewrite IHs with _ (Kblock k) _; auto.
- (* label *)
simpl in H0.
destruct (ident_eq lbl l); inv H0.
destruct b; simpl in H1; [|inv H1].
monadInv H1.
rewrite H2.
apply unrollE in EQ.
simpl; destruct (ident_eq lbl l).
 elim n; auto.
apply IHs with k; auto.
Qed.

Remark find_label_commut:
  forall lbl s k s' k',
  match_cont k k' ->
  unroll s s' ->
  match find_label lbl s k, find_label lbl s' k' with
  | None, None => True
  | Some(s1, k1), Some(s1', k1') => 
    unroll s1 s1' /\ match_cont k1 k1'
  | _, _ => False
  end.
Proof.
induction s; intros until k'; simpl; intros MC SE;
 try (inv SE; inv H; simpl; auto).
- (* seq *)
monadInv H1.
exploit (IHs1 (Kseq s2 k)); eauto. 
  econstructor. 
   econstructor; eauto. 
  apply MC.
 econstructor; eauto. 
destruct (find_label lbl s1 (Kseq s2 k)) as [[sx kx] | ]; simpl;
destruct (find_label lbl x (Kseq x0 k')) as [[sy ky] | ];
intuition. 
apply IHs2; auto.
econstructor; eauto.
- (* if *)
monadInv H1.
exploit (IHs1 k); eauto.
 econstructor; eauto. 
destruct (find_label lbl s1 k) as [[sx kx] | ]; simpl;
destruct (find_label lbl x k') as [[sy ky] | ];
intuition. 
apply IHs2; auto.
econstructor; eauto.
- (* loop *)
inv SE.
 monadInv H.
 case_eq (guess l); [intros Hn|intros n Hn].
  rewrite Hn, unroll_flag_0 in EQ; simpl. 
  apply IHs.
   econstructor; auto. 
   constructor 1 with b guess l; simpl.
   rewrite Hn, unroll_flag_0, EQ; simpl; f_equal.
  eapply unrollE; eauto.
 rewrite Hn, unroll_flag_S in EQ.
 assert (find_label lbl (iterseq (S n) x (Sloop x)) k' =
         find_label lbl (Sloop x) k').
  assert (forall k', find_label lbl (Sloop x) k' = None).
   intro kk'; apply find_label_loop; intro kk.
   apply unroll_find_label with s kk'.
    eapply unrollE; apply EQ.
   eapply find_label_unroll; apply EQ.
  rewrite H.
  apply find_label_iterseq; intro kk.
   apply unroll_find_label with s k.
    eapply unrollE; apply EQ.
   eapply find_label_unroll; apply EQ.
  apply H.
 rewrite H; simpl; apply IHs.
  constructor; auto.
  constructor 2 with guess l x; simpl.
   rewrite EQ; f_equal.
  apply iterseq_suffix.
 eapply unrollE; eauto.
assert (find_label lbl s (Kseq (Sloop s) k) = find_label lbl s k).
 erewrite find_label_unroll; eauto.
 erewrite find_label_unroll; eauto.
rewrite H; clear H.
assert (find_label lbl s' k' = find_label lbl s'0 k').
 assert (forall k, find_label lbl s'0 k = None).
  intro kk; apply unroll_find_label with s kk.
   eapply unrollE; eauto.
  eapply find_label_unroll; apply H0.
 rewrite H.
 apply find_label_suffix with (iterseq (guess l) s'0 (Sloop s'0)); auto.
 intros ?; apply find_label_iterseq; auto.
 intros ?; apply find_label_loop; auto.
simpl; rewrite H; apply IHs; auto.
eapply unrollE; eauto.
- (* block *)
monadInv H1.
exploit (IHs k); eauto.
 econstructor; eauto. 
destruct (find_label lbl s k) as [[sx kx] | ]; simpl;
destruct (find_label lbl x k') as [[sy ky] | ];
intuition. 
 apply IHs; auto.
 econstructor; eauto.
 eapply unrollE; eauto.
apply IHs; auto.
econstructor; eauto.
eapply unrollE; eauto.
- (* label *)
destruct b; monadInv H1; simpl.
destruct (ident_eq lbl l). 
 split; [eapply unrollE; eauto|assumption].
apply IHs; auto.
eapply unrollE; eauto.
Qed.

Combined Scheme eval_expr_ind3plus
 from eval_expr_ind3, eval_exprlist_ind3, eval_condexpr_ind3.

Lemma unroll_expr3_correct:
  forall sp env m,
  (forall a e v, eval_expr ge sp env m a e v  ->
                 eval_expr tge sp env m a e v)
  /\
  (forall a e v, eval_exprlist ge sp env m a e v ->
                 eval_exprlist tge sp env m a e v)
  /\
  forall a e v,  eval_condexpr ge sp env m a e v ->
                 eval_condexpr tge sp env m a e v.
Proof.
generalize symbols_preserved; intros SP.
generalize public_symbols_preserved; intros PSP.
generalize varinfo_preserved; intros VP.
intros sp env m; apply eval_expr_ind3plus; intros; econstructor; eauto.
erewrite Op.eval_operation_preserved; eauto.
try solve [erewrite Op.eval_addressing_preserved; eauto].
eapply external_call_symbols_preserved; eauto.
erewrite SP; eauto.
apply function_ptr_translated in H0; destruct H0 as [tf H0].
destruct H0 as [H0 H0']; inv H0'; auto.
eapply external_call_symbols_preserved; eauto.
Qed.

Lemma unroll_expr_correct:
  forall sp env m a e v, eval_expr ge sp env m a e v  ->
                         eval_expr tge sp env m a e v.
Proof.
intros. exploit unroll_expr3_correct; intros [H1 _].
apply H1; auto.
Qed.

Lemma unroll_exprlist_correct:
  forall sp env m a e v, eval_exprlist ge sp env m a e v  ->
                         eval_exprlist tge sp env m a e v.
Proof.
intros. exploit unroll_expr3_correct; intros [_ [H1 _]].
apply H1; auto.
Qed.

Lemma unroll_builtin_arg_correct:
  forall sp env m e v, eval_builtin_arg ge sp env m e v  ->
                       eval_builtin_arg tge sp env m e v.
Proof.
intros.
inv H; try constructor; auto.
- exploit unroll_expr3_correct; intros [H1 _].
  apply H1 in H0; auto.
- rewrite symbol_address_preserved; auto.
- rewrite <- symbol_address_preserved; constructor; auto.
- apply unroll_expr_correct; auto.
- apply unroll_expr_correct; auto.
Qed.

Lemma unroll_builtin_args_correct:
  forall sp m al e vl,
     list_forall2 (eval_builtin_arg ge sp e m) al vl ->
     list_forall2 (eval_builtin_arg tge sp e m) al vl.
Proof.
induction al; intros; inv H; [constructor|].
constructor.
 apply unroll_builtin_arg_correct; auto.
apply IHal; auto.
Qed.

Lemma unroll_condexpr_correct:
  forall sp env m a e v, eval_condexpr ge sp env m a e v  ->
                         eval_condexpr tge sp env m a e v.
Proof.
intros. exploit unroll_expr3_correct; intros [_ [_ H1]].
apply H1; auto.
Qed.

Lemma unroll_expr_or_symbol_correct:
  forall sp env m a e v,
  eval_expr_or_symbol ge sp env m a e v ->
  eval_expr_or_symbol tge sp env m a e v.
Proof.
intros; destruct e.
 inv H; constructor; apply unroll_expr_correct; auto.
inv H; constructor; rewrite symbols_preserved; auto.
Qed.

Lemma unroll_exitexpr_correct:
  forall sp env m a e v,
  eval_exitexpr ge sp env m a e v ->
  eval_exitexpr tge sp env m a e v.
Proof.
intros sp env m.
apply eval_exitexpr_ind; intros;
econstructor; auto.
- apply unroll_expr_correct; apply H.
- auto.
- apply unroll_condexpr_correct; apply H; auto.
- auto.
- apply unroll_expr_correct; apply H.
- auto.
Qed.

Lemma unroll_step_correct:
  forall S1 t S2, CminorSel.step ge S1 t S2 ->
  forall T1, match_states S1 T1 ->
  (exists T2, CminorSel.step tge T1 t T2 /\ match_states S2 T2).
Proof.
induction 1; intros T1 ME; inv ME; try monadInv TS;
try solve [inv MC; econstructor; split; constructor; auto].
- (* skip seq *)
  inv TS. inv H. inv MC; econstructor; split.
   constructor; eauto.
  constructor; auto.
- (* skip block *)
  inv TS; inv H. inv MC; econstructor; split; [constructor; auto|].
  constructor; auto.
  constructor 1 with b guess l; auto.
- (* skip call *)
  inv TS. inv H1.
  econstructor; split. 
   constructor. 
    inv MC; auto. 
   erewrite stackspace_function_translated; eauto.
  econstructor; eauto.
- (* assign *)
  inv TS. inv H0.
  econstructor; split.
   constructor; (apply unroll_expr_correct; eauto) || auto.
  constructor; auto.
  constructor 1 with b guess l; auto.
- (* store *)
  inv TS. inv H3.
  econstructor; split. 
   econstructor; (apply unroll_expr_correct; eauto) || 
   (apply unroll_exprlist_correct; eauto) || eauto.
  try solve
   [erewrite Op.eval_addressing_preserved; eauto; apply symbols_preserved].
  constructor; auto.
  constructor 1 with b0 guess l; auto.
- (* Scall *)
  inv TS. inv H2.
  exploit unroll_exprlist_correct; eauto. intros C.
  exploit functions_translated; eauto. intros (fd' & X & Y).
  econstructor; split.
   rewrite <- sig_function_translated with fd fd'; auto.
   econstructor; eauto.
   apply unroll_expr_or_symbol_correct; apply H; eauto.
  econstructor; eauto.
  constructor; eauto.
- (* Stailcall *)
  inv TS. inv H2.
  exploit unroll_exprlist_correct; eauto. intros C.
  exploit functions_translated; eauto. intros (fd' & X & Y).
  econstructor; split.
  rewrite <- sig_function_translated with fd fd'.
  econstructor; eauto.
  apply unroll_expr_or_symbol_correct; apply H.
  erewrite stackspace_function_translated; eauto.
  auto.
  econstructor; auto.
  apply call_cont_commut; eauto.
- (* Sbuiltin *)
  inv TS. inv H1.
  exploit unroll_builtin_args_correct; eauto. intros C.
  econstructor; split.
  econstructor; eauto. 
   eapply external_call_symbols_preserved; eauto.
    exact symbols_preserved. exact public_symbols_preserved.
    exact varinfo_preserved.
   constructor; auto.
  constructor 1 with true guess l; auto.
- (* Seq *)
  inv TS. monadInv H.
  econstructor; split.
   constructor; auto.
  constructor; auto.
   constructor 1 with b guess (xO l); auto.
  econstructor; eauto. econstructor. apply EQ1.
- (* Sifthenelse *)
  inv TS. monadInv H0.
  eexists; split. 
   econstructor; eauto. 
   apply unroll_condexpr_correct; apply H.
  constructor; auto.
  constructor 1 with b0 guess (if b then (xO l) else (xI l)).
  destruct b; [apply EQ|apply EQ1].
- (* Sloop *)
  generalize (loop_unroll_inv _ _ TS). 
  intros [sl [Hsl [H1|[n Hn]]]]; subst.
   econstructor; split. 
    econstructor. 
   constructor; auto.
   constructor 2; auto.
  destruct n; simpl in *.
   econstructor; split. 
    econstructor. 
   constructor; auto.
   constructor 2; auto.
  simpl; econstructor; split.
   econstructor. 
  constructor; auto.
  constructor 2; auto.
  eapply unroll_seq; eauto.
- (* Sblock *)
  inv TS. monadInv H.
  econstructor; split. 
   constructor. 
  constructor; auto.
   constructor 1 with b guess l; auto.
  constructor; auto.
- (* Sexit n *)
  inv TS. inv H.
  inv MC; econstructor; split.
   econstructor; auto.
  constructor; auto.
  constructor 1 with b guess l; auto.
- (* Sexit 0 *)
  inv TS. inv H.
  inv MC; econstructor; split.
   econstructor; auto.
  constructor; auto.
  constructor 1 with b guess l; auto.
- (* Sexit (S n) *)
  inv TS. inv H.
  inv MC; econstructor; split.
   econstructor; auto.
  constructor; auto.
  constructor 1 with b guess l; auto.
- (* Switch *)
  inv TS. inv H0.
  econstructor; split.
   econstructor; auto.
  apply unroll_exitexpr_correct; apply H.
  constructor; auto.
  constructor 1 with b guess l; auto.
- (* Sreturn None *)
  inv TS. inv H0.
  econstructor; split. 
   constructor. 
   erewrite stackspace_function_translated; eauto.
  econstructor; eauto. 
  apply call_cont_commut; eauto.
- (* Sreturn Some *)
  inv TS. inv H1.
  eexists; split. 
   econstructor. 
    apply unroll_expr_correct; apply H.
   erewrite stackspace_function_translated; eauto.
  econstructor; auto. 
  apply call_cont_commut; eauto.
- (* Slabel *)
  inv TS. destruct b; monadInv H.
  econstructor; split.
   econstructor. 
  constructor; auto.
  constructor 1 with true guess l; auto.
- (* Sgoto *)
  inv TS. inv H0.
  generalize TF; intros TF'.
  monadInv TF'; simpl.
  exploit (find_label_commut lbl (fn_body f) (call_cont k)).
    apply call_cont_commut; eauto.
   econstructor; apply EQ.
  rewrite H. 
  destruct (find_label lbl x (call_cont k'0))
  as [[s'' k'']|] eqn:?; intros; try contradiction.
  destruct H0. 
  econstructor; split.
   econstructor.
  simpl; apply Heqo.
  eapply match_state; eauto.
- (* internal function *)
  monadInv TF. generalize EQ; intros TF; monadInv TF.
  econstructor; split.
   constructor; simpl; eauto.
  econstructor; simpl; auto. 
  econstructor 1; apply EQ0.
- (* external call *)
  monadInv TF.
  econstructor; split.
   econstructor. 
   eapply external_call_symbols_preserved; eauto.
   exact symbols_preserved. exact public_symbols_preserved.
   exact varinfo_preserved.
  econstructor; eauto.
- (* ret *)
  inv MC.
  generalize H5; intros; monadInv H5.
  econstructor; split.
   econstructor. 
  constructor; auto.
  constructor 1 with true (Compopts.optim_loop_unroll_estimates (fn_body f)) xH; auto.
Qed.

Lemma unroll_initial_states:
  forall S, CminorSel.initial_state prog S ->
  exists R, CminorSel.initial_state tprog R /\ match_states S R.
Proof.
  induction 1.
  exploit function_ptr_translated; eauto. intros (f' & A & B).
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  simpl. fold tge. rewrite symbols_preserved.
  erewrite transform_partial_program_main by eauto. eexact H0.
  eauto.
  rewrite <- H2. apply sig_function_translated; auto.
  constructor; auto. constructor. 
Qed.

Lemma unroll_final_states:
  forall S R r,
  match_states S R -> CminorSel.final_state S r -> CminorSel.final_state R r.
Proof.
  intros. inv H0. inv H. inv MC. constructor.
Qed.

End PRESERVATION.

Theorem transf_program_correct:
  forall prog tprog,
  unroll_program prog = OK tprog ->
  forward_simulation (CminorSel.semantics prog) (CminorSel.semantics tprog).
Proof.
  intros. unfold unroll_program in H. 
  eapply forward_simulation_step.
  eapply public_symbols_preserved; eauto.
  apply unroll_initial_states; auto.
  apply unroll_final_states; auto.
  simpl; intros. apply unroll_step_correct with (S1:=s1); auto.
Qed.
