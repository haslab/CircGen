
Require Import Utf8.
Require Import Maps Integers.
Require Import AST Memory Smallstep Globalenvs.

Require Import ZArith NArith Psatz.
Require Import Coqlib ExtraLib.

Require Import ORbdt OpGates CircIO HLCirc HLCircGen.
Require Import ssrlib ssrValues seqN bits.
Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Unset Elimination Schemes.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.



Lemma int_eq_true {i j: int} :
  Int.eq i j = true → i = j.
Proof.
  intros H.
  generalize (Int.eq_spec i j). rewrite H. exact id.
Qed.

Lemma decode_one_byte byt :
  decode_val Mint8unsigned (Byte byt :: nil)
  = Values.Vint (Int.repr (Byte.unsigned byt)).
Proof.
  set (veb x y := match x, y with Values.Vint a, Values.Vint b => Int.eq a b | _, _ => false end).
  assert (∀ x y, veb x y = true → x = y) as veb_eq.
  { destruct x, y; try discriminate. intros H; f_equal. apply (int_eq_true H). }
  apply veb_eq. revert byt.
  apply FOR_ALL_BYTE.for_all_byte_correct.
  vm_compute.
  reflexivity.
Qed.

Remark sizeN_nlen {A} (m: list A) :
  sizeN m = ValCirc.nlen m.
Proof.
  elim m; clear m. reflexivity.
  intros a m IH. simpl.
  rewrite ValCirc.nlen_cons. f_equal. exact IH.
Qed.

Definition Some_eq {A} (a a': A) (H: Some a = Some a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition None_eq_Some {A} (P: Prop) (a: A) (H: None = Some a) : P :=
  let 'Logic.eq_refl := H in I.

Definition inl_eq {A B} (a a': A) (H: inl B a = inl a') : a = a' :=
  let 'Logic.eq_refl := H in Logic.eq_refl.

Definition inr_inl (P: Prop) {A B} {a: A} {b: B} (H: inr b = inl a) : P :=
  let 'Logic.eq_refl := H in I.

Definition pair_eq {A B} (a a': A) (b b': B) (H: (a, b) = (a', b')) : a = a' ∧ b = b' :=
  let 'Logic.eq_refl := H in conj Logic.eq_refl Logic.eq_refl.

Lemma Forall2_nil_l {A B} (R: A → B → Prop) mb :
  Forall2 R nil mb → mb = nil.
Proof. inversion 1. reflexivity. Qed.

Lemma Forall2_nil_r {A B} (R: A → B → Prop) ma :
  Forall2 R ma nil → ma = nil.
Proof. inversion 1. reflexivity. Qed.

Lemma Forall2_cons_l {A B} (R: A → B → Prop) a ma mb :
  Forall2 R (a :: ma) mb → ∃ b mb', mb = b :: mb' ∧ R a b ∧ Forall2 R ma mb'.
Proof. inversion 1. eauto. Qed.

Lemma Forall2_cons_r {A B} (R: A → B → Prop) ma b mb :
  Forall2 R ma (b :: mb) → ∃ a ma', ma = a :: ma' ∧ R a b ∧ Forall2 R ma' mb.
Proof. inversion 1. eauto. Qed.

Ltac hsplit :=
  repeat match goal with
         | H : False |- _ => destruct H
         | H : unit |- _ => destruct H
         | H : ?a = ?b |- _ => subst a || subst b
         | H : _ ∧ _ |- _ => destruct H
         | H : ∃ a,  _ |- _ => let b := fresh a in destruct H as (b & H)
         | H :  (_, _) = (_, _) |- _ => apply pair_eq in H
         | H : Some _ = Some _ |- _ => apply Some_eq in H
         | H : Forall2 _ nil nil |- _ => clear H
         | H : Forall2 _ nil _ |- _ => apply Forall2_nil_l in H
         | H : Forall2 _ _ nil |- _ => apply Forall2_nil_r in H
         | H : Forall2 _ (_ :: _) _ |- _ => apply Forall2_cons_l in H
         | H : Forall2 _ _ (_ :: _) |- _ => apply Forall2_cons_r in H
         end.


Lemma merror_bind_inv {A B} (ma: merror A) (f: A → merror B) res :
  merror_bind ma f = inl res →
  ∃ a , ma = inl a ∧ f a = inl res.
Proof. unfold merror_bind. destruct ma. eauto. apply inr_inl. Qed.

Lemma mstate_bind_inv {A B} (ma: mstate A) (f: A → mstate B) st res :
  mstate_bind ma f st = inl res →
  ∃ a st', ma st = inl (a, st') ∧ f a st' = inl res.
Proof. unfold mstate_bind. destruct (ma _) as [ (?, ?) |]. eauto. apply inr_inl. Qed.

Lemma mstate_emap_inv {A} (ma: mstate A) (f: exn → exn) st res :
  mstate_emap f ma st = inl res →
  ma st = inl res.
Proof. unfold mstate_emap. destruct (ma _). exact id. apply inr_inl. Qed.

Lemma mstate_lift_merror_inv {A} (ma: merror A) st res st' :
  mstate_lift_merror ma st = inl (res, st') →
  ma = inl res ∧ st' = st.
Proof. destruct ma. intros H; apply inl_eq, pair_eq in H. intuition. f_equal. auto. apply inr_inl. Qed.

Ltac mstate_bind :=
  repeat
  match goal with
  | H : merror_bind2 _ _ = inl _ |- _ => unfold merror_bind2 in H
  | H : merror_bind _ _ = inl _ |- _ =>
    apply merror_bind_inv in H;
    destruct H as (? & ? & H)
  | H : merror_ret _ = inl _ |- _ => apply inl_eq in H
  | H : merror_err _ = inl _ |- _ => revert H; apply inr_inl
  | H : mstate_lift_merror _ _ = inl _ |- _ =>
    apply mstate_lift_merror_inv in H;
    destruct H
  | H : mstate_ret _ _ = inl _ |- _ => apply inl_eq in H
  | H : mstate_bind _ _ _ = inl _ |- _ =>
    apply mstate_bind_inv in H;
    let st := fresh "st" in
    destruct H as (? & st & ? & H)
  | H : mstate_bind2 _ _ _ = inl _ |- _ => unfold mstate_bind2 in H
  | H : mstate_emap _ _ _ = inl _ |- _ => apply mstate_emap_inv in H
  | H : mstate_getstate _ = inl _ |- _ => apply inl_eq in H
  end.

Section CONDV.

Context (condv: PTree.t N). (* Maps ValCirc wires to condition names *)

Section SPEC.

Context (localv: PTree.t localv_info). (* Maps ValCirc wires to types and HLCirc gates *)

(** There are three distinct kinds of entries in (HLCirc) grids.
 The type information in [is_localv] discriminate between these variants:
 - [None]: bit-strings representing (a snapshot of) a global variable
 - [Some None]: single-bit entries representing guards.
 - [Some (Some ty]]: bit-strings representing normal CompCert values (of a given type)
*)
Definition is_localv (w: ValCirc.wire) (ooty: option (option typ)) (n: gate_number)
  : Prop :=
  PTree.get (N.succ_pos w) localv = Some (ooty, n).

Lemma is_localv_inj w ty n ty' n' :
  is_localv w ty n →
  is_localv w ty' n' →
  ty' = ty ∧ n' = n.
Proof.
  unfold is_localv. intuition congruence.
Qed.

Definition bounded_localv (rk x: N) : Prop :=
  ∀ w ty n, is_localv w ty n → w < rk /\ n <= x.

Definition monot_localv :=
  ∀ w1 w2 ty1 ty2 n1 n2, w1 < w2 -> is_localv w1 ty1 n1 → is_localv w2 ty2 n2 → n1 < n2.

Lemma is_localv_invinj w1 w2 oty1 oty2 n:
 monot_localv ->
 is_localv w1 oty1 n ->
 is_localv w2 oty2 n ->
 w1 = w2.
Proof.
move => Hmon H1 H2.
move: (N.lt_trichotomy w1 w2) => [H|[H|H]] //.
 elim (N.lt_irrefl n).
 by eapply Hmon; eauto.
elim (N.lt_irrefl n).
by eapply Hmon; eauto.
Qed.

Definition localv_conn (w: ValCirc.wire) (c: connector) : Prop :=
  ∃ ty gw, is_localv w (Some (Some ty)) gw ∧ c = conn_ty ty gw.

Fixpoint localv_conn_list (ws: list ValCirc.wire) (c: connector) : Prop :=
  match ws with
  | nil => c = nil
  | w :: ws' => ∃ cL c', c = cL ++ c' ∧ localv_conn w cL ∧ localv_conn_list ws' c'
end.

Lemma localv_conn_list_is_localv args conn :
  localv_conn_list args conn →
  ∀ w, In w args →
  ∃ ty gn,
    is_localv w (Some (Some ty)) gn.
Proof.
  revert conn. elim args; clear.
  - intros ? ? ? ().
  - intros a args IH conn (cL & c' & -> & (oty & n & H & Hcl) & REC).
    intros w [ <- | IN ]; eauto.
Qed.


Section RENAMING.

Context {A: eqType}.

Fixpoint is_renamed cur (t t': bdd A) : Prop :=
  match t with
  | Leaf _ => t' = t
  | Node v ℓ r =>
    ∃ n v' ℓ' r',
    n < cur /\
    PTree.get v condv = Some n ∧
    is_localv n (Some None) (Npos v') ∧
    is_renamed cur ℓ ℓ' ∧
    is_renamed cur r r' ∧
    t' = Node v' ℓ' r'
  end.

Lemma is_renamed_inj n (φ: bdd A) φ1' φ2':
 is_renamed n φ φ1' ->
 is_renamed n φ φ2' ->
 φ1' = φ2'.
Proof.
elim: φ φ1' φ2'.
 by move=> x phi1' phi2' /= <- <-.
move=> v l IHl r IHr /= phi1' phi2'.
move=> [n1 [v1 [l1 [r1 [H11 [H12 [H13 [H14 [H15 ->]]]]]]]]].
move=> [n2 [v2 [l2 [r2 [H21 [H22 [H23 [H24 [H25 ->]]]]]]]]].
rewrite H22 in H12; inv H12.
move: (is_localv_inj H13 H23); move=> [_ [->]]; f_equal.
 by apply IHl.
by apply IHr.
Qed.

Lemma is_renamed_invinj cw n (φ1 φ2: bdd A) φ':
 wire_of_condition_wires cw = Some condv ->
 monot_localv ->
 is_renamed n φ1 φ' ->
 is_renamed n φ2 φ' ->
 φ1 = φ2.
Proof.
move=> Hcw Hmon; elim:  φ' φ1 φ2.
 move=> x [y1|v1 l1 r1] [y2|v2 l2 r2] //=.
 - by move => [->] [->].
 - by move => _ [? [? [? [? [_ [_ [_ [_ [_ H]]]]]]]]]; inv H.
 - by move => [? [? [? [? [_ [_ [_ [_ [_ H]]]]]]]]]; inv H.
 - by move => [? [? [? [? [_ [_ [_ [_ [_ H]]]]]]]]]; inv H.
move=> v l IHl r IHr /=.
move=> [y1|v1 l1 r1] [y2|v2 l2 r2] //=.
move=> [n1' [v1' [l1' [r1' [H11 [H12 [H13 [H14 [H15 H16]]]]]]]]]; inv H16.
move=> [n2' [v2' [l2' [r2' [H21 [H22 [H23 [H24 [H25 H26]]]]]]]]]; inv H26.
f_equal.
- move: (is_localv_invinj Hmon H13 H23) H12 H22 => -> H12 H22.
  by eapply condv_inj; eauto.
- by apply IHl.
- by apply IHr.
Qed.

End RENAMING.

Lemma is_renamed_cond_of_phi cw n φ φ' x:
 wire_of_condition_wires cw = Some condv ->
 monot_localv ->
 is_renamed n φ φ' ->
 is_renamed n (cond_of_phi x φ) (cond_of_phi x φ').
Proof.
move=> Hcw Hmon; elim: φ φ' => //=.
 move=> [x'|] ? -> //.
 by case: (ifP _) => //= ->.
move=> v l IHl r IHr; elim => //=.
 by move=> s [n' [v' [l' [r' [_ [_ [_ [_ [_ H]]]]]]]]]; inv H.
move=> v' l' _ r' _ //= [n2 [v2 [l2 [r2 [A2 [B2 [C2 [D2 [E2 [F2 [G2 H2]]]]]]]]]]]; subst.
have Tl: is_renamed n (cond_of_phi x l) (cond_of_phi x l2) by apply IHl.
have Tr: is_renamed n (cond_of_phi x r) (cond_of_phi x r2) by apply IHr.
rewrite /chkN.
case: (ifP _) => // /eqP.
 case: (ifP _) => // /eqP.
 move=> H2 H1; elim H2.
 by rewrite H1 in Tl; apply (is_renamed_inj Tl Tr).
case: (ifP _) => //= /eqP.
 move=> H2 H1; elim H1.
 by rewrite H2 in Tl; apply (is_renamed_invinj Hcw Hmon Tl Tr).
move=> _ _; eexists _,_,_,_; eauto 6.
Qed.


(** Specs *)


Definition add_gate_spec (g: gateID) (wargs: connector) (ge: gentry) : Prop :=
  gate_inputs g = sizeN wargs ∧
  ge = {| gate := g ; conn := wargs |}.

Definition add_gate_ty_spec (ty: typ) (g: gateID) (wargs: connector)
           (ge: gentry) : Prop :=
  gate_outputs g = wires_of_type ty ∧
  add_gate_spec g wargs ge.

Definition proc_op_spec (op: Op.operation) (args: list ValCirc.wire) (ge: gentry) : Prop :=
    ∃ g wargs,
      gate_of_operation op = Some g ∧
      localv_conn_list args wargs ∧
      add_gate_ty_spec (snd (Op.type_of_operation op)) g wargs ge.

Definition proc_addr_spec
           (addr: Op.addressing) (args: list ValCirc.wire)
           (rk: N) (body: list gentry) (o: ident * (int + gate_number)) : Prop :=
  match addr with
  | Op.Aglobal s off =>
    args = nil ∧ body = nil ∧ o = (Pos.succ s, inl off)
  | Op.Abased s off =>
    ∃ w ge,
    args = w :: nil ∧
    proc_op_spec (Op.Olea (Op.Aindexed off)) args ge ∧
    body = ge :: nil ∧
    o = (Pos.succ s, inr (rk + 1))
  | Op.Abasedscaled sc s off =>
    ∃ w ge,
    args = w :: nil ∧
    proc_op_spec (Op.Olea (Op.Ascaled sc off)) args ge ∧
    body = ge :: nil ∧
    o = (Pos.succ s, inr (rk + 1))
  | Op.Ainstack off =>
    args = nil ∧ body = nil ∧ o = (1%positive, inl off)
  | _ => False
  end.

Definition globv_upd_spec (gm: PTree.t globv_info)
           (v: ident) newc (gm': PTree.t globv_info) : Prop :=
  ∃ oc,
    PTree.get v gm = Some oc
    ∧ sizeN oc = sizeN newc
    ∧ gm' = PTree.set v newc gm.

Definition all_lt (pos: ValCirc.wire) m : Prop :=
  ∀ x, In x m → x < pos.

Inductive phi_spec pos rk ty : N -> seq (pcond*ident) -> seq gentry -> Prop :=
  phi_spec_single:
    forall guard v gw ge gg,
      Pos.pred_N v < pos ->
      is_localv (Pos.pred_N v) (Some (Some ty)) gw ∧
      add_gate_spec (Gguard guard) (conn_guard guard) gg ∧
      add_gate_ty_spec ty (GbarrierN (wires_of_type ty)) ((rk+1,0)::(conn_ty ty gw)) ge ->
      phi_spec pos rk ty 2 [:: (guard,v)] [:: ge; gg]
| phi_spec_cons:
    forall guard v l n gw ge gg gx code,
      Pos.pred_N v < pos ->
      phi_spec pos rk ty n l code ->
      is_localv (Pos.pred_N v) (Some (Some ty)) gw ∧
      add_gate_spec (Gguard guard) (conn_guard guard) gg ∧
      add_gate_ty_spec ty (GbarrierN (wires_of_type ty)) ((rk+n+1,0)::(conn_ty ty gw)) ge ->
      add_gate_ty_spec ty (GxorN (wires_of_type ty))
                       (conn_ty ty (rk+n) ++ conn_ty ty (rk+n+2)) gx ->
      phi_spec pos rk ty (3+n) [:: (guard,v) & l] ([:: gx; ge; gg] ++ code).

Scheme phi_spec_ind := Induction for phi_spec Sort Prop.    

Lemma phi_specP pos rk ty flat_phi n code:
 phi_spec pos rk ty n flat_phi code ->
 forall v, v\in map snd flat_phi ->
 Pos.pred_N v < pos /\ 
 exists gw, is_localv (Pos.pred_N v) (Some (Some ty)) gw.
Proof.
elim: flat_phi n code; move => //= [c cv] l IH n code Hphi v.
rewrite in_cons /= => /orP [/eqP ->|H]; inv Hphi; hsplit => //.
  split; first by [].
  by exists gw.
 split; first by [].
 by exists gw.
by move: (IH _ _ H5 _ H).
Qed.

Definition proc_instr_spec
           (pos: ValCirc.wire) (instr: ValCirc.gate) (args: list ValCirc.wire)
           (rk: N) (gm: PTree.t globv_info) (body: list gentry)
           (gm': PTree.t globv_info) : Prop :=
  match instr with
  | ValCirc.Gop op =>
    ∃ ge,
      body = ge :: nil ∧
      gm' = gm ∧
      if Op.eq_operation op Op.Omove
      then
        ∃ r1 ty gw,
          args = r1 :: nil ∧
          r1 < pos ∧
          is_localv r1 (Some (Some ty)) gw ∧
          add_gate_spec (Gid (wires_of_type ty)) (conn_ty ty gw) ge ∧
          is_localv pos (Some (Some ty)) (N.succ rk)
    else
      all_lt pos args ∧
      proc_op_spec op args ge ∧
      is_localv pos (Some (Some (snd (Op.type_of_operation op)))) (N.succ rk)

  | ValCirc.Gload ϰ addr =>
    ∃ addr_body v s gconn ge gd,
      body = gd :: ge :: addr_body ∧
      gm' = gm ∧
      all_lt pos args ∧
      proc_addr_spec addr args rk addr_body (v, s) ∧
      PTree.get v gm = Some gconn ∧
      align_chunk ϰ = size_chunk ϰ ∧
      let width := 8 * sizeN_chunk ϰ in
      match s with
      | inl off => add_gate_spec (Gselk (width, sizeN gconn, 8 * N_of_int off)) gconn ge
      | inr n =>
        add_gate_spec (Gsel (width, sizeN gconn))
                      (gconn ++ conn_new n (N.log2 (sizeN_chunk ϰ))
                                         (size2idxbits width (sizeN gconn)))
                      ge
      end ∧
      add_gate_spec (Gid (wires_of_type (type_of_chunk ϰ)))
        (chunk_ext ϰ wire_FF (conn_new (rk + sizeN addr_body + 1) 0 width)) gd ∧
      is_localv pos (Some (Some (type_of_chunk ϰ))) (N.succ (rk + sizeN addr_body + 1))

  | ValCirc.Gstore guard ϰ addr =>
    let ty := type_of_chunk ϰ in
    ∃ src aargs,
    args = src :: aargs ∧
    all_lt pos args ∧
    ∃ guard' addr_body v s nsrc gconn gg gu,
    body = gu :: gg :: addr_body ∧
    is_renamed pos guard guard' ∧
    proc_addr_spec addr aargs rk addr_body (v, s) ∧
    is_localv src (Some (Some ty)) nsrc ∧
    PTree.get v gm = Some gconn ∧
    add_gate_spec (Gguard guard') (conn_guard guard') gg ∧
    align_chunk ϰ = size_chunk ϰ ∧
    chunk_not_any ϰ ∧
    let width := 8 * sizeN_chunk ϰ in
    match s with
    | inl ofs =>
      add_gate_spec (Gupdk (width, sizeN gconn, 8*N_of_int ofs))
                    ((rk + sizeN addr_body + 1, 0)
                     :: takeN (8*sizeN_chunk ϰ)
                              (conn_ty (type_of_chunk ϰ) nsrc) ++ gconn) gu
    | inr n1 =>
      add_gate_spec (Gupd (width, sizeN gconn))
                    ((rk + sizeN addr_body + 1, 0)
                     :: takeN (8*sizeN_chunk ϰ)
                              (conn_ty (type_of_chunk ϰ) nsrc)
                     ++ gconn
                     ++(conn_new n1 (N.log2 (sizeN_chunk ϰ)) (size2idxbits width (sizeN gconn)))) gu
    end ∧
    globv_upd_spec gm v (conn_new (rk+sizeN addr_body+2) 0 (sizeN gconn)) gm'
    ∧ is_localv pos None (rk+sizeN addr_body+2)

  | ValCirc.Gtest guard cnd =>
    ∃ gate wargs guard' gc gg ga,
    gate_of_condition cnd = Some gate ∧
    all_lt pos args ∧
    localv_conn_list args wargs ∧
    is_renamed pos guard guard' ∧
    add_gate_spec gate wargs gc ∧
    add_gate_spec (Gguard guard') (conn_guard guard') gg ∧
    add_gate_spec G_AND ((rk + 1, 0) :: (rk + 2, 0) :: nil) ga ∧
    is_localv pos (Some None) (rk + 3) ∧
    body = ga :: gg :: gc :: nil ∧
    gm' = gm
  | ValCirc.Gφ φ =>
    ∃ φ' ty,
    monot_localv /\
    is_renamed pos φ φ' ∧
(*    all_lt pos args ∧ *)
    gm' = gm ∧
    phi_spec pos rk ty (sizeN body) (flat_phi_node φ') body ∧
    is_localv pos (Some (Some ty)) (rk + sizeN body)
  end.

Fixpoint proc_code_spec (pos: ValCirc.wire) (body: ValCirc.code)
         (rk: N) (gm: PTree.t globv_info) (body': list gentry)
         (gm': PTree.t globv_info) : Prop :=
  match body with
  | nil => body' = nil ∧ gm' = gm
  | instr :: body =>
    ∃ ges gmi ges',
    body' = ges ++ ges' ∧
    proc_instr_spec pos (ValCirc.ggate instr) (ValCirc.gwires instr) rk gm (seq.rev ges) gmi ∧
    proc_code_spec (pos + 1) body (rk + sizeN ges) gmi ges' gm'
  end.

Fixpoint add_inputs_spec n (ins: list (slot * ident))
         (gm gm': PTree.t globv_info) : Prop :=
  match ins with
  | nil => gm' = gm
  | ((x, o), _) :: ins =>
    let x := Pos.succ x in
    ∃ c,
    PTree.get x gm = Some c ∧
    add_inputs_spec (N.succ n) ins
                    (PTree.set x (conn_upd_at c (8 * N_of_int o)
                                   (conn_new 1 (n * 8) 8)) gm) gm'
  end.

Context (gm: PTree.t globv_info).

Fixpoint proc_outputs_spec (outs: list (slot * ident)) (conn: connector) : Prop :=
  match outs with
  | nil => conn = nil
  | ((x, o), _) :: outs =>
    ∃ c co, PTree.get (Pos.succ x) gm = Some c
            ∧ conn = takeN_dflt (0, 0) 8 (dropN (8 * N_of_int o) c) ++ co
            ∧ proc_outputs_spec outs co
  end.

End SPEC.



(* The localv map is increasing: only new mapping are added. *)
Definition localv_le (m m': PTree.t localv_info) : Prop :=
  ∀ r i, PTree.get r m = Some i → PTree.get r m' = Some i.

Definition localv_le_refl m : localv_le m m :=
  λ r i, id.

Definition localv_le_trans m' m m'' :
  localv_le m m' →
  localv_le m' m'' →
  localv_le m m'' :=
  λ A B r i H, B r i (A r i H).

Lemma is_localv_m m m' w ooty n:
  localv_le m m' →
  is_localv m w ooty n →
  is_localv m' w ooty n.
Proof. intros LE H; apply LE, H. Qed.

Lemma localv_conn_m m m' w c :
  localv_le m m' →
  localv_conn m w c →
  localv_conn m' w c.
Proof.
  intros LE (ooty & gn & X & Y).
  exists ooty, gn. split. eauto using is_localv_m. exact Y.
Qed.

Lemma localv_conn_list_m m m' ws c :
  localv_le m m' →
  localv_conn_list m ws c →
  localv_conn_list m' ws c.
Proof.
  intros LE. revert c.
  elim ws; clear ws.
  exact (λ _, id).
  intros w ws IH c (cL & c' & EQ & H & REC).
  exists cL, c'. eauto using localv_conn_m.
Qed.

Lemma bounded_localv_set lv pos twire q :
  twire < q.2 ->
  bounded_localv lv pos twire →
  bounded_localv (PTree.set (N.succ_pos pos) q lv) (N.succ pos) q.2.
Proof.
  intros LT B w ty n.
  unfold is_localv. rewrite Maps.PTree.gsspec. case peq.
   intro EQ. apply n_succ_pos_inj in EQ. subst. 
   move=> [->] /=; Psatz.lia.
  intros NE Hw; split. 
   etransitivity. 2: apply N.lt_succ_diag_r.
   eapply B; eauto.
  eapply N.lt_le_incl, N.le_lt_trans; last by exact LT.
  eapply B; eauto.
Qed.

Lemma is_renamed_m {A} cur m m' (t t': bdd A) :
  localv_le m m' →
  is_renamed m cur t t' →
  is_renamed m' cur t t'.
Proof.
  intros LE; revert t'.
  elim t; clear t.
  intros a t'. exact id.
  intros v ℓ IHℓ r IHr t' (n & v' & ℓ' & r' & Hcur & Hn & H & Hℓ & Hr & ->).
  exists n, v', ℓ', r'.
  eauto 10 using is_localv_m.
Qed.

Lemma proc_op_spec_m m m' op args ge :
  localv_le m m' →
  proc_op_spec m op args ge →
  proc_op_spec m' op args ge.
Proof.
  intros LE (g & wargs & H & K & L).
  exists g, wargs.
  eauto using localv_conn_list_m.
Qed.

Lemma proc_addr_spec_m m m' addr args rk body o :
  localv_le m m' →
  proc_addr_spec m addr args rk body o →
  proc_addr_spec m' addr args rk body o.
Proof.
  intros LE. destruct addr; try exact id;
  simpl;
  intros (? & ? & -> & ? & -> & ->);
  eauto 8 using proc_op_spec_m.
Qed.

Lemma proc_phi_spec_m m m' pos rk ty sz phi body:
  localv_le m m' →
  phi_spec m pos rk ty sz phi body →
  phi_spec m' pos rk ty sz phi body.
Proof.
move=> LE; elim.
 move=> c v g ge gg Hle [H1 [H2 H3]].
 econstructor; eauto.
 split.
  eapply is_localv_m, H1.
  by apply LE.
 by split.
move=> c v l pos' rk' ge gg gx xs Hlt.
move=> H1 H2 [H3 H4] H5.
econstructor; eauto.
split; last eassumption.
eapply is_localv_m, H3.
by apply LE.
Qed.

Lemma proc_instr_spec_m m m' pos instr args rk gm body gm' :
  localv_le m m' →
  monot_localv m' ->
  proc_instr_spec m pos instr args rk gm body gm' →
  proc_instr_spec m' pos instr args rk gm body gm'.
Proof.
  intros LE MON. unfold proc_instr_spec. intros H.
  repeat match goal with
  | H: False |- _ => destruct H
  | H: ∃ a, _ |- _ => destruct H as [? H]
  | H: _ ∧ _ |- _ => destruct H
  | H: ?a = ?b |- _ => subst a || subst b
  | |- match ?a with _ => _ end => destruct a
  | H: match ?a with _ => _ end |- _ => destruct a
  end;
  eauto 34 using is_localv_m, localv_conn_list_m,
    proc_op_spec_m, proc_addr_spec_m, is_renamed_m, proc_phi_spec_m.
Qed.

End CONDV.

Record ok_state (pfx: N) (pos: N) (st: state) : Prop :=
  OK { ok_wire: st_wire st = pfx + sizeN (st_code st)
     ; ok_twire: st_twire st <= st_wire st
     ; ok_local: bounded_localv (st_localv st) pos (st_twire st)
     ; ok_monot: monot_localv (st_localv st)
    }.

Definition incr_state (st st': state) : Prop :=
  localv_le (st_localv st) (st_localv st') ∧
  monot_localv (st_localv st') ∧
  st_condv st' = st_condv st.

Definition incr_state_refl pfx cur st: 
  ok_state pfx cur st -> incr_state st st.
Proof.
move=> [H1 H2 H3]; split; last by [].
by apply localv_le_refl.
Defined.

Definition incr_state_trans st' st st'' :
  incr_state st st' →
  incr_state st' st'' →
  incr_state st st''.
Proof.
  intros [A [B C]] [A' [B' C']].
  split. apply (localv_le_trans A A'). 
  split; first by [].
  congruence.
Qed.

Lemma localv_get_correct v st i st' :
  localv_get v st = inl (i, st') →
  is_localv (st_localv st) v (fst i) (snd i) ∧ st' = st.
Proof.
  unfold localv_get, is_localv.
  intros H. mstate_bind. hsplit.
  destruct (PTree.get _ _) as [(?, ?)|]. apply inl_eq in H. hsplit.
  auto.
  revert H. apply inr_inl.
Qed.

Lemma globv_get_correct v st i st' :
  globv_get v st = inl (i, st') →
  PTree.get v (st_globv st) = Some i ∧ st' = st.
Proof.
  unfold globv_get, merror_globv_get, merror_ret, globv_info.
  intros H. mstate_bind. hsplit.
  destruct (@PTree.get connector v (st_globv st0)); split; auto;
  inversion_clear H.
  reflexivity.
Qed.

Lemma monot_localv_ok pfx st w x:
 ok_state pfx w st ->
 (st_localv st) ! (N.succ_pos w) = None ->
 st_twire st < x.2 ->
 monot_localv (PTree.set (N.succ_pos w) x (st_localv st)).
Proof.
move=> [OK1 OK2 OK3 OK4] Hw Hx a1 a2 t1 t2 b1 b2.
case E1: (w == a1).
 move: E1 => /eqP <- Ha.
 rewrite /is_localv PTree.gss; move=> [-Ex]; subst.
 rewrite PTree.gso => Hb.
 apply OK3 in Hb; lia.
 apply n_succ_pos_inj in Hb. lia.
rewrite /is_localv PTree.gso; last first.
 by move: E1 => /eqP E H; apply E; symmetry; apply n_succ_pos_inj.
case E2: (w == a2).
 move: E2 => /eqP <- Ha.
 rewrite PTree.gss; move=> [-Ex] [-Ey]; subst.
 apply OK3 in Ex. hsplit. simpl in Hx. lia.
rewrite PTree.gso; last first.
 by move: E2 => /eqP E2 H; apply E2; symmetry; apply n_succ_pos_inj.
by apply OK4.
Qed.

Lemma localv_conn_list_all_lt pfx pos st args x:
 ok_state pfx pos st ->
 localv_conn_list (st_localv st) args x ->
 all_lt pos args.
Proof.
move=> [ok1 ok2 ok3 ok4] /localv_conn_list_is_localv.
rewrite /all_lt; elim args => //=.
move=> w ws IH H w' [<-|Hw'].
 have T: w=w \/ In w ws by left.
 move: (H _ T) => [t [g Hl]].
 by move: (ok3 _ _ _ Hl) => [? _].
have T: w=w' \/ In w' ws by right.
move: (H _ T) => [t [g Hl]].
by move: (ok3 _ _ _ Hl) => [? _].
Qed.

Lemma localv_set_correct pfx v x st st' :
  ok_state pfx v st ->
  localv_set v x st = inl (tt, st') →
  incr_state st st' ∧
  is_localv (st_localv st') v (fst x) (snd x) ∧
  st_wire st' = st_wire st ∧
  st_twire st' = x.2 ∧
  st_code st' = st_code st ∧
  st_globv st' = st_globv st ∧
  st_localv st' = PTree.set (N.succ_pos v) x (st_localv st).
Proof.
  unfold localv_set, is_localv.
  intros OK H. apply mstate_bind_inv in H.
move: (OK) => [OK1 OK2 OK3 OK4].
  destruct H as (s & s' & X & H). apply inl_eq, pair_eq in X.
  destruct X as (-> & ->).
  destruct (PTree.get _ (st_localv s')) as [ i | ] eqn: K.
   revert H. apply inr_inl.
  move: H; case: (ifP _) => LT; last by apply inr_inl.
  move=> H; apply inl_eq, pair_eq in H. destruct H as [_ <-].
  split. 
   split.
    intros r i H. simpl. rewrite Maps.PTree.gso. auto. congruence.
   split; last reflexivity.
   rewrite /st_localv /=.
    eapply monot_localv_ok; eauto.
    by apply N.ltb_lt.
  split. 
   simpl. rewrite Maps.PTree.gss. f_equal. destruct x; reflexivity.
  split; first reflexivity.
  auto.
Qed.

Lemma condv_get_correct cur v st n st' :
  condv_get cur v st = inl (n, st') →
  ∃ c,
  PTree.get v (st_condv st) = Some c ∧
  is_localv (st_localv st) c (Some None) n ∧
  c < cur ∧
  st' = st.
Proof.
  unfold condv_get.
  intros H. mstate_bind. hsplit.
  destruct (PTree.get _ _)=> //; mstate_bind.
  move: H; case: (ifP _) => Hcur // H; mstate_bind.
  destruct x as [[[ty|]|] x] => //.
  apply localv_get_correct in H0; hsplit.
  simpl in H0; inv H.
  exists n0; repeat split; auto.
  by apply N.ltb_lt.
Qed.

Lemma bdt_ren_correct {A} cur (t: bdd A) st t' st' :
  bdt_ren cur t st = inl (t', st') →
  is_renamed (st_condv st) (st_localv st) cur t t' ∧
  st' = st.
Proof.
elim: t st t' st'.
 by move=> s st t' st' H; apply inl_eq in H; hsplit; split; reflexivity.
move=> v ℓ IHℓ r IHr st t' st' /= H; mstate_bind.
apply condv_get_correct in H0; hsplit.
move: H; case Ep: x => [|p] //= H; inv H.
move: (IHℓ _ _ _ H1) => Hℓ.
move: (IHr _ _ _ H2) => Hr; hsplit.
split; last by [].
exists c , p , x0, x1; auto 8.
Qed.

Lemma add_gate_correct {pfx pos g c st n st'} :
  ok_state pfx pos st →
  add_gate_unsafe g c st = inl (n, st') →
  ok_state pfx pos st' ∧
  st_wire st' = N.succ (st_wire st) ∧
  st_twire st' = st_twire st ∧
  incr_state st st' ∧
  st_globv st' = st_globv st ∧
  n = st_wire st' ∧
  ∃ ge,
  add_gate_spec g c ge ∧
  st_code st' = ge :: st_code st.
Proof.
  intros OK; move: (OK) => [OK1 OK2 OK3 OK4].
  unfold add_gate_unsafe.
  case: eqP. 2: intros _; apply inr_inl.
  intros EQ H. apply inl_eq, pair_eq in H. destruct H as [<- <-]. simpl.
  split. split. simpl. rewrite OK1. Psatz.lia. 
simpl. lia.
apply OK3.
  by [].
  split. reflexivity.
  split. auto. split.
   split; first by apply localv_le_refl.
   by auto.
  unfold add_gate_spec. eauto 6.
Qed.

Lemma add_gate_ty_correct {pfx pos ty g c st n st'} :
  ok_state pfx pos st →
  add_gate_ty ty g c st = inl (n, st') →
  ok_state pfx pos st' ∧
  st_wire st' = N.succ (st_wire st) ∧
  st_twire st' = st_twire st ∧
  incr_state st st' ∧
  st_globv st' = st_globv st ∧
  n = st_wire st' ∧
  ∃ ge,
  add_gate_ty_spec ty g c ge ∧
  st_code st' = ge :: st_code st.
Proof.
  intros OK.
  unfold add_gate_ty.
  case: eqP. 2: intros _; apply inr_inl.
  intros EQ H. generalize (add_gate_correct OK H). clear H.
  unfold add_gate_ty_spec.
  intros (? & ? & ? & ? & ? & ? & ? & ? & ?). eauto 10.
Qed.

Lemma args_wires_correct {pfx pos ws st c st'} :
  ok_state pfx pos st →
  args_wires ws st = inl (c, st') →
  ok_state pfx pos st' ∧
  incr_state st st' ∧
  st_globv st' = st_globv st ∧
  st_code st' = st_code st ∧
  st_wire st' = st_wire st ∧
  st_twire st' = st_twire st ∧
  localv_conn_list (st_localv st') ws c.
Proof.
  revert st c st'. elim ws; clear ws.
  intros st c st' OK H. apply inl_eq, pair_eq in H. destruct H as [<- <-].
  simpl. eauto 10 using incr_state_refl.
  intros w ws IH st c st' OK.
  simpl. unfold localv_get_conn.
  intros H; mstate_bind; hsplit.
  destruct x1 as [[[ty|]|] x12]; inv H0.
  apply localv_get_correct in H2; hsplit.
  simpl in H.
  move: (IH _ _ _ OK H1); intuition.
  eexists _, _; split; eauto; split; eauto;
  unfold incr_state in *;
  eapply localv_conn_m; intuition eauto; eexists _, _; split; eauto; simpl; eauto.
Qed.

Lemma proc_op_correct {pfx pos st op args q st'} :
  ok_state pfx pos st →
  proc_op op args st = inl (q, st') →
  ok_state pfx pos st' ∧
  incr_state st st' ∧
  st_globv st' = st_globv st ∧
  st_wire st' = N.succ (st_wire st) ∧
  st_twire st' = st_twire st ∧
  fst q = snd (Op.type_of_operation op) ∧
  snd q = st_wire st' ∧
  ∃ ge,
  st_code st' = ge :: st_code st ∧
  proc_op_spec (st_localv st') op args ge.
Proof.
  intros OK.
  unfold proc_op, proc_op_spec.
  destruct (gate_of_operation _) as [ g | ]. 2: apply inr_inl.
  destruct (Op.type_of_operation _) as (?, ty).
  intros H. mstate_bind.
  repeat
  match goal with
  | OK : ok_state _ _ ?s, H : args_wires _ ?s = inl _ |- _ =>
    generalize (args_wires_correct OK H); clear H; intros H; hsplit
  | OK : ok_state _ _ ?s, H : add_gate_ty _ _ _ ?s = inl _ |- _ =>
    generalize (add_gate_ty_correct OK H); clear H; intros H; hsplit
  end.
  split. assumption.
  split. eauto using incr_state_trans.
  split. congruence.
  split. congruence.
  split. congruence. 
  split. reflexivity.
  split. reflexivity.
  exists ge. split. congruence.
  unfold incr_state in *. hsplit.
  eauto 6 using localv_conn_list_m.
Qed.

Lemma proc_addr_correct {pfx pos addr args st q st'} :
  ok_state pfx pos st →
  proc_addr addr args st = inl (q, st') →
  ok_state pfx pos st' ∧
  incr_state st st' ∧
  st_globv st' = st_globv st ∧
  ∃ body,
  st_code st' = body ++ st_code st ∧
  proc_addr_spec (st_localv st') addr args (st_wire st) body q.
Proof.
  intros OK. unfold proc_addr.
  repeat match goal with
  | |- match ?a with _ => _ end _ = inl _ → _ =>
    destruct a; try apply inr_inl
  end;
  intros H; mstate_bind; hsplit;
  repeat match goal with H : proc_op _ _ _ = inl _ |- _ =>
                         generalize (proc_op_correct OK H); clear H; intros H; hsplit end;
  simpl;
  eauto 12 using incr_state_refl, app_nil_l.
  simpl in *.
  split. assumption.
  split. assumption.
  split. assumption.
  exists (ge :: nil). split. assumption.
  eexists _, _.
  split. reflexivity.
  split. eassumption.
  split. reflexivity.
  f_equal. f_equal. rewrite N.add_1_r. congruence.
  split. assumption.
  split. assumption.
  split. assumption.
  exists (ge :: nil). split. assumption.
  eexists _, _.
  split. reflexivity.
  split. eassumption.
  split. reflexivity.
  f_equal. f_equal. rewrite N.add_1_r. congruence.
Qed.


Lemma merror_globv_get_correct x m c :
  merror_globv_get x m = inl c →
  PTree.get x m = Some c.
Proof.
  unfold merror_globv_get.
  destruct (PTree.get _ m ). 2: apply inr_inl.
  intros H; apply inl_eq in H. f_equal. auto.
Qed.

Lemma proc_addr_spec_all_pos pos twire lv ad ar rk bo q :
  bounded_localv lv pos twire →
  proc_addr_spec lv ad ar rk bo q →
  all_lt pos ar.
Proof.
  intros B.
  destruct ad; simpl; intros H; hsplit;
  intros ?; (intros [ <- | () ] || intros ());
  red in H; hsplit;
  match goal with
  | H : localv_conn_list _ _ _ |- _ =>
    edestruct (localv_conn_list_is_localv H) as (? & ? & ?); simpl; eauto
  end.
  eapply B; eauto.
  eapply B; eauto.
Qed.

Ltac rw :=
  repeat match goal with H : _ = _ |- _ => rewrite H end.

Lemma proc_load_ok pfx pos st st' x addr args t:
 ok_state pfx pos st ->
 proc_load x addr args st = inl (t, st') ->
 ok_state pfx pos st' /\ st_twire st' < st_wire st'.
Proof.
rewrite /proc_load; move=> OK.
case E1: (align_chunk x == size_chunk x) => //= H; mstate_bind.
apply (proc_addr_correct OK) in H0; hsplit.
unfold add_gate_selk, add_gate_decode_val, globv_get in *.
destruct x0 as [v [o|n]]; mstate_bind.
 inv H9;repeat match goal with
        | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
              generalize (add_gate_correct OK H); clear H; intros H; hsplit
        | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
        end.
 rw; split; first by [].
 move: (ok_twire H0); rewrite -!N.add_1_l; lia.
unfold add_gate_sel, add_gate_decode_val, globv_get in *.
inv H8; inv H; mstate_bind.
repeat match goal with
       | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
             generalize (add_gate_correct OK H); clear H; intros H; hsplit
       | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
       end.
rw; split; first by [].
move: (ok_twire H0); rewrite -!N.add_1_l; lia.
Qed.

Lemma localv_set_ok pfx pos st st' oty:
 ok_state pfx pos st ->
 st_twire st < st_wire st ->
 st' = mkstate (st_wire st) (st_wire st) (st_code st)
               (st_globv st) (PTree.set (N.succ_pos pos)
                                        (oty, st_wire st)
                                        (st_localv st))
               (st_condv st) ->
 ok_state pfx (N.succ pos) st'.
Proof.
move=> [ok1 ok2 ok3 ok4] Htwire ->; split; simpl; auto.
  reflexivity.
 move=> x t n; rewrite /is_localv. case E: (x==pos).
  rewrite (eqP E) PTree.gss; move=> [_ <-]; split; lia.
 rewrite /is_localv PTree.gso; last first.
  by move=> /n_succ_pos_inj H; move/negP: E; apply; apply/eqP.
 move=> H; move: (ok3 x t n H) => [H1 H2]; split; lia.
move=> x1 x2 t1 t2 n1 n2 Hx.
rewrite /is_localv; case E: (x2 == pos).
 rewrite (eqP E) PTree.gss PTree.gso; last first.
  rewrite -(eqP E)=> /n_succ_pos_inj H; lia.
 move=> H [[E1 <-]].
 apply N.le_lt_trans with (st_twire st); last by [].
 by move: (ok3 x1 t1 n1 H) => [_].
move=> H1; rewrite PTree.gso; first last.
 by move=> /n_succ_pos_inj H; move/negP: E; apply; apply/eqP.
move=> H2; move: H1; rewrite PTree.gso; last first.
 move: (ok3 x2 t2 n2 H2) => [H _] /n_succ_pos_inj HH; lia.
by move=> H1; apply (ok4 _ _ _ _ _ _ Hx H1 H2).
Qed.

Lemma globv_upd_correct pfx pos x c st st':
 ok_state pfx pos st ->
 globv_upd x c st = inl (tt,st') ->
 incr_state st st' /\
 globv_upd_spec (st_globv st) x c (st_globv st') /\
 st_wire st' = st_wire st /\
 st_twire st' = st_twire st /\
 st_code st' = st_code st /\
 st_localv st' = st_localv st /\
 st_condv st' = st_condv st.
Proof.
rewrite /globv_upd => OK H; mstate_bind.
inv H0.
move: H; case Hc: ((st_globv st0) ! x) => [c'|] //.
case: (ifP _) => // /eqP E.
rewrite /mstate_updstate /st_upd_globv; move => [[<-]] /=.
repeat split => //=.
 by eapply ok_monot; eauto.
rewrite /globv_upd_spec; eexists; split; first eassumption.
by split.
Qed.

Lemma proc_store_ok pfx pos st st' guard x addr args src gw:
 ok_state pfx pos st ->
 proc_store guard x addr args src st = inl (gw, st') ->
 ok_state pfx pos st' /\ st_twire st' < st_wire st'.
Proof.
rewrite /proc_store; move=> OK H; mstate_bind.
move: H; case: (ifP _) => // _ H; mstate_bind.
apply (proc_addr_correct OK) in H0; hsplit.
destruct x0 as [v [vo|vinfo]]; 
destruct x1 as [[[vt|]|] vg]; try solve [inversion_clear H];
destruct (typ_eq (type_of_chunk x) vt); simpl in H; try solve [inversion_clear H];
mstate_bind;
apply localv_get_correct in H1; simpl in *; hsplit.
 unfold add_gate_updk, add_gate_guard, globv_get in *; mstate_bind.
 inv H; inv H7.
 repeat match goal with
        | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
        | OK: ok_state _ _ ?s, H : globv_upd _ _ ?s = inl _ |- _ =>
        generalize (globv_upd_correct OK H); clear H; intros H; hsplit
        | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
        end.
 split.
  destruct H0; split; rw.
  - simpl; lia.
  - move: ok_twire0; rw; lia.
  - move: (ok_local H8); rewrite /bounded_localv.
    by rw.
  - by apply (ok_monot H8).
 rw; move: (ok_twire H0); lia.
unfold add_gate_upd, add_gate_guard, globv_get in *; mstate_bind.
inv H; inv H7.
repeat match goal with
        | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
        | OK: ok_state _ _ ?s, H : globv_upd _ _ ?s = inl _ |- _ =>
        generalize (globv_upd_correct OK H); clear H; intros H; hsplit
        | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
        end.
split.
 destruct H0; split; rw.
 - simpl; lia.
 - move: ok_twire0; rw; lia.
 - move: (ok_local H8); rewrite /bounded_localv.
   by rw.
 - by apply (ok_monot H8).
rw; move: (ok_twire H0); lia.
Qed.


Lemma proc_phi_conds_correct pfx pos st l st' ty gn:
 ok_state pfx pos st ->
 proc_phi_conds l st = inl ((ty,gn), st') ->
 ok_state pfx pos st' /\
 incr_state st st' /\
 exists body,
  sizeN body > 0 /\
  st_wire st' = gn /\
  st_twire st' = st_twire st /\
  st_code st' = body ++ st_code st /\
  st_globv st' = st_globv st /\
  phi_spec (st_localv st') pos (st_wire st) ty (sizeN body) l body.
Proof.
move=> OK; elim: l gn st' => //=.
move=> [c v] [|x xs] IH gn st' H; mstate_bind.
 destruct x as [[[t|]|] gw] => // {IH}; mstate_bind.
 apply localv_get_correct in H0; hsplit; simpl in *.
 unfold add_gate_guard in H1; mstate_bind; inv H1.
 apply (add_gate_correct OK) in H; hsplit.
 apply (add_gate_ty_correct H) in H2; unfold add_gate_ty_spec in H2; hsplit.
 split; first assumption.
 split; first by eauto using incr_state_trans.
 exists [:: ge0; ge].
 split; first by simpl; lia.
 split; first reflexivity.
 split; first by rw.
 split; first by rw.
 split; first by rw.
 apply phi_spec_single with gw.
- by move: (ok_local OK H0) => [? _].
- split.
   apply is_localv_m with (st_localv st) => //.
   have: incr_state st st' by eauto using incr_state_trans.
   by move => [? _].
  split; first assumption.
  split; first assumption.
  by move: H14; rw; rewrite -N.add_1_r; apply.
destruct x0 as [[[t|]|] gw] => //; mstate_bind.
move: H; destruct (typ_eq t x0.1) => //= H; mstate_bind.
apply localv_get_correct in H0; hsplit.
destruct x0 as [t gg].
move: {IH H1} (IH _ _ H1); simpl in * => H1; hsplit.
unfold add_gate_guard in H2; mstate_bind; inv H2.
apply (add_gate_correct H) in H10; hsplit.
apply (add_gate_ty_correct H2) in H3; unfold add_gate_ty_spec in H3; hsplit.
apply (add_gate_ty_correct H3) in H4; unfold add_gate_ty_spec in H4; hsplit.
split; first assumption.
split; first by eauto using incr_state_trans.
exists [:: ge1, ge0, ge & body].
split; first by simpl; lia.
split; first reflexivity.
split; first by rw.
split; first by rw.
split; first by rw.
rewrite [sizeN _]/= -!N.add_1_l ?N.add_assoc.
apply phi_spec_cons with gw.
- by move: (ok_local OK H0) => [? _].
- apply proc_phi_spec_m with (st_localv st1) => //.
  have: incr_state st1 st' by eauto using incr_state_trans.
  by move => [? _].
- split.
   apply is_localv_m with (st_localv st) => //.
   have: incr_state st st' by eauto using incr_state_trans.
   by move => [? _].
  split; first assumption.
  split; first assumption.
  move: H22; rw; rewrite (ok_wire H) (ok_wire OK); rw.
  have ->: N.succ (pfx + sizeN (body ++ st_code st)) = pfx + sizeN (st_code st) + sizeN body + 1.
   rewrite sizeN_app; lia.
  by apply.
- split; first assumption.
  move: H29; rw; rewrite (ok_wire H) (ok_wire OK); rw.
  rewrite sizeN_app -!N.add_1_r.
  have ->: sizeN body + sizeN (st_code st) = sizeN (st_code st) + sizeN body by apply N.add_comm.
  by rewrite -!N.add_assoc /=; apply.
Qed.


Opaque N.mul.
Lemma proc_instr_correct pfx pos instr args st st' :
  ok_state pfx pos st →
  proc_instr pos instr args st = inl (tt, st') →
  ok_state pfx (N.succ pos) st' ∧
  incr_state st st' ∧
  ∃ body',
    st_code st' = body' ++ st_code st ∧
    proc_instr_spec (st_condv st') (st_localv st') pos instr args (st_wire st)
                    (st_globv st) body' (st_globv st').
Proof.
  intros OK.
  destruct instr as [ op | ϰ addr | g ϰ addr | g cnd | φ ]; simpl.
  - case (Op.eq_operation _ _).
    + intros ->. destruct args as [ | r1 [ | ? ? ] ]; try apply inr_inl.
      intros H; mstate_bind.
      repeat match goal with
             | o : (option (option typ) * _)%type |- _ => destruct o as [[[|]|] ? ]; simpl in *; mstate_bind; try (revert H; apply inr_inl)
             | H : localv_get _ _ = inl _ |- _ => apply localv_get_correct in H; destruct H; subst
             | OK : ok_state _ _ _, H : localv_set _ _ _ = inl _ |- _ => apply (localv_set_correct OK) in H; destruct H as (? & ? & ? & ? & ?); hsplit
             | OK : ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
               generalize (add_gate_correct OK H); clear H; intros H; hsplit
             end.
      simpl in *.
      split.
        split. destruct H1. congruence.
          by rw; reflexivity.
        rw. eapply bounded_localv_set, ok_local; eauto. 
        simpl; rw.
        eapply N.le_lt_trans. eapply ok_twire; eauto.
        lia.
       by eapply H.
      split.
       by eauto using incr_state_trans.
      exists (ge :: nil). split. simpl. 
      congruence.
      eexists. split. reflexivity.
      split. congruence.
      eexists _, _, _.
      split. reflexivity.
      unfold incr_state in *; hsplit.
      split. eapply ok_local. 2: eassumption. eassumption.
      split. eapply is_localv_m. 2: eassumption. eauto using localv_le_trans.
      split. eassumption.
      congruence.
    + intros NE H. mstate_bind. 
      match goal with H : proc_op _ _ _ = inl _ |- _ =>
                      generalize (proc_op_correct OK H); clear H; intros H
      end.
      hsplit.
      eapply localv_set_correct in H; last eassumption.
      destruct H as (INCR & Hlocal & Hw & Htw & Hc & Hg & Hl).
      simpl.
      split.
        split. rw.  rewrite (ok_wire OK) /=; lia.
         rw; reflexivity.
        rw. eapply bounded_localv_set. 2: eapply ok_local; eassumption.
        simpl; rw. 
        apply N.le_lt_trans with (st_wire st); last lia.
        eapply OK.
        eapply INCR.
      split. eauto using incr_state_trans.
      exists (ge :: nil). split. simpl. congruence.
      eexists. split. reflexivity.
      split. congruence.
      split. unfold proc_op_spec in *. hsplit.
        intros w A. edestruct localv_conn_list_is_localv as (oty & gn & B); try eassumption.
        eapply ok_local; eauto.
      split. eapply proc_op_spec_m; eauto.
      unfold incr_state in *. hsplit. eauto using localv_le_trans.
      simpl in *. intuition congruence.

  - (* proc_load *)
    intros H. mstate_bind.
    move: (proc_load_ok OK H0) => [OK' OK_twire].
    apply (@localv_set_correct pfx) in H; auto.
    destruct H as (INCR & Hlocal & Hw & Htw & Hc & Hg & Hl).
    move: H0; rewrite /proc_load; case: (ifP _) => [/eqP E|_] H0; mstate_bind;
     last by inv H0.
    match goal with H : proc_addr _ _ _ = _ |- _ =>
                    generalize (proc_addr_correct OK H); clear H; intros H
    end.
    match goal with H : (ident * (int + gate_number))%type |- _ => destruct H as (v, [ ofs | n ]) end;
      mstate_bind; hsplit.
    + unfold add_gate_selk, add_gate_decode_val, globv_get in *.
      mstate_bind; hsplit. simpl in *.
      repeat match goal with
      | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
      | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
      end.
      split.
       apply localv_set_ok with st0 (Some (Some (type_of_chunk ϰ))); auto.
        move: INCR => [INCR1 [INCR2 INCR3]].
        destruct st'; simpl in *; subst; reflexivity.
       split. eauto using incr_state_trans.
      eexists (_ :: _ :: body). split. rw. reflexivity.
      eexists _, _, _, _, _, _. split. reflexivity.
      split. congruence.
      split. eauto using proc_addr_spec_all_pos, ok_local.
      split. eapply proc_addr_spec_m; eauto.
      unfold incr_state in *; hsplit; eauto using localv_le_trans.
      split. etransitivity. 2: eassumption. rw. reflexivity.
      split. eassumption.
      split. eassumption.
      assert (st_wire st3 = st_wire st + sizeN body + 1) as X.
      { rw. erewrite ! ok_wire by eassumption. rw.
        rewrite sizeN_app. Psatz.lia. }
      split. rewrite -> X in *. assumption.
      revert Hlocal. rw. exact id.
    + revert H0.
      intros H0. mstate_bind.
      unfold add_gate_sel, add_gate_decode_val, globv_get in *.
      mstate_bind; hsplit. simpl in *.
      repeat match goal with
      | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
      | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
      end.
      split.
       apply localv_set_ok with st0 (Some (Some (type_of_chunk ϰ))); auto.
        move: INCR => [INCR1 [INCR2 INCR3]].
        destruct st'; simpl in *; subst; reflexivity.
       split. eauto using incr_state_trans.
      eexists (_ :: _ :: body). split. rw. reflexivity.
      eexists _, _, _, _, _, _. split. reflexivity.
      split. congruence.
      split. eauto using proc_addr_spec_all_pos, ok_local.
      split. eapply proc_addr_spec_m; eauto.
      unfold incr_state in *; hsplit; eauto using localv_le_trans.
      split. etransitivity. 2: eassumption. rw. reflexivity.
      split. assumption.
      split. assumption.
      assert (st_wire st3 = st_wire st + sizeN body + 1) as X.
      { rw. erewrite ! ok_wire by eassumption. rw.
        rewrite sizeN_app. Psatz.lia. }
      rewrite -> X in *. split. assumption.
      revert Hlocal. rw. exact id.
  - (* proc_store *)
    destruct args as [ | src addr_args ]. apply inr_inl.
    intros H; mstate_bind.
    apply bdt_ren_correct in H0. hsplit.
    move: (proc_store_ok OK H1) => [OK' OK_twire].
    apply (@localv_set_correct pfx) in H; auto; hsplit.
    simpl in H2.
    move: H1; rewrite /proc_store; case: (ifP _) => [/eqP E|_] H1; mstate_bind;
     last by inv H1.
    apply localv_get_correct in H9. 
    generalize (proc_addr_correct OK H8); clear H8; intro H8; hsplit.
    destruct x1 as [v [Hv|Hv]].
    + (* global with constant offset *)
      destruct x2 as [[[ty|]|] n1]; [|inversion_clear H1|inversion_clear H1].
      destruct (typ_eq (type_of_chunk ϰ) ty); simpl in H1; [|inversion_clear H1].
      mstate_bind.
      hsplit; simpl in *.
      apply globv_get_correct in H14.
      unfold add_gate_updk, add_gate_guard in *; mstate_bind.
      inv H15; hsplit; repeat match goal with
      | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
      | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
      end.
      apply (globv_upd_correct H16) in H17; hsplit.
      split.
       apply localv_set_ok with st1 None; auto.
        destruct st'; simpl in *; subst. 
         rw; f_equal.
        move: H => [INCR1 [INCR2 /= INCR3]].
        unfold globv_upd_spec in *; hsplit.
        rw; f_equal. 
       split. by eauto using incr_state_trans.
      exists ([:: ge0; ge]++body); split.
       simpl; rw; reflexivity.
      eexists; eexists; split; first reflexivity.
      split.
       move: (ok_local H8) => T.
       move=> k /= [<-|Hk].
        by move: (T _ _ _ H9) => [? _].
       by apply (proc_addr_spec_all_pos T H13 Hk).
      eexists _, _, _, _, _, _, _, _.
      split; first reflexivity.
      have: incr_state st st' by eauto using incr_state_trans.
      rewrite /incr_state; move=> [I1 [I2 I3]].
      split. 
       by rewrite I3; apply (is_renamed_m I1 H0).
      split.
       eapply proc_addr_spec_m; last by apply H13.
       have: incr_state st0 st' by eauto using incr_state_trans.
       by rewrite /incr_state; move=> [? _].
      split.
       eapply is_localv_m; last by apply H9.
       have: incr_state st0 st' by eauto using incr_state_trans.
       by rewrite /incr_state; move=> [? _].
      split.
       rewrite -H11; eassumption.
      split; first assumption.
      move/eqP: E => /andP [/eqP E1 E2].
      split; first assumption.
      split; first assumption.
      assert (st_wire st3 = st_wire st + sizeN body + 1) as X.
      { rw. erewrite ! ok_wire by eassumption. rw.
        rewrite sizeN_app. Psatz.lia. }
      rewrite -> X in *.
      split.
       have ->: takeN (8 * sizeN_chunk ϰ) (conn_ty (type_of_chunk ϰ) n1)
                = conn_new n1 0 (8 * sizeN_chunk ϰ).
        destruct ϰ; reflexivity.
       by apply H27.
      split. 
       revert H29; rw.
       by rewrite -H14 -N.add_1_r -N.add_assoc /=; apply.
      have <-: st_twire st' = st_wire st + sizeN body + 2.
       rw; rewrite -H14 -N.add_1_r; lia.
      by apply H2.
    + (* global with variable offset *)
      destruct x2 as [[[ty|]|] n1]; [|inversion_clear H1|inversion_clear H1].
      destruct (typ_eq (type_of_chunk ϰ) ty); simpl in H1; [|inversion_clear H1].
      mstate_bind.
      hsplit; simpl in *.
      apply globv_get_correct in H14.
      unfold add_gate_upd, add_gate_guard in *; mstate_bind; hsplit.
      repeat match goal with
      | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
      | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
      end.
      apply (globv_upd_correct H16) in H17; hsplit.
      split.
       apply localv_set_ok with st1 None; auto.
        destruct st'; simpl in *; subst. 
         rw; f_equal.
        move: H => [INCR1 [INCR2 /= INCR3]].
        unfold globv_upd_spec in *; hsplit.
        rw; f_equal. 
       split. by eauto using incr_state_trans.
      exists ([:: ge0; ge]++body); split.
       simpl; rw; reflexivity.
      eexists; eexists; split; first reflexivity.
      split.
       move: (ok_local H8) => T.
       move=> k /= [<-|Hk].
        by move: (T _ _ _ H9) => [? _].
       by apply (proc_addr_spec_all_pos T H13 Hk).
      eexists _, _, _, _, _, _, _, _.
      split; first reflexivity.
      have: incr_state st st' by eauto using incr_state_trans.
      rewrite /incr_state; move=> [I1 [I2 I3]].
      split. 
       by rewrite I3; apply (is_renamed_m I1 H0).
      split.
       eapply proc_addr_spec_m; last by apply H13.
       have: incr_state st0 st' by eauto using incr_state_trans.
       by rewrite /incr_state; move=> [? _].
      split.
       eapply is_localv_m; last by apply H9.
       have: incr_state st0 st' by eauto using incr_state_trans.
       by rewrite /incr_state; move=> [? _].
      split.
       rewrite -H11; eassumption.
      split; first assumption.
      move/eqP: E => /andP [/eqP E1 E2].
      split; first assumption.
      split; first assumption.
      assert (st_wire st3 = st_wire st + sizeN body + 1) as X.
      { rw. erewrite ! ok_wire by eassumption. rw.
        rewrite sizeN_app. Psatz.lia. }
      rewrite -> X in *.
      split.
       have ->: takeN (8 * sizeN_chunk ϰ) (conn_ty (type_of_chunk ϰ) n1)
                = conn_new n1 0 (8 * sizeN_chunk ϰ).
        destruct ϰ; reflexivity.
       by apply H27.
      split. 
       revert H29; rw.
       by rewrite -H14 -N.add_1_r -N.add_assoc /=; apply.
      have <-: st_twire st' = st_wire st + sizeN body + 2.
       rw; rewrite -H14 -N.add_1_r; lia.
      by apply H2.
  - (* test *)
    destruct (gate_of_condition _) as [ gate | ] eqn: Hcnd. 2: apply inr_inl.
    intros H; mstate_bind.
    apply bdt_ren_correct in H2; hsplit.
    unfold add_gate_and_guard, add_gate_guard in *; mstate_bind.
    inv H3.
    repeat match goal with
      | OK : ok_state _ _ ?s, H : args_wires _ ?s = inl _ |- _ =>
        generalize (args_wires_correct OK H); clear H; intros H; hsplit
      | OK : ok_state _ _ _, H : localv_set _ _ _ = inl _ |- _ =>
        apply (localv_set_correct OK) in H; destruct H as (? & ? & ? & ? & ?); hsplit
      | OK: ok_state _ _ ?s, H : add_gate_unsafe _ _ ?s = inl _ |- _ =>
        generalize (add_gate_correct OK H); clear H; intros H; hsplit
      | H : merror_globv_get _ _ = inl _ |- _ => apply merror_globv_get_correct in H
      end.
    simpl in *; split.
    apply localv_set_ok with st4 (Some None); auto.
     rw; move: (ok_twire OK); lia.
    destruct st'; simpl in *; rw; f_equal.
    by move: H => [_ [_ /=]].
    split; first by eauto using incr_state_trans.
    exists [:: ge1; ge0; ge]; split; first by rw; reflexivity.
    eexists _, _, _, _, _, _.
    split; first reflexivity.
    split.
     by apply (localv_conn_list_all_lt H0 H10).
    split.
     have: incr_state st0 st'; eauto using incr_state_trans.
     move=> [T _]; apply (localv_conn_list_m T); eassumption.
    split.
     have: incr_state st1 st'; eauto using incr_state_trans.
     move=> [T1 [T2 T3]].
     move: H2; rw => H2.
     apply is_renamed_m with (st_localv st1); last by eassumption.
     by move: T1; rw; apply.
    split; first eassumption.
    split; first eassumption.
    split.
     by move: H27; rw; rewrite -!N.add_1_r -N.add_assoc /=; apply.
    split.
     by move: H29; rw; rewrite -!N.add_1_r -!N.add_assoc /=; apply.
    split; first reflexivity.
    by rw.
  - (* phi *)
    intros H; mstate_bind.
    apply bdt_ren_correct in H0; hsplit.
    destruct x0 as [ty gn]; apply (proc_phi_conds_correct OK) in H1; hsplit.
    apply (localv_set_correct H1) in H; hsplit; simpl in *.
    split.
     apply localv_set_ok with st1 (Some (Some ty)); auto.
      move: (ok_twire OK); rw; rewrite (ok_wire H1) H5 sizeN_app (ok_wire OK); lia.
     destruct st'; simpl in *; rw; f_equal.
     by move: H => [_ [_ <-]].
    split; first by eauto using incr_state_trans.
    exists body; split; first by rw.
    exists x, ty; split; first by move: H => [_ [? _]].
    split.
     have: incr_state st st' by eauto using incr_state_trans.
     move=> [Xlocal [Xmon ->]].
     by apply is_renamed_m with (st_localv st).
    split; first by rw.
    split.
     apply proc_phi_spec_m with (st_localv st1) => //.
     by move: H => [? _].
    rewrite /is_localv H13 PTree.gss (ok_wire H1) H5 sizeN_app (ok_wire OK).
    f_equal; f_equal; lia.
Qed.

Lemma proc_code_correct {pfx pos body st st'} :
  ok_state pfx pos st →
  proc_code pos body st = inl (tt, st') →
  ok_state pfx (sizeN body + pos) st' ∧
  incr_state st st' ∧
  ∃ body',
  st_code st' = body' ++ st_code st ∧
  proc_code_spec (st_condv st') (st_localv st') pos body (st_wire st)
                 (st_globv st) (seq.rev body') (st_globv st').
Proof.
  revert pos st st'. elim body; clear body.
  - intros pos st st' OK H; apply inl_eq, pair_eq in H. destruct H as [_ <-].
    simpl. eauto 9 using incr_state_refl, app_nil_l.
  - intros ge body IH pos st st' OK.
    simpl. intros REC; mstate_bind. hsplit.
    match goal with
    | H : proc_instr _ _ _ _ = inl _ |- _ =>
      destruct (proc_instr_correct OK H) as (OK' & INCR & body' & Hbody' & Hinstr)
    end.
    rewrite N.add_1_r in REC.
    specialize (IH _ _ _ OK' REC).
    destruct IH as (OK'' & INCR' & body'' & Hbody'' & IH).
    rewrite <- N.add_succ_comm in OK''.
    apply (conj OK'').
    split. eauto using incr_state_trans.
    exists (body'' ++ body'). split.
    rewrite Hbody'' Hbody'. apply app_assoc.
    eexists _, _, _.
    split. apply seq.rev_cat.
    split.
    move: INCR'; rewrite /incr_state; move => [I1 [I2 I3]]; rewrite I3.
    eapply proc_instr_spec_m. 3: rewrite seq.revK(*_involutive*); eassumption. 
assumption.
assumption.
    rewrite -> (ok_wire OK), N.add_1_r. rewrite sizeN_rev.
    rewrite -> (ok_wire OK'), Hbody', sizeN_app, (N.add_comm (sizeN body')), N.add_assoc in IH.
    exact IH.
Qed.

Lemma proc_outputs_correct gm outs conn :
  proc_outputs gm outs = inl conn →
  proc_outputs_spec gm outs conn.
Proof.
  revert conn; elim outs; clear.
  intros co H; apply inl_eq, Logic.eq_sym in H; exact H.
  intros ((x, o), ?) outs IH conn.
  unfold proc_outputs. fold (proc_outputs gm outs).
  unfold globv_getbyte, merror_globv_get.
  intros H. mstate_bind. subst.
  destruct (PTree.get _ _) eqn: K; mstate_bind; subst.
  eexists _, _.
  apply (conj K). eauto.
Qed.

Lemma translate_circuit_correct {pfx ni ic code outs st circ st'} :
  ok_state pfx 0 st →
  translate_circuit ni ic code outs st = inl (circ, st') →
  ok_state pfx (sizeN code) st' ∧
  incr_state st st' ∧
  ∃ conn body',
  proc_outputs_spec (st_globv st') outs conn ∧
  st_code st' = body' ++ st_code st ∧
  proc_code_spec (st_condv st') (st_localv st') 0 code
         (st_wire st) (st_globv st) (seq.rev body') (st_globv st') ∧
  circ = {|  inputs := ni ; initconsts := ic ; gates := seq.rev (st_code st') ; outputs := conn |}.
Proof.
  intros OK.
  unfold translate_circuit.
  intros; mstate_bind; hsplit.
  repeat
  match goal with
  | H : proc_code _ _ _ = inl _ |- _ =>
    generalize (proc_code_correct OK H); clear H; intros H
  | H : proc_outputs _ _ = inl _ |- _ => apply proc_outputs_correct in H
  end.
  unfold get_code in *. mstate_bind. hsplit.
  rewrite -> N.add_0_r in *.
  eauto 8.
Qed.

Lemma add_inputs_correct n ins gm gm' :
  add_inputs n ins gm = inl gm' →
  add_inputs_spec n ins gm gm'.
Proof.
  revert n gm gm'. elim ins; clear.
  intros ? ? ? H; apply inl_eq, Logic.eq_sym in H. exact H.
  intros ((x, o), ?) ins IH n gm gm'.
  simpl. unfold merror_globv_upd_at, merror_globv_get.
  intros H; mstate_bind. destruct (PTree.get _ gm ) eqn: ?; mstate_bind. subst.
  eauto.
Qed.

Lemma add_inputs_spec_stack n ins gm gm' :
  add_inputs_spec n ins gm gm' →
  PTree.get xH gm' = PTree.get xH gm.
Proof.
  revert n gm gm'. elim ins; clear.
  - intros n ? ? ->. reflexivity.
  - intros ((x, o), ?) m IH n gm gm' (c & Hc & REC).
    specialize (IH _ _ _ REC).
    rewrite IH. clear IH.
    apply Maps.PTree.gso. Psatz.lia.
Qed.

Opaque N.add.
Opaque takeN_dflt dropN.

Lemma translate_function_correct gs f tf :
  translate_function gs f = inl tf →
  ∃ ssz gm condv localv body' globv conn,
    ssz = Int.repr (ValCirc.fn_stacksize f) ∧
    (0 <= ValCirc.fn_stacksize f <= Int.max_unsigned)%Z ∧
    add_inputs_spec 0 (ValCirc.fn_inputs f)
                    (init_globmap (ValCirc.fn_stacksize f) 3 gs) gm ∧
    wire_of_condition_wires (ValCirc.fn_conditions f) = Some condv ∧
    proc_code_spec condv localv 0
                   (ValCirc.fn_body f) (2 + sizeN_globs gs) gm body'
                   globv ∧
    proc_outputs_spec globv (ValCirc.fn_outputs f) conn ∧
  tf = {|
    fn_inputs := ValCirc.fn_inputs f;
    fn_outputs := seq.map snd (ValCirc.fn_outputs f);
    fn_stacksize := ssz;
    fn_code := {|
                inputs := 8 * sizeN (ValCirc.fn_inputs f);
                initconsts := initmem_stack ssz :: globs_initdata gs;
                gates := body';
                outputs := conn |} |}.
Proof.
  unfold translate_function, init_state.
  intros H; mstate_bind. subst.
  match goal with H : appcontext [(if _ <=? _ then _ else _)%Z] |- _ => revert H end.
  case Z.leb_spec. 2: intros _; apply inr_inl. intros LE.
  case Z.leb_spec. 2: intros _; apply inr_inl. intros LE'.
  intros X; apply inl_eq in X. subst.
  match goal with H : add_inputs _ _ _ = _ |- _ => apply add_inputs_correct in H end.
  destruct (wire_of_condition_wires _) eqn: H; mstate_bind. subst.
  match goal with H : translate_circuit _ _ _ _ ?st = inl ?q |- _ =>
                  destruct q;
                  let OK := fresh "OK" in
                  assert (ok_state (2 + sizeN_globs gs) 0 st) as OK;
                  [| generalize (translate_circuit_correct OK H); clear OK H; intros H ]
  end.
  clear. split. simpl. rewrite -> N.add_0_r. reflexivity.
simpl. lia.
  intros w oty gn H. simpl in H. unfold is_localv in H. rewrite Maps.PTree.gempty in H. discriminate.
by move => a1 a2 t1 t2 b1 b2 Ha; rewrite /is_localv /= !PTree.gempty.
  unfold incr_state in *.
  hsplit. simpl in *. rewrite -> app_nil_r in *. subst.
  eexists _, _, _, _, _, _, _.
  split. reflexivity.
  split. exact (conj LE LE').
  split. eassumption.
  split. reflexivity.
  split. eassumption. 
  split. eassumption.
  f_equal.
Qed.

Lemma proc_outputs_spec_size gm outs conn :
  proc_outputs_spec gm outs conn →
  sizeN conn = 8 * sizeN outs.
Proof.
  rewrite ! sizeN_nlen.
  revert conn. elim outs; clear.
  intros ? ->. reflexivity.
  intros ((x, o), ?) outs IH conn (c & co & Hc & -> & REC).
  specialize (IH _ REC).
  rewrite -> ValCirc.nlen_cons, ValCirc.nlen_app.
  unfold ValCirc.nlen at 1.
  rewrite -> ssrlib.lengthE, size_takeN_dflt, Nnat.N2Nat.id, <- N.add_1_l, N.mul_add_distr_l.
  f_equal. exact IH.
Qed.





Section SIMULATION.

Context (p: ValCirc.program) (p': program).
Context (TR': translate_program p = Errors.OK p').

Let gsT : { gs : list (ident * option bytes)
          | collect_globals nil (prog_defs p) = Some gs }.
Proof.
  revert TR'. unfold translate_program.
  destruct (collect_globals _) as [ gs | ]. intros _; exists gs; reflexivity.
  abstract discriminate.
Qed.

Let gs := proj1_sig gsT.
Let gsE := proj2_sig gsT.
Lemma TR : transform_partial_program (translate_fundef gs) p = Errors.OK p'.
Proof.
  revert TR'. unfold translate_program.
  rewrite gsE. exact id.
Qed.

Lemma collect_globals_transf :
  collect_globals nil (prog_defs p') = Some gs.
Proof.
  unfold gs. rewrite <- gsE.
  generalize TR. clear.
  unfold transform_partial_program, transform_partial_program2.
  intros H. apply Errors.bind_inversion in H.
  destruct H as (defs' & Hdefs & H). inv H. simpl.
  move: [::]. revert Hdefs.
  generalize (prog_defs p). intros defs. revert defs'. 
  elim defs; clear.
   intros ? H; inv H; reflexivity.
  intros (n, [ fd | gv ]) defs IH defs' H; simpl in H.
   destruct (translate_fundef _ _) as [ tf | msg ] eqn: Htf. 2: discriminate.
   apply Errors.bind_inversion in H. destruct H as (defs'' & Hdefs' & H).
   inv H.
   intro acc; simpl.
   apply IH; auto.
  apply Errors.bind_inversion in H. destruct H as (defs'' & Hdefs' & H).
  inv H. simpl.
  destruct (gvar_volatile _). auto.
  unfold initmem_of_globvar; simpl.
  destruct (bytes_of_initdata_list (gvar_init gv)) => //.
  intro H.
  rewrite IH; auto.
Qed.

Definition match_io sp (io: option (slot * Values.val)) (io': option Values.val) : Prop :=
  match io with
  | None => io' = None
  | Some ((x, _), v) => (∀ o, Values.Vptr x o ≠ sp) ∧ io' = Some v
  end.

Definition match_outval (io io': option (Values.val * ident)) : Prop :=
  match io with
  | None => io' = None
  | Some (v, s) => ∃ v', Values.Val.lessdef v v' ∧ io' = Some (v', s)
  end.

(** There are three distinct kinds of entries in (HLCirc) grids.
     1. bit-strings representing normal CompCert values (of a given type)
     2. single-bit entries representing guards.
     3. bit-strings representing (a snapshot of) a global variable
*)
Definition match_val (oty: option typ) (v: Values.val) (bs: bits) :=
 if oty is Some ty
 then match_val_ty v bs
 else bs = [:: ValCirc.val_is_true v].

Record match_block (m: Mem.mem) (b: Values.block) (sz: Z) (grd: grid) (c: connector) : Prop :=
  { mb_valid: Mem.valid_block m b
  ; mb_bounds: ∀ o, Mem.perm m b o Cur Readable → (0 <= o < sz)%Z
  ; mb_size: sizeN c <= 8 * Z.to_N Int.max_unsigned
  ; mb_load: ∃ mbs bs',
      Mem.loadbytes m b 0 sz = Some mbs ∧
      conn_eval grd c = Some (bits_of_bytes bs') ∧
      match_bytes mbs bs'
  }.

Arguments mb_valid [m b] _ _ _ _.
Arguments mb_bounds [m b sz grd c] _ _ _.
Arguments mb_size [m b sz grd c] _ _.
Arguments mb_load [m b sz grd c] _.

Definition match_grid_local (localv: PTree.t localv_info)
       (g: ValCirc.grid) (g': grid) : Prop :=
  ∀ x oty gn,
    is_localv localv x (Some oty) gn →
    x < sizeN g →
    ∃ v',
    read_wire g' oty gn = Some v' ∧
    match_val oty (ValCirc.read_wire g x) v'.

Definition match_grid_global
       (globv: PTree.t globv_info)
       (sp: Values.val) (ssz: Z)
       (m: Mem.mem) (g': grid) : Prop :=
  ∃ bstk,
    sp = Values.Vptr bstk Int.zero
    ∧ (∀ c, PTree.get xH globv = Some c  → match_block m bstk ssz g' c)
    ∧ ∀ g c, PTree.get (Pos.succ g) globv = Some c →
             ∃ b gv, match_block m b (Genv.init_data_list_size (gvar_init gv)) g' c
                     ∧ Genv.block_is_volatile (Genv.globalenv p) b = false
                     ∧ Genv.find_symbol (Genv.globalenv p) g = Some b
                     ∧ b <> bstk
                     ∧ Genv.find_var_info (Genv.globalenv p) b = Some gv.

Definition is_global_block (g: positive) :
  { n | g = Pos.succ n } + { g = xH }.
Proof.
  refine match g with
         | xH => inright Logic.eq_refl
         | xI n => inleft (exist _ (xO n) _)
         | xO n => inleft (exist _ (Pos.pred_double n) _)
         end.
  abstract Psatz.lia.
  abstract (symmetry; apply (Pos.succ_pred (xO n)); Psatz.lia).
Defined.

Remark is_global_block_succ (n: positive) :
  is_global_block (Pos.succ n) = inleft (exist _ n Logic.eq_refl).
Proof.
  destruct is_global_block as [ (n' & H) | K ]. 2: exfalso; Psatz.lia.
  f_equal. generalize (Pos.succ_inj _ _ H). intros <-. f_equal.
  apply Eqdep_dec.UIP_dec, Pos.eq_dec.
Qed.

Lemma match_grid_block {globv sp ssz m g'} :
  match_grid_global globv sp ssz m g' →
  ∀ g c,
    PTree.get g globv = Some c →
    ∃ b sz,
      match_block m b sz g' c ∧
      match is_global_block g with
      | inleft (exist n Hg) => ∃ gv,
            Genv.find_symbol (Genv.globalenv p) n = Some b ∧
            Genv.find_var_info (Genv.globalenv p) b = Some gv ∧
            sz = Genv.init_data_list_size (gvar_init gv)
      | inright Hg => sp = Values.Vptr b Int.zero ∧ sz = ssz
      end.
Proof.
intros (bstk & Hsp & Mstk & Mglob) g c H.
destruct (is_global_block _) as [ (n & ->) | -> ].
 destruct (Mglob n c H) as (b & gv & Hmb & Hvol & Hfind & Hbstk & Hinfo).
 eauto 7.
eauto 6.
Qed.

Definition match_grid_const (g': grid) : Prop :=
  onthN g' N0 = Some (false :: true :: nil).

Definition match_grid
       (localv: PTree.t localv_info) (globv: PTree.t globv_info)
       (sp: Values.val) (ssz: Z)
       (g: ValCirc.grid) (m: Mem.mem) (g': grid) : Prop :=
  match_grid_local localv g g' ∧ match_grid_global globv sp ssz m g' ∧ match_grid_const g'.

Lemma match_grid_nonempty lv gv sp ssz g m g' :
  match_grid lv gv sp ssz g m g' →
  sizeN g' ≠ 0.
Proof.
  intros (_ & _ & H).
  destruct g'. discriminate. simpl; Psatz.lia.
Qed.

Lemma loadbytes_storebytes_o m ps os bs m' pl ol n :
  pl ≠ ps →
  Mem.storebytes m ps os bs = Some m' →
  Mem.loadbytes m' pl ol n = Mem.loadbytes m pl ol n.
Proof.
  move=> ne hs.
  assert (n <= 0 ∨ n >= 0)%Z as D by Psatz.lia.
  case: D => hn.
  - move: (λ m, Mem.loadbytes_empty m pl ol n hn) => X.
    by rewrite ! X.
  - apply (Mem.loadbytes_storebytes_other _ ps os bs). eassumption. exact hn.
    by left.
Qed.

Definition match_state (s: ValCirc.state) (s': HLCirc.state) : Prop :=
  match s with
  | ValCirc.InitState f m =>
    ∃ f',
    translate_function gs f = inl f' ∧
    Genv.init_mem p = Some m ∧
    s' = InitState f' (globs_initdata gs)
  | ValCirc.InputState None ins sp ssz cw body m outs =>
    ∃ condv localv globvc globvi globvf nin inp grid body' oc,
    wire_of_condition_wires cw = Some condv ∧
    nin * 8 = sizeN inp ∧
    add_inputs_spec nin ins globvc globvi ∧
    proc_code_spec condv localv 0 body (1 + sizeN grid) globvi body' globvf ∧
    match_grid_global globvc sp ssz m (fill_grid inp grid) ∧
    proc_outputs_spec globvf outs oc ∧
    s' = InputState None (map snd ins) inp grid body' (map snd outs) oc
  | ValCirc.InputState (Some (x,o,v)) ins sp ssz cw body m outs =>
    ∃ ident condv localv globvc globvi globvf nin inp grid body' oc,
    wire_of_condition_wires cw = Some condv ∧
    nin * 8 = sizeN inp ∧
    add_inputs_spec nin ((x,o,ident)::ins) globvc globvi ∧
    proc_code_spec condv localv 0 body (1 + sizeN grid) globvi body' globvf ∧
    match_grid_global globvc sp ssz m (fill_grid (inp++bits_of_byte (byte_of_input_val v)) grid) ∧
    proc_outputs_spec globvf outs oc ∧
    s' = InputState (Some v) (map snd ins) inp grid body' (map snd outs) oc
  | ValCirc.InputFenceState sp ssz cw body m outs =>
    ∃ condv localv globvi globvf inp grid body' oc,
    wire_of_condition_wires cw = Some condv ∧
    proc_code_spec condv localv 0 body (1 + sizeN grid) globvi body' globvf ∧
    match_grid localv globvi sp ssz nil m (fill_grid inp grid) ∧
    proc_outputs_spec globvf outs oc ∧
    s' = InputFenceState false inp grid body' (map snd outs) oc
  | ValCirc.PostInputState sp ssz cw body m outs =>
    ∃ condv localv globvi globvf inp grid body' oc,
    wire_of_condition_wires cw = Some condv ∧
    proc_code_spec condv localv 0 body (1 + sizeN grid) globvi body' globvf ∧
    match_grid localv globvi sp ssz nil m (fill_grid inp grid) ∧
    proc_outputs_spec globvf outs oc ∧
    s' = InputFenceState true inp grid body' (map snd outs) oc
  | ValCirc.State sp ssz cw body g m outs =>
    ∃ condv localv globvi globvf body' oc g',
    wire_of_condition_wires cw = Some condv ∧
    proc_code_spec condv localv (sizeN g) body (N.pred (sizeN g')) globvi body' globvf ∧
    match_grid localv globvi sp ssz g m g' ∧
    proc_outputs_spec globvf outs oc ∧
    s' = State body' (map snd outs) oc g'
  | ValCirc.OutputFenceState sp ssz m outs =>
    ∃ globv oc g',
    match_grid_const g' ∧
    match_grid_global globv sp ssz m g' ∧
    proc_outputs_spec globv outs oc ∧
    s' = OutputFenceState false (map snd outs) oc g'
  | ValCirc.PreOutputState sp ssz m outs =>
    ∃ globv oc g',
    match_grid_const g' ∧
    match_grid_global globv sp ssz m g' ∧
    proc_outputs_spec globv outs oc ∧
    s' = OutputFenceState true (map snd outs) oc g'
  | ValCirc.OutputState io outs sp ssz m =>
    ∃ globv oc g' io',
    match_outval io io' ∧
    match_grid_const g' ∧
    match_grid_global globv sp ssz m g' ∧
    proc_outputs_spec globv outs oc ∧
    s' = OutputState io' (map snd outs) oc g'
  | ValCirc.FinishingState _ _ _ => s' = FinishingState
  | ValCirc.FinalState => s' = FinalState
  end.

Lemma bits_of_byte_sizeN b : sizeN (bits_of_byte b) = 8.
Proof.
  apply N.eqb_eq. revert b.
  apply FOR_ALL_BYTE.for_all_byte_correct.
  vm_compute.
  reflexivity.
Qed.

Lemma bits_of_int32_sizeN i : sizeN (bits_of_int32 i) = 32.
  unfold bits_of_int32. simpl.
  rewrite -> ! sizeN_app, ! bits_of_byte_sizeN.
  vm_compute.
  reflexivity.
Qed.

Definition comparison_dec (c c': Datatypes.comparison) : { c = c' } + { c ≠ c' }.
Proof.
  refine
  match c, c' with
  | Eq, Eq
  | Lt, Lt
  | Gt, Gt => left Logic.eq_refl
  | _, _ => right _
  end; abstract exact (λ K, let 'Logic.eq_refl := K in I).
Defined.

Definition int_eq (i j: int) :
  Int.intval i = Int.intval j → i = j.
Proof.
  destruct i as [i Hi], j as [j Hj]. simpl. intros ->.
  cut (Hi = Hj). congruence.
  destruct Hj as [J1 J2], Hi as [I1 I2].
  apply (f_equal2); apply Eqdep_dec.UIP_dec, comparison_dec.
Qed.

Lemma intval_repr x :
  Int.intval (Int.repr x) = Int.Z_mod_modulus x.
Proof. reflexivity. Qed.

Lemma N2Z_inj_shiftl x y :
  Z.of_N (N.shiftl x y) = Z.shiftl (Z.of_N x) (Z.of_N y).
Proof.
  destruct x as [ | x ]. rewrite -> N.shiftl_0_l, Z.shiftl_0_l. reflexivity.
  destruct y as [ | y ]. reflexivity.
  simpl. clear.
  elim y using Pos.peano_ind. reflexivity.
  intros p IH. rewrite -> ! Pos.iter_succ, <- IH. reflexivity.
Qed.

Definition N_of_opos (p: option positive) :=
  match p with Some x => Npos x | None => 0 end.

Lemma Npos_xO q : Npos q~0 = 2 * Npos q.
Proof. Psatz.lia. Qed.

Lemma Npos_xI q : Npos q~1 = 2 * Npos q + 1.
Proof. Psatz.lia. Qed.

Lemma Nadd_eq_0 a b : 0 = a + b → a = 0 ∧ b = 0.
Proof. Psatz.lia. Qed.

Opaque N.shiftl.

Lemma pos_of_bits_app b b' :
  N_of_opos (pos_of_bits (b ++ b')) = N.shiftl (N_of_opos (pos_of_bits b')) (sizeN b) + N_of_opos (pos_of_bits b).
Proof.
  elim b; clear.
  rewrite N.add_0_r. symmetry. apply N.shiftl_0_r.
  intros x b IH. simpl.
  destruct (pos_of_bits (_ ++ _)) eqn: E. simpl in IH.
  destruct x; simpl.
  rewrite -> Npos_xI, IH. clear.
  rewrite N.shiftl_succ_r. rewrite -> N.double_spec at 1.
  destruct (pos_of_bits b); simpl; Psatz.lia.
  rewrite -> Npos_xO, IH. clear.
  rewrite N.shiftl_succ_r. rewrite -> N.double_spec at 1.
  destruct (pos_of_bits b); simpl; Psatz.lia.

  apply Nadd_eq_0 in IH. destruct IH as [ IH IH']. destruct (pos_of_bits b). discriminate. clear IH'.
  apply N.shiftl_eq_0_iff in IH. rewrite IH. clear.
  destruct x; simpl; now rewrite N.shiftl_0_l.
Qed.

Opaque Int.Z_mod_modulus.

Lemma pos_of_bits_of_byte b :
  Z.of_N (N_of_opos (pos_of_bits (bits_of_byte b))) = Byte.unsigned b.
Proof.
  apply Z.eqb_eq. revert b.
  apply FOR_ALL_BYTE.for_all_byte_correct.
  vm_compute.
  reflexivity.
Qed.

Lemma proc_op_spec_gate_eval localv globv sp ssz g m g' op args ge:
  op ≠ Op.Omove →
  all_lt (sizeN g) args →
  match_grid localv globv sp ssz g m g' →
  proc_op_spec localv op args ge →
  ∃ xbits : bits,
    gate_eval (gateInfo (gate ge)) g' (conn ge) = Some xbits ∧
    wires_of_type (Op.type_of_operation op).2 = sizeN xbits ∧
    match_val_ty
              (RTLC.eval_operation (Genv.globalenv p) sp op (ValCirc.read_wires g args) m)
              xbits.
Proof.
  intros NotMove LT M (n & wargs & Hop & Hargs & Hout & Hin & ->).
  destruct M as (ML & MG & MC).

  assert (∃ argbits, conn_eval g' wargs = Some (flatten argbits) ∧
                     Forall2 match_val_ty (ValCirc.read_wires g args) argbits) as H.
  {
    clear - Hargs ML LT. revert wargs Hargs LT.
    elim args; clear - ML.
    - intros ? -> _. exists nil. apply (conj Logic.eq_refl). constructor.
    - intros a args IH ? (w & wargs & -> & Haw & REC) LT.
      specialize (IH _ REC (λ n H, LT n (or_intror _ H))).
      destruct IH as (argbits & EV & M).
      destruct Haw as (oty & n & H & Hw).
      specialize (ML _ _ _ H (LT _ (or_introl _ Logic.eq_refl))).
      destruct ML as (v' & Ev' & Mv').
      eexists (v' :: argbits). split.
      simpl. apply conn_eval_cat.
      destruct oty; subst w; exact Ev'.
      exact EV.
      constructor; auto.
  }
  clear Hargs.
  destruct H as (argbits & Hargbits & MA).
  eexists. split.
  unfold gate_eval. simpl. rewrite Hargbits. reflexivity.
  split.
  rewrite <- Hout. symmetry.
  apply sizeN_takeN_dflt.

  set (vargs := ValCirc.read_wires _ _). fold vargs in MA.

  apply (@gate_of_operation_correct op n vargs (seq.flatten argbits)); auto.
  elim MA.
   simpl; constructor.
  simpl; constructor; auto.
Qed.

Lemma match_block_add_right m bstk ssz g c v:
 match_block m bstk ssz g c -> match_block m bstk ssz (seq.rcons g v) c.
Proof. 
intros [Hvb Hbnd Hsize (mbs & bs & Hload & Heval & Hmbs)]; constructor; auto.
exists mbs, bs; auto.
split; [assumption|split; [|assumption]].
apply conn_eval_rcons; assumption.
Qed.

Lemma match_grid_global_add_right globv sp ssz m g v:
  match_grid_global globv sp ssz m g ->
  match_grid_global globv sp ssz m (seq.rcons g v).
Proof.
intros (bstk & Hsp & Hstk & Hgv).
exists bstk; split; [assumption| split].
 intros c H; pose (Hstk c H).
 apply match_block_add_right; assumption.
intros gv c H.
destruct (Hgv gv c H) as (b & gvinfo & Hmb & Hvol & Hfind & Hsp' & Hgvinfo).
exists b, gvinfo; split.
 apply match_block_add_right; assumption.
auto.
Qed.

Lemma match_grid_global_add_cat globv sp ssz m g g':
 match_grid_global globv sp ssz m g -> match_grid_global globv sp ssz m (g++g').
Proof.
elim: g' g.
 by move=> g H; rewrite cats0.
move=> x xs IH g H.
rewrite -[x::xs]cat1s catA cats1; apply IH.
by apply match_grid_global_add_right.
Qed.

Lemma conn_eval_conn_ty ty v v':
  match_val (Some ty) v v' ->
  wires_of_type ty = sizeN v' ->
  conn_eval [:: v'] (conn_ty ty 0) = Some v'.
Proof.
have HH: sizeN v' <= sizeN v' by lia.
by rewrite /conn_ty /wires_of_type; move: ty => [| | | | |] /=;
   move: v => [|i|i|f|f|b o] //=;
   move=> _ ->; rewrite conn_eval_conn_new //= takeN_all //.
Qed.

Lemma read_wire_last_match g' oty v v':
  wires_of_oty oty = sizeN v' ->
  match_val oty v v' ->
  read_wire (rcons g' v') oty (sizeN g') = Some v'.
Proof.
move: oty => [ty|] Hsz M.
 by rewrite read_wire_last read_wire_first.
simpl in *; subst.
by rewrite read_wire_last /read_wire /conn_eval.
Qed.

Lemma match_grid_add_local localv globv sp ssz g m g' oty' v v' :
  is_localv localv (sizeN g) (Some oty') (sizeN g') →
  wires_of_oty oty' = sizeN v' →
  match_val oty' v v' →
  match_grid localv globv sp ssz g m g' →
  match_grid localv globv sp ssz (g ++ v :: nil) m (seq.rcons g' v').
Proof.
move=> Hlocalv Hsz_v' Mv [Mlocal [Mglobal Mconst]].
repeat split.
- (* local *)
move=> w oty gn Hw Hsz.
move: Hsz; rewrite sizeN_size size_cat Nat2N.inj_add /= -sizeN_size.
rewrite N.add_1_r N.lt_succ_r N.lt_eq_cases; move => [Hsz|Hsz].
 move: (Mlocal w oty gn Hw Hsz) => [bs [Hread Hmatch]].
 exists bs; split.
  rewrite read_wire_rcons //.
  by eauto using read_wire_lt.
 rewrite /ValCirc.read_wire ValCirc.nth_app.
 case: (ifP _); first by [].
 by move: Hsz; rewrite sizeN_nlen N.ltb_nlt.
move: Hw; rewrite Hsz => Hw.
move: (is_localv_inj Hw Hlocalv) => [[Ety] Egn]; subst.
exists v'; split.
 by eapply read_wire_last_match; eauto.
rewrite /ValCirc.read_wire ValCirc.nth_skip -sizeN_nlen; last reflexivity.
rewrite N.sub_diag.
by move: Mv; clear; destruct oty.
- (* global *)
move: Mglobal => [bsp [Esp [Msp Mglob]]].
exists bsp; split; [assumption| split].
 by move=> c Hc; apply match_block_add_right, Msp.
move=> x c Hc; move: (Mglob x c Hc) => [b [gv [Mb [Hvol [Hb [Hsp Hgv]]]]]].
exists b, gv; split.
 by apply match_block_add_right, Mb.
repeat split; assumption.
- (* const *)
by rewrite /match_grid_const -cats1; apply onthN_isS_cat, Mconst.
Qed.

Lemma match_grid_add_right localv globv sp ssz g m g' v :
  match_grid localv globv sp ssz g m g' →
  match_grid localv globv sp ssz g m (seq.rcons g' v).
Proof.
  intros (ML & MG & MC).
  split; [ | split ].
  - (* Local *)
    intros w oty gn L LT.
    destruct (ML _ _ _ L LT) as (v' & Hv' & M).
    exists v'. split. rewrite read_wire_rcons. exact Hv'. eauto using read_wire_lt.
    exact M.
  - (* Global *)
    apply match_grid_global_add_right; assumption.
  - (* Const *)
    destruct g'. discriminate. exact MC.
Qed.

Lemma eventval_valid_transf {ev} :
  Events.eventval_valid (Genv.globalenv p) ev →
  Events.eventval_valid (Genv.globalenv p') ev.
Proof.
  destruct ev; auto.
  simpl. intros <-.
  eapply Genv.public_symbol_transf_partial, TR.
Qed.

Lemma eventval_match_transf {ev ty v v'} :
  Values.Val.lessdef v v' →
  Events.eventval_match (Genv.globalenv p) ev ty v →
  Events.eventval_match (Genv.globalenv p') ev ty v'.
Proof.
  unfold translate_program.
  intros LD.
  intros H; inv H; inv LD; constructor.
  simpl. erewrite Genv.public_symbol_transf_partial by apply TR. assumption.
  simpl. erewrite Genv.find_symbol_transf_partial by apply TR. assumption.
Qed.

Lemma N_div_mod_full a b :
  b ≠ 0 →
  let (q, r) := N.div_eucl a b in a = b * q + r ∧ r < b.
Proof.
  intros NZ.
  generalize (N.div_eucl_spec a b).
  generalize (N.mod_lt a b NZ). unfold N.modulo.
  destruct (N.div_eucl _ _); simpl; auto.
Qed.

Opaque N.lt.

Lemma pointers_need_no_more_than_32bits ϰ (c: connector) :
  sizeN c <= 8*N_of_Z Int.max_unsigned →
  N.log2 (sizeN_chunk ϰ) + size2idxbits (8 * sizeN_chunk ϰ) (sizeN c) <= 32.
Proof.
clear.
set (n := sizeN c). simpl. intros LE.
unfold size2idxbits.
set (s := sizeN_chunk _).
assert (1 <= s ∧ s <= 16) as R by (unfold s; split; apply N.leb_le; destruct ϰ; reflexivity).
set (m := n / _).
move: (N.le_gt_cases m 0) => [Hm|Hm].
 rewrite N.log2_up_nonpos // N.add_0_r.
 transitivity (N.log2 16).
  apply N.log2_le_mono; lia.
 by vm_compute.
have BND: N.log2 4294967295 = 31 by reflexivity.
have H1: N.log2 (s*m) <= 31.
 rewrite /m -BND.
 apply N.log2_le_mono. 
 rewrite -N.div_div //; last lia.
 transitivity (n/8).
  apply N.mul_div_le; lia.
 rewrite (N.mul_le_mono_pos_l _ _ 8) //. 
 transitivity n.
  apply N.mul_div_le; lia.
 by [].
transitivity (N.log2 s + N.log2 m + 1).
 move: (N.le_log2_up_succ_log2 m); lia.
transitivity (N.log2 (s*m) + 1).
rewrite -N.add_le_mono_r.
apply N.log2_mul_below; lia.
lia.
Qed.

(*-------*)

Lemma init_globmap_stack ssz globs:
 PTree.get 1 (init_globmap ssz 3 globs) = Some (conn_new 2 0 (8*Z.to_N ssz)).
Proof.
move: 3; elim: globs => //.
move=> [v [vinit|]] globs IH n.
 rewrite PTree.gso; last by lia.
 by apply IH.
rewrite PTree.gro; last by lia.
by apply IH.
Qed.

Lemma match_grid_const_is_grid g':
  match_grid_const g' ->
  is_grid g'.
Proof.
intros H; inversion H; hsplit.
rewrite -> onthN_onth, onth_isS, seq.nth0 in H1; hsplit.
apply H1.
Qed.

Lemma loadbytes_isS_sizeN m b off len bs:
  Mem.loadbytes m b off len = Some bs -> sizeN bs = N_of_Z len.
Proof.
intros H; generalize (Mem.loadbytes_length _ _ _ _ _ H).
rewrite lengthE; unfold nat_of_Z; clear H.
rewrite <- Z_N_nat, size_sizeN; intros H; apply N2Nat.inj; assumption.
Qed.

(* auxiliary function *)
Definition get_initdata (l: seq (ident*option bytes)) (k:ident) :=
 if aget l k is Some (Some x)
 then Some x
 else None.

Lemma collect_globals_keys F V: forall (gdefs: seq (ident*globdef F V)) acc l,
 collect_globals acc gdefs = Some l ->
 map fst l = rev (map fst gdefs) ++ map fst acc.
Proof.
elim => //=.
 by move=> acc l [<-].
move=> [x [gx|gx]] gdefs IH acc l /=.
 by move=> H; rewrite (IH _ _ H) /= rev_cons -cats1 -catA.
case: (ifP _) => Hvol /=.
 by move=> H; rewrite (IH _ _ H) /= rev_cons -cats1 -catA.
case Hini: (initmem_of_globvar gx) => [xinit|]; last by [].
case: (ifP _) => Hsz /=; last by [].
by move=> H; rewrite (IH _ _ H) /= rev_cons -cats1 -catA.
Qed.

Lemma collect_globals_cat_isS F V: 
  forall (gdefs: seq (ident*globdef F V)) a1 a2 l,
    collect_globals (a1++a2) gdefs = Some l ->
    exists l', collect_globals a1 gdefs = Some l' /\ l = l' ++ a2.
Proof.
elim.
 by move=> a1 a2 l /= [<-]; exists a1.
move=> [x [gf|gx]] gdefs IH a1 a2 l /=.
 by move=> H; apply IH.
case: (ifP _) => Hvol.
 by move=> H; apply IH.
case Hinit: (initmem_of_globvar gx) => [xinit|]; last by [].
case: (ifP _) => Hsz; last by [].
rewrite -cat_cons => HH; case: (IH _ _ _ HH) => l' [H0 Hl'].
by exists l'.
Qed.

Lemma get_initdata_nil v: get_initdata [::] v = None.
Proof. by []. Qed.

Lemma get_initdata_consN l v v':
 get_initdata l v = None ->
 get_initdata ((v',None)::l) v = None.
Proof. by rewrite /get_initdata //=; case: (ifP _). Qed.

Lemma get_initdata_cat_lN l1 l2 v:
 get_initdata l2 v = None ->
 get_initdata (l1++l2) v = get_initdata l1 v.
Proof.
rewrite /get_initdata aget_cat.
by case: (aget _ _) => [[a|]|]; case: (aget _ _) => [[b|]|].
Qed.

Lemma collect_globals_prop F V v vinit:
  forall (gdefs: seq (ident*globdef F V)) acc l,
    collect_globals acc gdefs = Some l ->
    get_initdata acc v = None ->
    get_initdata l v = (Some vinit) ->
    exists gv l1 l2,
      gdefs = l1 ++ (v,Gvar gv):: l2
      /\ ~~ (v \in (map fst l2))
      /\ ~~ (gvar_volatile gv)
      /\ initmem_of_globvar gv = Some vinit
      /\ (Genv.init_data_list_size (gvar_init gv) <= Int.max_unsigned)%Z.
Proof.
move: (get_initdata_nil v) => Hnil.
elim.
 by move => acc l /= [<-] ->.
move=> [x [gx|gx]] gdefs IH acc l /= H Hacc Hget; move: H.
 rewrite -[_::_]cat0s => /collect_globals_cat_isS [l1 [H Hl]].
 move: Hget; rewrite Hl get_initdata_cat_lN; last by apply get_initdata_consN.
 move=> Hget.
 move: {IH H Hnil Hget} (IH _ _ H Hnil Hget) => [gx' [la [lb [Egs HH]]]].
 exists gx', ((x,Gfun gx)::la), lb; split => //=; f_equal; assumption.
case: (ifP _) => Hvol.
 rewrite -[_::_]cat0s => /collect_globals_cat_isS [l1 [H Hl]].
 move: Hget; rewrite Hl get_initdata_cat_lN; last by apply get_initdata_consN.
 move=> Hget.
 move: {IH H Hnil Hget} (IH _ _ H Hnil Hget) => [gx' [la [lb [Egs HH]]]].
 exists gx', ((x,Gvar gx)::la), lb; split => //=; f_equal; assumption.
case Hinit: (initmem_of_globvar gx) => [xinit|]; last by [].
case: (ifP _) => Hsz; last by [].
rewrite -[_::_]cat0s => /collect_globals_cat_isS [l1 [H Hl]].
move: Hget; rewrite Hl /get_initdata aget_cat.
case Al1: (aget l1 v) => [[vinit''|]|] => //=.
 move=> [[E]]; subst.
 have Hget1: get_initdata l1 v = Some vinit by rewrite /get_initdata Al1.
 move: (IH _ _ H Hnil Hget1) => [gx' [la [lb [Egs HH]]]].
 exists gx', ((x,Gvar gx)::la), lb; split => //=; f_equal; assumption.
case: (ifP _) => E; last first.
 by move: Hacc; rewrite /get_initdata; case: (aget acc v) => [[?|]|].
move=> [<-]; rewrite -(eqP E); exists gx, [::], gdefs.
split; first by [].
split.
 rewrite -mem_rev -[rev _]cats0 -[nil]/(map (@fst ident bytes) [::]).
 rewrite -(@collect_globals_keys _ _ gdefs [::] _ H).
 by apply aget_isN.
split; first by rewrite Hvol.
split; first by [].
by apply Z.leb_le.
Qed.

Definition grid_of_initdata globs := grid_of_globconsts (globs_initdata globs).

Definition mk_grid inbits ssz globs :=
  [:: [:: false; true]
    ; inbits
    ; bits_of_bytes (initmem_stack (Int.repr ssz)) ] ++ grid_of_initdata globs.

Lemma valid_block_alloc m b lo hi m' b':
 Mem.valid_block m b ->
 Mem.alloc m lo hi = (m',b') -> b <> b'.
Proof.
intros Hvalid Halloc Habsurd.
apply (Plt_ne _ _ Hvalid).
rewrite Habsurd; apply (Mem.alloc_result _ _ _ _ _ Halloc).
Qed.

Lemma match_block_alloc m lo hi m' newb b sz g c:
 Mem.alloc m lo hi = (m', newb) ->
 match_block m b sz g c -> 
 match_block m' b sz g c.
Proof.
intros Halloc H; destruct H as [Hvalid Hbnds Hsize (mbs & bs & Hload & Hconn & Hmbs)].
pose Hdiff := valid_block_alloc Hvalid Halloc.
constructor.
- eapply Mem.valid_block_alloc; eauto.
- intros o Hperm'; apply Hbnds; auto.
  eapply Mem.perm_alloc_4; eauto.
- assumption.
- exists mbs, bs; split; [| split; assumption].
  erewrite Mem.loadbytes_alloc_unchanged; eauto.
Qed.

Lemma alloc_valid_block_new m lo hi m' sp:
  Mem.alloc m lo hi = (m', sp) -> Mem.valid_block m' sp.
Proof.
intros H.
unfold Mem.valid_block.
rewrite -> (Mem.alloc_result _ _ _ _ _ H), (Mem.nextblock_alloc _ _ _ _ _ H).
apply Plt_succ.
Qed.

Lemma get_initdata_pos l v:
 get_initdata l v = (nth (v,None) l (find [fun x=>v==x.1] l)).2.
Proof.
elim: l => //=.
by move=> [x [y|]] l IH; rewrite /get_initdata /=; case: (ifP _).
Qed.

Lemma get_initdata_filter l v x:
 get_initdata l v = Some x ->
 get_initdata (filter [fun x=> x.2 != None] l) v = Some x.
Proof.
elim: l => //=.
by move=> [a [b|]] l; rewrite /get_initdata /= => IH; case: (ifP _).
Qed.

Lemma get_initdata_cons_other x xinit globs v:
 x <> v ->
 get_initdata ((x,xinit)::globs) v = get_initdata globs v.
Proof. by rewrite /get_initdata /= => E; case: (ifP _) => //= /eqP E2; elim: E. Qed.

Lemma get_initdata_cons_same x xinit globs:
 get_initdata ((x,xinit)::globs) x = xinit.
Proof. by rewrite /get_initdata /= eq_refl; case: xinit. Qed.


Lemma get_initdata_isN_globmap ssz n v globs:
 get_initdata globs v = None <-> (init_globmap ssz n globs) ! (Pos.succ v) = None.
Proof.
rewrite /get_initdata; elim: globs n.
 split => // _.
 rewrite PTree.gso; last by lia.
 by rewrite PTree.gempty.
move=> [x [xinit|]] globs IH n /=.
 case: (ifP _) => /=.
  move=> /eqP <-; split => //=.
  by rewrite PTree.gss.
 move/eqP => E; rewrite IH PTree.gso; first reflexivity.
 by move=> HH; apply E; apply Pos.succ_inj.
case: (ifP _) => /eqP E; split => //=. 
  by move=> _; rewrite E PTree.grs.
 rewrite IH PTree.gro; first by apply.
 by move=> HH; apply E; apply Pos.succ_inj.
rewrite IH PTree.gro; first by apply.
by move=> HH; apply E; apply Pos.succ_inj.
Qed.

Lemma init_globmap_conn v ssz globs c:
  PTree.get (Pos.succ v) (init_globmap ssz 3 globs) = Some c <->
  exists vinit,
   get_initdata globs v = Some vinit /\
   c = conn_new (3+n2N (find [fun x=>v==x.1] (filter [fun x=> x.2 != None] globs))) 0 (8*sizeN vinit).
Proof.
move: 3; elim: globs c.
 move=> c n.
 rewrite PTree.gso ?PTree.gempty; last by lia.
 split => //=.
 by move=> [vinit]; rewrite get_initdata_nil; move => [? _].
move=> [x [xinit|]] globs IH c n /=.
 case E: (v==x).
  rewrite (eqP E) PTree.gss; split.
   move=> [<-]; exists xinit; rewrite get_initdata_cons_same /= N.add_0_r.
   by split.
  rewrite get_initdata_cons_same; move => [vinit [[<-] ->]] /=.
  by rewrite N.add_0_r.
 rewrite PTree.gso; last first.
  by move=> H; move/negP: E; apply; apply/eqP; apply Pos.succ_inj.
 move: E; rewrite eq_sym => /eqP E.
 rewrite (IH _ _); split.
  move=> [vinit [Hget Hc]]; exists vinit.
  rewrite get_initdata_cons_other //; split; first assumption.
  rewrite Hc; f_equal.
  by rewrite Nat2N.inj_succ -!N.add_1_l N.add_assoc [1 + n]N.add_comm.
 move=> [vinit]; rewrite get_initdata_cons_other //.
 rewrite Nat2N.inj_succ -!N.add_1_l N.add_assoc [1 + n]N.add_comm. 
 move => [Hget Hc].
 by exists vinit; split.
case E: (v==x).
 rewrite (eqP E) get_initdata_cons_same PTree.grs; split => //.
 by move=> [vinit] [H _].
rewrite PTree.gro; last first. 
 by move=> H; move/negP: E; apply; apply/eqP; apply Pos.succ_inj.
rewrite get_initdata_cons_other; last first.
 move=> H; move/eqP: E; apply; rewrite H; reflexivity.
by rewrite IH.
Qed.

Lemma conn_eval_cat_conn_new a na b n pos sz:
 sizeN a = na ->
 conn_eval (a++b) (conn_new (na+n) pos sz)
 = conn_eval b (conn_new n pos sz).
Proof.
move=> <-; rewrite /conn_eval omap_all_oseq omap_all_oseq /wire_eval; f_equal.
rewrite /conn_new -map_comp -map_comp.
apply eq_map => w /=.
rewrite !nthN_nth nth_cat.
case: (ifP _).
 rewrite N2Nat.inj_add -size_sizeN => /ltP H; lia.
move=> _; f_equal.
rewrite N2Nat.inj_add -size_sizeN; f_equal.
rewrite -minusE; lia. 
Qed.

Lemma grid_of_initdataE globs v vinit:
 (nth (v,None) [seq x <- globs | [fun x => x.2 != None] x]
      (find [fun x => v == x.1] [seq x <- globs | [fun x => x.2 != None] x])).2
 = Some vinit ->
 nth [::] (grid_of_initdata globs)
     (find [fun x => v == x.1] [seq x <- globs | [fun x => x.2 != None] x])
 = bits_of_bytes vinit.
Proof.
elim: globs => //=.
move=> [x [xinit|]] globs IH //=. 
case: (ifP _) => /eqP E /=.
 by move=> [<-].
by move=> H; rewrite IH.
Qed.

Lemma conn_eval_find_gvar v inbits ssz globs vinit:
  get_initdata globs v = Some vinit ->
  conn_eval (mk_grid inbits ssz globs)
            (conn_new (3+n2N (find [fun x => v == x.1]
                                   [seq x <- globs | [fun x => x.2 != None] x])) 
                      0 (8*sizeN vinit))
  = Some (bits_of_bytes vinit).
Proof.
move=> /get_initdata_filter.
rewrite get_initdata_pos => H.
rewrite /mk_grid conn_eval_cat_conn_new //.
move: (grid_of_initdataE H) => E.
move: (sizeN_bits_of_bytes vinit) => Hsz.
rewrite conn_eval_conn_new nthN_nth n2N2n E; last by lia.
rewrite takeN_all //. 
rewrite Hsz; lia.
Qed.

Lemma list_repeatE A n (x:A): list_repeat n x = nseq n x.
Proof. by elim: n => //= n ->. Qed.

Lemma initmem_init_data_list {F V} (genv:Genv.t F V) (gv:globvar V) bs:
 initmem_of_globvar gv = Some bs ->
 Genv.bytes_of_init_data_list genv gv.(gvar_init) = map Byte bs.
Proof.
rewrite /initmem_of_globvar; elim: (gvar_init gv) bs => //=.
 by move=> _ [<-].
move=> [x|x|x|x|x|x|sz|? ?] xs IH bs // /obind_isS;
rewrite /bytes_of_initdata; move => [y [[<-]]] /obind_isS [ys [H [<-]]];
rewrite (IH ys) //= /encode_int /inj_bytes. 
rewrite takeN_take_dflt take_dflt_nil.
rewrite map_cat map_nseq -appE; f_equal.
by rewrite list_repeatE Z_N_nat.
Qed.

Lemma match_initmem_init_globmap m v ssz globs c:
 Genv.init_mem p = Some m ->
 collect_globals nil (prog_defs p) = Some globs ->
 PTree.get (Pos.succ v) (init_globmap ssz 3 globs) = Some c ->
 ∃ (b : Values.block) (gv : globvar unit),
   match_block m b (Genv.init_data_list_size (gvar_init gv))
     (mk_grid nil ssz gs) c
   ∧ Genv.block_is_volatile (Genv.globalenv p) b = false
     ∧ Genv.find_symbol (Genv.globalenv p) v = Some b
       ∧ Genv.find_var_info (Genv.globalenv p) b = Some gv
         ∧ Mem.valid_block m b.
Proof.
move=> Hmem Hglobs.
rewrite init_globmap_conn; move=> [vinit [Hget Hc]].
move: (get_initdata_nil v) => Hnil.
move: (collect_globals_prop Hglobs Hnil Hget)
=> [gv [l1 [l2 [H1 [H2 [/negPf H3 [H4 H5]]]]]]].
have Hnin: ¬In v (List.map fst l2) by rewrite -InE -mapE; apply/negP.
move: (Genv.find_var_exists_2 _ _ _ _ _ H1 Hnin) => [b [Hb Hgv]].
exists b, gv.
move: (Genv.find_symbol_not_fresh _ _ Hmem Hb) => Hb_valid.
move: (Genv.init_mem_characterization' _ _ Hgv Hmem) => [MA [MB [MC MD]]].
move: {MD} (MD H3) => Hload.
split.
pose E := (initmem_init_data_list _ H4).
 (* match_block *)
 constructor.
 - by [].
 - move=> o Hperm.
   by move: (MB o _ _ Hperm) => [MB1 _].
 - rewrite Hc sizeN_conn_new; apply N.mul_le_mono_nonneg_l=> //.
   rewrite N2Z.inj_le.
   transitivity (Genv.init_data_list_size (gvar_init gv)); last by rewrite Z2N.id.
   apply loadbytes_isS_sizeN in Hload.
   rewrite E sizeN_map in Hload.
   rewrite Hload Z2N.inj_le; first last.
     move: (Genv.init_data_list_size_pos (gvar_init gv)); lia.
    by apply N2Z.is_nonneg.   
   by rewrite N2Z.id; reflexivity.
 - exists (Genv.bytes_of_init_data_list (Genv.globalenv p) (gvar_init gv)), vinit; split => //.
   split => //.
    rewrite Hc.
    have [<-]: Some globs = Some gs by rewrite /gs -gsE Hglobs.
    by rewrite -(conn_eval_find_gvar [::] ssz Hget); f_equal.
    by rewrite E; clear; elim: vinit => //= x xs ->; rewrite eq_refl.
split; first by rewrite /Genv.block_is_volatile Hgv.
split; first by [].
by split.
Qed.

Lemma match_grid_global_initial_grid m (ssz:Z) m' sp:
  Genv.init_mem p = Some m ->
  (0 <= ssz <= Int.max_unsigned)%Z ->
  Mem.alloc m 0 ssz = (m', sp) ->
  match_grid_global
    (init_globmap ssz 3 gs)
    (Values.Vptr sp Int.zero) ssz m'
    (fill_grid nil 
               (initmem_stack (Int.repr ssz) :: globs_initdata gs)).
Proof.
intros Hinit [Hbnd1 Hbnd2] Halloc; exists sp; split; [reflexivity|].
split.
 (* Stack entry *)
 intros c Hc; constructor.
 - eapply alloc_valid_block_new; eauto.
 - intros o Hperm.
   eapply Mem.perm_alloc_3; eauto.
 - move: Hc; rewrite init_globmap_stack; move => [<-].
   rewrite sizeN_conn_new.
   apply N.mul_le_mono_nonneg_l; [lia|].
   generalize (Int.unsigned_range_2 (Int.repr ssz)); intros.
   solve [unfold N_of_int; rewrite <- Z2N.inj_le; lia].
 - assert (Mem.range_perm m' sp 0 (0 + ssz) Cur Readable).
    intros off Hoff.
    apply Mem.perm_implies with Freeable; [|constructor].
    apply (Mem.perm_alloc_2 _ _ _ _ _ Halloc); omega.
    destruct (Mem.range_perm_loadbytes m' sp 0 ssz H) as (mbs & Hload).
   exists mbs, (initmem_stack (Int.repr ssz)).
   split; [assumption|].
   split.
    move: Hc; rewrite init_globmap_stack; move => [<-].
    rewrite /mk_grid conn_eval_conn_new; last first.
     rewrite sizeN_size nthN_nth /= size_bits_of_bytes /initmem_stack.
     rewrite size_takeN_dflt Nat2N.inj_mul /= N2n2N.
     apply N.mul_le_mono_pos_l; first by [].
     rewrite /N_of_int Int.unsigned_repr //; lia.
    f_equal; rewrite nthN_nth /= takeN_all //.
    rewrite sizeN_bits_of_bytes sizeN_takeN_dflt.
    rewrite /N_of_int Int.unsigned_repr //; lia.
   generalize (Mem.loadbytes_length _ _ _ _ _ Hload); rewrite lengthE; intro Hsize.
(*   unfold match_bytes, initmem_stack. *)
   assert (forall x, In x mbs -> x = Undef) as Hconst.
    intros x; apply (Mem.loadbytes_alloc_same _ _ _ _ _ Halloc ssz 0 mbs); assumption.
   apply loadbytes_isS_sizeN in Hload; revert Hbnd1 Hbnd2 Hload Hconst.
   generalize ssz; clear.
   intros ssz Hbnd1 Hbnd2; assert (N_of_int (Int.repr ssz)=Z.to_N ssz) as ZN.
    rewrite /N_of_int Int.unsigned_repr; split; assumption. 
   rewrite /initmem_stack ZN; clear ZN; clear; revert ssz.
   elim mbs; simpl.
    intros ssz E Hconst. 
    rewrite <- E, takeN_take_dflt; constructor.
   intros x xs IH ssz E Hconst.
   rewrite <- E, takeN_take_dflt, N2Nat.inj_succ; simpl.
   (*constructor.*)
   rewrite (Hconst x) /=; [ |by left]. 
   assert (sizeN xs = Z.to_N (ssz-1)%Z).
    rewrite -> Z2N.inj_sub, <- E, <- N.add_1_r by lia; simpl.
    rewrite <- N.add_sub_assoc, N.add_0_r by reflexivity; reflexivity.
   rewrite -> H, <- takeN_take_dflt.
   apply IH; auto.
(* gvar entry *)
move=> v c H.
have Hglobs: collect_globals [::] (prog_defs p) = Some gs by rewrite /gs -gsE.
destruct (match_initmem_init_globmap Hinit Hglobs H) as (b & gv & HH).
destruct HH as (Hmb & Hvol & Hb & Hgv & Hvalid).
exists b, gv; split.
 by eapply match_block_alloc; eauto.
split; [assumption|].
split; [assumption|].
split;[|assumption].
eapply valid_block_alloc; eassumption.
Qed.

Lemma load_store_loadbytes o xs sz m b mbs m':
  (Int.unsigned o + Z.of_nat (size xs) <= sz)%Z ->
  Mem.loadbytes m b 0 sz = Some mbs ->
  Mem.storebytes m b (Int.unsigned o) xs = Some m' ->
  Mem.loadbytes m' b 0 sz = Some (conn_upd_at mbs (N_of_int o) xs).
Proof.
rewrite /N_of_int.
move: (Int.unsigned_range o).
set off := Int.unsigned o => [[Hoff _] H2].
have sz0: (sz >= 0)%Z by lia.
have: (sz = 0 \/ sz > 0)%Z by lia.
move=> [H0|H0].
rewrite -> !H0, !Mem.loadbytes_empty by lia.
 move=> [<-] H; f_equal.
 by rewrite /conn_upd_at updprefAtN_E takeN_nil dropN_nil updpref_nil.
move: H2; set size_xs := Z.of_nat (size xs).
have size_xs0: (0 <= size_xs)%Z by apply Zle_0_nat.
move=> Hbnds.
have E1: (sz = off + (size_xs + (sz - off - size_xs)))%Z by Psatz.lia.
rewrite E1 => Hl.
case: {Hl} (Mem.loadbytes_split _ _ _ _ _ _ Hl); [lia|lia|].
move => mbsL [mbs' [LBL [/= LB' ->]]].
case: (Mem.loadbytes_split _ _ _ _ _ _ LB'); [lia|lia|].
move => mbsM [mbsR [LBM [LBR ->]]] Hs.
rewrite /conn_upd_at updprefAtN_E updprefE -!appE E1.
move: (loadbytes_isS_sizeN LBL) => LBLsize.
move: (loadbytes_isS_sizeN LBM).
rewrite sizeN_size -Z_nat_N => /(f_equal N2n) LBMsize.
rewrite /size_xs Nat2Z.id n2N2n n2N2n in LBMsize.
move: (loadbytes_isS_sizeN LBR) => LBRsize.
apply Mem.loadbytes_concat; [| |lia|lia].
 rewrite takeN_take take_size_cat -?takeN_take; last first.
  by rewrite size_sizeN LBLsize.
 rewrite (Mem.loadbytes_storebytes_disjoint _ _ _ _ _ Hs) //; first by lia.
 right; apply Intv.disjoint_range; left; reflexivity.
apply Mem.loadbytes_concat; [| |lia|lia].
 rewrite take_oversize ?cats0; last first.
 rewrite dropN_drop drop_size_cat //=.
   by rewrite size_cat LBMsize; apply leq_addr.
  by rewrite size_sizeN LBLsize.
 by rewrite (Mem.loadbytes_storebytes_same _ _ _ _ _ Hs).
rewrite /= dropN_drop drop_size_cat ?drop_size_cat //; last first.
 by rewrite size_sizeN LBLsize.
rewrite (Mem.loadbytes_storebytes_disjoint _ _ _ _ _ Hs) //; last 2 first.
  lia.
 right; apply Intv.disjoint_range; right.
 rewrite /= lengthE /size_xs; lia.
have ->:(off + (size_xs + (sz - off - size_xs)) - off - size_xs = sz - off - size_xs)%Z.
 lia.
assumption.
Qed.

Lemma bits_of_bytes_take n xs:
  bits_of_bytes (take n xs) = take (muln 8 n) (bits_of_bytes xs).
Proof.
elim: xs n => //=.
move=> x xs IH [|n] //=.
 by rewrite take0.
rewrite take_cat.
rewrite !size_bits_of_byte.
case: (ifP _).
 rewrite -multE => /ltP H; lia.
rewrite IH mulnS => _; f_equal; f_equal.
by rewrite addnC -addnBA.
Qed.

Lemma bits_of_bytes_takeN n xs:
  bits_of_bytes (takeN n xs) = takeN (8*n) (bits_of_bytes xs).
Proof. by rewrite !takeN_take bits_of_bytes_take N2Nat.inj_mul. Qed.

Lemma bits_of_bytes_drop n xs:
  bits_of_bytes (drop n xs) = drop (muln 8 n) (bits_of_bytes xs).
Proof.
elim: xs n => //=.
move=> x xs IH [|n] //=.
 by rewrite drop0.
rewrite mulnS drop_cat.
case: (ifP _).
 rewrite -plusE size_bits_of_byte=> /ltP H; lia.
move=> _.
rewrite size_bits_of_byte addnC -addnBA // subnn addn0.
by apply IH.
Qed.

Lemma bits_of_bytes_dropN n xs:
  bits_of_bytes (dropN n xs) = dropN (8*n) (bits_of_bytes xs).
Proof. by rewrite !dropN_drop bits_of_bytes_drop N2Nat.inj_mul. Qed.

Lemma bits_of_bytes_updpref xs ys:
  bits_of_bytes (updpref xs ys) = updpref (bits_of_bytes xs) (bits_of_bytes ys).
Proof.
rewrite !updprefE size_bits_of_bytes size_bits_of_bytes.
by rewrite bits_of_bytes_cat bits_of_bytes_take bits_of_bytes_drop.
Qed.

Lemma bits_of_bytes_updprefAtN orig pos new:
  bits_of_bytes (updprefAtN pos orig new)
  = updprefAtN (8*pos) (bits_of_bytes orig) (bits_of_bytes new).
Proof.
rewrite !updprefAtN_E bits_of_bytes_cat.
apply/eqP; rewrite eqseq_cat; last first.
 by rewrite bits_of_bytes_takeN.
apply/andP; split; apply/eqP.
 by rewrite bits_of_bytes_takeN.
by rewrite bits_of_bytes_updpref bits_of_bytes_dropN.
Qed.

Lemma conn_eval_conn_new' g n pos sz:
  pos + sz <= sizeN (nthN nil g n) → 
  conn_eval g (conn_new n pos sz) = Some (takeN sz (dropN pos (nthN nil g n))).
Proof.
move=> Hsize; rewrite /conn_eval /wire_eval /conn_new.
rewrite omap_all_map omap_all_oseq oseq_isS. 
rewrite (takeN_map_nthN false) //; last first.
 rewrite sizeN_size dropN_drop size_drop Nat2N.inj_sub -sizeN_size; lia.
rewrite !iotaN_iota.
rewrite iota_map0 -!map_comp /=.
apply eq_in_map => x /=.
rewrite mem_iota add0n=> /andP [/leP Hl /ltP Hh].
rewrite onthN_isS.
rewrite -> !addnE, !Nat2N.inj_add, !N2n2N; split.
 apply: N.lt_le_trans; last first.
  apply Hsize.
 rewrite -N.add_lt_mono_l -N.ltb_lt /N.ltb N2Nat.inj_compare n2N2n.
 by move: Hh; rewrite nat_compare_lt => ->.
rewrite -> !dropN_drop, !nthN_nth, nth_drop; f_equal.
by rewrite N2Nat.inj_add.
Qed.

Lemma match_block_storev_input_same m b o x m' sz inp c globs:
  Mem.storev Mint8unsigned m (Values.Vptr b o) x = Some m' ->
  match_block m b sz
              (fill_grid (inp++(bits_of_byte (byte_of_input_val x))) globs) c ->
  match_block m' b sz
              (fill_grid (inp++(bits_of_byte (byte_of_input_val x))) globs)
              (conn_upd_at c (8 * N_of_int o) (conn_new 1 (sizeN inp) 8)).
Proof.
intros Hstore [Hval Hsz Hbnds (mbs & bs & Hload & Hc & Hmbs)].
have BOUNDS: (0 <= Int.unsigned o < sz)%Z. 
 apply Hsz, Mem.valid_access_perm with Mint8unsigned.
 apply Mem.valid_access_implies with Writable.
 eapply Mem.store_valid_access_3.
  apply Hstore.
 constructor.
constructor.
- eapply Mem.store_valid_block_1; eassumption.
- intros o' Ho'; apply Hsz.
  eapply Mem.perm_store_2; eassumption.
- rewrite sizeN_conn_upd_at; assumption.
- assert (sz >= 0)%Z as D by Psatz.lia.
  exists (conn_upd_at mbs (N_of_int o) (encode_val Mint8unsigned x)).
  exists (updprefAtN (N_of_int o) bs [:: byte_of_input_val x]).
  split.
   apply Mem.store_storebytes in Hstore.
   eapply load_store_loadbytes; eauto.
   destruct x; simpl; try lia.
   rewrite <- lengthE, length_inj_bytes, encode_int_length; lia.
  split.
   rewrite bits_of_bytes_updprefAtN; apply conn_eval_conn_upd_at; [assumption|].
   unfold fill_grid.
   rewrite conn_eval_conn_new'.
Opaque takeN. simpl; f_equal. rewrite -> seq.cats0, takeN_all, dropN_drop, seq.drop_size_cat. Transparent takeN.
reflexivity. rewrite <- size_sizeN; auto.
rewrite -> dropN_drop, seq.drop_size_cat. 
by rewrite sizeN_size size_bits_of_byte.
by rewrite -size_sizeN.
rewrite sizeN_app  sizeN_size sizeN_size  size_bits_of_byte. 
apply N.add_le_mono; reflexivity.
  apply all2_updprefAtN; auto.
  destruct x; auto.
by rewrite /= /encode_int /rev_if_be /Archi.big_endian /= eq_refl.
Qed.

Lemma match_block_storev_globv_same m b o x chunk xbs m' sz g gconn orig newbits:
  match_block m b sz g gconn ->
  conn_eval g gconn = Some orig ->
  Mem.storev chunk m (Values.Vptr b o) x = Some m' ->
  match_bytes (encode_val chunk x) xbs ->
  newbits = updprefAtN (8 * N_of_int o)
                       orig
                       (bits_of_bytes xbs) ->
  match_block m' b sz (rcons g newbits) (conn_new (sizeN g) 0 (sizeN gconn)).
Proof.
intros [Hval Hsz Hbnds (mbs & bs & Hload & Hc & Hmbs)].
rewrite Hc; move => [<-] /= Hstore Mxbs ->.
have Sz_encval: forall chunk x, Z.of_nat (size (encode_val chunk x))
                           = size_chunk chunk.
 by move=> [| | | | | | | | |] [|?|?|?|?|? ?]; 
  rewrite /encode_val ?list_repeatE ?size_nseq.
move: (conn_eval_isS_sizeN Hc) => Sz_gconn.
move: (size_chunk_pos chunk) => Sz_chunk_pos.
have T1: perm_order Writable Readable by constructor.
move: (Mem.store_valid_access_3 _ _ _ _ _ _ Hstore) => T2.
move: (Mem.valid_access_implies _ _ _ _ _ _ T2 T1) => {T1 T2} [T Sz_div].
have BOUNDS: (0 <= Int.unsigned o < sz)%Z by apply Hsz, T; lia.
have BOUNDS2: (Int.unsigned o + size_chunk chunk -1 < sz)%Z.
 by apply Hsz, T; lia.
constructor.
- eapply Mem.store_valid_block_1; eassumption.
- intros o' Ho'; apply Hsz.
  eapply Mem.perm_store_2; eassumption.
- rewrite sizeN_conn_new; assumption.
- assert (sz >= 0)%Z as D by Psatz.lia.
  exists (conn_upd_at mbs (N_of_int o) (encode_val chunk x)).
  exists (updprefAtN (N_of_int o) bs xbs).
  split.
   apply Mem.store_storebytes in Hstore.
   eapply load_store_loadbytes; [|eassumption|eassumption].
   by rewrite Sz_encval; lia.
  split.
   rewrite bits_of_bytes_updprefAtN.
   rewrite conn_eval_conn_new'.
    Opaque takeN.
    simpl; f_equal.
    rewrite dropN_drop drop0 nth_rcons_last takeN_all; last first.
     rewrite sizeN_updprefAtN Sz_gconn; reflexivity.
    reflexivity.
    Transparent takeN.
   rewrite nth_rcons_last sizeN_updprefAtN Sz_gconn; reflexivity.
  by apply all2_updprefAtN.
Qed.

Lemma match_block_storev_other chunk b o x m m' b' sz g c:
  Mem.store chunk m b o x = Some m' ->
  b <> b' ->
  match_block m b' sz g c ->
  match_block m' b' sz g c.
Proof.
intros Hstore Hdiff [Hval Hsz Hbnds (mbs & bs & Hload & Hconn & Hmatch)].
constructor.
- eapply Mem.store_valid_block_1; eassumption.
- intros o' Hperm; apply Hsz.
  eapply Mem.perm_store_2; eassumption.
- assumption.
- assert (sz <= 0 ∨ sz >= 0)%Z as D by Psatz.lia.
  case: D => HH.
   exists nil, nil.
   move: (Mem.loadbytes_empty m b' 0 sz HH) => X.
   rewrite X in Hload; apply Some_eq in Hload; subst.
   destruct bs=> //; auto; simpl in Hconn.
   split; [apply Mem.loadbytes_empty; assumption|].
   rewrite Hconn; split; [simpl; reflexivity|constructor].
  exists mbs, bs; split; auto.
  apply Mem.store_storebytes in Hstore.
  rewrite (Mem.loadbytes_storebytes_disjoint _ _ _ _ _ Hstore); auto.
Qed.


Lemma match_grid_global_input_increase globv sp ssz m inp globs xs:
 match_grid_global globv sp ssz m (fill_grid inp globs) ->
 match_grid_global globv sp ssz m (fill_grid (seq.cat inp xs) globs).
Proof.
intros (bstk & Hbstk & Hs & Hglob).
exists bstk; split; auto; split.
 intros c Hc; destruct (Hs _ Hc) as [Hval Hssz Hbnds (mbs & bs & Hload & Heval & Hmbs)]. split; auto.
 exists mbs, bs; split; auto.
 split; auto.
 unfold fill_grid; rewrite <- seq.cat1s; apply conn_eval_input; assumption.
intros v vinfo Hv.
destruct (Hglob _ _ Hv) as [b (gv & Hmb & Hvol & Hfind & Hsp & Hgv)].
exists b, gv.
split; auto.
destruct Hmb as [Hval Hssz Hbnds (mbs & bs & Hload & Heval & Hmbs)].
split; auto.
exists mbs, bs; split; auto.
split; auto.
unfold fill_grid; rewrite <- seq.cat1s; apply conn_eval_input; assumption.
Qed.

Lemma match_grid_global_add_input m m' v o x globs nin inp sp ssz globv c:
  nin * 8 = sizeN inp ->
  Mem.storev Mint8unsigned m (Genv.symbol_address (Genv.globalenv p) v o) x = Some m'
  -> PTree.get (Pos.succ v) globv = Some c
  -> match_grid_global globv sp ssz m (fill_grid (seq.cat inp (bits_of_byte (byte_of_input_val x))) globs)
  -> match_grid_global
       (PTree.set (Pos.succ v) (conn_upd_at c (8 * N_of_int o) (conn_new 1 (nin * 8) 8))
                  globv) sp ssz m' (fill_grid (seq.cat inp (bits_of_byte (byte_of_input_val x))) globs).
Proof.
intros Hsize Hstore Hv (bstk & Hbstk & Hstk & Hc).
exists bstk; split; [assumption|].
unfold Genv.symbol_address in Hstore.
case_eq (Genv.find_symbol (Genv.globalenv p) v);
[|intros Hb; rewrite Hb in Hstore; simpl in Hstore; congruence].
intros b Ev; rewrite Ev in Hstore.
destruct (Hc _ _ Hv) as (b' & gv & H1 & H2 & H3 & H4 & H5).
rewrite Ev in H3; symmetry in H3; inv H3.
split.
 intros c'; rewrite -> Maps.PTree.gso by lia; intros Hv'.
 specialize Hstk with c'; apply Hstk in Hv'.
 eapply match_block_storev_other; eauto.
intros v' c'.
case (Pos.eq_dec v v') => Ev'.
 rewrite Ev'; rewrite Maps.PTree.gss; intros H; inv H.
 exists b, gv.
 split.
  rewrite Hsize; eapply match_block_storev_input_same; eassumption.
 split; [assumption |].
 split; [assumption |].
 split; assumption.
rewrite -> Maps.PTree.gso by lia; intros Hv'.
destruct (Hc _ _ Hv') as (b' & gv' & H1' & H2' & H3' & H4' & H5').
exists b', gv'.
split.
 clear H4; eapply match_block_storev_other; eauto.
 clear H4'; eapply Genv.global_addresses_distinct; eassumption.
split; [assumption |].
split; [assumption |].
split; assumption.
Qed.

Lemma sizeN_globs_initdata globs:
 sizeN (globs_initdata globs) = sizeN_globs globs.
Proof.
rewrite !sizeN_size; elim: globs => //=.
move=> [v [vinit|]] globs IH.
 by rewrite Nat2N.inj_succ IH.
by rewrite /globs_initdata /= IH.
Qed.


Lemma match_decode_val ϰ mdata data:
  sizeN mdata = sizeN_chunk ϰ ->
  match_bytes mdata data ->
  match_val (Some (type_of_chunk ϰ))
            (decode_val ϰ mdata) 
            (chunk_ext ϰ false (bits_of_bytes data)).
Proof.
move=> Hsz Hmatch; have: sizeN data = sizeN_chunk ϰ.
 by rewrite -(all2_sizeN Hmatch). 
move: (match_bytes_byte_shape_md Hmatch).
move: ϰ Hsz Hmatch => [|||||||||]; rewrite /sizeN_chunk /=.
- move: mdata => [| [|mb1|? ?] [|? ?]] //=; last lia.
  move: data =>  [| b1 [| ?]] //=; last (intros; lia).
  move=> _ /andP [/eqP -> _] _ _.
  rewrite /chunk_ext /= sign_extN_int32_of_bits //.
  rewrite bits_of_int32_of_bits /sign_extN //.
  by rewrite sign_extN_ext size_sign_ext.
- move: mdata => [| [|mb1|? ?] [|? ?]] //=; last lia.
  move: data =>  [| b1 [| ?]] //=; last (intros; lia).
  move=> _ /andP [/eqP -> _] _ _.
  rewrite /chunk_ext /= zero_extN_int32_of_bits //.
  rewrite bits_of_int32_of_bits /zero_extN //.
  by rewrite size_takeN_dflt.
- move: mdata => [| [|mb0|? ?] // [|[|mb1|? ?] [|? ?]]] //=; last lia.
  move: data =>  [| b1 [| b2 [| ?]]] //=; last (intros; lia).
  move=> _ /andP [/eqP -> /andP [/eqP -> _]] _ _.
  rewrite /chunk_ext /= sign_extN_int32_of_bits //.
  rewrite bits_of_int32_of_bits /sign_extN //.
  by rewrite sign_extN_ext size_sign_ext.
- move: mdata => [| [|mb0|? ?] // [|[|mb1|? ?] [|? ?]]] //=; last lia.
  move: data =>  [| b1 [| b2 [| ?]]] //=; last (intros; lia).
  move=> _ /andP [/eqP -> /andP [/eqP -> _]] _ _.
  rewrite /chunk_ext /= zero_extN_int32_of_bits //.
  rewrite bits_of_int32_of_bits /zero_extN //. 
  by rewrite size_takeN_dflt.
- move: mdata => [| [|mb0|? ?] //= [|[|mb1|? ?] //
                 [| [|mb2|? ?] // [|[|mb3|? ?] [|? ?]]]]] //= ; last lia.
  move: data =>  [| b0 [| b1 [| b2 [| b3 [|? ?]]]]] //=; last (intros; lia).
  move=> _ /and4P [/eqP -> /eqP -> /eqP -> /andP [/eqP -> _]] _ _.
  set bs := (_ ++ _). Transparent N.mul.
  set i := (Int.repr _).
  have E: sizeN bs = 32.
   by rewrite /bs sizeN_size ?size_cat ?size_bits_of_byte.
  rewrite /chunk_ext [is_left _]/= /wires_of_type /= -E takeN_dflt_all.
  by rewrite /bits_of_int32 bytes_of_int32_decode_int.
- move: mdata => [|[|mb0|? ?] // [|[|mb1|? ?] // 
                 [|[|mb2|? ?] // [|[|mb3|? ?] //
                 [|[|mb4|? ?] // [|[|mb5|? ?] //
                 [|[|mb6|? ?] // [|[|mb7|? ?] // [|? ?]]]]]]]]] //=; last lia.
  move: data => [|b0 // [|b1 // 
                [|b2 // [|b3 //
                [|b4 // [|b5 //
                [|b6 // [|b7 // [|? ?]]]]]]]]] //=; last (intros; lia).
  move=> _ /and4P [/eqP -> /eqP -> /eqP -> /andP [/eqP -> H]] _ _.
  move: H => /and4P [/eqP -> /eqP -> /eqP -> /andP [/eqP -> _]].
  set bs := (_ ++ _).
  set i := (Int64.repr _).
  have E: sizeN bs = 64.
   by rewrite /bs sizeN_size ?size_cat ?size_bits_of_byte.
  rewrite /chunk_ext [is_left _]/= /wires_of_type /= -E takeN_dflt_all.
  by rewrite /bits_of_int64 bytes_of_int64_decode_int.
- move: mdata => [| [|mb0|? ?] //= [|[|mb1|? ?] //
                 [| [|mb2|? ?] // [|[|mb3|? ?] [|? ?]]]]] //= ; last lia.
  move: data =>  [| b0 [| b1 [| b2 [| b3 [|? ?]]]]] //=; last (intros; lia).
  move=> _ /and4P [/eqP -> /eqP -> /eqP -> /andP [/eqP -> _]] _ _.
  set bs := (_ ++ _). 
  set i := (Int.repr _).
  have E: sizeN bs = 32.
   by rewrite /bs sizeN_size ?size_cat ?size_bits_of_byte.
  rewrite /chunk_ext [is_left _]/= /wires_of_type /= -E takeN_dflt_all.
  by rewrite Floats.Float32.to_of_bits /bits_of_int32 bytes_of_int32_decode_int.
- move: mdata => [|[|mb0|? ?] // [|[|mb1|? ?] // 
                 [|[|mb2|? ?] // [|[|mb3|? ?] //
                 [|[|mb4|? ?] // [|[|mb5|? ?] //
                 [|[|mb6|? ?] // [|[|mb7|? ?] // [|? ?]]]]]]]]] //=; last lia.
  move: data => [|b0 // [|b1 // 
                [|b2 // [|b3 //
                [|b4 // [|b5 //
                [|b6 // [|b7 // [|? ?]]]]]]]]] //=; last (intros; lia).
  move=> _ /and4P [/eqP -> /eqP -> /eqP -> /andP [/eqP -> H]] _ _.
  move: H => /and4P [/eqP -> /eqP -> /eqP -> /andP [/eqP -> _]].
  set bs := (_ ++ _).
  set i := (Int64.repr _).
  have E: sizeN bs = 64.
   by rewrite /bs sizeN_size ?size_cat ?size_bits_of_byte.
  rewrite /chunk_ext [is_left _]/= /wires_of_type /= -E takeN_dflt_all.
  by rewrite Floats.Float.to_of_bits /bits_of_int64 bytes_of_int64_decode_int.
- by move: mdata => [| [|mb0|? ?] //= [|[|mb1|? ?] //
                 [| [|mb2|? ?] // [|[|mb3|? ?] [|? ?]]]]] //= ; last lia.
- move: mdata => [|[|mb0|? ?] // [|[|mb1|? ?] // 
                 [|[|mb2|? ?] // [|[|mb3|? ?] //
                 [|[|mb4|? ?] // [|[|mb5|? ?] //
                 [|[|mb6|? ?] // [|[|mb7|? ?] // [|? ?]]]]]]]]] //=; last lia.
Qed.

Lemma loadbytes_loadbytes_split m b varsize mbs off sz mres:
 (sz > 0)%Z ->
 Mem.loadbytes m b 0 varsize = Some mbs ->
 Mem.loadbytes m b off sz = Some mres ->
 (forall o, Mem.perm m b o Cur Readable → (0 <= o < varsize)%Z) ->
 (0 <= off)%Z /\ (0 <= off + sz <= varsize)%Z /\
 exists mbsL mbsR, 
   mbs = mbsL ++ mres ++ mbsR
   /\ Mem.loadbytes m b 0 off = Some mbsL
   /\ Mem.loadbytes m b (off+sz) (varsize-off-sz) = Some mbsR.
Proof.
move=> Hsz Hl1 Hl2 Hperm.
move: (Mem.loadbytes_length _ _ _ _ _ Hl1); rewrite lengthE => Hl1_sz.
move: (Mem.loadbytes_range_perm _ _ _ _ _ Hl1) => Hl1_perm.
move: (Mem.loadbytes_length _ _ _ _ _ Hl2); rewrite lengthE => Hl2_sz.
move: (Mem.loadbytes_range_perm _ _ _ _ _ Hl2) => Hl2_perm.
have T: (off <= off < off+sz)%Z by lia.
move: {T} (Hperm _ (Hl2_perm off T)) => Boff.
have T: (off <= off+sz-1 < off+sz)%Z by lia.
move: {T} (Hperm _ (Hl2_perm _ T)) => Boffsz.
split; first lia.
split; first lia.
have E: varsize = (off + (sz + (varsize - off - sz)))%Z by lia.
move: Hl1; rewrite {1} E => Hl1.
have T1: (off >= 0)%Z by lia.
have T2: (sz + (varsize-off-sz) >= 0)%Z by lia.
move: {T1 T2} (Mem.loadbytes_split _ _ _ _ _ _ Hl1 T1 T2).
rewrite Z.add_0_l; move=> [mbsL [rest [HmbsL [Hrest ->]]]].
have T1: (sz >= 0)%Z by lia.
have T2: (varsize-off-sz >= 0)%Z by lia.
move: {T1 T2} (Mem.loadbytes_split _ _ _ _ _ _ Hrest T1 T2). 
rewrite Hl2; move=> [mbsC [mbsR [[<-] [HmbsR ->]]]].
exists mbsL, mbsR; rewrite -appE ?catA.
split; first reflexivity.
by split.
Qed.

Lemma size_sign_ext' A n (d:A) l:
 size (sign_ext' n d l) = n.
Proof. by elim: n d l => //= n IH d [|x xs] /=; rewrite IH. Qed.

Lemma sizeN_sign_extN' A n (d:A) l:
 sizeN (sign_extN' n d l) = n.
Proof. by rewrite sizeN_size sign_extN_ext size_sign_ext' N2n2N. Qed.


Lemma sizeN_chunk_ext l ϰ:
 sizeN (chunk_ext ϰ false l) = wires_of_type (type_of_chunk ϰ).
Proof.
rewrite /chunk_ext; case: (ifP _) => _ //=.
 by rewrite sizeN_sign_extN'.
by rewrite sizeN_takeN_dflt.
Qed.

Lemma nthN_width_succ A w n (l: seq A):
  nthN_width w l (N.succ n) = nthN_width w (dropN w l) n.
Proof. by rewrite /nthN_width N.peano_rect_succ. Qed.

Lemma nthN_widthE A w (l:seq A) off:
  nthN_width w l off = takeN w (dropN (off*w) l).
Proof.
move: off l. apply: N.peano_ind => //=.
move=> n IH l.
by rewrite nthN_width_succ IH N.mul_succ_l dropN_add.
Qed.

Lemma sizeN_nthN_width A w (data: seq A) pos:
 pos*w+w <= sizeN data ->
 sizeN (nthN_width w data pos) = w.
Proof.
move=> Hpos.
rewrite nthN_widthE sizeN_size takeN_take size_take.
case: (ltnP _ _).
 by move=> H; rewrite N2n2N.
rewrite dropN_drop size_drop.
rewrite size_sizeN -minusE -N2Nat.inj_sub -N2n_le => Hpos'.
lia.
Qed.


Lemma sizeN_chunk_log2 ϰ:
 sizeN_chunk ϰ = 2 ^ (N.log2 (sizeN_chunk ϰ)).
Proof. by move: ϰ => [| | | | | | | | |] //=. Qed.


Opaque N.mul.

Lemma N_of_drop_bits n bs:
 N_of_bits (drop n bs) = N.shiftr (N_of_bits bs) (n2N n).
Proof.
elim: n bs => //=.
 by move=> bs; rewrite drop0.
move=> [|n] IH [|x xs] //=.
  move: x => [|].
   rewrite IH N_of_bits_cons N.add_comm -N.succ_double_spec.
   by rewrite N.div2_succ_double N.shiftr_0_r. 
  rewrite IH N_of_bits_cons N.add_comm -N.double_spec N.add_0_r.
  by rewrite N.div2_double N.shiftr_0_r.
 rewrite /N_of_bits //= Pos.iter_succ -Pos.iter_swap N.div2_div N.div_0_l //.
 clear; elim: n => //= n IH; rewrite Pos.iter_succ -Pos.iter_swap N.div2_div.
 by rewrite N.div_0_l // IH.
rewrite IH /= Pos.iter_succ -Pos.iter_swap N_of_bits_cons.
move: x => [|] /=.
 by rewrite N.add_comm -N.succ_double_spec N.div2_succ_double.
by rewrite N.add_0_l -N.double_spec N.div2_double.
Qed.

Lemma drop_log2_div_size_chunk ϰ i:
 N_of_bits (dropN (N.log2 (sizeN_chunk ϰ)) (bits_of_int32 i))
 = N_of_int i / sizeN_chunk ϰ.
Proof.
rewrite {2}sizeN_chunk_log2 -N.shiftr_div_pow2 .
rewrite dropN_drop N_of_drop_bits N2n2N; f_equal.
rewrite /N_of_int.
have N_of_bits_via_Z bs: N_of_bits bs = Z.to_N (Z_of_bits bs).
 by rewrite /Z_of_bits N2Z.id.
rewrite N_of_bits_via_Z /bits_of_int32; f_equal.
rewrite Z_of_bits_of_bytes int_of_bytes_of_int /= Zmod_small //.
by apply Int.unsigned_range.
Qed.

Lemma N_of_bits_eq_Z bs1 n:
  N_of_bits bs1 = n <-> Z_of_bits bs1 = Z.of_N n.
Proof.
rewrite /Z_of_bits; split.
 move => H.
 apply Z2N.inj; try by apply N2Z.is_nonneg.
 by rewrite ?N2Z.id.
by move=> /N2Z.inj H.
Qed.

Lemma Z_of_bits_drop: forall n bs,
 Z_of_bits (drop n bs) = (Z_of_bits bs / two_power_nat n)%Z.
Proof.
elim => //=.
 by move=> [| x xs]; rewrite //= Z_of_bits_cons two_power_nat_O Z.div_1_r.
move=> n IH [|[|] xs] //=.
 rewrite IH Z_of_bits_cons /Z_of_bool Z.add_comm two_power_nat_S.
 rewrite -Z.div_div // Z.mul_comm Z.div_add_l //.
 by rewrite [(1/_)%Z]Z.div_small // Z.add_0_r.
rewrite IH Z_of_bits_cons /Z_of_bool Z.add_comm two_power_nat_S Z.add_0_r.
by rewrite -Z.div_div // Z.mul_comm Z.div_mul.
Qed.

Lemma Z_of_bits_take: forall n bs,
 Z_of_bits (take n bs) = (Z_of_bits bs mod two_power_nat n)%Z.
Proof.
elim => //=.
 by move=> [| x xs]; rewrite //= Z_of_bits_cons two_power_nat_O Z.mod_1_r.
move=> n IH [|[|] xs] //=.
 rewrite !Z_of_bits_cons IH /Z_of_bool Z.add_comm two_power_nat_S.
 rewrite -Z.mul_mod_distr_l // Z.add_comm.
 rewrite !Zmod_eq //.
 have ->: ((1 + 2 * Z_of_bits xs) / (2 * two_power_nat n)
           = 2 * Z_of_bits xs / (2 * two_power_nat n))%Z.
  rewrite Z.add_comm  -Z.div_div // Z.mul_comm Z.div_add_l //.
  rewrite [(1/_)%Z]Z.div_small // Z.add_0_r.
  by rewrite Z.mul_comm Zdiv_mult_cancel_l.
 lia. 
rewrite !Z_of_bits_cons IH /Z_of_bool Z.add_comm two_power_nat_S.
by rewrite -Z.mul_mod_distr_l // Z.add_comm // !Z.add_0_l.
Qed.

Lemma Z_of_bits_take': forall z n bs,
 (0 <= z < two_power_nat n)%Z ->
 Z_of_bits bs = z ->
 Z_of_bits (take n bs) = z.
Proof.
move=> z n bs H E; rewrite Z_of_bits_take Z.mod_small //.
by rewrite E.
Qed.

Lemma takeN_dflt_all' A (d:A) l n:
 sizeN l = n -> takeN_dflt d n l = l.
Proof. by move=> <-; apply takeN_dflt_all. Qed.

Lemma idxbits_correct ϰ varsize off:
 (size_chunk ϰ | Int.unsigned off)%Z ->
 (0 <= Int.unsigned off)%Z ->
 (0 <= Int.unsigned off + size_chunk ϰ <= varsize)%Z ->
 N_of_bits
    (takeN (size2idxbits (8 * sizeN_chunk ϰ) (8 * Z.to_N varsize))
        (dropN (N.log2 (sizeN_chunk ϰ)) (bits_of_int32 off)))
 = N_of_int off / sizeN_chunk ϰ.
Proof.
move=> Hdivides Hoff1 Hoff2.
move: (size_chunk_pos ϰ) => X1.
rewrite N_of_bits_eq_Z N2Z.inj_div takeN_take.
erewrite Z_of_bits_take'; first reflexivity.
 (* significant bits... *)
 rewrite /N_of_int /sizeN_chunk ?Z2N.id //; last lia.
 rewrite /size2idxbits two_power_nat_equiv.
 split; first by apply Z_div_pos.
 apply (Z.lt_le_trans _ (varsize / size_chunk ϰ)).
  have HA: ((Int.unsigned off + size_chunk ϰ)/(size_chunk ϰ) 
            <= varsize / (size_chunk ϰ))%Z. 
   apply Z.div_le_mono; lia.
  have HB: ((Int.unsigned off + size_chunk ϰ)/(size_chunk ϰ)
            = Zsucc ((Int.unsigned off)/(size_chunk ϰ)))%Z.
   rewrite -Z.add_1_l -Z.div_add_l; last lia.
   by rewrite Z.mul_1_l Z.add_comm.
  move: HA; rewrite HB => HA.
  lia.
 rewrite -[2%Z]/(Z.of_N 2) N_nat_Z -N2Z.inj_pow.
 move: (N.le_gt_cases (8 * Z.to_N varsize / (8 * sizeN_chunk ϰ)) 1) => [Hsz|Hsz].
  rewrite N.log2_up_eqn0 //; last first.
  rewrite N.pow_0_r.
  rewrite -(Zdiv_mult_cancel_l _ _ 8) //.
  move: Hsz; rewrite N2Z.inj_le.
  rewrite N2Z.inj_div ?N2Z.inj_mul ?Z2N.id //; lia.
 move: (N.log2_up_spec (8 * Z.to_N varsize / (8 * sizeN_chunk ϰ)) Hsz) => [_].
 have X2: Z.to_N 0%Z < Z.to_N (size_chunk ϰ) by rewrite -Z2N.inj_lt; lia.
 rewrite /sizeN_chunk N.div_mul_cancel_l //; last lia.
 move=> HH.
 rewrite -{1}[varsize]Z2N.id; last lia.
 rewrite -{1}[size_chunk _]Z2N.id; last lia.
 by rewrite -N2Z.inj_div; apply N2Z.inj_le.
(* drop_div *)
rewrite -N2Z.inj_div -N_of_bits_eq_Z.
by apply drop_log2_div_size_chunk.
Qed.


Lemma Gselk_correct m b off varsize ϰ mbs data databits idx:
 Memdata.align_chunk ϰ = Memdata.size_chunk ϰ ->
 (∀ o : Z,
       Mem.perm m b o Cur Readable
       → (0 <= o < varsize)%Z ) ->
 Mem.loadbytes m b 0 varsize = Some mbs ->
 match_bytes mbs data ->
 databits = bits_of_bytes data ->
 idx = N_of_int off / sizeN_chunk  ϰ ->
 match_val
   (Some (type_of_chunk ϰ))
   (RTLC.val_of_oval (Mem.load ϰ m b (Int.unsigned off)))
   (zero_extN' false (wires_of_type (type_of_chunk ϰ))
               (chunk_ext ϰ false
                 (zero_extN' false (8*sizeN_chunk ϰ)
                        (nthN_width (8*sizeN_chunk ϰ) databits idx)))).
Proof.
move=> Halign_chunk Hperm Hload Hmatch Edatabits ->.
case Eload: (Mem.load ϰ m b (Int.unsigned off)) => [res|] //=.
move: (Mem.load_valid_access _ _ _ _ _ Eload).
rewrite /Mem.valid_access Halign_chunk; move => [_ Halign].
move: {Eload} (Mem.load_loadbytes _ _ _ _ _ Eload) => [mres [Hmres ->]].
move: (size_chunk_pos ϰ) => Hpos.
move: (loadbytes_loadbytes_split Hpos Hload Hmres Hperm) Edatabits.
move=> [Hoff1 [Hoff2 [mbsL [mbsR [Embs [HloadL HloadR]]]]]].
move: Hload Hmatch; rewrite Embs => Hload /all2_catIl [bsL [bsR [-> [ML MR]]]].
move: bsR MR => ? /all2_catIl [bsres [bsR [-> [MC MR]]]] E.
rewrite E{E} takeN_dflt_all'; last by rewrite sizeN_chunk_ext.
have E: bsres = nthN_width (sizeN_chunk ϰ) (bsL++bsres++bsR)
                           (N_of_int off / sizeN_chunk ϰ).
 rewrite nthN_widthE takeN_take dropN_drop drop_size_cat; last first.
  rewrite size_sizeN -(all2_sizeN ML) (loadbytes_isS_sizeN HloadL).
  f_equal; rewrite /N_of_int /sizeN_chunk -Z2N.inj_div; [| lia|lia].
  rewrite -Z2N.inj_mul; first last.
    lia.
   apply Z_div_pos; lia.
  f_equal; rewrite Z.mul_comm -Z.divide_div_mul_exact //; last lia.
  rewrite Z.mul_comm Z_div_mult_full //; last lia.
 by rewrite take_size_cat // size_sizeN -(all2_sizeN MC) (loadbytes_isS_sizeN Hmres).
set tmp:= zero_extN' _ _ _.
have ->: tmp = bits_of_bytes bsres.
 rewrite /tmp takeN_dflt_all'; last first.
  rewrite sizeN_nthN_width //.
  apply all2_sizeN in ML.
  apply all2_sizeN in MC.
  apply all2_sizeN in MR.
  apply loadbytes_isS_sizeN in HloadL.
  apply loadbytes_isS_sizeN in HloadR.
  apply loadbytes_isS_sizeN in Hmres.
  have ->: sizeN (bits_of_bytes (bsL ++ bsres ++ bsR)) = 8 * Z.to_N varsize.
   rewrite sizeN_bits_of_bytes sizeN_size ?size_cat ?Nat2N.inj_add -!sizeN_size.
   rewrite -ML -MC -MR HloadL HloadR Hmres.
   rewrite -!Z2N.inj_add //; [|lia|lia|lia]; f_equal; f_equal; lia.
  rewrite N.mul_comm -N.mul_assoc.
  have: N_of_int off mod sizeN_chunk ϰ = 0. 
   rewrite /N_of_int /sizeN_chunk -Z2N.inj_mod //; last lia.
   rewrite -[0]N2Z.id; f_equal.
   by apply Zdivide_mod.
  have T1: sizeN_chunk ϰ ≠ 0.
   rewrite /sizeN_chunk -[0]N2Z.id => HH. 
   apply Z2N.inj in HH;  lia.
  rewrite -(N.div_exact (N_of_int off) (sizeN_chunk ϰ) T1) => <-.
  rewrite -N.mul_add_distr_l; apply N.mul_le_mono_nonneg_l => //.
  rewrite /N_of_int /sizeN_chunk -Z2N.inj_add; [|lia|lia].
  rewrite -Z2N.inj_le; lia.
 rewrite {2}E /tmp ?nthN_widthE bits_of_bytes_takeN bits_of_bytes_dropN.
 f_equal; f_equal; lia.
apply match_decode_val => //.
by rewrite (loadbytes_isS_sizeN Hmres) /sizeN_chunk.
Qed.

Lemma Gsel_correct m b off varsize ϰ mbs data databits idxbits:
 Memdata.align_chunk ϰ = Memdata.size_chunk ϰ ->
 (∀ o : Z,
       Mem.perm m b o Cur Readable
       → (0 <= o < varsize)%Z ) ->
 Mem.loadbytes m b 0 varsize = Some mbs ->
 match_bytes mbs data ->
 databits = bits_of_bytes data ->
(* idx = N_of_int off / sizeN_chunk  ϰ ->*)
 idxbits = takeN (size2idxbits (8 * sizeN_chunk ϰ) (8*Z.to_N varsize))
                 (dropN (N.log2 (sizeN_chunk ϰ)) 
                        (bits_of_int32 off)) ->
 match_val
   (Some (type_of_chunk ϰ))
   (RTLC.val_of_oval (Mem.load ϰ m b (Int.unsigned off)))
   (zero_extN' false (wires_of_type (type_of_chunk ϰ))
               (chunk_ext ϰ false
                 (zero_extN' false (8*sizeN_chunk ϰ)
                        (nthN_width (8*sizeN_chunk ϰ) databits (N_of_bits idxbits))))).
Proof.
move=> Halign_chunk Hperm Hload Hmatch Edatabits Eidxbits.
case Eload: (Mem.load ϰ m b (Int.unsigned off)) => [res|] //=.
move: (Mem.load_valid_access _ _ _ _ _ Eload).
rewrite /Mem.valid_access Halign_chunk; move => [_ Halign].
move: {Eload} (Mem.load_loadbytes _ _ _ _ _ Eload) => [mres [Hmres ->]].
move: (size_chunk_pos ϰ) => Hpos.
move: (loadbytes_loadbytes_split Hpos Hload Hmres Hperm) Edatabits.
move=> [Hoff1 [Hoff2 [mbsL [mbsR [Embs [HloadL HloadR]]]]]].
move: Hload Hmatch; rewrite Embs => Hload /all2_catIl [bsL [bsR [-> [ML MR]]]].
move: bsR MR => ? /all2_catIl [bsres [bsR [-> [MC MR]]]] E.
(* index manipulation *)
rewrite Eidxbits idxbits_correct //.
(* data manipulation *)
rewrite E{E} takeN_dflt_all'; last by rewrite sizeN_chunk_ext.
have E: bsres = nthN_width (sizeN_chunk ϰ) (bsL++bsres++bsR)
                           (N_of_int off / sizeN_chunk ϰ).
 rewrite nthN_widthE takeN_take dropN_drop drop_size_cat; last first.
  rewrite size_sizeN -(all2_sizeN ML) (loadbytes_isS_sizeN HloadL).
  f_equal; rewrite /N_of_int /sizeN_chunk -Z2N.inj_div; [| lia|lia].
  rewrite -Z2N.inj_mul; first last.
    lia.
   apply Z_div_pos; lia.
  f_equal; rewrite Z.mul_comm -Z.divide_div_mul_exact //; last lia.
  rewrite Z.mul_comm Z_div_mult_full //; last lia.
 by rewrite take_size_cat // size_sizeN -(all2_sizeN MC) (loadbytes_isS_sizeN Hmres).
set tmp:= zero_extN' _ _ _.
have ->: tmp = bits_of_bytes bsres.
 rewrite /tmp takeN_dflt_all'; last first.
  rewrite sizeN_nthN_width //.
  apply all2_sizeN in ML.
  apply all2_sizeN in MC.
  apply all2_sizeN in MR.
  apply loadbytes_isS_sizeN in HloadL.
  apply loadbytes_isS_sizeN in HloadR.
  apply loadbytes_isS_sizeN in Hmres.
  have ->: sizeN (bits_of_bytes (bsL ++ bsres ++ bsR)) = 8 * Z.to_N varsize.
   rewrite sizeN_bits_of_bytes sizeN_size ?size_cat ?Nat2N.inj_add -!sizeN_size.
   rewrite -ML -MC -MR HloadL HloadR Hmres.
   rewrite -!Z2N.inj_add //; [|lia|lia|lia]; f_equal; f_equal; lia.
  rewrite N.mul_comm -N.mul_assoc.
  have: N_of_int off mod sizeN_chunk ϰ = 0. 
   rewrite /N_of_int /sizeN_chunk -Z2N.inj_mod //; last lia.
   rewrite -[0]N2Z.id; f_equal.
   by apply Zdivide_mod.
  have T1: sizeN_chunk ϰ ≠ 0.
   rewrite /sizeN_chunk -[0]N2Z.id => HH. 
   apply Z2N.inj in HH;  lia.
  rewrite -(N.div_exact (N_of_int off) (sizeN_chunk ϰ) T1) => <-.
  rewrite -N.mul_add_distr_l; apply N.mul_le_mono_nonneg_l => //.
  rewrite /N_of_int /sizeN_chunk -Z2N.inj_add; [|lia|lia].
  rewrite -Z2N.inj_le; lia.
 rewrite {2}E /tmp ?nthN_widthE bits_of_bytes_takeN bits_of_bytes_dropN.
 f_equal; f_equal; lia.
apply match_decode_val => //.
by rewrite (loadbytes_isS_sizeN Hmres) /sizeN_chunk.
Qed.




Lemma all_lt_cons n x xs:
 all_lt n (x::xs) -> x < n /\ all_lt n xs.
Proof.
move=> H; split.
 by apply (H x); left; reflexivity.
by move=> y Hy; apply (H y); right.
Qed.

Lemma localv_args_eval localv g g' args wargs :
 all_lt (sizeN g) args ->
 match_grid_local localv g g' ->
 localv_conn_list localv args wargs ->
 exists x, conn_eval g' wargs = Some x.
Proof.
elim: args wargs => /=.
 by move=> wargs _ _ -> /=; exists [::] => //.
move=> a args IH wargs /all_lt_cons [Halt Hargslt] /= Hlocal [aconn [argsconn [->]]].
move=> [[ty [gw [Ha Hc]]]] Hargs.
move: (Hlocal _ _ _ Ha Halt) => [abits [HH1 HH2]].
move: (IH argsconn Hargslt Hlocal Hargs) => [argsbits HH].
subst; rewrite /read_wire in HH1.
by exists (abits++argsbits); apply conn_eval_cat => //.
Qed.

Lemma gate_eval_sizeN ginfo g args res:
 gate_eval ginfo g args = Some res -> sizeN res = ginfo.(gate_out_arity).
Proof.
by rewrite /gate_eval omap_isS; move => [x [H1 ->]]; rewrite sizeN_takeN_dflt.
Qed.

Lemma cmp_gate_out_arity gate cnd:
 gate_of_condition cnd = Some gate -> gate_out_arity (gateInfo gate) = 1.
Proof.
by destruct cnd; try destruct c => //=; move=> [<-] //.
Qed.

Lemma eval_guard_cat rest g vars b vars':
 (size (bdt_vars g) <= size vars)%N ->
 eval_guard g vars = (b,vars') -> 
 size vars = (size (bdt_vars g) + size vars')%N
 /\ eval_guard g (vars++rest) = (b,vars'++rest).
Proof.
elim: g vars b vars' => //=.
 by move=> [|] vars b vars' _ [E1 E2]; subst.
move=> v l IHl r IHr [|x xs] //= b vars'; rewrite size_cat -plusE => /ltP H.
case El: (eval_guard l xs) => [r1 vars1].
case Er: (eval_guard r vars1) => [r2 vars2].
move=> HH.
have Hxs: (size (bdt_vars l) <= size xs)%N.
 apply/leP; lia.
move: (IHl xs r1 vars1 Hxs El) => [Hl1 Hl2].
have Hxs2: (size (bdt_vars r) <= size vars1)%N.
 have Evars': vars' = vars2 by destruct x; inv HH.
 move: H Hxs; move => /ltP H /leP Hxs.
 rewrite -(leq_add2l (size (bdt_vars l))) -Hl1.
 by apply H.
move: (IHr vars1 r2 vars2 Hxs2 Er) => [Hr1 Hr2].
have Evars': vars' = vars2 by destruct x; inv HH.
split. 
 rewrite Hl1 Hr1 Evars' -!plusE; lia.
by move: HH; rewrite Hl2 Hr2; case x; move=> [-> ->].
Qed.

Lemma mem_get_path_model g cw condv n v:
 wire_of_condition_wires cw = Some condv ->
 condv ! v = Some n ->
 (v \in ValCirc.get_path_model g cw)
 = ValCirc.val_is_true (ValCirc.read_wire g n).
Proof.
move=> Hcondv.
rewrite (wire_of_condition_wiresP _ _ _ _ Hcondv).
move: n v.
rewrite /ValCirc.get_path_model /ValCirc.get_path_model'.
set f := fun pcm_i v0 => let '(pcm,i) := pcm_i in
                         (match cw!(N.succ_pos i) with
                          | Some c => if ValCirc.val_is_true v0
                                      then c::pcm
                                      else pcm
                          | None => pcm end, N.succ i).
move=> n v Hn.
have HX: forall n b p, n-b = N.pos p -> Pos.pred_N p = n-N.succ b.
 move=> x y z H.
 by rewrite N.pos_pred_spec -H N.sub_succ_r.
have HY: forall g a b,
  (v\in (fold_left f g (a,b)).1) = 
  (v\in a) || (v\in (fold_left f g ([::],b)).1). 
 elim => //=.
  by move=> a b; rewrite in_nil orbF.
 move=> g0 g' IH a b /=.
 rewrite IH; case E: (cw ! (N.succ_pos b)) => [w|] //.
 case: (ifP _) => // H.
 by rewrite (IH [:: w]) ?in_cons ?in_nil orbF [(_==_)||_]orbC orbA. 
have HZ: forall b, 
    (v \in (fold_left f g ([::], b)).1)
    = (b<=?n)&& ValCirc.val_is_true (ValCirc.read_wire g (n-b)).
 elim: g => //= [b|g0 g IH b].
  by rewrite /ValCirc.val_is_true /Values.Val.eq /= andbF in_nil.
 rewrite /= HY. 
 case E1: (n == b); move: E1 => /eqP E1.
  rewrite E1 N.sub_diag N.leb_refl /=.
  case E2: (cw! (N.succ_pos b)) => [y|]; last first.
   by move: E2; rewrite -E1 Hn.
  move: E2; rewrite -E1 Hn; move => [E2]; subst.
  case: (ifP _) => Hb0.
   by rewrite in_cons eq_refl.
  rewrite in_nil /= IH.
  have ->: (N.succ b <=? b) = false.
   rewrite N.leb_gt; lia.
  by [].
 have T1: (N.succ b <=? n) = (b <=? n).
  apply/idP/idP.
   case E: (N.succ b <=? n) => // _.
   move: E; rewrite N.leb_le //= => E.
   apply N.leb_le; lia.
  case E: (b <=? n) => // _.
  move: E; rewrite N.leb_le //= => /N.lt_eq_cases [E|E].
   apply N.leb_le; lia.
  by elim E1.
 have T2: n-b = 0 <-> n <= b by lia.
 case E2: (cw! (N.succ_pos b)) => [y|]; last first.
  rewrite in_nil /= IH.
  rewrite T1; case E3: (b <=? n) => //=.
  move: E3; rewrite N.leb_le /= => E3.
  case E4: (n-b) => [|nb].
   move: E4; rewrite T2 => E4; elim E1; simpl; lia. 
  by rewrite (HX n b).
 case: (ifP _) => Hb0.
  rewrite in_cons in_nil.
  have ->: (v==y) = false.
   apply/eqP => E; apply E1.
   rewrite E in Hn.
   by apply (condition_wires_inj cw condv y n b Hcondv Hn E2).
  rewrite /= IH -T1.
  case E3: (N.succ b <=? n) => //=.
  move: E3; rewrite N.leb_le /= => E3.
  case E4: (n-b) => [|nb].
   lia.
  by rewrite (HX n b).
 rewrite in_nil IH //= -T1.
 case E3: (N.succ b <=? n) => //=.
 move: E3; rewrite N.leb_le /= => E3.
 case E4: (n-b) => [|nb].
  lia.
 by rewrite (HX n b).
replace n with (n-0); last by lia.
have: 0 <= n by lia.
rewrite -N.leb_le.
replace (ValCirc.val_is_true (ValCirc.read_wire g (n - 0)))
with (true && ValCirc.val_is_true (ValCirc.read_wire g (n - 0))); last by auto.
by move=> <-. 
Qed.

Lemma pcond_cond_eval condv localv g g' cw pc guard:
wire_of_condition_wires cw = Some condv ->
match_grid_local localv g g' ->
is_renamed condv localv (sizeN g) pc guard ->
exists vars_val,
conn_eval g' (conn_guard guard) = Some vars_val
/\ eval_guard guard (vars_val) = (eval_pcond (ValCirc.get_path_model g cw) pc,[::]).
Proof.
move=> Hcw Hlocal; elim: pc guard => //=.
 move=> b guard ->.
 exists [::]; rewrite /conn_eval /conn_guard /=; split => //.
 by case: b.
move=> v l IHl r IHr guard [n [v' [l' [r' [H1 [H2 [H3 [H4 [H5 E]]]]]]]]]. 
move: (Hlocal _ _ _ H3 H1) => [bbits].
rewrite /read_wire; move => [X1 X2]. 
move: (IHl l' H4) => [bitsl [Hl1 Hl2]].
move: (IHr r' H5) => [bitsr [Hr1 Hr2]].
exists ((take_dflt false 1 bbits)++bitsl++bitsr).
have Ecg: conn_guard (Node v' l' r')
          = [:: (N.pos v',0)] ++ (conn_guard l') ++ (conn_guard r'). 
 by rewrite /conn_guard /= map_cat /=.
have: exists b, bbits = [:: b].
 move: bbits X1 X2 (conn_eval_isS_sizeN X1) => [|b [| b' bs]] //= X1 X2.
 by exists b=> //.
move=> [b Eb]; subst.
have L: conn_eval g' (conn_guard (Node v' l' r'))
        = Some ((take_dflt false 1 [:: b])++ bitsl ++ bitsr).
 rewrite Ecg. 
 apply conn_eval_cat.
  by rewrite /zero_ext' /=. 
 by apply conn_eval_cat.
split => //=.
have T1: (size (bdt_vars l') <= size bitsl)%N.
 move: (conn_eval_isS_sizeN Hl1).
 rewrite !sizeN_size => /Nat2N.inj <-.
 by rewrite /conn_guard size_map.
move: (eval_guard_cat bitsr T1 Hl2) => [_ ->] /=.
rewrite Hr2.
have ->: b = (v \in ValCirc.get_path_model g cw).
 move: X2; rewrite /match_val.
 rewrite /ValCirc.get_path_model /=; move => [->].
 symmetry; eapply mem_get_path_model; eauto.
by case: (ifP _).
Qed.

Lemma match_grid_upd_globv_noguard globvi globvf localv sp ssz g m g' i conn newconn cbits:
 is_localv localv (sizeN g) None (sizeN g') ->
 globvi ! (Pos.succ i) = Some conn ->
 conn_eval g' conn = Some cbits ->
 globv_upd_spec globvi (Pos.succ i) newconn globvf ->
 match_grid localv globvi sp ssz g m g' ->
 conn_eval (rcons g' cbits) newconn = Some cbits ->
 match_grid localv globvf sp ssz (rcons g Values.Vundef) m (rcons g' cbits).
Proof.
move=> Hlocalv Hc EVc [x [H1 [H2 H3]]] [Mlocal [Mglob Mconst]] EVc'.
repeat split.
- (* match_local *)
move=> w oty gn Hw Hsz.
move: Hsz; rewrite -cats1 sizeN_size size_cat Nat2N.inj_add /= -sizeN_size.
rewrite N.add_1_r N.lt_succ_r N.lt_eq_cases; move => [Hsz|Hsz]; last first.
 by subst; move: (is_localv_inj Hlocalv Hw) => [E1 _]; inv E1.
move: (Mlocal w oty gn Hw Hsz) => [bs [Hread Hmatch]].
exists bs; split.
 rewrite read_wire_rcons //.
 by eauto using read_wire_lt.
rewrite /ValCirc.read_wire ValCirc.nth_app.
case: (ifP _); first by [].
by move: Hsz; rewrite sizeN_nlen N.ltb_nlt.
- (* match_global *)
move: Mglob => [bstk [Hbstk [Mstk Mglob]]].
exists bstk; split => //.
split.
 move=> sinfo Hs; apply match_block_add_right.
 apply Mstk => //.
 move: Hs; rewrite H3 PTree.gso //; lia.
move=> v vinfo.
case E: (v==i).
 rewrite (eqP E) H3 PTree.gss => [[Ec]]; subst.
 move: (Mglob _ _ Hc) => [b [gv [Mb MM]]].
 exists b, gv; split; last by [].
 move: Mb => [HH1 HH2 HH3 [mbs [bs [HH4 [HH5 HH6]]]]].
 constructor => //.
  by rewrite (conn_eval_isS_sizeN EVc') -(conn_eval_isS_sizeN EVc).
 exists mbs, bs; repeat split; auto.
 by rewrite EVc' -EVc.
rewrite H3 PTree.gso; last first.
 by move=> /Pos.succ_inj X; move: E; rewrite X eq_refl.
move=> Hv; move: (Mglob _ _ Hv) => [b [gv [Mb MM]]].
exists b, gv; split; last by [].
by apply match_block_add_right.
- (* match_const *)
by rewrite /match_grid_const -cats1; apply onthN_isS_cat, Mconst.  
Qed.

Lemma match_grid_upd_stack_noguard globvi globvf localv sp ssz g m g' conn newconn cbits:
 is_localv localv (sizeN g) None (sizeN g') ->
 globvi ! xH = Some conn ->
 conn_eval g' conn = Some cbits ->
 globv_upd_spec globvi xH newconn globvf ->
 match_grid localv globvi sp ssz g m g' ->
 conn_eval (rcons g' cbits) newconn = Some cbits ->
 match_grid localv globvf sp ssz (rcons g Values.Vundef) m (rcons g' cbits).
Proof.
move=> Hlocalv Hc EVc [x [H1 [H2 H3]]] [Mlocal [Mglob Mconst]] EVc'.
repeat split.
- (* match_local *)
move=> w oty gn Hw Hsz.
move: Hsz; rewrite -cats1 sizeN_size size_cat Nat2N.inj_add /= -sizeN_size.
rewrite N.add_1_r N.lt_succ_r N.lt_eq_cases; move => [Hsz|Hsz]; last first.
 by subst; move: (is_localv_inj Hlocalv Hw) => [E1 _]; inv E1.
move: (Mlocal w oty gn Hw Hsz) => [bs [Hread Hmatch]].
exists bs; split.
 rewrite read_wire_rcons //.
 by eauto using read_wire_lt.
rewrite /ValCirc.read_wire ValCirc.nth_app.
case: (ifP _); first by [].
by move: Hsz; rewrite sizeN_nlen N.ltb_nlt.
- (* match_global *)
move: Mglob => [bstk [Hbstk [Mstk Mglob]]].
exists bstk; split => //.
split.
 move=> sinfo Hs.
 rewrite Hc in H1; inv H1.
 move: (Mstk _ Hc) => [HH1 HH2 HH3 [mbs [bs [HH4 [HH5 HH6]]]]].
rewrite PTree.gss in Hs; inv Hs.
 constructor => //.
  by rewrite -H2.
 exists mbs, bs; repeat split => //.
 by rewrite -HH5 EVc.
move=> gv c.
rewrite H3 PTree.gso; last lia.
move=> Hgv; move: (Mglob _ _ Hgv). 
move=> [b [gv' [HH1 HH2]]].
exists b, gv'; split => //.
by apply match_block_add_right.
- (* match_const *)
by rewrite /match_grid_const -cats1; apply onthN_isS_cat, Mconst.  
Qed.

Lemma match_bytes_Vundef chunk bs:
  chunk_not_any chunk ->
  match_bytes (encode_val chunk Values.Vundef) (takeN_dflt Byte.zero (sizeN_chunk chunk) bs).
Proof.
by move: chunk bs => [| | | | | | | | |] [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 ?]]]]]]]];
rewrite takeN_take_dflt //=.
Qed.

Lemma match_bytes_Vint chunk i:
 chunk_not_any chunk ->
 match_bytes (encode_val chunk (Values.Vint i))
             (takeN_dflt Byte.zero (sizeN_chunk chunk) (encode_int 4 (Int.unsigned i))).
Proof.
by move: chunk => [| | | | | | | | |] //= _;
rewrite /encode_int /rev_if_be /Archi.big_endian takeN_take_dflt /= !eq_refl.
Qed.

Lemma match_bytes_Vlong chunk i:
 chunk_not_any chunk ->
 match_bytes (encode_val chunk (Values.Vlong i))
             (takeN_dflt Byte.zero (sizeN_chunk chunk) (encode_int 8 (Int64.unsigned i))).
Proof.
by move: chunk => [| | | | | | | | |] //= _;
rewrite /encode_int /rev_if_be /Archi.big_endian takeN_take_dflt /= !eq_refl.
Qed.

Lemma match_bytes_Vfloat chunk f:
 chunk_not_any chunk ->
 match_bytes (encode_val chunk (Values.Vfloat f))
             (takeN_dflt Byte.zero (sizeN_chunk chunk)
                         (encode_int 8 (Int64.unsigned (Floats.Float.to_bits f)))).
Proof.
by move: chunk => [| | | | | | | | |] //= _;
rewrite /encode_int /rev_if_be /Archi.big_endian takeN_take_dflt /= !eq_refl.
Qed.

Lemma match_bytes_Vsingle chunk f:
 chunk_not_any chunk ->
 match_bytes (encode_val chunk (Values.Vsingle f))
             (takeN_dflt Byte.zero (sizeN_chunk chunk)
                         (encode_int 4 (Int.unsigned (Floats.Float32.to_bits f)))).
Proof.
by move: chunk => [| | | | | | | | |] //= _;
rewrite /encode_int /rev_if_be /Archi.big_endian takeN_take_dflt /= !eq_refl.
Qed.

Lemma match_val_bytes chunk v bs:
 chunk_not_any chunk ->
 match_val_ty v (bits_of_bytes bs) ->
 match_bytes (encode_val chunk v) (takeN_dflt Byte.zero (sizeN_chunk chunk) bs).
Proof.
move: v chunk bs => [|i|i|f|f|b o] //.
- (* Vundef *)
  by move => chunk bs H _; apply match_bytes_Vundef.
- (* Vint *)
  rewrite /match_val_ty; move => chunk bs // Hchunk
  /bytes_of_bits_of_int32 ->.
  by apply match_bytes_Vint.
- (* Vlong *)
  rewrite /match_val_ty; move => chunk bs // Hchunk
  /bytes_of_bits_of_int64 ->.
  by apply match_bytes_Vlong.
- (* Vfloat *)
  rewrite /match_val_ty; move => chunk bs // Hchunk
  /bytes_of_bits_of_int64 ->.
  by apply match_bytes_Vfloat.
- (* Vsingle *)
  rewrite /match_val_ty; move => chunk bs // Hchunk
  /bytes_of_bits_of_int32 ->.
  by apply match_bytes_Vsingle.
Qed.

Lemma nseq_addn A n1 n2 (x:A):
 nseq (n1+n2) x = nseq n1 x ++ nseq n2 x.
Proof. by elim n1 => //= n ->. Qed.
Lemma bits_of_bytes_nseq0 n:
 bits_of_bytes (nseq n Byte.zero) = nseq (8*n) false.
Proof.
elim: n => // n IH.
rewrite [nseq _ _]/= [bits_of_bytes _]/= IH.
have ->: (8*n.+1 = 8 + 8*n)%N.
 by rewrite -multE -plusE; lia.
by rewrite nseq_addn; f_equal.
Qed.

Lemma bits_of_bytes_zero_extN n bs:
 bits_of_bytes (takeN_dflt Byte.zero n bs) = zero_extN (8*n) (bits_of_bytes bs).
Proof.
rewrite /zero_extN ?takeN_take_dflt ?take_dflt_split bits_of_bytes_cat.
rewrite -takeN_take bits_of_bytes_takeN; f_equal.
 by rewrite takeN_take; f_equal.
rewrite bits_of_bytes_nseq0; f_equal.
by rewrite size_bits_of_bytes N2Nat.inj_mul mulnBr; f_equal.
Qed.

Lemma match_grid_upd_globv_guard globvi globvf localv sp ssz 
                                g m g' m' i chunk b off value conn
                                ibits obits srcbits srcbs:
 chunk_not_any chunk ->
 is_localv localv (sizeN g) None (sizeN g') ->
 globvi ! (Pos.succ i) = Some conn ->
 conn_eval g' conn = Some ibits ->
 match_grid localv globvi sp ssz g m g' ->
 globv_upd_spec globvi (Pos.succ i) (conn_new (sizeN g') 0 (sizeN conn)) globvf ->
 Genv.find_symbol (Genv.globalenv p) i = Some b ->
 match_val_ty value srcbits -> 
 srcbits = bits_of_bytes srcbs ->
 Mem.storev chunk m (Values.Vptr b off) value = Some m' ->
 obits = updprefAtN (8*N_of_int off) ibits (zero_extN' false (8*sizeN_chunk chunk) (bits_of_bytes srcbs)) ->
 match_grid localv globvf sp ssz (rcons g Values.Vundef) m' (rcons g' obits).
Proof.
move=> Hchunk Hlocalv Hc EVc [Mlocal [Mglob Mconst]] [x].
rewrite Hc; move=> [[<-] [Hsz_newconn Hgm]] Hb Mv Esrcbits
      Hstore Eobits.
repeat split.
- (* match_local *)
move=> w oty gn Hw Hsz.
move: Hsz; rewrite -cats1 sizeN_size size_cat Nat2N.inj_add /= -sizeN_size.
rewrite N.add_1_r N.lt_succ_r N.lt_eq_cases; move => [Hsz|Hsz]; last first.
 by subst; move: (is_localv_inj Hlocalv Hw) => [E1 _]; inv E1.
move: (Mlocal w oty gn Hw Hsz) => [bs [Hread Hmatch]].
exists bs; split.
 rewrite read_wire_rcons //.
 by eauto using read_wire_lt.
rewrite /ValCirc.read_wire ValCirc.nth_app.
case: (ifP _); first by [].
by move: Hsz; rewrite sizeN_nlen N.ltb_nlt.
- (* match_global *)
move: Mglob => [bstk [Hbstk [Mstk Mglob]]].
move: (Mglob _ _ Hc) => [b' [gv]].
rewrite Hb; move => [Mb' [Hvol [[Eb'] [Eb Hfind]]]]; subst.
exists bstk; split => //.
split.
 move=> sinfo Hs; apply match_block_add_right.
 apply (match_block_storev_other Hstore) => //.
 apply Mstk => //.
 move: Hs; rewrite PTree.gso //; lia.
move=> v vinfo.
case E: (v==i).
 rewrite (eqP E) PTree.gss => [[Ec]]. subst.
 exists b', gv; split; last repeat split => //.
 eapply match_block_storev_globv_same; eauto.
  apply match_val_bytes; auto. apply Mv.
 f_equal.
 by rewrite bits_of_bytes_zero_extN.
rewrite PTree.gso; last first.
 by move=> /Pos.succ_inj X; move: E; rewrite X eq_refl.
move=> Hv; move: (Mglob _ _ Hv) => [b'' [gv'' [Mb'']]].
move=> [Mvol [Mfind'' [Mbstk'' Mgv'']]].
exists b'', gv''; split; last by [].
apply match_block_add_right.
eapply match_block_storev_other; eauto.
move: E; rewrite eq_sym => /eqP E.
eapply Genv.global_addresses_distinct; eauto.
- (* match_const *)
by rewrite /match_grid_const -cats1; apply onthN_isS_cat, Mconst.  
Qed.


Lemma match_grid_upd_stack_guard globvi globvf localv bstk ssz 
                                g m g' m' chunk off value conn
                                ibits obits srcbits srcbs:
 chunk_not_any chunk ->
 is_localv localv (sizeN g) None (sizeN g') ->
 globvi ! xH = Some conn ->
 conn_eval g' conn = Some ibits ->
 match_grid localv globvi (Values.Vptr bstk Int.zero) ssz g m g' ->
 globv_upd_spec globvi xH (conn_new (sizeN g') 0 (sizeN conn)) globvf ->
 match_val_ty value srcbits -> 
 srcbits = bits_of_bytes srcbs ->
 Mem.storev chunk m (Values.Vptr bstk off) value = Some m' ->
 obits = updprefAtN (8*N_of_int off) ibits (zero_extN' false (8*sizeN_chunk chunk) (bits_of_bytes srcbs)) ->
 match_grid localv globvf (Values.Vptr bstk Int.zero) ssz (rcons g Values.Vundef) m' (rcons g' obits).
Proof.
move=> Hchunk Hlocalv Hc EVc [Mlocal [Mglob Mconst]] [x] [Hc_stk [Hc_sz Hgf]].
repeat split.
- (* match_local *)
move=> w oty gn Hw Hsz.
move: Hsz; rewrite -cats1 sizeN_size size_cat Nat2N.inj_add /= -sizeN_size.
rewrite N.add_1_r N.lt_succ_r N.lt_eq_cases; move => [Hsz|Hsz]; last first.
 by subst; move: (is_localv_inj Hlocalv Hw) => [E1 _]; inv E1.
move: (Mlocal w oty gn Hw Hsz) => [bs [Hread Hmatch]].
exists bs; split.
 rewrite read_wire_rcons //.
 by eauto using read_wire_lt.
rewrite /ValCirc.read_wire ValCirc.nth_app.
case: (ifP _); first by [].
by move: Hsz; rewrite sizeN_nlen N.ltb_nlt.
- (* match_global *)
move: Mglob => [bstk' [[<-] [Mstk Mglob]]].
exists bstk; split => //.
split.
 move=> sinfo Hs.
 move: {Mglob} (Mstk _ Hc_stk)=> [HH1 HH2 HH3 [mbs [bs [HH4 [HH5 HH6]]]]].
 rewrite Hc in Hc_stk; inv Hc_stk.
 rewrite PTree.gss in Hs; inv Hs.
 eapply match_block_storev_globv_same; eauto.
  by apply match_val_bytes, H.
 f_equal.
 by rewrite bits_of_bytes_zero_extN.
move=> gv c.
rewrite Hgf PTree.gso; last lia.
move=> Hgv; move: (Mglob _ _ Hgv). 
move=> [b' [gv' [HH1 [HH2 [HH3 [HH4 HH5]]]]]].
exists b', gv'; split => //.
apply match_block_add_right.
eapply match_block_storev_other; eauto.
- (* match_const *)
by rewrite /match_grid_const -cats1; apply onthN_isS_cat, Mconst.  
Qed.

Lemma takeN_dflt_takeN A d n (s: seq A):
 n <= sizeN s -> takeN_dflt d n s = takeN n s.
Proof.
rewrite takeN_take_dflt takeN_take sizeN_size -{1}(N2n2N n) -n2N_le.
elim: {n} (N2n n) s => //=.
 by move=> s; rewrite take0.
move=> n IH [|x xs] //= /leP Hsz; f_equal; apply IH; apply/leP; lia.
Qed.

Lemma sizeN_chunk_ty chunk:
  8*sizeN_chunk chunk <= wires_of_type (type_of_chunk chunk).
Proof. by destruct chunk; rewrite /sizeN_chunk /wires_of_type. Qed.


Lemma localv_conn_list_match_val g g' localv args wargs abits:
 all_lt (sizeN g) args ->
 match_grid_local localv g g' ->
 localv_conn_list localv args wargs ->
 conn_eval g' wargs = Some abits ->
 match_val_list (ValCirc.read_wires g args) abits.
Proof.
move=> LT Mlocal Hargs.
  assert (∃ argbits, conn_eval g' wargs = Some (flatten argbits) ∧
                     Forall2 match_val_ty (ValCirc.read_wires g args) argbits).
  {
    clear - Hargs Mlocal LT. revert wargs Hargs LT.
    elim args; clear - Mlocal.
    - intros ? -> _. exists nil. apply (conj Logic.eq_refl). constructor.
    - intros a args IH ? (w & wargs & -> & Haw & REC) LT.
      specialize (IH _ REC (λ n H, LT n (or_intror _ H))).
      destruct IH as (argbits & EV & M).
      destruct Haw as (oty & n & H & Hw).
      specialize (Mlocal _ _ _ H (LT _ (or_introl _ Logic.eq_refl))).
      destruct Mlocal as (v' & Ev' & Mv').
      eexists (v' :: argbits). split.
      simpl. apply conn_eval_cat.
      destruct oty; subst w; exact Ev'.
      exact EV.
      constructor; auto.
  }
move: H {LT Mlocal Hargs} => [abitsl [-> Mabitsl]] [<-].
elim: args abitsl Mabitsl => //=.
 by move=> abitsl H; inv H; constructor.
move=> a args IH argsl H.
apply Forall2_cons_l in H; move: H => [b [bs [-> [H1 /= H2]]]].
constructor => //.
by  apply IH.
Qed.

Definition full_eval_guard g cond :=
 if conn_eval g (conn_guard cond) is Some vars
 then (eval_guard cond vars).1
 else false.

Lemma pcond_cond_full_eval condv localv g g' cw pc guard:
wire_of_condition_wires cw = Some condv ->
match_grid_local localv g g' ->
is_renamed condv localv (sizeN g) pc guard ->
full_eval_guard g' guard = eval_pcond (ValCirc.get_path_model g cw) pc.
Proof.
rewrite /full_eval_guard => Hcw Mlocal Hren.
by move: (pcond_cond_eval Hcw Mlocal Hren) => [vars [-> ->]].
Qed.

Fixpoint get_phi_assoc (localv : PTree.t localv_info) ty g l :=
 if l is (x::xs)
 then if full_eval_guard g x.1
      then if localv ! (x.2) is Some (_,gw)
           then  if conn_eval g (conn_ty ty gw) is Some x
                 then x
                 else bits0 (wires_of_type ty)
           else bits0 (wires_of_type ty)
      else get_phi_assoc localv ty g xs
 else bits0 (wires_of_type ty).

Lemma bits0_nseqN n: bits0 n = nseqN n false.
Proof.
rewrite /bits0 takeN_take_dflt nseqN_nseq.
by elim: (N2n n) => //= n' /= ->.
Qed.

Lemma sizeN_bits0 n: sizeN (bits0 n) = n.
Proof. by rewrite /bits0 sizeN_takeN_dflt. Qed.

Lemma phi_idents_renamed φ φ' condv localv n:
 is_renamed condv localv n φ φ' ->
 phi_idents φ' = phi_idents φ.
Proof.
elim: φ φ' => //=.
 by move=> [x|] phi' ->.
move=> v l IHl r IHr; elim => //=.
 move=> oy //= .
 by move=> [? [? [? [? [_ [_ [_ [_ [_ HH]]]]]]]]]; inv HH.
move=> v' l' _ r' _.
move=> [n0 [v0 [l0 [r0 [H1 [H2 [H3 [H4 [H5 [E1 [E2 E3]]]]]]]]]]]; subst.
by rewrite IHl // (@IHr r0).
Qed.

Lemma flat_phi_renamed φ φ' cw condv localv n x:
 wire_of_condition_wires cw = Some condv ->
 monot_localv localv ->
 is_renamed condv localv n φ φ' ->
 x \in flat_phi_node φ' ->
 (cond_of_phi x.2 φ,x.2) \in flat_phi_node φ /\ is_renamed condv localv n (cond_of_phi x.2 φ) x.1.
Proof.
move=> Hcw Hmon Hren /mapP [y].
rewrite (phi_idents_renamed Hren) => Hin -> /=; split; first by apply: map_f.
by apply: is_renamed_cond_of_phi.
Qed.

Lemma conn_eval_isS_subgrid g g' c x:
 conn_eval g c = Some x -> conn_eval (g++g') c = Some x.
Proof.
elim: g' g.
 by move=> g H; rewrite cats0.
move=> y ys IH g H.
by rewrite -cat1s catA cats1; apply IH, conn_eval_rcons.
Qed.

Lemma sizeN_get_phi_assoc localv ty g l: sizeN (get_phi_assoc localv ty g l) = wires_of_type ty.
Proof.
move: (sizeN_bits0 (wires_of_type ty)) => T.
elim: l=> //=.
move=> [c v] l IH; case: (ifP _) => _ //=.
case: (localv ! v) => //.
move=> [? gw].
case E: (conn_eval g (conn_ty ty gw)) => [x|] //.
by apply conn_eval_isS_sizeN in E; rewrite -E sizeN_conn_ty.
Qed.

Lemma size_zipWith f xs ys: size (zipWith f xs ys) = min (size xs) (size ys).
Proof.
elim: xs ys => //= x xs IH; elim => //= => y ys _.
by f_equal; apply IH.
Qed.

Lemma sizeN_xor_bits xs ys: sizeN xs = sizeN ys -> sizeN (xor_bits xs ys) = sizeN xs.
Proof.
rewrite /xor_bits ?sizeN_size size_zipWith Nat2N.inj_min -!sizeN_size => ->.
by apply N.min_id.
Qed.

Lemma subseq_cons_s {A:eqType} (x:A) xs ys:
 subseq (x::xs) ys -> subseq xs ys.
Proof.
elim: ys x xs => // y ys IH x xs.
rewrite [subseq (_::_) (_::_)]/=; case: (ifP _) => /eqP E Hsub.
 apply: subseq_trans; last by apply subseq_cons.
 by apply Hsub.
apply IH in Hsub; apply: subseq_trans; last by apply subseq_cons.
by apply Hsub.
Qed.

Lemma flat_phi_nodeE φ x:
 x\in flat_phi_node φ -> x.1 = cond_of_phi x.2 φ.
Proof. by move=> /mapP [vv [Hvv1 ->]] /=. Qed.

Lemma in_flat_phi_node v φ:
 ((cond_of_phi v φ, v) \in flat_phi_node φ) = (v \in phi_idents φ).
Proof. by rewrite /flat_phi_node mem_map // => x y [_ ->]. Qed.

Lemma phi_idents_flat_phi φ: phi_idents φ = map snd (flat_phi_node φ).
Proof. by rewrite /flat_phi_node mapK. Qed.

Lemma subseq_flat_phiNode_renamed cw condv localv g φ φ' g' x xs:
 wire_of_condition_wires cw = Some condv ->
 monot_localv localv ->
 is_renamed condv localv (sizeN g) φ φ' ->
 match_grid_local localv g g' ->
 subseq (x::xs) (flat_phi_node φ') ->
 full_eval_guard g' x.1 ->
 forall y2, y2\in map snd xs -> full_eval_guard g' (cond_of_phi y2 φ') = false.
Proof.
move=> Hcw Hmon Hren Mlocal Hsub; move: (Hsub) => /(map_subseq snd) Hsub2 EV.
have: uniq (map snd (flat_phi_node φ')).
 by rewrite /flat_phi_node -map_comp /funcomp /= map_id uniq_phi_idents.
move=> /(subseq_uniq Hsub2) /= /andP [Hnin Huniq].
move: EV; rewrite (@flat_phi_nodeE φ'); last first.
 by apply: (mem_subseq Hsub); rewrite in_cons; apply/orP; left.
erewrite pcond_cond_full_eval; eauto; last by eapply is_renamed_cond_of_phi; eauto.
move=> EV y H /=.
erewrite pcond_cond_full_eval; eauto; last by eapply is_renamed_cond_of_phi; eauto.
case X: (eval_pcond (ValCirc.get_path_model g cw) (cond_of_phi y φ)) => //.
have: (cond_of_phi x.2 φ,x.2).2 = (cond_of_phi y φ,y).2.
 apply: (@flat_phiNodeP φ (cond_of_phi x.2 φ,x.2) _ (ValCirc.get_path_model g cw)) => //.
  rewrite in_flat_phi_node -(@phi_idents_renamed _ φ' _ _ _ Hren) phi_idents_flat_phi.
  by apply: (mem_subseq Hsub2); rewrite in_cons; apply/orP; left.
 rewrite in_flat_phi_node -(@phi_idents_renamed _ φ' _ _ _ Hren) phi_idents_flat_phi.
 by apply: (mem_subseq Hsub2); rewrite in_cons; apply/orP; right.
by move=> /= E; move/negP: Hnin; elim; rewrite E.
Qed.


Lemma nsucc_pospred: forall p, N.succ_pos (Pos.pred_N p) = p.
Proof.
move=> x.
have E: N.pos (N.succ_pos (Pos.pred_N x)) = N.pos x.
 by rewrite N.succ_pos_spec N.succ_pos_pred.
by injection E.
Qed.

Lemma get_phi_assoc_tailP cw condv localv g φ φ' g' ty:
 wire_of_condition_wires cw = Some condv ->
 monot_localv localv ->
 is_renamed condv localv (sizeN g) φ φ' ->
 match_grid_local localv g g' ->
 forall c' cv' gw l code,
 is_localv localv (Pos.pred_N cv') (Some (Some ty)) gw ->
 Pos.pred_N cv' < sizeN g ->
 phi_spec localv (sizeN g) (N.pred (sizeN g')) ty (sizeN code) l code ->
 subseq ((c', cv') :: l) (flat_phi_node φ') ->
 full_eval_guard g' c' ->
 get_phi_assoc localv ty g' l = bits0 (wires_of_type ty).
Proof.
move=> Hcw Hmon Hren Mlocal c' v gw; elim => //.
move=> [c cv] l IH code Hloc Hcv' Hphi Hsub Hguard /=.
have T x: x\in [:: (c', v), (c, cv) & l] -> x.1 = cond_of_phi x.2 φ'.
 by move=> /(mem_subseq Hsub) /mapP [vv [Hvv1 ->]] /=.
have T2: (c', v)\in [:: (c', v), (c, cv) & l].
 by rewrite in_cons eq_refl.
move: {T2} (T (c',v) T2) => /= Hc'.
have T2: (c, cv)\in [:: (c', v), (c, cv) & l].
 by rewrite !in_cons eq_refl orTb orbT.
move: {T2 T} (T (c,cv) T2) => /= Hc.
have Ec': eval_pcond (ValCirc.get_path_model g cw) (cond_of_phi v φ).
 case E: (eval_pcond (ValCirc.get_path_model g cw) (cond_of_phi v φ)) => //.
 move: Hguard; rewrite /full_eval_guard.
 case Eguard: (conn_eval g' (conn_guard c')) => [vars|] // E'.
 move: (is_renamed_cond_of_phi v Hcw Hmon Hren); rewrite -Hc' => Hren_c'.
 move: (pcond_cond_eval Hcw Mlocal Hren_c') E' => [vars']; rewrite Eguard; move=> [[<-]].
 by rewrite E => ->.
 rewrite Hc; erewrite subseq_flat_phiNode_renamed; eauto; first last.
 by rewrite in_cons eq_refl.
have Hsub': subseq [:: (c', v) & l] (flat_phi_node φ').
 apply: (@subseq_trans _ [:: (c', v), (c, cv) & l]); last assumption.
 rewrite -cat1s -[_::_::l]cat1s; apply cat_subseq => //.
 by apply subseq_cons.
inv Hphi; first by [].
move: H4; have ->: n = sizeN code0.
 by move: H; rewrite /=; lia.
by move=> H4; eapply IH; eauto.
Qed.

Lemma cond_of_phiPN pcm phi v:
 eval_phiNode pcm phi = None ->
 eval_pcond pcm (cond_of_phi v phi) = false.
Proof.
elim: phi => //=.
 by move=> [v'|] //; case: (ifP _).
move=> v' l IHl r IHr.
rewrite chkNP; case: (ifP _) => Hin.
 by apply IHl.
by apply IHr.
Qed.

Lemma eval_phiNode_isN cw condv localv (g:ValCirc.grid) phi phi' ty g':
 wire_of_condition_wires cw = Some condv ->
 monot_localv localv ->
 is_renamed condv localv (sizeN g) phi phi' ->
 match_grid_local localv g g' ->
 eval_phiNode (ValCirc.get_path_model g cw) phi = None ->
 get_phi_assoc localv ty g' (flat_phi_node phi') = bits0 (wires_of_type ty).
Proof.
move=> Hcw Hmon Hren Mlocal Hphi.
have: forall v, v\in phi_idents phi' -> 
                  full_eval_guard g' (cond_of_phi v phi') = false.
 move=> v; rewrite (phi_idents_renamed Hren) => Hv.
 move: (is_renamed_cond_of_phi v Hcw Hmon Hren) => Hren'.
 rewrite {Hren'} (pcond_cond_full_eval Hcw Mlocal Hren').
 by apply cond_of_phiPN.
rewrite /flat_phi_node;  elim:(phi_idents phi')=> //=.
move => v l IH H.
rewrite H; last by rewrite in_cons eq_refl.
by apply IH => v' Hv'; apply H; rewrite in_cons; apply/orP; right.
Qed.

Lemma eval_phiNode_isS cw condv localv (g:ValCirc.grid) phi phi'
      ty g' v npos n code:
 wire_of_condition_wires cw = Some condv ->
 monot_localv localv ->
 match_grid_local localv g g' ->
 is_renamed condv localv (sizeN g) phi phi' ->
 phi_spec localv (sizeN g) npos ty n (flat_phi_node phi') code ->
 eval_phiNode (ValCirc.get_path_model g cw) phi = Some v ->
 Pos.pred_N v < sizeN g /\
 exists gn,
 is_localv localv (Pos.pred_N v) (Some (Some ty)) gn /\
 conn_eval g' (conn_ty ty gn) = Some (get_phi_assoc localv ty g' (flat_phi_node phi')).
Proof.
move=> Hcw Hmon Mlocal Hren Hphi EVphi.
move: EVphi (eval_phiNode_idents EVphi) => /cond_of_phiP EV Hv.
move: (Hv); rewrite -!(phi_idents_renamed Hren) {1}phi_idents_flat_phi => HHv.
move: (phi_specP Hphi HHv) => [H1 [gn Hgn]].
split => //; exists gn; split => //.
move: (Mlocal (Pos.pred_N v) (Some ty) gn Hgn H1) => [vbits].
rewrite /read_wire; move => [Evbits Mvbits].
move: (is_renamed_cond_of_phi v Hcw Hmon Hren) => Hren_v.
move: (pcond_cond_full_eval Hcw Mlocal Hren_v); rewrite EV => EV'.
have: forall x, x\in (phi_idents phi') -> full_eval_guard g' (cond_of_phi x phi') = (x==v).
 move=> x xIN; case E: (x==v); first by rewrite (eqP E).
 case EVx: (full_eval_guard g' (cond_of_phi x phi')) => //.
 move: (is_renamed_cond_of_phi x Hcw Hmon Hren) => Hren_x.
 move: (pcond_cond_full_eval Hcw Mlocal Hren_x); rewrite EVx => EVx'.
 move: EVx; rewrite -E; symmetry; apply/eqP.
 change ((cond_of_phi x phi,x).2 = (cond_of_phi v phi,v).2).
 eapply (@flat_phiNodeP phi); eauto.
  by rewrite in_flat_phi_node -(phi_idents_renamed Hren).
 by rewrite in_flat_phi_node.
move: Hv; rewrite -(phi_idents_renamed Hren) /flat_phi_node.
elim: (phi_idents phi') => //=.
move=> x l IH; rewrite in_cons => /orP [/eqP <-|H] HH.
 by move: Hgn; rewrite /is_localv nsucc_pospred=> Hgn; rewrite EV' Hgn Evbits.
case EE: (x==v).
 rewrite (eqP EE).
 by move: Hgn; rewrite /is_localv nsucc_pospred=> Hgn; rewrite EV' Hgn Evbits.
move: (HH x); rewrite EE => ->; last by rewrite in_cons eq_refl.
by apply IH => // x' Hx'; apply HH; rewrite in_cons; apply/orP; right.
Qed.

Theorem simulation :
  forward_simulation (ValCirc.semantics p) (HLCirc.semantics p').
Proof.
refine (forward_simulation_plus (ValCirc.semantics p) (HLCirc.semantics p')
                                (Genv.public_symbol_transf_partial _ _ TR)
                                match_state
                                _ _ _).
- intros ? (m & b & f & Hm & Hb & Hf & ->).
  rewrite <- (Genv.find_symbol_transf_partial _ _ TR) in Hb.
  rewrite <- (transform_partial_program_main _ _ TR) in Hb.
  destruct (Genv.find_funct_ptr_transf_partial _ _ TR _ Hf) as (f' & Hf' & Hff').
  simpl in Hff'. destruct (translate_function _ _) as [ tf | e ] eqn: Htf; inv Hff'.
  eexists. split.
  eexists b, _, _.
  apply (conj Hb).
  apply (conj Hf').
  split. unfold initmem_globs. rewrite collect_globals_transf. reflexivity.
  reflexivity.
  simpl.
  exists tf; split; [assumption|].
  by split.

- intros ? ? ? M (-> & ->). split; easy.

- intros (); simpl.
 + (* InitState -> InputState None *)
   intros f m tr s'.
   destruct (Mem.alloc _ _ _) as (m', sp) eqn: Hm'.
   intros (-> & ->) s2 (f' & Hf' & Hinit & ->).
   apply translate_function_correct in Hf'. hsplit.
   eexists. split.
    apply plus_one. simpl.
    split. reflexivity.
    split. reflexivity.
    split. reflexivity.
    split.
     erewrite proc_outputs_spec_size by eassumption.
     by rewrite sizeN_map.
    reflexivity.
   simpl.
   eexists _, localv, _, _, _, _, nil, _, _, _.
   split. eassumption.
   split; [ erewrite N.mul_0_l; reflexivity |].
   split.
    by simpl; apply H0.
   split; [| split; [| split; [eassumption|reflexivity]]].
    simpl.
    rewrite /= sizeN_globs_initdata  -N.add_1_l N.add_assoc; assumption.
   by apply match_grid_global_initial_grid with m; auto.

 + intros [ ((x, o), v) | ] ins sp ssz cw body m outs tr s'.
    (* InputState (Some v) -> *)
    intros (-> & m' & Hm' & ->) s2 M.
    destruct M as (var & condv & localv & globvc & globvi & globvf & nin & inp & globs & body' & oc & M).
    destruct M as (Hcw & Hnin & (c & Hc & Hinp) & Hcode & M & Hout & ->).
    eexists.
    split.
     by apply plus_one; simpl; eauto.
    simpl; exists condv, localv.
    exists (Maps.PTree.set (Pos.succ x)
                (conn_upd_at c (8 * N_of_int o) (conn_new 1 (nin * 8) 8)) globvc).
    eexists globvi, globvf, (N.succ nin), _, globs, body', oc.
    repeat split; [assumption| |assumption |assumption| |assumption]. 
     by rewrite Nmult_Sn_m sizeN_size size_cat size_sizeN -plusE Nat2N.inj_add
                ?N2n2N Hnin N.add_comm size_bits_of_byte.
    by eapply match_grid_global_add_input; eauto.
   (* InputState None ... *)
   destruct ins as [ | ((x, o), src) ins ].
    (* InputState None nil -> InputFence *)
    intros (-> & ->).
    intros ? (condv & localv & globvc & globvi & globvf & nin & inp & globs & body' & oc & M).
    destruct M as (Hcw & Hnin & Hins & Hcode & M & Hout & ->).
    eexists; split.
     by apply plus_one; simpl; eauto.
    simpl; simpl in Hins; subst.
    exists condv, localv, globvc, globvf, inp, globs, body', oc.
    split; [assumption|].
    split; [assumption|].
    split.
     split.
      unfold match_grid_local; simpl; intros; elimtype False; lia.
     split; [assumption|].
     unfold fill_grid, match_grid_const; simpl; reflexivity.
    by split; [assumption| reflexivity].
   (* InputState None (_::_) *)
   intros (b & ev & v & V & Hb & -> & Hev & Hv & ->).
   intros ? (condv & localv & globvc & globvi & globvf & nin & inp & globs & body' & oc & M).
   destruct M as (Hcw & Hnin & Hins & Hcode & M & Hout & ->).
   eexists; split.
    apply plus_one; simpl.
    eexists _, _, _.
    split. 
     by rewrite <- V; eapply Genv.block_is_volatile_transf_partial, TR.
    split.
     by rewrite <- Hb; eapply Genv.find_symbol_transf_partial, TR.
    split; first reflexivity.
    split; first by eauto using eventval_valid_transf.
    split; first by eauto using eventval_match_transf.
    reflexivity.
   eexists x, condv, localv, globvc, globvi, globvf, nin, inp, globs, body', oc.
   split; first assumption.
   split; first eassumption.
   split.
    destruct Hins as (c & Hc & Hadd).
    exists c; split; assumption.
   split; first eassumption.
   split; [| split; [assumption| reflexivity]].
   apply match_grid_global_input_increase; assumption.

 + intros sp ssz cw body m outs ? ? (-> & ->).
   intros ? (condv & localv & globvi & globvf & inp & globs & body' & oc & M).
   destruct M as (Hcw & Hcode & M & Hout & ->).
   eexists; split.
    by apply plus_one; simpl; eauto.
   by simpl; eauto 13.

 + intros sp ssz cw body m outs ? ? (-> & ->).
   intros ? (condv & localv & globvi & globvf & inp & globs & body' & oc & M).
   destruct M as (Hcw & Hcode & M & Hout & ->).
   eexists; split. 
    by apply plus_one; simpl; eauto.
   eexists condv, localv, globvi, globvf, body', oc, _.
   split; first assumption.
   split; last by eauto.
   by rewrite /= N.pred_succ -N.add_1_l /grid_of_globconsts sizeN_map.

 + intros sp ssz cw [ | ga body ] g m outs.
    intros ? ? (-> & ->).
    intros ? (condv & localv & globvi & globvf & body' & oc & g' & M).
    destruct M as (Hcw & Hcode & M & Hout & ->).
    destruct Hcode as (-> & ->).
    eexists; split.
     by apply plus_one; simpl; eauto.
    by simpl; destruct M as (? & ? & ?); eauto 8.
   intros tr s'.
   destruct ga as (ga, args).
   intros (-> & v & m' & EV & ->).
   intros ? (condv & localv & globvi & globvf & body' & oc & g' & M).
   destruct M as (Hcw & Hcode & M & Hout & ->).
   destruct Hcode as (ges & gmi & ges' & -> & Hga & Hcode).
   destruct ga as [ op | ϰ addr | pc ϰ addr | pc cnd | φ ]; simpl in Hga.
   destruct (Op.eq_operation _ _).
   { (* Omove *)
     subst.
     destruct Hga as (ge & Hges & -> & r1 & ty & gw & -> & LT & Hr1 & Hg & H).
     apply rev_is_cons in Hges; rewrite appE in Hges. simpl in Hges. subst ges.
     destruct Hg as (Hg & ->).
     destruct EV as (EV & ->).
     rewrite /RTLC.eval_operation /= in EV; subst v.
     destruct (proj1 M _ _ _ Hr1 LT) as (v' & Hv' & Hvv').
     eexists; split.
      eapply plus_one.
      apply (conj Logic.eq_refl).
      unfold read_wire in Hv'.
      unfold gate_eval. simpl.
      by rewrite Hv' /=; eauto.
     simpl; eexists condv, localv, _, _, _, _, _.
     split; first eassumption.
     split; [|split; [| split; [eassumption|reflexivity]]].
      simpl in Hcode.
      rewrite -> sizeN_app, sizeN_rcons, <- N.add_pred_l.
       eassumption.
      by eauto using match_grid_nonempty.
     apply (sizeN_read_wire) in Hv'; unfold wires_of_oty in Hv'. 
     eapply match_grid_add_local; eauto; first last.
       by rewrite takeN_dflt_all'; first exact Hvv'.
      rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt.
      by rewrite N2n2N; reflexivity.
     erewrite N.succ_pred in H; first by assumption.
     by eapply match_grid_nonempty; eassumption.
   }

   { (* Op *)
     destruct Hga as (ge & X & -> & LT & Hge & Hlocal).
     apply rev_is_cons in X; simpl in X; subst ges.
     edestruct (proc_op_spec_gate_eval) as ( xbits & EV' & SZx & Mx); try eassumption.
     destruct EV as [ EV -> ].
     eexists; split.
      eapply plus_one.
      by apply (conj Logic.eq_refl); exists xbits; eauto.
     eexists condv, _, _, _, _, _, _.
     split; first eassumption.
     split; [|split; [| split; [eassumption|reflexivity]]].
      rewrite -> sizeN_app; simpl.
      rewrite <- seq.cats1, sizeN_app, <- N.add_pred_l; first eassumption.
      by eauto using match_grid_nonempty.
     rewrite -> N.succ_pred in Hlocal by (eauto using match_grid_nonempty).
     eapply match_grid_add_local; eauto.
     simpl; congruence.
   }

   { (* Load *)
     destruct Hga as (addr_body & src & s & gconn & ge & gd & Hges & -> & LT & Haddr & Hsrc & Halign & Hload & Hid & Hlocal).
     apply rev_is_cons in Hges; rewrite /= rev_cons -seq.cats1 -catA /= in Hges.
     subst ges; destruct EV as [ EV -> ].
     generalize (match_grid_block (proj1 (proj2 M)) Hsrc).
     intros (b & sz & MB & Hb).
     destruct MB as [ MBv MB MBs (mbs & bs' & Hmbs & Hbs' & MBS) ].
     destruct addr; simpl in Haddr; hsplit;
     unfold add_gate_spec in *; hsplit; simpl in *.
     (* obs: Aindexed, Ascaled and Aindexed2scaled are not supported *)
     { (* Aglobal v i *)
       rewrite is_global_block_succ in Hb.
       destruct Hb as (gv & Hb & Hgv & ->).
       eexists; split.
        econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
         split; first reflexivity.
         eexists; split; last reflexivity.
         rewrite /gate_eval /=; apply omap_isS.
         exists (bits_of_bytes bs'); split; first assumption.
         reflexivity.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        eexists; split; last reflexivity.
        rewrite /gate_eval /= conn_eval_conn_ext; first last.
          by rewrite /conn_new sizeN_map sizeN_iotaN; destruct ϰ; easy.
         by inversion_clear M; hsplit;
             generalize (match_grid_const_is_grid H3);
             rewrite -!cats1; intro HH; apply is_grid_cat; easy.
        rewrite conn_eval_conn_new; last first.
         cutrewrite (N.pred (sizeN g') + 0 + 1 = sizeN g'); last first.
          move: (match_grid_nonempty M); rewrite -N.sub_1_r; lia.
         rewrite nth_rcons_last sizeN_takeN_dflt //; reflexivity.
        apply omap_isS.
        eexists; split; last reflexivity.
        apply omap_isS.
        eexists; split; reflexivity.
       eexists _, _, _, _, _, _, _.
       split; first eassumption.
       split; [|split; [|split; [eassumption|reflexivity]]].
        rewrite sizeN_app ?sizeN_rcons /=.
        replace (N.pred (sizeN g' + 1 + 1)) with (N.pred (sizeN g') + 2).
         eassumption.
        rewrite ! N.pred_sub.
        generalize (match_grid_nonempty M); lia.
       eapply match_grid_add_local.
       - rewrite ! sizeN_rcons.
         replace (sizeN g' + 1) with (N.succ (N.pred (sizeN g') + 0 + 1)).
          exact Hlocal.
         generalize (match_grid_nonempty M).
         rewrite N.pred_sub; lia.
       - by rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt N2n2N.
       - cutrewrite (N.pred (sizeN g') + 0 + 1 = sizeN g'); last first.
          move: (match_grid_nonempty M); rewrite -N.sub_1_r; lia.
         rewrite takeN_all; last first.
          rewrite nth_rcons_last sizeN_takeN_dflt //; reflexivity.
         set (wd := wires_of_type (type_of_chunk ϰ)).
         set (wb := 8 * sizeN_chunk ϰ).
         set (ℓ := sizeN gconn).
         rewrite /RTLC.eval_addressing /= /Genv.symbol_address Hb /= /RTLC.mem_loadv. 
         rewrite nth_rcons_last.
         simpl in *.
         eapply Gselk_correct; eauto.
         by rewrite /wb N.div_mul_cancel_l /sizeN_chunk //; destruct ϰ.
       - repeat apply match_grid_add_right; assumption.
     }
     { (* Abased v i *)
       rewrite is_global_block_succ in Hb.
       destruct Hb as (gv & Hb & Hgv & ->).
       edestruct (proc_op_spec_gate_eval) as (lea & Hlea & Hszlea & EVlea); try eassumption.
        discriminate.
       rewrite /RTLC.eval_operation /= in EVlea.
       eexists; split.
        econstructor; simpl; eauto; last reflexivity.
        eright; simpl; [| |by rewrite (Events.E0_left [::])].
         split; first reflexivity.
         rewrite N.add_1_r N.succ_pred; last by eauto using match_grid_nonempty.
         eexists; split; last reflexivity.
         rewrite /gate_eval /=; erewrite conn_eval_cat; first reflexivity.
          by eauto using conn_eval_rcons.
         rewrite /conn_eval /conn_new omap_all_map /wire_eval /= nth_rcons_last.
         apply omap_all_isS, map_onthN_iotaN.
         rewrite -Hszlea /= /wires_of_type /=.
          by apply pointers_need_no_more_than_32bits, MBs.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        eexists; split; last reflexivity.
        rewrite /gate_eval /= conn_eval_conn_ext; first last.
          by rewrite /conn_new sizeN_map sizeN_iotaN; destruct ϰ; easy.
         by inversion_clear M; hsplit; 
             generalize (match_grid_const_is_grid H4);
             rewrite <- !seq.cats1, <- !seq.catA; intro HH; apply is_grid_cat; easy.
        rewrite conn_eval_conn_new; last first.
         rewrite -!cats1 -catA nthN_cat.
         case: (ifP _) => [/N.ltb_lt E|E]; first lia.
         cutrewrite (sizeN g' + 1 - sizeN g' = 1); [|lia].
         by rewrite /= sizeN_takeN_dflt; reflexivity.
        rewrite /= -!seq.cats1 nthN_cat cats1 sizeN_rcons.
        rewrite -> (proj2 (N.ltb_ge _ _)) by apply N.le_refl.
        by rewrite N.sub_diag /=; reflexivity.
       eexists _, _, _, _, _, _, _.
       split; first eassumption.
       split; [|split; [|split; [eassumption|reflexivity]]].
        rewrite sizeN_app ?sizeN_rcons /=.
        replace (N.pred (sizeN g' + 1 + 1 + 1)) with (N.pred (sizeN g') + 3).
         eassumption.
        rewrite ! N.pred_sub.
        generalize (match_grid_nonempty M); lia.
       eapply match_grid_add_local.
       - rewrite ! sizeN_rcons.
         replace (sizeN g' + 1 + 1) with (N.succ (N.pred (sizeN g') + 1 + 1)).
          exact Hlocal.
         generalize (match_grid_nonempty M).
         rewrite N.pred_sub; lia.
       - by rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt N2n2N.
       - rewrite takeN_all; last first.
          rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt N2n2N.
          by apply N.le_refl.
         set (wd := wires_of_type (type_of_chunk ϰ)).
         set (wb := 8 * sizeN_chunk ϰ).
         set (ℓ := sizeN gconn).
         rewrite /RTLC.eval_addressing /= /Genv.symbol_address Hb /=.
         destruct (ValCirc.read_wire _ _); try exact I.
         unfold RTLC.mem_loadv. 
         simpl in *.
         eapply Gsel_correct; eauto.
          rewrite takeN_take take_size_cat //.
          by rewrite /ℓ (conn_eval_isS_sizeN Hbs') size_sizeN.
         rewrite !takeN_take ?dropN_drop drop_size_cat; last first. 
          by rewrite /ℓ (conn_eval_isS_sizeN Hbs') size_sizeN.
         f_equal.
          rewrite /wb /ℓ (conn_eval_isS_sizeN Hbs') sizeN_bits_of_bytes.
          f_equal; f_equal.
          by rewrite -(all2_sizeN MBS) (loadbytes_isS_sizeN Hmbs).
         by rewrite EVlea Int.add_commut.
       - repeat apply match_grid_add_right; assumption.
     }
     { (* Abasedscaled v i0 i1 *)  
       rewrite is_global_block_succ in Hb.
       destruct Hb as (gv & Hb & Hgv & ->).
       edestruct (proc_op_spec_gate_eval) as (lea & Hlea & Hszlea & EVlea); try eassumption.
        discriminate.
       rewrite /RTLC.eval_operation /= in EVlea.
       eexists; split.
        econstructor; simpl; eauto; last reflexivity.
        eright; simpl; [| |by rewrite (Events.E0_left [::])].
         split; first reflexivity.
         rewrite N.add_1_r N.succ_pred; last by eauto using match_grid_nonempty.
         eexists; split; last reflexivity.
         rewrite /gate_eval /=; erewrite conn_eval_cat; first reflexivity.
          by eauto using conn_eval_rcons.
         rewrite /conn_eval /conn_new omap_all_map /wire_eval /= nth_rcons_last.
         apply omap_all_isS, map_onthN_iotaN.
         rewrite -Hszlea /= /wires_of_type /=.
          by apply pointers_need_no_more_than_32bits, MBs.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        eexists; split; last reflexivity.
        rewrite /gate_eval /= conn_eval_conn_ext; first last.
          by rewrite /conn_new sizeN_map sizeN_iotaN; destruct ϰ; easy.
         by inversion_clear M; hsplit; 
             generalize (match_grid_const_is_grid H4);
             rewrite <- !seq.cats1, <- !seq.catA; intro HH; apply is_grid_cat; easy.
        rewrite conn_eval_conn_new; last first.
         rewrite -!cats1 -catA nthN_cat.
         case: (ifP _) => [/N.ltb_lt E|E]; first lia.
         cutrewrite (sizeN g' + 1 - sizeN g' = 1); [|lia].
         by rewrite /= sizeN_takeN_dflt; reflexivity.
        rewrite /= -!seq.cats1 nthN_cat cats1 sizeN_rcons.
        rewrite -> (proj2 (N.ltb_ge _ _)) by apply N.le_refl.
        by rewrite N.sub_diag /=; reflexivity.
       eexists _, _, _, _, _, _, _.
       split; first eassumption.
       split; [|split; [|split; [eassumption|reflexivity]]].
        rewrite sizeN_app ?sizeN_rcons /=.
        replace (N.pred (sizeN g' + 1 + 1 + 1)) with (N.pred (sizeN g') + 3).
         eassumption.
        rewrite ! N.pred_sub.
        generalize (match_grid_nonempty M); lia.
       eapply match_grid_add_local.
       - rewrite ! sizeN_rcons.
         replace (sizeN g' + 1 + 1) with (N.succ (N.pred (sizeN g') + 1 + 1)).
          exact Hlocal.
         generalize (match_grid_nonempty M).
         rewrite N.pred_sub; lia.
       - by rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt N2n2N.
       - rewrite takeN_all; last first.
          rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt N2n2N.
          by apply N.le_refl.
         set (wd := wires_of_type (type_of_chunk ϰ)).
         set (wb := 8 * sizeN_chunk ϰ).
         set (ℓ := sizeN gconn).
         rewrite /RTLC.eval_addressing /= /Genv.symbol_address Hb /=.
         destruct (ValCirc.read_wire _ _); try exact I.
         unfold RTLC.mem_loadv. 
         simpl in *.
         eapply Gsel_correct; eauto.
          rewrite takeN_take take_size_cat //.
          by rewrite /ℓ (conn_eval_isS_sizeN Hbs') size_sizeN.
         rewrite !takeN_take ?dropN_drop drop_size_cat; last first. 
          by rewrite /ℓ (conn_eval_isS_sizeN Hbs') size_sizeN.
         f_equal.
          rewrite /wb /ℓ (conn_eval_isS_sizeN Hbs') sizeN_bits_of_bytes.
          f_equal; f_equal.
          by rewrite -(all2_sizeN MBS) (loadbytes_isS_sizeN Hmbs).
         by rewrite EVlea Int.add_commut.
       - repeat apply match_grid_add_right; assumption.
     }
     { (* Ainstack i *)
       destruct Hb; subst.
       eexists; split.
        econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
         split; first reflexivity.
         eexists; split; last reflexivity.
         rewrite /gate_eval /=; apply omap_isS.
         exists (bits_of_bytes bs'); split; first assumption.
         reflexivity.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        eexists; split; last reflexivity.
        rewrite /gate_eval /= conn_eval_conn_ext; first last.
          by rewrite /conn_new sizeN_map sizeN_iotaN; destruct ϰ; easy.
         by inversion_clear M; hsplit;
             generalize (match_grid_const_is_grid H3);
             rewrite -!cats1; intro HH; apply is_grid_cat; easy.
        rewrite conn_eval_conn_new; last first.
         cutrewrite (N.pred (sizeN g') + 0 + 1 = sizeN g'); last first.
          move: (match_grid_nonempty M); rewrite -N.sub_1_r; lia.
         rewrite nth_rcons_last sizeN_takeN_dflt //; reflexivity.
        apply omap_isS.
        eexists; split; last reflexivity.
        apply omap_isS.
        eexists; split; reflexivity.
       eexists _, _, _, _, _, _, _.
       split; first eassumption.
       split; [|split; [|split; [eassumption|reflexivity]]].
        rewrite sizeN_app ?sizeN_rcons /=.
        replace (N.pred (sizeN g' + 1 + 1)) with (N.pred (sizeN g') + 2).
         eassumption.
        rewrite ! N.pred_sub.
        generalize (match_grid_nonempty M); lia.
       eapply match_grid_add_local.
       - rewrite ! sizeN_rcons.
         replace (sizeN g' + 1) with (N.succ (N.pred (sizeN g') + 0 + 1)).
          exact Hlocal.
         generalize (match_grid_nonempty M).
         rewrite N.pred_sub; lia.
       - by rewrite sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt N2n2N.
       - cutrewrite (N.pred (sizeN g') + 0 + 1 = sizeN g'); last first.
          move: (match_grid_nonempty M); rewrite -N.sub_1_r; lia.
         rewrite takeN_all; last first.
          rewrite nth_rcons_last sizeN_takeN_dflt //; reflexivity.
         rewrite nth_rcons_last /=.
         set (wd := wires_of_type (type_of_chunk ϰ)).
         set (wb := 8 * sizeN_chunk ϰ).
         set (ℓ := sizeN gconn).
         rewrite /RTLC.eval_addressing /= /Genv.symbol_address /= /RTLC.mem_loadv. 
         simpl in *.
         eapply Gselk_correct; eauto.
         by rewrite /wb Int.add_zero_l N.div_mul_cancel_l /sizeN_chunk //; destruct ϰ.
       - repeat apply match_grid_add_right; assumption.
     }
   }

   { (* Store *)
     move: (match_grid_nonempty M) => Hsz_g'.
     move: args Hga EV => ? [wsrc [args [Eargs [LT Hga]]]] EV; subst.
     move: Hga => [guard [addr_body [gvar [addr_class [gsrc [gconn [gg [gu Hga]]]]]]]].
     move: Hga => [Eges [Hren_guard [Haddr [Hlocal [Hsrc [Hgguard [Halign [Hchunk [Hga [Hupd Hlocalnew]]]]]]]]]].
     apply rev_is_cons in Eges;
     rewrite /= rev_cons -seq.cats1 -catA /= in Eges.
     subst ges; destruct Hgguard as [ Hgguard -> ].
     move: Hupd => [res_conn].
     rewrite Hsrc; move=> [[<-]].
     have ->: N.pred (sizeN g') + sizeN addr_body + 2 = sizeN g' + sizeN addr_body + 1.
      by rewrite -N.sub_1_r; lia.
     rewrite sizeN_conn_new; move => [Hsz_res_conn Hglob].

     move: (match_grid_block (proj1 (proj2 M)) Hsrc).
     intros (b & sz & MB & Hb).
     destruct MB as [ MBv MB MBs (mbs & bs' & Hmbs & Hbs' & MBS) ].

     move: (conn_eval_isS_sizeN Hbs') => Hsz_gconn.

     move: (M) => [Mlocal [Mglobal Mconst]].
     move: (pcond_cond_eval Hcw Mlocal Hren_guard) => [gargs [Hgargs Hgev]].
     have LTwsrc: wsrc < sizeN g by apply LT; left.
     move: (Mlocal _ _ _ Hlocal LTwsrc); rewrite /read_wire;
     move => [srcbits [Esrcbits Msrc]].
     set src_conn := takeN_dflt wire_FF (8*sizeN_chunk ϰ)
                                (conn_ty (type_of_chunk ϰ) gsrc).
     have Hsz_src_conn: sizeN src_conn = 8*sizeN_chunk ϰ.
      by rewrite sizeN_takeN_dflt.
     destruct addr; simpl in Haddr; hsplit;
     unfold add_gate_spec in *; hsplit; simpl in *.
     { (* Aglobal *)
       rewrite is_global_block_succ in Hb.
       destruct Hb as (gv & Hb & Hgv & ->).
       move: v EV => vv; case: (ifP _) => Epcond; last first.
        (* guard = false *)
        move: Hgev; rewrite Epcond => Hgev.
        move=> [-> Hm']; subst; clear vv.
        eexists; split.
         econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
          split; first reflexivity.
          eexists; split; last reflexivity.
          rewrite /gate_eval /=; apply omap_isS.
          eexists; split; last reflexivity.
          eassumption.
         eright; simpl; [|by left; reflexivity|reflexivity].
         split; first reflexivity.
         exists (bits_of_bytes bs'); split; last reflexivity.
         rewrite /gate_eval /= omap_isS /=.
         move: (conn_eval_isS_sizeN Esrcbits);
         rewrite sizeN_conn_ty => Hsz_srcbits.
         exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
              & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
                ++ bits_of_bytes bs').
         split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite N.add_0_r /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 = sizeN g'
           by rewrite -N.sub_1_r; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           by apply conn_eval_takeN.
          by apply conn_eval_rcons.
         rewrite Epcond /cond_eval /=.
         rewrite takeN_dflt_all'; last first.
          rewrite sizeN_size dropN_drop size_drop size_cat -plusE -minusE. 
          rewrite Nat2N.inj_sub Nat2N.inj_add N2n2N -?sizeN_size.
          rewrite -(conn_eval_isS_sizeN Hbs').
          by rewrite sizeN_size takeN_take_dflt size_take_dflt N2n2N; lia.
         rewrite dropN_sizeN_cat //.
         by rewrite sizeN_size takeN_take_dflt size_take_dflt N2n2N.
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1) = N.pred (sizeN g') + 2
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1 N.add_0_r.
        eapply match_grid_upd_globv_noguard.
        - move: Hlocalnew; rewrite -N.sub_1_r sizeN_rcons.
          have ->: sizeN g' - 1 + 0 + 2 = sizeN g' + 1 by lia.
          by apply.
        - by apply Hsrc.
        - by apply conn_eval_rcons.
        - exists gconn; split; first by eassumption.
          split; last reflexivity.
          by rewrite sizeN_conn_new.
        - apply match_grid_add_right => //.
          rewrite conn_eval_conn_new'; f_equal.
          rewrite takeN_all; last first.
           rewrite sizeN_size dropN_drop size_drop.
           rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
           rewrite nth_rcons_last subn0 -sizeN_size; lia.
          rewrite dropN_drop drop0.
          rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
          rewrite nth_rcons_last //=; lia.
        - rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
          rewrite nth_rcons_last //=; lia.
       (* PCOND = true *)
       move: Hgev; rewrite Epcond => Hgev.
       move=> [srcm [dstm [Ewsrc [Hm' ->]]]]; subst; clear vv.
       eexists; split.
        econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
         split; first reflexivity.
         eexists; split; last reflexivity.
         rewrite /gate_eval /=; apply omap_isS.
         eexists; split; last reflexivity.
         eassumption.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        exists (updprefAtN (8 * N_of_int i0)
                      (bits_of_bytes bs')
                      (zero_extN' false (8 * sizeN_chunk ϰ) srcbits) 
                      ); split; last reflexivity.
        rewrite /gate_eval /= omap_isS /=.
        move: (conn_eval_isS_sizeN Esrcbits);
        rewrite sizeN_conn_ty => Hsz_srcbits.
        exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
             & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
               ++ bits_of_bytes bs').
        split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite N.add_0_r /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 = sizeN g'
            by rewrite -N.sub_1_r; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           by apply conn_eval_takeN.
          by apply conn_eval_rcons.
         rewrite Epcond /cond_eval /=.
         rewrite dropN_drop drop_size_cat; last first.
          by rewrite size_takeN_dflt.
         symmetry; rewrite takeN_dflt_all'; first last.
          rewrite sizeN_updprefAtN. 
          rewrite takeN_all // Hsz_gconn; reflexivity.
         f_equal.
          rewrite takeN_all // Hsz_gconn; reflexivity.
         rewrite takeN_take take_size_cat; first last.
          by rewrite size_takeN_dflt.
         by [].
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1) = N.pred (sizeN g') + 2
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1 N.add_0_r.
        move: Hm'; rewrite /RTLC.eval_addressing /=.
        destruct dstm => //=.
        rewrite /Genv.symbol_address Hb; move: Ewsrc => [<-] Hstore.
        have T:∃ k : nat, size srcbits = (8 * k)%N.
         move: (conn_eval_isS_sizeN Esrcbits).
         rewrite sizeN_conn_ty /wires_of_type.
         rewrite -[8]N2n2N -Z_nat_N sizeN_size -Nat2N.inj_mul; move=> /Nat2N.inj T.
         exists (Z.to_nat (typesize (type_of_chunk ϰ))).
         by rewrite -T.
        move: (bytes_of_bits T) => [srcbs Hsrcbs]; subst.
        eapply match_grid_upd_globv_guard; eauto.
        - move: Hlocalnew; rewrite -N.sub_1_r sizeN_rcons.
          have ->: sizeN g' - 1 + 0 + 2 = sizeN g' + 1 by lia.
          by apply.
        - by apply conn_eval_rcons, Hbs'.
        - by apply match_grid_add_right.
        - exists gconn; split; first by eassumption.
          split.
           by rewrite sizeN_conn_new.
          by rewrite sizeN_rcons.
     }
     { (* Abased *)
       rewrite is_global_block_succ in Hb.
       destruct Hb as (gv & Hb & Hgv & ->).
       have LT2: all_lt (sizeN g) [:: w].
        by move=> x Hx; apply LT; right. 
       edestruct (proc_op_spec_gate_eval) as (lea & Hlea & Hszlea & EVlea); try eassumption.
        discriminate.
       rewrite /RTLC.eval_operation /= in EVlea.
       move: v EV => vv; case: (ifP _) => Epcond; last first.
        (* guard = false *)
        move: Hgev; rewrite Epcond => Hgev.
        move=> [-> Hm']; subst; clear vv.
        eexists; split.
         econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
         eright.
          split; first reflexivity.
          eexists; split; last reflexivity.
          rewrite /gate_eval /=; apply omap_isS.
          eexists; split; last reflexivity.
          apply conn_eval_rcons.
          eassumption.
         eright; simpl; [|by left; reflexivity|reflexivity].
         split; first reflexivity.
         exists (bits_of_bytes bs'); split; last reflexivity.
         rewrite /gate_eval /= omap_isS /=.
         move: (conn_eval_isS_sizeN Esrcbits);
         rewrite sizeN_conn_ty => Hsz_srcbits.
         exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
              & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
                ++ bits_of_bytes bs' ++ takeN (size2idxbits (8 * sizeN_chunk ϰ) (sizeN gconn))
                (dropN (N.log2 (sizeN_chunk ϰ)) lea)).
         split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 + 1 = sizeN (rcons g' lea)
           by rewrite -N.sub_1_r sizeN_rcons ; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           apply conn_eval_rcons. 
           by apply conn_eval_takeN.
          apply conn_eval_rcons.
          apply conn_eval_cat. 
           apply conn_eval_rcons; assumption. 
          have ->: N.pred (sizeN g') + 1 = sizeN g'
            by rewrite -N.sub_1_r; lia.
          rewrite conn_eval_conn_new'; repeat f_equal.
           by rewrite nth_rcons_last.
          rewrite nth_rcons_last -Hszlea /wires_of_type /=.
          by apply pointers_need_no_more_than_32bits.
         rewrite Epcond /cond_eval /=.
         rewrite takeN_dflt_all'; last first.
          rewrite dropN_sizeN_cat; last first. 
           by rewrite sizeN_takeN_dflt.
          rewrite takeN_take -size_sizeN take_size_cat //.
          by apply Nat2N.inj; rewrite -!sizeN_size.
         rewrite dropN_sizeN_cat; last first. 
          by rewrite sizeN_takeN_dflt.
         rewrite takeN_take -size_sizeN take_size_cat //.
         by apply Nat2N.inj; rewrite -!sizeN_size.
        by rewrite (Events.E0_left [::]).
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1 + 1) = N.pred (sizeN g') + 3
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1.
        eapply match_grid_upd_globv_noguard.
        - move: Hlocalnew; rewrite -N.sub_1_r ?sizeN_rcons.
          have ->: sizeN g' - 1 + 1 + 2 = sizeN g' + 1 + 1 by lia.
          by apply.
        - by apply Hsrc.
        - by apply conn_eval_rcons, conn_eval_rcons.
        - exists gconn; split; first by eassumption.
          split; last reflexivity.
          by rewrite sizeN_conn_new.
        - apply match_grid_add_right.
           apply match_grid_add_right => //.
           rewrite conn_eval_conn_new'; f_equal.
           rewrite takeN_all; last first.
            rewrite sizeN_size dropN_drop size_drop.
            rewrite -(sizeN_rcons _ lea).
            rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
            rewrite nth_rcons_last subn0 -sizeN_size; lia.
           rewrite dropN_drop drop0.
           rewrite -(sizeN_rcons _ lea).
           rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
           rewrite nth_rcons_last //=; lia.
        - rewrite -(sizeN_rcons _ lea).
          rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
          rewrite nth_rcons_last //=; lia.
       (* PCOND = true *)
       move: Hgev; rewrite Epcond => Hgev.
       move=> [srcm [dstm [Ewsrc [Hm' ->]]]]; subst; clear vv.
       move: Hm'; rewrite /RTLC.eval_addressing /=.
       destruct dstm as [|a1 [| a2 aa]] => //=.
       rewrite /Genv.symbol_address Hb; move: Ewsrc => [<- <-].
       rewrite /Values.Val.add /=.
       destruct (ValCirc.read_wire g w) => // /= Hstore.
       move: (Mem.store_valid_access_3 _ _ _ _ _ _ Hstore).
       rewrite /Mem.valid_access Halign; move => [T0 T1].
       move: (Mem.loadbytes_length _ _ _ _ _ Hmbs); rewrite lengthE => Hmbs_sz.
       move: (Mem.loadbytes_range_perm _ _ _ _ _ Hmbs) => Hmbs_perm.
       set off:= Int.unsigned (Int.add i0 i1).
       move: (size_chunk_pos ϰ) => T2.
       have T3: Mem.perm m b (Int.unsigned (Int.add i1 i0) + size_chunk ϰ - 1) Cur Readable.
        apply Mem.perm_implies with Writable; last by constructor.
        by rewrite Int.add_commut; apply T0; lia.
       move:  {T0 T3} (MB _ T3) => T0.
       move: EVlea; rewrite /match_val_ty /= => EVlea.
       eexists; split.
        econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
        eright.
          split; first reflexivity.
          eexists; split; last reflexivity.
          rewrite /gate_eval /=; apply omap_isS.
          eexists; split; last reflexivity.
          apply conn_eval_rcons.
          eassumption.
         eright; simpl; [|by left; reflexivity|reflexivity].
         split; first reflexivity.
         exists (updprefAtN (8 * (N_of_int (Int.add i1 i0)))
                       (bits_of_bytes bs')
                       (zero_extN' false (8 * sizeN_chunk ϰ) srcbits) 
           ); split; last reflexivity.
         rewrite /gate_eval /= omap_isS /=.
         move: (conn_eval_isS_sizeN Esrcbits);
         rewrite sizeN_conn_ty => Hsz_srcbits.
         exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
              & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
                ++ bits_of_bytes bs' ++ takeN (size2idxbits (8 * sizeN_chunk ϰ) (sizeN gconn))
                (dropN (N.log2 (sizeN_chunk ϰ)) lea)).
         split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 + 1 = sizeN (rcons g' lea)
           by rewrite -N.sub_1_r sizeN_rcons ; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           apply conn_eval_rcons. 
           by apply conn_eval_takeN.
          apply conn_eval_rcons.
          apply conn_eval_cat. 
           apply conn_eval_rcons; assumption. 
          have ->: N.pred (sizeN g') + 1 = sizeN g'
            by rewrite -N.sub_1_r; lia.
          rewrite conn_eval_conn_new'; repeat f_equal.
           by rewrite nth_rcons_last.
          rewrite nth_rcons_last -Hszlea /wires_of_type /=.
          by apply pointers_need_no_more_than_32bits.
         rewrite Epcond /cond_eval /=.
         rewrite dropN_drop catA drop_size_cat //; last first.
          rewrite N.add_comm size_cat ?size_sizeN -plusE.
          rewrite -N2Nat.inj_add; apply Nat2N.inj.
          rewrite !N2n2N; f_equal => //.
          by rewrite sizeN_takeN_dflt.
         symmetry; rewrite takeN_dflt_all'; last first.
          rewrite sizeN_updprefAtN Hsz_gconn; f_equal.
          rewrite dropN_drop -catA drop_size_cat //; last first.
           by rewrite size_sizeN sizeN_takeN_dflt.
          by rewrite takeN_take take_size_cat // -size_sizeN.
         f_equal.
           rewrite Hsz_gconn sizeN_bits_of_bytes EVlea.
           have ->: sizeN bs' = Z.to_N (Genv.init_data_list_size (gvar_init gv)).
            rewrite -(all2_sizeN MBS) sizeN_size -Z_nat_N.
            apply N2Nat.inj; rewrite !n2N2n.
            rewrite -lengthE.
            by rewrite (Mem.loadbytes_length _ _ _ _ _ Hmbs).
           rewrite idxbits_correct; first last.
              lia.
             by move: (Int.unsigned_range (Int.add i1 i0)); lia.
            by rewrite Int.add_commut.
           rewrite -N.mul_assoc; f_equal.
           symmetry; apply N.div_exact. 
            by destruct ϰ.
           rewrite -Z2N.inj_mod; first last.
             lia.
            by move: (Int.unsigned_range (Int.add i1 i0)); lia.            
           apply N2Z.inj; rewrite Z2N.id; first last.
            move: (Z_mod_lt (Int.unsigned (Int.add i1 i0)) (size_chunk ϰ)); lia.
           by rewrite Int.add_commut; apply Zdivide_mod.
          rewrite dropN_drop -catA drop_size_cat //; last first.
           by rewrite size_sizeN sizeN_takeN_dflt.
          by rewrite takeN_take take_size_cat // size_sizeN Hsz_gconn.
         rewrite takeN_take -catA take_size_cat; last first.
          by rewrite size_sizeN sizeN_takeN_dflt.
         by [].
        by rewrite (Events.E0_left [::]).
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1 + 1) = N.pred (sizeN g') + 3
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1.
        have T:∃ k : nat, size srcbits = (8 * k)%N.
         move: (conn_eval_isS_sizeN Esrcbits).
         rewrite sizeN_conn_ty /wires_of_type.
         rewrite -[8]N2n2N -Z_nat_N sizeN_size -Nat2N.inj_mul; move=> /Nat2N.inj T.
         exists (Z.to_nat (typesize (type_of_chunk ϰ))).
         by rewrite -T.
        move: (bytes_of_bits T) => [srcbs Hsrcbs]; subst.
        eapply match_grid_upd_globv_guard; eauto.
        - move: Hlocalnew; rewrite -N.sub_1_r ?sizeN_rcons.
          have ->: sizeN g' - 1 + 1 + 2 = sizeN g' + 1 + 1 by lia.
          by apply.
        - by apply conn_eval_rcons, conn_eval_rcons; eassumption.
        - by apply match_grid_add_right, match_grid_add_right; eassumption.
        - exists gconn; split; first by eassumption.
          split.
           by rewrite sizeN_conn_new.
          by rewrite !sizeN_rcons.
        - by rewrite Int.add_commut.
     }
     { (* Abasedscaled *)
       rewrite is_global_block_succ in Hb.
       destruct Hb as (gv & Hb & Hgv & ->).
       have LT2: all_lt (sizeN g) [:: w].
        by move=> x Hx; apply LT; right. 
       edestruct (proc_op_spec_gate_eval) as (lea & Hlea & Hszlea & EVlea); try eassumption.
        discriminate.
       rewrite /RTLC.eval_operation /= in EVlea.
       move: v EV => vv; case: (ifP _) => Epcond; last first.
        (* guard = false *)
        move: Hgev; rewrite Epcond => Hgev.
        move=> [-> Hm']; subst; clear vv.
        eexists; split.
         econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
         eright.
          split; first reflexivity.
          eexists; split; last reflexivity.
          rewrite /gate_eval /=; apply omap_isS.
          eexists; split; last reflexivity.
          apply conn_eval_rcons.
          eassumption.
         eright; simpl; [|by left; reflexivity|reflexivity].
         split; first reflexivity.
         exists (bits_of_bytes bs'); split; last reflexivity.
         rewrite /gate_eval /= omap_isS /=.
         move: (conn_eval_isS_sizeN Esrcbits);
         rewrite sizeN_conn_ty => Hsz_srcbits.
         exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
              & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
                ++ bits_of_bytes bs' ++ takeN (size2idxbits (8 * sizeN_chunk ϰ) (sizeN gconn))
                (dropN (N.log2 (sizeN_chunk ϰ)) lea)).
         split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 + 1 = sizeN (rcons g' lea)
           by rewrite -N.sub_1_r sizeN_rcons ; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           apply conn_eval_rcons. 
           by apply conn_eval_takeN.
          apply conn_eval_rcons.
          apply conn_eval_cat. 
           apply conn_eval_rcons; assumption. 
          have ->: N.pred (sizeN g') + 1 = sizeN g'
            by rewrite -N.sub_1_r; lia.
          rewrite conn_eval_conn_new'; repeat f_equal.
           by rewrite nth_rcons_last.
          rewrite nth_rcons_last -Hszlea /wires_of_type /=.
          by apply pointers_need_no_more_than_32bits.
         rewrite Epcond /cond_eval /=.
         rewrite takeN_dflt_all'; last first.
          rewrite dropN_sizeN_cat; last first. 
           by rewrite sizeN_takeN_dflt.
          rewrite takeN_take -size_sizeN take_size_cat //.
          by apply Nat2N.inj; rewrite -!sizeN_size.
         rewrite dropN_sizeN_cat; last first. 
          by rewrite sizeN_takeN_dflt.
         rewrite takeN_take -size_sizeN take_size_cat //.
         by apply Nat2N.inj; rewrite -!sizeN_size.
        by rewrite (Events.E0_left [::]).
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1 + 1) = N.pred (sizeN g') + 3
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1.
        eapply match_grid_upd_globv_noguard.
        - move: Hlocalnew; rewrite -N.sub_1_r ?sizeN_rcons.
          have ->: sizeN g' - 1 + 1 + 2 = sizeN g' + 1 + 1 by lia.
          by apply.
        - by apply Hsrc.
        - by apply conn_eval_rcons, conn_eval_rcons.
        - exists gconn; split; first by eassumption.
          split; last reflexivity.
          by rewrite sizeN_conn_new.
        - apply match_grid_add_right.
           apply match_grid_add_right => //.
           rewrite conn_eval_conn_new'; f_equal.
           rewrite takeN_all; last first.
            rewrite sizeN_size dropN_drop size_drop.
            rewrite -(sizeN_rcons _ lea).
            rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
            rewrite nth_rcons_last subn0 -sizeN_size; lia.
           rewrite dropN_drop drop0.
           rewrite -(sizeN_rcons _ lea).
           rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
           rewrite nth_rcons_last //=; lia.
        - rewrite -(sizeN_rcons _ lea).
          rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
          rewrite nth_rcons_last //=; lia.
       (* PCOND = true *)
       move: Hgev; rewrite Epcond => Hgev.
       move=> [srcm [dstm [Ewsrc [Hm' ->]]]]; subst; clear vv.
       move: Hm'; rewrite /RTLC.eval_addressing /=.
       destruct dstm as [|a1 [| a2 aa]] => //=.
       rewrite /Genv.symbol_address Hb; move: Ewsrc => [<- <-].
       rewrite /Values.Val.add /=.
       destruct (ValCirc.read_wire g w) => // /= Hstore.
       move: (Mem.store_valid_access_3 _ _ _ _ _ _ Hstore).
       rewrite /Mem.valid_access Halign; move => [T0 T1].
       move: (Mem.loadbytes_length _ _ _ _ _ Hmbs); rewrite lengthE => Hmbs_sz.
       move: (Mem.loadbytes_range_perm _ _ _ _ _ Hmbs) => Hmbs_perm.
       set off:= Int.unsigned (Int.add i1 (Int.mul i2 i)).
       move: (size_chunk_pos ϰ) => T2.
       have T3: Mem.perm m b (Int.unsigned (Int.add i1 (Int.mul i2 i)) + size_chunk ϰ - 1) Cur Readable.
        apply Mem.perm_implies with Writable; last by constructor.
        by apply T0; lia.
       move:  {T0 T3} (MB _ T3) => T0.
       move: EVlea; rewrite /match_val_ty /= => EVlea.
       eexists; split.
        econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
        eright.
          split; first reflexivity.
          eexists; split; last reflexivity.
          rewrite /gate_eval /=; apply omap_isS.
          eexists; split; last reflexivity.
          apply conn_eval_rcons.
          eassumption.
         eright; simpl; [|by left; reflexivity|reflexivity].
         split; first reflexivity.
         exists (updprefAtN (8 * (N_of_int (Int.add i1 (Int.mul i2 i))))
                       (bits_of_bytes bs')
                       (zero_extN' false (8 * sizeN_chunk ϰ) srcbits) 
           ); split; last reflexivity.
         rewrite /gate_eval /= omap_isS /=.
         move: (conn_eval_isS_sizeN Esrcbits);
         rewrite sizeN_conn_ty => Hsz_srcbits.
         exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
              & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
                ++ bits_of_bytes bs' ++ takeN (size2idxbits (8 * sizeN_chunk ϰ) (sizeN gconn))
                (dropN (N.log2 (sizeN_chunk ϰ)) lea)).
         split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 + 1 = sizeN (rcons g' lea)
           by rewrite -N.sub_1_r sizeN_rcons ; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           apply conn_eval_rcons. 
           by apply conn_eval_takeN.
          apply conn_eval_rcons.
          apply conn_eval_cat. 
           apply conn_eval_rcons; assumption. 
          have ->: N.pred (sizeN g') + 1 = sizeN g'
            by rewrite -N.sub_1_r; lia.
          rewrite conn_eval_conn_new'; repeat f_equal.
           by rewrite nth_rcons_last.
          rewrite nth_rcons_last -Hszlea /wires_of_type /=.
          by apply pointers_need_no_more_than_32bits.
         rewrite Epcond /cond_eval /=.
         rewrite dropN_drop catA drop_size_cat //; last first.
          rewrite N.add_comm size_cat ?size_sizeN -plusE.
          rewrite -N2Nat.inj_add; apply Nat2N.inj.
          rewrite !N2n2N; f_equal => //.
          by rewrite sizeN_takeN_dflt.
         symmetry; rewrite takeN_dflt_all'; last first.
          rewrite sizeN_updprefAtN Hsz_gconn; f_equal.
          rewrite dropN_drop -catA drop_size_cat //; last first.
           by rewrite size_sizeN sizeN_takeN_dflt.
          by rewrite takeN_take take_size_cat // -size_sizeN.
         f_equal.
           rewrite Hsz_gconn sizeN_bits_of_bytes EVlea.
           have ->: sizeN bs' = Z.to_N (Genv.init_data_list_size (gvar_init gv)).
            rewrite -(all2_sizeN MBS) sizeN_size -Z_nat_N.
            apply N2Nat.inj; rewrite !n2N2n.
            rewrite -lengthE.
            by rewrite (Mem.loadbytes_length _ _ _ _ _ Hmbs).
           rewrite idxbits_correct; first last.
              rewrite Int.add_commut; lia.
             by move: (Int.unsigned_range (Int.add (Int.mul i2 i) i1)); lia.
            by rewrite Int.add_commut.
           rewrite -N.mul_assoc; f_equal.
           rewrite Int.add_commut; symmetry; apply N.div_exact. 
            by destruct ϰ.
           rewrite -Z2N.inj_mod; first last.
             lia.
            by move: (Int.unsigned_range (Int.add i1 (Int.mul i2 i))); lia.            
           apply N2Z.inj; rewrite Z2N.id; first last.
            move: (Z_mod_lt (Int.unsigned (Int.add i1 (Int.mul i2 i))) (size_chunk ϰ)); lia.
           by apply Zdivide_mod.
          rewrite dropN_drop -catA drop_size_cat //; last first.
           by rewrite size_sizeN sizeN_takeN_dflt.
          by rewrite takeN_take take_size_cat // size_sizeN Hsz_gconn.
         rewrite takeN_take -catA take_size_cat; last first.
          by rewrite size_sizeN sizeN_takeN_dflt.
         by [].
        by rewrite (Events.E0_left [::]).
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1 + 1) = N.pred (sizeN g') + 3
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1.
        have T:∃ k : nat, size srcbits = (8 * k)%N.
         move: (conn_eval_isS_sizeN Esrcbits).
         rewrite sizeN_conn_ty /wires_of_type.
         rewrite -[8]N2n2N -Z_nat_N sizeN_size -Nat2N.inj_mul; move=> /Nat2N.inj T.
         exists (Z.to_nat (typesize (type_of_chunk ϰ))).
         by rewrite -T.
        move: (bytes_of_bits T) => [srcbs Hsrcbs]; subst.
        eapply match_grid_upd_globv_guard; eauto.
        - move: Hlocalnew; rewrite -N.sub_1_r ?sizeN_rcons.
          have ->: sizeN g' - 1 + 1 + 2 = sizeN g' + 1 + 1 by lia.
          by apply.
        - by apply conn_eval_rcons, conn_eval_rcons; eassumption.
        - by apply match_grid_add_right, match_grid_add_right; eassumption.
        - exists gconn; split; first by eassumption.
          split.
           by rewrite sizeN_conn_new.
          by rewrite !sizeN_rcons.
     }
     { (* Ainstack *)
       move: Hb => [ Hsp Hsz ].
       move: v EV => vv; case: (ifP _) => Epcond; last first.
        (* guard = false *)
        move: Hgev; rewrite Epcond => Hgev.
        move=> [-> Hm']; subst; clear vv.
        eexists; split.
         econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
          split; first reflexivity.
          eexists; split; last reflexivity.
          rewrite /gate_eval /=; apply omap_isS.
          eexists; split; last reflexivity.
          eassumption.
         eright; simpl; [|by left; reflexivity|reflexivity].
         split; first reflexivity.
         exists (bits_of_bytes bs'); split; last reflexivity.
         rewrite /gate_eval /= omap_isS /=.
         move: (conn_eval_isS_sizeN Esrcbits);
         rewrite sizeN_conn_ty => Hsz_srcbits.
         exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
              & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
                ++ bits_of_bytes bs').
         split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite N.add_0_r /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 = sizeN g'
           by rewrite -N.sub_1_r; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           by apply conn_eval_takeN.
          by apply conn_eval_rcons.
         rewrite Epcond /cond_eval /=.
         rewrite takeN_dflt_all'; last first.
          rewrite sizeN_size dropN_drop size_drop size_cat -plusE -minusE. 
          rewrite Nat2N.inj_sub Nat2N.inj_add N2n2N -?sizeN_size.
          rewrite -(conn_eval_isS_sizeN Hbs').
          by rewrite sizeN_size takeN_take_dflt size_take_dflt N2n2N; lia.
         rewrite dropN_sizeN_cat //.
         by rewrite sizeN_size takeN_take_dflt size_take_dflt N2n2N.
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1) = N.pred (sizeN g') + 2
          by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1 N.add_0_r.
        eapply match_grid_upd_stack_noguard.
        - move: Hlocalnew; rewrite -N.sub_1_r sizeN_rcons.
          have ->: sizeN g' - 1 + 0 + 2 = sizeN g' + 1 by lia.
          by apply.
        - by apply Hsrc.
        - by apply conn_eval_rcons.
        - exists gconn; split; first by eassumption.
          split; last reflexivity.
          by rewrite sizeN_conn_new.
        - apply match_grid_add_right => //.
          rewrite conn_eval_conn_new'; f_equal.
          rewrite takeN_all; last first.
           rewrite sizeN_size dropN_drop size_drop.
           rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
           rewrite nth_rcons_last subn0 -sizeN_size; lia.
          rewrite dropN_drop drop0.
          rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
          rewrite nth_rcons_last //=; lia.
        - rewrite -(sizeN_rcons _ (zero_extN' false 1 [:: (eval_guard guard gargs).1])).
          rewrite nth_rcons_last //=; lia.
       (* PCOND = true *)
       move: Hgev; rewrite Epcond => Hgev.
       move=> [srcm [dstm [Ewsrc [Hm' ->]]]]; subst; clear vv.
       eexists; split.
        econstructor; simpl; eauto; last by rewrite (Events.E0_left [::]).
         split; first reflexivity.
         eexists; split; last reflexivity.
         rewrite /gate_eval /=; apply omap_isS.
         eexists; split; last reflexivity.
         eassumption.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        exists (updprefAtN (8 * N_of_int i)
                      (bits_of_bytes bs')
                      (zero_extN' false (8 * sizeN_chunk ϰ) srcbits) 
                      ); split; last reflexivity.
        rewrite /gate_eval /= omap_isS /=.
        move: (conn_eval_isS_sizeN Esrcbits);
        rewrite sizeN_conn_ty => Hsz_srcbits.
        exists ([:: eval_pcond (ValCirc.get_path_model g cw) pc
             & takeN_dflt false (8*sizeN_chunk ϰ) srcbits]
               ++ bits_of_bytes bs').
        split.
          rewrite Hgev /=.
          rewrite -[(_,_)::_]cat1s -[_::(takeN_dflt _ _ _++_)]cat1s.
          apply conn_eval_cat.
           rewrite N.add_0_r /conn_eval omap_all_isS /=; f_equal.
           have ->: N.pred (sizeN g') + 1 = sizeN g'
            by rewrite -N.sub_1_r; lia.
           by rewrite /wire_eval nth_rcons_last Epcond takeN_take_dflt.
          apply conn_eval_cat.
           apply conn_eval_rcons.
           rewrite takeN_dflt_takeN; last first.
            rewrite -Hsz_srcbits.
            by apply sizeN_chunk_ty.
           by apply conn_eval_takeN.
          by apply conn_eval_rcons.
         rewrite Epcond /cond_eval /=.
         rewrite dropN_drop drop_size_cat; last first.
          by rewrite size_takeN_dflt.
         symmetry; rewrite takeN_dflt_all'; first last.
          rewrite sizeN_updprefAtN. 
          rewrite takeN_all // Hsz_gconn; reflexivity.
         f_equal.
          rewrite takeN_all // Hsz_gconn; reflexivity.
         rewrite takeN_take take_size_cat; first last.
          by rewrite size_takeN_dflt.
         by [].
        eexists _, _, _, _, _, _, _.
        split; first eassumption.
        split; [|split; [|split; [eassumption|reflexivity]]].
         rewrite sizeN_app ?sizeN_rcons /=.
         have ->: N.pred (sizeN g' + 1 + 1) = N.pred (sizeN g') + 2
         by rewrite !N.pred_sub; lia.
         eassumption.
        rewrite -appE cats1 N.add_0_r.
        move: Hm'; rewrite /RTLC.eval_addressing /=.
        destruct dstm => //= Hstore.
        have T:∃ k : nat, size srcbits = (8 * k)%N.
         move: (conn_eval_isS_sizeN Esrcbits).
         rewrite sizeN_conn_ty /wires_of_type.
         rewrite -[8]N2n2N -Z_nat_N sizeN_size -Nat2N.inj_mul; move=> /Nat2N.inj T.
         exists (Z.to_nat (typesize (type_of_chunk ϰ))).
         by rewrite -T.
        move: (bytes_of_bits T) => [srcbs Hsrcbs]; subst.
        eapply match_grid_upd_stack_guard; eauto.
        - move: Hlocalnew; rewrite -N.sub_1_r sizeN_rcons.
          have ->: sizeN g' - 1 + 0 + 2 = sizeN g' + 1 by lia.
          by apply.
        - by apply conn_eval_rcons, Hbs'.
        - eapply match_grid_add_right; eassumption.
        - exists gconn; split; first by eassumption.
          split.
           by rewrite sizeN_conn_new.
          by rewrite sizeN_rcons.
        - move: Hstore; rewrite /= Int.add_zero_l .
          by move: Ewsrc => [<-].
     }
   }

   { (* Test *)
     hsplit.
     move: (match_grid_nonempty M) => Gne.
     move: M => [Mlocal [Mglob Mconst]].
     move: (pcond_cond_eval Hcw Mlocal H2).
     move: EV; rewrite /=; case: (ifP _) => EV; last first.
      (* pcond false *)
      move=> [Hv Hm']; subst.
      move=> [gvars [Hgvars EVguard]].
      unfold add_gate_spec in *; hsplit.
      apply (f_equal rev) in H7.
      rewrite revK /rev /= in H7; subst.
      rewrite sizeN_size /= -sizeN_size in Hcode.
      move: (localv_args_eval H0 Mlocal H1) => [abits Hargsbits].
      case Xbits: (gate_eval (gateInfo gate) g' wargs) => [xbits|];last first.
       by rewrite /gate_eval Hargsbits /= in Xbits; inv Xbits.
      have: size xbits = N2n 1.
       by rewrite -(cmp_gate_out_arity H) size_sizeN (gate_eval_sizeN Xbits).
      move: xbits Xbits => [|res [|? ?]] //= Hres _.
      eexists; split.
       econstructor; simpl; eauto; last reflexivity.
       eright; simpl.
         split; first reflexivity.
         exists [:: false].
         split; last reflexivity.
         rewrite /gate_eval /=; apply omap_isS.
         exists gvars; split. 
          by apply conn_eval_rcons.
         by rewrite EVguard.
        eright; simpl; [|by left; reflexivity|reflexivity].
        split; first reflexivity.
        exists [:: false]; split; last reflexivity.
        rewrite /gate_eval /= omap_isS /=.
        exists ([:: res]++[:: false]); split; last first.
         by rewrite /= andbF.
        rewrite -[_::_::_]cat1s; apply conn_eval_cat.
         apply conn_eval_rcons.
         rewrite /conn_eval omap_all_isS /wire_eval /=.
         have ->: Npred (sizeN g') + 1 = sizeN g'.
          by rewrite -N.sub_1_r; lia.
         by rewrite nth_rcons_last.
        rewrite /conn_eval omap_all_isS /wire_eval /=.
        have ->: Npred (sizeN g') + 2 = sizeN (rcons g' [:: res]).
         by rewrite -N.sub_1_r sizeN_rcons; lia.
        by rewrite nth_rcons_last.
       by [].
      eexists _, _, _, _, _, _, _; split; first eassumption.
      split; [|split; [|split; [eassumption|reflexivity]]].
       rewrite sizeN_app ?sizeN_rcons /=.
       have ->: N.pred (sizeN g' + 1 + 1 + 1) = N.pred (sizeN g') + 3.
        by  rewrite ! N.pred_sub; lia.
       eassumption.
      rewrite -appE; eapply match_grid_add_local; eauto.
      - move: H6; rewrite /is_localv.
        rewrite !sizeN_rcons N.pred_sub.
        have ->: sizeN g' - 1 + 3 = sizeN g' + 1 + 1 by lia.
        by apply.
      - by [].
      - by [].
      - by apply match_grid_add_right, match_grid_add_right.
     (* pcond true *)
     move=> [Hv Hm']; subst.
     move=> [gvars [Hgvars EVguard]].
     unfold add_gate_spec in *; hsplit.
     apply (f_equal rev) in H7.
     rewrite revK /rev /= in H7; subst.
     rewrite sizeN_size /= -sizeN_size in Hcode.
     move: (localv_args_eval H0 Mlocal H1) => [abits Hargsbits].
     case Xbits: (gate_eval (gateInfo gate) g' wargs) => [xbits|];last first.
      by rewrite /gate_eval Hargsbits /= in Xbits; inv Xbits.
     have: size xbits = N2n 1.
      by rewrite -(cmp_gate_out_arity H) size_sizeN (gate_eval_sizeN Xbits).
     move: xbits Xbits => [|res [|? ?]] //= Hres _.
     eexists; split.
      econstructor; simpl; eauto; last reflexivity.
      eright; simpl.
        split; first reflexivity.
        exists [:: true].
        split; last reflexivity.
        rewrite /gate_eval /=; apply omap_isS.
        exists gvars; split. 
         by apply conn_eval_rcons.
        by rewrite EVguard.
       eright; simpl; [|by left; reflexivity|reflexivity].
       split; first reflexivity.
       exists [:: res]; split; last reflexivity.
       rewrite /gate_eval /= omap_isS /=.
       exists ([:: res]++[:: true]); split; last first.
        by rewrite /= andbT.
       rewrite -[_::_::_]cat1s; apply conn_eval_cat.
        apply conn_eval_rcons.
        rewrite /conn_eval omap_all_isS /wire_eval /=.
        have ->: Npred (sizeN g') + 1 = sizeN g'.
         by rewrite -N.sub_1_r; lia.
        by rewrite nth_rcons_last.
       rewrite /conn_eval omap_all_isS /wire_eval /=.
       have ->: Npred (sizeN g') + 2 = sizeN (rcons g' [:: res]).
        by rewrite -N.sub_1_r sizeN_rcons; lia.
       by rewrite nth_rcons_last.
      by [].
     eexists _, _, _, _, _, _, _; split; first eassumption.
      split; [|split; [|split; [eassumption|reflexivity]]].
       rewrite sizeN_app ?sizeN_rcons /=.
       have ->: N.pred (sizeN g' + 1 + 1 + 1) = N.pred (sizeN g') + 3.
        by  rewrite ! N.pred_sub; lia.
       eassumption.
      rewrite -appE; eapply match_grid_add_local; eauto.
      - move: H6; rewrite /is_localv.
        rewrite !sizeN_rcons N.pred_sub.
        have ->: sizeN g' - 1 + 3 = sizeN g' + 1 + 1 by lia.
        by apply.
      - by [].
      - move: Hres; rewrite /gate_eval /= omap_isS.
        rewrite Hargsbits; move=> [? [[<-]]].
        rewrite (gate_out_arity_condition H).
        move: (localv_conn_list_match_val H0 Mlocal H1 Hargsbits) => T.
        move: (gate_of_condition_correct H T H8) => ->.
        rewrite takeN_take_dflt /=; move => [<-].
        by rewrite /ValCirc.val_is_true; case: res; case: (Values.Val.eq _ _).
      - by apply match_grid_add_right, match_grid_add_right.
   }

   { (* φ *)
     move: (match_grid_nonempty M) => Gne.
     hsplit. 
     move: EV; simpl; set pcm:= ValCirc.get_path_model g cw; move=> {args} [_ [Ev ->]].
     move: H1; set flat_phi:= flat_phi_node φ'; move=> Hphi.
     have Xtra: forall l ges,
       subseq l flat_phi ->
       phi_spec localv (sizeN g) (N.pred (sizeN g')) ty (sizeN ges) l ges ->
       exists g2,
         plus step (Genv.globalenv p') (State (rev ges ++ ges') [seq i.2 | i <- outs] oc g')
              Events.E0 (State ges' [seq i.2 | i <- outs] oc (g'++g2))
         /\ conn_eval (g'++g2) (conn_ty ty (N.pred (sizeN g') + sizeN ges))
            = Some (get_phi_assoc localv ty g' l)
         /\ sizeN g2 = sizeN ges.
     { move=> l gess; elim: l gess ges' g' M {H2 Gne Hcode Hphi ges}.
        by move=> ges ges' g' M Hsub Hphi; inv Hphi.
       move=> [c' cv'] l IH ges ges' g' M.
       move: (M) => [Mlocal [Mglob Mconst]] Hsub.
       move: (match_grid_nonempty M) => M_sz.
       have Hin: (c',cv')\in flat_phi by apply (mem_subseq Hsub); rewrite in_cons eq_refl.
(*       move: (flat_phi_renamed Hcw H H0 Hin) => [[c cv] [Hc /= Hc_ren]].*)
       move: (flat_phi_renamed Hcw H H0 Hin) => [/= Hc Hc_ren].
       move: (pcond_cond_eval Hcw Mlocal Hc_ren) => [vars [Hev_guard Hev_cond]].
       move=> Hphi; inv Hphi; hsplit.
        clear IH Hsub.
        move: (Mlocal _ _ _ H2 H6) => [vbits [HH1 HH2]].
        set cond_ev := full_eval_guard g' c'.
        move: H2; rewrite /is_localv nsucc_pospred=> H2; rewrite H2.
        exists [:: [:: cond_ev]; if cond_ev then vbits else bits0 (wires_of_type ty)].
        unfold add_gate_ty_spec, add_gate_spec in *; hsplit.
        split.
         eapply plus_two; last by rewrite (Events.E0_left [::]).
         constructor; first reflexivity.
          exists [:: full_eval_guard g' c'].
          split; last reflexivity.
          rewrite /full_eval_guard /gate_eval /=.
          by rewrite Hev_guard /=; f_equal.
         constructor; first reflexivity.
          exists (if cond_ev then vbits else bits0 (wires_of_type ty)).
          rewrite -!cats1 -?catA /=.
          split; last reflexivity.
          rewrite /gate_eval /eval_GbarrierN /cond_eval /=.
          rewrite -[(_,_)::_]cat1s.
          have T1: conn_eval (g' ++ [:: [:: full_eval_guard g' c']]) [:: (N.pred (sizeN g')+1, 0)]
                   = Some [:: cond_ev].
           have ->: N.pred (sizeN g') + 1 = sizeN g' by rewrite -N.sub_1_r; lia.
           by rewrite /conn_eval /wire_eval cats1 /= nth_rcons_last.
          have T2: conn_eval (g' ++ [:: [:: full_eval_guard g' c']]) (conn_ty ty gw) = Some vbits.
           by apply conn_eval_isS_subgrid.
          rewrite (conn_eval_cat T1 T2) /=; f_equal.
          case: (ifP _) => _.
           move: (sizeN_read_wire HH1) => T. 
           rewrite takeN_all; last by rewrite T; reflexivity.
           by rewrite takeN_dflt_all'.
          rewrite takeN_dflt_all'; last by rewrite sizeN_takeN_dflt.
          rewrite takeN_dflt_split /= ?N.sub_0_r ?bits0_nseqN //.
          by destruct ty.
         split; last by [].
         move: (sizeN_read_wire HH1) => vbits_sz. 
         move: HH1; rewrite /read_wire /= => ->.
         rewrite -cat1s catA ?cats1.
         set gg':= rcons g' _.
         have ->: (N.pred (sizeN g') + 2) = sizeN gg'.
          by rewrite -N.sub_1_r /gg' sizeN_rcons; lia.
         change (read_wire (rcons gg' (if cond_ev then vbits else bits0 (wires_of_type ty))) (Some ty) (sizeN gg') = Some (if cond_ev then vbits else bits0 (wires_of_type ty))).
         rewrite read_wire_last read_wire_first //.
         case: (ifP _) => _; first by rewrite vbits_sz.
         by rewrite sizeN_bits0.
       have En: sizeN code = n.
        by move: H1; rewrite sizeN_size size_cat Nat2N.inj_add -?sizeN_size /=; lia.
       unfold add_gate_ty_spec, add_gate_spec in *; hsplit.
       rewrite !rev_cons -?cats1 /=.
       have Hsub': subseq l flat_phi by apply (subseq_cons_s Hsub).
       move: (Mlocal _ _ _ H2 H5); rewrite /read_wire; move => [vbits [HH1 HH2]].
       move: (conn_eval_isS_sizeN HH1); rewrite sizeN_conn_ty => vbits_sz.
       set cond_ev := full_eval_guard g' c'.
       move: (IH code ([:: {| gate := Gguard c'; conn := conn_guard c' |}
                        ,  {| gate := GbarrierN (wires_of_type ty);
                              conn := (N.pred (sizeN g') + sizeN code + 1, 0) :: conn_ty ty gw |}
                        ,  {| gate := GxorN (wires_of_type ty);
                              conn := conn_ty ty (N.pred (sizeN g') + sizeN code) ++
                                              conn_ty ty (N.pred (sizeN g') + sizeN code + 2) |}
                        &  ges']) g' M Hsub' H6) => [gss [Hss1 [Hss2 Hss3]]].
       eexists; split.
        rewrite -!catA /=.
        eapply (plus_star_trans Hss1); clear Hss1; last reflexivity.
        econstructor; last by rewrite (Events.E0_left [::]).
         constructor; first reflexivity.
         exists [:: cond_ev].
         split; last reflexivity.
         rewrite /gate_eval (conn_eval_isS_subgrid _ Hev_guard) /= Hev_cond; f_equal.
         by rewrite /cond_ev /full_eval_guard Hev_guard Hev_cond /=.
        econstructor; last by rewrite (Events.E0_left [::]).
         constructor; first reflexivity.
         exists (if cond_ev
            then vbits
            else bits0 (wires_of_type ty)).
         split; last reflexivity.
         rewrite /gate_eval /=.
         have T1: conn_eval ((g' ++ gss) ++ [:: [:: cond_ev]])
                            [:: (N.pred (sizeN g')+sizeN code+1, 0)]
                  = Some [:: cond_ev].
          have ->: N.pred (sizeN g') + sizeN code + 1 = sizeN (g'++gss).
           by rewrite -N.sub_1_r ?sizeN_size size_cat Nat2N.inj_add -!sizeN_size; lia.
          by rewrite /conn_eval /wire_eval cats1 /= nth_rcons_last.
         have T2: conn_eval ((g'++gss) ++ [:: [:: full_eval_guard g' c']]) (conn_ty ty gw) = Some vbits.
          by rewrite -catA; apply conn_eval_isS_subgrid.
         rewrite -cats1 (conn_eval_cat T1 T2) /=; f_equal.
         case: (ifP _) => _.
          rewrite takeN_all; last first. 
           by rewrite -vbits_sz; reflexivity.
          by rewrite takeN_dflt_all'.
         rewrite takeN_dflt_all'; last by rewrite sizeN_takeN_dflt.
         rewrite takeN_dflt_split /= ?N.sub_0_r ?bits0_nseqN //.
         by destruct ty.
        econstructor; last by rewrite (Events.E0_left [::]).
         constructor; first reflexivity.
         exists (if full_eval_guard g' c'
            then vbits
            else get_phi_assoc localv ty g' l).
         split; last reflexivity.
         rewrite /gate_eval /=.
         set gg':= (rcons (_++_) _).
         have T1: conn_eval (rcons gg' (if cond_ev then vbits else bits0 (wires_of_type ty)))
                            (conn_ty ty (N.pred (sizeN g') + sizeN code))
                  = Some (get_phi_assoc localv ty g' l).
          rewrite /gg' -!cats1 -?catA catA.
          by apply conn_eval_isS_subgrid.
         have T2: conn_eval (rcons gg' (if cond_ev then vbits else bits0 (wires_of_type ty)))
                            (conn_ty ty (N.pred (sizeN g') + sizeN code + 2))
                  = Some (if cond_ev then vbits else bits0 (wires_of_type ty)).
          have ->: N.pred (sizeN g') + sizeN code + 2 = sizeN gg'.
           symmetry; rewrite /gg' sizeN_rcons sizeN_size size_cat Nat2N.inj_add -!sizeN_size.
           rewrite -N.sub_1_r; lia.
          change (read_wire (rcons gg' (if cond_ev then vbits else bits0 (wires_of_type ty)))
                            (Some ty) (sizeN gg')
                  = Some (if cond_ev then vbits else bits0 (wires_of_type ty))).
          rewrite read_wire_last read_wire_first //.
          case: (ifP _) => _; first by rewrite vbits_sz.
          by rewrite sizeN_bits0.
         rewrite (conn_eval_cat T1 T2) {T1 T2} /=; f_equal.
         rewrite /eval_GxorN /cond_ev takeN_take take_size_cat; last first.
          by rewrite size_sizeN sizeN_get_phi_assoc; apply Nat2N.inj; rewrite !N2n2N.
         rewrite dropN_sizeN_cat; last by apply sizeN_get_phi_assoc.
         rewrite takeN_all; last first.
          case: (ifP _) => _.
           rewrite -vbits_sz; reflexivity.
          rewrite sizeN_bits0; reflexivity.
         case: (ifP _) => Hc'.
          rewrite takeN_dflt_all'; last first.
           by rewrite sizeN_xor_bits sizeN_get_phi_assoc.
          erewrite get_phi_assoc_tailP; eauto.
          by rewrite xor_bitsC xor_bits_blk0.
         rewrite xor_bits_blk0; last by apply sizeN_get_phi_assoc.
         by rewrite takeN_dflt_all'; last by rewrite sizeN_get_phi_assoc.
        rewrite -!cats1 -?catA.
        by apply star_refl.
       clear Hss1; split; last first.
        by rewrite -Hss3 ?sizeN_size size_cat /= Nat2N.inj_add N.add_comm.
       move: H2; rewrite /is_localv nsucc_pospred=> H2.
       rewrite H2 HH1 ?catA cats1.
       set gg':= (_ ++ _).
       have ->: (N.pred (sizeN g') + (3 + sizeN code)) = sizeN gg'.
        by rewrite -N.sub_1_r /gg' ?sizeN_size ?size_cat /= ?Nat2N.inj_add -!sizeN_size -Hss3; lia.
       change (read_wire (rcons gg' (if cond_ev then vbits else get_phi_assoc localv ty g' l)) (Some ty) (sizeN gg') = Some (if cond_ev then vbits else get_phi_assoc localv ty g' l)).
       rewrite read_wire_last read_wire_first //.
       case: (ifP _) => _; first by rewrite -vbits_sz.
       by rewrite sizeN_get_phi_assoc.
     } 
     move: (@subseq_refl _ flat_phi) => Hsub.
     move: (Xtra _ _ Hsub Hphi) => [g2]; rewrite revK sizeN_rev; move =>  [H1g2 [H2g2 H3g2]].
     exists (State ges' [seq i.2 | i <- outs] oc (g'++g2)); split.
      assumption.
     exists condv,localv,globvi,globvf,ges',oc,(g'++g2).
     split; first eassumption.
     have ->: N.pred (sizeN (g' ++ g2)) = N.pred (sizeN g') + sizeN ges.
      by rewrite -!N.sub_1_r sizeN_size size_cat Nat2N.inj_add -?sizeN_size H3g2; lia.
     split.
      rewrite -appE cats1 sizeN_rcons.
      by apply Hcode.
     split; last by split.
     move: M => [Mlocal [Mglob Mconst]].
     split; first last.
      split; first by apply match_grid_global_add_cat.
      rewrite /match_grid_const.
      by apply onthN_isS_cat, Mconst.
     move=> w oty gn Hw.
     rewrite -appE cats1 sizeN_rcons.
     rewrite N.add_1_r N.lt_succ_r N.lt_eq_cases; move => [Hsz|Hsz].
     move: (Mlocal w oty gn Hw Hsz) => [bs [Hread Hmatch]].
     exists bs; split.
      rewrite read_wire_catl //.
      by eauto using read_wire_lt.
     rewrite -cats1 appE /ValCirc.read_wire ValCirc.nth_app.
     case: (ifP _); first by [].
      by move: Hsz; rewrite sizeN_nlen N.ltb_nlt.
     move: Hw; rewrite Hsz => Hw.
     move: (is_localv_inj Hw H2) => [[Ety] Egn]; subst.
     case E: (eval_phiNode pcm φ) => [v|]; last first.
      exists (bits0 (wires_of_type ty)).
      rewrite /read_wire sizeN_rev H2g2.
      split; first by rewrite /flat_phi (eval_phiNode_isN _ Hcw H H0).
      rewrite -cats1 appE /ValCirc.read_wire ValCirc.nth_app.
      case: (ifP _).
       rewrite sizeN_nlen /ValCirc.nlen.
       by move=> /N.ltb_lt LT; lia.
      by move=> _; rewrite sizeN_nlen N.sub_diag.
     move: (eval_phiNode_isS Hcw H Mlocal H0 Hphi E) => [HH3 [gn [HH1 HH2]]].
     move: (Mlocal _ _ _ HH1 HH3); rewrite /read_wire; move => [v' [H1v' H2v']].
     exists v'.
     split.
      by rewrite /read_wire sizeN_rev H2g2 -HH2 -H1v'.
     rewrite -cats1 appE /ValCirc.read_wire ValCirc.nth_app.
     case: (ifP _).
      rewrite sizeN_nlen /ValCirc.nlen.
      by move=> /N.ltb_lt HH; lia.
     by move=> _; rewrite sizeN_nlen N.sub_diag /=.
   }

 + intros sp ssz m outs ? ? (-> & ->).
   intros ? (globv & oc & g' & Mconst & M & Hout & ->).
   eexists; split; first by apply plus_one; simpl; eauto.
   by simpl; eauto 7.

 + intros sp ssz m outs ? ? (-> & ->).
   intros ? (globv & oc & g' & Mconst & M & Hout & ->).
   eexists; split; first by apply plus_one; simpl; eauto.
   by simpl; eauto 9.

 + intros [ (v, dst) | ] outs sp ssz m tr s'.
  * intros (b & ev & V & Hb & -> & Hev & ->).
    intros ? (globv & oc & g' & ? & (v' & Hvv' & ->) & Mconst & M & Hout & ->).
    eexists; split.
     apply plus_one.
     exists b, ev; split.
      by simpl; erewrite Genv.block_is_volatile_transf_partial by apply TR; exact V.
     split. 
      by simpl; erewrite Genv.find_symbol_transf_partial by apply TR; exact Hb.
     split; first reflexivity.
     split; first by eauto using eventval_match_transf.
     reflexivity.
    by simpl; eauto 9.
  * destruct outs as [ | ((x, o), dst) ].
     intros (-> & ->).
     intros ? (globv & oc & g' & ? & -> & Mconst & M & Hout & ->).
     eexists; split; first apply plus_one; simpl; eauto.
     intros (-> & v & Hv & ->).
     intros ? (globv & oc & g' & ? & -> & Mconst & M & Hout & ->).
     destruct Hout as (c & co & Hc & -> & Hout).
     generalize M; intros (bstk & Hbstk & Hstk & Hgv).
     generalize (Hgv _ _ Hc); clear Hgv.
     intros (b & gv & MB' & Hvol & Hb & Hdiff & Hgv).
     destruct (mb_load MB') as (mbs & bs' & Hmbs & Hbs' & MB).
     rewrite /Mem.loadv /Genv.symbol_address Hb in Hv.
     set (sz := Genv.init_data_list_size (gvar_init gv)).
     assert (sz = Int.unsigned o + (1 + (sz - Int.unsigned o - 1)))%Z as PM by lia.
     fold sz in Hmbs.
     rewrite PM in Hmbs.
     generalize (λ X, mb_bounds MB' _ (proj1 (Mem.load_valid_access _ _ _ _ _ Hv) _ (conj (Z.le_refl _) X))). 
     fold sz.
     unfold size_chunk; intros X.
     destruct (Mem.loadbytes_split _ _ _ _ _ _ Hmbs) as (mbsL & mbs' & LBL & LB' & ->).
     clear; generalize (Int.unsigned_range o); first lia.
     clear -X; lia.
    destruct (Mem.loadbytes_split _ _ _ _ _ _ LB') as (mbsM & mbsR & LBM & LBR & ->).
      lia.
     clear -X; lia.
    pose proof (Mem.load_loadbytes _ _ _ _ _ Hv) as (mbs' & Hv' & DV).
    simpl in LBM; rewrite /= LBM in Hv'; apply Some_eq in Hv'; subst mbs'.
    move/all2_catIl: MB => [bsL [bs'' [E1 [MBL MB]]]].
    move/all2_catIl: MB => [bsM [bsR [E2 [MBM MBR]]]].
    eexists; split.
     apply plus_one; simpl.
     split; first reflexivity.
     eexists _, _, (bits_of_bytes bsM).
     apply loadbytes_isS_sizeN in LBL.
     apply loadbytes_isS_sizeN in LBM.
     split; first reflexivity.
     split.
      by rewrite /conn_size sizeN_nlen /ValCirc.nlen lengthE size_takeN_dflt.
     split; last reflexivity.
     rewrite (conn_eval_isS_sub _ _ Hbs').
      f_equal; rewrite E1 E2 2!bits_of_bytes_cat dropN_sizeN_cat.
       rewrite -> takeN_dflt_catl, takeN_dflt_eqsize; auto.
        by rewrite -> sizeN_bits_of_bytes, <- (all2_sizeN MBM), LBM; easy.
       by rewrite -> sizeN_bits_of_bytes, <- (all2_sizeN MBM), LBM; easy.
      by rewrite -> sizeN_bits_of_bytes, <- (all2_sizeN MBL), LBL; easy.
     by apply match_grid_const_is_grid; assumption.
    eexists globv, co, g', _.
    split; [|split;[assumption|split;[assumption|split; [assumption|reflexivity]]]].
    eexists; split; [|reflexivity].
    rewrite DV.
    generalize (Mem.loadbytes_length _ _ _ _ _ LBM).
    destruct mbsM as [ | byt [ | ]]; try discriminate.
    intros _.
    destruct bsM as [ | byt' [|]] => //.
     move: MBM => /= /andP [MB _].
     unfold int32_of_bits; simpl; rewrite Z_of_bits_of_byte.
     subst; destruct byt. 
       by right.
      rewrite decode_one_byte Z.add_0_r.
      by simpl in *; rewrite (eqP MB); left.
     easy.
    by move: MBM => /=; rewrite andbF. 

 + intros sp ssz m ? ? (-> & b & -> & m' & Hm' & ->).
   intros ? ->.
   eexists; split; first by apply plus_one; simpl; eauto.
   reflexivity.

 + intros ? ? ().
Qed.



End SIMULATION.
