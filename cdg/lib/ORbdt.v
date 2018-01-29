(** * Ordered-Reduced Binary Decision Trees *)

Require Import ssreflect ssrfun ssrbool ssrnat eqtype seq.
Require Import BinPos zint.
Require Import Integers ssrValues.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Lemma submem_trans {A} : forall (p1 p2 p3: mem_pred A),
 sub_mem p1 p2 -> sub_mem p2 p3 -> sub_mem p1 p3.
Proof. by move=> p1 p2 p3 H1 H2 x Hx; apply H2; apply H1. Qed.



Definition ident := positive.

Section BDT.

Variable A: eqType.

Inductive bdd :=
 | Leaf : A -> bdd
 | Node : positive -> bdd -> bdd -> bdd.

Fixpoint bdd_eq (bdd1 bdd2: bdd) : bool :=
 match bdd1, bdd2 with
 | Leaf x1, Leaf x2 => x1==x2
 | Node v1 l1 r1, Node v2 l2 r2 =>
    (v1==v2) && bdd_eq l1 l2 && bdd_eq r1 r2
 | _, _ => false
 end.

Lemma bdd_eq_refl: forall p, bdd_eq p p.
Proof.
elim => //=.
move=> v p IH1 q IH2.
by rewrite eq_refl IH1 IH2.
Qed.

Lemma bdd_eqP : Equality.axiom bdd_eq.
Proof.
move=> p q; apply: (iffP  idP)=>[|<-]; last first.
 by rewrite /bdd_eq; apply bdd_eq_refl.
elim: p q.
 move=> x [y|y l r] => //=.
 by move=> /eqP ->.
move=> x l IH1 r IH2 [y| y l' r'] //=.
move=> /andP [/andP [/eqP -> H1] H2].
f_equal.
 by apply IH1.
by apply IH2.
Qed.

Canonical Structure bdd_eqMixin := EqMixin bdd_eqP.
Canonical Structure bdd_eqType := Eval hnf in @EqType bdd bdd_eqMixin.

(** * Evaluation of BDTs *)

(** Propositional models are captured as sequences of (true) propositions
*)
Definition pEnv := seq ident.


Fixpoint eval_bdd (m: pEnv) (t: bdd) : A :=
 match t with
 | Leaf b => b
 | Node v l r => if v \in m then eval_bdd m l else eval_bdd m r
 end.

(* Set of variables that appear in a formula *)
Fixpoint literal_of_bdd (bdd: bdd) : list positive :=
  match bdd with
  | Leaf _ => nil
  | Node p ℓ r => p :: literal_of_bdd ℓ ++ literal_of_bdd r
  end.

Definition chkN v bdd1 bdd2 :=
 if bdd_eq bdd1 bdd2 then bdd1 else Node v bdd1 bdd2.

Lemma chkNP: forall v (bdd1 bdd2: bdd) m,
 eval_bdd m (chkN v bdd1 bdd2) =
 if v\in m then eval_bdd m bdd1 else eval_bdd m bdd2.
Proof.
rewrite /chkN => v bdd1 bdd2 m.
case: (ifP _) => // /eqP ->.
by case: (ifP _).
Qed.

Lemma literal_of_chkN: forall v (t1 t2: bdd),
 {subset literal_of_bdd (chkN v t1 t2) 
  <= v::literal_of_bdd t1 ++ literal_of_bdd t2}.
Proof.
move=> v l r; rewrite /chkN.
 case: (ifP _) => _ x //= Hx.
by rewrite in_cons mem_cat; apply/orP; right; apply/orP; left.
Qed.

(*
(** test if a bdd is an ordered-reduced tree *)
Fixpoint bdd_prop bound bdd :=
 match bdd with
 | Leaf _ => true
 | Node v l r => [&& (Pos.ltb bound v), (l!=r), bdd_prop v l & bdd_prop v r]
 end.

Definition bddE bdd : bool :=
  match bdd with
  | Leaf _ => true
  | Node v l r => [&& (l!= r), bdd_prop v l & bdd_prop v r]
  end.

Lemma bdd_prop_bddE: forall bdd v,
 bdd_prop v bdd -> bddE bdd.
Proof.
elim => //=.
move=> bound l H1 r H2 v /and4P [Ha Hb Hc Hd].
by apply/and3P; split.
Qed.

Lemma chkN_prop: forall v bdd1 bdd2,
 bdd_prop v bdd1 -> bdd_prop v bdd2 -> bddE (chkN v bdd1 bdd2).
Proof.
move=> v bdd1 bdd2 H1 H2; rewrite /chkN.
case: (ifP _).
 by move=> _; apply: bdd_prop_bddE; apply H1.
move=> /eqP H /=; apply/and3P; split => //.
by apply/eqP.
Qed.
*)
End BDT.

Fixpoint bdd_map {A B: eqType} (f:A->B) (x: bdd A) : bdd B :=
 match x with
 | Leaf a => Leaf (f a)
 | Node v l r => chkN v (bdd_map f l) (bdd_map f r)
 end.


(** ** Propositional formulas (path-conditions)

  A first use of BDDs is a canonical encoding of propositional formulas,
  that we use to characterise "path-conditions" (hence the [pcond] name).
  These BDDs have boolean leafs
 *)
Definition pcond := (bdd bool_eqType).

Notation eval_pcond := (@eval_bdd bool_eqType).
Notation pcondT := (Leaf true).
Notation pcondF := (Leaf false).

Lemma pcondTP: forall m, eval_pcond m pcondT = true.
Proof. by []. Qed.

Lemma pcondFP: forall m, eval_pcond m pcondF = false.
Proof. by []. Qed.

(* building BDDs *)
Definition pcond_lit v : pcond := Node v pcondT pcondF.
Definition pcond_litN v : pcond := Node v pcondF pcondT.

Lemma pcond_litP: forall m v, eval_pcond m (pcond_lit v) = (v \in m).
Proof. by move=> m v //=; case: (ifP _). Qed.

Lemma pcond_litNP: forall m v, eval_pcond m (pcond_litN v) = (v \notin m).
Proof. by move=> m v //=; case: (ifP _). Qed.

Fixpoint pcond_not (bdd: pcond) : pcond :=
 match bdd with
 | Leaf x => Leaf (~~ x)
 | Node v l r => Node v (pcond_not l) (pcond_not r)
 end.

Lemma pcond_notP: forall bdd m,
 eval_pcond m (pcond_not bdd) = ~~(eval_pcond m bdd).
Proof. 
elim=> //=.
by move=> v l IHl r IHr m; case: (ifP _).
Qed.

Fixpoint pcond_and (bdd1: pcond) : pcond -> pcond :=
 match bdd1 with
 | pcondT => id
 | pcondF => fun _ => pcondF
 | Node v1 l1 r1 =>
    fix aux bdd2 : pcond :=
     match bdd2 with
     | pcondT => bdd1
     | pcondF => pcondF
     | Node v2 l2 r2 =>
        if v1==v2
        then chkN v1 (pcond_and l1 l2) (pcond_and r1 r2)
        else if (Pos.ltb v1 v2)
             then chkN v1 (pcond_and l1 bdd2) (pcond_and r1 bdd2)
             else chkN v2 (aux l2) (aux r2)
     end
 end.

Lemma pcond_andP: forall bdd1 bdd2 m,
 eval_pcond m (pcond_and bdd1 bdd2) = (eval_pcond m bdd1 && eval_pcond m bdd2).
Proof. 
elim; first by move=> [|] bdd2 m.
move=> v l IHl r IHr.
elim => [[|]|v' l' IHl' r' IHr'] m.
  by rewrite /= andbT.
 by rewrite !pcondFP andbF.
rewrite /=.
case: (ifP _) => [/eqP ->|Ha].
 by rewrite chkNP; case: (ifP _).
case: (ifP _) => Hb.
 rewrite chkNP IHl IHr /=.
 by case: (ifP _); case: (ifP _).
rewrite chkNP IHl' IHr' /=.
by case: (ifP _); case: (ifP _).
Qed.

Fixpoint pcond_or (bdd1: pcond) : pcond -> pcond :=
 match bdd1 with
 | pcondT => fun _ => pcondT
 | pcondF => id
 | Node v1 l1 r1 =>
    fix aux bdd2 : pcond :=
     match bdd2 with
     | pcondT => pcondT
     | pcondF => bdd1
     | Node v2 l2 r2 =>
        if v1==v2
        then chkN v1 (pcond_or l1 l2) (pcond_or r1 r2)
        else if (Pos.ltb v1 v2)
             then chkN v1 (pcond_or l1 bdd2) (pcond_or r1 bdd2)
             else chkN v2 (aux l2) (aux r2)
     end
 end.

Lemma pcond_orP: forall bdd1 bdd2 m,
 eval_pcond m (pcond_or bdd1 bdd2) = (eval_pcond m bdd1 || eval_pcond m bdd2).
Proof. 
elim; first by move=> [|] bdd2 m.
move=> v l IHl r IHr.
elim => [[|]|v' l' IHl' r' IHr'] m.
  by rewrite /= orbT.
 by rewrite !pcondFP orbF.
rewrite /=.
case: (ifP _) => [/eqP ->|Ha].
 by rewrite chkNP; case: (ifP _).
case: (ifP _) => Hb.
 rewrite chkNP IHl IHr /=.
 by case: (ifP _); case: (ifP _).
rewrite chkNP IHl' IHr' /=.
by case: (ifP _); case: (ifP _).
Qed.

Definition pcond_implE bdd1 bdd2 :=
 forall m, eval_pcond m bdd1 -> eval_pcond m bdd2.

(* quering BDDs *)

(* check of two path-conditions are disjoint *)
Definition pcond_disjoint bdd1 bdd2 := (pcond_and bdd1 bdd2 == pcondF).

Lemma pcond_disjoint_w x y m :
  pcond_disjoint x y = true ->
  eval_pcond m x = true ->
  eval_pcond m y = false.
Proof.
  unfold pcond_disjoint. case eqP. 2: discriminate.
  intros H _ Hx. generalize (pcondFP m).
  rewrite <- H, pcond_andP, Hx. exact id.
Qed.

(* check for implication *)
Definition bdd_leq bdd1 bdd2 := (pcond_or (pcond_not bdd1) bdd2 == pcondT).

Lemma bdd_leq_w x y m :
  bdd_leq x y = true ->
  eval_pcond m x = true ->
  eval_pcond m y = true.
Proof.
  unfold bdd_leq. case eqP. 2: discriminate.
  intros H _ Hx. generalize (pcondTP m).
  rewrite <- H, pcond_orP, pcond_notP, Hx.
  exact id.
Qed.

(** * PhiNode

 [phiNode] is a BDD-like structure that store the information regarding
 the variable indexes. It can be seen as a map whose key is propositional
 and values are variable indexes.
*)

Definition phiNode := bdd [eqType of option ident].

Notation eval_phiNode := (@eval_bdd [eqType of (option ident)]).
Notation phi_single v := (Leaf (Some v)).

Section BDD_ADD.

Context {T: eqType}.
(** [phi_add cond r phi] updates the phi-information [phi] with a new
 association to [r] whenever [cond] holds. *)
Fixpoint phi_add (b: pcond) (r: T) : bdd [eqType of option T] -> _ :=
 match b with
 | pcondT => fun _ => Leaf (Some r)
 | pcondF => id
 | Node v1 l1 r1 =>
    fix aux phi :=
     match phi with
     | Leaf x => chkN v1 (phi_add l1 r phi) (phi_add r1 r phi)
     | Node v2 l2 r2 =>
         if v1==v2
         then chkN v1 (phi_add l1 r l2) (phi_add r1 r r2)
         else if Pos.ltb v1 v2
              then chkN v1 (phi_add l1 r phi) (phi_add r1 r phi) 
              else chkN v2 (aux l2) (aux r2)
     end
 end.

Lemma phi_add_E1: forall x v l r l' r',
 phi_add (Node v l r) x (Node v l' r')
 = chkN v (phi_add l x l') (phi_add r x r').
Proof.
move => x v l r l' r' /=.
case: (ifP _) => // /eqP E1.
case: (ifP _) => //=.
Qed.

Lemma phi_add_E2: forall x v l r v' l' r',
 (v <? v')%positive ->
 phi_add (Node v l r) x (Node v' l' r')
 = chkN v (phi_add l x (Node v' l' r')) (phi_add r x (Node v' l' r')).
Proof.
move => x v l r v' l' r' Hvv' /=.
case: (ifP _) => // E.
 by move: Hvv'; rewrite (eqP E) Pos.ltb_irrefl.
case: (ifP _) => //.
by rewrite Hvv'.
Qed.

Lemma phi_add_E3: forall x v l r v' l' r',
 (v' <? v)%positive ->
 phi_add (Node v l r) x (Node v' l' r')
 = chkN v' (phi_add (Node v l r) x l') (phi_add (Node v l r) x r').
Proof.
move => x v l r v' l' r' Hvv' /=.
case: (ifP _) => // E.
 by move: Hvv'; rewrite (eqP E) Pos.ltb_irrefl.
case: (ifP _) => //.
move: Hvv'; rewrite /is_true Pos.ltb_lt => Hvv'.
by rewrite /is_true Pos.ltb_lt => Hv'v; Pos.order.
Qed.

Lemma bdd_addP x bdd b m :
  eval_bdd m (phi_add b x bdd)
  = if eval_pcond m b then Some x else eval_bdd m bdd.
Proof.
elim: b bdd => //=.
 by move=> [|].
move=> v1 l1 IHl1 r1 IHr1.
elim => //=.
 move=> y; case: ifP; case: ifP.
    rewrite chkNP => -> l1_eval.
    by rewrite IHl1 l1_eval.
   rewrite chkNP => -> l1_eval.
   by rewrite IHr1 l1_eval.
  rewrite chkNP => -> l1_eval.
  by rewrite IHl1 l1_eval.
 rewrite chkNP => -> l1_eval.
 by rewrite IHr1 l1_eval.
move=> v2 l2 IHl2 r2 IHr2.
case: ifP => E.
 rewrite (eqP E) chkNP; case: ifP => vIN.
  by rewrite IHl1. 
 by rewrite IHr1.
case: ifP => E2.
 rewrite chkNP; case: ifP => vIN.
  by rewrite IHl1. 
 by rewrite IHr1.
rewrite chkNP; case: ifP => vIN.
 by rewrite IHl2. 
by rewrite IHr2.
Qed.

Lemma literal_of_phi_add g w φ :
  {subset literal_of_bdd (phi_add g w φ)
   <= literal_of_bdd g ++ literal_of_bdd φ}.
Proof.
elim: g φ.
 by move=> [|] φ v /=.
move=> v1 l1 IHl1 r1 IHr1.
elim.
 move=> x /=. 
 eapply submem_trans; first by apply literal_of_chkN.
 rewrite cats0 => v; rewrite in_cons => /orP [/eqP ->|].
  by rewrite in_cons eq_refl.
 rewrite mem_cat => /orP [H|H]; rewrite in_cons mem_cat; apply/orP; right.
  move: {H} (IHl1 _ _ H); rewrite mem_cat /= in_nil orbF => H.
  by apply/orP; left.
 move: {H} (IHr1 _ _ H); rewrite mem_cat /= in_nil orbF => H.
 by apply/orP; right.
move=> v2 l2 IHl2 r2 IHr2 /=.
case: ifP.
 move=> /eqP <-.
 eapply submem_trans; first by apply literal_of_chkN.
 move => v; rewrite in_cons => /orP [/eqP ->|].
  by rewrite in_cons eq_refl.
 rewrite mem_cat => /orP [H|H]; rewrite in_cons mem_cat; apply/orP; right.
  move: {H} (IHl1 _ _ H); rewrite mem_cat /= => /orP [H1|H1].
   by apply/orP; left; rewrite mem_cat H1.
  by apply/orP; right; rewrite in_cons mem_cat H1 orbT.
 move: {H} (IHr1 _ _ H); rewrite mem_cat /= => /orP [H1|H1].
   by apply/orP; left; rewrite mem_cat H1 orbT.
  by apply/orP; right; rewrite in_cons mem_cat H1 !orbT.
move=> E; case: ifP => E2.
 eapply submem_trans; first by apply literal_of_chkN.
 move => v; rewrite in_cons => /orP [/eqP ->|].
  by rewrite in_cons eq_refl.
 rewrite mem_cat => /orP [H|H]; rewrite in_cons mem_cat; apply/orP; right.
  move: {H} (IHl1 _ _ H); rewrite mem_cat /= => /orP [H1|H1].
   by apply/orP; left; rewrite mem_cat H1.
  by apply/orP; right.
 move: {H} (IHr1 _ _ H); rewrite mem_cat /= => /orP [H1|H1].
  by apply/orP; left; rewrite mem_cat H1 orbT.
 by apply/orP; right.
eapply submem_trans; first by apply literal_of_chkN.
move => v; rewrite in_cons => /orP [/eqP ->|].
 rewrite in_cons; apply/orP; right. 
 by rewrite mem_cat in_cons eq_refl; apply/orP; right. 
rewrite mem_cat => /orP [H|H]; rewrite in_cons mem_cat.
 move: {H} (IHl2 _ H); rewrite mem_cat /=.
  rewrite in_cons mem_cat => /orP [H1|H1].
  rewrite !orbA; apply/orP; left. apply/orP; left.
  by rewrite -!orbA.
 rewrite in_cons !orbA; apply/orP; right.
 by rewrite mem_cat; apply/orP; left.
move: {H} (IHr2 _ H); rewrite mem_cat /=.
 rewrite in_cons mem_cat => /orP [H1|H1].
 rewrite !orbA; apply/orP; left. apply/orP; left.
 by rewrite -!orbA.
rewrite in_cons !orbA; apply/orP; right.
by rewrite mem_cat; apply/orP; right.
Qed.

End BDD_ADD.

Corollary phi_addP:
 forall x phi b (m:pEnv),
  eval_phiNode m (phi_add b x phi)
  = if eval_pcond m b then Some x else eval_phiNode m phi.
Proof. apply bdd_addP. Qed.

Section BDD_SLICING.

Definition chkN_slice {A} v (l: bdd A) lcond r rcond :=
 if lcond is pcondF
 then r
 else if rcond is pcondF
      then l
      else chkN v l r.

Lemma chkN_sliceP: forall A v (bdd1 bdd2: bdd A) c1 c2 m,
 eval_pcond m (Node v c1 c2) ->
 eval_bdd m (chkN_slice v bdd1 c1 bdd2 c2) =
 if v\in m 
 then eval_bdd m bdd1
 else eval_bdd m bdd2.
Proof.
rewrite /chkN => A v bdd1 bdd2 c1 c2 m /=.
case: (ifP _) => /= Hv.
 by  move: c1 c2 => [[|]|v1 l1 r1] [[|]|v2 l2 r2] //=; rewrite chkNP Hv.
by  move: c1 c2 => [[|]|v1 l1 r1] [[|]|v2 l2 r2] //=; rewrite chkNP Hv.
Qed.

Context {T: eqType}.

Fixpoint phi_slice (phi: bdd [eqType of option T]) : pcond -> bdd [eqType of option T] :=
 match phi with
 | Leaf x => fun cond => Leaf (if cond is pcondF then None else x)
 | Node v l r =>
    fix aux cond :=
     match cond with
     | pcondT => phi
     | pcondF => Leaf None
     | Node v' l' r' =>
        if v==v'
        then chkN_slice v (phi_slice l l') l' (phi_slice r r') r'
        else if Pos.ltb v v'
             then chkN v (phi_slice l cond) (phi_slice r cond)
             else chkN_slice v' (aux l') l' (aux r') r'
     end
 end.

Lemma phi_slice_E1: forall v l r l' r',
 phi_slice (Node v l r) (Node v l' r')
 = chkN_slice v (phi_slice l l') l' (phi_slice r r') r'.
Proof.
move => v l r l' r' /=.
case: (ifP _) => // /eqP E1.
case: (ifP _) => //=.
Qed.

Lemma phi_slice_E2: forall v l r v' l' r',
 (v <? v')%positive ->
 phi_slice (Node v l r) (Node v' l' r')
 = chkN v (phi_slice l (Node v' l' r')) (phi_slice r (Node v' l' r')).
Proof.
move => v l r v' l' r' Hvv' /=.
case: (ifP _) => // E.
 by move: Hvv'; rewrite (eqP E) Pos.ltb_irrefl.
case: (ifP _) => //.
by rewrite Hvv'.
Qed.

Lemma phi_slice_E3: forall v l r v' l' r',
 (v' <? v)%positive ->
 phi_slice (Node v l r) (Node v' l' r')
 = chkN_slice v' (phi_slice (Node v l r) l') l' (phi_slice (Node v l r) r') r'.
Proof.
move => v l r v' l' r' Hvv' /=.
case: (ifP _) => // E.
 by move: Hvv'; rewrite (eqP E) Pos.ltb_irrefl.
case: (ifP _) => //.
move: Hvv'; rewrite /is_true Pos.ltb_lt => Hvv'.
by rewrite /is_true Pos.ltb_lt => Hv'v; Pos.order.
Qed.

Lemma bdd_sliceP:
 forall bdd b (m:pEnv),
  eval_pcond m b -> 
  eval_bdd m (phi_slice bdd b) = eval_bdd m bdd.
Proof.
elim.
 by move => [x|] [[|]|? ? ?] m H.
move => v l IHl r IHr.
elim; first by move => [|].
Opaque phi_slice.
move => v' l' IHl' r' IHr' m /=.
case: (ifP _) => Hv'.
 case: (ifP _) => Hv Hm.
  case E1: (v == v').
   rewrite -(eqP E1) phi_slice_E1 chkN_sliceP; last first. 
    by rewrite /= Hv.
   by rewrite Hv IHl.
  case E2: (v <? v')%positive.
   by rewrite phi_slice_E2 // chkNP Hv IHl //= Hv'.
  case E3: (v' <? v)%positive.
   rewrite phi_slice_E3 // chkN_sliceP; last first.
    by rewrite /= Hv'.
   by rewrite Hv' IHl' //= Hv.
  rewrite -> Pos.ltb_nlt in E2.
  rewrite -> Pos.ltb_nlt in E3.
  move/negP: E1; elim; apply/eqP; Pos.order.
 case E1: (v == v').
  by move: Hv' Hv; rewrite -(eqP E1) => ->.
 case E2: (v <? v')%positive.
  by rewrite phi_slice_E2 // chkNP Hv IHr //= Hv'.
 case E3: (v' <? v)%positive.
  rewrite phi_slice_E3 // chkN_sliceP; last first.
   by rewrite /= Hv'.
  by rewrite Hv' IHl' //= Hv.
 rewrite -> Pos.ltb_nlt in E2.
 rewrite -> Pos.ltb_nlt in E3.
 move/negP: E1; elim; apply/eqP; Pos.order.
case: (ifP _) => Hv Hm.
 case E1: (v == v').
  by move: Hv Hv'; rewrite -(eqP E1) => ->.
 case E2: (v <? v')%positive.
  by rewrite phi_slice_E2 // chkNP Hv IHl //= Hv'.
 case E3: (v' <? v)%positive.
  rewrite phi_slice_E3 // chkN_sliceP; last first.
   by rewrite /= Hv'.
  by rewrite Hv' IHr' //= Hv.
 rewrite -> Pos.ltb_nlt in E2.
 rewrite -> Pos.ltb_nlt in E3.
 move/negP: E1; elim; apply/eqP; Pos.order.
case E1: (v == v').
 rewrite -(eqP E1) phi_slice_E1 chkN_sliceP; last first.
  by rewrite /= Hv.
 by rewrite Hv IHr.
case E2: (v <? v')%positive.
 by rewrite phi_slice_E2 // chkNP Hv IHr //= Hv'.
case E3: (v' <? v)%positive.
 rewrite phi_slice_E3 // chkN_sliceP; last first.
  by rewrite /= Hv'.
 by rewrite Hv' IHr' //= Hv.
rewrite -> Pos.ltb_nlt in E2.
rewrite -> Pos.ltb_nlt in E3.
move/negP: E1; elim; apply/eqP; Pos.order.
Transparent phi_slice.
Qed.

Lemma phi_slice_pcondF phi (g:pcond):
  g = pcondF -> phi_slice phi g = Leaf None.
Proof.
elim: phi g => //=.
 by move => _ _ ->.
by move=> v l IHl r IHr g ->.
Qed.

End BDD_SLICING.

Corollary phi_sliceP (phi: phiNode) b (m: pEnv) :
  eval_pcond m b ->
  eval_phiNode m (phi_slice phi b) = eval_phiNode m phi.
Proof. apply (bdd_sliceP phi). Qed.

(** [phi_idents phi] collects the identifiers contained in a phi node *)
Fixpoint merge_idents (s1: seq ident)
  : seq ident -> seq ident :=
 if s1 is x::xs
 then fix merge_s1 (s2: seq ident) : seq ident :=
          if s2 is y::ys
          then if Pos.eqb x y
               then x :: merge_idents xs ys
               else if Pos.ltb x y
                    then x :: merge_idents xs s2
                    else y :: merge_s1 ys
          else s1
 else id.

Require Import path.

Lemma merge_identsP b xs ys:
 path Pos.ltb b xs -> 
 path Pos.ltb b ys -> 
 path Pos.ltb b (merge_idents xs ys).
Proof.
elim: xs ys b => // x xs IH1; elim => // y ys IH2 b /=.
move=> /andP [Hx Hxs] /andP [Hy Hys]; case: (ifP _).
 move=>  /Pos.eqb_eq E /=; apply/andP; split => //.
 apply IH1 => //.
 by rewrite E.
case: (ifP _) => LT En /=; apply/andP; split => //.
 by apply IH1 => //=; apply/andP; split.
apply IH2 => //=; apply/andP; split => //.
by apply Pos.ltb_lt; move: En LT; rewrite Pos.ltb_nlt Pos.eqb_neq; Pos.order.
Qed.

Lemma sorted_merge_idents: forall xs ys,
 sorted Pos.ltb xs -> sorted Pos.ltb ys -> sorted Pos.ltb (merge_idents xs ys).
Proof.
move=> [|x xs] [|y ys] //= Hxs Hys /=.
case: (ifP _).
 move=> /Pos.eqb_eq E /=.
 by apply merge_identsP => //; rewrite E.
move=> /Pos.eqb_neq En; case: (ifP _).
 by move=> LT /=; apply merge_identsP => //=; apply/andP.
move=> /Pos.ltb_nlt LT /=.
apply: (@merge_identsP y (x::xs) ys) => //=; apply/andP; split => //.
by apply Pos.ltb_lt; Pos.order.
Qed.

Lemma in_merge_idents s1 s2 v:
 v \in merge_idents s1 s2 = (v\in s1) || (v\in s2).
Proof.
elim: s1 s2 => //=.
move=> x xs IH1; elim => //.
 by rewrite orbF.
move=> y ys IH2.
case: (ifP _).
 move=> /Pos.eqb_eq <-.
 by rewrite !in_cons IH1; case: (v==x).
move=> H; case: (ifP _) => E'.
 by rewrite in_cons IH1 -!orbA.
rewrite in_cons IH2.
by symmetry; rewrite orbC in_cons -orbA [(v\in ys)||_]orbC.
Qed.

Fixpoint phi_idents (phi: phiNode) : list ident :=
 match phi with
 | Leaf None => [::]
 | Leaf (Some v) => [:: v]
 | Node _ l r => merge_idents (phi_idents l) (phi_idents r)
 end.

Lemma uniq_phi_idents phi: uniq (phi_idents phi).
Proof.
apply (@sorted_uniq _ Pos.ltb).
  by move=> x y z /Pos.ltb_lt H1 /Pos.ltb_lt H2; apply/Pos.ltb_lt; Pos.order.
 by apply: Pos.ltb_irrefl.
elim phi => //=.
 by move=> [x|].
by move=> v l IHl r IHr /=; apply sorted_merge_idents.
Qed.

Lemma eval_phiNode_idents phi v pcm:
 eval_phiNode pcm phi = Some v -> v \in phi_idents phi.
Proof.
elim: phi => //=.
 by move=> [v'|] // [->]; rewrite in_cons eq_refl.
move=> p l IHl r IHr; case: (ifP _) => Hp Hv.
 by rewrite in_merge_idents IHl.
by rewrite in_merge_idents IHr // orbT.
Qed.

(** [cond_of_phi x phi] returns the condition under which the phi node
 returns identifier [x] *)
Fixpoint cond_of_phi (x:ident) (phi:phiNode) : pcond :=
 match phi with
 | Leaf None => pcondF
 | Leaf (Some x') => if Pos.eqb x x'
                     then pcondT
                     else pcondF
 | Node v l r => chkN v (cond_of_phi x l) (cond_of_phi x r)
 end.

Lemma cond_of_phiP (phi:phiNode): forall pcm v,
 eval_phiNode pcm phi = Some v <-> eval_pcond pcm (cond_of_phi v phi).
Proof.
move=> pcm; elim: phi => //=.
 move=> [v'|] v //; case: (ifP _) => //.
  by move/Pos.eqb_eq => ->; split.
 move/Pos.eqb_neq. move=> H; split; move => // [E].
 by elim H; symmetry.
move=> p l IHl r IHr v.
rewrite chkNP; case: (ifP _) => H.
 by apply IHl.
by apply IHr.
Qed.

(** [flat_phi_node phi] converts a [phiNode] into a list of condition/ident
 pairs (to be used in the Iphi instruction) *)
Definition flat_phi_node (phi:phiNode) : list (pcond*ident) :=
 map (fun x => (cond_of_phi x phi,x)) (phi_idents phi).

Lemma flat_phiNodeP phi x y pcm:
 x \in (flat_phi_node phi) ->
 y \in (flat_phi_node phi) ->
 eval_pcond pcm x.1 ->
 eval_pcond pcm y.1 ->
 x.2 = y.2.
Proof.
move=> /mapP [vx Hvx ->] /mapP [vy Hvy ->] /= /cond_of_phiP H1 /cond_of_phiP.
by rewrite H1; move=> [->].
Qed.


Lemma subseq_flat_phiNode phi x xs pcm:
 subseq (x::xs) (flat_phi_node phi) ->
 eval_pcond pcm x.1 ->
 forall y, y\in xs -> eval_pcond pcm y.1 = false.
Proof.
move=> Hsub; move: (Hsub) => /(map_subseq snd) Hsub2 EV.
have: uniq (map snd (flat_phi_node phi)).
 by rewrite /flat_phi_node -map_comp /funcomp /= map_id uniq_phi_idents.
move=> /(subseq_uniq Hsub2) /= /andP [Hnin Huniq].
move=> y H /=.
case X: (eval_pcond pcm y.1) => //.
have E: x.2 = y.2.
 apply: (@flat_phiNodeP phi x y pcm) => //.
  by apply: (mem_subseq Hsub); rewrite in_cons; apply/orP; left.
 by apply: (mem_subseq Hsub); rewrite in_cons; apply/orP; right.
move/negP: Hnin; elim; rewrite E.
by apply map_f.
Qed.

(* BDDs as a semilattice with top *)
Require Import Lattice.

Module PCONDlatt <: SEMILATTICE_WITH_TOP.

  Definition t := pcond.
  Definition eq (x y: t) := (x = y).
  Definition eq_refl: forall x, eq x x := (@refl_equal t).
  Definition eq_sym: forall x y, eq x y -> eq y x := (@sym_equal t).
  Definition eq_trans: forall x y z, eq x y -> eq y z -> eq x z := (@trans_equal t).
  Definition beq (x y: t) : bool := x==y.
  Lemma beq_correct: forall x y, beq x y = true -> eq x y.
  Proof. by move=> x y /eqP ->. Qed.
  Definition ge x y := pcond_implE y x.
  Lemma ge_refl: forall x y, eq x y -> ge x y.
  Proof. by move=> x y -> m H. Qed.
  Lemma ge_trans: forall x y z, ge x y -> ge y z -> ge x z.
  Proof. by move=> x y z H1 H2 m H; apply H1; apply H2. Qed.
  Definition bot : t := pcondF.
  Lemma ge_bot: forall x, ge x bot.
  Proof. by move => x m; rewrite pcondFP. Qed.
  Definition top : t := pcondT.
  Lemma ge_top: forall x, ge top x.
  Proof. by move => x m; rewrite pcondTP. Qed. 
  Definition lub := pcond_or.
  Lemma ge_lub_left: forall x y, ge (lub x y) x.
  Proof. by move=> x y m H; rewrite pcond_orP H. Qed.
  Lemma ge_lub_right: forall x y, ge (lub x y) y.
  Proof. by move=> x y m H; rewrite pcond_orP H orbT. Qed.

End PCONDlatt.
