Require BinPos POrderedType.
Require ZArith Zbool.
Require NArith.

(** Adapted from the infra.v library from CAD project *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require choice bigop ssralg.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Import ZArith NArith.
Lemma pospred_ofsuccnat n:
  Pos.pred_N (Pos.of_succ_nat n) = N.of_nat n.
Proof.
by apply N2Nat.inj;
rewrite N.pos_pred_spec Nat2N.id N2Nat.inj_pred /= SuccNat2Pos.pred_id.
Qed.

Lemma n_succ_pos_inj {p q} :
  N.succ_pos p = N.succ_pos q ->
  p = q.
Proof.
move=> H; move: (f_equal Npos H).
by rewrite !N.succ_pos_spec; apply N.succ_inj.
Qed.



(** Shorter names for the bijection between [N] and [nat] *)
Notation N2n := N.to_nat.
Notation n2N := N.of_nat.
Notation N2n2N := N2Nat.id.
Notation n2N2n := Nat2N.id.
Notation nsuccI := N2Nat.inj_succ.

Require Import Psatz.
Lemma N2n_lt a b:
 (a < b)%num <-> (N2n a < N2n b).
Proof.
symmetry; split => [/ltP H | H]; [|apply/ltP]; lia.
Qed.

Lemma n2N_lt a b:
 (a < b) <-> (n2N a < n2N b)%num.
Proof.
split => [/ltP H | H]; [|apply/ltP]; lia.
Qed.

Lemma N2n_le a b:
 (a <= b)%num <-> (N2n a <= N2n b).
Proof.
symmetry; split => [/leP H | H]; [|apply/leP]; lia.
Qed.

Lemma n2N_le a b:
 (a <= b) <-> (n2N a <= n2N b)%num.
Proof.
split => [/leP H | H]; [|apply/leP]; lia.
Qed.

Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
(* Various eqtype, subtype, choice, count canonical structures          *)
(*               from the standard library                              *)
(* -------------------------------------------------------------------- *)

(* Structures on positive *)
Import BinPos.

Definition eqp (p q : positive) : bool :=
  match ( (Pos.compare_cont p q Eq))%positive with Eq => true | _ => false end.

Lemma eqpP : Equality.axiom eqp.
Proof.
move=> p q; apply: (iffP  idP)=>[|<-]; last by rewrite /eqp Pcompare_refl.
rewrite /eqp; case e: (Pos.compare_cont p q Eq)%positive=> // _; exact: Pcompare_Eq_eq.
Qed.

Canonical Structure eqp_Mixin := EqMixin eqpP.
Canonical Structure eqp_eqType := Eval hnf in @EqType positive eqp_Mixin.

Definition p_unpickle n := Some (Ppred (P_of_succ_nat n)).

Lemma p_pick_cancel : pcancel nat_of_P p_unpickle.
Proof.
move=> x; rewrite /p_unpickle; congr Some.
by rewrite Pnat.pred_o_P_of_succ_nat_o_nat_of_P_eq_id.
Qed.

Import choice.
Definition p_countMixin  := CountMixin p_pick_cancel.
Definition p_choiceMixin := CountChoiceMixin p_countMixin.

Canonical Structure p_choiceType :=
  Eval hnf in ChoiceType positive p_choiceMixin.
Canonical Structure p_countType :=
  Eval hnf in CountType positive p_countMixin.

Lemma eqNP: Equality.axiom N.eqb.
Proof.
move=> p q; apply: (iffP  idP)=>[|<-].
 by move=> /N.eqb_eq ->.
by rewrite N.eqb_refl.
Qed.

Canonical Structure eqN_Mixin := EqMixin eqNP.
Canonical Structure eqN_eqType := Eval hnf in @EqType N eqN_Mixin.

Section ComparisonAddendum.

(** First, we equip the comparison type with the eqType structure *)
Definition eq_comparison :=
 [rel x y | match x,y with Lt,Lt | Eq,Eq | Gt,Gt => true | _,_ => false end].
 
Lemma eq_comparisonP :  Equality.axiom eq_comparison.
Proof.
move=> x y; apply: (iffP idP) => [|<-]; last by elim x.
case: x; case: y; by [].
Qed.

Canonical Structure comparison_eqMixin := EqMixin eq_comparisonP.
Canonical Structure comparison_eqType := Eval hnf in @EqType _ comparison_eqMixin.

Implicit Arguments eq_comparisonP [x y].
Prenex Implicits eq_comparisonP.

Lemma eq_comparisonE : eq_comparison = eq_op :> rel _ . Proof. by []. Qed.

End ComparisonAddendum.

(* Structures on Z *)

Lemma eqzP : Equality.axiom Zeq_bool.
Proof. by move=> z1 z2;  apply: (iffP idP); move/Zeq_is_eq_bool. Qed.

Canonical Structure Z_Mixin := EqMixin eqzP.
Require Import ZArith.
Canonical Structure Z_eqType := Eval hnf in EqType Z Z_Mixin.

Definition z_code (z : Z) :=
  match z with
    |0%Z => (0%nat, true)
    |Zpos p => (pickle p, true)
    |Zneg p => (pickle p, false)
  end.

Definition z_pickle z := pickle (z_code z).

Definition z_decode c :=
  match c with
    |(0%nat, true) => Some 0%Z
    |(0%nat, false) => None
    |(n, true) =>
      if (@unpickle p_countType n) is Some p then Some (Zpos p) else None
    |(n, false) =>
      if (@unpickle p_countType n) is Some p then Some (Zneg p) else None
  end.

Definition z_unpickle n :=
  match (unpickle n) with
    |None => None
    |Some u => z_decode u
  end.

Lemma z_codeK : pcancel z_code z_decode.
Proof.
rewrite /z_code /z_decode.
case=> // n; case e : (@pickle p_countType n)=>[|m]; rewrite -?e ?pickleK //;
by move/ltP: (lt_O_nat_of_P n); rewrite -e -[pickle]/nat_of_P ltnn.
Qed.

Lemma z_pick_cancel : pcancel z_pickle z_unpickle.
Proof. by move=> x; rewrite /z_pickle /z_unpickle pickleK z_codeK. Qed.

Definition z_countMixin  := CountMixin z_pick_cancel.
Definition z_choiceMixin := CountChoiceMixin z_countMixin.

Canonical Structure z_choiceType :=
  Eval hnf in ChoiceType Z z_choiceMixin.
Canonical Structure z_countType :=
  Eval hnf in CountType Z z_countMixin.


Lemma ZplusA : associative Zplus.
Proof. by exact Zplus_assoc. Qed.

Lemma ZplusC : commutative Zplus.
Proof. by exact Zplus_comm. Qed.

Lemma Zplus0 : left_id (0%Z) Zplus.
Proof. by exact Zplus_0_l. Qed.

Lemma ZplusNr : left_inverse  0%Z Zopp Zplus.
Proof. exact Zplus_opp_l. Qed. 

Lemma ZplusrN : right_inverse 0%Z Zopp Zplus.
Proof. exact Zplus_opp_r. Qed.

Import ssralg.
Definition Z_zmodMixin :=
  ZmodMixin ZplusA ZplusC Zplus0 ZplusNr.

Canonical Structure Z_zmodType := ZmodType Z Z_zmodMixin.

(* Z Ring *)
Lemma ZmultA : associative Zmult.
Proof. exact: Zmult_assoc. Qed.

Lemma Zmult1q : left_id 1%Z Zmult.
Proof. exact: Zmult_1_l. Qed.

Lemma Zmultq1 : right_id 1%Z Zmult.
Proof. exact: Zmult_1_r. Qed.

Lemma Zmultq0 : forall (q : Z), Zmult q 0%Z = 0%Z.
Proof. exact: Zmult_0_r. Qed.

Lemma Zmult_addl : left_distributive Zmult Zplus.
Proof. exact: Zmult_plus_distr_l. Qed.

Lemma Zmult_addr : right_distributive Zmult Zplus.
Proof. exact: Zmult_plus_distr_r. Qed.

Lemma nonzeroZ1 : 1%Z != 0%Z.
Proof. by []. Qed.

Lemma ZmultC : commutative Zmult.
Proof. exact: Zmult_comm. Qed.

Definition Z_comRingMixin :=
  ComRingMixin ZmultA ZmultC Zmult1q Zmult_addl nonzeroZ1.
(*
Definition Z_ringMixin :=
  RingMixin ZmultA Zmult1q Zmultq1 Zmult_addl Zmult_addr nonzeroZ1.
*)
Canonical Structure Z_Ring := Eval hnf in RingType Z Z_comRingMixin.
Canonical Structure Z_comRing := Eval hnf in ComRingType Z ZmultC.


(*
Canonical Structure Z_ringType :=
  Eval hnf in RingType Z_ringMixin.

Canonical Structure Z_comRingType := ComRingType ZmultC.
*)

(* Warning : an antisymmetric an a transitive predicates are
present in loaded Relations.Relation_Definition *)
Lemma ZleP: forall x y, reflect (x <= y)%Z (Zle_bool x y).
Proof.
move=> x y; apply/(iffP idP).
 by move=> H; apply Zle_bool_imp_le in H.
by move=> H; apply Zle_imp_le_bool.
Qed.

Lemma Zle_bool_antisymb : ssrbool.antisymmetric  Zle_bool.
Proof. by move=> x y; case/andP=> h1 h2; apply: Zle_bool_antisym. Qed.

Lemma Zle_bool_transb : ssrbool.transitive Zle_bool.
Proof. move=> x y z; exact: Zle_bool_trans. Qed.

Lemma Zle_bool_totalb : ssrbool.total Zle_bool.
Proof. by move=> x y; case: (Zle_bool_total x y)=> -> //; rewrite orbT. Qed.

Lemma Zle_bool_addr : forall z x y, Zle_bool x y -> Zle_bool (x + z) (y + z).
Proof. by move=> x y z h; rewrite Zle_bool_plus_mono // Zle_bool_refl. Qed.

Lemma Zle_bool_mulr : forall x y, 
  Zle_bool 0 x -> Zle_bool 0 y -> Zle_bool 0 (x * y).
Proof. 
move=> x y; move/Zle_is_le_bool=> px; move/Zle_is_le_bool=> py.
by apply/Zle_is_le_bool; apply: Zmult_le_0_compat.
Qed.

Lemma ZltP: forall x y, reflect (x < y)%Z (Zlt_bool x y).
Proof. move=> x y; apply/(iffP idP); by apply Zlt_is_lt_bool. Qed.

Lemma ZgeP: forall x y, reflect (x >= y)%Z (Zge_bool x y).
Proof. move=> x y; apply/(iffP idP); rewrite Z.geb_leb.
 by move => /ZleP; auto with zarith.
by move=> H; apply/ZleP; auto with zarith.
Qed.

Lemma ZgtP: forall x y, reflect (x > y)%Z (Zgt_bool x y).
Proof. move=> x y; apply/(iffP idP); by apply Zgt_is_gt_bool. Qed.


Definition Zunit := pred2 1%Z (-1)%Z.

Definition Zinv (z : Z) := z.


Lemma ZmulV : {in Zunit, left_inverse 1%R Zinv *%R}.
Proof. by move=> x; rewrite inE; case/pred2P => ->. Qed.

(* Zmult_1_inversion_r does not exist *)
Lemma unitZPl : forall x y, y * x = 1 -> Zunit x.
Proof.
move=> y x; rewrite GRing.mulrC -[y * x]/(Zmult y x); move/Zmult_1_inversion_l.
by case=> ->.
Qed.

Lemma  Zinv_out : {in predC Zunit, Zinv =1 id}.
Proof. exact. Qed.

Definition Z_comUnitRingMixin :=  ComUnitRingMixin ZmulV unitZPl Zinv_out.

Canonical Structure Z_unitRingType :=
  Eval hnf in UnitRingType Z Z_comUnitRingMixin.


Canonical Structure Z_comUnitRing := Eval hnf in [comUnitRingType of Z].

(*
Canonical Structure Z_comUnitRing := ComUnitRingType Z_comUnitRingMixin. (*Eval hnf in [comUnitRingType of Z].*)
*)
Lemma Z_idomain_axiom : forall x y : Z,
  x * y = 0 -> (x == 0) || (y == 0).
Proof.
move=> x y; rewrite -[x * y]/(Zmult x y); move/Zmult_integral; case=> -> //=.
by rewrite eqxx orbT.
Qed.
Canonical Structure Z_iDomain := Eval hnf in IdomainType Z Z_idomain_axiom.
(*
Canonical Structure Z_iDomain := Eval hnf in IdomainType Z_idomain_axiom.
*)
(*
Definition Z_OrderedRingMixin :=
  OrderedRing.Mixin 
  Zle_bool_antisymb Zle_bool_transb Zle_bool_totalb Zle_bool_addr Zle_bool_mulr.

Canonical Structure Z_oIdomainType := 
  Eval hnf in OIdomainType Z Z_OrderedRingMixin.

*)



