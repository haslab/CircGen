Require Import ORbdt.
Require Import ExtraLib.
Import Utf8.
Import Coqlib.

Import eqtype.
Import zint.

Section BOUNDED_BDD.

Context {A: eqType}.

(* A BDD is bounded by n when all variables that appear in the formula are larger than n *)
Definition bounded_bdd (bdd: bdd A) (pc: positive) : Prop :=
  ∀ p, In p (literal_of_bdd bdd) → (pc < p)%positive.

Lemma bounded_lt pc' bdd pc :
  (pc < pc')%positive →
  bounded_bdd bdd pc' →
  bounded_bdd bdd pc.
Proof.
  intros LT H p IN. specialize (H p IN). Psatz.lia.
Qed.

Lemma bounded_bdd_Node_inv p ℓ r pc :
  bounded_bdd (Node p ℓ r) pc →
  (pc < p)%positive ∧ bounded_bdd ℓ pc ∧ bounded_bdd r pc.
Proof.
  intros H.
  split. generalize (H p). simpl. auto.
  split; intros q; generalize (H q); simpl; rewrite in_app; auto.
Qed.

(* When evaluating a BDD that is bounded by n,
   the model can be extended with a smaller variable. *)
Lemma eval_bounded {pc pcm bdd} :
  bounded_bdd bdd pc →
  eval_bdd pcm bdd = eval_bdd (pc :: pcm) bdd.
Proof.
  elim bdd; clear.
  reflexivity.
  intros p ℓ IHℓ r IHr.
  intros BND; apply bounded_bdd_Node_inv in BND.
  destruct BND as (LT & Hℓ & Hr).
  simpl.
  rewrite seq.in_cons.
  destruct (ssrbool.in_mem _ _).
  rewrite orb_true_r; auto.
  case eqP. intros ->. Psatz.lia. auto.
Qed.

Definition check_bounded_bdd (g: bdd A) (n: positive) : bool :=
  List.forallb (Pos.ltb n) (literal_of_bdd g).

Lemma check_bounded_bdd_iff g n :
  reflect (bounded_bdd g n) (check_bounded_bdd g n).
Proof.
  unfold check_bounded_bdd, bounded_bdd.
  match goal with
  | |- context[ forallb ?x ?y ] => set (f := x); set (m := y)
  end.
  generalize (forallb_forall f m).
  destruct (forallb _ _).
  - intros [H _]; specialize (H Logic.eq_refl).
    constructor. intros p IN; generalize (H p IN).
    apply Pos.ltb_lt.
  - intros [_ H]. constructor.
    intros K. apply diff_false_true, H.
    intros p IN; generalize (K p IN).
    apply Pos.ltb_lt.
Qed.

End BOUNDED_BDD.

Lemma literal_of_pcond_lit p :
  literal_of_bdd (pcond_lit p) = p :: nil.
Proof. reflexivity. Qed.

Lemma literal_of_pcond_litN p :
  literal_of_bdd (pcond_litN p) = p :: nil.
Proof. reflexivity. Qed.

Lemma literal_of_pcond_or b1 b2 :
  incl (literal_of_bdd (pcond_or b1 b2)) (literal_of_bdd b1 ++ literal_of_bdd b2).
Proof.
  revert b2. elim b1; clear.
  intros (). intros ? ? (). intros ?; apply incl_refl.
  intros p ℓ IHℓ r IHr b2.
  elim b2; clear b2.
  intros (). intros ? (). simpl. rewrite app_nil_r. apply incl_refl.
  intros p' ℓ' IHℓ' r' IHr'.
  simpl.
  case eqP.
  - intros ->. unfold chkN.
    case bdd_eqP.
    intros EQ. eapply incl_tran. apply IHℓ. clear. intros q. repeat (simpl; rewrite in_app). intuition.
    intros NE. intros q. repeat (simpl; rewrite in_app). clear -IHℓ IHr.
    intros [ H | [ H | H ] ]. auto. right. specialize (IHℓ _ _ H). rewrite in_app in IHℓ. clear -IHℓ. intuition.
    right. specialize (IHr _ _ H). rewrite in_app in IHr. clear -IHr; intuition.
  - intros NE.
    case Pos.ltb_spec.
    + intros LT. unfold chkN.
    case bdd_eqP.
    intros EQ. eapply incl_tran. apply IHℓ. clear. intros q. repeat (simpl; rewrite in_app). intuition.
    intros NE'. intros q. repeat (simpl; rewrite in_app).
    intros [ H | [ H | H ] ]. auto. right. specialize (IHℓ _ _ H). repeat (simpl in IHℓ; rewrite in_app in IHℓ). clear -IHℓ. intuition.
    right. specialize (IHr _ _ H). repeat (simpl in IHr; rewrite in_app in IHr). clear -IHr; intuition.
    + intros LE. unfold chkN.
    case bdd_eqP.
    intros EQ. eapply incl_tran. apply IHℓ'. clear. intros q. repeat (simpl; rewrite in_app). intuition.
    intros NE'. intros q. repeat (simpl; rewrite in_app).
    intros [ H | [ H | H ] ]. auto. specialize (IHℓ' _ H). repeat (simpl in IHℓ'; rewrite in_app in IHℓ'). clear -IHℓ'. intuition.
    specialize (IHr' _ H). repeat (simpl in IHr'; rewrite in_app in IHr'). clear -IHr'; intuition.
Qed.

Lemma literal_of_pcond_and b1 b2 :
  incl (literal_of_bdd (pcond_and b1 b2)) (literal_of_bdd b1 ++ literal_of_bdd b2).
Proof.
  revert b2. elim b1; clear.
  intros (). intros ?; apply incl_refl. intros ? ? ().
  intros p ℓ IHℓ r IHr b2.
  elim b2; clear b2.
  intros (). simpl. rewrite app_nil_r. apply incl_refl. intros ? ().
  intros p' ℓ' IHℓ' r' IHr'.
  simpl.
  case eqP.
  - intros ->. unfold chkN.
    case bdd_eqP.
    intros EQ. eapply incl_tran. apply IHℓ. clear. intros q. repeat (simpl; rewrite in_app). intuition.
    intros NE. intros q. repeat (simpl; rewrite in_app). clear -IHℓ IHr.
    intros [ H | [ H | H ] ]. auto. right. specialize (IHℓ _ _ H). rewrite in_app in IHℓ. clear -IHℓ. intuition.
    right. specialize (IHr _ _ H). rewrite in_app in IHr. clear -IHr; intuition.
  - intros NE.
    case Pos.ltb_spec.
    + intros LT. unfold chkN.
    case bdd_eqP.
    intros EQ. eapply incl_tran. apply IHℓ. clear. intros q. repeat (simpl; rewrite in_app). intuition.
    intros NE'. intros q. repeat (simpl; rewrite in_app).
    intros [ H | [ H | H ] ]. auto. right. specialize (IHℓ _ _ H). repeat (simpl in IHℓ; rewrite in_app in IHℓ). clear -IHℓ. intuition.
    right. specialize (IHr _ _ H). repeat (simpl in IHr; rewrite in_app in IHr). clear -IHr; intuition.
    + intros LE. unfold chkN.
    case bdd_eqP.
    intros EQ. eapply incl_tran. apply IHℓ'. clear. intros q. repeat (simpl; rewrite in_app). intuition.
    intros NE'. intros q. repeat (simpl; rewrite in_app).
    intros [ H | [ H | H ] ]. auto. specialize (IHℓ' _ H). repeat (simpl in IHℓ'; rewrite in_app in IHℓ'). clear -IHℓ'. intuition.
    specialize (IHr' _ H). repeat (simpl in IHr'; rewrite in_app in IHr'). clear -IHr'; intuition.
Qed.

Lemma bounded_pcond_or ℓ r pc :
  bounded_bdd ℓ pc →
  bounded_bdd r pc →
  bounded_bdd (pcond_or ℓ r) pc.
Proof.
  intros Hℓ Hr p IN.
  generalize (literal_of_pcond_or _ _ _ IN). rewrite in_app.
  intros [ L | R ]; auto.
Qed.

Lemma bounded_pcond_and ℓ r pc :
  bounded_bdd ℓ pc →
  bounded_bdd r pc →
  bounded_bdd (pcond_and ℓ r) pc.
Proof.
  intros Hℓ Hr p IN.
  generalize (literal_of_pcond_and _ _ _ IN). rewrite in_app.
  intros [ L | R ]; auto.
Qed.

Lemma bounded_pcond_lit x y :
  (y < x)%positive →
  bounded_bdd (pcond_lit x) y.
Proof.
  unfold bounded_bdd.
  rewrite literal_of_pcond_lit. simpl. intuition Psatz.lia.
Qed.

Lemma bounded_pcond_litN x y :
  (y < x)%positive →
  bounded_bdd (pcond_litN x) y.
Proof.
  unfold bounded_bdd.
  rewrite literal_of_pcond_litN. simpl. intuition Psatz.lia.
Qed.

Section ON_BDD.
  Import ssrbool seq.

  Context {A: eqType}.

  Lemma eval_bdd_m (x y: pEnv) :
    (∀ n, In n x ↔ In n y) →
    ∀ bdd : bdd A, eval_bdd x bdd = eval_bdd y bdd.
  Proof.
    intros EXT.
    intros bdd; elim bdd; clear bdd. reflexivity.
    intros n ℓ IHℓ r IHr.
    generalize (EXT n). rewrite <- (ssrlib.InE n x), <- (ssrlib.InE n y).
    simpl. case (n \in _). intros H.
    rewrite (proj1 H Logic.eq_refl). exact IHℓ.
    case (n \in _); auto.
    intros H. generalize (proj2 H Logic.eq_refl). discriminate.
  Qed.

  Lemma not_bounded_bdd_ex (bdd: bdd A) n :
    ¬ bounded_bdd bdd n →
    ∃ m,
    In m (literal_of_bdd bdd) ∧ (m <= n)%positive.
  Proof.
    intros K.
    set (q := literal_of_bdd bdd).
    generalize (min_name_iff q). destruct (min_name _) as [ m | ].
    intros [Hm LE]. exists m. apply (conj Hm).
    case (Pos.leb_spec m n). exact id.
    intros LT. elim K. intros p Hp. specialize (LE _ Hp). Psatz.lia.
    intros Q. elim K. intros p Hp. fold q in Hp. rewrite Q in Hp. destruct Hp.
  Qed.

  Definition bounded_bdd' (bdd: bdd A) n :=
    match n with
    | None => True
    | Some n => bounded_bdd bdd n
    end.

End ON_BDD.
