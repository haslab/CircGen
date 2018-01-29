Require Import Utf8.
Require AST.
Import Coqlib.
Import AST.

Section MIN_LIST.

Definition min_name_below (n: ident) (ns: list ident) : ident :=
  fold_left Pos.min ns n.

Definition min_name (ns: list ident) : option ident :=
  match ns with
  | nil => None
  | n :: ns => Some (min_name_below n ns)
  end.

Lemma min_name_below_iff n ns :
  (n = min_name_below n ns ∨ In (min_name_below n ns) ns) ∧
  (min_name_below n ns <= n)%positive ∧
  (∀ x, In x ns → min_name_below n ns <= x)%positive.
Proof.
  revert n. elim ns; clear.
  simpl. intuition.
  intros n' ns IH n.
  specialize (IH (Pos.min n n')).
  destruct IH as (IH & IH' & IH'').
  split. clear -IH. simpl.
  destruct IH as [ IH | IH ]. 2: intuition.
  generalize (Pos.min_spec n n'). intros [(_ & H) | (_ & H)].
  left. congruence. right; left. simpl. congruence.
  clear IH. split.
  simpl. etransitivity. apply IH'. Psatz.lia.
  intros x [ -> | IN ].
  simpl. etransitivity. apply IH'. Psatz.lia.
  exact (IH'' _ IN).
Qed.

Lemma min_name_iff ns :
  match min_name ns with
  | None => ns = nil
  | Some n => In n ns ∧ ∀ x, In x ns → n <= x
  end%positive.
Proof.
  destruct ns as [ | n ns ]. reflexivity.
  generalize (min_name_below_iff n ns). simpl.
  intuition; subst; Psatz.lia.
Qed.

End MIN_LIST.

Section MAP.

  Context {A B: Type} (f: A → B).

  Lemma map_eq_cons b bs m :
    b :: bs = map f m →
    ∃ a m', m = a :: m' ∧ b = f a ∧ bs = map f m'.
  Proof.
    destruct m as [ | a m ]; intros H; inversion H; clear H. subst. eauto.
  Qed.

  Lemma map_eq_app ma mbL mbR :
    map f ma = mbL ++ mbR →
    ∃ maL maR,
      ma = maL ++ maR ∧
      map f maL = mbL ∧
      map f maR = mbR.
  Proof.
    revert mbL mbR. elim ma; clear.
    intros [ | ? ? ]. 2: discriminate.
    intros [ | ? ? ]. 2: discriminate.
    intros _. exists nil, nil. simpl. eauto.
    intros a ma IH [ | b mbL].
    intros [ | b mbR ]. discriminate. simpl.
    intros H. inv H. specialize (IH nil _ eq_refl). destruct IH as (maL & maR & -> & N & IH).
    apply map_eq_nil in N. subst maL.
    exists nil, (a :: maR). simpl in *. eauto.
    intros mbR H; inv H. edestruct IH as (maL & maR & -> & IHL & IHR). eassumption.
    clear IH.
    exists (a :: maL), maR. apply (conj eq_refl). simpl. intuition congruence.
  Qed.


  Lemma map_eq_forall2 {C} (g: C → B) ma mb :
    map f ma = map g mb ↔ Forall2 (λ a b, f a = g b) ma mb.
  Proof.
    revert mb; elim ma; clear.
    - intros mb; split; intros H.
      + symmetry in H. apply map_eq_nil in H. rewrite H. left.
      + inv H. reflexivity.
    - intros a ma IH mb; split; intros H.
      + destruct mb. discriminate. inv H. right. assumption. apply IH. assumption.
      + inv H. simpl. f_equal. assumption. apply IH. assumption.
  Qed.


End MAP.


Module FOR_ALL_BYTE.
Section FOR_ALL_BYTE.

Coercion is_true : bool >-> Sortclass.

Fixpoint forallb {A} (f: A → bool) (m: list A) : bool :=
  match m with
  | nil => true
  | a :: m' => if f a then forallb f m' else false
  end.

Fixpoint forallb_forall {A} (f: A → bool) (m: list A) :
  forallb f m → ∀ a, In a m → f a = true.
Proof.
  destruct m as [ | a m ]. intros _ a ().
  simpl.
  intros H a' [ -> | IN ].
  destruct (f a'); auto.
  destruct (f a); auto.
  apply (forallb_forall A f m H a' IN).
  congruence.
Qed.

Lemma In_seq x y z :
  (x ≤ y → y < x + z → In y (seq x z))%nat.
Proof.
  revert x y. induction z as [ | z IH ].
  intros. zify. Psatz.lia.
  intros x y H H0. simpl.
  assert (x = y ∨ S x ≤ y)%nat as K by (Psatz.lia).
  destruct K; auto.
  right. apply IH; auto. Psatz.lia.
Qed.

Import Integers.
Definition all_the_bytes_def : list byte := 
  List.map (λ n, Byte.repr (Z.of_nat n)) (seq 0 256)%nat.

Definition all_the_bytes : list byte := 
  Eval vm_compute in all_the_bytes_def.

Definition for_all_byte (f: byte → bool) : bool :=
  forallb f all_the_bytes.

Lemma for_all_byte_correct f :
  for_all_byte f → ∀ b : byte, f b.
Proof.
  unfold for_all_byte.
  intros H b.
  apply (forallb_forall _ _ H).
  change (In b all_the_bytes_def).
  apply in_map_iff.
  exists (Z.to_nat (Byte.unsigned b)).
  pose proof (Byte.unsigned_range b) as R.
  change Byte.modulus with 256%Z in R.
  rewrite Z2Nat.id, Byte.repr_unsigned.
  split. easy.
  apply In_seq; zify; try Psatz.lia.
  rewrite Z2Nat.id; Psatz.lia.
  Psatz.lia.
Qed.

End FOR_ALL_BYTE.
End FOR_ALL_BYTE.

