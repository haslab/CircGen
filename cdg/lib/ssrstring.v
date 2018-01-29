Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Require Export String.
Import Ascii.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** * [ascii] ssreflect instances *)

Definition ascii_eq (x y:ascii) : bool :=
 if ascii_dec x y then true else false.

Lemma ascii_eqP : Equality.axiom ascii_eq.
Proof.
move=> p q; apply: (iffP  idP)=>[|<-]; rewrite /ascii_eq.
 case: (ascii_dec p q) => //=.
case: (ascii_dec p p) => //=.
Qed.

Canonical Structure ascii_eqMixin := EqMixin ascii_eqP.
Canonical Structure ascii_eqType := Eval hnf in @EqType ascii ascii_eqMixin.

Definition ascii_unpickle n := Some (ascii_of_nat n).

Lemma ascii_pick_cancel : pcancel nat_of_ascii ascii_unpickle.
Proof.
move=> x; rewrite /ascii_unpickle; congr Some.
by apply ascii_nat_embedding.
Qed.

Definition ascii_countMixin  := CountMixin ascii_pick_cancel.
Definition ascii_choiceMixin := CountChoiceMixin ascii_countMixin.

Canonical Structure ascii_choiceType :=
 Eval hnf in ChoiceType ascii ascii_choiceMixin.
Canonical Structure ascii_countType :=
 Eval hnf in CountType ascii ascii_countMixin.

Definition ascii_enum := (map ascii_of_nat (iota O 256)).

Lemma ascii_enum_uniq : uniq ascii_enum.
Proof. by vm_compute. Qed.

Lemma mem_ascii_enum a : a \in ascii_enum.
Proof.
unfold ascii_enum.
apply/mapP.
exists (nat_of_ascii a); last first.
 by rewrite ascii_nat_embedding.
by case: a => [[|] [|] [|] [|] [|] [|] [|] [|]]; vm_compute.
Qed.

Definition ascii_finMixin :=
 Eval hnf in UniqFinMixin ascii_enum_uniq mem_ascii_enum.
Canonical ascii_finType := Eval hnf in FinType ascii ascii_finMixin.

(** Some predicates on [ascii] *)
Definition is_upper (c:ascii) : bool :=
  (BinNat.N.leb 65 (N_of_ascii c))%N && (BinNat.N.leb (N_of_ascii c) 90)%N.

Definition is_lower (c:ascii) : bool :=
  (BinNat.N.leb 97 (N_of_ascii c))%N && (BinNat.N.leb (N_of_ascii c) 122)%N.

Definition is_digit (c:ascii) : bool :=
  (BinNat.N.leb 48 (N_of_ascii c))%N && (BinNat.N.leb (N_of_ascii c) 57)%N.

Definition is_space (c:ascii) : bool := BinNat.N.eqb (N_of_ascii c) 32.

Definition is_tab (c:ascii) : bool := BinNat.N.eqb (N_of_ascii c) 9.

Definition is_newline (c:ascii) : bool := BinNat.N.eqb (N_of_ascii c) 13.

(** * [string] ssreflect instances *)

Definition string_eq (x y:string) : bool :=
  if string_dec x y then true else false.

Lemma string_eqP : Equality.axiom string_eq.
Proof.
move=> p q; apply: (iffP  idP)=>[|<-]; rewrite /string_eq.
 case: (string_dec p q) => //=.
case: (string_dec p p) => //=.
Qed.

Canonical Structure string_eqMixin := EqMixin string_eqP.
Canonical Structure string_eqType := Eval hnf in @EqType string string_eqMixin.

Fixpoint str2seq (s:string) : seq ascii :=
  match s with
    | EmptyString => [::]
    | String c s' => [:: c & str2seq s']
  end.

Fixpoint seq2str (l:seq ascii) : string :=
  match l with
    | [::] => EmptyString
    | (c::l') => String c (seq2str l')
  end.

Lemma str2seqK : cancel str2seq seq2str.
Proof. by elim => //= a s ->. Qed.

Lemma seq2strK : cancel seq2str str2seq.
Proof. by elim => //= a s ->. Qed.

Definition string_pickle s := pickle_seq (str2seq s).

Definition string_unpickle n :=
  omap seq2str (unpickle_seq ascii_countType n).

Lemma string_pick_cancel : pcancel string_pickle string_unpickle.
Proof.
move=> x; rewrite /string_unpickle /string_pickle.
rewrite pickle_seqK; congr Some.
by rewrite str2seqK.
Qed.

Definition string_countMixin  := CountMixin string_pick_cancel.
Definition string_choiceMixin := CountChoiceMixin string_countMixin.

Canonical Structure string_choiceType :=
  Eval hnf in ChoiceType string string_choiceMixin.
Canonical Structure string_countType :=
  Eval hnf in CountType string string_countMixin.
