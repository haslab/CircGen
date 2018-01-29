Require Import Utf8.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Require Export zint.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** * ssreflect integration *)


(** Some assorted additional lemmas on lists *)

Lemma map_is_nil A B (f: A->B): forall s,
  map f s = [::] -> s = [::].
Proof. by elim. Qed.

Lemma rev_is_nil {A} (m: list A) :
  rev m = nil → m = nil.
Proof.
move: m => [|x xs] //=; rewrite rev_cons -cats1.
by move: (rev xs) => [|y ys].
Qed.

Lemma rev_is_cons {A} a (m m': list A) :
  rev m = a :: m' →
  m = rev m' ++ a :: nil.
Proof.
move: m => [| x xs] //=; rewrite !rev_cons -cats1 /= .
case E: (rev xs) => [|y ys] /=.
 by move=> [<- <-]; rewrite (rev_is_nil E).
move=> [<- <-]; rewrite rev_cat /= -[[:: y]]/(rev [:: y]) -rev_cat /=; f_equal.
by rewrite -(revK xs) E.
Qed.

Lemma map_nseq {A B} (f:A -> B) (x:A) n:
  [seq f i | i <- nseq n x] = nseq n (f x).
Proof. by elim: n => //= n IH; f_equal. Qed.

Lemma uniq_in_map: forall (A B:eqType) (f:A->B) l x1 x2,
 uniq (map f l) -> x1 \in l -> x2 \in l -> f x1 = f x2 -> x1 = x2.
Proof.
move=> A B f; elim; first by [].
move=> y ys IH x1 x2 /= /andP [Hy Hys].
rewrite ! seq.in_cons => /orP [/eqP ->|H1] /orP [/eqP ->|H2] // H; last by apply IH.
 absurd (f y \in map f ys); first by apply/negP.
 by rewrite H; apply map_f.
absurd (f x1 \in map f ys); first by rewrite H; apply/negP.
by apply map_f.
Qed.

Lemma uniq_cons_None : forall  (A:eqType) (l:list (option A)) x,
 uniq [:: None & l] -> x \in l -> 
 exists y, x = Some y.
Proof.
move=> A l x /= /andP [Hh Ht].
move: x => [y|]; first by move=> Hy; exists y.
move=> Hf; elimtype False.
by move/negP: Hh; apply.
Qed.

Lemma iota_map0 m n:
 iota m n = map (addn m) (iota 0 n).
Proof.
elim: n m => //= n IH m.
rewrite IH addn0; f_equal.
rewrite [iota 1 n]IH -map_comp /=.
apply eq_map => x /=; ring.
Qed.

Lemma take_map_nth {A} d (s: seq A) n:
(n <= size s)%N -> take n s = map (nth d s) (iota 0 n).
Proof.
elim: n s => [| n IH] /= s; first by rewrite take0.
move: s => [|x xs] /= H //=.
rewrite IH; last first.
 move/ltP: H => H; apply/leP; omega.
f_equal.
by rewrite [iota 1 n]iota_map0 -map_comp; apply eq_map => y.
Qed.

Lemma drop_add {A} (s: seq A): forall n n',
  drop (n + n') s = drop n (drop n' s).
Proof.
elim: s => //= x xs IH n [|n'].
 by rewrite addn0.
by rewrite addnS IH.
Qed.

Lemma drop_is_nil {A} (s:seq A) n:
 drop n s = nil -> (size s <= n)%N.
Proof. by elim: s n => //= x xs IH [|n] // /IH H. Qed.

Lemma foldr_cat_spec {A B} (f: A → list B) acc m :
  foldr (λ a, cat (f a)) acc m = flatten (map f m) ++ acc.
Proof.
elim: m acc => //= x xs IH acc.
by rewrite IH catA.
Qed.




(* some more list functions *)

Fixpoint zipWith (f:bool->bool->bool) (s1 s2: seq bool) :=
 match s1, s2 with
 | x::xs, y::ys => f x y :: zipWith f xs ys
 | _, _ => [::]
 end.

Fixpoint insert {A:eqType} (x:A) (l:seq.seq A) : seq.seq A :=
 match l with
 | [::] => [:: x]
 | [:: y & ys] => if x==y then l else [:: y & insert x ys]
 end.

(** Association lists *)
Fixpoint aget {A:eqType} {B} (l: seq (A*B)) (k:A) : option B :=
 if l is x::xs
 then if k==x.1
      then Some x.2
      else aget xs k
 else None.

Lemma aget_cat {A:eqType} B k: forall (l1 l2: seq (A*B)),
 aget (l1++l2) k = if aget l1 k is Some x
                   then Some x
                   else aget l2 k.
Proof. by elim => //= x l IH l2; case: (ifP _). Qed.

Lemma aget_isN (A:eqType) B v: forall (l:seq (A*B)),
 aget l v = None <-> v \notin (map (@fst _ _) l).
Proof.
elim => //= x l IH. case: (ifP _) => E.
 by rewrite in_cons (eqP E) eq_refl.
by rewrite IH in_cons E.
Qed.


Fixpoint take_dflt {A} dflt n (s:seq A) {struct n} :=
  if n is n'.+1
  then if s is x :: xs
       then x :: take_dflt dflt n' xs
       else dflt :: take_dflt dflt n' [::]
  else [::].

Lemma size_take_dflt {A} (dflt:A):
 forall n s, size (take_dflt dflt n s) = n.
Proof. by elim => // n IH [|x xs]; rewrite /= (IH _). Qed.

Lemma take_dflt_nil A (d:A) n:
 take_dflt d n [::] = nseq n d.
Proof. by elim: n => //= n IH; rewrite IH. Qed.

Lemma nth_take_dflt A (d:A) bs n x:
 nth d (take_dflt d n bs) x = if (x < n)%N
                              then nth d bs x
                              else d.
Proof.
elim: x n bs => //=.
 by move=> [|n] [|b bs].
move=> x IH [|n] [|b bs] //=.
 by rewrite take_dflt_nil nth_nseq ltnS; case: (ifP _).
by rewrite IH ltnS.
Qed.

Lemma take_dflt_split {A} (d: A) s n:
  take_dflt d n s = take n s ++ nseq (n-size s) d.
Proof.
elim: n s => /= [|n IH] s; first by rewrite take0.
move: s => [|x xs] /=; rewrite IH {IH}; f_equal.
by move: n => [|n].
Qed.

Lemma take_dflt_catl: forall n (T : Type) (s1 : seq T),
    (n <= size s1)%N -> forall d s2, take_dflt d n (s1 ++ s2) = take_dflt d n s1.
Proof.
move=> n T s1; elim: s1 n => /=.
 by move=> [|n].
by move=> x xs IH [|n] H d s2 //=; rewrite IH.
Qed.

Lemma take_dflt_addl: forall n1 n2 (T : Type) (s : seq T) d,
    (size s <= n1)%N ->
    take_dflt d (n1+n2) s = take_dflt d n1 s ++ take_dflt d n2 [::].
Proof.
move=> n1 n2 T s d; elim: s n1 => /=.
 by elim => //= n IH H; rewrite IH.
by move=> x xs IH; elim => //= n IHn H; rewrite IH.
Qed.

Lemma take_dflt_eqsize: forall T d n (s : seq T),
    (size s = n)%N -> take_dflt d n s = s.
Proof.
move=> T d n s; elim: s n => /=.
 by move=> n <-.
by move=> x xs IH n <- /=; rewrite IH.
Qed.


(** * [eqType] cannonical structures *)

(** [eqType] from a decidable equality *)

Section EqDecEqType.

Variable A: Type.
Variable (eq_dec: forall (x y:A), {x=y}+{x<>y}).

Lemma EqDecEqAxiom:
 Equality.axiom [fun x y:A => if eq_dec x y then true else false].
Proof.
by move=> x y /=; apply (iffP idP); case: (eq_dec x y)=> ? H //=.
Qed.

End EqDecEqType.

(** option monad extensions and notations *)

Definition obind2 aT bT rT (f:aT->bT->option rT) (x:option (aT*bT)) : option rT :=
 obind (fun x=>f x.1 x.2) x.

Definition obind3 aT bT cT rT (f:aT->bT->cT->option rT) (x:option (aT*bT*cT)) : option rT :=
 obind (fun x=> f x.1.1 x.1.2 x.2) x.

Remark obind_isS:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
  obind g f = Some y <->
  exists x, f = Some x /\ g x = Some y.
Proof.
move=> A B [x|] g y /=; split.
  by move => H; exists x; split.
 by move=> [z [[->] H2]].
move=> H; inversion H.
move=> [z [H1 H2]]; inversion H1.
Qed.

Remark obind_isN:
  forall (A B: Type) (f: option A) (g: A -> option B),
  obind g f = None <-> f = None \/ exists x, f = Some x /\ g x = None.
Proof.
move=> A B [x|] g; split => //=.
  by move=> E; right; exists x.
 by move=> [H|[y [[->] Hg]]].
by move=> _; left.
Qed.

(*
Remark obind_NoneP (A B:eqType) (g: A -> option B): forall (f: option A),
  reflect (f = None \/ exists2 x, f == Some x & g x == None) (obind g f == None).
Proof.
move=> [x|]; apply/(iffP idP) => //.
  by move=> /eqP E; right; exists x; apply/eqP.
 by move=> [H|[y [/eqP[->] /eqP Hg]]]; apply/eqP.
by move=> _; left.
Qed.
*)

Remark obind2_isS:
  forall (A B C: Type) (f: option (A*B)) (g: A -> B -> option C) (z: C),
  obind2 g f = Some z <->
  exists x, exists y, f = Some (x, y) /\ g x y = Some z.
Proof.
move=> A B C f g z; split.
 move/obind_isS => [[xA xB] [Hx1 /= Hx2]].
 by exists xA; exists xB; split.
by move=> [xA [xB [-> H2]]].
Qed.

Remark obind3_isS:
  forall (A B C D: Type) (f: option (A*B*C)) (g: A->B->C->option D) (d: D),
  obind3 g f = Some d <->
  exists x, exists y, exists z, f = Some (x, y, z) /\ g x y z = Some d.
Proof.
move=> A B C D f g d; split.
 move/obind_isS => [[[xA xB] xC] [Hx1 /= Hx2]].
 by exists xA; exists xB; exists xC; repeat split.
by move=> [xA [xB [xC [-> H]]]].
Qed.

Lemma omap_isS : forall A B (f:A->B) x y,
 omap f x = Some y <-> exists z, x = Some z /\ y = f z.
Proof.
move=> A B f [x|] y; split => //=.
  by move=> [<-]; exists x.
 by move=> [w [[->] ->]].
by move=> [w //[H _]].
Qed.

Notation "'do' X <- A ; B" := (obind (fun X => B) A)
 (at level 200, X ident, A at level 100, B at level 200)
 : option_monad_scope.

Notation "'do' X , Y <- A ; B" := (obind2 (fun X Y => B) A)
 (at level 200, X ident, Y ident, A at level 100, B at level 200)
 : option_monad_scope.

Notation "'do' X , Y, Z <- A ; B" := (obind3 (fun X Y Z => B) A)
 (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
 : option_monad_scope.

Local Open Scope option_monad_scope.

Fixpoint oseq {aT:Type} (l:list (option aT)) : option (list aT) :=
 match l with
 | nil => Some nil
 | [:: x & xs] => 
   do y <- x; do ys <- oseq xs; Some [:: y & ys]
 end.

Lemma oseq_isS : forall A lo (l:list A),
 oseq lo = Some l <-> lo = map (@Some A) l.
Proof.
move=> A; elim => [l|x xs IH l].
 split => /= [[<-]|] //.
 by move: l => [|x xs].
split.
 move/obind_isS => [y [Hy [/obind_isS [ys /= [Hys [<-]]]]]].
 simpl; f_equal => //.
 by apply -> IH.
move: l => [|y ys] //= [->] H /=.
apply/obind_isS; exists ys; split => //.
by apply <- IH.
Qed.

Lemma oseq_isN (A:eqType) : forall (lo: seq (option A)),
 (oseq lo = None) <-> (None \in lo).
Proof.
elim => //= x xs IH.
split.
 move/obind_isN => [-> //|[y [[->]]]].
 move/obind_isN; rewrite IH{IH}; move => [H|[z [_ Hz]]]; last discriminate Hz.
 by rewrite in_cons.
rewrite in_cons => /orP [/eqP <- //|].
rewrite -IH => -> /=.
by case: x.
Qed.

Lemma oseq_isN_catl {A} (s1 s2: seq (option A)):
  oseq s1 = None -> oseq (s1++s2) = None.
Proof.
elim: s1 => //= x xs IH.
rewrite obind_isN; move => [->|[y [->]]] //=.
by case E: (oseq xs) => [v|] //= _; rewrite IH.
Qed.

Lemma oseq_isN_catr {A} (s1 s2: seq (option A)):
  oseq s2 = None -> oseq (s1++s2) = None.
Proof.
elim: s1 => //= x xs IH H.
move: x => [x|]; rewrite obind_isN; last by left.
right; exists x; split => //.
by rewrite IH.
Qed.

Lemma oseq_isS_cat {A} (s1 s2: seq (option A)) l1 l2:
  oseq s1 = Some l1 -> oseq s2 = Some l2 -> oseq (s1++s2) = Some (l1++l2).
Proof.
elim: s1 l1 => /=.
 by move=> l1 [<-] ->.
move=> x xs IH l1.
rewrite obind_isS => [[y [-> /obind_isS [y' [Hy [<-]]]]] H] /=.
by rewrite (IH y').
Qed.






Fixpoint onth {A} (s: seq A) n :=
  if s is x::xs
  then if n is S n'
       then onth xs n'
       else Some x
  else None.

Lemma onth_isN A: forall (s: seq A) n,
  onth s n = None <-> (size s <= n)%N.
Proof. by elim => //= x xs IH [|n] //=; apply IH. Qed.

Lemma onth_isS A d: forall (s: seq A) n v,
  onth s n = Some v <-> (n < size s)%N /\ nth d s n = v.
Proof. 
elim => [|x xs IH] /=.
 move=> n v; split => //.
 by move=> [HH _].
move=> [|n] v; split => /=.
   by move=> [->].
  by move=> [_ ->]. 
 by rewrite IH.
by move=> H; rewrite IH.
Qed.

Lemma onth_isS_cat {A} (x y: list A) n z :
  onth x n = Some z →
  onth (x ++ y) n = Some z.
Proof.
elim: n x.
 by move=> [|h t] /=.
move=> n IH [|h t] //= H.
by rewrite IH.
Qed.

Lemma eqseq_onth {A} (s1 s2: seq A):
 s1 = s2 <-> forall n, onth s1 n = onth s2 n.
Proof.
elim: s1 s2 => [|x xs IHx]; elim => [|y ys IHy] //; split; try discriminate.
- move => H; move: (H 0); discriminate.
- move => H; move: (H 0); discriminate.
- by move=> [<- <-].  
- move=> H; move: (H 0) => /= [<-]; f_equal.
  by rewrite IHx => n; move: (H n.+1).
Qed.

Lemma map_onth_iota {A} (m: list A) n :
  ∀ x,
    (x + n <= size m)%N →
    map (onth m) (iota x n) = map (@Some _) (take n (drop x m)).
Proof.
elim: n m => /= [|n IH] m v Hv.
 by rewrite take0 /=.
rewrite IH; last first. 
 by move: Hv; rewrite addnS addSn.
move: m Hv => [|x xs] /=.
 by rewrite addnS.
case: v => [|v] //= Hv.
 by rewrite drop0.
move: Hv; rewrite addSn addnS -plusE => /leP Hv.
have: (v < size xs)%coq_nat by omega.
move=> {Hv} /leP Hv.
rewrite [drop v xs](drop_nth x) //=.
by f_equal; rewrite onth_isS; split; last by reflexivity.
Qed.



(*
Definition oguard aT (p:aT-> bool) x := if p x then Some x else None.

Lemma oguardP : forall aT p (x y:aT),
 oguard p x = Some y <-> p x /\ y = x.
Proof.
rewrite /oguard => aT p x y; split.
 case: (p x) => //.
 by move=> [->]; split.
by move=> [Hx ->]; rewrite Hx.
Qed.
*)


Fixpoint omap_all {A B} (f: A -> option B) (s: seq A) : option (seq B) :=
 if s is x::xs
 then obind (fun x => obind (fun r => Some (x::r)) (omap_all f xs)) (f x)
 else Some [::].

Lemma omap_all_oseq {A B} (f: A -> option B): forall ma,
 omap_all f ma = oseq (map f ma).
Proof. by elim => //= x xs ->. Qed.

Lemma omap_all_isS {A B} (f: A -> option B) ma mb :
  omap_all f ma = Some mb <->
  map f ma = map (@Some B) mb.
Proof. by rewrite omap_all_oseq; apply oseq_isS. Qed.

Corollary omap_all_size {A B} (f: A -> option B) ma mb :
  omap_all f ma = Some mb ->
  size ma = size mb.
Proof. by rewrite -(size_map f _) => /omap_all_isS ->; rewrite size_map. Qed.

Lemma omap_all_map {A B C} (f: A -> B) (g: B -> option C) ma :
  omap_all g (map f ma) = omap_all (fun x=> g (f x)) ma.
Proof. by rewrite !omap_all_oseq -map_comp. Qed.




(** [updpref] updates a prefix of a sequence *)
Fixpoint updpref {A} (orig new: seq A) : seq A :=
 match new, orig with
 | x::xs, y::ys => x::updpref ys xs
 | _, ys => ys
 end.

Lemma updpref_nil: forall A (new: seq A),
 updpref [::] new = [::].
Proof. by move=> A; elim. Qed.

Lemma updpref_cons_nil: forall A x (xs: seq A),
 updpref (x::xs) [::] = x::xs.
Proof. by move=> A. Qed.

Lemma updpref_cons_cons: forall A x y(xs ys: seq A),
 updpref (x::xs) (y::ys) = y::updpref xs ys.
Proof. by move=> A. Qed.

Lemma size_updpref A: forall (xs ys: seq A),
 size (updpref xs ys) = size xs.
Proof.
elim => [[|y ys] | x xs IH [|y ys]] //.
by rewrite updpref_cons_cons /= IH.
Qed.

Lemma onth_updpref A (orig new: seq A) n:
 size new <= size orig ->
 onth (updpref orig new) n = if n < min (size orig) (size new)
                             then onth new n
                             else onth orig n.
Proof.
elim: n orig new => /=.
 by move=>[|x xs] [|y ys].
move=> n IH [|x xs] [|y ys] //=.
by move=> H; rewrite IH.
Qed.

Lemma updprefE A (orig new: seq A):
  updpref orig new = take (size orig) new ++ drop (size new) orig.
Proof.
elim: orig new.
 by move=> [| y ys].
move=> x xs IH1; elim => //=.
move=> y ys IH2; f_equal.
by rewrite IH1.
Qed.

(*
Lemma updpref_drop A (orig new: seq A):
  size new <= size orig ->
  updpref orig new = new ++ drop (size new) orig.
Proof. by move=> H; rewrite updprefE take_oversize. Qed.
*)


Fixpoint updprefAt {A} n (orig new: seq A) : seq A :=
 if n is n'.+1
 then if orig is x::xs
      then x::updprefAt n' xs new
      else [::]
 else updpref orig new.

Lemma updprefAtE A (orig: seq A) n new:
  updprefAt n orig new = take n orig ++ updpref (drop n orig) new.
Proof.
elim: n orig new.
 by move=> [|x xs] [|y ys].
by move=> n IH [|x xs] [|y ys] //=; f_equal.
Qed.

Lemma size_updprefAt A (orig: seq A) n new:
  size (updprefAt n orig new) = size orig.
Proof.
rewrite updprefAtE size_cat size_take size_updpref size_drop.
case: (ifP _) => //= H.
 by rewrite subnKC //; apply ltnW.
have: leq (size orig) n.
 by move/negP/negP: H; rewrite -leqNgt.
by rewrite /leq => /eqP ->; rewrite addn0.
 Qed.



(** ssreflect integration of some StdLib defs. *)

Lemma InE: forall (A:eqType) a (l:list A),
  a \in l <-> List.In a l.
Proof.
move=> A a; elim; first by [].
move=> x xs IH; split.
 rewrite seq.in_cons => /orP [H|H].
  rewrite (eqP H) /=; left; reflexivity.  
 by right; apply -> IH.
move=> /= [H|H].
 by rewrite inE H eq_refl.
rewrite inE; apply/orP; right.
by apply <- IH.
Qed.

Lemma lengthE : forall A, @length A = @size A.
Proof. by []. Qed.

Lemma appE: forall A (xs ys: seq A),
 cat xs ys = app xs ys.
Proof. by move=> A; elim. Qed.

Lemma revE A: forall (xs: seq A),
 rev xs = List.rev xs.
Proof. by elim => //= x xs IH; rewrite rev_cons -cats1 IH appE. Qed.

Lemma mapE A B (f:A -> B): forall (xs: seq A),
 map f xs = List.map f xs.
Proof. by elim => //= x xs IH; rewrite rev_cons -cats1 IH. Qed.


(*
Lemma map_eq_forall2 {A B C} (f: A → C) (g: B → C) ma mb :
  map f ma = map g mb ↔ List.Forall2 (λ a b, f a = g b) ma mb.
Proof.
elim: ma mb => [|a ma IH] mb; split => /= H.
- by symmetry in H; apply map_is_nil in H; rewrite H; left.
- inversion_clear H; reflexivity.
- move: mb H => [|b mb] /=; first by discriminate.
  by move => [E1 E2]; right => //; apply IH.
- by inversion H; simpl; f_equal => //; apply IH.
Qed.
*)