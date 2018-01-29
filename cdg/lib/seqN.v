Require Import NArith.
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrlib.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Open Scope N_scope.

(** Some [N]versions of standard ssreflect operations. *)
Definition iotaN (m n:N) : seq N :=
 N.peano_rect _ (fun _=>[::]) (fun n r m=> [:: m & r (N.succ m)]) n m.

Lemma iotaN_succ x n:
 iotaN x (N.succ n) = x :: iotaN (N.succ x) n.
Proof. by rewrite /iotaN N.peano_rect_succ. Qed.

Lemma iotaN_iota x n:
 iotaN x n = map n2N (iota (N2n x) (N2n n)).
Proof.
elim/N.peano_ind: n x => //= n IH x.
rewrite N2Nat.inj_succ /= iotaN_succ N2n2N; f_equal.
by rewrite (IH (N.succ x)) N2Nat.inj_succ.
Qed.

Lemma mem_iotaN m n x:
  (x \in iotaN m n) <-> (m <= x < m+n).
Proof.
rewrite iotaN_iota; split.
 move/mapP => [y []]; rewrite mem_iota; move => [/andP[]].
 rewrite -{1 2}[y]n2N2n N2n_le -plusE -N2Nat.inj_add N2n_lt.
 by move=> H1 H2 ->; split.
move=> [H1 H2]. apply/mapP.
exists (N2n x); last by rewrite N2n2N.
rewrite mem_iota; apply/andP; split.
 by rewrite -N2n_le.
by rewrite -plusE -N2Nat.inj_add -N2n_lt.
Qed.



Definition nseqN {A} : N -> A -> seq A :=
 N.peano_rect _ (fun _=>[::]) (fun n r x=> x::r x).

Lemma nseqN_nseq {A} n (x:A) : nseqN n x = nseq (N2n n) x.
Proof.
elim/N.peano_ind: n => //= n.
by rewrite /nseqN /= N.peano_rect_succ N2Nat.inj_succ /= => ->. 
Qed.

Lemma map_nseqN {A B} (f:A -> B) (x:A) n:
  [seq f i | i <- nseqN n x] = nseqN n (f x).
Proof. by rewrite nseqN_nseq map_nseq nseqN_nseq. Qed.




Fixpoint sizeN {A} (s: seq A) : N :=
 if s is x::xs then N.succ (sizeN xs) else 0.

Lemma size_sizeN {A}: forall (s: seq A),
 size s = N.to_nat (sizeN s).
Proof.
elim => //= x xs IH.
by rewrite N2Nat.inj_succ; f_equal.
Qed.

Lemma sizeN_size {A}: forall (s: seq A),
 sizeN s = N.of_nat (size s).
Proof. by move=> s; rewrite size_sizeN N2Nat.id. Qed.

Corollary sizeN_map {A B} (f: A -> B) (m: list A) :
  sizeN (map f m) = sizeN m.
Proof. by rewrite !sizeN_size size_map. Qed.

Corollary sizeN_rev {A} (m: list A) :
  sizeN (rev m) = sizeN m.
Proof. by rewrite !sizeN_size size_rev. Qed.

Corollary sizeN_app {A} (m m': list A) :
  sizeN (m ++ m') = sizeN m + sizeN m'.
Proof. by rewrite !sizeN_size size_cat Nat2N.inj_add. Qed.

Corollary sizeN_rcons {A} (m: list A) a :
  sizeN (rcons m a) = sizeN m + 1.
Proof.
rewrite !sizeN_size size_rcons -[1]/(n2N 1) -Nat2N.inj_add.
by rewrite plusE addn1.
Qed.

Lemma sizeN_iotaN m n :
  sizeN (iotaN m n) = n.
Proof. by rewrite sizeN_size iotaN_iota size_map size_iota N2n2N. Qed.



Fixpoint nthN {A} (dfl: A) (s: seq A) (n: N) : A :=
 if s is x::xs
 then if n is N0 then x else nthN dfl xs (N.pred n)
 else dfl.

Lemma nth_nthN: forall A (dfl:A) n xs,
 nth dfl xs n = nthN dfl xs (N.of_nat n).
Proof.
move=> A d; elim => [|n IH] [|x xs] //=.
by rewrite IH pospred_ofsuccnat; f_equal.
Qed.

Lemma nthN_nth: forall A (dfl:A) xs n,
 nthN dfl xs n = nth dfl xs (N.to_nat n).
Proof. by move=> A d xs n; rewrite nth_nthN N2Nat.id. Qed.

Corollary nth_rcons_last {A} (d: A) m a :
  nthN d (rcons m a) (sizeN m) = a.
Proof.
rewrite nthN_nth -size_sizeN nth_rcons.
case: (ifP _). 
 move=> /ltP H; omega.
by rewrite eq_refl.
Qed.

Lemma nthN_cat {A} (d: A) m m' n :
  nthN d (m ++ m') n
  = (if n <? sizeN m then nthN d m n else nthN d m' (n - sizeN m)).
Proof.
rewrite !nthN_nth nth_cat !sizeN_size N2Nat.inj_sub /= n2N2n.
have ->: (N2n n < size m)%N = (n <? n2N (size m)).
 rewrite -{1}[size m]n2N2n.
 by apply/idP/idP; rewrite -N2n_lt -N.ltb_lt.
by rewrite minusE.
Qed.







Definition takeN {A} (n:N) : seq A -> seq A :=
 N.peano_rect _ (fun _=>[::]) (fun n r s=> if s is x::xs
                                           then x::r xs
                                           else [::]) n.

Lemma takeN_nil A: forall pos,
 takeN pos [::] = @nil A.
Proof.
elim/N.peano_ind => //=.
by move=> n IH; rewrite /takeN N.peano_rect_succ.
Qed.

Lemma takeN_0 A: forall (s: seq A),
 takeN 0 s = [::].
Proof. by move=> s; rewrite /takeN. Qed.

Lemma takeN_cons A: forall p x (xs: seq A),
 takeN (Npos p) (x::xs) = x::takeN (Npred (Npos p)) xs.
Proof.
move => p x xs.
by rewrite /takeN -N.succ_pos_pred N.peano_rect_succ N.pred_succ.
Qed.

Lemma take_takeN: forall {A} (xs: seq A) n,
 take n xs = takeN (N.of_nat n) xs.
Proof.
move=> A; elim => //.
 by move=> n; rewrite /= takeN_nil.
move=> x xs IH [|n] //.
rewrite takeN_cons /= IH; f_equal; f_equal.
by rewrite pospred_ofsuccnat.
Qed.

Lemma takeN_take: forall {A} n (xs: seq A),
 takeN n xs = take (N.to_nat n) xs.
Proof. by move=> A n xs; rewrite take_takeN N2Nat.id. Qed.

Lemma takeN_all {A} (m: list A) n :
  sizeN m <= n -> takeN n m = m.
Proof.
  revert m; elim n using N.peano_ind; clear.
  intros [ | a m ]. reflexivity. simpl. Psatz.lia.
  intros n IH m LE.
  unfold takeN. rewrite N.peano_rect_succ. fold (@takeN A n).
  destruct m as [ | a m ]. reflexivity.
  f_equal. apply IH. simpl in LE. Psatz.lia.
Qed.

Lemma takeN_map_nthN {A} x (s: seq A) n:
(n <= sizeN s) -> takeN n s = map (nthN x s) (iotaN 0 n).
Proof.
rewrite sizeN_size takeN_take iotaN_iota -map_comp.
have E: nthN x s \o n2N =1 nth x s by move=> y /=; rewrite nth_nthN.
move=> H; rewrite (eq_map E) (take_map_nth x) //=.
by rewrite size_sizeN -N2n_le sizeN_size.
Qed.





Definition dropN {A} (n:N) : seq A -> seq A :=
 N.peano_rect _ id (fun n r s=> if s is x::xs
                                then r xs
                                else [::]) n.

Lemma dropN_nil A: forall pos,
 dropN pos [::] = @nil A.
Proof.
elim/N.peano_ind => //=.
by move=> n IH; rewrite /dropN N.peano_rect_succ.
Qed.

Lemma dropN_0 A: forall (s: seq A),
 dropN 0 s = s.
Proof. by move=> s; rewrite /dropN. Qed.

Lemma dropN_succ_cons A: forall n x (xs: seq A),
 dropN (N.succ n) (x::xs) = dropN n xs.
Proof. by move=> n x xs; rewrite /dropN N.peano_rect_succ. Qed.

Lemma dropN_pos_cons A: forall p x (xs: seq A),
 dropN (Npos p) (x::xs) = dropN (Npred (Npos p)) xs.
Proof.
move=> p x xs.
by rewrite /dropN -N.succ_pos_pred N.peano_rect_succ N.pred_succ.
Qed.

Lemma drop_dropN: forall A (xs: seq A) n,
 drop n xs = dropN (N.of_nat n) xs.
Proof.
move=> A; elim => //.
 by move=> n; rewrite dropN_nil.
move=> x xs IH [|n] //. 
by rewrite [drop _ _]/= IH Nat2N.inj_succ dropN_succ_cons.
Qed.

Lemma dropN_drop: forall A (xs: seq A) n,
 dropN n xs = drop (N.to_nat n) xs.
Proof. by move=> A n xs; rewrite drop_dropN N2Nat.id. Qed.

Lemma dropN_sizeN_cat: forall T n (s1 s2: seq T),
    sizeN s1 = n -> dropN n (s1++s2) = s2.
Proof.
move=> T n s1 s2.
rewrite sizeN_size => H.
move/(f_equal N.to_nat): H; rewrite Nat2N.id => H.
by rewrite dropN_drop drop_size_cat.
Qed.

Lemma dropN_add {A} (m: list A) n n' :
  dropN (n + n') m = dropN n (dropN n' m).
Proof. by rewrite !dropN_drop N2Nat.inj_add drop_add. Qed.

Lemma dropN_is_nil {A} (m: list A) n :
  dropN n m = nil -> sizeN m <= n.
Proof. by rewrite dropN_drop => /drop_is_nil; rewrite size_sizeN -N2n_le. Qed.





Definition takeN_dflt {A} (dflt: A) (n:N) : seq A -> seq A :=
 N.peano_rect _ (fun _=>[::]) (fun n r s=> if s is x::xs
                                           then x::r xs
                                           else dflt:: r [::]) n.

Lemma take_takeN_dflt: forall A (dfl:A) n s,
 take_dflt dfl n s = takeN_dflt dfl (N.of_nat n) s.
Proof.
by move=> A d; elim => // n IH [|x xs];
rewrite Nat2N.inj_succ /takeN_dflt N.peano_rect_succ /= IH.
Qed.

Lemma takeN_take_dflt: forall A (dfl:A) n s,
 takeN_dflt dfl n s = take_dflt dfl (N.to_nat n) s.
Proof. by move=> A d n s; rewrite take_takeN_dflt N2Nat.id. Qed.

Lemma takeN_dflt_catl: forall n (T : Type) (s1 : seq T),
    (n <= sizeN s1) -> forall d s2, takeN_dflt d n (s1 ++ s2) = takeN_dflt d n s1.
Proof.
move=> n T s1 H d s2.
rewrite !takeN_take_dflt take_dflt_catl //.
by apply/leP; rewrite Compare_dec.nat_compare_le size_sizeN Nat2N.inj_compare !N2Nat.id.
Qed.

Lemma takeN_dflt_eqsize: forall T d n (s : seq T),
    (sizeN s = n) -> takeN_dflt d n s = s.
Proof.
move=> T d n s; rewrite sizeN_size => H.
rewrite takeN_take_dflt take_dflt_eqsize //.
by apply Nat2N.inj; rewrite H N2Nat.id.
Qed.

Lemma size_takeN_dflt: forall A (dfl:A) n s,
 size (takeN_dflt dfl n s) = N.to_nat n.
Proof.
move=> A dfl; elim/N.peano_ind => //=.
move=> n IH [|x xs].
 rewrite /takeN_dflt N.peano_rect_succ Nnat.N2Nat.inj_succ /=.
 by f_equal; apply IH.
rewrite /takeN_dflt N.peano_rect_succ Nnat.N2Nat.inj_succ /=.
by rewrite IH.
Qed.

Lemma sizeN_takeN_dflt: forall A (dfl:A) n s,
 sizeN (takeN_dflt dfl n s) = n.
Proof.
move=> A d n s; apply N2Nat.inj.
by rewrite sizeN_size size_takeN_dflt Nat2N.id.
Qed.

Lemma takeN_dflt_all {A} d (m: list A) :
  takeN_dflt d (sizeN m) m = m.
Proof.
  elim m; clear.
  reflexivity.
  intros a m IH.
  unfold takeN_dflt. simpl.
  rewrite N.peano_rect_succ.
  f_equal. apply IH.
Qed.

Lemma takeN_dflt_split {A} (d: A) s n:
  sizeN s <= n -> takeN_dflt d n s = s ++ (nseqN (n-sizeN s) d).
Proof.
rewrite takeN_take_dflt take_dflt_split sizeN_size nseqN_nseq => Hsize.
rewrite take_oversize; last first.
 by move: Hsize; rewrite N2n_le n2N2n.
by rewrite N2Nat.inj_sub n2N2n.
Qed.

Lemma nth_takeN_dflt A (d:A) bs n x:
 nth d (takeN_dflt d n bs) x = if (x < N2n n)%N
                               then nth d bs x
                               else d.
Proof. by rewrite takeN_take_dflt nth_take_dflt. Qed.




Fixpoint onthN {A} (s: seq A) (n: N) : option A :=
 if s is x::xs
 then if n is N0 then Some x else onthN xs (N.pred n)
 else None.

Lemma onth_onthN {A}: forall (s: seq A) n,
 onth s n = onthN s (N.of_nat n).
Proof.
elim => //= x xs IH [|n] //=.
by rewrite IH pospred_ofsuccnat; f_equal.
Qed.

Lemma onthN_onth: forall A (s: seq A) n,
 onthN s n = onth s (N.to_nat n).
Proof. by move=> A s n; rewrite onth_onthN N2Nat.id. Qed.

Lemma onthN_isS {A} d (s: seq A) n v:
  onthN s n = Some v <-> (n < sizeN s) /\ nthN d s n = v.
Proof.
rewrite onthN_onth (onth_isS d) sizeN_size nthN_nth.
split; move => [H1 H2]; split => //.
 by move: H1; rewrite size_sizeN N2n_lt N2n2N.
by rewrite size_sizeN -N2n_lt sizeN_size.
Qed.

Lemma onthN_isS_cat {A} (x y: seq A) n z :
  onthN x n = Some z ->
  onthN (x ++ y) n = Some z.
Proof. by rewrite !onthN_onth => H; apply onth_isS_cat. Qed.

Lemma map_onthN_iotaN {A} (m: list A) n :
  forall x,
    (x + n <= sizeN m) ->
    map (onthN m) (iotaN x n) = map (@Some _) (take (N2n n) (drop (N2n x) m)).
Proof.
move=> x Hsize.
rewrite -map_onth_iota; last first.
 by move: Hsize; rewrite N2n_le -size_sizeN N2Nat.inj_add plusE => Hsize.
rewrite iotaN_iota.
rewrite -map_comp /=; apply eq_map.
by move=> a /=; rewrite onth_onthN.
Qed.



Definition updprefAtN {A} : N -> seq A -> seq A -> seq A :=
 (N.peano_rect _ (fun orig new => updpref orig new)
               (fun n' r orig new => if orig is x::xs
                                     then x::r xs new
                                     else [::])).

Lemma updprefAtN_updprefAt {A} n (orig new: seq A):
 updprefAtN n orig new = updprefAt (N2n n) orig new.
Proof.
elim/N.peano_ind: n orig new => //= n IH [|x xs] new.
 by rewrite /updprefAtN N.peano_rect_succ Nnat.N2Nat.inj_succ /=.
by rewrite /updprefAtN N.peano_rect_succ Nnat.N2Nat.inj_succ /= -IH.
Qed.

Lemma updprefAt_updprefAtN {A} n (orig new: seq A):
 updprefAt n orig new = updprefAtN (n2N n) orig new.
Proof.
elim: n orig new => // n IH [|x xs] new.
 by rewrite /updprefAtN Nat2N.inj_succ N.peano_rect_succ.
by rewrite /updprefAtN Nat2N.inj_succ N.peano_rect_succ /= IH.
Qed.

Lemma updprefAtN_E {A} n (orig new: seq A):
  updprefAtN n orig new = takeN n orig ++ updpref (dropN n orig) new.
Proof. by rewrite updprefAtN_updprefAt updprefAtE !takeN_take dropN_drop. Qed.

Lemma sizeN_updprefAtN {A} n (orig new: seq A):
  sizeN (updprefAtN n orig new) = sizeN orig.
Proof.
by rewrite updprefAtN_updprefAt !sizeN_size size_updprefAt.
Qed.


(** selects the nth element with a given [width] *)
Definition nthN_width {A} (width:N) (s:seq A) (n:N) : seq A :=
 (N.peano_rect _ (takeN width) (fun n r s=> r (dropN width s)) n) s.

(** selects the nth double element with a given [width] *)
Definition nthN_dwidth {A} (width:N) (s:seq A) (n:N) : seq A :=
 (N.peano_rect _ (takeN (2*width)) (fun n r s=> r (dropN width s)) n) s.

(*
(** updates the nth element with a given [width] *)
Definition updN_width {A} (width:N) (x:seq A) (s:seq A) (n:N) : seq A :=
 (N.peano_rect _ (fun l => x++dropN width l)
               (fun n r s=> takeN width s ++ r (dropN width s)) n) s.

(** upd the nth double element with a given [width] *)
Definition updN_dwidth {A} (width:N) (x:seq A) (s:seq A) (n:N) : seq A :=
 (N.peano_rect _ (fun l => x++dropN (2*width) l)
               (fun n r s=> takeN width s ++ r (dropN width s)) n) s.
*)




