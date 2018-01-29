Require Import ZArith NArith Psatz.
Require Integers Memdata.

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssrlib ssrValues seqN.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


Open Scope N_scope.

Notation bits := (seq bool).
Definition bytes := seq Integers.byte.

Fixpoint drop0trail (s: bits) : bits :=
 if s is x::xs
 then if drop0trail xs is y::ys
      then x::y::ys
      else if x then [:: x] else [::]
 else [::].

Lemma last_drop0trail bs: last true (drop0trail bs).
Proof.
elim: bs => //= b bs IH.
case E: (drop0trail bs) => [| y ys] /=.
 by case: b.
by rewrite E /= in IH.
Qed.

Lemma size_drop0trail bs: (size (drop0trail bs) <= size bs)%N.
Proof.
by elim: bs => //= b bs IH; case E: (drop0trail _) => [|x xs] //=; 
case: b; move: IH; rewrite E.
Qed.

Definition zerobits (s: bits) : bool :=
 all [fun b=> b==false] s.

(* another characterization os [iszero_bits] *)
Lemma zerobits_last_false: forall s,
 zerobits s <-> last false (drop0trail s) = false.
Proof.
elim => //= x xs IH; split.
 move=> /andP [/eqP -> H2]; move: H2; rewrite IH.
 by case E: (drop0trail xs) => [| y ys].
case E: (drop0trail xs) => [| y ys] //=.
 move: IH; rewrite E /=; move => IH.
 by case: x => //=; rewrite -IH.
by move: (last_drop0trail xs); rewrite E /= => ->.
Qed.

Lemma zerobits_drop0trail: forall s,
 zerobits s <-> drop0trail s = [::].
Proof.
elim => //= x xs IH; split.
 move=> /andP [H1 H2]; move: H2; rewrite IH => ->.
 by move: H1; case: ifP.
case E: (drop0trail xs) => [| y ys] //.
by move: E; rewrite -IH => H; case: x.
Qed.

Lemma nth_drop0trail bs n:
 nth false (drop0trail bs) n = nth false bs n.
Proof.
elim: bs n => //=.
move=> b bs IH [|n] //=.
 by case: (drop0trail bs) => //; case: b.
rewrite -IH.
case: (drop0trail bs) => //.
by case: (ifP _) => //; case: n.
Qed.

Lemma nth_eq_drop0trail bs1 bs2:
 (forall n, nth false bs1 n = nth false bs2 n) <-> drop0trail bs1 = drop0trail bs2.
Proof.
split => H.
 apply (@eq_from_nth _ false).
  case: (leqP (size (drop0trail bs1)) (size (drop0trail bs2))); last first.
   move=> Hsz; move: (H (size (drop0trail bs1)).-1).
   rewrite -nth_drop0trail nth_last -nth_drop0trail nth_default.
    rewrite -zerobits_last_false zerobits_drop0trail => HH.
    by move: Hsz; rewrite HH.
   move: Hsz => /ltP Hsz; apply/leP; lia.
  move => /leP F1.
  case: (leqP (size (drop0trail bs2)) (size (drop0trail bs1))); last first.
   move=> Hsz; move: (H (size (drop0trail bs2)).-1).
   rewrite -[nth _ bs2 _]nth_drop0trail nth_last -nth_drop0trail nth_default.
    move=> /esym E; move: E; rewrite -zerobits_last_false zerobits_drop0trail => HH.
    by move: Hsz; rewrite HH.
   move: Hsz => /ltP Hsz; apply/leP; lia.
  move => /leP F2.
  lia.
 by move=> n Hn; rewrite !nth_drop0trail; apply H.
move=> n.
by rewrite -nth_drop0trail H nth_drop0trail.
Qed.

Lemma drop0trail_inj bs1 bs2:
 size bs1 = size bs2 -> drop0trail bs1 = drop0trail bs2 -> bs1 = bs2.
Proof.
move=> Hsz; rewrite -nth_eq_drop0trail => H.
by apply (@eq_from_nth _ false).
Qed.



(** zero/sign extension on bits
  remark: base defs are polymorphic, since they are used elsewhere (connectors)
 *)
Notation zero_ext' := (@take_dflt bool).
Definition zero_ext := zero_ext' false.
Notation zero_extN' := (@takeN_dflt bool).
Definition zero_extN := zero_extN' false.

Fixpoint sign_ext' {A} n (dflt:A) l :=
 if n is S n'
 then if l is (x::xs)
      then x::sign_ext' n' x xs
      else dflt::sign_ext' n' dflt [::]
 else [::].

Definition sign_extN' {A} : N -> A -> seq A -> seq A :=
 N.peano_rect _ (fun d c => [::])
              (fun n r d c => if c is x::xs
                              then x::r x xs
                              else d::r d [::]).
Definition sign_ext n bs := sign_ext' n false bs.
Definition sign_extN n bs := sign_extN' n false bs.

Lemma sign_ext_extN A (d:A) n bs: sign_ext' n d bs = sign_extN' (n2N n) d bs.
Proof.
elim: n d bs => //.
by move=> n IH d [|b bs]; rewrite /sign_extN' Nat2N.inj_succ N.peano_rect_succ /= IH.
Qed.

Lemma sign_extN_ext A (d:A) n bs: sign_extN' n d bs = sign_ext' (N2n n) d bs.
Proof. by rewrite sign_ext_extN N2Nat.id. Qed.

Lemma sign_ext_nil A n (dflt:A): sign_ext' n dflt [::] = nseq n dflt.
Proof. by elim: n dflt => //= n IH //= dflt; rewrite IH. Qed.

Lemma sign_extN_nil A n (dflt:A): sign_extN' n dflt [::] = nseq (N2n n) dflt.
Proof. by rewrite sign_extN_ext sign_ext_nil. Qed.

Lemma sign_ext_split A (d:A) n bs:
 (size bs <= n)%N ->
 sign_ext' n d bs = bs ++ nseq (n - size bs)%N (last d bs).
Proof.
elim: bs n d => //=.
 by move=> [|n] b Hsz; rewrite //= sign_ext_nil.
by move=> x xs IH [|n] b d //=; rewrite subSS IH.
Qed.

Lemma sign_extN_split A (d:A) n bs:
 sizeN bs <= n ->
 sign_extN' n d bs = bs ++ nseqN (n - sizeN bs)%num (last d bs).
Proof.
move=> Hsz; rewrite !sizeN_size sign_extN_ext sign_ext_split. 
 by rewrite nseqN_nseq N2Nat.inj_sub n2N2n minusE.
by rewrite size_sizeN -N2n_le.
Qed.

Lemma size_sign_ext n bs: size (sign_ext n bs) = n.
Proof.
rewrite /sign_ext; elim: n bs false => //= n IH [| b bs] d //=.
 by rewrite sign_ext_nil size_nseq.
by rewrite IH.
Qed.

Lemma sizeN_sign_extN n bs: sizeN (sign_extN n bs) = n.
Proof. by rewrite sizeN_size /sign_extN sign_extN_ext size_sign_ext N2n2N. Qed.

Lemma nth_sign_ext A (d:A) bs n x:
 (size bs <= n)%N ->
 nth d (sign_ext' n d bs) x = if (x < size bs)%N
                              then nth d bs x
                              else if (x < n)%N then last d bs else d.
Proof.
move=> Hn; rewrite sign_ext_split // nth_cat.
case: (ltnP _ _) => // /leP Hx.
case: (ltnP _ _) => // /leP H1; rewrite nth_nseq.
 case: (ltnP _ _) => //.
 rewrite -minusE => /leP H2.
 move/leP: Hn; lia.
case: (ltnP _ _) => //.
rewrite -minusE => /leP H2; lia.
Qed.

Lemma nth_sign_extN A (d:A) bs n x:
 (sizeN bs <= n) ->
 nth d (sign_extN' n d bs) x = if (x < N2n (sizeN bs))%N
                               then nth d bs x
                               else if (x < N2n n)%N then last d bs else d.
Proof.
rewrite sizeN_size -{1}[n]N2n2N -n2N_le => Hsz.
by rewrite sign_extN_ext nth_sign_ext // n2N2n.
Qed.



(** * positive <-> bits *)

(* lsb-first representation of machine integers *)
Fixpoint bits_of_pos (p:positive) : bits :=
 match p with
 | xH => [:: true]
 | xO p' => [:: false & bits_of_pos p']
 | xI p' => [:: true & bits_of_pos p']
 end.

Lemma bits_of_pos_cons p: bits_of_pos p <> [::].
Proof. by case: p. Qed.

Lemma size_bits_of_pos p:
 size (bits_of_pos p) = Pos.size_nat p.
Proof.
elim: p => //=.
 by move => p ->.
by move => p ->.
Qed.

Lemma pos_size_nat_eq: forall p,
 Pos.size_nat p = Pos.to_nat (Pos.size p).
Proof. by elim => //= p H; rewrite Pos2Nat.inj_succ; f_equal. Qed.


Lemma pos_size_bound p:
 (Zpos p < two_power_nat (Pos.size_nat p) <= 2*Zpos p)%Z.
Proof.
have: (Zpos p < two_p (Z.of_nat (Pos.size_nat p)) <= 2*Zpos p)%Z.
 split.
  move: (Pos.size_gt p).
  by rewrite two_p_equiv -Pos.ltb_lt Pos2Z.inj_ltb Pos2Z.inj_pow /= Zpower_pos_nat 
  -two_power_nat_correct two_power_nat_equiv Z.ltb_lt pos_size_nat_eq.
 move: (Pos.size_le p).
 by rewrite two_p_equiv -Pos.leb_le Pos2Z.inj_leb Pos2Z.inj_pow /= Zpower_pos_nat 
  -two_power_nat_correct two_power_nat_equiv Z.leb_le pos_size_nat_eq.
by rewrite two_power_nat_equiv two_p_equiv.
Qed.

Lemma bits_of_pos_not0: forall p n,
  (Pos.size_nat p <= n -> 
   zero_ext n (bits_of_pos p) = zero_ext n [::] -> 
   False)%coq_nat.
Proof.
elim => [p IH|p IH|] [|n] //=; try omega.
move=> H [E]; apply (IH n) => //.
omega.
Qed.

Lemma bits_of_pos_inj: forall p1 p2 n,
 (Pos.size_nat p1 <= n -> Pos.size_nat p2 <= n ->
 zero_ext n (bits_of_pos p1) = zero_ext n (bits_of_pos p2) ->
 p1 = p2)%coq_nat.
Proof.
elim => /= [p1 IH1|p1 IH1|]; elim => /= [p2 IH2|p2 IH2|] [|n] //= Hp1 Hp2;
try omega.
- move=> [E]; f_equal; apply IH1 with n; auto; lia.
- move=> [E]; f_equal.
elimtype False; apply (@bits_of_pos_not0 p1 n); auto; lia.
- move=> [E]; f_equal; apply IH1 with n; auto; lia.
- move=> [E]; f_equal; symmetry in E.
elimtype False; apply (@bits_of_pos_not0 p2 n); auto; lia.
Qed.

(*
Lemma zero_ext_drop0trail bs:
 zero_ext (size bs) (drop_0trail bs) = bs.
Proof.
Qed.
*)

(*
Lemma bits_of_pos_inj: forall p1 p2,
 drop_0trail (bits_of_pos p1) = drop_0trail (bits_of_pos p2) ->
 p1 = p2.
Proof.
Qed.
*)

Lemma size_bounds: forall (p: positive) (n: nat),
    (Z.pos p < 2 ^ Z.of_nat n)%Z -> (Pos.size_nat p <= n)%coq_nat.
Proof.
move=> p n H.
rewrite -[n]Nat2Z.id -[Pos.size_nat _]Nat2Z.id.
apply Z2Nat.inj_le; auto with zarith.
case: (Coqlib.zle (Z.of_nat (Pos.size_nat p)) (Z.of_nat n))=> // Habsurd.
elimtype False.
have: (2*Z.pos p < 2 ^ (Z.of_nat (succn n)))%Z.
 rewrite Nat2Z.inj_succ Z.pow_succ_r; lia.
move=> {H} H.
have: (0 <= Z.of_nat (succn n) <= Z.of_nat (Pos.size_nat p))%Z.
 lia.
move => {Habsurd} Habsurd.
apply Coqlib.two_p_monotone in Habsurd.
move: (pos_size_bound p) => Hbound.
have: (two_power_nat (Pos.size_nat p) < 2 ^ Z.of_nat (succn n))%Z.
 lia.
move => {Hbound} Hbound.
move: Habsurd Hbound; rewrite two_power_nat_equiv !two_p_equiv; lia.
Qed.

(* [pos_of_bits] is a partial function *)
Fixpoint pos_of_bits (s: bits) : option positive :=
 match s with
 | [::] => None
 | true :: xs => if pos_of_bits xs is Some p
                 then Some (xI p)
                 else Some xH
 | false :: xs => if pos_of_bits xs is Some p
                  then Some (xO p)
                  else None
 end.

Lemma pos_of_bits_of_pos: forall p,
 pos_of_bits (bits_of_pos p) = Some p.
Proof. by elim => //= p ->. Qed.

Lemma pos_of_bits0: forall s,
 (pos_of_bits s == None) = (zerobits s).
Proof.
elim => // b bs IH.
by case b => /=; case: (pos_of_bits bs) IH => p'.
Qed.

Lemma pos_of_bits_drop0: forall bs,
 pos_of_bits (drop0trail bs) = pos_of_bits bs.
Proof.
elim => // x xs IH.
case_eq (pos_of_bits xs) => //= [p Ep|Ep].
 by rewrite -IH /=; destruct x; case: (drop0trail xs).
rewrite Ep.
move/eqP: Ep; rewrite pos_of_bits0 zerobits_drop0trail => Ep.
by rewrite Ep; case: x.
Qed.

Lemma bits_of_pos_of_bits: forall s p,
 pos_of_bits s = Some p -> bits_of_pos p = drop0trail s.
Proof.
elim => // b bs IH p /=.
case: ifP => Eb.
 case_eq (pos_of_bits bs).
  move=> p' Ep' [[E]]; rewrite -E /= IH //.
  by case: (drop0trail bs).
 move=> Ep' [[E]]; rewrite -E /=.
 by move/eqP: Ep'; rewrite pos_of_bits0 zerobits_drop0trail => ->.
case_eq (pos_of_bits bs).
 move=> p' Ep' [[E]]; rewrite -E /= -(IH p') //.
 by move: (@bits_of_pos_cons p'); case: (bits_of_pos p').
move => _ H; discriminate H.
Qed.


(** Testbit checks *)

Lemma testbitnat_bits_of_pos n p:
 Pos.testbit_nat p n = nth false (bits_of_pos p) n.
Proof.
elim: n p => //=.
 by move=> [p|p|].
move=> n IH [p|p|] //=.
by case: {IH} n => [|n].
Qed.

Lemma testbitnat_pos_of_bits n bs x:
 pos_of_bits bs = Some x ->
 Pos.testbit_nat x n = nth false bs n.
Proof.
move=> /bits_of_pos_of_bits H.
by rewrite testbitnat_bits_of_pos H nth_drop0trail.
Qed.





(** * N <-> bits
*)


(* by convention, we set the empty sequence of bits to represent [N0]. *)
Definition bits_of_N (n:N) : bits :=
 if n is Npos p
 then bits_of_pos p
 else [::].

Definition N_of_bits (s: bits) : N :=
 if pos_of_bits s is Some p
 then Npos p
 else N0.

Definition N_of_bool (b:bool) : N := if b then 1 else 0.

Lemma N_of_bits_cons b bs:
  N_of_bits (b::bs) = N_of_bool b + 2*(N_of_bits bs).
Proof.
by rewrite /N_of_bits /=; case E: (pos_of_bits bs) => [x|] /=; case: b.
Qed.

Lemma N_of_bits_of_N: forall n,
 N_of_bits (bits_of_N n) = n.
Proof.
move => [|p] //=.
by rewrite /N_of_bits pos_of_bits_of_pos.
Qed.

Lemma bits_of_N_of_bits: forall bs,
 bits_of_N (N_of_bits bs) = drop0trail bs.
Proof.
rewrite /N_of_bits=> bs.
case_eq (pos_of_bits bs) => [p|Ep].
 by move=> /bits_of_pos_of_bits H.
by move/eqP: Ep; rewrite pos_of_bits0 zerobits_drop0trail => ->.
Qed.

Lemma testbitnat_N_of_bits bs n:
 N.testbit_nat (N_of_bits bs) n = nth false bs n.
Proof.
rewrite /N_of_bits; case E: (pos_of_bits bs) => /=. (* => [s|] -> /=.*)
 by rewrite (testbitnat_pos_of_bits _ E).
move/eqP: E; rewrite pos_of_bits0 => /allP E.
case: (@leqP (size bs) n)%N => H.
 by rewrite nth_default.
by symmetry; apply/eqP; apply E; rewrite mem_nth.
Qed.

Lemma testbit_N_of_bits bs n:
 N.testbit (N_of_bits bs) n = nth false bs (N2n n).
Proof. by rewrite -Nbit_Ntestbit testbitnat_N_of_bits. Qed.





(** * Z <-> bits
*)

(* by convention, we set the empty sequence of bits to represent [Z0]. *)
Definition bits_of_Z (z:Z) : bits :=
 if z is Zpos p
 then bits_of_pos p
 else [::].

Lemma size_bits_of_Z z: forall n,
 (z < two_power_nat n)%Z -> (size (bits_of_Z z) <= n)%coq_nat.
Proof.
move=> n; rewrite two_power_nat_equiv => H.
destruct z; try (simpl; lia).
rewrite /bits_of_Z size_bits_of_pos.
by apply size_bounds.
Qed.

Definition Z_of_bits (s: bits) : Z := Z_of_N (N_of_bits s).

Open Scope Z_scope.
Definition Z_of_bool (b:bool) : Z := if b then 1 else 0.

Lemma Z_of_bits_cons: forall x xs,
 Z_of_bits (x::xs) = Z_of_bool x + 2*Z_of_bits xs.
Proof.
by rewrite /Z_of_bits /N_of_bits /=; move => [|] xs ;case: (pos_of_bits xs).
Qed.

Lemma Z_of_bits_cat: forall xs ys,
 Z_of_bits (xs++ys) = (Z_of_bits xs + two_power_nat (size xs) * Z_of_bits ys)%Z.
Proof.
elim => [ys|x xs IH ys].
 by rewrite Coqlib.two_power_nat_O Z.mul_1_l.
by rewrite cat_cons !Z_of_bits_cons IH Zmult_addr Zplus_assoc Zmult_assoc.
Qed.

Lemma Z_of_bits_bounds: forall bs,
    0 <= Z_of_bits bs < two_power_nat (size bs).
Proof.
elim => [|x xs IH].
 by rewrite Coqlib.two_power_nat_O.
rewrite Z_of_bits_cons [size _]/=  two_power_nat_S. 
case: x; rewrite [Z_of_bool _]/=; lia.
Qed.


Lemma Z_of_bits_bounds' bs:
    0 <= Z_of_bits bs <= two_power_nat (size bs) - 1.
Proof.
move: (Z_of_bits_bounds bs).
move=> [H1 H2]; split => //. 
rewrite -[Z_of_bits _]Z.add_0_r -[0%Z]/(1-1)%Z Z.add_sub_assoc Z.add_1_r.
by apply Z.sub_le_mono => //; apply Zlt_le_succ; apply H2.
Qed.

Lemma Z_of_bits_of_Z: forall n,
 (n >= 0)%Z ->
 Z_of_bits (bits_of_Z n) = n.
Proof.
move => [|p|p] //=.
 by rewrite /Z_of_bits /N_of_bits pos_of_bits_of_pos.
move: (Zlt_neg_0 p) => H1 H2; elimtype False; auto.
Qed.

Lemma bits_of_Z_of_bits: forall bs,
 bits_of_Z (Z_of_bits bs) = drop0trail bs.
Proof.
rewrite /Z_of_bits /Z.of_N /N_of_bits => bs.
case_eq (pos_of_bits bs) => [p|Ep].
 by move=> /bits_of_pos_of_bits H.
by move/eqP: Ep; rewrite pos_of_bits0 zerobits_drop0trail => ->.
Qed.

Lemma Z_of_bits_inj bs1 bs2:
 size bs1 = size bs2 -> Z_of_bits bs1 = Z_of_bits bs2 -> bs1=bs2.
Proof.
move=> Hsz E.
apply drop0trail_inj => //.
by rewrite -!bits_of_Z_of_bits E.
Qed.

Lemma Z_of_bits_zero_ext: forall bs n,
 (size bs <= n)%N -> Z_of_bits (zero_ext n bs) = Z_of_bits bs.
Proof.
elim => //=.
 by move=> n _; elim: n => // n IH; rewrite Z_of_bits_cons IH.
move=> b bs IH [|n] H //=.
by rewrite !Z_of_bits_cons IH.
Qed.

Lemma Z_of_bits_zero_ext': forall n z,
 0 <= z < two_power_nat n -> Z_of_bits (zero_ext n (bits_of_Z z)) = z.
Proof.
move=> n z [H1 H2]. 
rewrite Z_of_bits_zero_ext; first rewrite Z_of_bits_of_Z; auto with zarith.
by apply/leP; apply size_bits_of_Z.
Qed.

Lemma Z_of_bits_take: forall n z,
 0 <= z < two_power_nat n -> Z_of_bits (take n (bits_of_Z z)) = z.
Proof.
move=> n z [H1 H2]. 
rewrite take_oversize; first rewrite Z_of_bits_of_Z; auto with zarith.
by apply/leP; apply size_bits_of_Z.
Qed.


Lemma testbitnat_Z_of_bits n bs:
 Z.testbit (Z_of_bits bs) (Z.of_nat n) = nth false bs n.
Proof.
rewrite -nat_N_Z Z2N.inj_testbit; last first.
 by apply N2Z.is_nonneg.
by rewrite N2Z.id Ntestbit_Nbit testbitnat_N_of_bits.
Qed.

Lemma testbit_Z_of_bits n bs:
 (0 <= n)%Z ->
 Z.testbit (Z_of_bits bs) n = nth false bs (Z.to_nat n).
Proof. by move=> H; rewrite -[n]Z2Nat.id // testbitnat_Z_of_bits Nat2Z.id. Qed.






Close Scope Z_scope.

Require Import Integers.
Definition bits_of_byte (i: byte) : bits :=
 take_dflt false Byte.wordsize (bits_of_Z (Byte.unsigned i)).

Lemma size_bits_of_byte i:
 size (bits_of_byte i) = 8%nat.
Proof. by rewrite (size_take_dflt _ _ _). Qed.

Lemma Z_of_bits_of_byte: forall b xs,
 Z_of_bits (bits_of_byte b ++ xs) = (Byte.unsigned b + Byte.modulus * Z_of_bits xs)%Z.
Proof.
move=> b xs. 
rewrite Z_of_bits_cat size_bits_of_byte /=; f_equal.
rewrite /Byte.unsigned /Byte.intval.
destruct b. unfold bits_of_byte.
rewrite Z_of_bits_zero_ext' //=.
move: intrange; unfold Byte.modulus; lia.
Qed.

Lemma bits_of_byte_inj b1 b2:
 bits_of_byte b1 = bits_of_byte b2 -> b1 = b2.
Proof.
rewrite /bits_of_byte; move/(f_equal Z_of_bits).
have Hbnd1 b: (Byte.unsigned b < two_power_nat Byte.wordsize)%Z.
 by move: (Byte.unsigned_range b); rewrite /Byte.modulus; lia.
have Hbnd2 b: (Byte.unsigned b >= 0)%Z.
 by move: (Byte.unsigned_range b); lia.
rewrite !Z_of_bits_zero_ext; first last.
  by apply/leP; apply size_bits_of_Z.
 by apply/leP; apply size_bits_of_Z.
rewrite !Z_of_bits_of_Z //.
move: b1 b2 => [b1 Hb1] [b2 Hb2] /= E. 
by apply Byte.mkint_eq.
Qed.

Definition bits_of_bytes (xs: seq byte) : bits :=
 foldr (fun x r=>(bits_of_byte x) ++ r) [::] xs.

Lemma size_bits_of_bytes bs:
 size (bits_of_bytes bs) = (8*size bs)%N.
Proof. 
elim: bs => //= x xs IH.
rewrite size_cat IH size_bits_of_byte /=; ring.
Qed.

Lemma sizeN_bits_of_bytes bs:
  sizeN (bits_of_bytes bs) = 8 * sizeN bs.
Proof. by rewrite !sizeN_size size_bits_of_bytes Nat2N.inj_mul. Qed.

Lemma bits_of_bytes_cat: forall xs ys,
 bits_of_bytes (xs++ys) = bits_of_bytes xs ++ bits_of_bytes ys.
Proof. by elim => //=; move=> x xs IH ys; rewrite IH catA. Qed.

Lemma bits_of_bytes_inj bs1 bs2:
 bits_of_bytes bs1 = bits_of_bytes bs2 -> bs1 = bs2.
Proof.
have HH b bs: bits_of_byte b ++ bs == [::] = false.
 apply/negP; move=> /eqP /(f_equal size) /=.
 by rewrite size_cat size_bits_of_byte.
elim: bs1 bs2 => //=.
 move=> [|b2 bs2] //=.
 by move/eqP; rewrite eq_sym HH.
move=> b1 bs1 IH1; elim => //=.
 by move/eqP; rewrite HH.
move=> b2 bs2 IH2.
move/eqP; rewrite eqseq_cat; last first.
 by rewrite !size_bits_of_byte.
move=> /andP [/eqP H1 /eqP H2].
rewrite (@bits_of_byte_inj b1 b2) //; f_equal.
by apply IH1.
Qed.

(** bits <-> bytes *)

Lemma Z_of_bits_of_bytes bs:
 Z_of_bits (bits_of_bytes bs) = Memdata.int_of_bytes bs.
Proof.
elim: bs => //= b bs <-; rewrite Z_of_bits_cat size_bits_of_byte Z.mul_comm; f_equal.
by rewrite -[bits_of_byte _]cats0 Z_of_bits_of_byte /= Z.add_0_r.
Qed.

Lemma decode_int_of_bytes bs:
 Memdata.decode_int bs = Memdata.int_of_bytes bs.
Proof. reflexivity. Qed.

(** int8 *)

Definition bytes_of_int8 (i: int) : bytes :=
 Memdata.bytes_of_int 1 (Int.unsigned i).

Definition bits_of_int8 (i: int) : bits :=
 bits_of_bytes (bytes_of_int8 i).

(*
Lemma bits_of_int8_size i: size (bits_of_int8 i) = 8.
Proof. by rewrite /bits_of_int8 /bytes_of_int8 bits_of_bytes_size. Qed.
*)

(** int16 *)

Definition bytes_of_int16 (i: int) : bytes :=
 Memdata.bytes_of_int 2 (Int.unsigned i).
(*
Definition bits_of_int16 (i: int) : bits :=
 bits_of_bytes (bytes_of_int16 i).

Lemma bits_of_int16_size i: size (bits_of_int16 i) = 16.
Proof. by rewrite /bits_of_int16 /bytes_of_int16 bits_of_bytes_size. Qed.
*)

(** int32 *)

Definition bytes_of_int32 (i: int) : bytes :=
 Memdata.bytes_of_int 4 (Int.unsigned i).

Definition bits_of_int32 (i: int) : bits :=
 bits_of_bytes (bytes_of_int32 i).

Lemma size_bits_of_int32 i: size (bits_of_int32 i) = 32%N.
Proof. by rewrite /bits_of_int32 /bytes_of_int32 size_bits_of_bytes. Qed.

Lemma Z_of_bits_of_int32: forall i xs,
 Z_of_bits (bits_of_int32 i ++ xs) = (Int.unsigned i + Int.modulus * Z_of_bits xs)%Z.
Proof.
move=> i xs.
rewrite /bits_of_int32 /bytes_of_int32.
rewrite Z_of_bits_cat Z_of_bits_of_bytes size_bits_of_bytes; f_equal.
by rewrite Memdata.int_of_bytes_of_int -Int.unsigned_repr_eq Int.repr_unsigned.
Qed.


Definition int32_of_bits (x: bits) : int :=
 Int.repr (Z_of_bits x).

Lemma int32_of_bits_of_bytes bs:
 int32_of_bits (bits_of_bytes bs) = Int.repr (Memdata.int_of_bytes bs).
Proof. by rewrite /int32_of_bits Z_of_bits_of_bytes. Qed.

Lemma bytes_of_bits_of_int32 i bs:
 bits_of_bytes bs = bits_of_int32 i ->
 bs = Memdata.encode_int 4 (Int.unsigned i).
Proof.
by rewrite /bits_of_int32 /bytes_of_int32; move=> /bits_of_bytes_inj ->.
Qed.

Lemma int32_of_bits_of_int32: forall i,
 int32_of_bits (bits_of_int32 i) = i.
Proof.
move=> [i Hi]; rewrite /int32_of_bits /Int.repr /=. 
apply Int.mkint_eq.
rewrite -[bits_of_int32 _]cats0 Z_of_bits_of_int32 /=.
rewrite ZplusC /=.
rewrite Int.Z_mod_modulus_eq Coqlib.Zmod_small; auto with zarith.
Qed.

Definition bits_of_int32_inj i1 i2:
  bits_of_int32 i1 = bits_of_int32 i2 ->
  i1 = i2.
Proof.
by move=> E; rewrite -[i1]int32_of_bits_of_int32 -[i2]int32_of_bits_of_int32 E.
Qed.

Definition int32_of_bits_inj bs1 bs2:
  size bs1 = 32%N ->
  size bs2 = 32%N ->
  int32_of_bits bs1 = int32_of_bits bs2 ->
  bs1 = bs2.
Proof.
rewrite /int32_of_bits => Hbs1 Hbs2 H.
apply Z_of_bits_inj; first by rewrite Hbs1 Hbs2.
rewrite -[_ bs1]Int.unsigned_repr; last first.
 by move: (Z_of_bits_bounds' bs1); rewrite Hbs1.
rewrite -[_ bs2]Int.unsigned_repr; last first.
 by move: (Z_of_bits_bounds' bs2); rewrite Hbs2.
by rewrite H.
Qed.

Lemma bits_of_int32_of_bits bs:
  size bs = 32%N -> bits_of_int32 (int32_of_bits bs) = bs.
Proof.
move=> Hsz; apply int32_of_bits_inj => //.
 by rewrite size_bits_of_int32.
by rewrite int32_of_bits_of_int32.
Qed.

Lemma testbit_int32_of_bits bs n:
 (0 <= n)%Z -> (size bs <= 32)%N ->
  Int.testbit (int32_of_bits bs) n = nth false bs (Z.to_nat n).
Proof.
move=> H1 H2; rewrite /Int.testbit Int.unsigned_repr; last first.
 have: (two_p (Z.of_nat (size bs)) <= two_p (Z.of_nat 32))%Z.
  apply (Coqlib.two_p_monotone (Z.of_nat (size bs)) (Z.of_nat 32)); split.
   by apply Nat2Z.is_nonneg.
  by apply Nat2Z.inj_le; apply/leP.
 rewrite -!Coqlib.two_power_nat_two_p.
 move: (Z_of_bits_bounds bs) => H.
 rewrite /Int.max_unsigned /Int.modulus /Int.wordsize /Wordsize_32.wordsize.
 lia.
by rewrite testbit_Z_of_bits.
Qed.

Lemma testbit_bits_of_int32 n i:
 (0 <= n)%Z ->
 Int.testbit i n = nth false (bits_of_int32 i) (Z.to_nat n).
Proof.
move=> H.
rewrite -[i]int32_of_bits_of_int32 // testbit_int32_of_bits //. 
 by rewrite int32_of_bits_of_int32.
by rewrite size_bits_of_int32.
Qed.

Lemma zero_extN_int32_of_bits n data:
 (0 < n <= 32)%Z ->
 (8*Z.of_N (sizeN data) = n)%Z ->
 Int.zero_ext n (Int.repr (Memdata.decode_int data))
 = int32_of_bits (zero_extN 32 (bits_of_bytes data)).
Proof.
move=> [H0 H32] Hn; rewrite decode_int_of_bytes -int32_of_bits_of_bytes.
apply Int.same_bits_eq.
rewrite /Int.zwordsize /Int.wordsize /Wordsize_32.wordsize => q [Hq1 Hq2].
rewrite Int.bits_zero_ext //.
rewrite [Int.testbit _ q]testbit_int32_of_bits //; last first.
 move: H32; rewrite -Hn sizeN_size size_bits_of_bytes nat_N_Z -multE => HH.
 apply/leP; lia.
rewrite testbit_int32_of_bits //; last first.
 by rewrite /zero_extN size_takeN_dflt.
rewrite /zero_extN nth_takeN_dflt //; last first.
case: (ifP _) => H1; last first.
 move/negP: H1; rewrite -Z_N_nat -N2n_lt -[32]/(Z.to_N 32%Z) -Z2N.inj_lt; lia.
case: (Coqlib.zlt q n) => H2 //.
rewrite nth_default // size_bits_of_bytes. 
have ->: (8*size data = Z.to_nat n)%N.
 rewrite size_sizeN -[8%N]/(N2n 8) -multE -N2Nat.inj_mul -Z_N_nat; f_equal.
 rewrite -Hn Z2N.inj_mul ?N2Z.id //; lia.
apply/leP; rewrite -Z2Nat.inj_le; lia.
Qed.

Lemma sign_extN_int32_of_bits n data:
 (0 < n <= 32)%Z ->
 (8*Z.of_N (sizeN data) = n)%Z ->
 Int.sign_ext n (Int.repr (Memdata.decode_int data))
 = int32_of_bits (sign_extN 32 (bits_of_bytes data)).
Proof.
move=> [H0 H32] Hn.
move: (Hn); rewrite -{1}[8%Z]Z2Nat.id // sizeN_size nat_N_Z -Nat2Z.inj_mul.
rewrite -{1}[n]Z2Nat.id; last lia.
move/Nat2Z.inj; rewrite multE => Hn'.
rewrite decode_int_of_bytes -int32_of_bits_of_bytes.
apply Int.same_bits_eq.
rewrite /Int.zwordsize /Int.wordsize /Wordsize_32.wordsize => q [Hq1 Hq2].
rewrite Int.bits_sign_ext //.
rewrite [Int.testbit _ q]testbit_int32_of_bits //; last first.
 by rewrite /sign_extN sign_extN_ext size_sign_ext.
rewrite nth_sign_extN //; last first.
 rewrite sizeN_size size_bits_of_bytes Hn' -Z_N_nat N2n2N. 
 rewrite -[32]/(Z.to_N 32)%Z -Z2N.inj_le //; lia.
rewrite testbit_int32_of_bits; first last.
  rewrite size_bits_of_bytes Hn'.
  apply/leP. rewrite -[32%N]/(Z.to_nat 32)%Z -Z2Nat.inj_le //; lia.
 case: (Coqlib.zlt _ _) => //=; lia.
case: (ifP _) => /ltP; rewrite sizeN_size size_bits_of_bytes Hn' n2N2n.
 rewrite -Z2Nat.inj_lt //; last lia.
 by case: (Coqlib.zlt _ _) => //= H2. 
case: (Coqlib.zlt _ _) => //= H2.
 rewrite -Z2Nat.inj_lt //; lia. 
case: (ltnP _ _) => //=; rewrite -Z2Nat.inj_lt //; [|lia| |lia].
 move=> H4; rewrite -nth_last size_bits_of_bytes Z2Nat.inj_sub //= -Hn.
 move => HH; f_equal.
 rewrite Z2Nat.inj_mul //; last lia.
 by rewrite sizeN_size nat_N_Z Nat2Z.id -multE -subn1 -minusE.
move/ltP; rewrite -[31%N]Nat2Z.id -Z2Nat.inj_lt //= => H3; lia.
Qed.


(** argument picking *)

Definition int32_of_bits_at (pos: N) (x: bits) : int :=
 int32_of_bits (take Int.wordsize (dropN pos x)).

Lemma int32_of_bits_at_n': forall n xs i ys,
    sizeN xs = n -> int32_of_bits_at n (xs ++ bits_of_int32 i ++ ys) = i.
Proof.
move=> n xs i ys H; rewrite /int32_of_bits_at.
rewrite dropN_sizeN_cat //.
rewrite takel_cat; last first.
 by rewrite size_bits_of_int32 /Int.wordsize.
rewrite take_oversize; last first.
 by rewrite size_bits_of_int32 /Int.wordsize.
by apply int32_of_bits_of_int32.
Qed.

Lemma int32_of_bits_at_n: forall n xs i,
    sizeN xs = n -> int32_of_bits_at n (xs ++ bits_of_int32 i) = i.
Proof. by move=> n xs i H; rewrite -[bits_of_int32 _]cats0 int32_of_bits_at_n'. Qed.

Lemma int32_of_bits_at_0': forall i bs,
    int32_of_bits_at 0 (bits_of_int32 i ++ bs) = i.
Proof. by move=> i bs; rewrite -[_++_]/([::]++_) int32_of_bits_at_n'. Qed.

Lemma int32_of_bits_at_0: forall i,
    int32_of_bits_at 0 (bits_of_int32 i) = i.
Proof. by move=> i; rewrite -[bits_of_int32 _]cats0 int32_of_bits_at_0'. Qed.

Lemma int32_of_bits_at_32: forall i1 i2,
    int32_of_bits_at 32 (bits_of_int32 i1 ++ bits_of_int32 i2) = i2.
Proof.
by move=> i1 i2; rewrite int32_of_bits_at_n // sizeN_size size_bits_of_int32.
Qed.

(** int64 *)

Definition bytes_of_int64 (i: Int64.int) : bytes :=
 Memdata.bytes_of_int 8 (Int64.unsigned i).

Definition bits_of_int64 (i: Int64.int) : bits :=
 bits_of_bytes (bytes_of_int64 i).

Lemma size_bits_of_int64 i: size (bits_of_int64 i) = 64%N.
Proof. by rewrite /bits_of_int64 /bytes_of_int64 size_bits_of_bytes. Qed.

Definition int64_of_bits (x: bits) : int64 :=
 Int64.repr (Z_of_bits x).

(*
Definition int64_of_bits_at (pos: N) (x: bits) : int64 :=
 int64_of_bits (takeN_dflt false 64 (dropN pos x)).
*)

Lemma Z_of_bits_of_int64: forall i xs,
 Z_of_bits (bits_of_int64 i ++ xs) = (Int64.unsigned i + Int64.modulus * Z_of_bits xs)%Z.
Proof.
move=> i xs.
rewrite /bits_of_int32 /bytes_of_int32.
rewrite Z_of_bits_cat Z_of_bits_of_bytes size_bits_of_bytes; f_equal.
by rewrite Memdata.int_of_bytes_of_int -Int64.unsigned_repr_eq Int64.repr_unsigned.
Qed.

Lemma bits_of_int64_lohi: forall i,
  bits_of_int64 i = bits_of_int32 (Int64.loword i) ++ bits_of_int32 (Int64.hiword i).
Proof.
move=> i.
rewrite -{1}[i]Int64.ofwords_recompose /bits_of_int64 /bits_of_int32 
/bytes_of_int64 /bytes_of_int32 Memdata.bytes_of_int64 !Int64.lo_ofwords 
!Int64.hi_ofwords.
by rewrite -appE bits_of_bytes_cat.
Qed.

Lemma bytes_of_bits_of_int64 i bs:
 bits_of_bytes bs = bits_of_int64 i ->
 bs = Memdata.encode_int 8 (Int64.unsigned i).
Proof.
by rewrite /bits_of_int64 /bytes_of_int64; move=> /bits_of_bytes_inj ->.
Qed.

(* *)

Definition byte_of_bits bs := Byte.repr (Z_of_bits bs).
Definition byte_of_bits_inj bs1 bs2:
  size bs1 = 8%N ->
  size bs2 = 8%N ->
  byte_of_bits bs1 = byte_of_bits bs2 ->
  bs1 = bs2.
Proof.
rewrite /byte_of_bits => Hbs1 Hbs2 H.
apply Z_of_bits_inj; first by rewrite Hbs1 Hbs2.
rewrite -[_ bs1]Byte.unsigned_repr; last first.
 by move: (Z_of_bits_bounds' bs1); rewrite Hbs1.
rewrite -[_ bs2]Byte.unsigned_repr; last first.
 by move: (Z_of_bits_bounds' bs2); rewrite Hbs2.
by rewrite H.
Qed.
Lemma byte_of_bits_of_byte b:
 byte_of_bits (bits_of_byte b) = b.
Proof.
replace (bits_of_byte b) with (bits_of_bytes [:: b]); last first.
 by rewrite /= cats0.
move: b=> [i Hi]; rewrite /byte_of_bits /Byte.repr. 
apply Byte.mkint_eq.
rewrite Z_of_bits_of_bytes /= Z.add_0_r.
by rewrite Byte.Z_mod_modulus_eq Coqlib.Zmod_small; auto with zarith.
Qed.
Lemma bits_of_byte_of_bits bs:
  size bs = 8%N -> bits_of_byte (byte_of_bits bs) = bs.
Proof.
move=> Hsz; apply byte_of_bits_inj => //.
 by rewrite size_bits_of_byte.
by rewrite byte_of_bits_of_byte.
Qed.
Lemma bytes_of_bits xbits:
 (exists k, size xbits = 8 * k)%N -> exists bs, xbits = bits_of_bytes bs.
Proof.
move=> [k]; elim: k xbits => //=.
 rewrite muln0; move => [| x xs] // _.
 by exists [::].
move=> n IH xbits; rewrite mulnS => H.
move: (cat_take_drop 8 xbits) => E.
have T: size (drop 8 xbits) = (8*n)%N.
 by rewrite size_drop H addKn.
move: (IH _ T) => [bs IH'].
exists (byte_of_bits (take 8 xbits)::bs).
rewrite /= -{1}E; f_equal => //.
rewrite bits_of_byte_of_bits // size_take.
case: (ifP _) => //.
rewrite H => /ltP; rewrite -plusE; lia.
Qed.


(*
   Memory handling
*)

Definition match_byte (mv: Memdata.memval) (b: byte) : bool :=
  match mv with
  | Memdata.Undef => true
  | Memdata.Byte b' => b' == b
  | Memdata.Fragment _ _ _ => false
  end.


Section All2.

Variable A B: Type.

Variable p: A -> B -> bool.


Fixpoint all2 (l1: seq A) (l2: seq B) : bool :=
 if l1 is x::xs
 then if l2 is y::ys
      then p x y && all2 xs ys
      else false
 else if l2 is [::] then true else false.

Lemma all2_ind P:
  P [::] [::] ->
  (forall x xs y ys, P xs ys -> p x y -> all2 xs ys -> P (x::xs) (y::ys)) ->
  forall l1 l2, all2 l1 l2 -> P l1 l2.
Proof.
move=> P0 PS; elim => //=.
 by move=> [|y ys].
move=> x xs IH; elim => //= y ys IH2.
move=> /andP [Hp H]; apply PS => //.
by apply IH.
Qed.

Lemma all2_nil: all2 [::] [::].
Proof. by []. Qed.

Lemma all2_cons x xs y ys:
 p x y ->
 all2 xs ys ->
 all2 [:: x & xs] [:: y & ys].
Proof. by move=> /= -> ->. Qed.

Lemma all2_size xs ys:
 all2 xs ys -> size xs = size ys.
Proof.
elim: xs ys => //=.
 by move=> [|y ys].
move=> x xs IH /= [| y ys] // /andP [Hp H] /=.
by rewrite (IH ys).
Qed.

Lemma all2_catl x1 x2 y1 y2:
 all2 x1 y1 -> all2 x2 y2 = all2 (x1++x2) (y1++y2).
Proof.
elim: x1 y1 => //=.
 by move=> [|y y1].
move=> x x1 IH [|y y1] //= /andP [-> H].
rewrite -IH //.
Qed.

Lemma all2_catr x1 x2 y1 y2:
 all2 x2 y2 -> all2 x1 y1 = all2 (x1++x2) (y1++y2).
Proof.
elim: x1 y1 => //=.
  move=> [|y y1] //= H.
  symmetry; apply/negP => E.
  have: size x2 <> size (y::y1 ++ y2).
   rewrite /= size_cat (all2_size H) /= -plusE; omega.
  by apply; apply (all2_size E).
move=> x x1 IH; elim => //=.
 move: {IH} y2 => [|y' y2] //= => /all2_size /= H.
 symmetry; apply/negP/negP/nandP; right; apply/negP=> /all2_size.
 rewrite size_cat H -plusE => {H} H. omega.
move=> y y1 IH2 //= H.
by rewrite -IH.
Qed.

Lemma all2_cat x1 x2 y1 y2:
 all2 x1 y1 -> all2 x2 y2 -> all2 (x1++x2) (y1++y2).
Proof. by move=> H1 H2; rewrite -(all2_catl _ _ H1). Qed.

Lemma all2_catIl x1 x2 ys:
 reflect (exists y1 y2, ys=y1++y2 /\ all2 x1 y1 /\ all2 x2 y2)
         (all2 (x1++x2) ys).
Proof. 
elim: x1 ys => //=.
 move=> y; apply: (iffP idP).
  by move=> H; exists [::], y.
 by move=> [[|x y1] [y2 [-> [H1 H2]]]].
move=> x x1 IH; elim => //=.
 apply: (iffP idP) => //=.
 by move=> [[|y1 y11] [[|y2 y22] [E [H1 H2]]]].
move=> y y1 _ /=; apply: (iffP idP) => //=.
 move=> /andP [Hp /IH [z1 [z2 [-> [H1 H2]]]]].
 exists [:: y & z1], z2; split => //=.
 by rewrite Hp H1 H2.
move=> [[|z z1] //= [z2 [E [//= /andP [H1 H2] H3]]]].
move: E => [-> E]; apply/andP; split; first by exact H1.
by apply/IH; exists z1, z2.
Qed.

Lemma all2_catIr xs y1 y2:
 reflect (exists x1 x2, xs=x1++x2 /\ all2 x1 y1 /\ all2 x2 y2)
         (all2 xs (y1++y2)).
Proof.
elim: y1 xs => //=.
 move=> x; apply: (iffP idP).
  by move=> H; exists [::], x.
 by move=> [[|z z1] [z2 [-> [H1 H2]]]].
move=> y y1 IH; elim => //=.
 apply: (iffP idP) => //=.
 by move=> [[|x1 x11] [[|x2 x22] [E [H1 H2]]]].
move=> x x1 _ /=; apply: (iffP idP) => //=.
 move=> /andP [Hp /IH [z1 [z2 [-> [H1 H2]]]]].
 exists [:: x & z1], z2; split => //=.
 by rewrite Hp H1 H2.
move=> [[|z z1] //= [z2 [E [//= /andP [H1 H2] H3]]]].
move: E => [-> E]; apply/andP; split; first by exact H1.
by apply/IH; exists z1, z2.
Qed.

Section All2Props.

Variables (mxs: seq A) (xs: seq B).

Hypothesis H: all2 mxs xs.


Lemma all2_nseq n x x': p x x' -> all2 (nseq n x) (nseq n x').
Proof.
by elim: n => //= n IH Hp; apply/andP; split => //; apply IH.
Qed.

Lemma all2_take n: all2 (take n mxs) (take n xs).
Proof.
move: mxs xs H n; apply: all2_ind => //.
by move=> z zs y ys IH Hzy Hall [|n] //=; apply/andP; split.
Qed.

Lemma all2_take_dflt n dA dB: p dA dB -> all2 (take_dflt dA n mxs) (take_dflt dB n xs).
Proof.
move=> Hd; move: mxs xs H n; apply: all2_ind => //.
 by elim => //= n IH; apply/andP. 
by move=> z zs y ys IH Hyz Hall [|n] //=; apply/andP; split.
Qed.

Lemma all2_drop n: all2 (drop n mxs) (drop n xs).
Proof.
move: mxs xs H n; apply: all2_ind => //.
by move=> z zs y ys IH Hyz Hall [|n] //=; apply/andP; split.
Qed.

End All2Props.

Lemma all2_updpref mxs xs mys ys :
 all2 mxs xs -> all2 mys ys -> all2 (updpref mxs mys) (updpref xs ys).
Proof.
move=> H1 H2; rewrite !updprefE.
rewrite (all2_size H1) (all2_size H2); apply all2_cat.
 by apply all2_take.
by apply all2_drop.
Qed.

Lemma all2_updprefAt n mxs xs mys ys:
 all2 mxs xs -> all2 mys ys -> all2 (updprefAt n mxs mys) (updprefAt n xs ys).
Proof.
move=> H1 H2; rewrite !updprefAtE; apply all2_cat.
 by apply all2_take.
apply all2_updpref => //.
by apply all2_drop.
Qed.

Section All2PropsN.

Variables (mxs: seq A) (xs: seq B).

Hypothesis H: all2 mxs xs.

Lemma all2_sizeN: sizeN mxs = sizeN xs.
Proof. by rewrite !sizeN_size (all2_size H). Qed.

Lemma all2_nseqN n x x': p x x' -> all2 (nseqN n x) (nseqN n x').
Proof. by rewrite !nseqN_nseq; apply all2_nseq. Qed.

Lemma all2_takeN n: all2 (takeN n mxs) (takeN n xs).
Proof. by rewrite !takeN_take; apply all2_take. Qed.

Lemma all2_takeN_dflt n dA dB:
  p dA dB -> all2 (takeN_dflt dA n mxs) (takeN_dflt dB n xs).
Proof. by rewrite !takeN_take_dflt; apply all2_take_dflt. Qed.

Lemma all2_dropN n: all2 (dropN n mxs) (dropN n xs).
Proof. by rewrite !dropN_drop; apply all2_drop. Qed.

Lemma all2_updprefAtN n mys ys:
 all2 mys ys -> all2 (updprefAtN n mxs mys) (updprefAtN n xs ys).
Proof. by rewrite !updprefAtN_updprefAt; apply all2_updprefAt. Qed.

End All2PropsN.

End All2.

Lemma all2_map {A B C D} (f:A->C) (g:B->D) (p:A->B->bool) (p':C->D->bool) xs ys:
 (forall x y, p x y -> p' (f x) (g y)) ->
 all2 p xs ys -> all2 p' (map f xs) (map g ys).
Proof.
move=> Hmap; move: xs ys; apply: all2_ind => //=.
move=> x xs y ys IH Hp Hall; apply/andP; split.
 by apply Hmap.
by apply IH.
Qed.




Notation match_bytes := (@all2 _ _ match_byte). 

Fixpoint byte_shape_md (l: seq Memdata.memval) : bool :=
 if l is x::xs
 then if x is (Memdata.Fragment _ _ _) then false else byte_shape_md xs
 else true.

Lemma match_bytes_byte_shape_md mbs bs:
 match_bytes mbs bs -> byte_shape_md mbs.
Proof.
move: mbs bs; apply: all2_ind => //=.
by move=> [|b|? ? ?].
Qed.

Lemma byte_shape_md_catl l1 l2: byte_shape_md (l1++l2) -> byte_shape_md l1.
Proof.
elim: l1 => //=.
by move=> [|?|? ? ?] mbs IH H //; apply IH.
Qed.

Lemma byte_shape_md_catr l1 l2: byte_shape_md (l1++l2) -> byte_shape_md l2.
Proof.
elim: l1 => //=.
by move=> [|?|? ? ?] mbs IH H //; apply IH.
Qed.

Lemma match_bytes_map_Byte bs: match_bytes (map Memdata.Byte bs) bs.
Proof. by elim: bs => //= x xs ->; rewrite eq_refl. Qed.



Lemma bytes_of_int_of_bytes n bs:
 size bs = n ->
 Memdata.bytes_of_int n (Memdata.int_of_bytes bs) = bs.
Proof.
elim: bs n => //=.
 by move=> n <-.
move=> b bs IH [|n] [Hsz] //.
rewrite -add1n -plusE -[256%Z]/(two_p (Z.of_nat 1 * 8)).
rewrite Memdata.bytes_of_int_append; last first.
 move: (Byte.unsigned_range b).
 rewrite /Byte.modulus /= /two_power_pos /shift_pos /Byte.wordsize
         /Wordsize_8.wordsize /two_power_nat /shift_nat /=; lia.
by rewrite IH //= Byte.repr_unsigned.
Qed.

(*
Lemma match_bytes_int8 b0:
   match_bytes [:: Byte b0]
               (bytes_of_int8 (Int.repr (decode_int [:: b0]))).
Proof.
rewrite decode_int_of_bytes /bytes_of_int8 Int.unsigned_repr; last first.
 move: (int_of_bytes_range [:: b0]). 
 rewrite (lock int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
rewrite bytes_of_int_of_bytes //.
by apply: (match_bytes_map_Byte [:: _]).
Qed.
*)

Lemma bytes_of_int8_decode_int bs:
 size bs = 1 ->
 bytes_of_int8 (Int.repr (Memdata.decode_int bs)) = bs.
Proof.
move: bs=> [| b0 [| ? ?]] //= _.
rewrite decode_int_of_bytes /bytes_of_int8 Int.unsigned_repr; last first.
 move: (Memdata.int_of_bytes_range [:: b0]). 
 rewrite (lock Memdata.int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
by rewrite bytes_of_int_of_bytes.
Qed.

Lemma bytes_of_int16_decode_int bs:
 size bs = 2 ->
 bytes_of_int16 (Int.repr (Memdata.decode_int bs)) = bs.
Proof.
move: bs=> [| b0 [| b1 [|? ?]]] //= _.
rewrite decode_int_of_bytes /bytes_of_int16 Int.unsigned_repr; last first.
 move: (Memdata.int_of_bytes_range [:: b0; b1]). 
 rewrite (lock Memdata.int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
by rewrite bytes_of_int_of_bytes.
Qed.

Lemma bytes_of_int32_decode_int bs:
 size bs = 4 ->
 bytes_of_int32 (Int.repr (Memdata.decode_int bs)) = bs.
Proof.
move: bs=> [| b0 [| b1 [| b2 [| b3 [|? ?]]]]] //= _.
rewrite decode_int_of_bytes /bytes_of_int32 Int.unsigned_repr; last first.
 move: (Memdata.int_of_bytes_range [:: b0; b1; b2; b3]). 
 rewrite (lock Memdata.int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
by rewrite bytes_of_int_of_bytes.
Qed.

Lemma bytes_of_int64_decode_int bs:
 size bs = 8 ->
 bytes_of_int64 (Int64.repr (Memdata.decode_int bs)) = bs.
Proof.
move: bs=> [|b0 [|b1 [|b2 [|b3 [|b4 [|b5 [|b6 [|b7 [|? ?]]]]]]]]] //= _.
rewrite /bytes_of_int64 decode_int_of_bytes /bytes_of_int64 Int64.unsigned_repr; last first.
 move: (Memdata.int_of_bytes_range [:: b0; b1; b2; b3; b4; b5; b6; b7]).
 rewrite (lock Memdata.int_of_bytes) /= /two_power_pos /shift_pos /Int64.max_unsigned //= ; lia.
by rewrite !bytes_of_int_of_bytes.
Qed.

(*
Lemma decode_val_Mint32 mbs i:
  size mbs = 4 ->
  byte_shape_md mbs ->
  decode_val AST.Mint32 mbs = Values.Vint i -> 
  mbs = map Byte (bytes_of_int32 i).
Proof.
rewrite /decode_val; move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [| ? ?]]]]] // _.
move: mb0 mb1 => [|b0|? ?] // [|b1|? ?] //.
move: mb2 mb3 => [|b2|? ?] // [|b3|? ?] // _.
case E: (proj_bytes _) => //; move: E => [<-]; clear.
move=> [<-].
by rewrite bytes_of_int32_decode_int.
Qed.

Lemma match_bytes_decode_int32 i bs mbs:
  size mbs = 4 ->
  byte_shape_md mbs ->
  Values.Vint i = decode_val Mint32 mbs ->
  match_bytes mbs (bytes_of_int32 i).
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] // _.
move: mb0 mb1 => [|b0|? ?] // [|b1|? ?] //.
move: mb2 mb3 => [|b2|? ?] // [|b3|? ?] // _ /= [<-].
rewrite /decode_val /=; move => [->].
by apply match_bytes_int.
Qed.









Lemma bytes_of_int_of_bytes n bs:
 size bs = n ->
 Memdata.bytes_of_int n (int_of_bytes bs) = bs.
Proof.
elim: bs n => //=.
 by move=> n <-.
move=> b bs IH [|n] [Hsz] //.
rewrite -add1n -plusE -[256%Z]/(two_p (Z.of_nat 1 * 8)).
rewrite bytes_of_int_append; last first.
 move: (Byte.unsigned_range b).
 rewrite /Byte.modulus /= /two_power_pos /shift_pos /Byte.wordsize
         /Wordsize_8.wordsize /two_power_nat /shift_nat /=; lia.
by rewrite IH //= Byte.repr_unsigned.
Qed.

Lemma match_bytes_int8 b0:
   match_bytes [:: Byte b0]
               (bytes_of_int8 (Int.repr (decode_int [:: b0]))).
Proof.
rewrite /decode_int /rev_if_be /Archi.big_endian.
rewrite /bytes_of_int8 Int.unsigned_repr; last first.
 move: (int_of_bytes_range [:: b0]). 
 rewrite (lock int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
rewrite bytes_of_int_of_bytes //.
by constructor.
Qed.

Lemma eq_val_bytes_of_int8 i1 i2:
  Values.Vint (Int.zero_ext 8 i1) = Values.Vint (Int.zero_ext 8 i2) ->
  bytes_of_int8 i1 = bytes_of_int8 i2.
Proof.
rewrite /bytes_of_int8; move=> [E'].
have E: Int.unsigned (Int.zero_ext 8 i1) = Int.unsigned (Int.zero_ext 8 i2).
 by exact E'.
apply encode_int_8_mod; move: (Int.eqmod_zero_ext 8).
rewrite /Int.zwordsize /Int.wordsize /Wordsize_32.wordsize /= => H.
apply: Int.eqmod_trans.
 apply Int.eqmod_sym, H => //.
by rewrite E; apply Int.eqmod_zero_ext.
Qed.

Lemma match_bytes_decode_int8 i bs mbs:
  size mbs = 1 ->
  bytes_of_initdata (Init_int8 i) = Some bs ->
  Values.Vint (Int.zero_ext 8 i) = decode_val Mint8unsigned mbs ->
  match_bytes mbs bs.
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] //= _.
move: mb0 => [|b0|? ?] //= [<-].
move=> /eq_val_bytes_of_int8 ->.
by apply match_bytes_int8.
Qed.

Lemma eq_val_bytes_of_int16 i1 i2:
  Values.Vint (Int.zero_ext 16 i1) = Values.Vint (Int.zero_ext 16 i2) ->
  bytes_of_int16 i1 = bytes_of_int16 i2.
Proof.
rewrite /bytes_of_int16; move=> [E'].
have E: Int.unsigned (Int.zero_ext 16 i1) = Int.unsigned (Int.zero_ext 16 i2).
 by exact E'.
apply encode_int_16_mod; move: (Int.eqmod_zero_ext 16).
rewrite /Int.zwordsize /Int.wordsize /Wordsize_32.wordsize /= => H.
apply: Int.eqmod_trans.
 apply Int.eqmod_sym, H => //.
by rewrite E; apply Int.eqmod_zero_ext.
Qed.


Lemma match_bytes_int16 b0 b1:
   match_bytes [:: Byte b0; Byte b1]
               (bytes_of_int16 (Int.repr (decode_int [:: b0; b1]))).
Proof.
rewrite /decode_int /rev_if_be /Archi.big_endian.
rewrite /bytes_of_int16 Int.unsigned_repr; last first.
 move: (int_of_bytes_range [:: b0; b1]). 
 rewrite (lock int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
rewrite bytes_of_int_of_bytes //.
constructor => //.
by constructor.
Qed.

Lemma match_bytes_int b0 b1 b2 b3:
   match_bytes [:: Byte b0; Byte b1; Byte b2; Byte b3]
               (bytes_of_int (Int.repr (decode_int [:: b0; b1; b2; b3]))).
Proof.
rewrite /decode_int /rev_if_be /Archi.big_endian.
rewrite /bytes_of_int Int.unsigned_repr; last first.
 move: (int_of_bytes_range [:: b0; b1; b2; b3]). 
 rewrite (lock int_of_bytes) /= /two_power_pos /shift_pos /Int.max_unsigned /=; lia.
rewrite bytes_of_int_of_bytes //.
by repeat constructor.
Qed.

Lemma match_bytes_int64 b0 b1 b2 b3 b4 b5 b6 b7:
   match_bytes [:: Byte b0; Byte b1; Byte b2; Byte b3
                 ; Byte b4; Byte b5; Byte b6; Byte b7]
               (bytes_of_int64 (Int64.repr (decode_int [:: b0; b1; b2; b3
                                                         ; b4; b5; b6; b7]))).
Proof.
rewrite /decode_int /rev_if_be /Archi.big_endian.
rewrite /bytes_of_int64 Int64.unsigned_repr; last first.
 move: (int_of_bytes_range [:: b0; b1; b2; b3; b4; b5; b6; b7]). 
 rewrite (lock int_of_bytes) /= /two_power_pos /shift_pos /Int64.max_unsigned /=; lia.
rewrite bytes_of_int_of_bytes //.
by repeat constructor.
Qed.

Lemma match_bytes_decode_int16 i bs mbs:
  size mbs = 2 ->
  bytes_of_initdata (Init_int16 i) = Some bs ->
  Values.Vint (Int.zero_ext 16 i) = decode_val Mint16unsigned mbs ->
  match_bytes mbs bs.
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] //= _.
move: mb0 mb1 => [|b0|? ?] //= [|b1|? ?] //= [<-].
move=> /eq_val_bytes_of_int16 ->.
by apply match_bytes_int16.
Qed.

Fixpoint byte_shape_md (l: seq memval) : bool :=
 if l is x::xs
 then if x is (Fragment _ _ _) then false else byte_shape_md xs
 else true.

Lemma match_bytes_decode_int32 i bs mbs:
  size mbs = 4 ->
  byte_shape_md mbs ->
  bytes_of_initdata (Init_int32 i) = Some bs ->
  Values.Vint i = decode_val Mint32 mbs ->
  match_bytes mbs bs.
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] // _.
move: mb0 mb1 => [|b0|? ?] // [|b1|? ?] //.
move: mb2 mb3 => [|b2|? ?] // [|b3|? ?] // _ /= [<-].
rewrite /decode_val /=; move => [->].
by apply match_bytes_int.
Qed.

Lemma match_bytes_decode_int64 i bs mbs:
  size mbs = 8 ->
  bytes_of_initdata (Init_int64 i) = Some bs ->
  Values.Vlong i = decode_val Mint64 mbs ->
  match_bytes mbs bs.
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] //= _.
move: mb0 mb1 => [|b0|? ?] //= [|b1|? ?] //=.
move: mb2 mb3 => [|b2|? ?] //= [|b3|? ?] //=.
move: mb4 mb5 => [|b4|? ?] //= [|b5|? ?] //=.
move: mb6 mb7 => [|b6|? ?] //= [|b7|? ?] //= [<-].
rewrite /decode_val /=; move => [->].
by apply match_bytes_int64.
Qed.

Lemma match_bytes_decode_float32 f bs mbs:
  size mbs = 4 ->
  bytes_of_initdata (Init_float32 f) = Some bs ->
  Values.Vsingle f = decode_val Mfloat32 mbs ->
  match_bytes mbs bs.
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] //= _.
move: mb0 mb1 => [|b0|? ?] //= [|b1|? ?] //=.
move: mb2 mb3 => [|b2|? ?] //= [|b3|? ?] //= [<-].
rewrite /decode_val /=; move => [->].
rewrite Floats.Float32.to_of_bits.
by apply match_bytes_int.
Qed.

Lemma match_bytes_decode_float64 f bs mbs:
  size mbs = 8 ->
  bytes_of_initdata (Init_float64 f) = Some bs ->
  Values.Vfloat f = decode_val Mfloat64 mbs ->
  match_bytes mbs bs.
Proof.
move: mbs => [|mb0 [|mb1 [|mb2 [|mb3 [|mb4 [|mb5 [|mb6 [|mb7 [|mb8 rest]]]]]]]]] //= _.
move: mb0 mb1 => [|b0|? ?] //= [|b1|? ?] //=.
move: mb2 mb3 => [|b2|? ?] //= [|b3|? ?] //=.
move: mb4 mb5 => [|b4|? ?] //= [|b5|? ?] //=.
move: mb6 mb7 => [|b6|? ?] //= [|b7|? ?] //= [<-].
rewrite /decode_val /=; move => [->].
rewrite Floats.Float.to_of_bits.
by apply match_bytes_int64.
Qed.

Lemma match_bytes_zeros sz:
  match_bytes (nseq (Z.to_nat sz) (Byte Byte.zero))
              (take_dflt Byte.zero (Z.to_nat sz) [::]).
Proof.
rewrite take_dflt_split /= subn0.
elim: (Z.to_nat sz) => //=.
by move=> n IH; constructor.
Qed.

*)