(** BCirc.v - High-level boolean circuits

 High-level boolean circuits are arrays of interconnected buses with
 complex gates (that are themselves built from simpler circuits).
 The general pattern of a circuit is:

 1: INPUT <bus-width>					| INPUT SECTION
 ...							-------
 n: GATE <gate> [ <bus-spec1> ; ... ; <bus-speck> ]	| GATE SECTION
 ...							-------
 m: OUTPUT [ <bus-spec1> ; ... ; <bus-specl> ]		| OUPUT SECTION
 ...

Each gate has a fixed arity (number of input/output wires). Hence, in a
gate specification line

 n: GATE <gate> [ <input-wires> ]

the concatenation of all input-wire buses should match the in-arity of the
gate. Accordingly, <n> will act as a bus-identifier with out-arity bits.
A single bus is specified as a tuple

 (<bus-id>, <position-bit>)

where <bus-id> is expected to be a bus occuring before the current gate. A
special entry with <bus-id>=0 is used to denote truth values

 (0,0) - False
 (0,1) - True


REMARK: for the sake of simplicity, sizes are not enforced in the definition
of circuits. Sensible default actions are prescribed to deal with possible
mismatches.
*)
Require Import Utf8.
Require Import AST.
Require Import Events.
Require Import Memory.
Require Import Globalenvs.
Require Import Smallstep.

Require Import ZArith NArith Psatz.
Require ExtraLib.
Require Import CircIO ORbdt OpGates.
Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.
Require Import ssrlib ssrValues seqN bits.

Import Integers.

Unset Elimination Schemes.


Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Open Scope N_scope.


Section CircuitWires.

(* [grid] stores bit-values for the circuit wires*)

Definition grid := seq bits.

Definition is_grid g := seq.head nil g = false::true::nil.

Lemma is_grid_cat g s:
  is_grid g -> is_grid (g++s).
Proof. by move: g => [|x xs]. Qed.


Definition gate_number := N.

(** Wire := (entryNum * pos) *)
Definition wire := (N*N)%type.
Definition wire_FF := (0,0)%num.
Definition wire_TT := (0,1)%num.

Definition wires_of_type (ty: typ) : N := 8*N_of_Z (typesize ty).

Definition wires_of_oty (oty: option typ) : N :=
  match oty with None => 1 | Some ty => wires_of_type ty end.

Definition wire_eval (indata: grid) (w:wire) : option bool :=
 onthN (nthN [::] indata (w.1)) w.2.

Lemma wire_eval_lt g w n b :
  wire_eval g (w, n) = Some b →
  w < sizeN g.
Proof.
rewrite /wire_eval /= (onthN_isS false) !sizeN_size !nthN_nth.
rewrite -{1}[g]cats0 nth_cat; move => /= [H _].
rewrite N2n_lt n2N2n; move: H; case: (ifP _) => //.
by rewrite nth_nil /= N2n_lt => _.
Qed.

Lemma wire_eval_catl g1 g2 w:
 w.1 < sizeN g1 ->
 wire_eval (g1++g2) w = wire_eval g1 w.
Proof.
move=> Hsize; rewrite /wire_eval !nthN_nth nth_cat.
case: (ifP _) => //.
move=> /negP H; elim: H.
by rewrite size_sizeN -N2n_lt.
Qed.

Lemma wire_eval_catr g1 g2 w:
 sizeN g1 <= w.1 ->
 wire_eval (g1++g2) w = wire_eval g2 (w.1 - sizeN g1, w.2).
Proof.
move=> Hsize; rewrite /wire_eval !nthN_nth nth_cat.
case: (ifP _).
 move: Hsize; rewrite sizeN_size N2n_le n2N2n => /leP H1 /leP H2.
 omega.
move=> _.
by rewrite N2Nat.inj_sub sizeN_size n2N2n minusE.
Qed.

Lemma wire_eval_rcons g v w b :
  wire_eval g w = Some b →
  wire_eval (rcons g v) w = wire_eval g w.
Proof. move=> /wire_eval_lt H; by rewrite -cats1 wire_eval_catl. Qed.

Lemma wire_eval_input x y y' z c b :
  wire_eval (x ++ y :: z) c = Some b →
  wire_eval (x ++ (y ++ y') :: z) c = Some b.
Proof.
  unfold wire_eval; rewrite ! nthN_cat.
  case N.ltb. exact id.
  simpl. case (_ - _). 2: easy. apply onthN_isS_cat.
Qed.

End CircuitWires.





Section Connector.

Definition connector := seq wire.

Definition conn_size (conn: connector) : N := sizeN conn.

Definition conn_eval (indata: grid) (c: connector) : option bits :=
 omap_all (wire_eval indata) c.


Lemma conn_eval_isS_sizeN g c v:
  conn_eval g c = Some v -> sizeN c = sizeN v.
Proof.
rewrite /conn_eval omap_all_isS => /(f_equal sizeN).
by rewrite !sizeN_size !size_map.
Qed.

Lemma conn_eval_lt g c v w:
  conn_eval g c = Some v →
  w \in c -> w.1 < sizeN g.
Proof.
rewrite /conn_eval omap_all_isS => H Hw.
have: wire_eval g w \in [seq wire_eval g i | i <- c] by apply map_f.
by rewrite H => /mapP [_ _ /wire_eval_lt HH].
Qed.

Lemma conn_eval_cat g c v c' v' :
  conn_eval g c = Some v →
  conn_eval g c' = Some v' →
  conn_eval g (c ++ c') = Some (v ++ v').
Proof. by rewrite /conn_eval !omap_all_oseq map_cat; apply oseq_isS_cat. Qed.

Lemma conn_eval_catl g c v c' v' :
  sizeN c = sizeN v →
  conn_eval g (c ++ c') = Some (v ++ v') →
  conn_eval g c = Some v.
Proof. 
rewrite /conn_eval !omap_all_oseq => Hsize /oseq_isS.
rewrite !map_cat => /eqP; rewrite eqseq_cat; last first.
 by rewrite !size_map !size_sizeN Hsize.
move => /andP [/eqP -> _].
by rewrite oseq_isS.
Qed.

Lemma conn_eval_catr g c v c' v' :
  sizeN c' = sizeN v' →
  conn_eval g (c ++ c') = Some (v ++ v') →
  conn_eval g c' = Some v'.
Proof.
move=> Hsize H; move: (conn_eval_isS_sizeN H).
move: Hsize H; rewrite !sizeN_size !size_cat !Nat2N.inj_add.
rewrite /conn_eval !omap_all_oseq => Hsize /oseq_isS H E.
move: H; rewrite !map_cat => /eqP; rewrite eqseq_cat; last first.
 by rewrite !size_map; apply Nat2N.inj; lia.
move => /andP [_ /eqP ->].
by rewrite oseq_isS.
Qed.

Lemma conn_eval_dropN g c n v:
  conn_eval g c = Some v ->
  conn_eval g (dropN n c) = Some (dropN n v).
Proof.
move=> H; move: (conn_eval_isS_sizeN H);move: H.
rewrite !dropN_drop !sizeN_size.
rewrite -{1}[c](cat_take_drop (N2n n)).
rewrite -{1}[v](cat_take_drop (N2n n)).
move=> H Hsize ; apply (@conn_eval_catr _ (take (N2n n) c) (take (N2n n) v)).
 by rewrite !sizeN_size !size_drop !Nat2N.inj_sub Hsize.
apply H.
Qed.

Lemma conn_eval_takeN g c n v:
  conn_eval g c = Some v ->
  conn_eval g (takeN n c) = Some (takeN n v).
Proof.
move=> H; move: (conn_eval_isS_sizeN H);move: H.
rewrite !takeN_take !sizeN_size.
rewrite -{1}[c](cat_take_drop (N2n n)).
rewrite -{1}[v](cat_take_drop (N2n n)).
move=> H Hsize; apply (@conn_eval_catl _ _ _ (drop (N2n n) c) (drop (N2n n) v)).
 by rewrite !sizeN_size !size_take (Nat2N.inj _ _ Hsize).
apply H.
Qed.

Lemma conn_eval_nseqN g n:
  is_grid g -> 
  conn_eval g (nseqN n wire_FF) = Some (nseqN n false).
Proof.
move=> Hgrid; rewrite !nseqN_nseq /conn_eval omap_all_isS.
rewrite !map_nseq /=; f_equal.
by rewrite nthN_nth nth0 Hgrid.
Qed.

Lemma conn_eval_takeN_dflt g c n v:
  is_grid g ->
  conn_eval g c = Some v ->
  conn_eval g (takeN_dflt wire_FF n c) = Some (takeN_dflt false n v).
Proof.
move=> Hgrid H; move: (conn_eval_isS_sizeN H);move: H.
move=> H; rewrite !takeN_take_dflt !take_dflt_split => Hsize.
apply conn_eval_cat.
 by rewrite -!takeN_take; apply conn_eval_takeN.
rewrite !size_sizeN -minusE -!N2Nat.inj_sub Hsize -!nseqN_nseq.
by apply conn_eval_nseqN.
Qed.

Lemma conn_eval_isS_sub g c v width pos:
  conn_eval g c = Some v ->
  is_grid g ->
  conn_eval g (takeN_dflt wire_FF width (dropN pos c))
  = Some (takeN_dflt false width (dropN pos v)).
Proof.
move => Hev Hgrid.
apply conn_eval_takeN_dflt => //.
by apply conn_eval_dropN.
Qed.

Definition conn_shft n (c:connector) := [seq (n+i.1,i.2) | i <- c].

Lemma conn_eval_rcons g c b v :
  conn_eval g c = Some b →
  conn_eval (rcons g v) c = Some b.
Proof.
move => HH; move: (HH).
rewrite /conn_eval !omap_all_oseq -cats1 => H.
have ->: [seq wire_eval (g ++ [:: v]) i | i <- c]
         = [seq wire_eval g i | i <- c].
 apply eq_in_map => x Hx; rewrite wire_eval_catl //.
 by apply (@conn_eval_lt _ c b x).
by [].
Qed.

Lemma conn_eval_input x y y' z c b :
  conn_eval (x ++ y :: z) c = Some b →
  conn_eval (x ++ (y ++ y') :: z) c = Some b.
Proof.
  intros H. apply omap_all_isS in H. apply omap_all_isS. rewrite <- H.
  revert b H. elim c; clear.
  exact (λ _ _, Logic.eq_refl).
  intros w c IH b H. simpl in H. apply ExtraLib.map_eq_cons in H. destruct H as (b' & bs & -> & Hb & REC).
  apply (f_equal2 cons). 2: eapply IH, REC.
  rewrite Hb; eauto using wire_eval_input.
Qed.

Corollary conn_eval_input' x y y' z c b :
  conn_eval (x :: y :: z) c = Some b →
  conn_eval (x :: (y ++ y') :: z) c = Some b.
Proof.
  exact (@conn_eval_input (x :: nil) y y' z c b).
Qed.




Definition conn_new (gate init size: N) : connector :=
 map (fun wire=> (gate, wire)) (iotaN init size).

Lemma sizeN_conn_new g init size:
  sizeN (conn_new g init size) = size.
Proof.
by rewrite /conn_new sizeN_size iotaN_iota !size_map size_iota N2n2N.
Qed.

(** [conn_ty] and [conn_chunk] returns the connector holding 
 the result of a given gate or memory chunk                          *)
Definition conn_ty (ty: typ) (gn: gate_number) : connector :=
 conn_new gn 0 (wires_of_type ty).

Lemma sizeN_conn_ty ty gn :
  sizeN (conn_ty ty gn) = wires_of_type ty.
Proof.
  unfold conn_ty, conn_new.
  rewrite sizeN_map.
  apply sizeN_iotaN.
Qed.


Definition conn_zero_ext (size: N) (conn: connector) : connector :=
  takeN_dflt wire_FF size conn.

Definition conn_sign_ext n := sign_extN' n wire_FF.

Definition signed_chunk (ϰ: memory_chunk) :
  { ϰ = Mint8signed ∨ ϰ = Mint16signed } +
  { ϰ ≠ Mint8signed ∧ ϰ ≠ Mint16signed }.
Proof.
  destruct ϰ; try (left; auto; fail);
  right; abstract (intuition congruence).
Defined.

Definition sizeN_chunk chunk := N_of_Z (Memdata.size_chunk chunk).

(* [chunk_ext] performs the appropriate sign extension for [decode_val] *)
Definition chunk_ext {A} ϰ (dflt:A) :=
  if signed_chunk ϰ
  then sign_extN' (wires_of_type (type_of_chunk ϰ)) dflt
  else takeN_dflt dflt (wires_of_type (type_of_chunk ϰ)).

(** adjusts the size of a connector (fills with FALSE wire)
Definition conn_sizeadj (size: N) : connector -> connector :=
 takeN_dflt wire_FF size.
*)

Definition conn_upd_at {A} orig pos (new: seq A) :=
 updprefAtN pos orig new.

Lemma sizeN_conn_upd_at {A} orig pos (new: seq A):
  sizeN (conn_upd_at orig pos new) = sizeN orig.
Proof. by rewrite /conn_upd_at sizeN_updprefAtN. Qed.

(*
Lemma conn_upd_at_nil: forall A (new: seq A) pos,
 conn_upd_at [::] pos new = [::].
Proof. 
by move=> A [|x xs] pos; rewrite /conn_upd_at takeN_nil dropN_nil /=.
Qed.

Lemma conn_upd_at_size: forall A (orig new: seq A) pos,
 size (conn_upd_at orig pos new) = size orig.
Proof.
move=> A; rewrite /conn_upd_at; elim => //=.
 by move=> [|x xs] [|pos]; rewrite takeN_nil dropN_nil conn_upd_nil.
move=> x xs IH [|y ys] [|pos] => //.
  by rewrite takeN_cons dropN_pos_cons cat_cons [size _] /= IH.
 by rewrite takeN_0 dropN_0 //= conn_upd_size.
by rewrite takeN_cons dropN_pos_cons cat_cons [size _] /= IH.
Qed.
*)

Definition conn_sub (pos size: N) (c: connector) : connector :=
 takeN_dflt wire_FF size (dropN pos c).

Lemma conn_eval_conn_new g n sz :
  sz <= sizeN (nthN nil g n) →
  conn_eval g (conn_new n 0 sz) = Some (takeN sz (nthN nil g n)).
Proof.
move=> Hsize; rewrite /conn_eval /wire_eval /conn_new.
rewrite omap_all_map omap_all_oseq oseq_isS. 
rewrite (takeN_map_nthN false) //.
rewrite -map_comp /=.
apply eq_in_map => x /=.
rewrite mem_iotaN => HH.
rewrite onthN_isS; split; last by reflexivity.
lia.
Qed.

Lemma conn_eval_zero_ext g n c :
  head [::] g = [:: false; true] →
  sizeN c <= n →
  conn_eval g (conn_zero_ext n c) = omap (takeN_dflt false n) (conn_eval g c).
Proof.
move=> Hgrid Hsize; rewrite /conn_zero_ext.
rewrite /conn_eval !omap_all_oseq.
case E: (oseq [seq wire_eval g i | i <- c]) => [x|] /=; last first.
 by rewrite takeN_dflt_split // map_cat ; apply oseq_isN_catl.
have x_size: size x = size c.
 by move: E; rewrite oseq_isS -(size_map Some) => <-; apply size_map.
have x_sizeN: sizeN x = sizeN c.
 by apply N2Nat.inj; rewrite !sizeN_size !n2N2n.
rewrite /= oseq_isS !takeN_dflt_split ?x_sizeN // !map_cat.
apply/eqP; rewrite eqseq_cat; last by rewrite !size_map.
apply/andP; split; first by apply/eqP; rewrite -oseq_isS.
apply/eqP.
by rewrite !map_nseqN nthN_nth nth0 Hgrid.
Qed.

Lemma conn_eval_sign_ext g n c :
  head [::] g = [:: false; true] →
  sizeN c <= n ->
  conn_eval g (conn_sign_ext n c) = omap (sign_extN' n false) (conn_eval g c).
Proof.
move=> Hgrid Hsize.
rewrite /conn_sign_ext /conn_eval !omap_all_oseq.
case E: (oseq [seq wire_eval g i | i <- c]) => [x|] /=; last first.
 by rewrite sign_extN_split // map_cat; apply oseq_isN_catl.
have x_size: size x = size c.
 by move: E; rewrite oseq_isS -(size_map Some) => <-; apply size_map.
have x_sizeN: sizeN x = sizeN c.
 by apply N2Nat.inj; rewrite !sizeN_size !n2N2n.
move: E; rewrite !oseq_isS => E.
rewrite !sign_extN_split //; last first. 
 by rewrite sizeN_size x_size -sizeN_size.
rewrite map_cat // !map_cat.
rewrite E; f_equal. rewrite !map_nseqN. f_equal; f_equal.
  by rewrite !sizeN_size x_size. 
rewrite (onthN_isS false) /wire_FF /=.
have Efalse: wire_eval g (0,0) = Some false.
 by rewrite /wire_eval nthN_nth nth0 Hgrid. 
have HH: wire_eval g (last (0,0) c) = Some (last false x).
 by rewrite -last_map E Efalse -[Some (last false x)]last_map; f_equal.
by move: HH; rewrite /wire_eval (onthN_isS false); move => [H1 H2]; split.
Qed.

Lemma conn_eval_conn_ext ϰ g c :
  head [::] g = [:: false; true] →
  sizeN c <= wires_of_type (type_of_chunk ϰ) →
  conn_eval g (chunk_ext ϰ wire_FF c) =
  omap (chunk_ext ϰ false) (conn_eval g c).
Proof.
move=> Hgrid Hsize; rewrite /chunk_ext.
case: (signed_chunk _) => _ /=.
 by apply conn_eval_sign_ext.
by apply conn_eval_zero_ext.
Qed.

Lemma conn_eval_updpref g orig new bs1 bs2:
  conn_eval g orig = Some bs1 ->
  conn_eval g new = Some bs2 ->
  conn_eval g (updpref orig new) = Some (updpref bs1 bs2).
Proof.
move=> H1 H2; 
rewrite !updprefE !take_takeN !drop_dropN -!sizeN_size
        (conn_eval_isS_sizeN H1) (conn_eval_isS_sizeN H2).
apply conn_eval_cat.
 by apply conn_eval_takeN.
by apply conn_eval_dropN.
Qed.

Lemma conn_eval_conn_upd_at g n orig new bs1 bs2:
  conn_eval g orig = Some bs1 ->
  conn_eval g new = Some bs2 ->
  conn_eval g (conn_upd_at orig n new) = Some (updprefAtN n bs1 bs2).
Proof.
move=> H1 H2.
rewrite /conn_upd_at !updprefAtN_E.
apply conn_eval_cat.
 by apply conn_eval_takeN.
apply conn_eval_updpref => //.
by apply conn_eval_dropN.
Qed.

End Connector.


Section ReadWire.

Definition read_wire (g: grid) (oty: option typ) (gn: gate_number)
  : option bits :=
  conn_eval g match oty with 
              | None => (gn, 0) :: nil
              | Some ty => conn_ty ty gn
              end.

Lemma sizeN_read_wire g oty w v :
  read_wire g oty w = Some v -> sizeN v = wires_of_oty oty.
Proof.
move: oty => [ty|]; rewrite /read_wire => H; rewrite -(conn_eval_isS_sizeN H) //.
by rewrite sizeN_conn_ty.
Qed.

Lemma read_wire_lt g oty gn v :
  read_wire g oty gn = Some v →
  gn < sizeN g.
Proof.
rewrite /read_wire /conn_eval omap_all_isS eqseq_onth => H.
move: v {H}(H 0) => [|v vs] /=.
 by move: oty => [[|||||]|]; discriminate.
rewrite (@onth_isS _ (Some v)) size_map; move=> [_].
by move: oty => [[|||||]|] => /=; apply wire_eval_lt.
Qed.

Lemma read_wire_first ty v g :
  wires_of_type ty = sizeN v →
  read_wire (v :: g) (Some ty) 0 = Some v.
Proof.
move=> Hsize; rewrite /read_wire /conn_ty Hsize conn_eval_conn_new /=; 
 last by reflexivity.
f_equal; apply takeN_all; reflexivity.
Qed.


Lemma read_wire_catr g1 g2 oty n:
  read_wire (g1++g2) oty (sizeN g1 + n) = read_wire g2 oty n.
Proof.
move: oty => [ty|]; rewrite /read_wire /conn_eval !omap_all_oseq; f_equal.
 transitivity
   [seq wire_eval (g1++g2) i | i <- conn_shft (sizeN g1) (conn_ty ty n)].
  by rewrite /conn_shft -!map_comp /=; apply eq_map => x.
 rewrite -map_comp; apply eq_map => x /=.
 rewrite wire_eval_catr /=; f_equal.
  rewrite [x]surjective_pairing; f_equal; simpl.
  lia. 
 lia.
transitivity
  [seq wire_eval (g1 ++ g2) i | i <- conn_shft (sizeN g1) [:: (n,0)]].
 by rewrite /conn_shft -!map_comp /=.
rewrite -map_comp; apply eq_map => x /=.
rewrite wire_eval_catr /=; f_equal.
 rewrite [x]surjective_pairing; f_equal; simpl.
 lia. 
lia.
Qed.

Lemma read_wire_catl g1 g2 oty n:
  n < sizeN g1 ->
  read_wire (g1++g2) oty n = read_wire g1 oty n.
Proof.
move: oty => [ty|] Hsize;
rewrite /read_wire /conn_eval !omap_all_oseq; f_equal;
apply eq_in_map => w Hw; rewrite wire_eval_catl //.
 have ->: w.1 = n.
  by move: Hw; rewrite /conn_ty /conn_new => /mapP [y [_ ->]].
 by [].
by move: Hw; rewrite in_cons => /orP [/eqP ->|H].
Qed.

Lemma read_wire_last g v oty:
  read_wire (rcons g v) oty (sizeN g) = read_wire (v :: nil) oty 0.
Proof. by rewrite -cats1 -[sizeN g]N.add_0_r read_wire_catr. Qed.

Lemma read_wire_rcons g v oty n :
  n < sizeN g →
  read_wire (rcons g v) oty n = read_wire g oty n.
Proof. by move=> H; rewrite -cats1 read_wire_catl. Qed.



End ReadWire.





(* Construction of the initial memory (global variables) *)


Definition bytes_of_initdata (initd: AST.init_data) : option bytes :=
 match initd with
 | Init_int8 i => Some (bytes_of_int8 i)
 | Init_int16 i => Some (bytes_of_int16 i)
 | Init_int32 i => Some (bytes_of_int32 i)
 | Init_int64 i => Some (bytes_of_int64 i)
 | Init_float32 f => Some (bytes_of_int32 (Floats.Float32.to_bits f))
 | Init_float64 f => Some (bytes_of_int64 (Floats.Float.to_bits f))
 | Init_space size => Some (takeN_dflt Byte.zero (N_of_Z size) [::])
 | _ => None
 end.

Fixpoint bytes_of_initdata_list (initd: seq AST.init_data)
 : option bytes :=
 if initd is x::xs
 then obind (fun xbits => obind (fun xsbits => Some (xbits++xsbits)) 
                                (bytes_of_initdata_list xs))
            (bytes_of_initdata x)
 else Some [::].

Definition initmem_of_globvar {V} (v: globvar V) : option bytes :=
 bytes_of_initdata_list v.(gvar_init).

Definition N_of_int x : N := N_of_Z (Int.unsigned x).

Definition initmem_stack (stacksize: int) : bytes :=
 takeN_dflt Byte.zero (N_of_int stacksize) [::].

(** [collect_globals] extract all global variables from the environment.
 It discharge volatile global variables (as their use would disturb the
 execution trace), and returns a bytelevel encoding of the initialization
 data.
 Note that [collect_globals] keep data for identifiers that are not
 handled (function symbols or volatile globals), in order to hide
 names correctly.
 It enforces that no global requires more than 2³² bytes.
 *)
Fixpoint collect_globals F V acc (gdefs: seq (ident*globdef F V))
 : option (seq (ident*option bytes)) :=
 if gdefs is x::xs
 then if x.2 is Gvar gv
      then if gvar_volatile gv
           then collect_globals ((x.1,None)::acc) xs
           else if initmem_of_globvar gv is Some vinit
                then if (Genv.init_data_list_size (gvar_init gv)
                         <=? Int.max_unsigned)%Z
                     then collect_globals ((x.1, Some vinit) :: acc) xs
                     else None
                else None
      else collect_globals ((x.1,None)::acc) xs
 else Some acc.

(** [initmem_globs] constructs the (bytelevel) initial memory of the
 program. *)
Definition globs_initdata (globs: seq (ident*option bytes)) :=
 map [fun x=>if x.2 is Some vini then vini else [::]]
     (filter [fun x=> x.2 != None] globs).

Definition initmem_globs {F V} (p:program F V) 
 : option (seq bytes) :=
 if collect_globals nil p.(prog_defs) is Some globs
 then Some (globs_initdata globs)
 else None.

(* Semantics *)



Record gentry := { gate: gateID
                 ; conn: connector
                 }.

Section GateEvaluation.
(* * Gate Evaluation
   To evaluate a circuit we need to provide a characterization of
 each GateID. This is established by a mapping    *)



(** a gate is evaluated in a given
    - [guard], which is always the first bit of input
    - [wire_model], which stores the contents of (already computed) wires
*)
Definition gate_eval gInfo wire_model conn : option bits :=
 omap (fun indata => takeN_dflt false gInfo.(gate_out_arity)
                                       (gInfo.(gate_ev) indata))
       (conn_eval wire_model conn).

End GateEvaluation.


(** * High-level Boolean Circuits 

 Remark: we discriminate in [initconsts] the initial memory of stack
 and global variables (including inputs). Of course, one can easily
 generate gates for these, but it will complicate the argument that relates
 the initial memory in both semantics.
*)
Record circuit := { inputs: N	(* number of input wires *)
                  ; initconsts: seq (seq byte)
                  ; gates: seq gentry
                  ; outputs: connector (* output wires *)
                  }.

Definition memfree_circuit (c: circuit) : bool :=
 if c.(initconsts) is [::] then true else false.

Definition nOutputs (circ:circuit) : N :=
 8 * (sizeN (outputs circ)).

(* Still, for Compcert we retain the name of inputs (to construct the
 initial memory) *)
Record function: Type := mkfunction {
  fn_inputs: seq (CircIO.slot*ident); (* (globalV, offset (bytes)),vol.var. *)
  fn_outputs: seq ident; (* vol.vars *)
  fn_stacksize: int;
  fn_code: circuit
}.

Definition memfree_function (f: function) : bool :=
 (Int.eq f.(fn_stacksize) Int.zero) && memfree_circuit f.(fn_code).

Definition fundef := AST.fundef function.

Definition program := AST.program fundef unit.

(** * Operational semantics *)

Definition genv := Genv.t fundef unit.

Inductive state : Type :=
| InitState `(function)
            `(seq (seq byte))		(**r globvar init. data *)
| InputState
        `(option Values.val)	(**r input value *)
        `(seq ident)	(**r input locations *)
        `(bits)		(**r input bits *)
        `(seq (seq byte))		(**r globvar init. data *)
        `(seq gentry)	(**r gates *)
        `(seq ident)	(**r outputs (volatile vars) *)
        `(connector)	(**r output wires *)
| InputFenceState `(bool)
        `(bits)		(**r input bits *)
        `(seq (seq byte))		(**r globvar init. data *)
        `(seq gentry)	(**r gates *)
        `(seq ident)	(**r outputs (volatile vars) *)
        `(connector)	(**r output wires *)
| State `(seq gentry)		(**r gates *)
        `(seq ident)		(**r outputs (volatile vars) *)
        `(connector)		(**r output wires *)
        `(grid)			(**r values (bits) on wires *)
| OutputFenceState `(bool)
        `(seq ident)		(**r outputs (volatile vars) *)
        `(connector)		(**r output wires *)
        `(grid)			(**r values (bits) on wires *)
| OutputState `(option (Values.val * ident))	(**r output value *)
        `(seq ident)		(**r outputs (volatile vars) *)
        `(connector)		(**r output wires *)
        `(grid)			(**r values (bits) on wires *)
| FinishingState
| FinalState.

(** [grid_of_globconsts] constructs the initial [grid] (wire values)
  from global constant initialization data *)
Definition grid_of_globconsts (globinit: seq (seq byte)) : seq bits :=
 map bits_of_bytes globinit.

Section RELSEM.

Variable ge: genv.

Definition input_event varname (ev: event) (ibyte: int) : Prop :=
 exists varoff eval v,
   ev = Event_vload Mint8unsigned varname varoff eval /\
   eventval_match ge eval Tint v /\
   Values.Vint ibyte = Values.Val.load_result Mint8unsigned v.

Definition output_event varname (ev: event) (obyte: int) : Prop :=
 exists varoff eval v,
   ev = Event_vstore Mint8unsigned varname varoff eval /\
   eventval_match ge eval Tint v /\
   Values.Vint obyte = v.

Definition fill_grid (inbits: bits) (globs: _) : grid :=
  [:: false; true] :: inbits :: grid_of_globconsts globs.

Definition byte_of_input_val (x:Values.val) : byte :=
 match x with
   Values.Vint i => Byte.repr (Int.unsigned i)
 | _ => Byte.zero
 end.

Definition step (s1: state) (tr: trace) (s2: state) : Prop :=
 match s1 with
 | InitState f globmem =>
   tr = E0 ∧
   f.(fn_code).(initconsts) = initmem_stack f.(fn_stacksize) :: globmem ∧
   8 * sizeN f.(fn_inputs) = f.(fn_code).(inputs) ∧
   8 * sizeN f.(fn_outputs) = sizeN f.(fn_code).(outputs) ∧
   s2 = InputState None (map snd (fn_inputs f)) nil
                   f.(fn_code).(initconsts) f.(fn_code).(gates) f.(fn_outputs) f.(fn_code).(outputs)
 | InputState None (src :: ins) inp globs body outs oc =>
   ∃ b ev v,
   Senv.block_is_volatile ge b = true ∧
   Senv.find_symbol ge src = Some b ∧
   tr = Event_vload Mint8unsigned src Int.zero ev :: nil ∧
   eventval_valid ge ev ∧
   eventval_match ge ev Tint v ∧
  s2 = InputState (Some (Values.Val.load_result Mint8unsigned v)) ins inp globs body outs oc
| InputState (Some v) ins inp globs body outs oc =>
  tr = E0 ∧
  s2 = InputState None ins (inp ++ bits_of_byte (byte_of_input_val v)) globs body outs oc
| InputState None nil inp globs body outs oc =>
  tr = E0 ∧
  s2 = InputFenceState false inp globs body outs oc
| InputFenceState false inp globs body outs oc =>
  tr = E0 ∧
  s2 = InputFenceState true inp globs body outs oc
| InputFenceState true inp globs body outs oc =>
  tr = E0 ∧
  s2 = State body outs oc (fill_grid inp globs)
| State (entry :: circ) outs oc wires =>
  tr = E0 ∧
  let ginfo := gateInfo entry.(gate) in
  ∃ xbits,
    gate_eval ginfo wires entry.(conn) = Some xbits ∧
    s2 = State circ outs oc (rcons wires xbits)
| State nil outs oc wires =>
  tr = E0 ∧
  s2 = OutputFenceState false outs oc wires
| OutputFenceState false outs oc wires =>
  tr = E0 ∧
  s2 = OutputFenceState true outs oc wires
| OutputFenceState true outs oc wires =>
  tr = E0 ∧
  s2 = OutputState None outs oc wires
| OutputState None (dst :: outs) oc wires =>
  tr = E0 ∧
  ∃ obyte oc' xbits,
    oc = obyte ++ oc' ∧
    conn_size obyte = 8 ∧
    conn_eval wires obyte = Some xbits ∧
    s2 = OutputState (Some (Values.Vint (int32_of_bits xbits), dst)) outs oc' wires
| OutputState (Some (v, dst)) outs oc wires =>
  ∃ b ev,
   Senv.block_is_volatile ge b = true ∧
   Senv.find_symbol ge dst = Some b ∧
   tr = Event_vstore Mint8unsigned dst Int.zero ev :: nil ∧
   eventval_match ge ev Tint v ∧
  s2 = OutputState None outs oc wires
| OutputState None nil oc wires =>
  tr = E0 ∧
  s2 = FinishingState
| FinishingState =>
  tr = E0 ∧
  s2 = FinalState
| FinalState => False
end.

End RELSEM.


Definition initial_state (p: program) (s: state) : Prop :=
  let ge := Genv.globalenv p in
  ∃ b f globmem,
      Genv.find_symbol ge p.(prog_main) = Some b ∧
      Genv.find_funct_ptr ge b = Some (Internal f) ∧
      initmem_globs p = Some globmem ∧
      s = InitState f globmem.

Definition final_state (st: state) (res: int) : Prop :=
  res = Int.zero ∧ st = FinalState.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).


Lemma semantics_determinate p :
  determinate (semantics p).
Proof.
split; try apply semantics_receptive;
  intros (); simpl; intros;
    repeat match goal with
           | H : False |- _ => destruct H
           | H : ?a = ?b |- _ => subst a || subst b
           | H : _ /\ _ |- _ => let K := fresh H in destruct H as [ H K ]
           | H : _ :: _ = _ :: _ |- _ => inversion H; clear H
           | H : exists a, _ |- _ => let b := fresh a in destruct H as [ b H ]
           | H : let (u, v) := ?a in _ |- _ => destruct a
           | H : match ?a with _ => _ end |- _ => destruct a
           | H : ?a = Some _, K : ?a = Some _ |- _ => rewrite H in K; inversion K; clear K
           | H : initial_state _ _ |- _ => unfold initial_state in H
           | H : final_state _ _ |- _ => unfold final_state in H
           | H : _ = FinalState |- _ => inversion H; clear H
           | H : eventval_match _ _ _ _, K: eventval_match _ _ _ _ |- _ =>
             generalize (eventval_match_determ_1 H K); clear H K;
               intro
           | H : eventval_match _ _ _ _, K: eventval_match _ _ _ _ |- _ =>
             generalize (eventval_match_determ_2 H K); clear H K;
               intro
           | |- nostep _ _ _ => intros ? (); intros
           | H : external_call _ _ _ _ _ _ _, K : external_call _ _ _ _ _ _ _ |- _ =>
             generalize (external_call_determ _ _ _ _ _ _ _ _ _ _ H K); clear H K;
               intros [H K]
           | |- _ ∧ _ => split
           | |- _ → _ => intro
           | H : ?a = ?a → _ |- _ => specialize (H Logic.eq_refl)
           end; eauto using match_traces_E0.
constructor; eauto using eventval_match_same_type.
constructor.
move/eqP: H2 H3; rewrite eqseq_cat.
move=> /andP [/eqP -> /eqP ->].
by rewrite H5 => [[->]].
move: H4 H1; rewrite /conn_size.
move=> /(f_equal N.to_nat); rewrite sizeN_size Nat2N.id => H1.
by move=> /(f_equal N.to_nat); rewrite sizeN_size Nat2N.id -H1.
Qed.
