Require Import ZArith NArith.
Require Import Integers Op.

Require Import ssreflect ssrfun ssrbool ssrnat seq eqtype.

Require Import ORbdt ssrlib seqN bits.

Open Scope N_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.


(** numbers of index-bits for a given size *)
Definition size2idxbits (width size:N) : N := N.log2_up (size/width).


(* ALL AVAILABLE GATES names *)

Inductive gateID :=
 (* ELEMENTARY GATES *)
 | G_AND
 | G_XOR
 (* comparisons *)
 | Geq32
 | Gneq32
 | Gslt32
 | Gsle32
 | Gsgt32
 | Gsge32
 | Gult32
 | Gule32
 | Gugt32
 | Guge32
 | Geq32i of int
 | Gneq32i of int
 | Gslt32i of int
 | Gsle32i of int
 | Gsgt32i of int
 | Gsge32i of int
 | Gult32i of int
 | Gule32i of int
 | Gugt32i of int
 | Guge32i of int
 | Gmaskzero of int
 | Gnotmaskzero of int
 (* operations *)
 | Gconst32 of int
 | Gsint_cast of N
 | Guint_cast of N
 | Gadd32
 | Gadd32i of int
 | Gaddadd32i of int
 | Gmuladd32i of (int*int)
 | Gmuladdadd32i of (int*int)
 | Gneg32
 | Gsub32
 | Gmul32
 | Gmul32i of int
 | Gmulhs
 | Gmulhu
(* NYI: | Gdiv32 | Gdiv32u | Gmod32 | Gmod32u *)
 | Gand32
 | Gand32i of int
 | Gor32
 | Gor32i of int
 | Gxor32
 | Gxor32i of int
 | Gnot32
 | Gshl32
 | Gshl32i of int
 | Gshr32
 | Gshr32i of int
 | Gshrx32i of int
 | Gshru32
 | Gshru32i of int
 | Gror32i of int
 | Gshld32i of int
 | Gint64
 | Gint64low
 | Gint64hi
 (* support gates *)
 | Gid of N	(* identity gate *)
(* | Gcmp		(* int_of_bool *)*)
 | Gcond	(* cond gate "w1 ? w2 : w3" *)
 | GxorN of N	(* variable-width XOR *)
 | GcondN of N	(* variable-width COND *)
 | GbarrierN of N	(* variable-width barrier *)
 | Gconstbytes of (seq int)
 | Gguard of pcond
 | Gselk of (N*N*N) (* (aligned access) - width, size, offset *)
 | Gdsel of (N*N) (* (half-aligned access) - width, size *) 
 | Gsel of (N*N) (* (aligned access) - width, size *)
 | Gupdk of (N*N*N) (* (constant access) - width, size, offset *)
 | Gdupd of (N*N) (* (half-aligned access) -  width, size *) 
 | Gupd of (N*N) (* (aligned access) - width, size *)
 | Gcmp_uint of gateID (* 32-bit unsigned extension of a gate *)
.

Record gate_info := { gate_in_arity: N
                    ; gate_out_arity: N
                    ; gate_ev : seq bool -> seq bool
                    }.

(** gate of condition *)
Definition gate_of_scomparison (cmp: comparison) : gateID :=
 match cmp with
 | Ceq => Geq32
 | Cne => Gneq32
 | Clt => Gslt32
 | Cle => Gsle32
 | Cgt => Gsgt32
 | Cge => Gsge32
 end.

Definition gate_of_ucomparison (cmp: comparison) : gateID :=
 match cmp with
 | Ceq => Geq32
 | Cne => Gneq32
 | Clt => Gult32
 | Cle => Gule32
 | Cgt => Gugt32
 | Cge => Guge32
 end.

Definition gate_of_sicomparison (cmp: comparison) n : gateID :=
 match cmp with
 | Ceq => Geq32i n
 | Cne => Gneq32i n
 | Clt => Gslt32i n
 | Cle => Gsle32i n
 | Cgt => Gsgt32i n
 | Cge => Gsge32i n
 end.

Definition gate_of_uicomparison (cmp: comparison) n : gateID :=
 match cmp with
 | Ceq => Geq32i n
 | Cne => Gneq32i n
 | Clt => Gult32i n
 | Cle => Gule32i n
 | Cgt => Gugt32i n
 | Cge => Guge32i n
 end.

Definition gate_of_condition (cond: condition) : option gateID :=
 match cond with
 | Ccomp c => Some (gate_of_scomparison c)
 | Ccompu c => Some (gate_of_ucomparison c)
 | Ccompimm c n => Some (gate_of_sicomparison c n)
 | Ccompuimm c n => Some (gate_of_uicomparison c n)
 | Cmaskzero n => Some (Gmaskzero n)
 | Cmasknotzero n => Some (Gnotmaskzero n)
 | _ => None
 end.

Definition gate_of_cmp (cond: condition) : option gateID :=
 match cond with
 | Ccomp c => Some (gate_of_scomparison c)
 | Ccompu c => Some (gate_of_ucomparison c)
 | Ccompimm c n => Some (gate_of_sicomparison c n)
 | Ccompuimm c n => Some (gate_of_uicomparison c n)
 | Cmaskzero n => Some (Gmaskzero n)
 | Cmasknotzero n => Some (Gnotmaskzero n)
 | _ => None
 end.

Definition gate_of_operation (op: operation) : option gateID :=
 match op with
 | Omove => None (* handled separately *)
 | Ointconst n => Some (Gconst32 n)
 | Ofloatconst _ => None (* Not Yet Supported *)
 | Osingleconst _ => None (* Not Yet Supported *)
 | Oindirectsymbol _ => None (* Not Yet Supported *)
 | Ocast8signed => Some (Gsint_cast 8)
 | Ocast8unsigned => Some (Guint_cast 8)
 | Ocast16signed => Some (Gsint_cast 16)
 | Ocast16unsigned => Some (Guint_cast 16)
 | Oneg => Some Gneg32
 | Osub => Some Gsub32
 | Omul => Some Gmul32
 | Omulimm n => Some (Gmul32i n)
 | Omulhs => Some Gmulhs
 | Omulhu => Some Gmulhu
 | Odiv => None (* NYI: Some Gsdiv32 *)
 | Odivu => None (* NYI: Some Gudiv32 *)
 | Omod => None (* NYI: Some Gsmod32 *)
 | Omodu => None (* NYI: Some Gumod32 *)
 | Oand => Some Gand32
 | Oandimm n => Some (Gand32i n)
 | Oor => Some Gor32
 | Oorimm n => Some (Gor32i n)
 | Oxor => Some Gxor32
 | Oxorimm n => Some (Gxor32i n)
 | Onot => Some Gnot32
 | Oshl => Some Gshl32
 | Oshlimm n => Some (Gshl32i n)
 | Oshr => Some Gshr32
 | Oshrimm n => Some (Gshr32i n)
 | Oshrximm n => Some (Gshrx32i n)
 | Oshru => Some Gshru32
 | Oshruimm n => Some (Gshru32i n)
 | Ororimm n => Some (Gror32i n)
 | Oshldimm n => Some (Gshld32i n)
 | Omakelong => Some Gint64
 | Olowlong => Some Gint64low
 | Ohighlong => Some Gint64hi
 | Ocmp c => obind (fun g => Some (Gcmp_uint g)) (gate_of_condition c)
 (* Remark: [Olea] is a special case! Here, we handle just its use in
    arithmetic operations... *)
 | Olea (Aglobal _ _) => None  (* Not Yet Supported *)
 | Olea (Ainstack _) => None  (* Not Yet Supported *)
 | Olea (Abased _ _) => None  (* Not Yet Supported *)
 | Olea (Abasedscaled _ _ _) => None  (* Not Yet Supported *)
 | Olea (Aindexed n) => Some (Gadd32i n)
 | Olea (Aindexed2 n) => Some (Gaddadd32i n)
 | Olea (Ascaled sc ofs) => Some (Gmuladd32i (sc,ofs))
 | Olea (Aindexed2scaled sc ofs) => Some (Gmuladdadd32i (sc,ofs))
 (* float ops *)
 | Onegf => None	(* Not Yet Supported *)
 | Oabsf => None	(* Not Yet Supported *)
 | Oaddf => None	(* Not Yet Supported *)
 | Osubf => None	(* Not Yet Supported *)
 | Omulf => None	(* Not Yet Supported *)
 | Odivf => None	(* Not Yet Supported *)
 | Onegfs => None	(* Not Yet Supported *)
 | Oabsfs => None	(* Not Yet Supported *)
 | Oaddfs => None	(* Not Yet Supported *)
 | Osubfs => None	(* Not Yet Supported *)
 | Omulfs => None	(* Not Yet Supported *)
 | Odivfs => None	(* Not Yet Supported *)
 | Osingleoffloat => None	(* Not Yet Supported *)
 | Ofloatofsingle => None	(* Not Yet Supported *)
 | Ointoffloat => None	(* Not Yet Supported *)
 | Ofloatofint => None	(* Not Yet Supported *)
 | Ointofsingle => None	(* Not Yet Supported *)
 | Osingletofint => None	(* Not Yet Supported *)
 end.



(**
   SEMANTICS
*)

(** [cond_eval] converts an evaluation function on a condition-garded
 evaluation function *)
Definition cond_eval (fT fF:seq bool->seq bool) (data: seq bool): seq bool :=
 if data is x::xs
 then if x then fT xs else fF xs
 else [::].


(** constant int *)
Definition gate_const32 n :=
 {| gate_in_arity := 0
  ; gate_out_arity := 32
  ; gate_ev := fun _ => bits_of_int32 n
 |}.

Definition gate_cast_sint size :=
 {| gate_in_arity := 32
  ; gate_out_arity := 32
  ; gate_ev := fun data => bits_of_int32 (Int.sign_ext (Z_of_N size)
                                                     (int32_of_bits_at 0 data))
 |}.

Definition gate_cast_uint size :=
 {| gate_in_arity := 32
  ; gate_out_arity := 32
  ; gate_ev := fun data => bits_of_int32 (Int.zero_ext (Z_of_N size)
                                                (int32_of_bits_at 0 data))
 |}.

Definition eval_GcondN n : bits -> bits :=
 cond_eval (takeN n) (dropN n).

Definition eval_GbarrierN n : bits -> bits :=
 cond_eval (takeN n) (fun _ => takeN_dflt false n [::]).

Definition xor_bits (x y: bits) : bits :=
  zipWith xorb x y.

Lemma xor_bitsC: forall x y,
 xor_bits x y = xor_bits y x.
Proof.
rewrite /xor_bits; elim => [|x xs IHx]; elim => [|y ys IHy] //=.
by rewrite Bool.xorb_comm IHx.
Qed.

Definition bits0 n := takeN_dflt false n [::].

Lemma xor_bits_blk0: forall n x,
 sizeN x = n -> xor_bits x (bits0 n) = x.
Proof.
move => n x /= H.
rewrite /bits0 -H. 
elim: x {H} => //=.
move => x xs IH; rewrite /takeN_dflt N.peano_rect_succ /=.
rewrite /xor_bits /= Bool.xorb_false_r; f_equal.
by apply IH.
Qed.

Lemma xor_bitsK: forall x,
 xor_bits x x = bits0 (sizeN x).
Proof.
rewrite /xor_bits /bits0; elim => //= x xs IH.
by rewrite Bool.xorb_nilpotent IH !takeN_take_dflt N2Nat.inj_succ.
Qed.

Definition eval_GxorN n (l: bits) : bits :=
 xor_bits (takeN n l) (takeN n (dropN n l)).


(** binary comparison of signed ints *)
Definition gate_eval_cmp_bin (f:int->int->bool) (data: bits)
 : bits :=
 [:: f (int32_of_bits_at 0 data) (int32_of_bits_at 32 data)].

Definition ginfo_cmp_bin fsem : gate_info :=
 {| gate_in_arity := 64
  ; gate_out_arity := 1
  ; gate_ev := gate_eval_cmp_bin fsem
 |}.

Definition ginfo_cmp_bin1 fsem n :=
 {| gate_in_arity := 32
  ; gate_out_arity := 1
  ; gate_ev := fun data => gate_eval_cmp_bin fsem (data ++ bits_of_int32 n)
 |}.

(** boolean (comparison) seen as an int *)
Definition gate_bool_cast g :=
 {| gate_in_arity := g.(gate_in_arity)
  ; gate_out_arity := 32
  ; gate_ev := fun data => takeN_dflt false 32 (g.(gate_ev) data)
 |}.

Definition gate_eval_op_un (f: int->int) (data: seq bool)
 : seq bool :=
 bits_of_int32 (f (int32_of_bits_at 0 data)).

Definition gate_eval_op_bin (f: int->int->int) (data: seq bool)
 : seq bool :=
 bits_of_int32 (f (int32_of_bits_at 0 data) (int32_of_bits_at 32 data)).

Definition gate_op_un fsem := 
  {| gate_in_arity := 32
   ; gate_out_arity := 32
   ; gate_ev := gate_eval_op_un fsem
  |}.

Definition gate_op_bin fsem := 
  {| gate_in_arity := 64
   ; gate_out_arity := 32
   ; gate_ev := gate_eval_op_bin fsem
  |}.

Definition gate_op_bin1 fsem n := 
  {| gate_in_arity := 32
   ; gate_out_arity := 32
   ; gate_ev := fun data => gate_eval_op_bin fsem (data ++ bits_of_int32 n)
  |}.


Fixpoint eval_guard (c: pcond) (vars: bits) : bool*bits :=
 match c, vars with
 | pcondT, _ => (true,vars)
 | pcondF, _ => (false,vars)
 | _, [::] => (false, [::])
 | Node v l r, x::xs => let (r1, vars1) := eval_guard l xs in
                        let (r2, vars2) := eval_guard r vars1 in
                        if x then (r1,vars2) else (r2,vars2)
 end.
 
Fixpoint bdt_vars {A} (t: bdd A) : seq ident :=
 match t with
 | Leaf _ => nil
 | Node v l r => v :: bdt_vars l ++ bdt_vars r
 end.


Fixpoint gateInfo (gid: gateID) : gate_info :=
 match gid with
 (* elementary gates *)
 | G_AND => Build_gate_info 2 1 (fun l => if l is [:: b1; b2]
                                          then [:: b1 && b2]
                                          else [::])
 | G_XOR => Build_gate_info 2 1 (fun l => if l is [:: b1; b2]
                                          then [:: xorb b1 b2]
                                          else [::])
 (* Comparisons *)
 | Geq32 => ginfo_cmp_bin Int.eq
 | Gneq32 => ginfo_cmp_bin (fun x y=> ~~ Int.eq x y)
 | Gslt32 => ginfo_cmp_bin Int.lt
 | Gsle32 => ginfo_cmp_bin (fun x y=> ~~ Int.lt y x)
 | Gsgt32 => ginfo_cmp_bin (fun x y=> Int.lt y x)
 | Gsge32 => ginfo_cmp_bin (fun x y=> ~~ Int.lt x y)
 | Gult32 => ginfo_cmp_bin Int.ltu
 | Gule32 => ginfo_cmp_bin (fun x y=> ~~ Int.ltu y x)
 | Gugt32 => ginfo_cmp_bin (fun x y=> Int.ltu y x)
 | Guge32 => ginfo_cmp_bin (fun x y=> ~~ Int.ltu x y)
 | Geq32i n => ginfo_cmp_bin1 Int.eq n
 | Gneq32i n => ginfo_cmp_bin1 (fun x y=> ~~ Int.eq x y) n
 | Gslt32i n => ginfo_cmp_bin1 Int.lt n
 | Gsle32i n => ginfo_cmp_bin1 (fun x y=> ~~ Int.lt y x) n
 | Gsgt32i n => ginfo_cmp_bin1 (fun x y=> Int.lt y x) n
 | Gsge32i n => ginfo_cmp_bin1 (fun x y=> ~~ Int.lt x y) n
 | Gult32i n => ginfo_cmp_bin1 Int.ltu n
 | Gule32i n => ginfo_cmp_bin1 (fun x y=> ~~ Int.ltu y x) n
 | Gugt32i n => ginfo_cmp_bin1 (fun x y=> Int.ltu y x) n
 | Guge32i n => ginfo_cmp_bin1 (fun x y=> ~~ Int.ltu x y) n
 | Gmaskzero n => ginfo_cmp_bin1 (fun x y=> Int.eq (Int.and x y) Int.zero) n
 | Gnotmaskzero n => ginfo_cmp_bin1 ((fun x y=> ~~ Int.eq (Int.and x y) Int.zero)) n
 (* OPERATORS *)
 (* operations *)
 | Gconst32 n => gate_const32 n
 | Gsint_cast n => gate_cast_sint n
 | Guint_cast n => gate_cast_uint n
 | Gadd32 => gate_op_bin Int.add
 | Gadd32i n => gate_op_bin1 Int.add n
 | Gaddadd32i n => gate_op_bin (fun x y=> Int.add n (Int.add x y))
 | Gmuladd32i (sc,ofs) => gate_op_un (fun x=> Int.add (Int.mul sc x) ofs) 
 | Gmuladdadd32i (sc,ofs) => gate_op_bin (fun x y=> Int.add x (Int.add (Int.mul sc y) ofs))
 | Gneg32 => gate_op_un Int.neg
 | Gsub32 => gate_op_bin Int.sub
 | Gmul32 => gate_op_bin Int.mul
 | Gmul32i n => gate_op_bin1 Int.mul n
 | Gmulhs => gate_op_bin Int.mulhs
 | Gmulhu => gate_op_bin Int.mulhu
(* NYI: | Gdiv32 | Gdiv32u | Gmod32 | Gmod32u *)
 | Gand32 => gate_op_bin Int.and
 | Gand32i n => gate_op_bin1 Int.and n
 | Gor32 => gate_op_bin Int.or
 | Gor32i n => gate_op_bin1 Int.or n
 | Gxor32 => gate_op_bin Int.xor
 | Gxor32i n => gate_op_bin1 Int.xor n
 | Gnot32 => gate_op_un Int.not
 | Gshl32 => gate_op_bin Int.shl
 | Gshl32i n => gate_op_bin1 Int.shl n
 | Gshr32 => gate_op_bin Int.shr
 | Gshr32i n => gate_op_bin1 Int.shr n
 | Gshrx32i n => gate_op_bin1 Int.shrx n
 | Gshru32 => gate_op_bin Int.shru
 | Gshru32i n => gate_op_bin1 Int.shru n
 | Gror32i n => gate_op_bin1 Int.ror n
 | Gshld32i n => gate_op_bin (fun x y=> Int.or (Int.shl x n) (Int.shru y (Int.sub Int.iwordsize n)))
 | Gint64 => Build_gate_info 64 64 (fun l=> bits_of_int64 (Int64.ofwords (int32_of_bits_at 0 l) (int32_of_bits_at 32 l)))
 | Gint64low => Build_gate_info 64 32 (fun l=> bits_of_int32 (int32_of_bits_at 0 l))
 | Gint64hi => Build_gate_info 64 32 (fun l=> bits_of_int32 (int32_of_bits_at 32 l))
 (* Support gates *)
 | Gid n => Build_gate_info n n id
(* | Gcmp =>  Build_gate_info 1 32 id*)
 | Gcond => 
     Build_gate_info 3 1 (fun l => if l is [:: b1; b2; b3]
                                   then [:: if b1 then b2 else b3]
                                   else [::])
 | GcondN n =>
     Build_gate_info (1+2*n) n (eval_GcondN n)
 | GbarrierN n =>
     Build_gate_info (1+n) n (eval_GbarrierN n)
 | GxorN n =>
     Build_gate_info (2*n) n (eval_GxorN n)
 | Gconstbytes l =>
     Build_gate_info 0 (8*sizeN l) (fun _ => (flatten (map bits_of_int8 l)))
 | Gguard c =>
     Build_gate_info (sizeN (bdt_vars c)) 1 (fun l => [:: (eval_guard c l).1])
 | Gselk (width, size, ofs) => (* obs: ofs in bits *)
     Build_gate_info size width
                     (fun l => nthN_width width l (ofs/width))
 | Gsel (width, size)  => (* obs: idx is element index *)
     Build_gate_info  (size+size2idxbits width size) width
                      (fun l => nthN_width width (takeN size l)
                                           (N_of_bits (dropN size l)))
 | Gdsel (width, size)  =>
     Build_gate_info  (size+size2idxbits width size) (2*width)
                      (fun l => nthN_dwidth width (takeN size l)
                                            (N_of_bits (dropN size l)))
 | Gupdk (width, size, ofs) => (* obs: ofs in bits *)
     Build_gate_info (1+width+size) size
                     (cond_eval
                        (fun l => updprefAtN (ofs)
                                             (takeN size (dropN width l))
                                             (takeN width l))
                        (dropN width))
 | Gupd (width, size)  => (* obs: newv++array++idx (idx is element idex)*)
     Build_gate_info (1+width+size+size2idxbits width size) size
                     (cond_eval
                        (fun l => updprefAtN (width*N_of_bits (dropN (size+width) l))
                                             (takeN size (dropN width l))
                                             (takeN width l))
                        (fun l => takeN size (dropN width l)))
 | Gdupd (width, size)  =>
     Build_gate_info (1+2*width+size+size2idxbits width size) size
                     (cond_eval
                        (fun l => updprefAtN (width*N_of_bits (dropN (size+2*width) l))
                                             (takeN size (dropN (2*width) l))
                                             (takeN (2*width) l))
                        (fun l => takeN size (dropN (2*width) l)))
 | Gcmp_uint g => gate_bool_cast (gateInfo g)
 end.

Definition gate_inputs (g: gateID) : N :=
 (gateInfo g).(gate_in_arity).

Definition gate_outputs (g: gateID) : N :=
 (gateInfo g).(gate_out_arity).

(** [match_val_ty] relates ValCirc wire-values of Compcert kind (not guards) *)
Definition match_val_ty (v: Values.val) (v': bits) : Prop :=
  match v with
  | Values.Vundef => True
  | Values.Vint i => v' = bits_of_int32 i
  | Values.Vlong i => v' = bits_of_int64 i
  | Values.Vsingle f => v' = bits_of_int32 (Floats.Float32.to_bits f)
  | Values.Vfloat f => v' = bits_of_int64 (Floats.Float.to_bits f)
  | _ => False
  end.

Inductive match_val_list : list Values.val -> bits -> Prop :=
 | match_val_nil : match_val_list [::] [::]
 | match_val_cons : forall v vs bv bvs,
     match_val_ty v bv ->
     match_val_list vs bvs ->
     match_val_list (v::vs) (bv ++ bvs).

Lemma match_val_list_inv0: forall inbits,
 match_val_list [::] inbits -> inbits = [::].
Proof.
move => [| x xs] // => H; inversion H.
Qed.

Lemma match_val_list_inv1: forall v inbits,
 match_val_list [:: v] inbits -> 
 exists l, inbits = l ++ [::] /\ match_val_ty v l.
Proof.
 move => v inbits H; inversion_clear H.
inversion_clear H1.
by exists bv. 
Qed. 

Lemma match_val_list_inv2: forall v1 v2 inbits,
 match_val_list [:: v1; v2] inbits -> 
 exists l1 l2,
   inbits=l1++l2++[::] /\
   match_val_ty v1 l1 /\
   match_val_ty v2 l2.
Proof.
move => v1 v2 inbits H; inversion_clear H; inversion_clear H1; inversion_clear H2.
by exists bv, bv0.
Qed.

Lemma match_val_list_inv3: forall v1 v2 v3 inbits,
 match_val_list [:: v1; v2; v3] inbits -> 
 exists l1 l2 l3,
   inbits=l1++l2++l3++[::] /\
   match_val_ty v1 l1 /\
   match_val_ty v2 l2 /\
   match_val_ty v3 l3.
Proof.
move => v1 v2 v3 inbits H; inversion_clear H; inversion_clear H1; inversion_clear H2.
inversion_clear H3.
by exists bv, bv0, bv1.
Qed.

Ltac hargs_inv :=
  try by [] ||
  match goal with
  | H : match_val_list [::] ?l |- _ =>
    move/match_val_list_inv0: H => H; rewrite -?H {H}
  | H : match_val_list [:: ?v] ?l |- _ => 
    let t1 := fresh "t0" in
    let l1 := fresh "bits0" in
    let H1 := fresh "Hbits0" in
    move/match_val_list_inv1: H => [l1 [-> H1]]
  | H : match_val_list [:: ?v; ?w] ?l |- _ =>
    let l1 := fresh "bits0" in
    let H1 := fresh "Hbits0" in
    let l2 := fresh "bits0" in
    let H2 := fresh "Hbits0" in
    move/match_val_list_inv2: H => [l1 [l2 [-> [H1 H2]]]]
  | H : match_val_list [:: ?v; ?w; ?z] ?l |- _ =>
    let l1 := fresh "bits0" in
    let H1 := fresh "Hbits0" in
    let l2 := fresh "bits0" in
    let H2 := fresh "Hbits0" in
    let l3 := fresh "bits0" in
    let H3 := fresh "Hbits0" in
    move/match_val_list_inv3: H => [l1 [l2 [l3 [-> [H1 [H2 H3]]]]]]
  end.

Ltac value_destruct :=
  (repeat match goal with
  | vmatch: match_val_ty ?v ?bits |- _ =>
    let i := fresh "i" in move: v vmatch => [|i|i|?|?|? i] //= ->
  end)
  ; rewrite ?/gate_eval_cmp_bin ?/gate_eval_op_un ?cats0 ?/gate_eval_op_bin /= ?int32_of_bits_at_0 ?int32_of_bits_at_0' ?int32_of_bits_at_32 //=.

Lemma match_val_if: forall (cond:bool) v bits,
  match_val_ty v bits ->
  match_val_ty (if cond then v else Values.Vundef) bits.
Proof. by move=> cond v bits H; case: cond. Qed.

Lemma gate_of_condition_correct:
 forall cond gid args inbits mem res,
  gate_of_condition cond = Some gid ->
  match_val_list args inbits ->
  eval_condition cond args mem = Some res ->
  gate_ev (gateInfo gid) inbits = [:: res ].
Proof.
move=> [cond|cond|cond i|cond i|?|?|?|?|i|i] gid args inbits mem res;
move: args => [|v1 [| v2 [|v3 ?]]] [Egid] H Hev //=.
- by move: cond H Egid Hev => [|||||] H <- //;
  inversion_clear H; inversion_clear H1; inversion_clear H2;
  value_destruct; move => [<-] //.
- by move: cond H Egid Hev => [|||||] H <- //;
  inversion_clear H; inversion_clear H1; inversion_clear H2;
  value_destruct; move => [<-] //.
- by move: cond H Egid Hev => [|||||] H <- //;
  inversion_clear H; inversion_clear H1;
  value_destruct; move => [<-] //.
- by move: cond H Egid Hev => [|||||] H <- //;
  inversion_clear H; inversion_clear H1;
  value_destruct; move => [<-] //.
- by move: Egid Hev => <-; inversion_clear H; inversion_clear H1;
  value_destruct; move => [<-] //=.
- by move: Egid Hev => <-; inversion_clear H; inversion_clear H1;
  value_destruct; move => [<-] //=.
Qed.

Lemma gate_out_arity_condition cmp g:
  gate_of_condition cmp = Some g -> gate_out_arity (gateInfo g) = 1.
Proof.
by move: cmp => [c|c|c i|c i|c|c|c|c|i|i]; try destruct c;
move => // [E]; rewrite //= -E.
Qed.

Lemma gate_of_operation_correct':
 forall op gid args inbits outbits F V (genv:Globalenvs.Genv.t F V) sp mem res,
  gate_of_operation op = Some gid ->
  match_val_list args inbits ->
  gate_ev (gateInfo gid) inbits = outbits ->
  eval_operation genv sp op args mem = Some res ->
  match_val_ty res outbits.
Proof.
move=> op gid args inbits outbits F V genv sp mem res.
move: op =>
[|i|?|?|?||||||||i||||||||i||i||i|||i||i| i ||i|i|i
 |[off|off|sc off|sc off|? ?|? ?|? ? ?|?]|||||||||||||||||||||
 | cmp ]
(* |[cond|cond|cond i|cond i|?|?|?|?|i|i]]*)
/= Gop; try discriminate Gop;

( move: Gop => [<-] Hargs /= Hev;
move: args Hargs => [|v1 [| v2 [| ? ?]]] Hargs E; try discriminate E;
move: E; (move => [<-] || move => E); rewrite -Hev {Hev};
hargs_inv; value_destruct; try apply match_val_if; try by []) || idtac.
- move: v1 E Hbits0 => [|v1|?|?|?|? ?] /= E1; try discriminate E1.
  move: E1; case: (Int.ltu i (Int.repr 31)) => [[<-] -> |E]; last discriminate E.
  by rewrite int32_of_bits_at_0' int32_of_bits_at_32.
- case E1: (Int.ltu i Int.iwordsize) => //.
  value_destruct.
  case E2: (Int.ltu (Int.sub Int.iwordsize i) Int.iwordsize) => //.
- by rewrite Int.add_commut.
- by rewrite Int.mul_commut.
- by rewrite Int.mul_commut.
- by rewrite bits_of_int64_lohi int32_of_bits_at_0'.
- by rewrite bits_of_int64_lohi int32_of_bits_at_32.
- move=> H <- [<-].
  move: Gop.
  case Egate: (gate_of_condition cmp) => [gID|] /=; last by [].
  move=> [<-].
  case Econd: (eval_condition cmp args mem); last by [].
  move: (gate_of_condition_correct Egate H Econd).
  move => HH.
  by rewrite [gateInfo _]/= /gate_bool_cast [takeN_dflt]lock /= HH -lock; case: (ifP _).
Qed.

Require RTLC.

Lemma sizeN_gate_ev: forall op gid inbits,
 gate_of_operation op = Some gid ->
 sizeN (gate_ev (gateInfo gid) inbits) = gate_outputs gid.
Proof.
rewrite /gate_inputs /gate_outputs.
case => [|i|?|?|?||||||||i||||||||i||i||i|||i||i| i ||i|i|i
 |[off|off|sc off|sc off|? ?|? ?|? ? ?|?]|||||||||||||||||||||
 | cmp ] gid inbits /= E; discriminate E || move: E => [E];
 rewrite -?E /= ?/gate_eval_op_un /gate_eval_op_bin ?sizeN_size ?size_bits_of_int32 
         ?size_bits_of_int64 //.
move: E; case: (gate_of_condition cmp) => //=.
move=> gid' [<-]; simpl gateInfo; rewrite /gate_bool_cast [takeN_dflt]lock /=.
by rewrite -lock size_takeN_dflt N2Nat.id.
Qed.

Lemma gate_of_operation_correct:
 forall op gid args inbits F V (genv:Globalenvs.Genv.t F V) sp mem,
  gate_of_operation op = Some gid ->
  match_val_list args inbits ->
  match_val_ty (RTLC.eval_operation genv sp op args mem)
            (takeN_dflt false (gate_out_arity (gateInfo gid))
                        (gate_ev (gateInfo gid) inbits)).
Proof.
move=> op gid args inbits F V genv sp mem.
move=> Gop Hin.
move Hout: (gate_ev (gateInfo gid) inbits) => outbits.
rewrite /RTLC.eval_operation.
move Hev: (eval_operation genv sp op args mem) => [res|] //.
move: (gate_of_operation_correct' Gop Hin Hout Hev) => HH.
by rewrite takeN_dflt_eqsize // -Hout (@sizeN_gate_ev op).
Qed.
