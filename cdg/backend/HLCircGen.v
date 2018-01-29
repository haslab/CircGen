(** Translation from ValCirc into HLCirc. *)

Require Import Coqlib.
Require Errors.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Op.

Require ValCirc.
Require Import OpGates HLCirc.

Require Import ssreflect ssrfun ssrbool seq eqtype.
Require Import ORbdt ssrlib ssrValues seqN bits.
Import Utf8.

Unset Elimination Schemes.

(** [globv_info] is connector associated to a global var.            *)
Definition globv_info := connector.

(* [localv_info] keeps track, for ValCirc wires, of:
   - type_of_wire
     + [None], if not meaningfull (e.g. global var.)
     + [Some None], for conditions (single bit)
     + [Some (Some ty)], for normal CompCert values
   - gate_number (global_id=0 is reserved for the "Stack")      *)
Definition localv_info := ((option (option typ))*gate_number)%type.

Record state: Type := mkstate {
  st_wire: N; (* next gate entry *)
  st_twire: N; (* last used target wire *)
  st_code: seq gentry; (* code (in reverse order...) *)
  st_globv: PTree.t globv_info; (* globvar map (connector) *)
  st_localv: PTree.t localv_info; (* local map (gID + gID,off,args) *)
  st_condv: PTree.t N	(* (ValCirc)wire_of_condition *)
}.

Definition st_add_code (ge: gentry) (st: state) : N * state :=
  let w := N.succ (st_wire st) in
  (w, mkstate w (st_twire st) (ge :: st_code st)
          (st_globv st) (st_localv st) (st_condv st)).

Definition st_upd_globv (upd_globv: PTree.t globv_info -> PTree.t globv_info)
                        (st: state) : state :=
 mkstate st.(st_wire) st.(st_twire) st.(st_code)
         (upd_globv st.(st_globv)) st.(st_localv) st.(st_condv).
 
Definition st_upd_localv w x (st: state) : state :=
 mkstate st.(st_wire) x.2 st.(st_code)
         st.(st_globv) (PTree.set w x st.(st_localv)) st.(st_condv).

(** ** error monad *)

Inductive exn :=
 | exn_initmem_creation		(* cannot create initmem (pointers) *)
 | exn_input_wires_mismatch : exn	(* number of inp. wires don't match *)
 | exn_output_wires_mismatch : exn	(* number of out. wires don't match *)
 | exn_malformed_condv : exn	(* cannot invert condv map *)
 | exn_condv_notfound : exn	(* undefined cond. var *)
 | exn_globv_notfound : exn	(* undefined global var *)
 | exn_localv_notfound : exn	(* accessing a not yet defined local var *)
 | exn_localv_kinderror : exn	(* kind mismatch of local var (val vs. bool) *)
 | exn_localv_rewrite : exn	(* rewrite attempt on a local var *)
 | exn_globv_sizemismatch : exn	(* inconsistent sizes on global var *)
 | exn_typerror : exn		(* op. type doesn't match *)
 | exn_invalid_address : exn	(* non-supported address in load/store *)
 | exn_ptr_in_memory : exn	(* trying to store ptr in memory *)
 | exn_malformed_guard : exn	(* malformed guard *)
 | exn_malformed_phi : exn	(* malformed (null?) phiNode *)
 | exn_nonsupported_gate: exn	(* non-supported gate (yet, at least) *)
 | exn_msg : seq Errors.errcode -> exn.

Definition merror A := (A + exn)%type.

Definition merror_ret {A} (x:A) : merror A := inl x.

Definition merror_err {A} (e:exn) : merror A := inr e.

Definition merror_bind {A B} (x:merror A) (f: A -> merror B) : merror B :=
 match x with
 | inl v => f v
 | inr e => inr e
 end.

Definition merror_map {A B} (f:A->B) (x:merror A) : merror B :=
 match x with
 | inl y => inl (f y)
 | inr e => inr e
 end.

Definition merror_emap {A} (f:exn->exn) (x:merror A) : merror A :=
 if x is inr e then inr (f e) else x.

Definition merror_bind2 {A B C: Type} 
  (x: merror (A * B)) (g: A -> B -> merror C) :=
  merror_bind x (fun xy => g (fst xy) (snd xy)).

Notation "'doE' X <- A ; B" := (merror_bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : merror_scope.
Notation "'doE' ( X , Y ) <- A ; B" := (merror_bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : merror_scope.

Open Scope merror_scope.

Definition mstate A : Type := state → merror (A * state).

Definition mstate_ret {A} (x:A) : mstate A := fun st => inl (x,st).

Definition mstate_err {A} (e:exn) : mstate A := fun st => inr e.

Definition mstate_emap {A} (f: exn -> exn) (x: mstate A): mstate A :=
 fun st => let y := x st in match y with inr e => inr (f e) | _ => y end.

Definition mstate_bind {A B} (x:mstate A) (f: A -> mstate B) : mstate B :=
 fun st => match x st with
           | inl (v',st') => f v' st'
           | inr e => inr e
           end.

Definition mstate_bind2 {A B C: Type} 
  (x: mstate (A * B)) (g: A -> B -> mstate C) :=
  mstate_bind x (fun xy => g (fst xy) (snd xy)).

Definition mstate_getstate : mstate state := fun st => inl (st,st).

Definition mstate_updstate (upd: state->state) : mstate unit :=
 fun st => inl (tt,upd st).

Definition mstate_lift_merror {A} (x: merror A) : mstate A :=
 match x with
 | inl y => mstate_ret y
 | inr e => mstate_err e
 end.

Definition mstate_lift_state {A} (f: state → A * state) : mstate A :=
  λ s, inl (f s).

Notation "'doS' X <- A ; B" := (mstate_bind A (fun X => B))
   (at level 200, X ident, A at level 100, B at level 200)
   : mstate_scope.
Notation "'doS' ( X , Y ) <- A ; B" := (mstate_bind2 A (fun X Y => B))
   (at level 200, X ident, Y ident, A at level 100, B at level 200)
   : mstate_scope.

Open Scope mstate_scope.

(* state access and update *)

(* [add_gate_unsafe] only checks conformance on the input sizes.     *)
Definition add_gate_unsafe (g: gateID) (c: connector) : mstate gate_number :=
 if gate_inputs g == sizeN c
 then mstate_lift_state (st_add_code {| gate := g ; conn := c |})
 else mstate_err exn_input_wires_mismatch.

(* [add_gate_ty] adds a gate producing a value of type [ty]       *)
Definition add_gate_ty (ty:typ) g c : mstate gate_number :=
 if (gate_outputs g == wires_of_type ty)
 then add_gate_unsafe g c
 else mstate_err exn_output_wires_mismatch.

Definition get_code : mstate (seq gentry) :=
 doS st <- mstate_getstate;
 mstate_ret (rev st.(st_code)).
 
Definition merror_globv_get (v:ident) gmap : merror connector :=
 if PTree.get v gmap is Some c
 then merror_ret c
 else merror_err exn_globv_notfound.

Definition globv_get (v:ident) : mstate connector :=
 doS st <- mstate_getstate;
 mstate_lift_merror (merror_globv_get v st.(st_globv)).

Definition globv_getbyte gmap (v:ident) (ofs: Integers.int): merror connector :=
 doE c <- merror_globv_get v gmap;
 merror_ret (takeN_dflt wire_FF 8 (dropN (8 * N_of_Z (Integers.Int.intval ofs)) c)).

Definition globv_upd (v:ident) new_conn : mstate unit :=
 doS st <- mstate_getstate;
 if PTree.get v st.(st_globv) is Some conn
 then if sizeN conn == sizeN new_conn
      then mstate_updstate (st_upd_globv (PTree.set v new_conn))
      else mstate_err exn_globv_sizemismatch
 else mstate_err exn_globv_notfound.

Definition localv_get (v:ValCirc.wire) : mstate localv_info :=
 doS st <- mstate_getstate;
 if PTree.get (N.succ_pos v) st.(st_localv) is Some x
 then mstate_ret x
 else mstate_err exn_localv_notfound.

Definition localv_get_conn (v:ValCirc.wire) : mstate connector :=
 doS (ooty,gw) <- localv_get v;
 if ooty is Some (Some ty)
 then mstate_ret (conn_ty ty gw)
 else mstate_err exn_localv_kinderror.

Definition localv_set (v:ValCirc.wire) x : mstate unit :=
 doS st <- mstate_getstate;
 if PTree.get (N.succ_pos v) st.(st_localv) is Some y
 then mstate_err exn_localv_rewrite
 else if N.ltb st.(st_twire) x.2
      then mstate_updstate (st_upd_localv (N.succ_pos v) x)
      else mstate_err exn_localv_rewrite.

(** [condv_get] returns the HLCirc wire of a guard-variable. It
 also enforces correctness of the (ValCirc) guard-variable, by checking:
 - its value is below of the current wire
 - have been assigned the correct type *)
Definition condv_get cur (cvar: ident) : mstate gate_number :=
 doS st <- mstate_getstate;
 if PTree.get cvar st.(st_condv) is Some n
 then if n <? cur
      then doS ninfo <- localv_get n;
           if ninfo is (Some None,gw)
           then mstate_ret gw
           else mstate_err exn_typerror
      else mstate_err exn_malformed_guard
 else mstate_err exn_condv_notfound.

(** The initial state (empty CFG). 
 globv_map:
  1: INPUT
  2: STACK (global xH)
  3: GLOBAL #1 (global (Psucc id))
  ...
*)

Definition merror_globv_upd_at (v:ident) pos (new:connector) gmap
 : merror (PTree.t globv_info) :=
 doE c <- merror_globv_get v gmap;
 merror_ret (PTree.set v (conn_upd_at c (8*N_of_Z pos) new) gmap).

Fixpoint add_inputs n (inputs: seq (CircIO.slot*ident)) (gmap: PTree.t connector)
 : merror (PTree.t connector) :=
 if inputs is (((inp,off),_)::rest)
 then doE gmap' <- merror_globv_upd_at (Psucc inp) (Integers.Int.intval off)
                                       (conn_new 1 (n*8) 8) gmap;
      add_inputs (N.succ n) rest gmap'
 else merror_ret gmap.

Definition PTree_add {A} k v (map: PTree.t A) : option (PTree.t A) :=
 if map ! k is Some v'
 then None
 else Some (PTree.set k v map).

Definition wire_of_condition_wires (map: PTree.t ident)
 : option (PTree.t N) :=
 PTree.fold (fun rmap wire cond => obind (PTree_add cond (Npred (Npos wire)))
                                         rmap)
            map (Some (PTree.empty N)).

Lemma wire_of_condition_wiresP cw condv n v:
 wire_of_condition_wires cw = Some condv ->
 (condv ! v = Some n <-> cw ! (N.succ_pos n) = Some v).
Proof.
rewrite /wire_of_condition_wires PTree.fold_spec -fold_left_rev_right => H.
have T:  cw ! (N.succ_pos n) = Some v <-> In (N.succ_pos n, v) (PTree.elements cw).
 split. 
  by apply PTree.elements_correct.
 by apply PTree.elements_complete.
rewrite T {T} In_rev.
elim: (List.rev (PTree.elements cw)) condv H v n => //=.
 by move=> condv [<-] v n /=; rewrite PTree.gempty.
move=> [n' v'] l IH /= condv /obind_isS [x [H1]].
rewrite /PTree_add.
case Hv': (x!v'); move=> // [Econdv].
move: IH; rewrite -Econdv => IH v n.
case Ev: (v==v').
 rewrite (eqP Ev) PTree.gss; split.
  move=> [<-]; left; f_equal.
  have T: Npos n' = Npos (N.succ_pos (Pos.pred_N n')).
   by rewrite N.succ_pos_spec N.succ_pos_pred.
  by injection T.
 move=> [H|H].
  injection H => ->; f_equal.
  by rewrite N.pos_pred_succ.
 move: H; rewrite -(IH _ H1).
 by rewrite Hv'.
rewrite PTree.gso; last first.
 by move=> H; move: Ev; rewrite H eq_refl.
split.
 move=> H; right.
 by rewrite -IH; eauto.
move=> [H|H].
 by injection H => Ev'; rewrite Ev' eq_refl in Ev.
move: H; rewrite -IH; eauto.
Qed.

Lemma condition_wires_inj cw condv v n1 n2:
 wire_of_condition_wires cw = Some condv ->
 cw ! (N.succ_pos n1) = Some v -> cw ! (N.succ_pos n2) = Some v -> n1 = n2.
Proof.
move=> Hcondv.
rewrite -!(@wire_of_condition_wiresP cw condv) //.
by move=> -> [->].
Qed.

Lemma condv_inj cw condv v n1 n2:
 wire_of_condition_wires cw = Some condv ->
 condv ! n1 = Some v -> condv ! n2 = Some v -> n1 = n2.
Proof.
move=> Hcondv.
rewrite !(@wire_of_condition_wiresP cw condv) //.
by move=> -> [->].
Qed.

Fixpoint init_globmap ssz n (globs: seq (ident*option bytes)) : PTree.t globv_info :=
 if globs is (v,vini)::rest
 then if vini is Some ibytes
      then PTree.set (Pos.succ v)
                     (conn_new n 0 (8*sizeN ibytes))
                     (init_globmap ssz (N.succ n) rest)
      else PTree.remove (Pos.succ v) (init_globmap ssz n rest)
 else PTree.set 1 (conn_new 2 0 (8*Z.to_N ssz)) (PTree.empty globv_info).

(* [sizeN_globs] is the number of global variables with initialization data *)
Fixpoint sizeN_globs (globs: seq (ident*option bytes)) :=
  if globs is x::xs
  then if x.2 is Some _
       then N.succ (sizeN_globs xs)
       else sizeN_globs xs
  else 0.

Definition init_state (ssz: Z)
                      (globs: seq (ident*option bytes))
                      (inputs: seq (CircIO.slot*ident))
                      (condition_wires: PTree.t ident)
  : merror state :=
  doE gmap <- add_inputs 0 inputs (init_globmap ssz 3 globs);
  if wire_of_condition_wires condition_wires is Some condv_map
  then merror_ret (mkstate (2+sizeN_globs globs) 0 [::] gmap
                  (PTree.empty localv_info) condv_map)
  else merror_err exn_malformed_condv.

(** fetch the gates of "pure" (non-addr) wires *)
Fixpoint args_wires (args: seq ValCirc.wire) : mstate connector :=
 match args with
 | (x::xs) =>
    doS wx <- localv_get_conn x;
    doS wxs <- args_wires xs ;
    mstate_ret (wx++wxs)
 | nil =>
    mstate_ret [::]
 end.

Definition proc_op (op: operation) (args: seq ValCirc.wire)
 : mstate (typ*gate_number) :=
 if gate_of_operation op is Some g
 then let (_, tres) := type_of_operation op in
      doS wargs <- args_wires args;
      doS gw <- add_gate_ty tres g wargs;
      mstate_ret (tres,gw)
 else mstate_err exn_nonsupported_gate.

Definition add_gate_Aglobal (off: int) : mstate gate_number :=
 add_gate_ty Tint (Gconst32 off) [::].

Definition add_gate_Aindexed (off: int) (r1: gate_number)
 : mstate gate_number :=
 add_gate_ty Tint (Gadd32i off) (conn_ty Tint r1).

Definition add_gate_Aindexed2 (off: int) (g1 g2: gate_number)
  : mstate gate_number :=
 add_gate_ty Tint (Gaddadd32i off) (conn_ty Tint g1 ++ conn_ty Tint g2).

Definition add_gate_Ascaled (sc off: int) (r1: gate_number)
  : mstate gate_number :=
 add_gate_ty Tint (Gmuladd32i (sc,off)) (conn_ty Tint r1).

Definition add_gate_Aindexed2scaled (sc off: int) (r1 r2: gate_number)
  : mstate gate_number :=
 add_gate_ty Tint (Gmuladdadd32i (sc,off)) (conn_ty Tint r1 ++ conn_ty Tint r2).

(** [proc_addr] processes addresses. It returns either
  - [addr] is a constant address -- result is [inr (ident,inl off)],
   where [off] is the constant offset;
  - [addr] is a non-constant address -- result is [inr (ident,inr wg)],
   where [wg] is the gate computing the index-part of the address.
*)
Definition proc_addr (addr: addressing) (args: seq ValCirc.wire)
 : mstate (ident*(int + gate_number)) :=
  match addr with
 | Aglobal s off => (* symbol + offset *)
   if args is [::] then
   mstate_ret (Psucc s, inl off)
   else mstate_err exn_invalid_address
 | Abased s off => (* symbol + offset + r1 *)
   if args is [:: r1] then
    doS (_,wg) <- proc_op (Olea (Aindexed off)) args;
    mstate_ret (Psucc s, inr wg)
   else mstate_err exn_invalid_address
 | Abasedscaled sc s off => (* symbol + offset + r1 * scale *)
   if args is [:: r1] then
    doS (_,wg) <- proc_op (Olea (Ascaled sc off)) args;
    mstate_ret (Psucc s, inr wg)
   else mstate_err exn_invalid_address
 | Ainstack off => (* stack_pointer + offset *)
   if args is [::] then
    mstate_ret (xH, inl off)
   else mstate_err exn_invalid_address
 | Aindexed _ (* r1 + offset *)
 | Aindexed2 _ (* r1 + r2 + offset *)
 | Ascaled _ _ (* r1 * scale + offset *)
 | Aindexed2scaled _ _ (* r1 + r2*scale + offset *)
   => mstate_err exn_invalid_address
 end.

(* Processing of Load/Store *)

Definition add_gate_selk (chunk: memory_chunk) (ofs: int) (gconn: connector)
 : mstate connector :=
 let width := 8*sizeN_chunk chunk in
 doS g <- add_gate_unsafe (Gselk (width, sizeN gconn, 8*N_of_int ofs))
                          gconn;
 mstate_ret (conn_new g 0 width).

Definition add_gate_sel (chunk: memory_chunk) (gconn gidx: connector)
 : mstate connector :=
 let width := 8*sizeN_chunk chunk in
 doS g <- add_gate_unsafe (Gsel (width, sizeN gconn))
                          (gconn++gidx);
 mstate_ret (conn_new g 0 width).

Definition add_gate_updk (wguard: wire) (chunk: memory_chunk) (ofs: int)
                         (gconn: connector) (x: gate_number)
 : mstate gate_number :=
 let width := 8*sizeN_chunk chunk in 
 add_gate_unsafe (Gupdk (width, sizeN gconn, 8*N_of_int ofs))
                 (wguard::(conn_new x 0 width)++gconn).

Definition add_gate_upd (wguard: wire) (chunk: memory_chunk)
                        (gconn idxconn: connector) (x: gate_number)
 : mstate gate_number :=
 let width := 8*sizeN_chunk chunk in
 add_gate_unsafe (Gupd (width, sizeN gconn))
                 (wguard::(conn_new x 0 width)++gconn++idxconn).

(* GUARDS *)

Fixpoint bdt_vars {A} (t: bdd A) : seq ident :=
 match t with
 | Leaf _ => nil
 | Node v l r => v :: bdt_vars l ++ bdt_vars r
 end.

(** [bdt_ren] ensures that all (ValCirc) variables from [t] are below [cur] *)
Fixpoint bdt_ren {A} (cur:N) (t: bdd A) : mstate (bdd A) :=
 match t with
 | Leaf x => mstate_ret (Leaf x)
 | Node v l r =>
     doS v_ren <- condv_get cur v;
     doS l_ren <- bdt_ren cur l;
     doS r_ren <- bdt_ren cur r;
     if v_ren is Npos p
     then mstate_ret (Node p l_ren r_ren)
     else mstate_err exn_malformed_guard
 end.

Definition conn_guard (t: pcond) :=
 map (fun x => (Npos x,0)) (bdt_vars t).

Definition add_gate_guard (guard: pcond) : mstate wire :=
(*
 if guard is pcondT
 then mstate_ret (0,1)
 else *)
      doS g <- add_gate_unsafe (Gguard guard) (conn_guard guard);
      mstate_ret (g,0).

Definition add_gate_and_guard (gw: N) (guard: wire) : mstate N :=
(*
  if (guard == wire_TT)
  then mstate_ret gw
  else *) add_gate_unsafe G_AND [:: (gw,0); guard].

(* LOAD *)
Definition add_gate_decode_val (ϰ: memory_chunk) (conn: connector)
 : mstate (typ*gate_number) :=
  let width := wires_of_type (type_of_chunk ϰ) in
  let newconn := chunk_ext ϰ wire_FF conn
  in doS g <- add_gate_unsafe (Gid width) newconn;
     mstate_ret (type_of_chunk ϰ, g).

Definition proc_load chunk addr args
 : mstate (typ*gate_number) :=
 if Memdata.align_chunk chunk == Memdata.size_chunk chunk
 then  doS paddr <- proc_addr addr args;
       match paddr with
       | (v, inl off) => 
            doS gconn <- globv_get v;
            doS xconn <- add_gate_selk chunk off gconn;
            add_gate_decode_val chunk xconn
       | (v, inr n) =>
            doS gconn <- globv_get v;
            let idxconn := conn_new n (N.log2 (sizeN_chunk chunk))
                                    (size2idxbits (8*sizeN_chunk chunk)
                                                  (sizeN gconn)) in
            doS xconn <- add_gate_sel chunk gconn idxconn;
            add_gate_decode_val chunk xconn
       end
 else (* REMARK: double accesses not yet supported *)
   mstate_err exn_invalid_address.


(* STORE *)
Definition chunk_not_any chunk := (chunk != Many32) && (chunk != Many64).

Definition proc_store (guard:pcond) (chunk:memory_chunk) addr args src
  : mstate gate_number :=
 if (Memdata.align_chunk chunk == Memdata.size_chunk chunk)
    && chunk_not_any chunk
 then doS paddr <- proc_addr addr args;
      doS psrc <- localv_get src;
      match paddr, psrc with
      | (v, inl off), (Some (Some ty),x) =>
          if typ_eq (type_of_chunk chunk) ty
          then doS gconn <- globv_get v;
               doS wguard <- add_gate_guard guard;
               doS wg <- add_gate_updk wguard chunk off gconn x;
               doS _ <- globv_upd v (conn_new wg 0 (conn_size gconn));
               mstate_ret wg
          else mstate_err exn_typerror
      | (v, inr n1), (Some (Some ty),x) =>
          if typ_eq (type_of_chunk chunk) ty
          then doS gconn <- globv_get v;
               let idxconn := conn_new n1 (N.log2 (sizeN_chunk chunk))
                                       (size2idxbits (8*sizeN_chunk chunk)
                                                     (sizeN gconn)) in
               doS gguard <- add_gate_guard guard;
               doS wg <- add_gate_upd gguard chunk gconn idxconn x;
               doS _ <- globv_upd v (conn_new wg 0 (conn_size gconn));
               mstate_ret wg
          else mstate_err exn_typerror
      | _, _ => mstate_err exn_typerror
      end
 else (* REMARK: double accesses not yet supported *)
   mstate_err exn_invalid_address.


(* Processing of phi-nodes *)
Fixpoint proc_phi_conds (l: seq (pcond*positive)) : mstate (typ*gate_number) :=
 match l with
 | [::] => mstate_err exn_malformed_phi
 | [:: (c,p)] => doS pinfo <- localv_get (Pos.pred_N p);
                 if pinfo is (Some (Some ty),gw)
                 then doS wc <- add_gate_guard c;
                      doS gg <- add_gate_ty ty (GbarrierN (wires_of_type ty)) 
                                (wc::conn_ty ty gw);
                      mstate_ret (ty,gg)
                 else mstate_err exn_typerror
 | (c,p)::xs => doS pinfo <- localv_get (Pos.pred_N p);
                if pinfo is (Some (Some ty),gw)
                then doS (t',gr) <- proc_phi_conds xs;
                     if typ_eq ty t'
                     then doS wc <- add_gate_guard c;
                          doS gg <- add_gate_ty ty (GbarrierN (wires_of_type ty)) 
                                     (wc::conn_ty ty gw);
                          doS gx <- add_gate_ty ty (GxorN (wires_of_type ty))
                                     (conn_ty ty gr ++ conn_ty ty gg);
                          mstate_ret (ty,gx)
                     else mstate_err exn_typerror
                else mstate_err exn_typerror
 end.
 
(* Global transformation *)

Definition proc_instr pos (instr: ValCirc.gate) (args: seq ValCirc.wire)
 : mstate unit :=
 match instr with
 | ValCirc.Gop op =>
   match eq_operation op Omove with
   | left EQ =>
    if args is [:: r1]
    then doS (ooty,gw) <- localv_get r1;
         if ooty is Some (Some t)
         then doS newg <- add_gate_unsafe (Gid (wires_of_type t))
                                      (conn_ty t gw);
              localv_set pos (ooty,newg)
         else mstate_err exn_malformed_condv
    else mstate_err exn_typerror
   | right NE =>
    doS (ty,gw) <- proc_op op args;
    localv_set pos (Some (Some ty),gw)
   end
 | ValCirc.Gload chunk addr =>
    doS (ty, gw) <- proc_load chunk addr args;
    localv_set pos (Some (Some ty), gw)
 | ValCirc.Gstore guard chunk addr =>
    if args is src::addr_args
    then doS new_guard <- bdt_ren pos guard;
         doS gw <- proc_store new_guard chunk addr addr_args src;
         localv_set pos (None, gw)
    else mstate_err exn_typerror
 | ValCirc.Gtest guard cond =>
    if gate_of_condition cond is Some gate
    then doS wargs <- args_wires args;
         doS gw <- add_gate_unsafe gate wargs;
         doS new_guard <- bdt_ren pos guard;
         doS wguard <- add_gate_guard new_guard;
         doS gr <- add_gate_and_guard gw wguard;
         localv_set pos (Some None,gr)
    else mstate_err exn_nonsupported_gate
 | ValCirc.Gφ phi =>
     doS new_phi <- bdt_ren pos phi;
     doS (ty,gw) <- proc_phi_conds (flat_phi_node new_phi);
     localv_set pos (Some (Some ty),gw)
 end.

Definition exn_str (e: exn) : Errors.errmsg :=
  match e with
  | exn_initmem_creation =>
      Errors.msg "error during creation of initmem (pointers are not allowed)"
  | exn_condv_notfound =>
      Errors.msg "(internal error) condition variable not found"
  | exn_malformed_condv =>
      Errors.msg "(internal error) malformed condition map"
  | exn_input_wires_mismatch =>
      Errors.msg "(internal error) mismatch on the number of input wires"
  | exn_output_wires_mismatch =>
      Errors.msg "(internal error) mismatch on the number of output wires"
  | exn_globv_notfound =>
      Errors.msg "(internal error) global variable not found"
  | exn_globv_sizemismatch =>
      Errors.msg "(internal error) inconsistent sizes when updating a glob. var."
  | exn_localv_notfound =>
      Errors.msg "(internal error) local variable not found"
  | exn_localv_kinderror =>
      Errors.msg "(internal error) local variable kind error"
  | exn_localv_rewrite =>
      Errors.msg "(internal error) rewrite on local variable (not in SSA)"
  | exn_typerror =>
      Errors.msg "(internal error) type error"
  | exn_invalid_address =>
      Errors.msg "non-supported address"
  | exn_ptr_in_memory =>
      Errors.msg "attempt to write a pointer into global memory"
  | exn_nonsupported_gate =>
      Errors.msg "Not Yet Supported gate"
  | exn_malformed_phi =>
      Errors.msg "(internal error) malformed phi-node"
  | exn_malformed_guard =>
      Errors.msg "(internal error) malformed guard"
  | exn_msg m => m
  end.

Definition exn_msg_at (opos: option N) (e: exn) : exn :=
  let prefix := Errors.MSG "HLCircGen " :: nil in
  let at_msg := 
      if opos is Some pos
      then let pos_msg := if pos is Npos p then Errors.POS p else Errors.MSG "0" in
           Errors.MSG "(at ValCirc gate " :: pos_msg :: Errors.MSG "): " :: nil
      else Errors.MSG ": " :: nil in
  exn_msg (Errors.MSG "HLCircGen " :: at_msg ++ exn_str e).

Fixpoint proc_code pos (code: ValCirc.code) : mstate unit :=
 if code is x::xs
 then doS _ <- mstate_emap (exn_msg_at (Some pos))
                 (proc_instr pos x.(ValCirc.ggate) x.(ValCirc.gwires));
      proc_code (pos+1) xs
 else mstate_ret tt.

Section PROC_OUTPUTS.
Context (gmap: PTree.t globv_info).

Fixpoint proc_outputs (outs: seq (CircIO.slot*ident)) : merror connector :=
 if outs is (x,_)::xs
 then doE c <- globv_getbyte gmap (Psucc x.1) x.2;
      doE cs <- proc_outputs xs;
      merror_ret (c++cs)
 else merror_ret [::].

End PROC_OUTPUTS.

Definition translate_circuit (ninputs: N)
                             (initconsts: seq bytes)
                             (code: ValCirc.code)
                             (outs: seq (CircIO.slot*ident))
 : mstate circuit :=
 doS _ <- proc_code 0 code;
 doS st <- mstate_getstate;
 doS outputs <- mstate_lift_merror (proc_outputs (st_globv st) outs);
 doS code <- get_code;
 mstate_ret {| inputs:= ninputs; initconsts:= initconsts;
               gates:= code; outputs:= outputs |}.

(*
Definition shift_globs (ssz: int) (globs: _) : seq (ident * bytes) :=
  (1%positive, initmem_stack ssz)
    :: map (fun g => (Pos.succ g.1, g.2)) globs.
*)

Definition translate_function (globs: seq (ident*option bytes))
                              (f: ValCirc.function)
  : merror function :=
  doE ssz <-
      let ssz := f.(ValCirc.fn_stacksize) in
      if (if 0 <=? ssz then ssz <=? Int.max_unsigned else false)%Z
      then merror_ret (Int.repr ssz)
      else merror_err exn_initmem_creation;
  doE st <- init_state f.(ValCirc.fn_stacksize) globs 
                       f.(ValCirc.fn_inputs) f.(ValCirc.fn_conditions);
  doE (circ, _) <- translate_circuit (8*sizeN f.(ValCirc.fn_inputs))
                                     (initmem_stack ssz::globs_initdata globs)
                                     f.(ValCirc.fn_body)
                                     f.(ValCirc.fn_outputs)
                                     st;
  merror_ret {| fn_inputs := f.(ValCirc.fn_inputs);
                fn_outputs := map snd f.(ValCirc.fn_outputs);
                fn_stacksize := ssz;
                fn_code := circ
             |}.

Definition translate_fundef (globs: seq (ident*option bytes))
                            (fd: AST.fundef ValCirc.function) 
  : Errors.res (AST.fundef function) :=
  match fd with
  | Internal fn =>
      match translate_function globs fn with
      | inl tf => Errors.OK (Internal tf)
      | inr e => Errors.Error (exn_str e)
      end
  | External ef => Errors.OK (External ef)
  end.

Definition translate_program (p: ValCirc.program)
 : Errors.res program :=
 if collect_globals nil p.(prog_defs) is Some gs
 then transform_partial_program (translate_fundef gs) p
 else Errors.Error (exn_str exn_initmem_creation).
