open Camlcoq
open BinNums
open BinPos
open Datatypes
open Integers
open AST
open Cminor
open CminorSel
open Clflags

open Op
open Printf

(** [chk_labels] checks if the statement has any label *)
let rec chk_labels s =
  match s with
  | Slabel(lbl, s1) -> false
  | Sskip | Sassign _ | Sstore _ 
  | Scall _ | Stailcall _ | Sbuiltin _ | Sexit _ | Sswitch _
  | Sreturn _ | Sgoto _ -> true
  | Sseq(s1,s2) | Sifthenelse(_, s1, s2) -> chk_labels s1 && chk_labels s2
  | Sloop(s1) | Sblock(s1) -> chk_labels s1

let ident_name id = Camlcoq.extern_atom id

let is_some = function
  | Some _ -> true
  | None -> false

let get = function
  | Some x -> x
  | None -> 0.0

(** [just_skips] skips the sequence of instructons with just Sskips *)
let rec just_skips = function
  | Sskip -> true
  | Sseq(s1,s2) -> just_skips s1 && just_skips s2
  | _ -> false


let check_cycle_logic init cond aft =
  let dif = get(cond) -. get(init) in
    ( dif >= 0.0 && get(aft) >= 0.0 ) || ( dif <= 0.0 && get(aft) <= 0.0 )
    
    
(** [prediction] calculate the number of unrolls given the parameters *)
let prediction init cond aft =
  let dif = get(cond) -. get(init) in
    ceil(abs_float(dif) /. abs_float(get(aft)))
    

(** [find_assign] find in the instructons before the loop any assignment to the variable desired*)
let find_assign name acc var =
  let rec aux_find acc = 
    match acc with
    | Sseq(s1,s2) when just_skips s1 && just_skips s2 -> ()
    | Sseq(s1,s2) when just_skips s1 -> aux_find s2
    | Sseq(s1,s2) when just_skips s2 -> aux_find s1
    | Sseq(s1,s2) -> aux_find s2; 
                     aux_find s1
    | Sblock(s1) -> aux_find s1 
    | Sassign(id, e) -> if name = id && not(is_some(!var))
                        then (match e with
                             | Eop(op, e) -> (match op with
                                             | Ointconst i -> var := Some (Int32.to_float(camlint_of_coqint i))  (*case: i = const *)
                                             | Ofloatconst i -> var := Some (camlfloat_of_coqfloat i)
                                             | _ -> var := None)
                             | _ -> var := None)
    | _ -> ()
  in aux_find acc


(** [get_after_instrution] get th value of increment /decrement*)
let rec get_after_instrution = function
  | Ointconst i -> Some (Int32.to_float(camlint_of_coqint i)) (*case: i++ *)
  | Ofloatconst i -> Some (camlfloat_of_coqfloat i)
  | Olea add -> (match add with
                | Aindexed i -> Some (Int32.to_float(camlint_of_coqint i))   (* i = i -1*)
                | _ -> None)
  | _ -> None


(** [get_condition] match to many types of conditions *)
let get_condition = function
  | Ccompimm(c1,c2)  
  | Ccompuimm(c1,c2) -> (match c1 with
                        | Ceq 
                        | Cne -> None
                        | Clt 
                        | Cgt -> Some (Int32.to_float(camlint_of_coqint c2))
                        | Cle -> Some (Int32.to_float(Int32.add (camlint_of_coqint c2) (Int32.of_int(1))))
                        | Cge -> Some (Int32.to_float(Int32.sub (camlint_of_coqint c2) (Int32.of_int(1))))
                        ) 
  | Ccomp c1 
  | Ccompu c1 -> (match c1 with
                        | Ceq 
                        | Cne -> None
                        | Clt 
                        | Cgt -> Some (Int32.to_float(Int32.of_int(0)))
                        | Cle -> Some (Int32.to_float(Int32.of_int(1)))
                        | Cge -> Some (Int32.to_float(Int32.of_int(-1)))
                        )
  | _ -> None


(** [eval_cond] get the condition expression and tries to extract the value of the condition and inicialization *)
let eval_cond e cond init namevar acc =
  let aux = ref None and aux2 = ref None in 
    match e with
        | CEcond(c,esp) -> (cond := get_condition c; 
                            aux := !cond;
                            match esp with
                            | Enil -> ()
                            | Econs(e1,t) -> (match e1 with
                                              | Evar(i) -> namevar := (ident_name i);  
                                                           find_assign i acc init 
                                              | _ -> init := None);
                                              if (is_some(!cond))
                                              then
                                                (match t with
                                                | Enil -> ()
                                                | Econs(e,es) -> (match e with
                                                                  | Evar(i) -> (find_assign i acc aux2; 
                                                                                cond := Some (get(!aux2) +. get(!aux)))  
                                                                  | _ -> cond := None)))
        | _ -> cond := None


(** [loop_unroll_oracle] tries to predict the level of unrolling, if it is not possible return None*)
let loop_unroll_oracle n acc s =
  let init = ref None and cond = ref None and after = ref None and namevar = ref "" and cond_evaluated = ref false in 
    let rec aux_oracle n acc s =
       match s with
        | Sseq(s1,s2) when just_skips s1 && just_skips s2 -> ()
        | Sseq(s1,s2) when just_skips s1 -> aux_oracle n acc s2 
        | Sseq(s1,s2) when just_skips s2 -> aux_oracle n acc s1
        | Sseq(s1,s2) -> aux_oracle n acc s1;
                         aux_oracle n acc s2                 
        | Sblock(s) 
        | Sloop(s) -> aux_oracle n acc s
        | Sifthenelse(e, s1, s2) -> if (not !cond_evaluated) 
                                    then (cond_evaluated := true; 
                                          eval_cond e cond init namevar acc)
        | Sassign(id, Eop(op, e)) -> if is_some(!init) && (ident_name id = !namevar) 
                                     then (if (not (is_some(!after)))
                                           then after := get_after_instrution op
                                           else init := None)
        | Sassign(id, _) -> if is_some(!init) && (ident_name id = !namevar)    
                            then init := None 
        | _ -> ()
      in
        aux_oracle n acc s;
        
        if (!option_floop_unroll_infer && is_some(!init) && is_some(!cond) && is_some(!after) 
            && check_cycle_logic !init !cond !after)        
        then (printf "Loop unroll_estimates as: %d\n" (int_of_float(prediction !init !cond !after)); 
              Some (prediction !init !cond !after))
        else (printf "Estimation not possible Default value assigned \n"; 
              None)



(** [fix_unroll_stmt] assigns to each loop a fixed number (or 0, if
 the loop body has any label). *)
let fix_unroll_stmt n s p = 
  let rec rev_pos acc = function
    | Coq_xO p -> rev_pos (Coq_xO acc) p
    | Coq_xI p -> rev_pos (Coq_xI acc) p
    | Coq_xH -> acc
  and aux_stmt acc s p =
    match p with
    | Coq_xH -> if chk_labels s
(* REMARK: disable LOOP_UNROLL_INFERENCE (for now, at least!) *)
                then ( let res = None (*loop_unroll_oracle n acc s*) in 
                          if is_some(res)
                          then Nat.of_int(int_of_float(get(res)))
                          else n )
                else ((*printf "\nLoopUnroll: blocked expansion of loop due to the presence of labels.\n";*) n)
    | Coq_xO p' -> (match s with
                   | Sseq(s1,_) 
                   | Sifthenelse(_,s1,_)  
                   | Sloop(s1) -> aux_stmt acc s1 p'
                   | Sblock(s) | Slabel(_,s) -> aux_stmt acc s p
                   | _ -> printf "\nLoopUnroll_estimates: this should never happend!!\n\n"; O)
    | Coq_xI p' -> (match s with
                   | Sseq(s1,s2)
                   | Sifthenelse(_, s1, s2) -> aux_stmt (Sseq(acc,s1)) s2 p'
                   | Sblock(s) | Slabel(_,s) -> aux_stmt acc s p
                   | _ -> printf "\nLoopUnroll_estimates: this should never happend!!\n\n"; O)
  in aux_stmt Sskip s (rev_pos Coq_xH p)

let loop_unroll_bounds = ref (None: (int list) option)

let unroll_estimates (f:stmt) (pos: Pos.t) : nat =
  let n = Nat.of_int !option_floop_unroll in
  match !Clflags.pragma_loop_unroll with
  | Some l -> (* some "#pragma loop_unroll" was used! these bound take precedence! *)
     begin
       (match !loop_unroll_bounds with
	| None -> loop_unroll_bounds := Some (List.rev l)
	| Some _ -> ());
       match !loop_unroll_bounds with
       | Some [] -> printf "\nLoopUnroll_estimates: not enough \"#pragma loop_unroll\" directives!! (using default value)"; n
       | Some (x::xs) -> loop_unroll_bounds := Some xs;
         (if x <= 0 then n else Nat.of_int x)
       | None -> printf "\nLoopUnroll_estimates: this should never happend!!\n\n"; O
     end
  | None -> fix_unroll_stmt n f pos


