(*open Camlcoq
open Hlcirc_def*)
open Mlcirc

let log2 x =
 let i = ref 0
 and y = ref x in
 while !y != 0 do
   i := !i+1;
   y := !y lsr 1
 done;
 !i
let log2_up x = log2 (x-1)
let size2idxbits size width = log2_up (size/width) (*max 1 (log2_up size)*)



(** * Wire gates *)
let g_id_n n = mkhlgate "id" [n] n n
let gc_id_n n = { hlcin = [n]
		; hlcgates = []
		; hlcout = sub_conn 1 0 n
		}
		  
let g_constint_n_c n c = mkhlgate "constint_N_C" [n; c] 0 n
let gc_constint_n_c n c =
  let cbits = List.map (fun b->(0, if b then 1 else 0)) (bits_of_int n c)
  in { hlcin = []
     ; hlcgates = []
     ; hlcout = cbits
     }

let g_constbytes_l bytes =
  mkhlgate "constbytes" bytes 0 (8 * List.length bytes)
let gc_constbytes l =
  match l with
  | [] -> { hlcin = [] ; hlcgates = []; hlcout = [] }
  | [x] -> { hlcin = []
	   ; hlcgates = [ g_constint_n_c 8 x, [] ]
	   ; hlcout = sub_conn 1 0 8
	   }
  | x::xs -> { hlcin = []
	     ; hlcgates = [ g_constint_n_c 8 x, []
			  ; g_constbytes_l xs, []
			  ]
	     ; hlcout = sub_conn 1 0 8 @ sub_conn 2 0 (8*List.length xs)
	     }

let g_selk width size pos =
  mkhlgate "selk_W_S_P" [width; size; pos] size width
let gc_selk width size pos = (* pos is bit position *)
  { hlcin = [size]
  ; hlcgates = []
  ; hlcout = sub_conn 1 pos width
  }


(** * Logical gates *)

let g_NOT = mkhlgate "NOT" [] 1 1
let gc_NOT = { hlcin = [1]
	     ; hlcgates = [(g_XOR, [(1,0);(0,1)])]
	     ; hlcout = [(2,0)]
	     }

let g_cond1 = mkhlgate "cond1" [] 3 1
let gc_cond1 = { hlcin = [1;2]
	       ; hlcgates = [(g_XOR, [(2,0); (2,1)])
			    ;(g_AND, [(1,0); (3,0)])
			    ;(g_XOR, [(2,1); (4,0)])
			    ]
	       ; hlcout = [(5,0)]
	       }
let chk_cond1 input output =
  match split_sizes [1;1;1] input with
  | [c;x1;x2] ->
     let y = if c = [true] then x1 else x2 in
     if not (y = output)
     then Printf.fprintf stdout 
			 ("ERROR cond1 [%a %a %a]\n  expected: %a\n  obtained: %a\n")
			 bits_pp c bits_pp x1 bits_pp x2 
			 bits_pp y
			 bits_pp output;
     ()
  | _ -> assert false

let g_OR = mkhlgate "OR" [] 2 1
let gc_OR = { hlcin = [1;1]
	    ; hlcgates = [ g_cond1, [(1,0);(0,1);(2,0)] ]
	    ; hlcout = [(3,0)]
	    }

(* n_input version of a BINARY gate *)
let rec gc_n_bingate gate n =
  assert (n>0);
  if n=1
  then gc_id_n 1
  else let aux = gc_n_bingate gate (n-1) in
       { hlcin = 1::aux.hlcin
       ; hlcgates = offset_gates 1 aux.hlcgates
		    @ [(gate, (1,0)::(offset_wires 1 aux.hlcout))]
       ; hlcout = [(2 + gc_lastg aux, 0)]
       }

(* parallel n_wire version of a BINARY gate *)
let g_n_bingate gate n =
  mkhlgate ("N_" ^ gate.hlgname) [n] n 1
let rec gc_bingate_n gate n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1]
       ; hlcgates = [(gate, [(1,0); (2,0)])]
       ; hlcout = [(3,0)]
       }
  else let aux = gc_bingate_n gate (n-1) in
       { hlcin = [n; n]
       ; hlcgates = aux.hlcgates
		    @ [(gate, [(1,n-1); (2,n-1)])]
       ; hlcout = aux.hlcout @ [(1+gc_lastg aux,0)]
       }

let g_bingate_n gate n =
  mkhlgate (gate.hlgname ^ "_N") [n] (2*n) n

let gc_n_and n = gc_n_bingate g_AND n
let gc_n_xor n = gc_n_bingate g_XOR n
let gc_and_n n = gc_bingate_n g_AND n
let gc_xor_n n = gc_bingate_n g_XOR n
let gc_or_n n = gc_bingate_n g_OR n

let g_n_and n = g_n_bingate g_AND n
let g_n_xor n = g_n_bingate g_XOR n
let g_and_n n = g_bingate_n g_AND n
let g_xor_n n = g_bingate_n g_XOR n
let g_or_n n = g_bingate_n g_OR n

let g_not_n n = mkhlgate "not_N" [n] n n
let rec gc_not_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1]
       ; hlcgates = [(g_XOR, [(0,1); (1,0)])]
       ; hlcout = [(2,0)]
       }
  else let aux = gc_not_n (n-1) in
       { hlcin = [n]
       ; hlcgates = aux.hlcgates
		    @ [(g_XOR, [(0,1);(1,n-1)])]
       ; hlcout = aux.hlcout @ [(1+gc_lastg aux,0)]
       }

(* parallel n_wire version of a BARRIER gate *)
let g_barrier_n n = mkhlgate "barrier_N" [n] (1+n) n
let rec gc_barrier_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1]
       ; hlcgates = [(g_AND, [(1,0); (2,0)])]
       ; hlcout = [(3,0)]
       }
  else { hlcin = [1; n]
       ; hlcgates = 
	   [ g_AND, [(1,0); (2,0)]
	   ; g_barrier_n (n-1), (1,0)::sub_conn 2 1 (n-1)
	   ; 
	   ]
       ; hlcout = (3,0)::sub_conn 4 0 (n-1)
       }

(* parallel n_wire version of a COND gate *)
let g_cond_n n = mkhlgate "cond_N" [n] (1+2*n) n
let rec gc_cond_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1; 1]
       ; hlcgates = [(g_cond1, [(1,0); (2,0); (3,0)])]
       ; hlcout = [(4,0)]
       }
  else { hlcin = [1; n; n]
       ; hlcgates = [ g_cond_n (n-1), 
		      (1,0)::(sub_conn 2 0 (n-1)
			      @ sub_conn 3 0 (n-1))
		    ; g_cond1, [(1,0); (2,n-1); (3,n-1)]
		    ]
       ; hlcout = (sub_conn 4 0 (n-1)) @ [(5,0)]
       }

let chk_cond_n input output =
  let size = (List.length input -1) / 2 in
  match split_sizes [1;size;size] input with
  | [c;x1;x2] ->
     let y = if c = [true] then x1 else x2 in
     if not (y = output)
     then Printf.fprintf stdout 
			 ("ERROR cond_n [%a %a %a]\n  expected: %a\n  obtained: %a\n")
			 bits_pp c bits_pp x1 bits_pp x2 
			 bits_pp y
			 bits_pp output;
     ()
  | _ -> assert false

let g_updk width size pos =
  mkhlgate "updk_W_S_P" [width; size; pos] (1 + width + size) size
let gc_updk width size pos = (* pos in bits *)
  if width <= 0 || pos < 0 || size < pos+width
  then internal_error
	 (msg "gc_updk: wrong parameters (width=%d; size=%d; pos=%d)\n"
	      width pos size)
  else
    { hlcin = [1;width;size]
    ; hlcgates = [ g_cond_n width, (1,0)::sub_conn 2 0 width @ sub_conn 3 pos width ]
    ; hlcout = sub_conn 3 0 pos @ sub_conn 4 0 width 
	       @ sub_conn 3 (pos+width) (size-pos-width)
    }
 

(** * Arithmetic gates *)
let g_fulladder1 = mkhlgate "fulladder1" [] 3 2
let gc_fulladder1 =
  { hlcin = [1;1;1] (* cIN, aIN, bIN *)
  ; hlcgates = [ g_XOR, [(2,0);(1,0)]
	       ; g_XOR, [(3,0);(1,0)]
	       ; g_XOR, [(2,0);(5,0)]
	       ; g_AND, [(4,0);(5,0)]
	       ; g_XOR, [(1,0);(7,0)]
	       ]
  ; hlcout = [(8,0);(6,0)] (* carryOUT, bOUT *)
  }

let g_halfadder1 = mkhlgate "halfadder1" [] 3 1
let gc_halfadder1 =
  { hlcin = [1;1;1] (* cIN, aIN, bIN *)
  ; hlcgates = [ g_XOR, [(3,0);(1,0)]
	       ; g_XOR, [(2,0);(4,0)]
	       ]
  ; hlcout = [(5,0)] (* bOUT *)
  }
(* obs: não faz sentido estar com estas chatices do halfadder! A verdade 
é que o halfadder implementado a partir do fulladder fica igualmente bom
por causa das optimizações realizadas. O circuito seguinte permite confirmar
isso mesmo... 
   gc_xpnd gc_halfadder1;;
   gc_xpnd gc_halfadder1_new;;
*)
let gc_halfadder1_new =
  { hlcin = [1;1;1] (* cIN, aIN, bIN *)
  ; hlcgates = [ g_fulladder1, [(1,0);(2,0);(3,0)] ]
  ; hlcout = [(4,1)] (* bOUT *)
  }

let g_fulladder_n n =
  mkhlgate "fulladder_N" [n] (1+2*n) (1+n)
let rec gc_fulladder_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1; 1]
       ; hlcgates = [(g_fulladder1, [(1,0); (2,0); (3,0)])]
       ; hlcout = [(4,0);(4,1)]
       }
  else { hlcin = [1;n;n]
       ; hlcgates = [ g_fulladder_n (n-1),
		      (1,0)::(sub_conn 2 0 (n-1) @ sub_conn 3 0 (n-1))
		    ; g_fulladder1, [(4,0);(2,n-1);(3,n-1)]
		    ]
       ; hlcout = (5,0)::(sub_conn 4 1 (n-1) @ [(5,1)])
       }

let g_int_add_n n =
  mkhlgate "int_add_N" [n] (2*n) n
let rec gc_int_add_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1]
       ; hlcgates = [(g_halfadder1, [(0,0); (1,0); (2,0)])]
       ; hlcout = [(3,0)]
       }
  else { hlcin = [n;n]
       ; hlcgates = [ g_fulladder_n (n-1),
		      (0,0)::(sub_conn 1 0 (n-1) @ sub_conn 2 0 (n-1))
		    ; g_halfadder1, [(3,0);(1,n-1);(2,n-1)]
		    ]
       ; hlcout = sub_conn 3 1 (n-1) @ [(4,0)]
       }

let chk_int_add_n input output =
  let size = (List.length input)/2 in
  let [x1;x2] = split_sizes [size;size] input in
  let n1 = uint_of_bits x1
  and n2 = uint_of_bits x2 in
  let y = bits_of_int size (n1+n2) in
  let nout = uint_of_bits output in
  if not (y = output)
  then Printf.fprintf stdout 
	("ERROR int_add [%a] (%d+%d)\n  expected (%d): %a\n  obtained (%d): %a\n")
	bits_pp input n1 n2 
	((n1+n2) mod (1 lsl size)) bits_pp y 
	nout bits_pp output;
  ()



let g_addimm_n_c n c =
  mkhlgate "addimm_N_C" [n;c] n n
let gc_addimm_n_c n c =
  { hlcin = [n]
  ; hlcgates = [ g_constint_n_c n c, []
	       ; g_int_add_n n, sub_conn 1 0 n @ sub_conn 2 0 n
	       ]
  ; hlcout = sub_conn 3 0 n
  }
let chk_addimm_n_c c input output =
  let size = (List.length input) in
  let x = uint_of_bits input in
  let y = bits_of_int size (x+c) in
  let nout = uint_of_bits output in
  if not (y = output)
  then Printf.fprintf stdout 
	("ERROR addimm [%a] (%d+%d)\n  expected (%d): %a\n  obtained (%d): %a\n")
	bits_pp input x c
	((x+c) mod (1 lsl size)) bits_pp y 
	nout bits_pp output;
  ()


let g_neg_n n =
  mkhlgate "neg_N" [n] n n
let gc_neg_n n =
  { hlcin = [n]
  ; hlcgates = [ g_not_n n, sub_conn 1 0 n
	       ; g_addimm_n_c n 1, sub_conn 2 0 n
	       ]
  ; hlcout = sub_conn 3 0 n
  }


let g_mul1 =
  mkhlgate "mul1" [] 4 2
let gc_mul1 =
  { hlcin = [1;1;1;1] (* cIN; sumIN; X; Y *)
  ; hlcgates = [ g_AND, [(3,0);(4,0)]
	       ; g_fulladder1, [(1,0);(2,0);(5,0)]
	       ]
  ; hlcout = [(6,1);(6,0)] (* sumOUT; cOUT *)
  }

(* row in a multiplication matrix... *)
let g_mulrow_n n =
  mkhlgate "mulrow_N" [n] (n+n+1 (* S0..; X0..; Yk *)) (n+1 (* S0..; C *))
let gc_mulrow_n n =
  assert (n>0);
  if n = 1
  then { hlcin = [n; n; 1]
       ; hlcgates = [ g_mul1, [(0,0);(1,0);(2,0);(3,0)] ]
       ; hlcout = [(4,0);(4,1)]
       }
  else { hlcin = [n;n;1]
       ; hlcgates = [ g_mulrow_n (n-1), sub_conn 1 0 (n-1)
					@ sub_conn 2 0 (n-1)
					@ [(3,0)]
		    ; g_mul1, [(4,n-1);(1,n-1);(2,n-1);(3,0)]
		    ]
       ; hlcout = sub_conn 4 0 (n-1) @ [(5,0);(5,1)]
       }

(* M multiplication rows of a N bit unsigned multiplier matrix *)
let g_mulumat_n_m n m =
  mkhlgate "mulumat_N_M" [n;m] (n+m) ((n+m-1)+1) (* sOUT + cOUT*)
let gc_mulumat_n_m n m =
  assert (n>0 && m>0);
  if m = 1
  then { hlcin = [n;1]
       ; hlcgates = [ g_barrier_n n, (2,0)::sub_conn 1 0 n ]
       ; hlcout = sub_conn 3 0 n @ [(0,0)]
       }
  else { hlcin = [n;m]
       ; hlcgates = [ g_mulumat_n_m n (m-1),
		      sub_conn 1 0 n 			(* X *)
		      @ sub_conn 2 0 (m-1)		(* Y *)
		    ; g_mulrow_n n, 
		      sub_conn 3 (m-1) n 		(* sumIN *)
		      @ sub_conn 1 0 n			(* X *)
		      @ [(2,m-1)]			(* Yk *)
		    ]
       ; hlcout = sub_conn 3 0 (m-1) @ sub_conn 4 0 n	(* sumOUT *)
		  @ [(4,n)]				(* cOUT *)
       }

let g_fullmulu_n n  =
  mkhlgate "fullmulu_N" [n] (2*n) (2*n)
let gc_fullmulu_n n =
  { hlcin = [n;n]
  ; hlcgates = [ g_mulumat_n_m n n, sub_conn 1 0 n @ sub_conn 2 0 n ]
  ; hlcout = sub_conn 3 0 (2*n)
  }
let chk_fullmulu_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = uint_of_bits x1
     and n2 = uint_of_bits x2 in
     let y = bits_of_int (2*size) (n1*n2) in
     let nout = uint_of_bits output in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR fullmulu [%a] (%d*%d)\n  expected (%d): %a\n  obtained (%d): %a\n")
	bits_pp input n1 n2 
	(n1*n2) bits_pp y 
	nout bits_pp output;
     ()
  | _ -> assert false

(* Booth-encoding: preciso de pensar melhor isto!!!
 ºrovavelmente será de dispensar g_mul1 e implementar de raiz a matriz de
 multiplicação a partir de fulladders...


(* M multiplication rows of a N bit signed multiplier matrix *)
let g_mulsmat_n_m n m =
  { hlgname = "mulsmat_N_M"
  ; hlgargs = [n;m]
  ; hlgin = n+m
  ; hlgout = (n+m-1)+1 (* sOUT + cOUT*)
  }
let gc_mulsmat_n_m n m =
  assert (n>0 && m>0);
  if m = 1
  then { hlcin = [n;1]
       ; hlcgates = [ g_barrier_n n, (2,0)::sub_conn 1 0 n
		    ; g_NOT, [(3,n-1)]
		    ]
       ; hlcout = sub_conn 3 0 n @ [(0,0)]
       }
  else { hlcin = [n;m]
       ; hlcgates = [ g_mulsmat_n_m n (m-1),
		      sub_conn 1 0 n 			(* X *)
		      @ sub_conn 2 0 (m-1)		(* Y *)
		    ; g_mulrow_n n, 
		      sub_conn 3 (m-1) n 		(* sumIN *)
		      @ sub_conn 1 0 n			(* X *)
		      @ [(2,m-1)]			(* Yk *)
		    ]
       ; hlcout = sub_conn 3 0 (m-1) @ sub_conn 4 0 n	(* sumOUT *)
		  @ [(4,n)]				(* cOUT *)
       }

let g_fullmuls_n n  =
  { hlgname = "fullmuls_N"
  ; hlgargs = [n]
  ; hlgin = 2*n
  ; hlgout = 2*n
  }
let gc_fullmuls_n n =
  { hlcin = [n;n]
  ; hlcgates = [ g_mulsmat_n_m n n, sub_conn 1 0 n @ sub_conn 2 0 n ]
  ; hlcout = sub_conn 3 0 (2*n)
  }
let chk_fullmuls_n input output =
  let size = (List.length input)/2 in
  let [x1;x2] = split_sizes [size;size] input in
  let n1 = sint_of_bits x1
  and n2 = sint_of_bits x2 in
  let y = bits_of_int (2*size) (n1*n2) in
  let nout = sint_of_bits output in
  if not (y = output)
  then Printf.fprintf stdout 
	("ERROR fullmuls [%a] (%d*%d)\n  expected (%d): %a\n  obtained (%d): %a\n")
	bits_pp input n1 n2 
	(n1*n2) bits_pp y 
	nout bits_pp output;
  ()

 *)

(** * Comparison gates *)
let g_neq1 = mkhlgate "neq1" [] 2 1
let gc_neq1 = { hlcin = [1;1]
	      ; hlcgates = [(g_XOR, [(1,0);(2,0)])]
	      ; hlcout = [(3,0)]
	      }

let g_eq1 = mkhlgate "eq1" [] 2 1
let gc_eq1 = { hlcin = [1;1]
	     ; hlcgates = [(g_neq1, [(1,0);(2,0)])
			  ;(g_NOT, [(2,0)])
			  ]
	     ; hlcout = [(3,0)]
	     }

let g_neq_n n = mkhlgate "neq_N" [n] (2*n) 1
let rec gc_neq_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1;1]
       ; hlcgates = [(g_XOR, [(1,0); (2,0)])]
       ; hlcout = [(3,0)]
       }
  else { hlcin = [n;n]
       ; hlcgates = [ g_neq_n (n-1), sub_conn 1 0 (n-1) @ sub_conn 2 0 (n-1)
		    ; g_XOR, [(1,n-1); (2,n-1)]
		    ; g_cond1, [(4,0);(0,1);(3,0)]
		    ]
       ; hlcout = [(5,0)]
       }

let chk_neq_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let y = [not (x1=x2)] in
     if not (y = output)
     then Printf.fprintf stdout 
			 ("ERROR neq_n [%a %a]\n  expected: %a\n  obtained: %a\n")
			 bits_pp x1 bits_pp x2 
			 bits_pp y 
			 bits_pp output;
     ()
  | _ -> assert false

let g_eq_n n = mkhlgate "eq_N" [n] (2*n) 1
let rec gc_eq_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1;1]
       ; hlcgates = [ g_XOR, [(1,0); (2,0)]
		    ; g_XOR, [(3,0);(0,1)]
		    ]
       ; hlcout = [(4,0)]
       }
  else { hlcin = [n;n]
       ; hlcgates = [ g_eq_n (n-1), sub_conn 1 0 (n-1) @ sub_conn 2 0 (n-1)
		    ; g_XOR, [(1,n-1); (2,n-1)]
		    ; g_cond1, [(4,0);(0,0);(3,0)]
		    ]
       ; hlcout = [(5,0)]
       }


let chk_eq_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let y = [x1=x2] in
     if not (y = output)
     then Printf.fprintf stdout 
			 ("ERROR eq_n [%a %a]\n  expected: %a\n  obtained: %a\n")
			 bits_pp x1 bits_pp x2 
			 bits_pp y 
			 bits_pp output;
     ()
  | _ -> assert false

let g_subsel_w_n w n = (* width, number of cells *)
  mkhlgate "subsel_W_N" [w;n] (n+w*n) w
let rec gc_subsel_w_n w n =
  assert (n>0 && w>0);
  if n=1
  then { hlcin = [1; w]
       ; hlcgates = [g_barrier_n w, (1,0)::(sub_conn 2 0 w)]
       ; hlcout = sub_conn 3 0 w
       }
  else { hlcin = [n; n*w]
       ; hlcgates = [ g_subsel_w_n w (n-1), 
		      sub_conn 1 0 (n-1) @ sub_conn 2 0 (w*(n-1)) 
		    ; g_barrier_n w, (1,n-1)::sub_conn 2 (w*(n-1)) w
		    ; g_xor_n w, sub_conn 3 0 w @ sub_conn 4 0 w
		    ]
       ; hlcout = sub_conn 5 0 w
       }

(** DECODER *)
let rec g_dec_n n =
  mkhlgate "dec_N" [n] (1+n (* en + index *)) (1 lsl n (* decoded output *))
let rec gc_dec_n n = 
  assert (n>0);
  if n=1
  then { hlcin = [1;1] (* enabler; bit *)
       ; hlcgates = [ g_AND, [(1,0);(2,0)]
		    ; g_XOR, [(1,0);(3,0)]
		    ]
       ; hlcout = [(4,0);(3,0)]
       }
  else { hlcin = [1;n]
       ; hlcgates = [ g_AND, [(1,0);(2,n-1)]
		    ; g_XOR, [(1,0);(3,0)]
		    ; g_dec_n (n-1), (4,0)::sub_conn 2 0 (n-1)
		    ; g_dec_n (n-1), (3,0)::sub_conn 2 0 (n-1)
		    ]
       ; hlcout = sub_conn 5 0 (1 lsl (n-1)) @ sub_conn 6 0 (1 lsl (n-1))
       }

(*
   w - width in bits
   i - indexvwidth in bits
   n - number of elements
 *)
let rec g_sel_w_n w n =
  mkhlgate "sel_W_N" [w;n] ((size2idxbits  n w)+n (* index-bits + data*)) w
let rec gc_sel_w_n w size = 
  assert (w>0 && size>0 && size mod w = 0);
  { hlcin = [size; size2idxbits size w] (* enabler; data *)
  ; hlcgates = [ g_dec_n (size2idxbits size w), 
		 (0,1)::sub_conn 2 0 (size2idxbits size w)
	       ; g_subsel_w_n w (size/w),
		 sub_conn 3 0 (size/w) @ sub_conn 1 0 size
	       ]
  ; hlcout = sub_conn 4 0 w
  }
  
(* byte oriented selection (remark: indexed element does not need to be
  aligned with element width) *)
(*
   w - width in bytes
   i - byte-index width in bits
   n - number of bytes
 *)
(*
let g_bsel_w_n w n =
  { hlgname = "bsel_W_N"
  ; hlgargs = [w;n]
  ; hlgin = 1+(size2idxbits n)+8*n (* en + index-bits + data*)
  ; hlgout = 8*w (* output *)
  }
let g_subbsel_w_n w n =
  { hlgname = "subbsel_W_N"
  ; hlgargs = [w;n]
  ; hlgin = n+8*n
  ; hlgout = 8*w
  }
let rec gc_subbsel_w_n w n = 
  assert (w>0 && n>=w);
  if w=1
  then { hlcin = [n;8*n] (* enabler; data *)
       ; hlcgates = [ g_subsel_w_n 8 n, sub_conn 1 0 n @ sub_conn 2 0 (8*n)
		    ]
       ; hlcout = sub_conn 3 0 8
       }
  else { hlcin = [n;8*n] (* enabler; data *)
       ; hlcgates = [ g_subsel_w_n 8 n, sub_conn 1 0 n @ sub_conn 2 0 (8*n)
		    ; g_subbsel_w_n (w-1) n, (0,0)::sub_conn 1 0 (n-1)
					     @ sub_conn 3 0 (8*n)
		    ]
       ; hlcout = sub_conn 3 0 8 @ sub_conn 4 0 (8*(w-1))
       }
let rec gc_bsel_w_n w n = 
  assert (w>0 && n>0);
  { hlcin = [1;(size2idxbits n);8*n] (* enabler; index; data *)
  ; hlcgates = [ g_dec_n (size2idxbits n), (1,0)::sub_conn 2 0 (size2idxbits n)
	       ; g_subbsel_w_n w n, sub_conn 4 0 n @ sub_conn 3 0 (8*n)
	       ]
  ; hlcout = sub_conn 5 0 (8*w)
  }  
 *)

let g_subupd_w_n w n = (* width, number of cells *)
  mkhlgate "subupd_W_N" [w;n] (n+w+w*n (* cells, width, size *)) (w*n)
let rec gc_subupd_w_n w n =
  assert (n>0 && w>0);
  if n=1
  then { hlcin = [1; w; w]
       ; hlcgates = [g_cond_n w, (1,0)::sub_conn 2 0 w @ sub_conn 3 0 w]
       ; hlcout = sub_conn 4 0 w
       }
  else { hlcin = [n; w; n*w]
       ; hlcgates = [ g_subupd_w_n w (n-1), 
		      sub_conn 1 0 (n-1) @ sub_conn 2 0 w
		      @ sub_conn 3 0 (w*(n-1)) 
		    ; g_cond_n w, (1,n-1)::(sub_conn 2 0 w
				  	    @ sub_conn 3 (w*(n-1)) w)
		    ]
       ; hlcout = sub_conn 4 0 (w*(n-1)) @ sub_conn 5 0 w
       }
(*
   w - width in bits
   i - indexvwidth in bits
   n - number of elements
 *)
let rec g_upd_w_n w n =
  mkhlgate "upd_W_N" [w;n] (1+w+(size2idxbits n w)+n(*en+val+idx+data*)) n
let rec gc_upd_w_n w n = 
  assert (w>0 && n>0);
  { hlcin = [1;w;n;size2idxbits n w] (* en + value + index-bits + data*)
  ; hlcgates = [ g_dec_n (size2idxbits n w), (1,0)::sub_conn 4 0 (size2idxbits n w)
	       ; g_subupd_w_n w (n/w), sub_conn 5 0 (n/w) 
				       @ sub_conn 2 0 w @ sub_conn 3 0 n
	       ]
  ; hlcout = sub_conn 6 0 n
  }

(*
   w - width in bytes
   i - index width in bits
   n - number of bytes
 *)
(*
let rec g_bupd_w_n w n =
  { hlgname = "bupd_W_N"
  ; hlgargs = [w;n]
  ; hlgin = 1+8*w+(size2idxbits n)+8*n (* en + value + index-bits + data*)
  ; hlgout = 8*n (* output *)
  }
let g_subbupd_w_n w n =
  { hlgname = "subbupd_W_N"
  ; hlgargs = [w;n]
  ; hlgin = 8*w+n+8*n
  ; hlgout = 8*n
  }
let rec gc_subbupd_w_n w n = 
  assert (w>0 && n>=w);
  if w=1
  then { hlcin = [1;8*w;n;8*n] (* pc; value; enabler; data *)
       ; hlcgates = [ g_subupd_w_n 8 n, (1,0)::sub_conn 3 0 n
					@ sub_conn 2 0 (8*w) @ sub_conn 4 0 (8*n)
		    ]
       ; hlcout = sub_conn 5 0 (8*n)
       }
  else { hlcin = [1;8*w;n;8*n] (* pc; value; enabler; data *)
       ; hlcgates = [ g_subupd_w_n 8 n, (1,0)::sub_conn 3 0 n
					@ sub_conn 2 0 8 @ sub_conn 4 0 (8*n)
		    ; g_subbupd_w_n (w-1) n, (1,0)::(0,0)::sub_conn 3 0 (n-1)
					     @ sub_conn 2 8 (8*(w-1)) 
					     @ sub_conn 5 0 (8*n)
		    ]
       ; hlcout = sub_conn 5 0 8 @ sub_conn 6 0 (8*(w-1))
       }
let rec gc_bupd_w_n w n = 
  assert (w>0 && n>=w);
  { hlcin = [1;8*w;(size2idxbits n);w*n] (* enabler; data *)
  ; hlcgates = [ g_dec_n (size2idxbits n), (1,0)::sub_conn 3 0 (size2idxbits n)
	       ; g_subupd_w_n w n, (1,0)::sub_conn 2 0 (8*w)
				   @ sub_conn 5 0 n @ sub_conn 4 0 (8*n)
	       ]
  ; hlcout = sub_conn 6 0 (8*n)
  }
 *)




(* SIGNED COMPARISONS:

  implemented with one's complement and addition

  x <= y == x-y <= 0 == x+NEG(y)+1 <= 0 == x+NEG(y) < 0 == SIGN(x+NEG(y))

  x > y == NOT(SIGN(x+NEG(y)))

  argument swap:

  x >= y == SIGN(y+NEG(x))

  x < y == NOT(SIGN(y+NEG(x)))


  Note however that, to avoid overflows, we need to perform additions/neg over
  n+1 bits...
 *)
let g_sint_le_n n = mkhlgate "sint_le_N" [n] (2*n) 1
let gc_sint_le_n n =
  assert (n>0);
  { hlcin = [n;n]
  ; hlcgates = [ g_not_n (n+1), sub_conn 2 0 n @ [(2,n-1)]
	       ; g_int_add_n (n+1), sub_conn 1 0 n @ [(1,n-1)] @ sub_conn 3 0 (n+1)
	       ]
  ; hlcout = [(4,n)] (* sign bit (addition of (n+1) bits *)
  }
let chk_sint_le_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = sint_of_bits x1
     and n2 = sint_of_bits x2 in
     let y = if n1 <= n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	     ("ERROR sint_le_n [%a] (%d <= %d)\n  expected: %a\n  obtained: %a\n")
	     bits_pp input n1 n2 
	     bits_pp y 
	     bits_pp output;
     ()
  | _ -> assert false

let g_sint_gt_n n = mkhlgate "sint_gt_N" [n] (2*n) 1
let gc_sint_gt_n n =
  assert (n>0);
  { hlcin = [n;n]
  ; hlcgates = [ g_not_n (n+1), sub_conn 2 0 n @ [(2,n-1)]
	       ; g_int_add_n (n+1), sub_conn 1 0 n @ [(1,n-1)] @ sub_conn 3 0 (n+1)
	       ; g_XOR, [(0,1); (4,n)]
	       ]
  ; hlcout = [(5,0)] (* negation of sign bit *)
  }
let chk_sint_gt_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = sint_of_bits x1
     and n2 = sint_of_bits x2 in
     let y = if n1 > n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR sint_gt_n [%a] (%d > %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false

let g_sint_lt_n n = mkhlgate "sint_lt_N" [n] (2*n) 1
let gc_sint_lt_n n =
  assert (n>0);
  { hlcin = [n;n]
  ; hlcgates = [ g_sint_gt_n n, sub_conn 2 0 n @ sub_conn 1 0 n
	       ]
  ; hlcout = [(3,0)]
  }
let chk_sint_lt_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = sint_of_bits x1
     and n2 = sint_of_bits x2 in
     let y = if n1 < n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR sint_lt_n [%a] (%d < %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false

let g_sint_ge_n n = mkhlgate "sint_ge_N" [n] (2*n) 1
let gc_sint_ge_n n =
  assert (n>0);
  { hlcin = [n;n]
  ; hlcgates = [ g_sint_le_n n, sub_conn 2 0 n @ sub_conn 1 0 n
	       ]
  ; hlcout = [(3,0)]
  }
let chk_sint_ge_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = sint_of_bits x1
     and n2 = sint_of_bits x2 in
     let y = if n1 >= n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR sint_ge_n [%a] (%d >= %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false

(* UNSIGNED COMPARISONS:

  implemented recursively with MUX2 and 1-bit comparisons
 *)
let g_lt1 = mkhlgate "lt1" [] 2 1
let gc_lt1 = { hlcin = [1;1]
	     ; hlcgates = [ g_XOR, [(1,0);(2,0)]
			  ; g_AND, [(2,0);(3,0)]
	                  ]
	     ; hlcout = [(4,0)]
	     }
let g_uint_lt_n n = mkhlgate "uint_lt_N" [n] (2*n) 1
let rec gc_uint_lt_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1]
       ; hlcgates = [(g_lt1, [(1,0); (2,0)])]
       ; hlcout = [(3,0)]
       }
  else { hlcin = [n;n]
       ; hlcgates = [ g_uint_lt_n (n-1), sub_conn 1 0 (n-1) @ sub_conn 2 0 (n-1)
		    ; g_XOR, [(1,n-1);(2,n-1)]
		    ; g_cond1, [(4,0);(2,n-1);(3,0)]
		    ]
       ; hlcout = [(5,0)]
       }
let chk_uint_lt_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = uint_of_bits x1
     and n2 = uint_of_bits x2 in
     let y = if n1 < n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR uint_lt_n [%a] (%d < %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false

let g_uint_gt_n n = mkhlgate "uint_gt_N" [n] (2*n) 1
let rec gc_uint_gt_n n =
  assert (n>0);
  { hlcin = [n;n]
  ; hlcgates = [ g_uint_lt_n n, sub_conn 2 0 n @ sub_conn 1 0 n
	       ]
  ; hlcout = [(3,0)]
  }
let chk_uint_gt_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = uint_of_bits x1
     and n2 = uint_of_bits x2 in
     let y = if n1 > n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR uint_gt_n [%a] (%d > %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false

let g_le1 = mkhlgate "le1" [] 2 1
let gc_le1 = { hlcin = [1;1]
	     ; hlcgates = [ g_XOR, [(1,0);(2,0)]
			  ; g_AND, [(1,0);(3,0)]
			  ; g_XOR, [(0,1);(4,0)]
	                  ]
	     ; hlcout = [(5,0)]
	     }

let g_uint_le_n n = mkhlgate "uint_le_N" [n] (2*n) 1
let rec gc_uint_le_n n =
  assert (n>0);
  if n=1
  then { hlcin = [1; 1]
       ; hlcgates = [(g_le1, [(1,0); (2,0)])]
       ; hlcout = [(3,0)]
       }
  else { hlcin = [n;n]
       ; hlcgates = [ g_uint_le_n (n-1), sub_conn 1 0 (n-1) @ sub_conn 2 0 (n-1)
		    ; g_XOR, [(1,n-1);(2,n-1)]
		    ; g_cond1, [(4,0);(2,n-1);(3,0)]
		    ]
       ; hlcout = [(5,0)]
       }
let chk_uint_le_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = uint_of_bits x1
     and n2 = uint_of_bits x2 in
     let y = if n1 <= n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR uint_le_n [%a] (%d < %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false

let g_uint_ge_n n = mkhlgate "uint_ge_N" [n] (2*n) 1
let rec gc_uint_ge_n n =
  assert (n>0);
  { hlcin = [n;n]
  ; hlcgates = [ g_uint_le_n n, sub_conn 2 0 n @ sub_conn 1 0 n
	       ]
  ; hlcout = [(3,0)]
  }
let chk_uint_ge_n input output =
  let size = (List.length input)/2 in
  match split_sizes [size;size] input with
  | [x1;x2] ->
     let n1 = uint_of_bits x1
     and n2 = uint_of_bits x2 in
     let y = if n1 >= n2 then [true] else [false] in
     if not (y = output)
     then Printf.fprintf stdout 
	("ERROR uint_ge_n [%a] (%d >= %d)\n  expected: %a\n  obtained: %a\n")
	bits_pp input n1 n2 
	bits_pp y 
	bits_pp output;
     ()
  | _ -> assert false



(* SHIFTS AND ROTATES *)


let g_ror_n_k n k = mkhlgate "ror_N_K" [n;k] n n
let gc_ror_n_k n k =
  if n <= 0
  then (Printf.printf "gc_ror_n_k: wrong parameters (size=%d; arg=%d)\n" n k;
	assert false);
  { hlcin = [n]
  ; hlcgates = []
  ; hlcout = sub_conn 1 k (n-k) @ sub_conn 1 0 (min n k)
  }
(* "n" is the word-width, and "p" the number of bits of the shifting arg. *)
let g_ror_n w n = mkhlgate "ror_W_N" [w;n] (n+w) w
let gc_ror_n w n =
  assert (n>0);
  if n=1
  then { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,0)::sub_conn 2 1 (w-1) @ (2,0)::sub_conn 2 0 w
	   ]
       ; hlcout = sub_conn 3 0 w
       }
  else 
       { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,n-1)
	     ::  sub_conn 2 (1 lsl (n-1)) (w-(1 lsl (n-1)))
   	         @ sub_conn 2 0 (min w (1 lsl (n-1)))
	     @ sub_conn 2 0 w
	   ; g_ror_n w (n-1), sub_conn 1 0 (n-1) @ sub_conn 3 0 w
	   ]
       ; hlcout = sub_conn 4 0 w
       }

let g_shl_n_k n k = mkhlgate "shl_N_K" [n;k] n n
let gc_shl_n_k n k =
  if n <= 0 || n < k
  then (Printf.printf "gc_shl_n_k: wrong parameters (size=%d; arg=%d)\n" n k;
	assert false);
  { hlcin = [n]
  ; hlcgates = []
  ; hlcout = zero_conn_n k @ sub_conn 1 0 (n-k) 
  }
(* "n" is the word-size, and "p" the number of bits of the shifting arg. *)
let g_shl_n w n = mkhlgate "shl_W_N" [w;n] (n+w) w
let gc_shl_n w n =
  assert (n>0);
  if n=1
  then { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,0)::(0,0)::sub_conn 2 0 (w-1) @ sub_conn 2 0 w
	   ]
       ; hlcout = sub_conn 3 0 w
       }
  else 
       { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,n-1)
	     :: zero_conn_n (min w (1 lsl (n-1)))
	        @ sub_conn 2 0 (w-(1 lsl (n-1)))
	     @ sub_conn 2 0 w
	   ; g_shl_n w (n-1), sub_conn 1 0 (n-1) @ sub_conn 3 0 w
	   ]
       ; hlcout = sub_conn 4 0 w
       }

let g_shru_n_k n k = mkhlgate "shru_N_K" [n;k] n n
let gc_shru_n_k n k =
  if n <= 0 || n < k
  then (Printf.printf "gc_shru_n_k: wrong parameters (size=%d; arg=%d)\n" n k;
	assert false);
  { hlcin = [n]
  ; hlcgates = []
  ; hlcout = sub_conn 1 k (n-k) @ zero_conn_n k
  }
(* "n" is the word-width, and "p" the number of bits of the shifting arg. *)
let g_shru_n w n = mkhlgate "shru_W_N" [w;n] (n+w) w
let gc_shru_n w n =
  assert (n>0);
  if n=1
  then { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,0)::sub_conn 2 1 (w-1) @ (0,0)::sub_conn 2 0 w
	   ]
       ; hlcout = sub_conn 3 0 w
       }
  else 
       { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,n-1)
	     ::  sub_conn 2 (1 lsl (n-1)) (w-(1 lsl (n-1)))
   	         @ zero_conn_n (min w (1 lsl (n-1)))
	     @ sub_conn 2 0 w
	   ; g_shru_n w (n-1), sub_conn 1 0 (n-1) @ sub_conn 3 0 w
	   ]
       ; hlcout = sub_conn 4 0 w
       }

let g_shr_n_k n k = mkhlgate "shr_N_K" [n;k] n n
let gc_shr_n_k n k =
  if n <= 0 || n < k
  then (Printf.printf "gc_shr_n_k: wrong parameters (size=%d; arg=%d)\n" n k;
	assert false);
  { hlcin = [n]
  ; hlcgates = []
  ; hlcout = sub_conn 1 k (n-k) @ rep_conn_n (1,n-1) k
  }
(* "n" is the word-width, and "p" the number of bits of the shifting arg. *)
let g_shr_n w n = mkhlgate "shr_W_N" [w;n] (n+w) w
let gc_shr_n w n =
  assert (n>0);
  if n=1
  then { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,0)::sub_conn 2 1 (w-1) @ (2,w-1)::sub_conn 2 0 w
	   ]
       ; hlcout = sub_conn 3 0 w
       }
  else 
       { hlcin = [n;w]
       ; hlcgates =
	   [ g_cond_n w,
	     (1,n-1)
	     ::  sub_conn 2 (1 lsl (n-1)) (w-(1 lsl (n-1)))
   	         @ rep_conn_n (2,w-1) (min w (1 lsl (n-1)))
	     @ sub_conn 2 0 w
	   ; g_shr_n w (n-1), sub_conn 1 0 (n-1) @ sub_conn 3 0 w
	   ]
       ; hlcout = sub_conn 4 0 w
       }



(* GUARDS *)

(* encoding PCOND into lists... (inorder) *)
open ORbdt
open Camlcoq
let rec pcond_varCnt = function
  | Leaf b -> 0
  | Node (x,l,r) -> 1 + pcond_varCnt l + pcond_varCnt r

let rec pcond_to_list = function
  | Leaf b -> if Obj.magic b then [-1] else [0]
  | Node (x,l,r) -> (P.to_int x)::pcond_to_list l @ pcond_to_list r


let pcond_of_list l =
 let rec pcond_of_list_aux = function
   | [] -> assert false
   | (x::xs) -> if x<0
                then (Leaf (Obj.magic true),xs)
		else (if x=0
	              then (Leaf (Obj.magic false),xs)
   		      else let (l,lxs) = pcond_of_list_aux xs in
			   let (r,rxs) = pcond_of_list_aux lxs in
			   (Node (P.of_int x,l,r),rxs))
 in fst (pcond_of_list_aux l)


let eval_guard args l =
 let g = pcond_of_list args in
 let rec ev_guard g l =
   match g with
   | Leaf s -> if Obj.magic s then (true, l) else (false, l)
   | Node (v,gl,gr) ->
      (match l with
       | [] ->  internal_error "malformed guard entry"
       | (x::xs) ->
	  let (rl,ll) = ev_guard gl xs in
	  let (rr,lr) = ev_guard gl ll in
	  (if x then rl else rr), lr
      )
 in match ev_guard g l with
    | (r, []) -> r
    | (_, _) -> internal_error "malformed guard-entry"
 
let g_guard g = 
  mkhlgate "guard" (pcond_to_list g) (pcond_varCnt g) 1
let gc_guard' g =
  match g with
  | Leaf b ->
     { hlcin = []
     ; hlcgates = []
     ; hlcout = [(0,(if Obj.magic b then 1 else 0))]
     }
  | Node (v,l,r) ->
     let lvars = pcond_varCnt l
     and rvars = pcond_varCnt r in
     { hlcin = [1;lvars;rvars]
     ; hlcgates =
	 [ g_guard l, sub_conn 2 0 lvars
	 ; g_guard r, sub_conn 3 0 rvars
	 ; g_cond1, [(1,0);(4,0);(5,0)]
	 ]
     ; hlcout = [(6,0)]
     }
let gc_guard l =
  let g = pcond_of_list l in
  let gc = gc_guard' g in
(*  Printf.fprintf stderr "GC_GUARD: %a\n" hlcirc_pp gc;*)
  gc

(** * CONCRETE COMPCERT GATES *)
let gc_eq32 = gc_eq_n 32
let gc_neq32 = gc_neq_n 32
let gc_slt32 = gc_sint_lt_n 32
let gc_sle32 = gc_sint_le_n 32
let gc_sgt32 = gc_sint_gt_n 32
let gc_sge32 = gc_sint_ge_n 32
let gc_ult32 = gc_uint_lt_n 32
let gc_ule32 = gc_uint_le_n 32
let gc_ugt32 = gc_uint_gt_n 32
let gc_uge32 = gc_uint_ge_n 32
let gc_eq32i c = { hlcin = [32]
		 ; hlcgates = [ g_constint_n_c 32 c, []
			      ; g_eq_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			      ]
		 ; hlcout = [(3,0)]
		 }
let gc_neq32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_neq_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_slt32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_sint_lt_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_sle32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_sint_le_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_sgt32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_sint_gt_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_sge32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_sint_ge_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_ult32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_uint_lt_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_ule32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_uint_le_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_ugt32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_uint_gt_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_uge32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_uint_ge_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = [(3,0)]
		  }
let gc_maskzero c = { hlcin = [32]
		    ; hlcgates = [ g_constint_n_c 32 c, []
				 ; g_and_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
				 ; g_eq_n 32, sub_conn 3 0 32 @ zero_conn_n 32
				 ]
		    ; hlcout = [(4,0)]
		    }
let gc_notmaskzero c = { hlcin = [32]
		       ; hlcgates = [ g_constint_n_c 32 c, []
				    ; g_and_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
				    ; g_neq_n 32, sub_conn 3 0 32 @ zero_conn_n 32
				    ]
		       ; hlcout = [(4,0)]
		       }

(* logic ops *)
let gc_const32 c = gc_constint_n_c 32 c
let gc_neg32 = gc_neg_n 32
let gc_sub32 = { hlcin = [32;32]
	       ; hlcgates = [ g_neg_n 32, sub_conn 2 0 32
			    ; g_int_add_n 32, sub_conn 1 0 32 @ sub_conn 3 0 32
			    ]
	       ; hlcout = sub_conn 4 0 32
	       }
let gc_not32 = gc_not_n 32
let gc_and32 = gc_and_n 32
let gc_or32 = gc_or_n 32
let gc_xor32 = gc_xor_n 32
let gc_and32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_and_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = sub_conn 3 0 32
		  }
let gc_or32i c = { hlcin = [32]
		 ; hlcgates = [ g_constint_n_c 32 c, []
			      ; g_or_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			      ]
		 ; hlcout = sub_conn 3 0 32
		 }
let gc_xor32i c = { hlcin = [32]
		  ; hlcgates = [ g_constint_n_c 32 c, []
			       ; g_xor_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
			       ]
		  ; hlcout = sub_conn 3 0 32
		  }

(* shift ops *)
let gc_shl32i c = gc_shl_n_k 32 c
let gc_shr32i c = gc_shr_n_k 32 c
let gc_shru32i c = gc_shru_n_k 32 c
let gc_ror32i c = gc_ror_n_k 32 c

let gc_add32 = gc_int_add_n 32
let gc_addaddi32 c =
  { hlcin = [32;32]
  ; hlcgates = [ g_int_add_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
	       ; g_addimm_n_c 32 c, sub_conn 3 0 32
	       ]
  ; hlcout = sub_conn 4 0 32
  }

let gc_mul32 = 
  { hlcin = [32;32]
  ; hlcgates = [ g_fullmulu_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
	       ]
  ; hlcout = sub_conn 3 0 32
  }
let gc_mul32i c = 
  { hlcin = [32]
  ; hlcgates = [ g_constint_n_c 32 c, []
	       ; g_fullmulu_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
	       ]
  ; hlcout = sub_conn 3 0 32
  }
let gc_mul32hu = 
  { hlcin = [32;32]
  ; hlcgates = [ g_fullmulu_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
	       ]
  ; hlcout = sub_conn 3 32 32
  }
let gc_mul32hs = (* this is sub-optimal!!! use Booth encoding instead*)
  { hlcin = [32;32]
  ; hlcgates = [ g_fullmulu_n 64, conn_sign_ext 64 (sub_conn 1 0 32) 
				  @ conn_sign_ext 64 (sub_conn 2 0 32)
	       ]
  ; hlcout = sub_conn 3 32 32
  }
let gc_muladd32i sc ofs =
  { hlcin = [32]
  ; hlcgates = [ g_constint_n_c 32 sc, []
	       ; g_fullmulu_n 32, sub_conn 1 0 32 @ sub_conn 2 0 32
	       ; g_addimm_n_c 32 ofs, sub_conn 3 0 32
	       ]
  ; hlcout = sub_conn 4 0 32
  }
let gc_muladdadd32i sc ofs =
  { hlcin = [32;32]
  ; hlcgates = [ g_constint_n_c 32 sc, []
	       ; g_fullmulu_n 32, sub_conn 2 0 32 @ sub_conn 3 0 32
	       ; g_addimm_n_c 32 ofs, sub_conn 4 0 32
	       ; g_int_add_n 32, sub_conn 1 0 32 @ sub_conn 5 0 32
	       ]
  ; hlcout = sub_conn 6 0 32
  }

let gc_uint_cast size =
  { hlcin = [32]
  ; hlcgates = []
  ; hlcout = conn_zero_ext 32 (sub_conn 1 0 size)
  }
let gc_sint_cast size =
  assert (size>0);
  { hlcin = [32]
  ; hlcgates = []
  ; hlcout = conn_sign_ext 32 (sub_conn 1 0 size)
  }
let gc_cmp =
  { hlcin = [1]
  ; hlcgates = []
  ; hlcout = conn_zero_ext 32 [(1,0)]
  }



(* long long ops *)
let gc_makelong =
  { hlcin = [32;32]
  ; hlcgates = []
  ; hlcout = sub_conn 2 0 32 @ sub_conn 1 0 32
  }
let gc_lowlong =
  { hlcin = [64]
  ; hlcgates = []
  ; hlcout = sub_conn 1 0 32
  }
let gc_hilong =
  { hlcin = [64]
  ; hlcgates = []
  ; hlcout = sub_conn 1 32 32
  }


(** FINAL EXPANSION TABLE *)

let g_xpnd_rule (gate: hlgate) : hlcirc option =
 match gate.hlgname, gate.hlgargs with
 | "AND", [] -> None
 | "XOR", [] -> None
 | "OR", [] -> Some gc_OR
 | "id", [n] -> Some (gc_id_n n)
 | "NOT", [] -> Some gc_NOT
 | "neq1", [] -> Some gc_neq1
 | "eq1", [] -> Some gc_eq1
 | "cond1", [] -> Some gc_cond1
 | "N_and", [n] -> Some (gc_n_and n)
 | "N_xor", [n] -> Some (gc_n_xor n)
 | "AND_N", [n] -> Some (gc_and_n n)
 | "XOR_N", [n] -> Some (gc_xor_n n)
 | "not_N", [n] -> Some (gc_not_n n)
 | "barrier_N", [n] -> Some (gc_barrier_n n)
 | "cond_N", [n] -> Some (gc_cond_n n)
 | "guard", l -> Some (gc_guard l)
 | "ror_W_N", [w;n] -> Some (gc_ror_n w n)
 | "shl_W_N", [w;n] -> Some (gc_shl_n w n)
 | "shru_W_N", [w;n] -> Some (gc_shru_n w n)
 | "shr_W_N", [w;n] -> Some (gc_shr_n w n)
 | "fulladder1", [] -> Some gc_fulladder1
 | "fulladder_N", [n] -> Some (gc_fulladder_n n)
 | "halfadder1", [] -> Some gc_halfadder1
 | "int_add_N", [n] -> Some (gc_int_add_n n)
 | "addimm_N_C", [n;c] -> Some (gc_addimm_n_c n c)
 | "dec_N", [n] -> Some (gc_dec_n n)
 | "constint_N_C", [n;c] -> Some (gc_constint_n_c n c)
 | "constbytes", l -> Some (gc_constbytes l)
 | "eq_N", [n] -> Some (gc_eq_n n)
 | "neq_N", [n] -> Some (gc_neq_n n)
 | "neg_N", [n] -> Some (gc_neg_n n)
 | "sint_le_N", [n] -> Some (gc_sint_le_n n)
 | "sint_lt_N", [n] -> Some (gc_sint_lt_n n)
 | "sint_ge_N", [n] -> Some (gc_sint_ge_n n)
 | "sint_gt_N", [n] -> Some (gc_sint_gt_n n)
 | "le1", [] -> Some (gc_le1)
 | "lt1", [] -> Some (gc_lt1)
 | "uint_le_N", [n] -> Some (gc_uint_le_n n)
 | "uint_lt_N", [n] -> Some (gc_uint_lt_n n)
 | "uint_ge_N", [n] -> Some (gc_uint_ge_n n)
 | "uint_gt_N", [n] -> Some (gc_uint_gt_n n)
 | "mul1", [] -> Some gc_mul1
 | "mulrow_N", [n] -> Some (gc_mulrow_n n)
 | "mulumat_N_M", [n;m] -> Some (gc_mulumat_n_m n m)
 | "fullmulu_N", [n] -> Some (gc_fullmulu_n n)
 | "selk", [width;size;idx] -> Some (gc_selk width size idx)
(* | "bsel_W_N", [width;size] -> Some (gc_bsel_w_n width size)
 | "subbsel_W_N", [width;size] -> Some (gc_subbsel_w_n width size)*)
 | "sel_W_N", [width;size] -> Some (gc_sel_w_n width size)
 | "subsel_W_N", [width;size] -> Some (gc_subsel_w_n width size)
 | "updk", [width;size;idx] -> Some (gc_updk width size idx)
(* | "bupd_W_N", [width;size] -> Some (gc_bupd_w_n width size)
 | "subbupd_W_N", [width;size] -> Some (gc_subbupd_w_n width size)*)
 | "upd_W_N", [width;size] -> Some (gc_upd_w_n width size)
 | "subupd_W_N", [width;size] -> Some (gc_subupd_w_n width size)
 (*| "updb", [width;size;idx] -> Some (gc_updk width size idx)*)
 | name,_ -> internal_error (msg "g_xpnd_rule: cannot handle gate %s\n" name)

let compcert_xpnd_rule (gate: hlgate) : hlcirc option =
 match gate.hlgname, gate.hlgargs with
 | "XOR", [] -> None
 | "AND", [] -> None
 (* comparisons *)
 | "eq32", [] -> Some gc_eq32
 | "neq32", [] -> Some gc_neq32
 | "slt32", [] -> Some gc_slt32
 | "sle32", [] -> Some gc_sle32
 | "sgt32", [] -> Some gc_sgt32
 | "sge32", [] -> Some gc_sge32
 | "ult32", [] -> Some gc_ult32
 | "ule32", [] -> Some gc_ule32
 | "ugt32", [] -> Some gc_ugt32
 | "uge32", [] -> Some gc_uge32
 | "eq32i", [c] -> Some (gc_eq32i c)
 | "neq32i", [c] -> Some (gc_neq32i c)
 | "slt32i", [c] -> Some (gc_slt32i c)
 | "sle32i", [c] -> Some (gc_sle32i c)
 | "sgt32i", [c] -> Some (gc_sgt32i c)
 | "sge32i", [c] -> Some (gc_sge32i c)
 | "ult32i", [c] -> Some (gc_ult32i c)
 | "ule32i", [c] -> Some (gc_ule32i c)
 | "ugt32i", [c] -> Some (gc_ugt32i c)
 | "uge32i", [c] -> Some (gc_uge32i c)
 | "maskzero", [c] -> Some (gc_maskzero c)
 | "notmaskzero", [c] -> Some (gc_notmaskzero c)
 (* unary operations *)
 | "const32", [c] -> Some (gc_constint_n_c 32 c)
 | "sint_cast", [n] -> Some (gc_sint_cast n)
 | "uint_cast", [n] -> Some (gc_uint_cast n)
 | "add32", [] -> Some gc_add32
 | "add32i", [c] -> Some (gc_addimm_n_c 32 c)
 | "addadd32i", [c] -> Some (gc_addaddi32 c)
 | "muladd32i", [sc;c] -> Some (gc_muladd32i sc c)
 | "muladdadd32i", [sc;c] -> Some (gc_muladdadd32i sc c)
 | "neg32", [] -> Some (gc_neg_n 32)
 | "sub32", [] -> Some gc_sub32
 | "mul32", [] -> Some gc_mul32
 | "mul32i", [c] -> Some (gc_mul32i c)
 | "mul32hs", [] -> Some gc_mul32hs
 | "mul32hu", [] -> Some gc_mul32hu
 | "and32", [] -> Some gc_and32
 | "and32i", [c] -> Some (gc_and32i c)
 | "or32", [] -> Some gc_or32
 | "or32i", [c] -> Some (gc_or32i c)
 | "xor32", [] -> Some gc_xor32
 | "xor32i", [c] -> Some (gc_xor32i c)
 | "not32", [] -> Some (gc_not_n 32)
 | "shl32", [] -> Some (gc_shl_n 32 5)
 | "shl32i", [c] -> Some (gc_shl32i c)
 | "shr32", [] -> Some (gc_shr_n 32 5)
 | "shr32i", [c] -> Some (gc_shr32i c)
 | "shrx32i", [c] -> None
 | "shru32i", [c] -> Some (gc_shru32i c)
 | "ror32i", [c] -> Some (gc_ror32i c)
 | "shld32i", [c] -> None
 | "int64", [] -> Some gc_makelong
 | "int64low", [] -> Some gc_lowlong
 | "int64hi", [] -> Some gc_hilong
 | "id", [n] -> Some (gc_id_n n)
 | "cmp", [] -> Some gc_cmp
 | "cond", [] -> Some gc_cond1
 | "xorN", [n] -> Some (gc_xor_n n)
 | "condN", [n] -> Some (gc_cond_n n)
 | "guard", l -> Some (gc_guard l)
 | "barrierN", [n] -> Some (gc_barrier_n n)
 | "constbytes", l -> Some (gc_constbytes l)
 | "selk", [width; size; ofs] -> Some (gc_selk width size ofs)
(* | "dsel", [width; size] -> None*)
 | "sel", [width; size] -> Some (gc_sel_w_n width size)
 | "updk", [width; size; ofs] -> Some (gc_updk width size ofs)
(* | "dupd", [width; size] -> None*)
 | "upd", [width; size] -> Some (gc_upd_w_n width size)
 (* fallback... *)
 | name,_ -> internal_error (msg "compcert_xpnd_rule: cannot handle gate %s\n" name)


let gc_xpnd gc = xpnd_gc g_xpnd_rule gc




(** Exhaustive tests *)
let test_add_int size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_int_add_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_int_add_n inp (gc_eval circ inp)) inps

let test_fullmulu size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_fullmulu_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_fullmulu_n inp (gc_eval circ inp)) inps

let test_sint_le_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_sint_le_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_sint_le_n inp (gc_eval circ inp)) inps

let test_sint_gt_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_sint_gt_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_sint_gt_n inp (gc_eval circ inp)) inps

let test_sint_lt_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_sint_lt_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_sint_lt_n inp (gc_eval circ inp)) inps

let test_sint_ge_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_sint_ge_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_sint_ge_n inp (gc_eval circ inp)) inps

let test_uint_le_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_uint_le_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_uint_le_n inp (gc_eval circ inp)) inps

let test_uint_gt_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_uint_gt_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_uint_gt_n inp (gc_eval circ inp)) inps

let test_uint_lt_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_uint_lt_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_uint_lt_n inp (gc_eval circ inp)) inps

let test_uint_ge_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_uint_ge_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_uint_ge_n inp (gc_eval circ inp)) inps

let test_addimm size =
  let x1 = all_bits size
  and x2 = List.map uint_of_bits (all_bits size) in
  List.iter (fun c -> let circ = gc_xpnd (gc_addimm_n_c size c) in
		      (List.iter (fun inp -> chk_addimm_n_c c inp (gc_eval circ inp))
				 x1))
	    x2

let test_cond1 () =
  let cond = all_bits 1
  and xt = all_bits 1
  and xf = all_bits 1 in
  let circ = gc_xpnd (gc_cond1)
  and inps = combine [cond;xt;xf] in
  List.iter (fun inp -> chk_cond1 inp (gc_eval circ inp)) inps

let test_cond_n size =
  let cond = all_bits 1
  and xt = all_bits size
  and xf = all_bits size in
  let circ = gc_xpnd (gc_cond_n size)
  and inps = combine [cond;xt;xf] in
  List.iter (fun inp -> chk_cond_n inp (gc_eval circ inp)) inps

let test_neq_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_neq_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_neq_n inp (gc_eval circ inp)) inps

let test_eq_n size =
  let x1 = all_bits size
  and x2 = all_bits size in
  let circ = gc_xpnd (gc_eq_n size)
  and inps = combine [x1;x2] in
  List.iter (fun inp -> chk_eq_n inp (gc_eval circ inp)) inps

(*
let test_shr x input =
  let w = List.length input in
  let n = size2idxbits w in
  let circ = gc_xpnd (gc_shr_n w n)
  and inps = bits_of_int n x @ input in
  (gc_eval circ inps)

let test_ror x input =
  let w = List.length input in
  let n = size2idxbits w in
  let circ = gc_xpnd (gc_ror_n w n)
  and inps = bits_of_int n x @ input in
  (gc_eval circ inps)

let test_shl x input =
  let w = List.length input in
  let n = size2idxbits w in
  let circ = gc_xpnd (gc_shl_n w n)
  and inps = bits_of_int n x @ input in
  (gc_eval circ inps)

let test_shru x input =
  let w = List.length input in
  let n = size2idxbits w in
  let circ = gc_xpnd (gc_shru_n w n)
  and inps = bits_of_int n x @ input in
  (gc_eval circ inps)
 *)
