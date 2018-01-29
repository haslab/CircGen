Require RTLC.
Import Utf8.
Import Coqlib.
Import Maps.
Import Integers.
Import Registers.
Import AST.
Import Smallstep.
Import RTLC.
Import ORbdt.

Import ssreflect ssrfun eqtype ssrValues.

Fixpoint merge_pcc (s1: list (pcond * int)) :
  list (pcond * int) → list (pcond * int) :=
  match s1 with
  | nil => id
  | gn1 :: s1' =>
    fix merge_s1 (s2: list (pcond * int)) : list (pcond * int) :=
    match s2 with
    | nil => s1
    | gn2 :: s2' =>
      let '(g1, n1) := gn1 in let '(g2, n2) := gn2 in
      if Int.eq_dec n1 n2
      then (pcond_or g1 g2, n1) :: merge_pcc s1' s2'
      else if Int.lt n1 n2
           then gn1 :: merge_pcc s1' s2
           else gn2 :: merge_s1 s2'
    end
  end.

Fixpoint get_consts (g: pcond) (bdd: bdd [eqType of option int]) :
  option (list (pcond * int)) :=
  match bdd with
  | Leaf None => None
  | Leaf (Some c) => Some ((g, c) :: nil)
  | Node v ℓ r =>
    obind
      (λ cL,
       obind
         (λ cR, Some (merge_pcc cL cR))
         (get_consts (pcond_and g (pcond_litN v)) r))
      (get_consts (pcond_and g (pcond_lit v)) ℓ)
  end.

Definition cst_map : Type :=
  PTree.t (bdd [eqType of option int]).

Definition kill_reg (r: reg) (cm: cst_map) : cst_map :=
  PTree.remove r cm.

Definition set_reg (r: reg) (g: pcond) (i: int) (cm: cst_map) : cst_map :=
  let old := match cm ! r with None => Leaf None | Some old => old end in
  let new := phi_add g i old in
  PTree.set r new cm.

Definition get_reg (r: reg) (g: pcond) (cm: cst_map) :
  option (list (pcond * int)) :=
  obind
    (λ bdd,
     get_consts g (phi_slice bdd g))
    (cm ! r).

Definition expand (cm: cst_map) (g: pcond) (instr: Op.addressing → list reg → instruction) (addr: Op.addressing) (args: list reg) (acc: code) : code :=
  match addr with
  | Op.Abased s ofs =>
    match args with
    | r :: nil =>
      match get_reg r g cm with
      | Some q => fold_left (λ acc gn,
                             let '(g, n) := gn in
                             (g, instr (Op.Aglobal s (Int.add ofs n)) nil) :: acc
                            ) q acc
      | None => (g, instr addr args) :: acc
      end
    | _ => (g, instr addr args) :: acc
    end
  | Op.Abasedscaled sc s ofs =>
    match args with
    | r :: nil =>
      match get_reg r g cm with
      | Some q => fold_left (λ acc gn,
                             let '(g, n) := gn in
                             (g, instr (Op.Aglobal s (Int.add ofs (Int.mul n sc))) nil) :: acc
                            ) q acc
      | None => (g, instr addr args) :: acc
      end
    | _ => (g, instr addr args) :: acc
    end
  | _ => (g, instr addr args) :: acc
  end.

Definition expand_load (cm: cst_map) (g: pcond) (ϰ: memory_chunk) (addr: Op.addressing) (args: list reg) (dst: reg) : code → code :=
  expand cm g (λ addr args, Iload ϰ addr args dst) addr args.

Definition expand_store cm g ϰ addr args src : code → code :=
  expand cm g (λ addr args, Istore ϰ addr args src) addr args.

Definition transf_instr (acc: cst_map * code) (gi: pcond * instruction) : cst_map * code :=
  let '(cm, res) := acc in
  let '(g, i) := gi in
  match i with
  | Iop (Op.Ointconst i) nil dst => (set_reg dst g i cm, gi :: res)
  | Iop _ _ dst => (kill_reg dst cm, gi :: res)
  | Iload ϰ addr args dst => (kill_reg dst cm, expand_load cm g ϰ addr args dst res)
  | Istore ϰ addr args src => (cm, expand_store cm g ϰ addr args src res)
  | Itest _ _ _ => (cm, gi :: res)
  end.

Definition transf_code (body: code) : code :=
  let '(_, ydob) := fold_left transf_instr body (PTree.empty _, nil) in
  rev' ydob.

Definition transf_function (fn: function) : function :=
  {|
    fn_stacksize := fn_stacksize fn;
    fn_inputs := fn_inputs fn;
    fn_outputs := fn_outputs fn;
    fn_code := transf_code (fn_code fn)
  |}.

Definition transf_fundef (fd: fundef) : fundef :=
  match fd with
  | Internal fn => Internal (transf_function fn)
  | External _ => fd
  end.

Definition transf_program : program → program :=
  transform_program transf_fundef.


Theorem simulation p :
  forward_simulation (semantics p) (semantics (transf_program p)).
Admitted.
