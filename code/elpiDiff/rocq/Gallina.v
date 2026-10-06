(* Gallina.v — mirrors gallina.elpi: another output, the derivative programs
   after simplification (L2′) as Gallina, the language of Rocq, for CertiRocq
   to compile to C, instead of C++.

   Gallina has no assignment: an assignment rebinds its variable (a let,
   shadowing the previous one); a branch and a loop return the tuple of the
   variables they assign that are defined before them; a loop is a call to
   for_up or for_down. The parameters passed by reference are results. Reals
   are primitive floats, integers nat, arrays and tapes lists of floats. The
   names are those of lower (Lower.v): the counter of the fresh names is
   threaded, as Elpi's new-name draws from new_int. Elpi's hypothesis
   `gtype N C`, the type of a variable by name, becomes an environment. *)

From Stdlib Require Import String Ascii ZArith List Bool.
From ElpiDiff Require Import Syntax Derivative Operations Dump Cxx.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

(* The Gallina name of a variable: its C++ name, unless that is a word of
   Gallina or a name of the preamble. *)
Definition reserved (n : string) : bool :=
  existsb (String.eqb n) ["fun"; "in"; "let"; "if"; "then"; "else"; "match"; "end"; "as"; "return";
    "with"; "fix"; "cofix"; "forall"; "exists"; "Type"; "Set"; "Prop"; "S"; "O"; "ret_"; "popped_";
    "get"; "set_at"; "add_at"; "pop"; "pow_int"; "for_up"; "for_down"; "fsin"; "fcos"; "fexp"; "flog"; "sqrt"].

Definition gname (v : dvar string) : string :=
  let n := var_name v in if reserved n then n ++ "_" else n.

(* The types, as codes: "R" a real, "Z" an integer, "B" a boolean, "A" an
   array, "T" a tape. *)
Definition ty_code (t : ty) : string :=
  match t with Real => "R" | Integer => "Z" | Boolean => "B" | Array _ => "A" end.

Definition code_type (c : string) : string :=
  if String.eqb c "Z" then "nat" else if String.eqb c "B" then "bool"
  else if String.eqb c "A" then "list float" else if String.eqb c "T" then "list float" else "float".

Definition env := list (string * string).

Fixpoint gtype (g : env) (n : string) : string :=
  match g with
  | [] => "R"
  | (m, c) :: g' => if String.eqb m n then c else gtype g' n
  end.

(* --- expressions ------------------------------------------------------------- *)

Definition comparison_op (f : binary) : bool :=
  match f with Lt | Le | Gt | Ge => true | _ => false end.

Fixpoint expr_type (g : env) (e : dexpr string) : string :=
  match e with
  | DVar v => gtype g (gname v)
  | DReal _ => "R"
  | DInt _ => "Z"
  | DAt _ _ => "R"
  | DOp1 _ _ => "R"
  | DOp2 f a _ => if comparison_op f then "B" else expr_type g a
  end.

(* A literal: a number, or the quotient of two (as the regular expression of
   gallina.elpi: the left side trimmed, the right side without its leading
   spaces). *)
Fixpoint drop_spaces (s : string) : string :=
  match s with String " " s' => drop_spaces s' | _ => s end.

Definition trim (s : string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string (drop_spaces
    (string_of_list_ascii (rev (list_ascii_of_string (drop_spaces s))))))).

Fixpoint split_slash (s : string) : option (string * string) :=
  match s with
  | EmptyString => None
  | String "/" s' => Some (EmptyString, s')
  | String c s' => match split_slash s' with Some (a, b) => Some (String c a, b) | None => None end
  end.

Definition literal (s : string) : string :=
  match split_slash s with
  | Some (a, b) =>
      let a' := trim a in let b' := drop_spaces b in
      if (String.eqb a' "" || String.eqb b' "")%bool then s else "(" ++ a' ++ " / " ++ b' ++ ")"
  | None => match s with String "-" _ => "(" ++ s ++ ")" | _ => s end
  end.

Definition op1_name (f : unary) : string :=
  match f with Sin => "fsin" | Cos => "fcos" | Exp => "fexp" | Log => "flog" | Sqrt => "sqrt" | _ => "?" end.

Definition float_op2 (f : binary) (a b : string) : string :=
  match f with
  | Add => "(" ++ a ++ " + " ++ b ++ ")"
  | Sub => "(" ++ a ++ " - " ++ b ++ ")"
  | Mul => "(" ++ a ++ " * " ++ b ++ ")"
  | Divide => "(" ++ a ++ " / " ++ b ++ ")"
  | Lt => "(" ++ a ++ " <? " ++ b ++ ")"
  | Le => "(" ++ a ++ " <=? " ++ b ++ ")"
  | Gt => "(" ++ b ++ " <? " ++ a ++ ")"
  | Ge => "(" ++ b ++ " <=? " ++ a ++ ")"
  | Unknown2 _ => "?"
  end.

Definition int_op2 (f : binary) (a b : string) : string :=
  match f with
  | Add => "(" ++ a ++ " + " ++ b ++ ")%nat"
  | Sub => "(" ++ a ++ " - " ++ b ++ ")%nat"
  | Mul => "(" ++ a ++ " * " ++ b ++ ")%nat"
  | Lt => "(Nat.ltb " ++ a ++ " " ++ b ++ ")"
  | Le => "(Nat.leb " ++ a ++ " " ++ b ++ ")"
  | Gt => "(Nat.ltb " ++ b ++ " " ++ a ++ ")"
  | Ge => "(Nat.leb " ++ b ++ " " ++ a ++ ")"
  | _ => "?"
  end.

Fixpoint expr_string (g : env) (e : dexpr string) : string :=
  match e with
  | DVar v => gname v
  | DReal s => literal s
  | DInt k => z_to_string k ++ "%nat"
  | DAt a i => "(get " ++ expr_string g a ++ " " ++ expr_string g i ++ ")"
  | DOp1 Neg a => "(- " ++ expr_string g a ++ ")"
  | DOp1 (Pow k) a => "(pow_int " ++ expr_string g a ++ " (" ++ z_to_string k ++ ")%Z)"
  | DOp1 f a => "(" ++ op1_name f ++ " " ++ expr_string g a ++ ")"
  | DOp2 f a b =>
      if String.eqb (expr_type g a) "Z" then int_op2 f (expr_string g a) (expr_string g b)
      else float_op2 f (expr_string g a) (expr_string g b)
  end.

(* --- the variables a block assigns -------------------------------------------- *)

Fixpoint lhs_name (l : dexpr string) : string :=
  match l with DVar v => gname v | DAt a _ => lhs_name a | _ => "" end.

(* add_assigned n (assigned, defined): n assigned, unless already assigned or
   defined in the block. *)
Definition add_assigned (acc : list string * list string) (n : string) : list string * list string :=
  let '(a, d) := acc in
  if existsb (String.eqb n) a || existsb (String.eqb n) d then (a, d) else (n :: a, d).

Fixpoint stmt_assigned (s : dstmt string) (acc : list string * list string) {struct s}
  : list string * list string :=
  let assigned := fun l => rev (fst ((fix go (l : list (dstmt string)) acc :=
                                       match l with [] => acc | s' :: l' => go l' (stmt_assigned s' acc) end)
                                      l ([], []))) in
  let '(a, d) := acc in
  match s with
  | DDefine _ v _ | DRealVar v | DTape v => (a, gname v :: d)
  | DAssign l _ | DIncrement l _ => add_assigned acc (lhs_name l)
  | DPush t _ => add_assigned acc (gname t)
  | DPop t l => add_assigned (add_assigned acc (gname t)) (lhs_name l)
  | DReturn _ => acc
  | DBranch _ t e => (fst (fold_left add_assigned (assigned t ++ assigned e) acc), d)
  | DFor i _ _ b | DForBack i _ _ b =>
      let ns := filter (fun n => negb (String.eqb n (gname i))) (assigned b) in
      (fst (fold_left add_assigned ns acc), d)
  end.

Definition assigned (l : list (dstmt string)) : list string :=
  rev (fst (fold_left (fun acc s => stmt_assigned s acc) l ([], []))).

Definition tuple (ns : list string) : string :=
  match ns with [n] => n | _ => "(" ++ String.concat ", " ns ++ ")" end.

Definition pattern (ns : list string) : string :=
  match ns with [n] => n | _ => "'" ++ tuple ns end.

(* --- statements -------------------------------------------------------------- *)

Definition split_last (l : list string) : list string * string :=
  (removelast l, last l "").

Definition update_string (g : env) (l : dexpr string) (se : string) : string :=
  match l with
  | DVar v => "let " ++ gname v ++ " := " ++ se ++ " in"
  | DAt a i => "let " ++ lhs_name a ++ " := set_at " ++ lhs_name a ++ " " ++ expr_string g i ++ " " ++ se ++ " in"
  | _ => ""
  end.

(* A loop: for_up lo hi (fun i state => body; state) state, rebinding the
   state, then the rest; body g' final' gives the lines of the body. *)
Definition loop_text (g : env) (ind lp : string) (i : dvar string) (lo hi : dexpr string)
  (ns : list string) (body : env -> string -> list string) (rest : list string) : list string :=
  match ns with
  | [] => rest
  | _ =>
      let ni := gname i in
      let '(lb0, lastb) := split_last (body ((ni, "Z") :: g) (tuple ns)) in
      app [ind ++ "let " ++ pattern ns ++ " :=";
           ind ++ "  " ++ lp ++ " " ++ expr_string g lo ++ " " ++ expr_string g hi ++ " (fun " ++ ni ++ " " ++ pattern ns ++ " =>"]
          (app lb0 (app [lastb ++ ") " ++ tuple ns ++ " in"] rest))
  end.

(* A branch: let state := if c then (t; state) else (e; state), then the rest. *)
Definition branch_text (g : env) (ind : string) (c : dexpr string) (ns : list string)
  (lt le rest : list string) : list string :=
  match ns with
  | [] => rest
  | _ =>
      let '(le0, laste) := split_last le in
      app [ind ++ "let " ++ pattern ns ++ " :="; ind ++ "  if " ++ expr_string g c ++ " then"]
          (app lt (app [ind ++ "  else"] (app le0 (app [laste ++ " in"] rest))))
  end.

(* stmt_lines g ind s k: the statement s as lines indented by ind, followed
   by the lines k g' of the rest, under the environment g' after s; s binds
   the variables it assigns in the lines that follow it. The blocks inside s
   are printed by an inner recursion (as Exec.v runs them), ended by their
   final expression. *)
Fixpoint stmt_lines (g : env) (ind : string) (s : dstmt string) (k : env -> list string) {struct s}
  : list string :=
  let block := fix block (g : env) (ind : string) (l : list (dstmt string)) (final : string) : list string :=
    match l with
    | [] => [ind ++ final]
    | s' :: l' => stmt_lines g ind s' (fun g' => block g' ind l' final)
    end in
  match s with
  | DDefine so v e =>
      let c := match so with DConstant t => ty_code t | DMutable => "R" end in
      (ind ++ "let " ++ gname v ++ " := " ++ expr_string g e ++ " in") :: k ((gname v, c) :: g)
  | DRealVar v => (ind ++ "let " ++ gname v ++ " := 0 in") :: k ((gname v, "R") :: g)
  | DTape v => (ind ++ "let " ++ gname v ++ " := @nil float in") :: k ((gname v, "T") :: g)
  | DAssign l e => (ind ++ update_string g l (expr_string g e)) :: k g
  | DIncrement (DVar v) e =>
      (ind ++ "let " ++ gname v ++ " := " ++ gname v ++ " + " ++ expr_string g e ++ " in") :: k g
  | DIncrement (DAt a i) e =>
      (ind ++ "let " ++ lhs_name a ++ " := add_at " ++ lhs_name a ++ " " ++ expr_string g i ++ " " ++ expr_string g e ++ " in")
        :: k g
  | DIncrement _ _ => k g
  | DPush t e => (ind ++ "let " ++ gname t ++ " := " ++ expr_string g e ++ " :: " ++ gname t ++ " in") :: k g
  | DPop t l =>
      (ind ++ "let '(popped_, " ++ gname t ++ ") := pop " ++ gname t ++ " in")
        :: (ind ++ update_string g l "popped_") :: k g
  | DReturn e => (ind ++ "let ret_ := " ++ expr_string g e ++ " in") :: k g
  | DBranch c t e =>
      let ns := assigned [s] in
      branch_text g ind c ns (block g (ind ++ "    ") t (tuple ns)) (block g (ind ++ "    ") e (tuple ns)) (k g)
  | DFor i lo hi b =>
      loop_text g ind "for_up" i lo hi (assigned [s]) (fun g' fin => block g' (ind ++ "    ") b fin) (k g)
  | DForBack i lo hi b =>
      loop_text g ind "for_down" i lo hi (assigned [s]) (fun g' fin => block g' (ind ++ "    ") b fin) (k g)
  end.

(* stmts_lines g ind ss final: the statements ss, then the expression final. *)
Fixpoint stmts_lines (g : env) (ind : string) (ss : list (dstmt string)) (final : string) : list string :=
  match ss with
  | [] => [ind ++ final]
  | s :: ss' => stmt_lines g ind s (fun g' => stmts_lines g' ind ss' final)
  end.

(* --- functions ---------------------------------------------------------------- *)

Definition param_binder (p : dparam string) : string :=
  let 'DParam _ t v := p in "(" ++ gname v ++ " : " ++ code_type (ty_code t) ++ ")".

Definition param_result (p : dparam string) : list (string * string) :=
  match p with DParam ByRef t v => [(gname v, ty_code t)] | _ => [] end.

Definition function_text (name : string) (b : dbody string) : string :=
  let 'DBody r ps ss := b in
  let outs0 := flat_map param_result ps in
  let '(outs, rcs) := match r with DReturnsReal => ("ret_" :: map fst outs0, "R" :: map snd outs0)
                                   | DVoid => (map fst outs0, map snd outs0) end in
  let g := rev (map (fun '(DParam _ t v) => (gname v, ty_code t)) ps) in
  "Definition " ++ name ++ " " ++ String.concat " " (map param_binder ps) ++ " : "
  ++ String.concat " * " (map code_type rcs) ++ " :=" ++ nl
  ++ String.concat nl (stmts_lines g "  " ss (tuple outs)) ++ "." ++ nl.

Fixpoint gallina_scoped (name : string) (s : scoped string (dbody string)) (k : nat) : string * nat :=
  match s with
  | Named n f => gallina_scoped name (f n) k
  | Fresh p f => gallina_scoped name (f (p ++ z_to_string (Z.of_nat k))) (S k)
  | Done b => (function_text name b, k)
  end.

Definition gallina_function (f : dfunction) (k : nat) : string * nat :=
  gallina_scoped (dfname f) (dfbody f string) k.

Fixpoint gallina_from (fs : list dfunction) (k : nat) : list string :=
  match fs with
  | [] => []
  | f :: fs' => let '(t, k') := gallina_function f k in t :: gallina_from fs' k'
  end.

Definition preamble : string :=
  "From Stdlib Require Import Floats List ZArith."
  ++ nl ++ "Import ListNotations."
  ++ nl ++ "Set Warnings ""-inexact-float""."
  ++ nl ++ "Open Scope float_scope."
  ++ nl ++ ""
  ++ nl ++ "(* The elementary functions that are not primitive floats: to be mapped to"
  ++ nl ++ "   the C math library (sin, cos, exp, log) when compiling with CertiRocq. *)"
  ++ nl ++ "Axiom fsin fcos fexp flog : float -> float."
  ++ nl ++ ""
  ++ nl ++ "(* Arrays and tapes are lists of floats. *)"
  ++ nl ++ "Definition get (a : list float) (i : nat) : float := nth i a 0."
  ++ nl ++ "Fixpoint set_at (a : list float) (i : nat) (x : float) : list float :="
  ++ nl ++ "  match a, i with"
  ++ nl ++ "  | [], _ => []"
  ++ nl ++ "  | _ :: a', O => x :: a'"
  ++ nl ++ "  | y :: a', S i' => y :: set_at a' i' x"
  ++ nl ++ "  end."
  ++ nl ++ "Definition add_at (a : list float) (i : nat) (x : float) : list float := set_at a i (get a i + x)."
  ++ nl ++ "Definition pop (t : list float) : float * list float :="
  ++ nl ++ "  match t with x :: t' => (x, t') | [] => (0, []) end."
  ++ nl ++ ""
  ++ nl ++ "(* x^k, k an integer. *)"
  ++ nl ++ "Fixpoint pow_nat (x : float) (n : nat) : float := match n with O => 1 | S n' => x * pow_nat x n' end."
  ++ nl ++ "Definition pow_int (x : float) (k : Z) : float :="
  ++ nl ++ "  if (k <? 0)%Z then 1 / pow_nat x (Z.to_nat (- k)) else pow_nat x (Z.to_nat k)."
  ++ nl ++ ""
  ++ nl ++ "(* The loops: the body applied to the state at each index of [lo, hi),"
  ++ nl ++ "   upward, or downward. *)"
  ++ nl ++ "Fixpoint up {A : Type} (n i : nat) (f : nat -> A -> A) (s : A) : A :="
  ++ nl ++ "  match n with O => s | S n' => up n' (S i) f (f i s) end."
  ++ nl ++ "Definition for_up {A : Type} (lo hi : nat) (f : nat -> A -> A) (s : A) : A := up (hi - lo) lo f s."
  ++ nl ++ "Fixpoint down {A : Type} (n i : nat) (f : nat -> A -> A) (s : A) : A :="
  ++ nl ++ "  match n with O => s | S n' => down n' (Nat.pred i) f (f (Nat.pred i) s) end."
  ++ nl ++ "Definition for_down {A : Type} (lo hi : nat) (f : nat -> A -> A) (s : A) : A := down (hi - lo) hi f s."
  ++ nl ++ "" ++ nl
  .

(* The file of the functions of a case; Elpi's new_int starts at 1. *)
Definition gallina_file (source : string) (fs : list dfunction) : string :=
  "(* Generated by adjudge from " ++ source ++ ". Do not edit. *)" ++ nl ++ nl
  ++ preamble ++ String.concat nl (gallina_from fs 1)
  ++ nl ++ "(* To compile with CertiRocq (not tested here), map the axioms to C:" ++ nl
  ++ "     From CertiRocq.Plugin Require Import CertiRocq." ++ nl
  ++ String.concat "" (map (fun f => "     CertiRocq Compile " ++ dfname f ++ nl
       ++ "       Extract Constants [ fsin => ""sin"", fcos => ""cos"", fexp => ""exp"", flog => ""log"" ]." ++ nl) fs)
  ++ "   The C functions must follow CertiRocq's calling convention for floats. *)" ++ nl.
