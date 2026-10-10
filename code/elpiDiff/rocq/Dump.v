(* Dump.v — mirrors the printer of L2 in dump.elpi: the derivative IR in a
   readable form, the same lines as `elpi … -exec dump -- derivative|simplified
   <mode>`. In PHOAS a printer instantiates the variables with their names: a
   fresh local is numbered per function, as pr-scoped does. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Derivative Operations.

Import ListNotations.
Open Scope string_scope.

Definition ty_string (t : ty) : string :=
  match t with
  | Real => "real" | Integer => "int" | Boolean => "bool"
  | Array n => "real[" ++ z_to_string n ++ "]"
  end.

(* Operators, shared with the printer of L1 in Elpi. *)
Definition op1_string (f : unary) (a p : string) : string :=
  match f with
  | Neg => "-" ++ p
  | Pow k => "pow(" ++ a ++ ", " ++ z_to_string k ++ ")"
  | _ => unary_name f ++ "(" ++ a ++ ")"
  end.

Definition op2_symbol (f : binary) : string :=
  match operation2 f with Some (_, _, _, s) => s | None => binary_name f end.

(* var-name of lower.elpi: a tangent, an adjoint and a tape are named after
   their variable. *)
Fixpoint var_name (v : dvar string) : string :=
  match v with
  | DBound s => s
  | DotOf v' => var_name v' ++ "_dot"
  | BarOf v' => var_name v' ++ "_bar"
  | TapeOf v' => var_name v' ++ "_tape"
  | ResultVar => "result"
  end.

(* An expression at top level, and as an operand: parenthesized when infix. *)
Fixpoint dexpr_strings (e : dexpr string) : string * string :=
  match e with
  | DVar v => let n := var_name v in (n, n)
  | DReal l => (l, l)
  | DInt k => let n := z_to_string k in (n, n)
  | DAt a i => let x := snd (dexpr_strings a) ++ "[" ++ fst (dexpr_strings i) ++
    "]" in (x, x)
  | DOp1 f a => let x := op1_string f (fst (dexpr_strings a))
    (snd (dexpr_strings a)) in (x, x)
  | DOp2 f a b =>
      let x := snd (dexpr_strings a) ++ " " ++ op2_symbol f ++ " " ++ snd
        (dexpr_strings b) in
      (x, "(" ++ x ++ ")")
  end.

Definition dexpr_string (e : dexpr string) : string := fst (dexpr_strings e).

Definition pass_word (p : dpass) : string :=
  match p with ByValue => "" | ByRef => "ref " | ByCref => "const ref " |
    ByRefUnused => "unused ref " end.

Definition param_text (p : dparam string) : string :=
  let 'DParam pw t v := p in var_name v ++ ": " ++ pass_word pw ++ ty_string t.

Fixpoint pr_stmt (ind : string) (s : dstmt string) : list string :=
  let pr_stmts ind l := List.concat (map (pr_stmt ind) l) in
  let ind2 := ind ++ "    " in
  match s with
  | DDefine (DConstant t) v e => [ind ++ "const " ++ ty_string t ++ " " ++
    var_name v ++ " = " ++ dexpr_string e]
  | DDefine DMutable v e => [ind ++ "var real " ++ var_name v ++ " = " ++
    dexpr_string e]
  | DRealVar v => [ind ++ "var real " ++ var_name v]
  | DTape v => [ind ++ "tape " ++ var_name v]
  | DAssign a b => [ind ++ dexpr_string a ++ " := " ++ dexpr_string b]
  | DIncrement a b => [ind ++ dexpr_string a ++ " += " ++ dexpr_string b]
  | DBranch c t e => app [ind ++ "if " ++ dexpr_string c ++ ":"]
                         (app (pr_stmts ind2 t)
                           ((ind ++ "else:") :: pr_stmts ind2 e))
  | DFor i lo hi b => (ind ++ "for " ++ var_name i ++ " in [" ++ dexpr_string lo
    ++ ", " ++ dexpr_string hi ++ "):")
                      :: pr_stmts ind2 b
  | DForBack i lo hi b => (ind ++ "for " ++ var_name i ++ " in [" ++
    dexpr_string lo ++ ", " ++ dexpr_string hi ++ ") downward:")
                          :: pr_stmts ind2 b
  | DPush t e => [ind ++ "push " ++ dexpr_string e ++ " onto " ++ var_name t]
  | DPop t e => [ind ++ dexpr_string e ++ " := pop " ++ var_name t]
  | DReturn e => [ind ++ "return " ++ dexpr_string e]
  end.

Fixpoint pr_scoped (name : string) (s : scoped string (dbody string)) (k : nat)
  : list string :=
  match s with
  | Named n f => pr_scoped name (f n) k
  | Fresh p f => pr_scoped name (f (p ++ z_to_string (Z.of_nat k))) (S k)
  | Done (DBody r ps ss) =>
      let params := map param_text ps in
      let rs := match r with DReturnsReal => " returns real" | DVoid =>
        "" end in
      (name ++ "(" ++ String.concat ", " params ++ ")" ++ rs ++ ":") ::
        List.concat (map (pr_stmt "    ") ss)
  end.

(* pr-dfunction F: the lines of F. *)
Definition pr_dfunction (f : dfunction) : list string :=
  pr_scoped (dfname f) (dfbody f string) 1.
