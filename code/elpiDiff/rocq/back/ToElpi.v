(* ToElpi.v — prints L2, the derivative IR, as an Elpi term of the types of
   derivative.elpi, so that the Elpi tool lowers the programs Rocq computed
   and prints them as C++ (lower.elpi, cxx.elpi): the theorems are about L2′,
   the simplified programs, and the printing to C++ is left to Elpi. In PHOAS
   the printer instantiates the variables with the names of Elpi binders,
   v1, v2, … in order of creation; the constructors keep their Elpi names
   (DVar → d-var, …). *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Derivative Operations.

Import ListNotations.
Open Scope string_scope.

(* An integer, parenthesized when negative: (-1). *)
Definition e_int (k : Z) : string :=
  if Z.ltb k 0 then "(" ++ z_to_string k ++ ")" else z_to_string k.

Definition e_quote (s : string) : string := """" ++ s ++ """".

Definition e_ty (t : ty) : string :=
  match t with
  | Real => "real" | Integer => "integer" | Boolean => "boolean"
  | Array n => "(array " ++ e_int n ++ ")"
  end.

Definition e_unary (f : unary) : string :=
  match f with
  | Neg => "neg" | Sin => "sin" | Cos => "cos" | Exp => "exp" | Log => "log"
  | Sqrt => "sqrt"
  | Pow k => "(pow " ++ e_int k ++ ")"
  | Unknown1 s => "(unknown1 " ++ e_quote s ++ ")"
  end.

Definition e_binary (f : binary) : string :=
  match f with
  | Add => "add" | Sub => "sub" | Mul => "mul" | Divide => "divide"
  | Lt => "lt" | Le => "le" | Gt => "gt" | Ge => "ge"
  | Unknown2 s => "(unknown2 " ++ e_quote s ++ ")"
  end.

Fixpoint e_dvar (v : dvar string) : string :=
  match v with
  | DBound s => s
  | DotOf v' => "(dot-of " ++ e_dvar v' ++ ")"
  | BarOf v' => "(bar-of " ++ e_dvar v' ++ ")"
  | TapeOf v' => "(tape-of " ++ e_dvar v' ++ ")"
  | ResultVar => "result-var"
  end.

Fixpoint e_dexpr (e : dexpr string) : string :=
  match e with
  | DVar v => "(d-var " ++ e_dvar v ++ ")"
  | DReal l => "(d-real " ++ e_quote l ++ ")"
  | DInt k => "(d-int " ++ e_int k ++ ")"
  | DAt a i => "(d-at " ++ e_dexpr a ++ " " ++ e_dexpr i ++ ")"
  | DOp1 f a => "(d-op1 " ++ e_unary f ++ " " ++ e_dexpr a ++ ")"
  | DOp2 f a b =>
      "(d-op2 " ++ e_binary f ++ " " ++ e_dexpr a ++ " " ++ e_dexpr b ++ ")"
  end.

Definition e_list (l : list string) : string :=
  "[" ++ String.concat ", " l ++ "]".

Fixpoint e_dstmt (s : dstmt string) : string :=
  let e_stmts l := e_list (map e_dstmt l) in
  match s with
  | DDefine (DConstant t) v e =>
      "(d-define (d-constant " ++ e_ty t ++ ") " ++ e_dvar v ++ " " ++
      e_dexpr e ++ ")"
  | DDefine DMutable v e =>
      "(d-define d-mutable " ++ e_dvar v ++ " " ++ e_dexpr e ++ ")"
  | DRealVar v => "(d-real-var " ++ e_dvar v ++ ")"
  | DTape v => "(d-tape " ++ e_dvar v ++ ")"
  | DAssign a b => "(d-assign " ++ e_dexpr a ++ " " ++ e_dexpr b ++ ")"
  | DIncrement a b => "(d-increment " ++ e_dexpr a ++ " " ++ e_dexpr b ++ ")"
  | DBranch c t e =>
      "(d-branch " ++ e_dexpr c ++ " " ++ e_stmts t ++ " " ++ e_stmts e ++ ")"
  | DFor i lo hi b =>
      "(d-for " ++ e_dvar i ++ " " ++ e_dexpr lo ++ " " ++ e_dexpr hi ++ " " ++
      e_stmts b ++ ")"
  | DForBack i lo hi b =>
      "(d-for-back " ++ e_dvar i ++ " " ++ e_dexpr lo ++ " " ++ e_dexpr hi ++
      " " ++ e_stmts b ++ ")"
  | DPush t e => "(d-push " ++ e_dvar t ++ " " ++ e_dexpr e ++ ")"
  | DPop t e => "(d-pop " ++ e_dvar t ++ " " ++ e_dexpr e ++ ")"
  | DReturn e => "(d-return " ++ e_dexpr e ++ ")"
  end.

Definition e_dpass (p : dpass) : string :=
  match p with
  | ByValue => "by-value" | ByRef => "by-ref" | ByCref => "by-cref"
  | ByRefUnused => "by-ref-unused"
  end.

Definition e_dparam (p : dparam string) : string :=
  let 'DParam pw t v := p in
  "(dparam " ++ e_dpass pw ++ " " ++ e_ty t ++ " " ++ e_dvar v ++ ")".

Definition e_dbody (b : dbody string) : string :=
  let 'DBody r ps ss := b in
  let rs := match r with DReturnsReal => "d-returns-real" | DVoid => "d-void"
    end in
  "(dbody " ++ rs ++ " " ++ e_list (map e_dparam ps) ++ " " ++
  e_list (map e_dstmt ss) ++ ")".

(* The binders, named v1, v2, … *)
Fixpoint e_scoped (s : scoped string (dbody string)) (k : nat) : string :=
  let x := "v" ++ z_to_string (Z.of_nat k) in
  match s with
  | Named n f => "(named " ++ e_quote n ++ " " ++ x ++ "\ " ++
      e_scoped (f x) (S k) ++ ")"
  | Fresh p f => "(fresh " ++ e_quote p ++ " " ++ x ++ "\ " ++
      e_scoped (f x) (S k) ++ ")"
  | Done b => "(done " ++ e_dbody b ++ ")"
  end.

(* to_elpi F: F as an Elpi term of type dfunction. *)
Definition to_elpi (f : dfunction) : string :=
  "dfunction " ++ e_quote (dfname f) ++ " " ++ e_scoped (dfbody f string) 1.
