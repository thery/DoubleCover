(* Operations.v — mirrors the table of operations.elpi: the types of the
   elementary operations, their C++ spelling and their partial derivatives.
   (The operators themselves are declared in Syntax.v, a Rocq inductive being
   declared in one place.)

   operation2 is a relation of several rows per operator, the first with a cut:
   a query with known operand types gets the first row that matches them, a
   query with unknown types gets the first row. The table is kept as rows, with
   one function for each of these two uses. *)

From Stdlib Require Import String ZArith List Bool DecimalString.
From ElpiDiff Require Import Syntax Anf.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Definition ty_eqb (a b : ty) : bool :=
  match a, b with
  | Real, Real | Integer, Integer | Boolean, Boolean => true
  | Array n, Array m => Z.eqb n m
  | _, _ => false
  end.

Definition z_to_string (k : Z) : string := NilZero.string_of_int (Z.to_int k).

(* operation1 F Type Result Spelling *)
Definition operation1 (f : unary) : option (ty * ty * string) :=
  match f with
  | Neg => Some (Real, Real, "neg")
  | Sin => Some (Real, Real, "sin")
  | Cos => Some (Real, Real, "cos")
  | Exp => Some (Real, Real, "exp")
  | Log => Some (Real, Real, "log")
  | Sqrt => Some (Real, Real, "sqrt")
  | Pow _ => Some (Real, Real, "pow")
  | Unknown1 _ => None
  end.

(* The literal arguments that follow the operand in the C++ call: the exponent of pow. *)
Definition extra_arguments (f : unary) : list string :=
  match f with
  | Pow k => [z_to_string k]
  | _ => []
  end.

(* operation2 F Type1 Type2 Result Spelling: the rows of an operator, in order. *)
Definition operation2_rows (f : binary) : list (ty * ty * ty * string) :=
  match f with
  | Add => [(Real, Real, Real, "+"); (Integer, Integer, Integer, "+")]
  | Sub => [(Real, Real, Real, "-"); (Integer, Integer, Integer, "-")]
  | Mul => [(Real, Real, Real, "*")]
  | Divide => [(Real, Real, Real, "/")]
  (* comparisons are passive: no partial derivative *)
  | Lt => [(Real, Real, Boolean, "<"); (Integer, Integer, Boolean, "<")]
  | Le => [(Real, Real, Boolean, "<="); (Integer, Integer, Boolean, "<=")]
  | Gt => [(Real, Real, Boolean, ">"); (Integer, Integer, Boolean, ">")]
  | Ge => [(Real, Real, Boolean, ">="); (Integer, Integer, Boolean, ">=")]
  | Unknown2 _ => []
  end.

(* `operation2 F _ _ T S`, unknown operand types: the first row. *)
Definition operation2 (f : binary) : option (ty * ty * ty * string) :=
  match operation2_rows f with r :: _ => Some r | [] => None end.

(* `operation2 F TA TB T S`, known operand types: the result and the spelling
   of the first row that matches them. *)
Definition operation2_typed (f : binary) (ta tb : ty) : option (ty * string) :=
  match find (fun '(a, b, _, _) => ty_eqb a ta && ty_eqb b tb) (operation2_rows f) with
  | Some (_, _, t, s) => Some (t, s)
  | None => None
  end.

(* comparison F (activity.elpi): the first row of F gives a boolean. *)
Definition comparison (f : binary) : bool :=
  match operation2 f with Some (_, _, Boolean, _) => true | _ => false end.

Section Partials.
Variable V : Type.

(* partial1 F A D: D is the derivative of `AOp1 F A` with respect to A, an expression over A. *)
Definition partial1 (f : unary) (a : atom V) : option (pexpr V) :=
  match f with
  | Neg => Some (PNum "-1")
  | Sin => Some (POp1 Cos (PAtom a))
  | Cos => Some (POp1 Neg (POp1 Sin (PAtom a)))
  | Exp => Some (POp1 Exp (PAtom a))
  | Log => Some (POp2 Divide (PNum "1") (PAtom a))
  | Sqrt => Some (POp2 Divide (PNum "1") (POp2 Mul (PNum "2") (POp1 Sqrt (PAtom a))))
  | Pow 0 => Some (PNum "0")                                   (* x^0 is the constant 1 *)
  | Pow k => Some (POp2 Mul (PNum (z_to_string k)) (POp1 (Pow (k - 1)) (PAtom a)))
  | Unknown1 _ => None
  end.

(* partial2 F A B: the derivatives of `AOp2 F A B` with respect to A and to B. *)
Definition partial2 (f : binary) (a b : atom V) : option (pexpr V * pexpr V) :=
  match f with
  | Add => Some (PNum "1", PNum "1")
  | Sub => Some (PNum "1", PNum "-1")
  | Mul => Some (PAtom b, PAtom a)
  | Divide => Some (POp2 Divide (PNum "1") (PAtom b),
                    POp1 Neg (POp2 Divide (PAtom a) (POp2 Mul (PAtom b) (PAtom b))))
  | _ => None
  end.

End Partials.

Arguments partial1 {V}.  Arguments partial2 {V}.

(* The name of an operator, for diagnostics: as Elpi's term_to_string prints
   it (a negative exponent in Elpi's syntax, `pow (~ 1)`). *)
Definition unary_name (f : unary) : string :=
  match f with
  | Neg => "neg" | Sin => "sin" | Cos => "cos" | Exp => "exp" | Log => "log" | Sqrt => "sqrt"
  | Pow k => if Z.ltb k 0 then "pow (~ " ++ z_to_string (- k) ++ ")" else "pow " ++ z_to_string k
  | Unknown1 s => s
  end.

Definition binary_name (f : binary) : string :=
  match f with
  | Add => "add" | Sub => "sub" | Mul => "mul" | Divide => "divide"
  | Lt => "lt" | Le => "le" | Gt => "gt" | Ge => "ge"
  | Unknown2 s => s
  end.
