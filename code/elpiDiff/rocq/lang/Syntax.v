(* Syntax.v — mirrors syntax.elpi: L0, the source language.

   The Elpi binders (λ-tree syntax, `let E (x\ B)`) are represented in PHOAS
   (parametric higher-order abstract syntax): a term is parameterized by the
   type V of its variables, a binder is a Rocq function `V -> term V`, and a
   variable is `Var v`. A closed program is quantified over V
   (`forall V, definition V`), so that, as in Elpi, no term names a variable
   with a string. An evaluator instantiates V with the values, as the Elpi
   evaluators open a binder with the hypothesis `value-of x V`.

   The constructors of Elpi are kept, with their arguments in the same order;
   they are capitalized (num → Num, nat → Nat, op1 → Op1, …), and the three
   that are reserved words of Rocq take an underscore: set → Set_,
   let → Let_, function → Function_. *)

From Stdlib Require Import String ZArith List.

(* The elementary operations (syntax.elpi declares unknown1 and unknown2,
   operations.elpi the others: a Rocq inductive is declared in one place). *)
Inductive unary : Type :=
| Neg | Sin | Cos | Exp | Log | Sqrt
| Pow (k : Z)                                     (* x |-> x^k *)
| Unknown1 (s : string).

Inductive binary : Type :=
| Add | Sub | Mul | Divide
| Lt | Le | Gt | Ge                               (* comparisons: passive *)
| Unknown2 (s : string).

Section Term.
Variable V : Type.                                (* the type of the bound
  variables *)

Inductive term : Type :=
| Var (x : V)                                     (* a bound variable *)
| Num (s : string)                                (* a real literal,
  spelled as in C++: "2", "0.9" *)
| Nat (k : Z)                                     (* an integer literal *)
| Op1 (f : unary) (a : term)                      (* a unary elementary
  operation *)
| Op2 (f : binary) (a b : term)                   (* a binary elementary
  operation *)
| Get (a i : term)                                (* a[i] *)
| Set_ (a i v : term)                              (* a with a[i] replaced: the
  next version of a *)
| Let_ (e : term) (b : V -> term)                  (* let x = e in b *)
| Ite (c t e : term)                              (* if c then t else e,
  where c is passive *)
| Map (lo hi : term) (b : V -> term)
  (* the array [ b i | lo <= i < hi ] *)
| Fold (lo hi init : term) (b : V -> V -> term).
  (* s := init; for lo <= i < hi: s := b i s *)

End Term.

Arguments Var {V}.   Arguments Num {V}.  Arguments Nat {V}.  Arguments Op1 {V}.
Arguments Op2 {V}.   Arguments Get {V}.  Arguments Set_ {V}.  Arguments Let_
  {V}.
Arguments Ite {V}.   Arguments Map {V}.  Arguments Fold {V}.

Inductive ty : Type :=
| Real
| Integer
| Boolean
| Array (n : Z).                                  (* an array of reals with a
  static extent *)

(* The role of an argument: Tapenade's independent and dependent variables. *)
Inductive role : Type :=
| Independent                                     (* an input we differentiate
  with respect to *)
| Dependent                                       (* written and never read;
  its derivative is wanted *)
| Inout                                           (* read,
  then overwritten: independent and dependent *)
| Passive.                                        (* neither *)

Inductive result (V : Type) : Type :=
| Returns (t : ty)                                (* the body's value is
  returned *)
| Writes (y : term V).                            (* the body's value is stored
  in this argument *)

Arguments Returns {V}.  Arguments Writes {V}.

(* The definition of a function: one binder per argument, in the order of the
   C++ signature, then where the result goes and the body. *)
Inductive definition (V : Type) : Type :=
| Arg (n : string) (t : ty) (r : role) (f : V -> definition V)
| Body (r : result V) (b : term V).

Arguments Arg {V}.  Arguments Body {V}.

(* A function: its name and its definition, closed. *)
Record function : Type := Function_ {
  fname : string;
  fdef : forall V, definition V
}.

(* An argument as plain data, for the signatures of the generated code. *)
Inductive decl : Type :=
| Decl (n : string) (t : ty) (r : role).

(* written-role R: the function writes an argument of role R. *)
Definition written_role (r : role) : bool :=
  match r with Dependent | Inout => true | _ => false end.

(* varied-role R: an argument of role R carries a derivative on entry. *)
Definition varied_role (r : role) : bool :=
  match r with Independent | Inout => true | _ => false end.
