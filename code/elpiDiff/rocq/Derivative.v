(* Derivative.v — mirrors the types of derivative.elpi: L2, the derivative IR.

   An imperative program whose variables are bound by binders, never named by
   a string: every variable of a generated function is bound at its head, in
   the order of creation (`scoped`), by `Named` (an argument, with its C++
   name) or `Fresh` (a local, with the prefix of its name). In PHOAS a bound
   variable is `DBound x`, with x of type V; a tangent, an adjoint and a tape
   are derived from it. The prefix d- of Elpi becomes D (d-var → DVar, …). *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax.

Section Derivative.
Variable V : Type.                                (* the type of the bound variables *)

Inductive dvar : Type :=                          (* a variable of the generated code *)
| DBound (x : V)                                  (* bound by Named or Fresh *)
| DotOf (v : dvar)                                (* its tangent *)
| BarOf (v : dvar)                                (* its adjoint *)
| TapeOf (v : dvar)                               (* the tape of its successive values *)
| ResultVar.                                      (* the returned value: its tangent or adjoint is an argument *)

Inductive dexpr : Type :=
| DVar (v : dvar)
| DReal (s : string)                              (* a real literal, spelled as in the source: "0", "2", "-1" *)
| DInt (k : Z)
| DAt (a i : dexpr)                               (* e[i] *)
| DOp1 (f : unary) (a : dexpr)
| DOp2 (f : binary) (a b : dexpr).

Inductive dsort : Type :=
| DConstant (t : ty)                              (* a value of this type, never reassigned *)
| DMutable.                                       (* a real, reassigned or accumulated *)

Inductive dstmt : Type :=
| DDefine (s : dsort) (v : dvar) (e : dexpr)      (* a variable and its initial value *)
| DRealVar (v : dvar)                             (* a real assigned later, in both branches of a test *)
| DTape (v : dvar)                                (* an empty tape *)
| DAssign (l e : dexpr)
| DIncrement (l e : dexpr)                        (* the adjoint accumulation *)
| DBranch (c : dexpr) (t e : list dstmt)
| DFor (i : dvar) (lo hi : dexpr) (b : list dstmt)       (* lo <= i < hi, upward *)
| DForBack (i : dvar) (lo hi : dexpr) (b : list dstmt)   (* the same indices, downward *)
| DPush (t : dvar) (e : dexpr)                    (* records a value on a tape *)
| DPop (t : dvar) (l : dexpr)                     (* restores the last recorded value *)
| DReturn (e : dexpr).

(* How a generated function receives an argument. *)
Inductive dpass : Type :=
| ByValue
| ByRef                                           (* written *)
| ByCref                                          (* read only *)
| ByRefUnused.                                    (* the caller's storage, never accessed *)

Inductive dparam : Type :=
| DParam (p : dpass) (t : ty) (v : dvar).

Inductive dreturn : Type :=
| DReturnsReal
| DVoid.

Inductive dbody : Type :=
| DBody (r : dreturn) (ps : list dparam) (ss : list dstmt).

(* A value under the binders of the variables it mentions, in order of creation. *)
Inductive scoped (A : Type) : Type :=
| Named (n : string) (f : V -> scoped A)          (* an argument, with its C++ name *)
| Fresh (p : string) (f : V -> scoped A)          (* a local, with the prefix of its name *)
| Done (a : A).

End Derivative.

Arguments DBound {V}.  Arguments DotOf {V}.  Arguments BarOf {V}.  Arguments TapeOf {V}.
Arguments ResultVar {V}.
Arguments DVar {V}.  Arguments DReal {V}.  Arguments DInt {V}.  Arguments DAt {V}.
Arguments DOp1 {V}.  Arguments DOp2 {V}.
Arguments DDefine {V}.  Arguments DRealVar {V}.  Arguments DTape {V}.  Arguments DAssign {V}.
Arguments DIncrement {V}.  Arguments DBranch {V}.  Arguments DFor {V}.  Arguments DForBack {V}.
Arguments DPush {V}.  Arguments DPop {V}.  Arguments DReturn {V}.
Arguments DParam {V}.  Arguments DBody {V}.
Arguments Named {V A}.  Arguments Fresh {V A}.  Arguments Done {V A}.

(* code: statements under their binders (typeabbrev code in Elpi). *)
Definition code (V : Type) := scoped V (list (dstmt V)).

(* A generated function: its name and its body under its binders, closed. *)
Record dfunction : Type := DFunction {
  dfname : string;
  dfbody : forall V, scoped V (dbody V)
}.
