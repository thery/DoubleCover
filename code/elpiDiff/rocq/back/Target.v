(* Target.v — mirrors target.elpi: L3, the target language: C++ statements,
   first order, names as strings. lower produces it from the derivative IR,
   cxx prints it. It has no binders, hence no PHOAS parameter. The names of
   Elpi are capitalized (id → Id, loop-back → LoopBack, …). *)

From Stdlib Require Import String List.

Inductive expr : Type :=
| Id (s : string)                                 (* a variable *)
| Lit (s : string)                                (* a literal, spelled *)
| At (a i : expr)                                 (* e[i] *)
| Call (f : string) (args : list expr).
  (* an operator ("+", "<", "neg") or a function ("sin") *)

Inductive stmt : Type :=
| Declare (t n : string) (e : expr)               (* type name = init; *)
| Allocate (t n : string)                         (* type name{}; *)
| Assign (l e : expr)                             (* lhs = rhs; *)
| Increment (l e : expr)                          (* lhs += rhs;
  the adjoint accumulation *)
| Branch (c : expr) (t e : list stmt)
| Loop (i : string) (lo hi : expr) (b : list stmt)
  (* for (i = lo; i < hi; ++i) *)
| LoopBack (i : string) (lo hi : expr) (b : list stmt)
  (* for (i = hi; i-- > lo;) *)
| Push (t : string) (e : expr)                    (* tape.push_back(e); *)
| Pop (t : string) (e : expr)                     (* lhs = tape.back();
  tape.pop_back(); *)
| Return (e : expr).

(* result type, name, arguments, body *)
Inductive cfunction : Type :=
| CFunction (ret name : string) (args : list string) (body : list stmt).
