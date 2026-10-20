(* Anf.v — mirrors the types of anf.elpi: L1, the A-normal form, and L1ᵃ.

   Every intermediate value is named by a let, and an operation applies to
   atoms only: a binder binds an atom (in PHOAS, a variable of type V, used as
   `AVar v`). L1 is indexed by what its binders are annotated with: `anf V bare`
   is L1, `anf V ann` is L1ᵃ; the constructors are the same. As in Elpi, a
   value and a body are mutually inductive, since a branch or a loop body is a
   body. The prefix a- of Elpi becomes A (a-let → ALet, a-ret → ARet, …). *)

From Stdlib Require Import String ZArith.
From ElpiDiff Require Import Syntax.

Section Anf.
Variable V : Type.                                (* the type of the bound atoms
  *)

Inductive atom : Type :=
| AVar (x : V)                                    (* a variable bound by L1 *)
| ANum (s : string)                               (* a real literal *)
| ANat (k : Z).                                   (* an integer literal *)

Variable I : Type.                                (* the annotations: bare or
  ann *)

Inductive value : Type :=                         (* what a let binds *)
| AOp1 (f : unary) (a : atom)
| AOp2 (f : binary) (a b : atom)
| AGet (a i : atom)                               (* a[i] *)
| ASet (a i v : atom)                             (* a with a[i] replaced *)
| AIte (c : atom) (t e : anf)                     (* the condition is an atom,
  the branches are bodies *)
| AMap (lo hi : atom) (b : V -> anf)
| AFold (ann : I) (lo hi init : atom) (b : V -> V -> anf)
with anf : Type :=                                (* a body *)
| ALet (ann : I) (e : value) (b : V -> anf)
| ARet (x : atom).

Inductive aresult : Type :=
| AReturns (t : ty)
| AWrites (y : atom).

Inductive adefinition : Type :=
| AArg (n : string) (t : ty) (r : role) (f : V -> adefinition)
| ABody (r : aresult) (b : anf).

(* A partial derivative: an expression over atoms, nested, since it is never
   itself differentiated. The table of partial derivatives is in
   Operations.v. *)
Inductive pexpr : Type :=
| PAtom (a : atom)
| PNum (s : string)                               (* a real literal *)
| POp1 (f : unary) (a : pexpr)
| POp2 (f : binary) (a b : pexpr).

End Anf.

Arguments AVar {V}.  Arguments ANum {V}.  Arguments ANat {V}.
Arguments AOp1 {V I}.  Arguments AOp2 {V I}.  Arguments AGet {V I}.  Arguments
  ASet {V I}.
Arguments AIte {V I}.  Arguments AMap {V I}.  Arguments AFold {V I}.
Arguments ALet {V I}.  Arguments ARet {V I}.
Arguments AReturns {V}.  Arguments AWrites {V}.
Arguments AArg {V I}.  Arguments ABody {V I}.
Arguments PAtom {V}.  Arguments PNum {V}.  Arguments POp1 {V}.  Arguments POp2
  {V}.

(* The annotations. *)
Inductive bare : Type := Bare.                    (* none: L1 *)

Inductive ann : Type :=                           (* L1ᵃ *)
| LetAnn (varied active computed : bool)
  (* on a let: the value is varied, active (varied and useful),
  computed in its sweep *)
| FoldAnn (varied recorded records : bool).
  (* on a fold: the state is varied, recorded before each overwrite;
  the fold records something *)

(* A function of L1: its name and its definition, closed. *)
Record afunction (I : Type) : Type := AFunction {
  afname : string;
  afdef : forall V, adefinition V I
}.

Arguments AFunction {I}.  Arguments afname {I}.  Arguments afdef {I}.
