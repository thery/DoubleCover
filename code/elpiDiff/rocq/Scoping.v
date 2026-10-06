(* Scoping.v — the discipline of the variables of the L2 programs the tool
   generates, and their opening with numbers, for the correctness theorems.

   `simplify` (Simplify.v) instantiates a generated function at the variables
   W = nat * V, and the evaluator (Exec.v) at V = nat: the variables of the
   function are opened in order, with the pair (k, k) for the k-th, and
   `simplify` compares the first components while the evaluator compares the
   second (`out_dvar`). `open_pairs` opens a scoped value in that way.

   `good sc wr ss` is the discipline the simplifications rely on, which the
   tangent programs follow: in the block ss, every variable read is in scope
   (sc, the variables defined before, in the block or around it), every
   variable assigned is writable (wr: a parameter, or a local defined mutable,
   never a constant), and every variable defined is new (not in scope), so
   that a variable defined in a block is not seen after the block, and a
   constant is never reassigned. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Derivative.

Import ListNotations.

Definition W := (nat * nat)%type.

(* Opening the binders of a scoped value, the k-th with (k, k): the value and
   the number of the next variable. *)
Fixpoint open_pairs {A : Type} (s : scoped W A) (k : nat) : A * nat :=
  match s with
  | Named _ f => open_pairs (f (k, k)) (S k)
  | Fresh _ f => open_pairs (f (k, k)) (S k)
  | Done a => (a, k)
  end.

(* A variable opened by open_pairs: its two numbers agree. *)
Fixpoint consistent (v : dvar W) : Prop :=
  match v with
  | DBound (i, j) => i = j
  | DotOf v' | BarOf v' | TapeOf v' => consistent v'
  | ResultVar => True
  end.

(* The variables an expression reads are in scope. *)
Fixpoint expr_ok (sc : list (dvar W)) (e : dexpr W) : Prop :=
  match e with
  | DVar x => In x sc
  | DReal _ | DInt _ => True
  | DAt a i => expr_ok sc a /\ expr_ok sc i
  | DOp1 _ a => expr_ok sc a
  | DOp2 _ a b => expr_ok sc a /\ expr_ok sc b
  end.

(* A location assigned: a writable variable, or an element of one. *)
Definition lhs_ok (sc wr : list (dvar W)) (l : dexpr W) : Prop :=
  match l with
  | DVar x => In x wr
  | DAt (DVar x) i => In x wr /\ expr_ok sc i
  | _ => False
  end.

Inductive good : list (dvar W) -> list (dvar W) -> list (dstmt W) -> Prop :=
| GoodNil sc wr : good sc wr []
| GoodConstant sc wr t v e r :
    expr_ok sc e -> ~ In v sc -> consistent v ->
    good (v :: sc) wr r -> good sc wr (DDefine (DConstant t) v e :: r)
| GoodMutable sc wr v e r :
    expr_ok sc e -> ~ In v sc -> consistent v ->
    good (v :: sc) (v :: wr) r -> good sc wr (DDefine DMutable v e :: r)
| GoodRealVar sc wr v r :
    ~ In v sc -> consistent v ->
    good (v :: sc) (v :: wr) r -> good sc wr (DRealVar v :: r)
| GoodTape sc wr v r :
    ~ In v sc -> consistent v ->
    good (v :: sc) (v :: wr) r -> good sc wr (DTape v :: r)
| GoodAssign sc wr l e r :
    lhs_ok sc wr l -> expr_ok sc e -> good sc wr r -> good sc wr (DAssign l e :: r)
| GoodIncrement sc wr l e r :
    lhs_ok sc wr l -> expr_ok sc e -> good sc wr r -> good sc wr (DIncrement l e :: r)
| GoodBranch sc wr c t e r :
    expr_ok sc c -> good sc wr t -> good sc wr e -> good sc wr r ->
    good sc wr (DBranch c t e :: r)
| GoodFor sc wr i lo hi b r :
    ~ In i sc -> consistent i -> expr_ok sc lo -> expr_ok sc hi ->
    good (i :: sc) wr b -> good sc wr r -> good sc wr (DFor i lo hi b :: r)
| GoodForBack sc wr i lo hi b r :
    ~ In i sc -> consistent i -> expr_ok sc lo -> expr_ok sc hi ->
    good (i :: sc) wr b -> good sc wr r -> good sc wr (DForBack i lo hi b :: r)
| GoodPush sc wr t e r :
    In t wr -> expr_ok sc e -> good sc wr r -> good sc wr (DPush t e :: r)
| GoodPop sc wr t l r :
    In t wr -> lhs_ok sc wr l -> good sc wr r -> good sc wr (DPop t l :: r)
| GoodReturn sc wr e r :
    expr_ok sc e -> good sc wr r -> good sc wr (DReturn e :: r).
