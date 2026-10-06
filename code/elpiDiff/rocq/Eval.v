(* Eval.v — mirrors eval.elpi: the evaluator of L0, the source language.

   `eval D t`: in the domain of numbers D (Domain.v), the value of the term t.
   A big-step semantics, one rule per construct. Elpi opens a binder with the
   hypothesis `value-of x V`; in PHOAS the evaluator instantiates the type of
   the variables with the values, and a binder `b` is applied to the value of
   its variable, `b v`. Elpi's relations become functions into option: None
   where the Elpi evaluator fails (an ill-typed program, an index out of an
   array). *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Domain Operations.

Import ListNotations.
Open Scope Z_scope.

(* A value whose reals are of type N (kind val in eval.elpi; v-tape, declared
   in exec.elpi, is here since a Rocq inductive is declared in one place). *)
Inductive val (N : Type) : Type :=
| VReal (x : N)
| VInt (k : Z)
| VBool (b : bool)
| VArray (xs : list N)
| VTape (xs : list N).                            (* a tape, the last value pushed first *)

Arguments VReal {N}.  Arguments VInt {N}.  Arguments VBool {N}.
Arguments VArray {N}.  Arguments VTape {N}.

Notation "'let*' x := a 'in' b" := (match a with Some x => b | None => None end)
  (at level 200, x pattern, b at level 200).

(* std.nth and replace-nth on a list, at an integer index. *)
Definition nth_z {A : Type} (k : Z) (l : list A) : option A :=
  if k <? 0 then None else nth_error l (Z.to_nat k).

Fixpoint replace_nth {A : Type} (k : nat) (x : A) (l : list A) : option (list A) :=
  match k, l with
  | O, _ :: l' => Some (x :: l')
  | S k', y :: l' => let* l1 := replace_nth k' x l' in Some (y :: l1)
  | _, [] => None
  end.

Definition replace_nth_z {A : Type} (k : Z) (x : A) (l : list A) : option (list A) :=
  if k <? 0 then None else replace_nth (Z.to_nat k) x l.

Section Eval.
Variable N : Type.
Variable D : domain N.

(* Integers compute exactly, reals in the domain; a comparison gives a boolean,
   or fails where the domain refuses to compare. *)
Definition int_holds (f : binary) (x y : Z) : bool :=
  match f with
  | Lt => x <? y | Le => x <=? y | Gt => x >? y | Ge => x >=? y
  | _ => false                                    (* int-holds fails: the `if` of int-op2 gives ff *)
  end.

Definition int_op2 (f : binary) (x y : Z) : val N :=
  match f with
  | Add => VInt (x + y)
  | Sub => VInt (x - y)
  | Mul => VInt (x * y)
  | _ => VBool (int_holds f x y)
  end.

Definition eval_op1 (f : unary) (a : val N) : option (val N) :=
  match a with
  | VReal x => let* y := dom_op1 D f x in Some (VReal y)
  | _ => None
  end.

Definition eval_op2 (f : binary) (a b : val N) : option (val N) :=
  match a, b with
  | VInt x, VInt y => Some (int_op2 f x y)
  | VReal x, VReal y => if comparison f then let* c := dom_cmp D f x y in Some (VBool c)
                        else let* z := dom_op2 D f x y in Some (VReal z)
  | _, _ => None
  end.

(* map: the array of the body at each of the n indices from i;
   fold: the state after the body at each of the n indices from i, in order.
   They take the evaluation of the body as an argument. *)
Fixpoint eval_map (ev : val N -> option (val N)) (i : Z) (n : nat) : option (list N) :=
  match n with
  | O => Some []
  | S n' => match ev (VInt i) with
            | Some (VReal x) => let* xs := eval_map ev (i + 1) n' in Some (x :: xs)
            | _ => None
            end
  end.

Fixpoint eval_fold (ev : val N -> val N -> option (val N)) (i : Z) (n : nat) (s : val N)
  : option (val N) :=
  match n with
  | O => Some s
  | S n' => let* s1 := ev (VInt i) s in eval_fold ev (i + 1) n' s1
  end.

(* The number of indices of [i, j). *)
Definition count (i j : Z) : nat := Z.to_nat (j - i).

Fixpoint eval (t : term (val N)) : option (val N) :=
  match t with
  | Var v => Some v
  | Num s => let* x := dom_lit D s in Some (VReal x)
  | Nat k => Some (VInt k)
  | Op1 f a => let* va := eval a in eval_op1 f va
  | Op2 f a b => let* va := eval a in let* vb := eval b in eval_op2 f va vb
  | Get a i =>
      match eval a, eval i with
      | Some (VArray l), Some (VInt k) => let* x := nth_z k l in Some (VReal x)
      | _, _ => None
      end
  | Set_ a i e =>
      match eval a, eval i, eval e with
      | Some (VArray l), Some (VInt k), Some (VReal x) => let* l1 := replace_nth_z k x l in Some (VArray l1)
      | _, _, _ => None
      end
  | Let_ e b => let* ve := eval e in eval (b ve)
  | Ite c t e =>
      match eval c with
      | Some (VBool true) => eval t
      | Some (VBool false) => eval e
      | _ => None
      end
  | Map lo hi b =>
      match eval lo, eval hi with
      | Some (VInt i), Some (VInt j) => let* xs := eval_map (fun v => eval (b v)) i (count i j) in Some (VArray xs)
      | _, _ => None
      end
  | Fold lo hi init b =>
      match eval lo, eval hi, eval init with
      | Some (VInt i), Some (VInt j), Some s => eval_fold (fun v w => eval (b v w)) i (count i j) s
      | _, _, _ => None
      end
  end.

(* eval_definition d args: d applied to args, in order: the returned value,
   or the new value of the argument it writes. *)
Fixpoint eval_definition (d : definition (val N)) (args : list (val N)) : option (val N) :=
  match d, args with
  | Arg _ _ _ f, a :: args' => eval_definition (f a) args'
  | Body _ b, [] => eval b
  | _, _ => None
  end.

Definition eval_function (f : function) (args : list (val N)) : option (val N) :=
  eval_definition (fdef f (val N)) args.

End Eval.

Arguments eval {N}.  Arguments eval_definition {N}.  Arguments eval_function {N}.
Arguments eval_op1 {N}.  Arguments eval_op2 {N}.  Arguments int_op2 {N}.
Arguments eval_map {N}.  Arguments eval_fold {N}.
