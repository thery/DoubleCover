(* EvalAnf.v — mirrors eval-anf.elpi: the evaluator of L1 and of L1ᵃ.

   The same rules as the evaluator of L0 (Eval.v), on the types of L1: a binder
   binds an atom, opened with its value (Elpi's hypothesis `atom-value x V`). It
   is polymorphic in the index I of L1, since the annotations of L1ᵃ do not
   change what a program computes: the same evaluator runs L1 and L1ᵃ. It shares
   the operations of the evaluator of L0. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Anf Domain Eval.

Import ListNotations.
Open Scope Z_scope.

Section EvalAnf.
Variable N : Type.
Variable D : domain N.
Variable I : Type.

Definition aeval_atom (a : atom (val N)) : option (val N) :=
  match a with
  | AVar v => Some v
  | ANum s => let* x := dom_lit D s in Some (VReal x)
  | ANat k => Some (VInt k)
  end.

(* A body: its lets in order, then its tail atom. *)
Fixpoint aeval (b : anf (val N) I) : option (val N) :=
  match b with
  | ALet _ e b' => let* ve := aeval_value e in aeval (b' ve)
  | ARet x => aeval_atom x
  end
with aeval_value (e : value (val N) I) : option (val N) :=
  match e with
  | AOp1 f a => let* va := aeval_atom a in eval_op1 D f va
  | AOp2 f a b => let* va := aeval_atom a in let* vb := aeval_atom b in eval_op2 D f va vb
  | AGet a i =>
      match aeval_atom a, aeval_atom i with
      | Some (VArray l), Some (VInt k) => let* x := nth_z k l in Some (VReal x)
      | _, _ => None
      end
  | ASet a i x =>
      match aeval_atom a, aeval_atom i, aeval_atom x with
      | Some (VArray l), Some (VInt k), Some (VReal y) => let* l1 := replace_nth_z k y l in Some (VArray l1)
      | _, _, _ => None
      end
  | AIte c t e =>
      match aeval_atom c with
      | Some (VBool true) => aeval t
      | Some (VBool false) => aeval e
      | _ => None
      end
  | AMap lo hi b =>
      match aeval_atom lo, aeval_atom hi with
      | Some (VInt i), Some (VInt j) => let* xs := eval_map (fun v => aeval (b v)) i (count i j) in Some (VArray xs)
      | _, _ => None
      end
  | AFold _ lo hi init b =>
      match aeval_atom lo, aeval_atom hi, aeval_atom init with
      | Some (VInt i), Some (VInt j), Some s => eval_fold (fun v w => aeval (b v w)) i (count i j) s
      | _, _, _ => None
      end
  end.

Fixpoint aeval_definition (d : adefinition (val N) I) (args : list (val N)) : option (val N) :=
  match d, args with
  | AArg _ _ _ f, a :: args' => aeval_definition (f a) args'
  | ABody _ b, [] => aeval b
  | _, _ => None
  end.

Definition aeval_function (f : afunction I) (args : list (val N)) : option (val N) :=
  aeval_definition (afdef f (val N)) args.

End EvalAnf.

Arguments aeval_atom {N}.  Arguments aeval {N} D {I}.  Arguments aeval_value {N} D {I}.
Arguments aeval_definition {N} D {I}.  Arguments aeval_function {N} D {I}.
