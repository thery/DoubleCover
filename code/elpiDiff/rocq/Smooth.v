(* Smooth.v — the partial semantics of Abadi and Plotkin, with no Elpi
   counterpart.

   Abadi and Plotkin, "A Simple Differentiable Programming Language" (POPL
   2020), give a program the meaning of a partial function: a comparison of
   two equal reals is undefined, and so is an operation where it is not
   differentiable. Where the program is defined, it is defined around, on an
   open set, and smooth there; there, automatic differentiation computes its
   derivative.

   We get that semantics by evaluating in a domain that fails where they say
   undefined: `smooth_reals`, the reals of Domain.v, except at a tie of a
   comparison and at the points where an operation is not differentiable.
   The theorems on the derivatives assume that the program is `defined` at
   the point. *)

From Stdlib Require Import String ZArith List Reals.
From ElpiDiff Require Import Syntax Domain Eval.

Open Scope R_scope.

(* An operation fails where it is not differentiable: the logarithm and the
   square root at 0 and below, a negative power at 0. *)
Definition smooth_op1 (f : unary) (x : R) : option R :=
  match f with
  | Log | Sqrt => if Rle_dec x 0 then None else real_op1 f x
  | Pow k => if (k <? 0)%Z then if Req_dec_T x 0 then None else real_op1 f x
             else real_op1 f x
  | _ => real_op1 f x
  end.

(* A division fails when the divisor is 0. *)
Definition smooth_op2 (f : binary) (x y : R) : option R :=
  match f with
  | Divide => if Req_dec_T y 0 then None else real_op2 f x y
  | _ => real_op2 f x y
  end.

(* A comparison fails at a tie: when the two values are equal. *)
Definition smooth_cmp (f : binary) (x y : R) : option bool :=
  if Req_dec_T x y then None else real_cmp f x y.

Definition smooth_reals : domain R := Domain real_lit smooth_op1 smooth_op2 smooth_cmp.

(* The program f is defined at the arguments args, in the sense of Abadi and
   Plotkin: its evaluation compares no two equal reals and applies no
   operation where it is not differentiable, so that it is smooth around
   args. *)
Definition defined (f : function) (args : list (val R)) : Prop :=
  exists v, eval_function smooth_reals f args = Some v.
