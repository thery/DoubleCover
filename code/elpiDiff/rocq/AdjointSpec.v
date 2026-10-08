(* AdjointSpec.v — the layout of the adjoint function: its arguments and its
   outputs, as AdjointMode.v states the correctness of the adjoint modes.

   The adjoint function (Adjoint.v) takes the primal arguments, then the
   adjoint of each argument that has a tangent (has_dot), then, for a
   returned value, the adjoint of the result: the seed. The seed of a written
   argument is the initial value of its adjoint. The adjoints of the other
   arguments are accumulated into: they leave the function with their initial
   value plus the gradient. As the tangents of TangentTop.v, the reals of
   every argument are laid out in one list (in_dim, DualsDerive.v): xb, the
   initial adjoints, and g, the gradient computed. *)

From Stdlib Require Import String ZArith List Bool Reals.
From ElpiDiff Require Import Syntax Anf Derivative Domain Eval EvalAnf Exec Normalize WellFormed.
From ElpiDiff Require TangentTop.
From ElpiDiff Require Import DualsDerive.

Import ListNotations.
Open Scope list_scope.
Open Scope R_scope.

Notation has_dot := TangentTop.has_dot.
Notation nreals := TangentTop.nreals.

(* The value v with its reals replaced by those of l. *)
Definition with_list (v : val R) (l : list R) : val R :=
  match v with
  | VReal _ => VReal (hd 0 l)
  | VArray a => VArray (firstn (length a) l)
  | _ => v
  end.

(* The adjoints given to the function: the seed yb for the written argument,
   the reals of xb for the others. *)
Fixpoint bar_inputs (ds : list decl) (x : list (val R)) (xb yb : list R) : list (val R) :=
  match ds, x with
  | d :: ds', v :: x' =>
      let m := nreals v in
      (if has_dot d then [with_list v (if written_decl d then yb else firstn m xb)] else []) ++
      bar_inputs ds' x' (skipn m xb) yb
  | _, _ => []
  end.

(* The arguments of the adjoint function: the primal arguments x, the
   adjoints, then the seed of a returned real. *)
Definition adjoint_inputs (ds : list decl) (x : list (val R)) (xb yb : list R) : list (val R) :=
  x ++ bar_inputs ds x xb yb ++ (if existsb written_decl ds then [] else [VReal (hd 0 yb)]).

Definition lsub (a b : list R) : list R := map (fun '(p, q) => p - q) (combine a b).

(* The gradient: for each argument with an adjoint, its final value minus its
   initial value, the seed excepted; 0 for the others. bars are the final
   values of the adjoints, in order. *)
Fixpoint gradient (ds : list decl) (x : list (val R)) (xb : list R) (bars : list (val R)) : option (list R) :=
  match ds, x with
  | d :: ds', v :: x' =>
      let m := nreals v in
      if has_dot d then
        match bars with
        | b :: bars' =>
            match gradient ds' x' (skipn m xb) bars' with
            | Some g =>
                let r := reals_of_val b in
                Some (app (if written_decl d then r else lsub r (firstn m xb)) g)
            | None => None
            end
        | [] => None
        end
      else option_map (fun g => app (repeat 0 m) g) (gradient ds' x' (skipn m xb) bars)
  | [], [] => Some []
  | _, _ => None
  end.

(* The value of the function, when the adjoint-value function gives it back: the
   returned value, or the final value of the written argument when it is
   dependent (an inout argument is passed by value). *)
Definition value_given (ds : list decl) (out : list (val R) * list (val R)) : option (val R) :=
  let '(finals, rets) := out in
  match TangentTop.index_of_written ds 0 with
  | None => match rets with [v] => Some v | _ => None end
  | Some j =>
      match nth_error ds j with
      | Some (Decl _ _ Dependent) => nth_error finals j
      | _ => None
      end
  end.

(* The function writes an inout argument. *)
Definition writes_inout (ds : list decl) : bool :=
  existsb (fun '(Decl _ _ r) => match r with Inout => true | _ => false end) ds.

(* What the adjoint function computes: the gradient, from the final values of
   the adjoints. *)
Definition adjoint_output (ds : list decl) (x : list (val R)) (xb : list R)
  (out : list (val R) * list (val R)) : option (list R) :=
  let '(finals, _) := out in
  gradient ds x xb (firstn (length (filter has_dot ds)) (skipn (length ds) finals)).

(* The dot product of two lists of reals. *)
Definition dotl (a b : list R) : R := fold_right Rplus 0 (map (fun '(p, q) => p * q) (combine a b)).
