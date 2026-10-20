(* Adjudge.v — mirrors the driver of adjudge.elpi: the passes chained, from
   the functions of a case to the header of their derivatives and the
   diagnostics of the refused ones. *)

From Stdlib Require Import String List.
From ElpiDiff Require Import Syntax Anf Normalize WellFormed Annotate Derivative
  Tangent Adjoint
  Simplify Target Lower Cxx.

Import ListNotations.
Open Scope string_scope.

(* The modes: tangent, adjoint (the derivative only) and adjoint-value (the
   value and the derivative); only the last one computes the value in its
   forward sweep. *)
Inductive mode : Type := ModeTangent | ModeAdjoint | ModeAdjointValue.

Definition mode_value (m : mode) : bool := match m with ModeAdjointValue => true
  | _ => false end.

Definition mode_name (m : mode) : string :=
  match m with ModeTangent => "tangent" | ModeAdjoint => "adjoint" |
    ModeAdjointValue => "adjoint-value" end.

(* check F: F in L1, when it is expressible there, with its diagnostic. *)
Definition check (f : function) : option (afunction bare) * diagnostic :=
  if expressible f then let a := normalize f in (Some a, well_formed a)
  else (None, Error "a function can only write a dependent or inout argument").

(* differentiate Mode F: the derivative program, in the derivative IR. *)
Definition differentiate (m : mode) (a : afunction ann) : dfunction :=
  match m with
  | ModeTangent => tangent a
  | ModeAdjoint => adjoint false a
  | ModeAdjointValue => adjoint true a
  end.

(* transform before lowering: annotate, differentiate, simplify. *)
Definition transform (m : mode) (a : afunction bare) : dfunction :=
  simplify (differentiate m (annotate (mode_value m) a)).

(* main: the header of the well-formed functions of a case (none when there
   is none), and the diagnostics of the refused ones, "name: message". *)
Definition main (m : mode) (source : string) (fs : list function) : option
  string * list string :=
  let checked := map (fun f => (fname f, check f)) fs in
  let wf := flat_map (fun '(_, (a, d)) => match a, d with Some a, Ok => [a] | _,
    _ => [] end) checked in
  let diags := flat_map (fun '(n, (_, d)) => match d with Error msg =>
    [n ++ ": " ++ msg] | Ok => [] end) checked in
  let header := match wf with
                | [] => None
                | _ => Some (header_string source
                  (lower_all (map (transform m) wf)))
                end in
  (header, diags).
