(* Supported.v — the programs on which the tangent mode is proved correct:
   well-formed (WellFormed.v), and `supported`, six more conditions, each
   excluding a well-formed program on which the generated tangent is wrong.

   Each was checked on the Elpi tool (`elpi -I code/elpiDiff primal.elpi
   -exec main -- <case> tangent <outdir>`), which generates the same code:

   1. A map starts at index 0. `y = map 1 3 (i\ x * x)`, writing y of extent
      2: the generated loop writes y[1] and y[2], out of the array, where the
      map gives y[0] and y[1].

   2. A map writes a dependent argument. With y inout,
      `let s = y[0] in map 0 1 (i\ 1.0)`: the map is constant, not varied, and
      the tangent does not write y_dot, which keeps the derivative of the
      input instead of 0.

   3. An in-place loop nested in another does not read the state of the outer
      one. `fold 0 1 y (n w\ fold 0 2 w (j v\ set v j (w[0] + 1)))`, y inout:
      the source reads w, the array before the inner loop, but the generated
      code reads y, updated in place by the inner loop: from y = [a, b], the
      source gives [a+1, a+1], the generated primal [a+1, a+2].

   4. A body that computes an array (the function writing it, or an in-place
      loop) does not end with another array argument. `writes y` with body
      `x`, x an independent array: the generated tangent is empty, y and
      y_dot are not written.

   5. An argument whose role is independent or inout is a real or an array.
      An independent integer n makes `n + 1` varied, and the tangent defines
      its derivative from `n_dot`, which is not a parameter (simplify removes
      the definition, never used, but the unsimplified program reads an
      undefined variable).

   6. A function writes a real or an array: well_formed refuses to write an
      integer, not a boolean. `writes y`, y a dependent boolean, with body
      `x < 1`: the tangent does not write y (the generated L2 is the single
      definition `const bool t1 = x < 1`; Elpi writes no header).

   The conditions are checked as well_formed checks a function, with the
   same variables (vinfo) opened the same way. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Operations Normalize WellFormed.

Import ListNotations.
Open Scope bool_scope.

(* The written argument is dependent. *)
Definition written_dependent (written : option (atom vinfo)) : bool :=
  match written with
  | Some (AVar y) => match varg y with Some (_, Dependent) => true | _ => false end
  | _ => false
  end.

(* A returned array is the written argument, or not an argument. *)
Definition returns_ok (written : option (atom vinfo)) (x : atom vinfo) : bool :=
  match x with
  | AVar v => negb (ty_is_array (vty v))
              || match varg v with
                 | None => true
                 | Some _ => match written with Some y => same_atom x y | None => false end
                 end
  | _ => true
  end.

Definition is_zero (a : atom vinfo) : bool :=
  match a with ANat 0 => true | _ => false end.

Definition state_id (p : place) : option nat :=
  match p with ArrayBody _ (AVar s) => Some (vid s) | _ => None end.

Section Supported.
Variable written : option (atom vinfo).

(* supported_body p k b: the body b, in place p, its binders numbered from k
   and opened as typecheck opens them, meets the conditions 1 to 4. *)
Fixpoint supported_body (p : place) (k : nat) (b : anf vinfo bare) : bool :=
  match b with
  | ALet _ e b' =>
      let tail := is_tail b' k in
      let te := fst (typecheck_value written p tail k e) in
      supported_value p k e && supported_body p (S k) (b' (VInfo k te None))
  | ARet x => returns_ok written x
  end
with supported_value (p : place) (k : nat) (e : value vinfo bare) : bool :=
  match e with
  | AIte _ t e => supported_body InBranch k t && supported_body InBranch k e
  | AMap lo _ b =>
      is_zero lo && written_dependent written
      && supported_body ScalarBody (S k) (b (VInfo k Integer None))
  | AFold _ _ _ init b =>
      match of_atom init with
      | Real => supported_body ScalarBody (S (S k)) (b (VInfo k Integer None) (VInfo (S k) Real None))
      | Array n =>
          let i := VInfo k Integer None in
          let s := VInfo (S k) (Array n) None in
          match state_id p with
          | Some sid => negb (occurs_anf sid (S (S k)) (b i s))
          | None => true
          end
          && supported_body (ArrayBody (AVar i) (AVar s)) (S (S k)) (b i s)
      | _ => true
      end
  | _ => true
  end.

End Supported.

(* The written argument is a real or an array (condition 6). *)
Definition writes_real_or_array (written : option (atom vinfo)) : bool :=
  match written with
  | Some (AVar y) => match vty y with Real | Array _ => true | _ => false end
  | Some _ => false
  | None => true
  end.

(* Condition 5, on the arguments, then 6 and 1 to 4 on the body. *)
Fixpoint supported_definition (k : nat) (d : adefinition vinfo bare) : bool :=
  match d with
  | AArg n t r f =>
      (negb (varied_role r) || match t with Real | Array _ => true | _ => false end)
      && supported_definition (S k) (f (VInfo k t (Some (n, r))))
  | ABody r b =>
      let written := match r with AWrites y => Some y | AReturns _ => None end in
      writes_real_or_array written && supported_body written Top k b
  end.

Definition supported (f : afunction bare) : bool := supported_definition 0 (afdef f vinfo).
