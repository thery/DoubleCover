(* Activity.v — mirrors activity.elpi: varied, the forward half of activity
   analysis.

   A value is varied when it depends on an independent argument. Elpi declares
   a bound variable varied with a hypothesis when its binder is opened; here the
   variable is an `avar` (Atoms.v) that carries the flag. The binders opened to
   look into a term are numbered from k on. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Operations Atoms.

Import ListNotations.
Open Scope bool_scope.

(* varied A: the atom A depends on an independent argument. *)
Definition varied (a : atom avar) : bool :=
  match a with AVar v => avaried v | _ => false end.

(* varied-value E, varied-anf B: the value E, the body B depends on an independent argument. *)
Fixpoint varied_value (k : nat) (e : value avar bare) : bool :=
  match e with
  | AOp1 _ a => varied a
  | AOp2 f a b => if comparison f then false else varied a || varied b
  | AGet a _ => varied a
  | ASet a _ v => varied a || varied v
  | AIte _ t e => varied_anf k t || varied_anf k e
  | AMap _ _ b => varied_anf (S k) (b (fresh k))
  | AFold _ _ _ init b => varied init || varied_anf (S (S k)) (b (fresh k) (fresh (S k)))
  end
with varied_anf (k : nat) (b : anf avar bare) : bool :=
  match b with
  | ALet _ e b' => varied_anf (S k) (b' (AV k (varied_value k e)))     (* let-binder *)
  | ARet x => varied x
  end.

(* The state of a fold is varied when its initial value is, or when one pass of
   the body makes it varied starting from a passive state. *)
Definition fold_varied (k : nat) (init : atom avar) (b : avar -> avar -> anf avar bare) : bool :=
  varied init || varied_anf (S (S k)) (b (fresh k) (fresh (S k))).

(* Opening binders knowing whether the bound value is varied: the variable of
   `let E`, and the index and the state of a fold. *)
Definition let_binder (k : nat) (e : value avar bare) : avar := AV k (varied_value k e).

Definition fold_binders (k : nat) (init : atom avar) (b : avar -> avar -> anf avar bare) : avar * avar :=
  (AV k false, AV (S k) (fold_varied k init b)).
