(* Normalize.v — mirrors the pass of anf.elpi: normalize, from L0 to L1.

   `norm t k`: the continuation-passing formulation, as in Elpi: the
   continuation k is a body builder that receives the atom holding the value
   of t. Elpi opens a binder of the source with the hypothesis `as-atom x a`,
   the atom that stands for the source variable x; in PHOAS the source is
   normalized with its variables instantiated as atoms (`term (atom V)`), so a
   source variable is its atom: `Var a` normalizes to a. Where Elpi uses a
   continuation K as the binder of a let (`a-let bare E K`), the binder of
   ALet, over V, is `fun v => k (AVar v)`. *)

From Stdlib Require Import String ZArith List.
From ElpiDiff Require Import Syntax Anf.

Section Normalize.
Variable V : Type.                                (* the variables of L1 *)

Definition bind (k : atom V -> anf V bare) : V -> anf V bare := fun v => k (AVar v).

Fixpoint norm (t : term (atom V)) (k : atom V -> anf V bare) : anf V bare :=
  match t with
  | Num s => k (ANum s)
  | Nat n => k (ANat n)
  | Let_ e b => norm e (fun a => norm (b a) k)
  | Op1 f a => norm a (fun x => ALet Bare (AOp1 f x) (bind k))
  | Op2 f a b => norm a (fun x => norm b (fun y => ALet Bare (AOp2 f x y) (bind k)))
  | Get a i => norm a (fun x => norm i (fun j => ALet Bare (AGet x j) (bind k)))
  | Set_ a i v => norm a (fun x => norm i (fun j => norm v (fun w => ALet Bare (ASet x j w) (bind k))))
  | Ite c t e =>
      let t1 := norm t (fun x => ARet x) in
      let e1 := norm e (fun x => ARet x) in
      norm c (fun x => ALet Bare (AIte x t1 e1) (bind k))
  | Map lo hi b =>
      let b1 := fun v => norm (b (AVar v)) (fun x => ARet x) in
      norm lo (fun l => norm hi (fun h => ALet Bare (AMap l h b1) (bind k)))
  | Fold lo hi init b =>
      let b1 := fun v w => norm (b (AVar v) (AVar w)) (fun x => ARet x) in
      norm lo (fun l => norm hi (fun h => norm init (fun x => ALet Bare (AFold Bare l h x b1) (bind k))))
  | Var a => k a
  end.

(* norm-body T R: a body, ended by its atom. *)
Definition norm_body (t : term (atom V)) : anf V bare := norm t (fun x => ARet x).

(* normalize-result: a written argument is a variable, hence an atom. The case
   of a written literal or expression cannot occur on an expressible function
   (below), on which alone normalize is called: Elpi's normalize-result has no
   clause for it; here it gives the literal 0. *)
Definition normalize_result (r : result (atom V)) : aresult V :=
  match r with
  | Returns t => AReturns t
  | Writes (Var a) => AWrites a
  | Writes _ => AWrites (ANum "0")
  end.

Fixpoint normalize_definition (d : definition (atom V)) : adefinition V bare :=
  match d with
  | Arg n t r f => AArg n t r (fun v => normalize_definition (f (AVar v)))
  | Body r b => ABody (normalize_result r) (norm_body b)
  end.

End Normalize.

Arguments norm {V}.  Arguments norm_body {V}.  Arguments normalize_result {V}.
Arguments normalize_definition {V}.

(* expressible F: F has a counterpart in L1, where a function returns its result
   or writes it into an argument. In the result of a body, the only variables
   in scope are the arguments: a written argument is a variable. *)
Fixpoint expressible_definition (d : definition unit) : bool :=
  match d with
  | Arg _ _ _ f => expressible_definition (f tt)
  | Body (Returns _) _ => true
  | Body (Writes (Var _)) _ => true
  | Body (Writes _) _ => false
  end.

Definition expressible (f : function) : bool := expressible_definition (fdef f unit).

(* normalize F: the translation of F, which must be expressible. *)
Definition normalize (f : function) : afunction bare :=
  AFunction (fname f) (fun V => normalize_definition (fdef f (atom V))).

(* declarations D: the arguments of D as plain data, in order; its binders
   are opened at unit, as Elpi's `pi x` when only their shape matters. *)
Fixpoint declarations {I : Type} (d : adefinition unit I) : list decl :=
  match d with
  | ABody _ _ => nil
  | AArg n t r f => Decl n t r :: declarations (f tt)
  end.
