(* Annotate.v — mirrors annotate.elpi: from L1 to L1ᵃ, the analyses run once
   and recorded on the term.

   Every let gets `LetAnn varied active computed` and every fold
   `FoldAnn varied live records`. Elpi reads its input and builds its output in
   one traversal, under the same binders. In PHOAS the analyses read the input
   with their own variables (avar, Atoms.v), while the output is over any type
   of variables V: the closed input is instantiated twice, the standard PHOAS
   technique. The first traversal, at avar, computes the annotations as Elpi
   does, into a tree that follows the lets and the folds of the body; the
   second, at V, rebuilds the body with them. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Operations Atoms Activity Tbr.

Import ListNotations.
Open Scope bool_scope.

(* The annotations of a body, in the shape of its lets, and of a value, in the
   shape of the bodies it contains. *)
Inductive ltree : Type :=
| TLet (a : ann) (v : vtree) (rest : ltree)
| TRet
with vtree : Type :=
| TLeaf                                           (* an operation: no body inside *)
| TIte (t e : ltree)
| TMap (b : ltree)
| TFold (a : ann) (b : ltree).

Section Annotate.
Variable cv : bool.                               (* computes-value: mode adjoint-value *)

(* annotate-body M B: B transposed in sweep M. A let is active when it is
   varied and useful to the result; its value is computed by its sweep when the
   rest of the body reads it, and, in the forward sweep, when a fold in it records. *)
Fixpoint annotate_body_t (m : sweep) (k : nat) (b : anf avar bare) : ltree :=
  match b with
  | ALet _ e b' =>
      let varied := varied_value k e in
      let x := let_binder k e in
      let '(u, l) := needs cv m (S k) (b' x) in
      let useful := atom_member (AVar x) u in
      let needed := atom_member (AVar x) l in
      let active := varied && useful in
      let computed := needed || (sweep_eqb m Forward && records cv k e) in
      TLet (LetAnn varied active computed) (annotate_value_t k e) (annotate_body_t m (S k) (b' x))
  | ARet _ => TRet
  end

(* The bodies inside a value are replayed. *)
with annotate_value_t (k : nat) (e : value avar bare) : vtree :=
  match e with
  | AIte _ t e => TIte (annotate_body_t Replay k t) (annotate_body_t Replay k e)
  | AMap _ _ b => TMap (annotate_body_t Replay (S k) (b (fresh k)))
  | AFold _ lo hi init b =>
      let varied := fold_varied k init b in
      let live := state_live cv k init b in
      let recs := records cv k e in
      let '(i, s) := fold_binders k init b in
      TFold (FoldAnn varied live recs) (annotate_body_t Replay (S (S k)) (b i s))
  | _ => TLeaf
  end.

(* The arguments are opened with their activity, as by the transformations. *)
Fixpoint annotate_definition_t (k : nat) (d : adefinition avar bare) : ltree :=
  match d with
  | AArg _ _ r f => annotate_definition_t (S k) (f (AV k (varied_role r)))
  | ABody _ b => annotate_body_t Forward k b
  end.

End Annotate.

Section Rebuild.
Variable V : Type.

(* The body over V with the annotations of the tree; the tree follows the body,
   so the defaults (no annotation) are never used. *)
Definition no_ann : ann := LetAnn false false false.

Fixpoint rebuild (b : anf V bare) (t : ltree) : anf V ann :=
  match b, t with
  | ALet _ e b', TLet a vt rest => ALet a (rebuild_value e vt) (fun v => rebuild (b' v) rest)
  | ALet _ e b', TRet => ALet no_ann (rebuild_value e TLeaf) (fun v => rebuild (b' v) TRet)
  | ARet x, _ => ARet x
  end
with rebuild_value (e : value V bare) (t : vtree) : value V ann :=
  match e, t with
  | AOp1 f a, _ => AOp1 f a
  | AOp2 f a b, _ => AOp2 f a b
  | AGet a i, _ => AGet a i
  | ASet a i v, _ => ASet a i v
  | AIte c t e, TIte t1 e1 => AIte c (rebuild t t1) (rebuild e e1)
  | AIte c t e, _ => AIte c (rebuild t TRet) (rebuild e TRet)
  | AMap lo hi b, TMap bt => AMap lo hi (fun i => rebuild (b i) bt)
  | AMap lo hi b, _ => AMap lo hi (fun i => rebuild (b i) TRet)
  | AFold _ lo hi init b, TFold a bt => AFold a lo hi init (fun i s => rebuild (b i s) bt)
  | AFold _ lo hi init b, _ => AFold no_ann lo hi init (fun i s => rebuild (b i s) TRet)
  end.

Fixpoint rebuild_definition (d : adefinition V bare) (t : ltree) : adefinition V ann :=
  match d with
  | AArg n ty r f => AArg n ty r (fun v => rebuild_definition (f v) t)
  | ABody r b => ABody r (rebuild b t)
  end.

End Rebuild.

(* annotate Value F: F annotated for a tangent or an adjoint that computes the
   derivative only (Value = false), or for an adjoint that computes the value
   of the function as well (Value = true). *)
Definition annotate (cv : bool) (f : afunction bare) : afunction ann :=
  let t := annotate_definition_t cv 0 (afdef f avar) in
  AFunction (afname f) (fun V => rebuild_definition V (afdef f V) t).
