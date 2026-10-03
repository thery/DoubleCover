(* Transform.v — mirrors the helpers of derivative.elpi, used by the
   transformations into L2: the composition of scoped code, the spelling of
   atoms, and the opening of the binders of L1ᵃ.

   Elpi opens a binder of L1ᵃ with hypotheses on its variable: the variable of
   the generated code that holds it (`stored x V`), its type (`of x T`), whether
   it is varied and carries a tangent and an adjoint (`varied x`, `has-dot x`,
   `has-bar x`), for an argument its name and role (`argument x N R`). In PHOAS
   the variables of L1ᵃ are instantiated with the record of that information,
   `tvar`, whose stored variable is a variable of the output, so a
   transformation is one traversal. Two more hypotheses of Elpi become fields:
   - `recorded N`, on a storage N, holds for every variable stored in N: a
     variable stored in the storage of another one inherits its flag;
   - `written Y` is compared with an atom (`written Init`): the arguments have
     an identity, their position, as has the probe that tests the shape
     `(x\ a-ret x)` of a body; the other variables need none. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Derivative Operations.

Import ListNotations.
Open Scope string_scope.
Open Scope bool_scope.

Section Transform.
Variable V : Type.                                (* the variables of the generated code *)

Record tvar : Type := TVar {
  tstored : dvar V;                               (* stored x V *)
  tty : ty;                                       (* of x T *)
  targ : option (string * role);                  (* argument x N R *)
  tvaried : bool;                                 (* varied x *)
  tdot : bool;                                    (* has-dot x *)
  tbar : bool;                                    (* has-bar x *)
  trecorded : bool;                               (* recorded N, N its storage *)
  tid : option nat                                (* the identity of an argument, or of the probe *)
}.

Definition code := scoped V (list (dstmt V)).

(* sbind S K: K applied to the value of S, under the binders of S followed by
   those K creates. Composing with sbind keeps the order of creation. *)
Fixpoint sbind {A B : Type} (s : scoped V A) (k : A -> scoped V B) : scoped V B :=
  match s with
  | Done x => k x
  | Named n f => Named n (fun v => sbind (f v) k)
  | Fresh p f => Fresh p (fun v => sbind (f v) k)
  end.

(* sflatten Ss: the statements of Ss, in order, under all their binders. *)
Fixpoint sflatten (ss : list code) : code :=
  match ss with
  | [] => Done []
  | s :: ss' => sbind s (fun x => sbind (sflatten ss') (fun y => Done (app x y)))
  end.

(* spell A: an atom as an expression. *)
Definition spell (a : atom tvar) : dexpr V :=
  match a with
  | ANum s => DReal s
  | ANat k => DInt k
  | AVar x => DVar (tstored x)
  end.

(* spell-partial P: a partial derivative as an expression. *)
Fixpoint spell_partial (p : pexpr tvar) : dexpr V :=
  match p with
  | PAtom a => spell a
  | PNum s => DReal s
  | POp1 f a => DOp1 f (spell_partial a)
  | POp2 f a b => DOp2 f (spell_partial a) (spell_partial b)
  end.

(* varied A, as the transformations see it. *)
Definition tvaried_atom (a : atom tvar) : bool :=
  match a with AVar x => tvaried x | _ => false end.

(* of A T *)
Definition tof (a : atom tvar) : ty :=
  match a with ANum _ => Real | ANat _ => Integer | AVar x => tty x end.

(* dot X: the tangent of an atom, 0 when it has none. *)
Definition dot (a : atom tvar) : dexpr V :=
  match a with
  | AVar x => if tdot x then DVar (DotOf (tstored x)) else DReal "0"
  | _ => DReal "0"
  end.

(* bar X: the adjoint of an atom; none when it carries no derivative. *)
Definition bar (a : atom tvar) : option (dexpr V) :=
  match a with
  | AVar x => if tbar x then Some (DVar (BarOf (tstored x))) else None
  | _ => None
  end.

Definition scale (p e : dexpr V) : dexpr V :=
  match p with
  | DReal s => if String.eqb s "1" then e
               else if String.eqb s "-1" then DOp1 Neg e
               else DOp2 Mul p e
  | _ => DOp2 Mul p e
  end.

Fixpoint sum (es : list (dexpr V)) : dexpr V :=
  match es with
  | [] => DReal "0"
  | [e] => e
  | e :: es' => DOp2 Add e (sum es')
  end.

(* The probe, and the shape (x\ a-ret x): the body only returns its variable. *)
Definition probe : tvar := TVar ResultVar Real None false false false false (Some 0).

Definition is_tail (b : tvar -> anf tvar ann) : bool :=
  match b probe with
  | ARet (AVar x) => match tid x with Some 0 => true | _ => false end
  | _ => false
  end.

(* written Init: Init is the written argument. *)
Definition is_written (written : option (atom tvar)) (a : atom tvar) : bool :=
  match written, a with
  | Some (AVar y), AVar x =>
      match tid x, tid y with Some i, Some j => Nat.eqb i j | _, _ => false end
  | _, _ => false
  end.

(* with-storage E B K: K applied to the variable that holds the value bound by
   `let E B`, with whether that storage is recorded: for arrays, the storage
   updated in place (the loop state, or the written argument); otherwise a
   fresh local. *)
Definition with_storage {A : Type} (written : option (atom tvar)) (e : value tvar ann)
  (b : tvar -> anf tvar ann) (k : dvar V -> bool -> scoped V A) : scoped V A :=
  match e with
  | ASet (AVar a) _ _ => k (tstored a) (trecorded a)
  | AFold _ _ _ (AVar init) _ =>
      match tty init with
      | Array _ => k (tstored init) (trecorded init)
      | _ => Fresh "t" (fun v => k (DBound v) false)
      end
  | AMap _ _ _ =>
      match is_tail b, written with
      | true, Some (AVar y) => k (tstored y) (trecorded y)
      | _, _ => Fresh "t" (fun v => k (DBound v) false)
      end
  | _ => Fresh "t" (fun v => k (DBound v) false)
  end.

(* Opening the binders of L1ᵃ with everything the transformations know about
   them. A varied value gets a tangent and an adjoint. *)
Definition open_let (t : ty) (n : dvar V) (vr : bool) (rec : bool) : tvar :=
  TVar n t None vr vr vr rec None.

(* open-fold Varied T N I: the index and the state of a fold, held in I and N. *)
Definition open_fold (vr : bool) (t : ty) (n i : dvar V) (rec : bool) : tvar * tvar :=
  (TVar i Integer None false false false false None, TVar n t None vr vr vr rec None).

Definition open_index (i : dvar V) : tvar := TVar i Integer None false false false false None.

(* with-arguments D K: binds the arguments of the definition D, then runs K on
   the arguments with their variables, the result, the body and the written
   argument. An argument is varied, with a tangent and an adjoint, when its role
   says so. *)
Fixpoint open_arguments {A : Type} (d : adefinition tvar ann) (pos : nat) (acc : list (decl * dvar V))
  (k : list (decl * dvar V) -> aresult tvar -> anf tvar ann -> option (atom tvar) -> scoped V A) : scoped V A :=
  match d with
  | AArg n t r f =>
      Named n (fun v =>
        let vr := varied_role r in
        let x := TVar (DBound v) t (Some (n, r)) vr vr vr false (Some (S pos)) in
        open_arguments (f x) (S pos) ((Decl n t r, DBound v) :: acc) k)
  | ABody (AWrites y) b => k (rev acc) (AWrites y) b (Some y)
  | ABody res b => k (rev acc) res b None
  end.

Definition with_arguments {A : Type} (d : adefinition tvar ann)
  (k : list (decl * dvar V) -> aresult tvar -> anf tvar ann -> option (atom tvar) -> scoped V A) : scoped V A :=
  open_arguments d 0 [] k.

(* type-of E T: the type of a value in a well-formed body (WellFormed.v), with
   the types the transformations know. *)
Definition type_of (e : value tvar ann) : ty :=
  match e with
  | AOp1 f a => match operation1 f with Some (ta, t, _) => if ty_eqb (tof a) ta then t else Real | None => Real end
  | AOp2 f a b => match operation2_typed f (tof a) (tof b) with Some (t, _) => t | None => Real end
  | AGet _ _ => Real
  | ASet a _ _ => tof a
  | AIte _ _ _ => Real
  | AMap (ANat l) (ANat h) _ => Array (h - l)
  | AMap _ _ _ => Real
  | AFold _ _ _ init _ => tof init
  end.

End Transform.

Arguments TVar {V}.  Arguments tstored {V}.  Arguments tty {V}.  Arguments targ {V}.
Arguments tvaried {V}.  Arguments tdot {V}.  Arguments tbar {V}.  Arguments trecorded {V}.
Arguments tid {V}.
Arguments sbind {V A B}.  Arguments sflatten {V}.  Arguments spell {V}.  Arguments spell_partial {V}.
Arguments tvaried_atom {V}.  Arguments tof {V}.  Arguments dot {V}.  Arguments bar {V}.
Arguments scale {V}.  Arguments sum {V}.  Arguments is_tail {V}.  Arguments is_written {V}.
Arguments with_storage {V A}.  Arguments open_let {V}.  Arguments open_fold {V}.
Arguments open_index {V}.  Arguments with_arguments {V A}.  Arguments type_of {V}.
