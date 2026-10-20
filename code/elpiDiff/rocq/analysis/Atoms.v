(* Atoms.v — mirrors the sets of atoms and atoms-of of anf.elpi, for the
   analyses.

   The analyses compare variables (Elpi's same_term) and read whether they are
   varied (the hypothesis `varied x` of activity.elpi): their variables are
   instantiated with `avar`, an identity numbered in order and that flag. A
   set of atoms is a list compared by identity; the binders a function opens to
   look into a term are numbered from k on, beyond the variables in scope, as
   Elpi's pi gives fresh variables. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf.

Import ListNotations.
Open Scope bool_scope.

Record avar : Type := AV {
  aid : nat;                                      (* the identity of the
    variable *)
  avaried : bool                                  (* varied x *)
}.

(* same_term on atoms: the same variable. *)
Definition same_term (a b : atom avar) : bool :=
  match a, b with
  | AVar x, AVar y => Nat.eqb (aid x) (aid y)
  | _, _ => false
  end.

(* Sets of atoms, as lists compared with same_term. In a set an atom is a bound
   variable. *)
Definition atom_member (x : atom avar) (l : list (atom avar)) : bool :=
  existsb (same_term x) l.

Definition atom_remove (x : atom avar) (l : list (atom avar)) : list (atom avar)
  :=
  filter (fun y => negb (same_term x y)) l.

(* atom-union L L': L with the atoms of L' it lacks, without duplicates. *)
Fixpoint atom_union (l l' : list (atom avar)) : list (atom avar) :=
  match l' with
  | [] => l
  | x :: xs => if atom_member x l then atom_union l xs else atom_union (x :: l)
    xs
  end.

(* The bound variables a term of L1 mentions, its own binders excluded. *)
Definition atoms_of_atom (a : atom avar) : list (atom avar) :=
  match a with AVar _ => [a] | _ => [] end.

Fixpoint atoms_of_atoms (l : list (atom avar)) : list (atom avar) :=
  match l with
  | [] => []
  | a :: l' => atom_union (atoms_of_atom a) (atoms_of_atoms l')
  end.

(* A variable opened to look into a binder. *)
Definition fresh (k : nat) : avar := AV k false.

Fixpoint atoms_of_anf {I : Type} (k : nat) (b : anf avar I) : list (atom avar)
  :=
  match b with
  | ALet _ e b' =>
      let x := fresh k in
      atom_union (atoms_of_value k e)
        (atom_remove (AVar x) (atoms_of_anf (S k) (b' x)))
  | ARet x => atoms_of_atom x
  end
with atoms_of_value {I : Type} (k : nat) (e : value avar I) : list (atom avar)
  :=
  match e with
  | AOp1 _ a => atoms_of_atom a
  | AOp2 _ a b => atoms_of_atoms [a; b]
  | AGet a i => atoms_of_atoms [a; i]
  | ASet a i v => atoms_of_atoms [a; i; v]
  | AIte c t e => atom_union (atom_union (atoms_of_atom c) (atoms_of_anf k t))
    (atoms_of_anf k e)
  | AMap lo hi b =>
      let i := fresh k in
      atom_union (atoms_of_atoms [lo; hi])
        (atom_remove (AVar i) (atoms_of_anf (S k) (b i)))
  | AFold _ lo hi init b =>
      let i := fresh k in let s := fresh (S k) in
      atom_union (atoms_of_atoms [lo; hi; init])
                 (atom_remove (AVar s)
                   (atom_remove (AVar i) (atoms_of_anf (S (S k)) (b i s))))
  end.

Fixpoint atoms_of_pexpr (p : pexpr avar) : list (atom avar) :=
  match p with
  | PAtom a => atoms_of_atom a
  | PNum _ => []
  | POp1 _ a => atoms_of_pexpr a
  | POp2 _ a b => atom_union (atoms_of_pexpr a) (atoms_of_pexpr b)
  end.
