(* Tbr.v — mirrors tbr.elpi: to-be-recorded, what the adjoint code needs,
   computed bottom-up.

   `needs m b = (U, L)` for a body b transposed in sweep m:
   - U, the atoms the value of b depends on through positions that carry a
     derivative (useful);
   - L, the atoms the adjoint code of b references by value.
   Elpi's hypothesis `computes-value` (mode adjoint-value: the forward sweep
   also reads the result) is the argument cv. Where Elpi's value-needs fails,
   on an operator without partial derivative, the sets here are empty: annotate
   only runs on well-formed functions, where it does not happen. *)

From Stdlib Require Import String ZArith List Bool.
From ElpiDiff Require Import Syntax Anf Operations Atoms Activity.

Import ListNotations.
Open Scope bool_scope.

Inductive sweep : Type :=
| Forward                                         (* the forward sweep of the
  adjoint: computes and records *)
| Replay.                                         (* a recomputation inside a
  reverse loop or branch: records nothing *)

Definition sweep_eqb (a b : sweep) : bool :=
  match a, b with Forward, Forward | Replay, Replay => true | _, _ => false end.

(* read-by A P R: the atoms the partial derivative P reads,
   when the operand A is varied. *)
Definition read_by (a : atom avar) (p : option (pexpr avar)) : list (atom avar)
  :=
  match p with
  | Some p => if varied a then atoms_of_pexpr p else []
  | None => []
  end.

Section Tbr.
Variable cv : bool.                               (* computes-value *)

Fixpoint needs (m : sweep) (k : nat) (b : anf avar bare) : list (atom avar) *
  list (atom avar) :=
  match b with
  | ALet _ e b' =>
      let v := varied_value k e in
      let x := let_binder k e in
      let '(ub, lb) := needs m (S k) (b' x) in
      let useful := atom_member (AVar x) ub in
      let needed := atom_member (AVar x) lb in
      let u0 := atom_remove (AVar x) ub in
      let l0 := atom_remove (AVar x) lb in
      let '(reads_e, flows_e) := if v && useful then value_needs k e else
        ([], []) in
      let atoms_e := if needed || (sweep_eqb m Forward && records k e) then
        atoms_of_value k e else [] in
      (atom_union u0 flows_e, atom_union (atom_union l0 reads_e) atoms_e)
  | ARet x =>
      (* the tail: the result is this atom; in the forward sweep of an
         adjoint-value, the result itself is read *)
      if sweep_eqb m Forward && cv then (atoms_of_atom x, atoms_of_atom x) else
        (atoms_of_atom x, [])
  end

(* value-needs E = (R, F): for an active value E, R the atoms its reverse reads,
   F the atoms its value depends on. Loop bodies and branches are always
     replayed. *)
with value_needs (k : nat) (e : value avar bare) : list (atom avar) * list
  (atom avar) :=
  match e with
  | AOp1 f a => (read_by a (partial1 f a), atoms_of_atom a)
  | AOp2 f a b =>
      if comparison f then ([], []) else
      match partial2 f a b with
      | Some (pa, pb) => (atom_union (read_by a (Some pa))
        (read_by b (Some pb)), atoms_of_atoms [a; b])
      | None => ([], atoms_of_atoms [a; b])
      end
  | AGet a i => (atoms_of_atom i, atoms_of_atom a)
  | ASet a i v => (atoms_of_atom i, atoms_of_atoms [a; v])
  | AIte c t e =>
      let '(ut, lt) := needs Replay k t in
      let '(ue, le) := needs Replay k e in
      (atom_union (atom_union (atoms_of_atom c) lt) le, atom_union ut ue)
  | AMap lo hi b =>
      let i := fresh k in
      let '(u, l) := needs Replay (S k) (b i) in
      (atom_union (atoms_of_atoms [lo; hi]) (atom_remove (AVar i) l),
        atom_remove (AVar i) u)
  | AFold _ lo hi init b =>
      let '(i, s) := fold_binders k init b in
      let '(u, l) := needs Replay (S (S k)) (b i s) in
      let u0 := atom_remove (AVar s) (atom_remove (AVar i) u) in
      let l0 := atom_remove (AVar s) (atom_remove (AVar i) l) in
      (atom_union (atoms_of_atoms [lo; hi]) l0,
        atom_union (atoms_of_atom init) u0)
  end

(* The forward sweep must run a let when a fold in it records something: when
   its state is recorded (state-live: the reverse loop reads it), or when a fold
   in its body records. *)
with records (k : nat) (e : value avar bare) : bool :=
  match e with
  | AFold _ _ _ init b =>
      let '(i, s) := fold_binders k init b in
      atom_member (AVar s) (snd (needs Replay (S (S k)) (b i s))) ||
        records_in (S (S k)) (b i s)
  | _ => false
  end

with records_in (k : nat) (b : anf avar bare) : bool :=
  match b with
  | ALet _ e b' => records k e || records_in (S k) (b' (let_binder k e))
  | ARet _ => false
  end.

End Tbr.


(* state-live Init B: the state of the fold is recorded before each overwrite
   iff the reverse loop reads it. *)
Definition state_live (cv : bool) (k : nat) (init : atom avar)
  (b : avar -> avar -> anf avar bare) : bool :=
  let '(i, s) := fold_binders k init b in
  atom_member (AVar s) (snd (needs cv Replay (S (S k)) (b i s))).
