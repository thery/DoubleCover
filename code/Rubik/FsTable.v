(* =========================================================================  *)
(*  FsTable.v -- The pruning table, and the two checks it has to pass.        *)
(* =========================================================================  *)

From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From mathcomp Require Import all_ssreflect all_fingroup.
From Rubik Require Import ssrint63.
Require Import Fstab FsData.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- The table ----------------------------------------------------------- *)

(* FsData.v holds the 2 097 152 words; this is the only place they become an
   array.  The Eval matters: without it the fold is redone on every Require.  *)
Definition mkarr (l : seq int) : arr :=
  (fix go (a : arr) (i : int) (l : seq int) {struct l} : arr :=
     if l is x :: l' then go (PArray.set a i x) (i + 1)%uint63 l' else a)
    (PArray.make nwordsi 0%uint63) 0%uint63 l.

(* NO Eval vm_compute HERE, ON PURPOSE, FOR NOW.  With it, the .vo holds the
   evaluated 2 097 152 entry array and nothing is rebuilt on Require -- which
   is what we want -- but the native compiler then has to emit that array and
   never produces NRubik_FsTable.cmxs, so every file requiring this one dies
   with "Unbound module NRubik_FsTable".  FsData.v's list compiles natively
   fine; it is the array value that it cannot do.

   And the Eval was never worth much anyway, native or not.  The fold is a
   second; the search it precedes is minutes at depth 12 and hours at depth
   19.  It is paid once per vm_compute -- not per node, not per Require, not
   per array access -- so even with one worker per root prefix it is 36
   seconds against hours.  Storing the table twice to save that was the wrong
   trade; the native failure only made us notice.

   It would start to matter if the work per vm_compute were itself about a
   second, i.e. if the search were split into thousands of tiny files.  At 36
   prefixes we are nowhere near that, and the fix then would be bigger
   chunks, not a second copy of the table.                                    *)
Definition fstab : arr := mkarr fsdata.

(* ---- What Fstab.v asks of it --------------------------------------------- *)

(* Both are now one read of a literal array rather than an induction.         *)
Lemma fstab_len : PArray.length fstab = nwordsi.
Proof. by vm_compute. Qed.

Lemma fstab_def : PArray.default fstab = 0%uint63.
Proof. by vm_compute. Qed.

(* ---- The two checks ------------------------------------------------------ *)

(* One lookup: the summary of the identity has to hold 0.                     *)
Lemma fstab_check0 : check0 fstab.
Proof. by vm_compute. Qed.

(* THE SECOND COMPUTATION lives in Fsmain.v, not here.
                                                                              *)
(* It used to be admitted here as                                             *)
(*                                                                            *)
(*    Lemma fstab_checkStep mtabs : checkStep fstab mtabs.                    *)
(*                                                                            *)
(* quantified over every table list.  That is FALSE -- for                    *)
(* mtabs = [:: comp_tab U R ] the check fails inside the first 2 ^ 20         *)
(* coordinates, since a two move composition cuts the flip x slice            *)
(* distance by two and breaks the local certificate -- and it was not         *)
(* something a computation could discharge either, mtabs being a variable.    *)
(* Far.v took it as the justification of Dfsd_step, so the depth 12           *)
(* theorem rested on a false axiom.                                           *)
(*                                                                            *)
(* The honest statement is at the concrete moves, and needs Moves.v, which    *)
(* this file must not depend on -- it would drag the move tables into the     *)
(* 55 MB table file.  So it lives in Fsmain.v, where the sixteen slices       *)
(* are glued.                                                                 *)
