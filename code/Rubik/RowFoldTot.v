(* =========================================================================  *)
(*  RowFoldTot.v -- the fold tables land in range at EVERY index.             *)
(* =========================================================================  *)

(* RowFoldOk and RowFoldMem ask three things of the fold tables with no       *)
(* premise at all: a page folds to a kept page, a group to a group, a bit to  *)
(* one of the twenty four -- for any number, not only for a page.  The        *)
(* sweeps in RowFoldConj answer them only where the argument is in range.     *)
(*                                                                            *)
(* THE GAP IS THE READ OUT OF BOUNDS, and PArray answers it: a read past the  *)
(* end gives the array's default.  So walking the array ITSELF -- every slot  *)
(* it has, plus its default -- settles every index there is, and that is what *)
(* these three sweeps do.                                                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Sym16 Moves.
Require Import Row RowMap RowFold RowTab RowTabF RowFoldTab RowFoldSym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

(* ---- every slot, and the default, is every index -------------------------- *)

Lemma get_tot (t : arr) (f : int -> bool) :
  iter (to_nat (PArray.length t)) 0%uint63 (fun i => f (PArray.get t i)) ->
  f (PArray.default t) -> forall i, f (PArray.get t i).
Proof.
move=> hi hd i.
have [h|h] := boolP (i <? PArray.length t)%uint63.
  by apply: (Row.iter_at hi); apply/nltbP; exact: h.
by rewrite (RowMap.get_oobE (negbTE h)).
Qed.

(* ---- a page folds to a kept page ----------------------------------------- *)

Definition fpgTC : bool :=
  iter (to_nat (PArray.length fpgi)) 0%uint63
    (fun i => (fkpt (PArray.get fpgi i) <? nrepi)) &&
  (fkpt (PArray.default fpgi) <? nrepi).
Lemma fpgTCP : fpgTC. Proof. by vm_compute. Qed.

Lemma fpgTCE : fpgTC =
  (iter (to_nat (PArray.length fpgi)) 0%uint63
     (fun i => (fkpt (PArray.get fpgi i) <? nrepi)) &&
   (fkpt (PArray.default fpgi) <? nrepi)).
Proof. by []. Qed.

Lemma fkptT pg : (to_nat (fkpt (PArray.get fpgi pg)) < nrepn)%N.
Proof.
apply/nltbP.
have h1 := fpgTCP; rewrite fpgTCE in h1.
have /andP[hi hd] := h1.
exact: (get_tot (f := fun w => (fkpt w <? nrepi)) hi hd pg).
Qed.

(* ---- a group goes to a group --------------------------------------------- *)

Definition fsgrTC : bool :=
  iter (to_nat (PArray.length fsgri)) 0%uint63
    (fun i => (PArray.get fsgri i <? ngroupi)) &&
  (PArray.default fsgri <? ngroupi).
Lemma fsgrTCP : fsgrTC. Proof. by vm_compute. Qed.

Lemma fsgrTCE : fsgrTC =
  (iter (to_nat (PArray.length fsgri)) 0%uint63
     (fun i => (PArray.get fsgri i <? ngroupi)) &&
   (PArray.default fsgri <? ngroupi)).
Proof. by []. Qed.

Lemma sgrmvT u pty g : (to_nat (sgrmv fsgri u pty g) < ngroupn)%N.
Proof.
apply/nltbP; rewrite /sgrmv.
have h1 := fsgrTCP; rewrite fsgrTCE in h1.
have /andP[hi hd] := h1.
exact: (get_tot (f := fun v => (v <? ngroupi)) hi hd _).
Qed.

(* ---- and a bit to one of the twenty four --------------------------------- *)

Definition fsbtTC : bool :=
  iter (to_nat (PArray.length fsbti)) 0%uint63
    (fun i => (PArray.get fsbti i <? nbiti)) &&
  (PArray.default fsbti <? nbiti).
Lemma fsbtTCP : fsbtTC. Proof. by vm_compute. Qed.

Lemma fsbtTCE : fsbtTC =
  (iter (to_nat (PArray.length fsbti)) 0%uint63
     (fun i => (PArray.get fsbti i <? nbiti)) &&
   (PArray.default fsbti <? nbiti)).
Proof. by []. Qed.

Lemma sbtmvT u bt : (sbtmv fsbti u bt <? nbiti).
Proof.
rewrite /sbtmv.
have h1 := fsbtTCP; rewrite fsbtTCE in h1.
have /andP[hi hd] := h1.
exact: (get_tot (f := fun v => (v <? nbiti)) hi hd _).
Qed.
