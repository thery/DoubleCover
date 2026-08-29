(* =========================================================================  *)
(*  RowFoldWrite.v -- what one write of the folded level is worth.            *)
(* =========================================================================  *)

(* RowFoldLvl.v proves the folded level and the folded run sound, on two      *)
(* hypotheses: Qlo_st and Qhi_st, one for each half of a source word.  They   *)
(* say that a member reading a bit of what the level ors in is one move of H  *)
(* out from a member the source had.  This file discharges them.              *)
(*                                                                            *)
(* THE GATHER IS THE PLAIN WRITE ON THE RENAMED SOURCE, and every leg of that *)
(* is now a fact: the page leg is RowFoldSrc.gathM, the group leg is the way  *)
(* the tables are indexed and needs no lemma at all, and the bit leg is       *)
(* RowFoldGath.cloX_bit.  What the member does under the two is               *)
(* RowFoldSrc.gather_conj_memb for the renaming and RowMembChk.memb2tab_moveC *)
(* for the move.                                                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Root Coord.
Require Import Diameter Moves Sym16 Sym16Row.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembChk.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart.
Require Import RowTabF RowFoldTab RowFoldSym RowFoldConj RowFoldGath RowFoldSrc.
Require Import RowFoldLvl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- where a member of the row stands ------------------------------------ *)

(* The row is the superflip coset, so the position a member stands for is the *)
(* superflip undone and then the member's own permutation.  It is RowInst's   *)
(* pos, written out on the real tables.                                       *)
Definition mposC (pg gr bt : int) : {perm facelet} :=
  superflip^-1 * pt flast (memb2tab (unplace e8invi e4ofi par8i par4i pg gr bt)).

Definition PdC (d : nat) (pg gr bt : int) : Prop :=
  mposC pg gr bt \in ball Sset d.

Lemma PdCW d pg gr bt : PdC d pg gr bt -> PdC d.+1 pg gr bt.
Proof. by apply: (subsetP (ball_mono Sset d)). Qed.

(* ---- the sixteen do not move the row, at any depth ----------------------- *)

(* Sym16Row.sym16_row says this at twenty; the run needs it at every depth,   *)
(* and needs it both ways round, because two members that fold together are   *)
(* each other's image under two of the sixteen.                               *)
Lemma sym16_rown i n h : (i < 16)%N ->
  superflip^-1 * h \in ball Sset n ->
  superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i)) \in ball Sset n.
Proof.
move=> hi hb; have := sym16_ball hi hb.
by rewrite conjMg conjVg (sym16_sf hi).
Qed.

Lemma sym16_rownV i n h : (i < 16)%N ->
  superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i)) \in ball Sset n ->
  superflip^-1 * h \in ball Sset n.
Proof.
move=> hi hb.
have he : superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i))
        = (superflip^-1 * h) ^ pt 47 (nth [::] sym16ts i).
  by rewrite conjMg conjVg (sym16_sf hi).
rewrite he in hb.
by have := sym16_ballV hi hb; rewrite conjgK.
Qed.

(* ---- so a member and the place it folds to stand or fall together -------- *)

Lemma fold_conjC pg gr bt : inrange pg gr bt ->
  exists2 i, (i < 16)%N &
    mposC (PArray.get fkeepi (fkpt (PArray.get fpgi pg)))
          (sgrmv fsgri (fren (PArray.get fpgi pg))
             (Uint63.lxor (fpar (PArray.get fpgi pg))
                (if (bt <? 12)%uint63 then 0%uint63 else 1%uint63)) gr)
          (sbtmv fsbti (fren (PArray.get fpgi pg)) bt)
    = mposC pg gr bt ^ pt 47 (nth [::] sym16ts i).
Proof.
move=> hr; have [i hi he] := fold_conj_memb hr.
exists i; first exact: hi.
by rewrite /mposC he conjMg conjVg (sym16_sf hi).
Qed.
