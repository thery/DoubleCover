(* =========================================================================  *)
(*  RowFoldPorb.v -- Porb on the real tables.                                 *)
(* =========================================================================  *)

(* RowFoldOk asks one thing of what the folded map claims: that members which *)
(* fold to the same page, the same group and the same bit stand or fall       *)
(* together.  RowFoldMem.fold_Porb proves it from three things, and all three *)
(* are now facts on the real tables:                                          *)
(*                                                                            *)
(*   the two ranges     RowFoldTot.sgrmvT and sbtmvT, at EVERY index;         *)
(*   fold_conj          RowFoldWrite.fold_conjC, the place a member folds to  *)
(*                      holds that member renamed.                            *)

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
Require Import RowFoldLvl RowFoldWrite RowFoldTot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* MEMBERS THAT FOLD TOGETHER STAND OR FALL TOGETHER, at every depth.         *)
Lemma PorbC d p q c pg gr bt :
  inrange p q c -> inrange pg gr bt ->
  pchk (fkpt (PArray.get fpgi p)) = pchk (fkpt (PArray.get fpgi pg)) ->
  Uint63.add (poff (fkpt (PArray.get fpgi p)))
    (sgrmv fsgri (fren (PArray.get fpgi p))
       (fpar (PArray.get fpgi p) lxor
          (if (c <? 12)%uint63 then 0%uint63 else 1%uint63)) q)
  = Uint63.add (poff (fkpt (PArray.get fpgi pg)))
      (sgrmv fsgri (fren (PArray.get fpgi pg))
         (fpar (PArray.get fpgi pg) lxor
            (if (bt <? 12)%uint63 then 0%uint63 else 1%uint63)) gr) ->
  ~~ (Uint63.land (bitof (sbtmv fsbti (fren (PArray.get fpgi p)) c))
                  (bitof (sbtmv fsbti (fren (PArray.get fpgi pg)) bt))
        =? 0)%uint63 ->
  PdC d p q c -> PdC d pg gr bt.
Proof.
apply: (@fold_Porb fpgi fsgri fsbti fkeepi
          (fun pg' gr' bt' => sgrmvT _ _ _) (fun pg' bt' => sbtmvT _ _)
          mposC fold_conjC).
Qed.
