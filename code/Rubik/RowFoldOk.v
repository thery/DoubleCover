(* =========================================================================  *)
(*  RowFoldOk.v -- what a full folded map answers.                            *)
(* =========================================================================  *)

(* The folded map keeps one page of each orbit under the sixteen renamings,   *)
(* and a member is read through the renaming that folds its page.  This file  *)
(* says the easy half of what that is worth: if every kept page has all       *)
(* twenty four bits then every member reads as marked, whatever page it is    *)
(* on.  What is still owed is the other half -- that a bit set at a kept page *)
(* means the member is within the depth -- which is RowRun's soundness redone *)
(* for fmark, and Sym16Row.sym16_row is what carries it round the orbit.      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowFold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FoldOk.

(* the three tables a member is read through: where its page is kept and by   *)
(* which renaming, the renaming on a group, the renaming on a bit            *)
Variable fpg fsgr fsbt : arr.

(* A FULL FOLDED MAP ANSWERS EVERY MEMBER.  The three conditions are that     *)
(* the fold lands in range: a kept page, a group of that page, one of the     *)
(* twenty four bits.  They are checks on the generated tables and are         *)
(* discharged where those tables are.                                         *)
Lemma mfullf_ftest m pg gr bt :
  (to_nat (fkpt (PArray.get fpg pg)) < nrepn)%N ->
  (to_nat (sgrmv fsgr (fren (PArray.get fpg pg))
             (fpar (PArray.get fpg pg)
              lxor (if bt <? 12 then 0%uint63 else 1%uint63))
             gr) < ngroupn)%N ->
  (sbtmv fsbt (fren (PArray.get fpg pg)) bt <? nbiti) ->
  mfullf m -> ftest fpg fsgr fsbt m pg gr bt.
Proof.
move=> hr hg hb hm.
rewrite /ftest /fget.
have h1 := Row.iter_at hm hr.
have h2 := Row.iter_at h1 hg.
move: h2 => /eqb_spec ->.
by rewrite (allbitsP hb).
Qed.

End FoldOk.
