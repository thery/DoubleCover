(* =========================================================================  *)
(*  RowCubReal.v -- the row on the PLAIN map, with nothing left open but the *)
(*  run.                                                                     *)
(* =========================================================================  *)

(* RowReal DISCHARGES EVERY CHECK the row asks for, on the real tables, and   *)
(* leaves exactly one thing open: the map is full, which is a run.  Nothing   *)
(* here repeats any of that.  RowCubInst's row asks for the SAME checks, so   *)
(* the only new line is the run, and it is a different run: the search        *)
(* carries twenty cubies instead of a forty eight entry table.                *)
(*                                                                            *)
(* MEASURED at depth thirteen on roquableu: the search is 236.5 s carrying    *)
(* the table and 141.7 s carrying the twenty, against 68.9 s with no          *)
(* position at all.  So the row costs a third less.                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import RowReal RowMembi RowMark RowSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section CubReal.

(* THE FOLDED PHASE ONE TABLE IS A VARIABLE HERE, and that is not a gap: no   *)
(* proof in the tree says what it holds.  The distance and the moves it names *)
(* are numbers the search tests, and a table that prunes too little only      *)
(* makes the search bigger.  So the theorem holds for any of them, and the    *)
(* run names the real one.  RowFoldCubReal does the same.                     *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.
Variable ishm : int.

(* THE PREPASS IS A PARAMETER, and nothing here cares which it is.  RowMap's  *)
(* is one; RowLvl's prepassD, which reads each page's chunk once and puts it  *)
(* back once, is another and is proved equal to it.                           *)
Variable prep : rmap -> rmap -> rmap.

Hypothesis prep_eq : forall m dst,
  prep m dst = prepass mpgi mgri mswi mloi mhii m dst.

(* the flip and slice move table's certificate, as RowReal carries it *)
Hypothesis hfm : fsmoveC.

(* ---- what the run buys --------------------------------------------------- *)

(* THIS FILE RUNS NOTHING.  RowCubDef names the map the twenty leave and the  *)
(* one boolean about it; RowCubBool settles that boolean in a process that    *)
(* loads no proof.  Here is what its being true buys, and RowCubDone puts     *)
(* the two together.                                                         *)

(* ---- what RowLvl's level asks of the move tables ------------------------- *)

(* A move sends a page to a page and a group to a group.  RowInst's pgok and  *)
(* grok say exactly that and the instance has already settled them.           *)
Lemma pgm_rangeC k pg : (to_nat k < nhn)%N -> (pg <? npagei)%uint63 ->
  (RowMap.pgmv mpgi k pg <? npagei)%uint63.
Proof. by move=> hk hp; apply: (iter_at (iter_at pgokC hk) (ltn_npagei hp)). Qed.

Lemma grm_rangeC k gr : (to_nat k < nhn)%N -> (gr <? ngroupi)%uint63 ->
  (RowMap.grmv mgri k gr <? ngroupi)%uint63.
Proof. by move=> hk hg; apply: (iter_at (iter_at grokC hk) (ltn_ngroupi hg)). Qed.

(* ---- the map, named ------------------------------------------------------ *)

(* The map the run leaves, and the same with the witnesses marked in.  They   *)
(* are named here so that RowCubProof can match RowCubDef's names against     *)
(* them by unfolding: left to itself the unifier does not fail when a name    *)
(* will not match -- it reduces, and reducing this is the run again, in the   *)
(* kernel.                                                                    *)
Definition ycmfinsp : rmap :=
  ymfinsk e8numi e4biti F frep fsym twsym dnlo dnhi fllo flhi
          ishm prep actfsri tomembi okmvv srch 20.

Definition ycwitsr : rmap :=
  foldr (fun t m => let: (pg, gr, bt, _) := t in mmark m pg gr bt)
        ycmfinsp rowwits.

(* ---- the map is sound, and stays sound when the witnesses go in ---------- *)

(* RowFoldCubReal goes through yfcmfino_sound and yfcwitso_sound; these are   *)
(* the same two on the plain map.  Each goal already names the map, so        *)
(* nothing is left for the unifier to find.                                   *)
Lemma ycmfinsp_sound :
  RowRun.soundat e8invi e4ofi par8i par4i
                 (RowFinal.pos (RowInst.ptab memb2tab)) ycmfinsp 20.
Proof.
rewrite /ycmfinsp.
exact: (ymfinsk_sound e8okC e4okC prep_eq memb2tab_okC srcokC halfokC
          (r_fsstepP hfm) r_leaf_membi r_tomembi_tab
          pgokC grokC btokC memb2tab_moveC).
Qed.

(* RowFoldCubReal states fwits_sound here rather than in the general file,    *)
(* fully instantiated, and this is that lemma on the plain map.               *)
(* NO `//=' HERE.  The base case is a soundat, and a goal handed to `done' is *)
(* unfolded and evaluated -- which here means the map.                        *)
Lemma pwits_sound l m :
  wgood e8invi e4ofi par8i par4i (RowInst.ptab memb2tab) l ->
  RowRun.soundat e8invi e4ofi par8i par4i
                 (RowFinal.pos (RowInst.ptab memb2tab)) m 20 ->
  RowRun.soundat e8invi e4ofi par8i par4i
                 (RowFinal.pos (RowInst.ptab memb2tab))
    (foldr (fun t m' => let: (pg, gr, bt, _) := t in mmark m' pg gr bt) m l)
    20.
Proof.
elim: l => [|t l ih].
  by move=> _ hm; exact: hm.
case: t => [[[pg gr] bt] w] /andP[/and3P[hi hs hw] hl] hm.
apply: mmark_sound.
- exact: hi.
- exact: (RowFinal.wokP (RowInst.ptab_ok memb2tab_okC) hw hs).
exact: ih hl hm.
Qed.

Lemma ycwitsr_sound :
  RowRun.soundat e8invi e4ofi par8i par4i
                 (RowFinal.pos (RowInst.ptab memb2tab)) ycwitsr 20.
Proof. exact: (pwits_sound witsokC ycmfinsp_sound). Qed.

(* ---- the certificate, with the optimizations on -------------------------- *)

Theorem real_superflip_row_p : mfull ycwitsr ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hf h hh.
have [x [hx hxe]] :=
  row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC hh.
case E : (place e8numi e4biti x) => [[pg gr] bt].
have hr := place_range e8okC e4okC hx E.
have hu := unplace_place e8okC e4okC hx E.
have := ycwitsr_sound hr (mfullP hf hr).
by rewrite /RowRun.wthn hu (RowInst.posE memb2tab_okC) hxe.
Qed.

End CubReal.
