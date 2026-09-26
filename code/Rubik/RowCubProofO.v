(* =========================================================================  *)
(*  RowCubProofO.v -- the plain run over the constants is RowCubDefD's run.  *)
(* =========================================================================  *)

(* Each function of RowCubDefO is its RowSrch, RowSrchC or RowSrchN original *)
(* at the constants RowCubDefD hands them, step for step: RowOpt's lemmas    *)
(* say each fast read is the read it replaces, for every int, and the       *)
(* searches follow by induction.  row_of_runpiD then carries over.           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowSrch RowMark RowLvl RowSrchC RowLeafFast.
Require Import RowCubDef RowCubDefD RowCubProofD.
Require Import RowCoord RowCoordLeaf RowSrchN RowOpt RowCubDefO.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Local Open Scope uint63_scope.

(* ---- the originals at RowCubDefD's constants -------------------------------- *)

Local Notation srk :=
  (RowSrch.srchski e8numi e4biti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved RowCubDef.ishmi).

Local Notation srkL :=
  (RowSrchC.srchskiL e8numi e4biti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved RowCubDef.ishmi).

Local Notation slv :=
  (RowSrchN.slvlskni e8numi e4biti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
     RowInst.croot (cofy yrooti) srch RowCubDef.ishmi).

Local Notation rsk :=
  (RowSrchN.runskni e8numi e4biti (prepassD cpgi cfli mgri mswi mloi mhii)
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
     RowInst.croot (cofy yrooti) srch RowCubDef.ishmi).

(* RowReal.okmvv and RowFoldCubDef.okmvvd are the same body                   *)
Lemma okmvOEv pv k : okmvO pv k = okmvv pv k.
Proof. by rewrite okmvOE. Qed.

(* ---- the searches ----------------------------------------------------------- *)

(* cbn unfolds one step of each fixpoint and folds the recursive calls back   *)
(* under their names, so the induction hypothesis applies to them; it does   *)
(* not unfold the tables, which are other constants.                          *)
(*                                                                            *)
(* NO GOAL IS CLOSED BY CONVERSION.  Two sides that are not the same term     *)
(* make the unifier unfold them, and unfolding a search runs it.  same closes *)
(* a goal whose two sides are the same term and fails otherwise; the tests    *)
(* are split with destruct on the test itself, which abstracts it            *)
(* syntactically, where case: ifP matches up to conversion.                  *)
(* two walks that take the same step are the same walk                       *)
Lemma ifold_eqf (A : Type) n j (f g : int -> A -> A) a :
  (forall i b, f i b = g i b) -> ifold n j f a = ifold n j g a.
Proof.
by move=> hfg; elim: n j a => [|n ih] j a //=; rewrite hfg; apply: ih.
Qed.

Ltac same :=
  lazymatch goal with |- ?x = ?y => constr_eq x y; reflexivity end.

Lemma srchskiOE cut togo :
  forall togoi c x msk pv enough mn,
  srchskiO cut togo togoi c x msk pv enough mn
  = srk cut togo togoi c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn;
  cbn [srchskiO RowSrch.srchski];
  destruct (Uint63.leb enough mn.2); cbv beta match; try same.
  rewrite placeOE; same.
rewrite ifoldME; apply: ifold_eqf => k a; cbv beta.
rewrite okmvOEv cstepOE p1gOEs mmaskOE ih; same.
Qed.

Lemma srchskiLOE cut togo :
  forall togoi c x msk pv enough mn,
  srchskiLO cut togo togoi c x msk pv enough mn
  = srkL cut togo togoi c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn;
  cbn [srchskiLO RowSrchC.srchskiL];
  destruct (Uint63.leb enough mn.2); cbv beta match; try same.
  exact: srchskiOE.
case: togo ih => [|togo] ih; cbv beta match.
  rewrite ifoldME; apply: ifold_eqf => k a; cbv beta.
  rewrite okmvOEv cstepOE srchskiOE; same.
rewrite ifoldME; apply: ifold_eqf => k a; cbv beta.
rewrite okmvOEv cstepOE p1gOEs mmaskOE ih; same.
Qed.

(* ---- the level and the run -------------------------------------------------- *)

Lemma slvlskniOE cut d m' nb : slvlskniO cut d m' nb = slv cut d m' nb.
Proof.
rewrite /slvlskniO /RowSrchN.slvlskni; cbv zeta.
rewrite p1gOEs mmaskOE srchskiLOE; same.
Qed.

Lemma runskniOE n :
  forall d n0 m dst, runskniO n d n0 m dst = rsk n d n0 m dst.
Proof.
elim: n => [|n ih] d n0 m dst; cbn [runskniO RowSrchN.runskni]; first same.
rewrite !slvlskniOE !ih; same.
Qed.

(* ---- the map, the witnesses, the boolean ------------------------------------ *)

Lemma rowmappiOE n : rowmappiO n = rowmappiD n.
Proof. rewrite /rowmappiO /rowmappiD runskniOE; same. Qed.

Lemma rowwitspiOE : rowwitspiO = rowwitspiD.
Proof. rewrite /rowwitspiO /rowwitspiD rowmappiOE; same. Qed.

Lemma rowfullpiOE : rowfullpiO = rowfullpiD.
Proof. rewrite /rowfullpiO /rowfullpiD rowwitspiOE; same. Qed.

Local Close Scope uint63_scope.

Theorem row_of_runpiO : rowfullpiO = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof. by rewrite rowfullpiOE; exact: row_of_runpiD. Qed.
