(* =========================================================================  *)
(*  RowFoldCubProofO.v -- the optimised folded run is RowFoldCubDefD's run,   *)
(*  so it is sound.                                                           *)
(* =========================================================================  *)

(* Each search of RowFoldCubDefO is shown equal to RowFoldCubDefD's at the   *)
(* same tables, by induction on the depth left, with RowOpt's equations for  *)
(* the faster reads and RowFoldLvlG's for the level.  The run is then        *)
(* rowmapiD itself, and RowFoldCubProofD's theorem carries over.             *)
(*                                                                            *)
(* NO GOAL BELOW COMPARES TWO SEARCHES BY CONVERSION.  One step of each      *)
(* fixpoint is unfolded by cbv with the fixpoint named, and every            *)
(* difference is closed by an equation.                                      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf RowWits.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowMembi FsmChk.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowFoldTab RowFoldSrch RowFoldCubDef RowFoldCubProof.
Require Import RowFoldSrchI RowFoldSrchIC RowLeafFast.
Require Import RowCoord RowCoordLeaf RowFoldN RowFoldNSim RowFoldCubDefD.
Require Import RowFoldCubProofD RowOpt RowFoldLvlG RowFoldCubDefO.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Local Open Scope uint63_scope.

(* ---- RowFoldCubDefD's searches, at its tables ------------------------------ *)

Local Notation fsrski :=
  (fsrchski e8numi e4biti fpgi fsgri fsbti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd ishmi).
Local Notation isrskL :=
  (isrchskL e8numi e4biti fpgi fsgri fsbti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd ishmi).
Local Notation iwsL :=
  (iwsrchL e8numi e4biti fpgi fsgri fsbti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd forbi ishmi).
Local Notation wlf :=
  (wleaf e8numi e4biti fpgi fsgri fsbti cmemb ycsolvedd forbi).
Local Notation wsl :=
  (wslv e8numi e4biti fpgi fsgri fsbti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd
     RowInst.croot crootD srchd forbi ishmi).
Local Notation wrn :=
  (wrun e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
     mgri mswi mloi mhii p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd
     RowInst.croot crootD srchd forbi fpopi ishmi).

(* ---- three small tools ------------------------------------------------------ *)

(* two ifs on the same test, compared branch by branch                        *)
Lemma if_elseO (A : Type) (b : bool) (a x y : A) :
  x = y -> (if b then a else x) = (if b then a else y).
Proof. by move=> ->. Qed.

Lemma if_thenO (A : Type) (b : bool) (x y z : A) :
  (b -> x = y) -> (if b then x else z) = (if b then y else z).
Proof. by case: b => // ->. Qed.

(* ifoldM and ifold, their steps equal                                        *)
Lemma ifoldM_eqf n j (f g : int -> rmap * int -> rmap * int) a :
  (forall i b, f i b = g i b) -> ifoldM n j f a = ifold n j g a.
Proof.
by move=> hfg; elim: n j a => [|n ih] j a //=; rewrite hfg; apply: ih.
Qed.

(* THE TWO SIDES ARE CASED ON THEIR TESTS, NEVER COMPARED.  A test is taken *)
(* from the left side as it stands and destructed, which rewrites it on both *)
(* sides.  NOT case: -- ssreflect looks for the test's other occurrences up  *)
(* to conversion, and the conversions it tries run the searches; destruct    *)
(* abstracts it as it stands, and took 0.004 s where case: did not finish.   *)
Ltac cases_on :=
  repeat (lazymatch goal with
          | |- (if ?b then _ else _) = _ =>
              destruct b; cbv beta match delta [negb andb]
          end).

(* a leaf: the same term on both sides, or the hypothesis given             *)
Ltac leaf_by t :=
  lazymatch goal with
  | |- ?x = ?y => tryif constr_eq x y then reflexivity else t
  end.

(* ---- the marks --------------------------------------------------------------- *)

Lemma fmarknOE mn pg gr bt :
  fmarknO mn pg gr bt = fmarkn fpgi fsgri fsbti mn pg gr bt.
Proof.
case: mn => m n; rewrite /fmarknO /fmarkn; cbv beta iota zeta.
by rewrite sgrmvOE.
Qed.

Lemma wleafOE c x a : wleafO c x a = wlf c x a.
Proof.
rewrite /wleafO /wleaf place24OE.
case: (place24 e8numi e4biti (cmemb x)) => [[pg gr] bt]; cbv beta iota.
by rewrite fmarknwOE.
Qed.

(* ---- the stopping search ------------------------------------------------------ *)

Lemma fsrchskiOE cut togo :
  forall togoi c x msk pv enough mn,
  fsrchskiO cut togo togoi c x msk pv enough mn
  = fsrski cut togo togoi c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn.
  cbv beta match fix zeta delta [fsrchskiO fsrchski].
  case: (Uint63.leb enough mn.2); first by [].
  case: (ycsolvedd c); last by [].
  rewrite place24OE.
  case: (place24 e8numi e4biti (cmemb x)) => [[pg gr] bt]; cbv beta iota.
  by rewrite fmarknOE.
cbv beta match fix zeta delta [fsrchskiO fsrchski].
case: (Uint63.leb enough mn.2); first by [].
apply: ifoldM_eqf => k a; cbv beta.
rewrite okmvOE cstepOE p1gOE mmaskOE.
case: cut ih => ih; cases_on; leaf_by ltac:(exact: ih).
Qed.

Lemma isrchskLOE cut togo :
  forall togoi c x msk pv enough mn,
  isrchskLO cut togo togoi c x msk pv enough mn
  = isrskL cut togo togoi c x msk pv enough mn.
Proof.
elim: togo => [|togo ih] togoi c x msk pv enough mn.
  cbn beta match fix zeta delta [isrchskLO isrchskL].
  case: (Uint63.leb enough mn.2); first by [].
  exact: fsrchskiOE.
cbn beta match fix zeta delta [isrchskLO isrchskL].
case: (Uint63.leb enough mn.2); first by [].
case: togo ih => [|togo] ih; cbv beta match.
  apply: ifoldM_eqf => k a; cbv beta.
  rewrite okmvOE cstepOE.
  case: cut ih => ih; cases_on; leaf_by ltac:(apply: fsrchskiOE).
apply: ifoldM_eqf => k a; cbv beta.
rewrite okmvOE cstepOE p1gOE mmaskOE.
case: cut ih => ih; cases_on; leaf_by ltac:(exact: ih).
Qed.

(* ---- the counting search ------------------------------------------------------ *)

Lemma iwsrchLOE cut togo :
  forall togoi c x msk pv a,
  iwsrchLO cut togo togoi c x msk pv a = iwsL cut togo togoi c x msk pv a.
Proof.
elim: togo => [|togo ih] togoi c x msk pv a.
  cbn beta match fix zeta delta [iwsrchLO iwsrchL].
  exact: wleafOE.
cbn beta match fix zeta delta [iwsrchLO iwsrchL].
case: togo ih => [|togo] ih; cbv beta match.
  apply: ifoldM_eqf => k a'; cbv beta.
  rewrite okmvOE cstepOE.
  case: cut ih => ih; cases_on; leaf_by ltac:(apply: wleafOE).
apply: ifoldM_eqf => k a'; cbv beta.
rewrite okmvOE cstepOE p1gOE mmaskOE.
case: cut ih => ih; cases_on; leaf_by ltac:(exact: ih).
Qed.

(* ---- the level and the run ----------------------------------------------------- *)

Lemma wslvOE cut d m' nb : wslvO cut d m' nb = wsl cut d m' nb.
Proof.
rewrite /wslvO /wslv; cbv zeta.
rewrite p1gOE mmaskOE; cases_on;
  leaf_by ltac:(first [apply: isrchskLOE | apply: iwsrchLOE]).
Qed.

Lemma wrunOE n d n0 m dst : wrunO n d n0 m dst = wrn n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst.
  by cbv beta match fix delta [wrunO wrun].
cbv beta match fix zeta delta [wrunO wrun].
rewrite flevelgE.
case: (Uint63.ltb ncutb n0); cbv iota; rewrite wslvOE; exact: ih.
Qed.

(* ---- the map, the boolean, the theorem ----------------------------------------- *)

Lemma rowmapiOE n : rowmapiO n = rowmapiD n.
Proof. by rewrite /rowmapiO /rowmapiD wrunOE. Qed.

Lemma rowfulliOE : rowfulliO = rowfulliD.
Proof. by rewrite /rowfulliO /ycwitsoiO /rowfulliD /ycwitsoiD rowmapiOE. Qed.

Theorem row_of_runO : rowfulliO = true ->
  forall h, h \in H -> (superflip^-1 * h)%g \in ball Sset 20.
Proof. by rewrite rowfulliOE; exact: row_of_runD. Qed.
