(* =========================================================================  *)
(*  RowCubProof.v -- what the plain run's answer buys.                        *)
(* =========================================================================  *)

(* rowfullpiO = true -> the row of the superflip is within twenty.  Nothing   *)
(* is computed here: RowCubBool settles the boolean and RowCubDone puts the   *)
(* two together.                                                              *)
(*                                                                            *)
(* The certificate is over RowSrchN's run (runskn_sound, which does not look  *)
(* at the count); rowmappiD is that run over the four numbers (RowSrchNSim),  *)
(* and rowmappiO is rowmappiD, each of its functions shown equal to its       *)
(* RowSrch, RowSrchC or RowSrchN original at the same constants.              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowPrep RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import RowReal FsmChk RowMark RowSrch.
Require Import Fold FoldTables P1Fdec P1FTable RowMask RowLvl.
Require Import RowSrchP RowSrchC RowCubReal RowFoldCubReal RowRealLeaf.
Require Import RowLeafFast.
Require Import RowCoord RowCoordLeaf RowCoordStep RowCoordRun.
Require Import RowSrchN RowSrchNSim RowRunConst RowOpt RowCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* ---- the certificate over RowSrchN's run --------------------------------- *)

Section CubRealD.

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.
Variable ishm : int.

Variable prep : rmap -> rmap -> rmap.
Hypothesis prep_eq : forall m dst,
  prep m dst = prepass cpgi cfli mgri mswi mloi mhii m dst.

Hypothesis hfm : fsmoveC.

(* ---- the map the run leaves ---------------------------------------------- *)

(* THE RUN IS RowSrchC's: the prepass only when the cuts are on, as the OCaml *)
Definition ycmfinspD : rmap :=
  runskn e8numi e4biti prep F frep fsym twsym dnlo dnhi fllo flhi
        (RowInst.cstep actfsri) zstepi bitleaf okmvv ycsolved
        RowInst.croot yrooti srch ishm 20 0 0%uint63 (mkempty tt) (mkempty tt).

Lemma ycmfinspD_sound :
  RowRun.soundat e8invi e4ofi par8i par4i
                 (RowFinal.pos (RowInst.ptab memb2tab)) ycmfinspD 20.
Proof.
rewrite /ycmfinspD -{2}[20%N]add0n.
apply: (runskn_sound e8okC e4okC prep_eq ycoord_root yroot_ball yroot_pok
          (ycoord_step (r_fsstepP hfm)) yxstep_pok yxstep_pos
          yleaf_membB yleaf_posPB
          RowInst.hmv_Sset (RowInst.grpmvP srcokC halfokC cflokC)
          (RowInst.prep_move e8okC memb2tab_okC pgokC grokC btokC
             memb2tab_moveC cflokC cpgokC));
  exact: RowInst.sound_mempty.
Qed.

Definition ycwitsrD : rmap :=
  foldr (fun t m => let: (pg, gr, bt, _) := t in mmark m pg gr bt)
        ycmfinspD rowwits48.

Lemma ycwitsrD_sound :
  RowRun.soundat e8invi e4ofi par8i par4i
                 (RowFinal.pos (RowInst.ptab memb2tab)) ycwitsrD 20.
Proof. exact: (pwits_sound witsokC ycmfinspD_sound). Qed.

(* ---- the certificate ----------------------------------------------------- *)

Theorem real_superflip_row_pD : mfull ycwitsrD ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hf h hh.
have [x [hx hxe]] :=
  row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC hh.
case E : (place e8numi e4biti x) => [[pg gr] bt].
have hr := place_range e8okC e4okC hx E.
have hu := unplace_place e8okC e4okC hx E.
have := ycwitsrD_sound hr (mfullP hf hr).
by rewrite /RowRun.wthn hu (RowInst.posE memb2tab_okC) hxe.
Qed.

End CubRealD.

(* ---- the run over the four numbers is that run --------------------------- *)

(* the run over the four numbers leaves the map the run over the cubies does  *)
Lemma rowmappiDE : rowmappiD 20 =
  ycmfinspD p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
            ishmi (prepassD cpgi cfli mgri mswi mloi mhii).
Proof.
rewrite /rowmappiD /ycmfinspD.
rewrite (@runskni_coord fsmoveCP cmemb cofy_step cmembE).
by apply: runskni_eq.
Qed.

Lemma rowwitspiDE : rowwitspiD =
  ycwitsrD p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
           ishmi (prepassD cpgi cfli mgri mswi mloi mhii).
Proof. by rewrite /rowwitspiD rowmappiDE /wmarkof /ycwitsrD. Qed.

Theorem row_of_runpiD : rowfullpiD = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
rewrite /rowfullpiD rowwitspiDE => hf.
exact: (real_superflip_row_pD
          (prepassD_eq cfli mswi mloi mhii pgm_rangeC grm_rangeC) fsmoveCP hf).
Qed.

(* ---- the optimised run is that run --------------------------------------- *)

Local Open Scope uint63_scope.

(* ---- the originals at rowmappiD's constants ------------------------------ *)

Local Notation srk :=
  (RowSrch.srchski e8numi e4biti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved RowRunConst.ishmi).

Local Notation srkL :=
  (RowSrchC.srchskiL e8numi e4biti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved RowRunConst.ishmi).

Local Notation slv :=
  (RowSrchN.slvlskni e8numi e4biti p1ftab frepi fsymi twsymi
     dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
     RowInst.croot (cofy yrooti) srch RowRunConst.ishmi).

Local Notation rsk :=
  (RowSrchN.runskni e8numi e4biti (prepassD cpgi cfli mgri mswi mloi mhii)
     p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
     (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
     RowInst.croot (cofy yrooti) srch RowRunConst.ishmi).

(* RowReal.okmvv and RowFoldCubDef.okmvvd are the same body                   *)
Lemma okmvOEv pv k : okmvO pv k = okmvv pv k.
Proof. by rewrite okmvOE. Qed.

(* ---- the searches -------------------------------------------------------- *)

(* cbn unfolds one step of each fixpoint and folds the recursive calls back   *)
(* under their names, so the induction hypothesis applies to them; it does    *)
(* not unfold the tables, which are other constants.                          *)
(*                                                                            *)
(* NO GOAL IS CLOSED BY CONVERSION.  Two sides that are not the same term     *)
(* make the unifier unfold them, and unfolding a search runs it.  same closes *)
(* a goal whose two sides are the same term and fails otherwise; the tests    *)
(* are split with destruct on the test itself, which abstracts it             *)
(* syntactically, where case: ifP matches up to conversion.                   *)
(* two walks that take the same step are the same walk                        *)
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

(* ---- the level and the run ----------------------------------------------- *)

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

(* ---- the map, the witnesses, the boolean --------------------------------- *)

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
