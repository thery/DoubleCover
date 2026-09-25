(* =========================================================================  *)
(*  RowFoldCubRealB.v -- the folded row's certificate, with the fast leaf.    *)
(* =========================================================================  *)

(* RowFoldCubReal's certificate, with RowLeafFast's bitleaf at the leaf in    *)
(* the place of ytomemb tomembi.  The run is generic in its leaf and asks two *)
(* things of it, both at a leaf only; bitleafE says bitleaf is the old leaf   *)
(* there, so the two carry over by one rewrite and nothing else changes.      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Cyc Sym Root Coord Sym16 Sym16Row.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowMembi.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart RowTabF RowFoldTab.
Require Import RowFoldSym RowFoldConj RowFoldGath RowFoldSrc RowFoldLvl.
Require Import RowFoldWrite RowFoldTot RowFoldPorb RowFoldSrch RowFoldRun.
Require Import RowFoldEmpty RowFoldFinal.
Require Import RowFoldCubReal RowLeafFast RowFoldRunC RowFoldFinalC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

(* ---- the two things the run asks of its leaf ----------------------------- *)

Lemma ybitleafE y : ypstok y -> bitleaf y = ytomemb tomembi y.
Proof. exact: bitleafE. Qed.

Lemma yleaf_membB c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> membok par8i par4i (bitleaf y).
Proof. by move=> hc hy hg hs; rewrite (ybitleafE hy); exact: (yleaf_membi hc hy hg hs). Qed.

Lemma yfleaf_posB c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> posC (bitleaf y) = yposp y.
Proof. by move=> hc hy hg hs; rewrite (ybitleafE hy); exact: (yfleaf_posi hc hy hg hs). Qed.

Section FCubRealB.

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Hypothesis hfm : fsmoveC.

Variables forb fpop : arr.
Variable ishm : int.

(* ---- the map the run leaves, every optimization on ----------------------- *)

(* THE RUN IS RowFoldRunC's: the prepass only when the cuts are on, as the   *)
(* OCaml and hcoset do.                                                       *)
Definition yfcmfinoB : rmap :=
  fmfinoC F frep fsym twsym dnlo dnhi fllo flhi
         (RowInst.cstep actfsri) zstepi bitleaf okmvv ycsolved
         RowInst.croot yrooti srch 20 forb fpop ishm.

Lemma yfcmfinoB_sound : soundatf fpgi fsgri fsbti (PdC 20) yfcmfinoB.
Proof.
refine (@fmfinoC_sound F frep fsym twsym dnlo dnhi fllo flhi
          arr (RowInst.cstep actfsri) zstepi bitleaf yposp okmvv
          ycsolved RowInst.croot yrooti srch 20 ycoordP ypstok
          ycoord_root yroot_ball yroot_pok
          (ycoord_step (r_fsstepP hfm)) yxstep_pok yxstep_pos
          yleaf_membB yfleaf_posB forb fpop ishm).
Qed.

Definition yfcwitsoB : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        yfcmfinoB rowwits.

Lemma yfcwitsoB_sound : soundatf fpgi fsgri fsbti (PdC 20) yfcwitsoB.
Proof. exact: (fwits_sound wits24C yfcmfinoB_sound). Qed.

(* THE CERTIFICATE, with the fast leaf                                        *)
Theorem real_superflip_row_foldoB : mfullf ffuli yfcwitsoB ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hf h hh.
have [x [hx hxe]] :=
  row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC hh.
case E : (place24 e8numi e4biti x) => [[pg gr] bt].
have hr := place24_range e8okC e4okC hx E.
have hu := unplace24_place24 e8okC e4okC hx E.
have hall : forall pg' gr' bt', inrange24 pg' gr' bt' -> PdC 20 pg' gr' bt'.
  refine (@foldf_all fpgi fsgri fsbti ffuli ffulT (PdC 20) fkptT
            (fun a b c => sgrmvT _ _ _) (fun a b => sbtmvT _ _)
            yfcwitsoB hf yfcwitsoB_sound).
have := hall _ _ _ hr.
by rewrite /PdC /mposC hu hxe.
Qed.

End FCubRealB.
