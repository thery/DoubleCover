(* =========================================================================  *)
(*  RowFoldCubReal.v -- the row on the FOLDED map, with nothing left open     *)
(*  but the run.                                                             *)
(* =========================================================================  *)

(* RowCubReal is this file on the plain map: everything proved except one     *)
(* boolean, which is the run.  This is the same on the folded map, and the    *)
(* difference is what the fold cost and what it saves.                        *)
(*                                                                            *)
(* THE FOLDED PHASE ONE TABLE IS A VARIABLE HERE, and that is not a gap: no   *)
(* proof in the tree says what it holds.  The distance and the mask are       *)
(* numbers the search tests, and a table that prunes too little only makes    *)
(* the search bigger.  So the theorem holds for any of them, and the run      *)
(* names the real one.                                                        *)
(*                                                                            *)
(* THE WITNESSES ARE MARKED IN, not held in a map of their own.  The plain    *)
(* row allocates a second whole map for thirty two bits and asks mfull2 of    *)
(* the two; here they are marked into the map the run leaves, which is        *)
(* already sound at twenty, and mfullf alone is the test.                     *)

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
Require Import Lehmer RowCub RowCubi RowCubInst RowReal.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart RowTabF RowFoldTab.
Require Import RowFoldSym RowFoldConj RowFoldGath RowFoldSrc RowFoldLvl.
Require Import RowFoldWrite RowFoldTot RowFoldPorb RowFoldSrch RowFoldRun.
Require Import RowFoldEmpty RowFoldFinal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

Section FCubReal.

(* the folded phase one table, which no proof here reads *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

(* the flip and slice move table's certificate, as RowReal carries it *)
Hypothesis hfm : fsmoveC.

(* ---- the one hypothesis that is not RowCubInst's word for word ----------- *)

(* RowFoldFinal asks for the position as posC writes it -- the superflip      *)
(* undone and then the member -- where RowCubInst gives RowFinal.pos of       *)
(* RowInst's ptab.  RowInst.posE says the two are the same.                   *)
Lemma yfleaf_pos c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c y -> posC (ytomemb tomemb y) = yposp y.
Proof.
move=> hc hy hg hs.
rewrite -(yleaf_pos memb2tab_okC r_tomemb_tab hc hy hg hs).
by rewrite /posC (RowInst.posE memb2tab_okC).
Qed.

(* ---- the map the folded run leaves --------------------------------------- *)

Definition yfcmfin : rmap :=
  fmfin F frep fsym twsym dnlo dnhi fllo flhi
        (RowInst.cstep actfsri) zstepi (ytomemb tomemb) okmvv ycsolved
        RowInst.croot yrooti srch 20.

Lemma yfcmfin_sound : soundatf fpgi fsgri fsbti (PdC 20) yfcmfin.
Proof.
refine (@fmfin_sound F frep fsym twsym dnlo dnhi fllo flhi
          arr (RowInst.cstep actfsri) zstepi (ytomemb tomemb) yposp okmvv
          ycsolved RowInst.croot yrooti srch 20 ycoordP ypstok
          ycoord_root yroot_ball yroot_pok
          (ycoord_step (r_fsstepP hfm)) yxstep_pok yxstep_pos
          (yleaf_memb r_leaf_memb) yfleaf_pos).
Qed.

(* ---- the witnesses, marked in rather than held in a map ------------------ *)

Lemma fwits_sound l m :
  wgood e8invi e4ofi par8i par4i (RowInst.ptab memb2tab) l ->
  soundatf fpgi fsgri fsbti (PdC 20) m ->
  soundatf fpgi fsgri fsbti (PdC 20)
    (foldr (fun t m' =>
              let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m' pg gr bt)
           m l).
Proof.
(* NO `//=' HERE.  The base case is a soundatf, and a goal handed to `done'  *)
(* is unfolded and evaluated -- which here means the map.                     *)
elim: l => [|t l ih].
  by move=> _ hm; exact: hm.
case: t => [[[pg gr] bt] w] /andP[/and3P[hi hs hw] hl] hm.
apply: fmark_sound.
- exact: hi.
- rewrite /PdC /mposC -(RowInst.posE memb2tab_okC).
  exact: (wokP (RowInst.ptab_ok memb2tab_okC) hw hs).
exact: ih hl hm.
Qed.

Definition yfcwits : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        yfcmfin rowwits.

Lemma yfcwits_sound : soundatf fpgi fsgri fsbti (PdC 20) yfcwits.
Proof. exact: (fwits_sound witsokC yfcmfin_sound). Qed.

(* ---- and the row of the superflip, with nothing left open but the run ---- *)

(* THE ONE THING LEFT IS A BOOLEAN, and it is the run: the folded map that    *)
(* twenty levels leave, with the thirty two witnesses marked into it, has no  *)
(* bit of the row clear.                                                      *)
Theorem real_superflip_row_fold : mfullf yfcwits ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hf h hh.
have [x [hx hxe]] :=
  row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC hh.
case E : (place e8numi e4biti x) => [[pg gr] bt].
have hr := place_range e8okC e4okC hx E.
have hu := unplace_place e8okC e4okC hx E.
have hall : forall pg' gr' bt', inrange pg' gr' bt' -> PdC 20 pg' gr' bt'.
  refine (@foldf_all fpgi fsgri fsbti (PdC 20) fkptT
            (fun a b c => sgrmvT _ _ _) (fun a b => sbtmvT _ _)
            yfcwits hf yfcwits_sound).
have := hall _ _ _ hr.
by rewrite /PdC /mposC hu hxe.
Qed.

(* =========================================================================  *)
(*  The same row, with every optimization on.                                 *)
(* =========================================================================  *)

(* THE CUTS AND THE STOP CHANGE NOTHING THAT IS PROVED.  What they decide is  *)
(* which branches the search takes and when it gives up, and a branch not     *)
(* taken writes nothing.  So forb, fpop and ishm are variables here for the   *)
(* same reason the phase one table is: no proof reads them, and the run names *)
(* the real ones.                                                             *)

Variables forb fpop : arr.
Variable ishm : int.

Definition yfcmfino : rmap :=
  fmfino F frep fsym twsym dnlo dnhi fllo flhi
         (RowInst.cstep actfsri) zstepi (ytomemb tomemb) okmvv ycsolved
         RowInst.croot yrooti srch 20 forb fpop ishm.

Lemma yfcmfino_sound : soundatf fpgi fsgri fsbti (PdC 20) yfcmfino.
Proof.
refine (@fmfino_sound F frep fsym twsym dnlo dnhi fllo flhi
          arr (RowInst.cstep actfsri) zstepi (ytomemb tomemb) yposp okmvv
          ycsolved RowInst.croot yrooti srch 20 ycoordP ypstok
          ycoord_root yroot_ball yroot_pok
          (ycoord_step (r_fsstepP hfm)) yxstep_pok yxstep_pos
          (yleaf_memb r_leaf_memb) yfleaf_pos forb fpop ishm).
Qed.

Definition yfcwitso : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        yfcmfino rowwits.

Lemma yfcwitso_sound : soundatf fpgi fsgri fsbti (PdC 20) yfcwitso.
Proof. exact: (fwits_sound witsokC yfcmfino_sound). Qed.

(* THE CERTIFICATE, with the optimizations on *)
Theorem real_superflip_row_foldo : mfullf yfcwitso ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof.
move=> hf h hh.
have [x [hx hxe]] :=
  row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC hh.
case E : (place e8numi e4biti x) => [[pg gr] bt].
have hr := place_range e8okC e4okC hx E.
have hu := unplace_place e8okC e4okC hx E.
have hall : forall pg' gr' bt', inrange pg' gr' bt' -> PdC 20 pg' gr' bt'.
  refine (@foldf_all fpgi fsgri fsbti (PdC 20) fkptT
            (fun a b c => sgrmvT _ _ _) (fun a b => sbtmvT _ _)
            yfcwitso hf yfcwitso_sound).
have := hall _ _ _ hr.
by rewrite /PdC /mposC hu hxe.
Qed.

End FCubReal.
