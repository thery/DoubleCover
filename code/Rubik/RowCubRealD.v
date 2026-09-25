(* =========================================================================  *)
(*  RowCubRealD.v -- the plain run with its running count, proved sound.      *)
(* =========================================================================  *)

(* RowCubRealB's certificate over RowSrchN's run: the count is kept as the   *)
(* run goes instead of walking the map after every level.  The soundness is   *)
(* runskn_sound, which does not look at the count.                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowPrep RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import RowReal RowMembi RowMark RowSrch.
Require Import RowSrchP RowSrchC RowCubReal RowFoldCubReal RowFoldCubRealB RowLeafFast.
Require Import RowSrchN RowCubRealB.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

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
