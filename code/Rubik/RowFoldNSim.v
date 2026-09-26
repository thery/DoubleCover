(* =========================================================================  *)
(*  RowFoldNSim.v -- the counting run over the four numbers, and what it      *)
(*  proves.                                                                   *)
(* =========================================================================  *)

(* RowFoldN's run, like RowFoldSrchIC's, does not see how its position is     *)
(* kept (the same simulation as RowFoldSim), so over hcoset's four numbers it *)
(* leaves the map it leaves over the twenty cubies; and over those it is      *)
(* sound (wrun_sound).  The certificate follows as RowFoldCubRealB's does.    *)

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

Require Import RowFoldSrchI RowFoldSrchIP RowFoldSrchIC RowFoldSim.
Require Import RowFoldCubRealB RowFoldN.
Require Import RowCoord RowCoordLeaf RowCoordStep RowCoordRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* ---- two kinds of position, the same run --------------------------------- *)

Section FNSim.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Variable cstep : int -> int -> int.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.
Variable croot : int.
Variable dsrch : nat.
Variables forb fpop : arr.
Variable ishm : int.

Variables pst1 pst2 : Type.
Variable xstep1 : pst1 -> int -> pst1.
Variable xstep2 : pst2 -> int -> pst2.
Variable tomemb1 : pst1 -> memb.
Variable tomemb2 : pst2 -> memb.
Variable sroot1 : pst1.
Variable sroot2 : pst2.

Variable R : int -> pst1 -> pst2 -> Prop.

Hypothesis R_root : R croot sroot1 sroot2.
Hypothesis R_step : forall c x1 x2 k, (to_nat k < RowRun.nmvn)%N ->
  R c x1 x2 -> R (cstep c k) (xstep1 x1 k) (xstep2 x2 k).
Hypothesis R_leaf : forall c x1 x2, R c x1 x2 -> csolved c ->
  tomemb1 x1 = tomemb2 x2.

Local Notation wleaf1 :=
  (wleaf e8num e4bit fpg fsgr fsbt tomemb1 csolved forb).
Local Notation wleaf2 :=
  (wleaf e8num e4bit fpg fsgr fsbt tomemb2 csolved forb).
Local Notation iws1 :=
  (iwsrchL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved forb ishm).
Local Notation iws2 :=
  (iwsrchL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved forb ishm).
Local Notation wrun1 :=
  (wrun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch forb fpop ishm).
Local Notation wrun2 :=
  (wrun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
     F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch forb fpop ishm).

Lemma wleaf_sim c x1 x2 a : R c x1 x2 -> wleaf1 c x1 a = wleaf2 c x2 a.
Proof.
move=> hR; rewrite /wleaf; case hs : (csolved c); last by [].
by rewrite (R_leaf hR hs).
Qed.

Lemma iwsrchL_sim cut togo :
  forall togoi c x1 x2 msk pv a, R c x1 x2 ->
  iws1 cut togo togoi c x1 msk pv a = iws2 cut togo togoi c x2 msk pv a.
Proof.
elim: togo => [|togo ih] togoi c x1 x2 msk pv a hR.
  exact: wleaf_sim.
case: togo ih => [|togo] ih.
  rewrite /iwsrchL.
  apply: ifold_eqi; first exact: nmvn_nwB.
  move=> k b hk.
  do 3 apply: if_else.
  by apply: wleaf_sim; apply: R_step.
rewrite /iwsrchL.
cbv zeta.
apply: ifold_eqi; first exact: nmvn_nwB.
move=> k b hk.
do 3 apply: if_else.
apply: if_then => _.
by apply: ih; apply: R_step.
Qed.

Lemma wrun_sim n d n0 m dst : wrun1 n d n0 m dst = wrun2 n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst; first by [].
have hl : forall cut d' m' nb,
  wslv e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
    cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch forb ishm
    cut d' m' nb
  = wslv e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
    cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch forb ishm
    cut d' m' nb.
  move=> cut d' m' nb; rewrite /wslv; cbv zeta.
  case: ifP => _; last by [].
  case: ifP => _; last by [].
  case: ifP => _.
    by apply: isrchskL_sim; [exact: R_step | exact: R_leaf | exact: R_root].
  by apply: iwsrchL_sim; exact: R_root.
rewrite /wrun; cbv zeta.
case: (Uint63.ltb ncutb n0); rewrite !hl; exact: ih.
Qed.

End FNSim.

(* ---- over the four numbers ----------------------------------------------- *)

Section NCoord.

Hypothesis hfm : fsmoveC.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.
Variable okmv : int -> int -> bool.
Variable dsrch : nat.
Variables forb fpop : arr.
Variable ishm : int.

Lemma wrun_coord n d n0 m dst :
  wrun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
    F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) cstepx cmemb okmv ycsolved
    RowInst.croot (cofy yrooti) dsrch forb fpop ishm n d n0 m dst
  = wrun e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
    F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) zstepi bitleaf okmv ycsolved
    RowInst.croot yrooti dsrch forb fpop ishm n d n0 m dst.
Proof.
apply: (@wrun_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _
          Rc).
- exact: Rc_root.
- by move=> c x1 x2 k hk hR; apply: (Rc_step hfm cofy_step).
by move=> c x1 x2 hR hs; apply: (Rc_leaf cmembE hR hs).
Qed.

End NCoord.

(* ---- the counting run is sound ------------------------------------------- *)

Import GroupScope.

Section FFinalD.

(* ---- the folded phase one table, which nothing here reads ---------------- *)

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

(* ---- what the search carries, and the five things it owes ---------------- *)

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable posp : pst -> {perm facelet}.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch nlev : nat.

Variable coordP : int -> pst -> Prop.
Variable pstok : pst -> bool.

Hypothesis coord_root : coordP croot sroot.
Hypothesis root_ball : posp sroot \in ball Sset 0.
Hypothesis root_pok : pstok sroot.
Hypothesis coord_step : forall c x k, (to_nat k < RowRun.nmvn)%N -> pstok x ->
  coordP c x -> coordP (cstep c k) (xstep x k).
Hypothesis xstep_pok : forall x k, (to_nat k < RowRun.nmvn)%N ->
  pstok x -> pstok (xstep x k).
Hypothesis xstep_pos : forall x k, (to_nat k < RowRun.nmvn)%N -> pstok x ->
  posp (xstep x k) = posp x * nth 1%g moves (to_nat k).
Hypothesis leaf_memb : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> membok par8i par4i (tomemb x).
Hypothesis leaf_pos : forall c x, coordP c x -> pstok x ->
  posp x \in G -> csolved c -> posC (tomemb x) = posp x.

Variables forb fpop : arr.
Variable ishm : int.

Hypothesis hnlev : (nlev <= 63)%N.

Definition fmfinoD : rmap :=
  wrun e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
       mgri mswi mloi mhii
       F frep fsym twsym dnlo dnhi fllo flhi
       cstep xstep tomemb okmv csolved croot sroot dsrch forb fpop ishm
       nlev 0 0%uint63 (mkempty tt) (mkempty tt).

Lemma fmfinoD_sound : soundatf fpgi fsgri fsbti (PdC nlev) fmfinoD.
Proof.
rewrite /fmfinoD -{1}[nlev]add0n.
refine (@wrun_sound e8numi e8invi e4biti e4ofi par8i par4i e8okC e4okC
          fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti mgri mswi mloi mhii
          F frep fsym twsym dnlo dnhi fllo flhi
          pst cstep xstep tomemb posp okmv csolved croot sroot dsrch
          posC _ _ _ coordP pstok _ _ _ _ _ _ _ _ forb fpop ishm
          nlev 0 0%uint63 (mkempty tt) (mkempty tt) _ _ _ _ _).
- exact: PorbC.
- exact: QloC.
- exact: QhiC.
- exact: coord_root.
- exact: root_ball.
- exact: root_pok.
- exact: coord_step.
- exact: xstep_pok.
- exact: xstep_pos.
- exact: leaf_memb.
- exact: leaf_pos.
- by rewrite add0n.
- exact: pchk_mkemptyf.
- exact: pchk_mkemptyf.
- exact: soundatf_mkemptyf.
exact: soundatf_mkemptyf.
Qed.

End FFinalD.

(* ---- the certificate, over the four numbers ------------------------------ *)

Section FCubRealD.

Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Hypothesis hfm : fsmoveC.

Variables forb fpop : arr.
Variable ishm : int.

Definition yfwmfinoD : rmap :=
  wrun e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
       mgri mswi mloi mhii
       F frep fsym twsym dnlo dnhi fllo flhi
       (RowInst.cstep actfsri) cstepx cmemb okmvv ycsolved
       RowInst.croot (cofy yrooti) srch forb fpop ishm
       20 0 0%uint63 (mkempty tt) (mkempty tt).

(* the run over the four numbers is the run over the twenty cubies           *)
Lemma yfwmfinoDE : yfwmfinoD =
  fmfinoD F frep fsym twsym dnlo dnhi fllo flhi
          (RowInst.cstep actfsri) zstepi bitleaf okmvv ycsolved
          RowInst.croot yrooti srch 20 forb fpop ishm.
Proof. exact: (wrun_coord hfm). Qed.

Lemma yfwmfinoD_sound : soundatf fpgi fsgri fsbti (PdC 20) yfwmfinoD.
Proof.
rewrite yfwmfinoDE.
exact: (@fmfinoD_sound F frep fsym twsym dnlo dnhi fllo flhi
          arr (RowInst.cstep actfsri) zstepi bitleaf yposp okmvv
          ycsolved RowInst.croot yrooti srch 20 ycoordP ypstok
          ycoord_root yroot_ball yroot_pok
          (ycoord_step (r_fsstepP hfm)) yxstep_pok yxstep_pos
          yleaf_membB yfleaf_posB forb fpop ishm (erefl true)).
Qed.

Definition yfwwitsoD : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        yfwmfinoD rowwits.

Lemma yfwwitsoD_sound : soundatf fpgi fsgri fsbti (PdC 20) yfwwitsoD.
Proof. exact: (fwits_sound wits24C yfwmfinoD_sound). Qed.

(* THE CERTIFICATE, the count kept as the run goes                            *)
Theorem real_superflip_row_foldoD : mfullf ffuli yfwwitsoD ->
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
            yfwwitsoD hf yfwwitsoD_sound).
have := hall _ _ _ hr.
by rewrite /PdC /mposC hu hxe.
Qed.

End FCubRealD.
