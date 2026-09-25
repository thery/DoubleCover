(* =========================================================================  *)
(*  RowSrchNSim.v -- the plain run with its running count does not see how a  *)
(*  position is kept, and so runs over the four numbers too.                  *)
(* =========================================================================  *)

(* RowSrchSim's lemma for RowSrchN's run: the searches are the same ones, so  *)
(* only the level and the run are new.  Then RowCoordRun's transfer.          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun Fold RowMask RowSrch RowSrchP RowSrchC.
Require Import RowFoldSim RowSrchSim RowSrchN.
Require Import Diameter RowFinal RowInst RowMemb.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowLeafFast.
Require Import RowCoordGuard RowCoord RowCoordRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section SNSim.

Variable e8num e4bit : arr.
Variable prep : rmap -> rmap -> rmap.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Variable cstep : int -> int -> int.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.
Variable croot : int.
Variable dsrch : nat.
Variable ishm : int.

(* ---- the two kinds of position -------------------------------------------- *)

Variables pst1 pst2 : Type.
Variable xstep1 : pst1 -> int -> pst1.
Variable xstep2 : pst2 -> int -> pst2.
Variable tomemb1 : pst1 -> memb.
Variable tomemb2 : pst2 -> memb.
Variable sroot1 : pst1.
Variable sroot2 : pst2.

(* in step, beside the phase one coordinate *)
Variable R : int -> pst1 -> pst2 -> Prop.

Hypothesis R_root : R croot sroot1 sroot2.
Hypothesis R_step : forall c x1 x2 k, (to_nat k < RowRun.nmvn)%N ->
  R c x1 x2 -> R (cstep c k) (xstep1 x1 k) (xstep2 x2 k).
Hypothesis R_leaf : forall c x1 x2, R c x1 x2 -> csolved c ->
  tomemb1 x1 = tomemb2 x2.

Local Notation srki1 :=
  (RowSrch.srchki e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srki2 :=
  (RowSrch.srchki e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation srski1 :=
  (RowSrch.srchski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srski2 :=
  (RowSrch.srchski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation srkiL1 :=
  (srchkiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srkiL2 :=
  (srchkiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation srskiL1 :=
  (srchskiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved ishm).
Local Notation srskiL2 :=
  (srchskiL e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved ishm).
Local Notation slv1 :=
  (slvlski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch ishm).
Local Notation slv2 :=
  (slvlski e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch ishm).
Local Notation run1 :=
  (runskic e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch ishm).
Local Notation run2 :=
  (runskic e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch ishm).

Local Notation slvn1 :=
  (slvlskni e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch ishm).
Local Notation slvn2 :=
  (slvlskni e8num e4bit F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch ishm).
Local Notation runn1 :=
  (runskni e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep1 tomemb1 okmv csolved croot sroot1 dsrch ishm).
Local Notation runn2 :=
  (runskni e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep2 tomemb2 okmv csolved croot sroot2 dsrch ishm).

Lemma slvlskni_sim cut d m nb : slvn1 cut d m nb = slvn2 cut d m nb.
Proof.
rewrite /slvlskni; cbv zeta.
case: ifP => _; last by [].
case: ifP => _; last by [].
apply: srchskiL_sim; try exact: R_root; try exact: R_step; try exact: R_leaf.
Qed.

Lemma runskni_sim n d n0 m dst : runn1 n d n0 m dst = runn2 n d n0 m dst.
Proof.
elim: n d n0 m dst => [|n ih] d n0 m dst; first by [].
rewrite /runskni; cbv zeta.
case: (Uint63.ltb ncutb n0); rewrite !slvlskni_sim; exact: ih.
Qed.

End SNSim.

(* ---- the run over the four numbers is the run over the twenty cubies ------ *)

Section CoordN.

Hypothesis hfm : fsmoveC.

Variable cmemb : cpos -> Row.memb.
Hypothesis cofy_step : forall y k, (k < 18)%N -> ypstok y ->
  cstepx (cofy y) (of_nat k) = cofy (zstepi y (of_nat k)).
Hypothesis cmembE : forall y, ypstok y -> lbguard y -> cmemb (cofy y) = bitleaf y.

Variable e8num e4bit : arr.
Variable prep : rmap -> rmap -> rmap.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.
Variable okmv : int -> int -> bool.
Variable dsrch : nat.
Variable ishm : int.

Lemma runskni_coord n d n0 m dst :
  runskni e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) cstepx cmemb okmv ycsolved
    RowInst.croot (cofy yrooti) dsrch ishm n d n0 m dst
  = runskni e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) zstepi bitleaf okmv ycsolved
    RowInst.croot yrooti dsrch ishm n d n0 m dst.
Proof.
apply: (@runskni_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rc).
- exact: Rc_root.
- by move=> c x1 x2 k hk hR; apply: (Rc_step hfm cofy_step).
by move=> c x1 x2 hR hs; apply: (Rc_leaf cmembE hR hs).
Qed.

End CoordN.
