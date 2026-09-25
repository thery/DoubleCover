(* =========================================================================  *)
(*  RowCoordRun.v -- the runs over hcoset's four numbers are the proved runs. *)
(* =========================================================================  *)

(* RowFoldSim and RowSrchSim say that a run does not see how its position is  *)
(* kept.  Here the two kinds are the twenty cubies and RowCoord's four        *)
(* numbers: they move in step (cofy_step) and a leaf reads the same member    *)
(* off both (cmembE, and RowCoordGuard's leaf_guard for bitleaf's test).  So  *)
(* the folded and the plain run over the four numbers leave the maps the     *)
(* proved runs over the twenty cubies leave.                                  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst RowMemb.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Lehmer RowCub RowCubi RowCubInst RowReal RowLeafFast.
Require Import Fold RowMask RowFold RowFoldSrch RowFoldSrchI RowFoldRunC.
Require Import RowFoldSrchIC RowSrch RowSrchC.
Require Import RowFoldSim RowSrchSim RowCoordGuard RowCoord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Import GroupScope.

Section CoordRun.

(* the phase one step table, as RowReal asks                                  *)
Hypothesis hfm : fsmoveC.

(* ---- the two facts about the four numbers --------------------------------- *)

Variable cmemb : cpos -> Row.memb.

Hypothesis cofy_step : forall y k, (k < 18)%N -> ypstok y ->
  cstepx (cofy y) (of_nat k) = cofy (zstepi y (of_nat k)).
Hypothesis cmembE : forall y, ypstok y -> lbguard y -> cmemb (cofy y) = bitleaf y.

(* ---- in step --------------------------------------------------------------- *)

Definition Rc (c : int) (x : cpos) (y : arr) : Prop :=
  [/\ x = cofy y, ypstok y, ycoordP c y & yposp y \in G].

Lemma Rc_root : Rc RowInst.croot (cofy yrooti) yrooti.
Proof.
split; [exact: erefl | exact: yroot_pok | exact: ycoord_root | ].
exact: (subsetP (ball_sub_gen Sset 0)) _ yroot_ball.
Qed.

Lemma Rc_step c x y k : (to_nat k < RowRun.nmvn)%N -> Rc c x y ->
  Rc (RowInst.cstep actfsri c k) (cstepx x k) (zstepi y k).
Proof.
move=> hk [-> hy hc hG].
have hk18 : (to_nat k < 18)%N by [].
have hke := int_of_nat_k hk18.
split.
- by rewrite hke (cofy_step hk18 hy) -hke.
- exact: yxstep_pok.
- exact: (ycoord_step (r_fsstepP hfm)).
rewrite (yxstep_pos hk hy); apply: groupM; first exact: hG.
have hm : nth 1 moves (to_nat k) \in Sset.
  by rewrite /Sset in_set; apply: mem_nth.
exact: mem_gen hm.
Qed.

Lemma Rc_leaf c x y : Rc c x y -> ycsolved c -> cmemb x = bitleaf y.
Proof.
move=> [-> hy hc hG] hs.
apply: cmembE; first exact: hy.
exact: (leaf_guard hc hy hG hs).
Qed.

(* ---- the folded run ------------------------------------------------------- *)

Section Fold.

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

Lemma frunskic_coord n d n0 m dst :
  frunskic e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
    F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) cstepx cmemb okmv ycsolved
    RowInst.croot (cofy yrooti) dsrch forb fpop ishm n d n0 m dst
  = frunskic e8num e4bit fpg fsrc fsrc2 fful fsgr fslo fshi fsbt mgr msw mlo mhi
    F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) zstepi bitleaf okmv ycsolved
    RowInst.croot yrooti dsrch forb fpop ishm n d n0 m dst.
Proof.
apply: (@frunskic_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rc).
- exact: Rc_root.
- by move=> c x1 x2 k hk hR; apply: Rc_step.
by move=> c x1 x2 hR hs; apply: Rc_leaf hR hs.
Qed.

End Fold.

(* ---- the plain run -------------------------------------------------------- *)

Section Plain.

Variable e8num e4bit : arr.
Variable prep : rmap -> rmap -> rmap.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.
Variable okmv : int -> int -> bool.
Variable dsrch : nat.
Variable ishm : int.

Lemma runskic_coord n d n0 m dst :
  runskic e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) cstepx cmemb okmv ycsolved
    RowInst.croot (cofy yrooti) dsrch ishm n d n0 m dst
  = runskic e8num e4bit prep F frep fsym twsym dnlo dnhi fllo flhi
    (RowInst.cstep actfsri) zstepi bitleaf okmv ycsolved
    RowInst.croot yrooti dsrch ishm n d n0 m dst.
Proof.
apply: (@runskic_sim _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Rc).
- exact: Rc_root.
- by move=> c x1 x2 k hk hR; apply: Rc_step.
by move=> c x1 x2 hR hs; apply: Rc_leaf hR hs.
Qed.

End Plain.

End CoordRun.
