(* =========================================================================  *)
(*  RowCubDefO.v -- the plain run, its search written over the tables        *)
(*  themselves, with RowOpt's reads.                                          *)
(* =========================================================================  *)

(* RowCubDefD's run, with three things changed and nothing else:              *)
(*   - the search names its tables and its steps as constants, where         *)
(*     RowSrch's takes them as section variables and hands every one of them *)
(*     along at every test;                                                  *)
(*   - the step, the table read, the mask, the moves and the place are        *)
(*     RowOpt's, with no division;                                            *)
(*   - the moves are walked with ifoldM, so no type is passed.               *)
(* RowCubProofO shows the run equal to RowCubDefD's.  No proof here.          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf.
Require Import RowWits RowWitsChk.
Require Import Lehmer RowCub RowCubi RowCubInst.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import P1Table RowReal.
Require Import Fold FoldTables P1Fdec P1FTable RowMask RowSrch RowMark.
Require Import RowLvl.
Require Import RowLeafFast RowSrchC.
Require Import RowCubDef.
Require Import RowCoord RowCoordLeaf RowSrchN RowOpt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- RowSrch.srchski, over the constants ----------------------------------- *)

Fixpoint srchskiO (cut : bool) (togo : nat) (togoi : int) (c : int) (x : cpos)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    ifoldM RowRun.nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmvO pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land RowCubDef.ishmi
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a
         else
           let c' := cstepO c k in
           let w := p1gO c' in
           let nd := mdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else rcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then srchskiO cut togo' togoi' c' (cstepx x k)
                        (mmaskO w (sslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if ycsolved c
       then let: (pg, gr, bt) := placeO (cmemb x) in mmarkn mn pg gr bt
       else mn.

(* ---- RowSrchC.srchskiL, over the constants --------------------------------- *)

Fixpoint srchskiLO (cut : bool) (togo : nat) (togoi : int) (c : int)
                   (x : cpos) (msk pv : int) (enough : int) (mn : rmap * int)
                   : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      ifoldM RowRun.nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmvO pv k then a
           else if (if cut then ~~ Uint63.eqb (Uint63.land RowCubDef.ishmi
                                                 (Uint63.lsl 1 k)) 0
                    else false)
           then a
           else srchskiO cut 0 0 (cstepO c k) (cstepx x k) 0 k enough a)
        mn
    else
    let togoi' := Uint63.sub togoi 1 in
    ifoldM RowRun.nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmvO pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land RowCubDef.ishmi
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a
         else
           let c' := cstepO c k in
           let w := p1gO c' in
           let nd := mdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else rcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then srchskiLO cut togo' togoi' c' (cstepx x k)
                         (mmaskO w (sslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else srchskiO cut 0 togoi c x msk pv enough mn.

(* ---- RowSrchN's level and run, over the constants -------------------------- *)

(* RowSrchN.slvlskni                                                          *)
Definition slvlskniO (cut : bool) (d : nat) (m' : rmap) (nb : int)
  : rmap * int :=
  if (d <= srch)%N then
    let w := p1gO RowInst.croot in
    let di := of_nat d in
    if (mdist w <=? di) then
      let msk := mmaskO w (sslack (Uint63.sub di (mdist w))) in
      let e := if (d == srch)%N
               then Uint63.add enoughb (Uint63.div nb enoughd) else nbig in
      srchskiLO cut d di RowInst.croot (cofy yrooti) msk 18 e (m', nb)
    else (m', nb)
  else (m', nb).

(* RowSrchN.runskni, the prepass RowLvl's                                     *)
Fixpoint runskniO (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := prepassD cpgi cfli mgri mswi mloi mhii m dst in
      let mn := slvlskniO true d.+1 m1 (mcount m1) in
      runskniO n1 d.+1 mn.2 mn.1 m
    else
      let mn := slvlskniO false d.+1 m n0 in
      runskniO n1 d.+1 mn.2 mn.1 dst
  else m.

(* ---- the map, the witnesses, the boolean ----------------------------------- *)

Definition rowmappiO (n : nat) : rmap :=
  runskniO n 0 0%uint63 (RowMap.mkempty tt) (RowMap.mkempty tt).

Definition rowwitspiO : rmap := wmarkof rowwits48 (rowmappiO 20).

Definition rowfullpiO : bool := mfull rowwitspiO.
