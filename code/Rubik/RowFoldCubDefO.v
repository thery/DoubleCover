(* =========================================================================  *)
(*  RowFoldCubDefO.v -- the folded run, optimised: its searches over the      *)
(*  tables themselves, and RowOpt's faster reads.                             *)
(* =========================================================================  *)

(* RowFoldCubDefD's run, with the counting search, the stopping search, the  *)
(* level and the run written over global constants rather than a section's   *)
(* variables, and each read RowOpt makes faster replaced by its fast form:   *)
(* ifoldM for ifold, okmvO, cstepO, p1gO, mmaskO, place24O, fmarknwO, and a  *)
(* packed fsgr in the stopping search's mark; the level is flevelg, which    *)
(* skips a word already right.  RowFoldCubProofO shows every one of them     *)
(* equal to RowFoldCubDefD's.  No proof here.                                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembi RowLeaf RowWits.
Require Import Lehmer RowCub RowCubi.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.
Require Import RowFoldCubDef RowFoldSrchI.
Require Import RowLeafFast RowFoldSrchIC.
Require Import RowCoord RowCoordLeaf RowFoldN RowFoldCubDefD RowOpt.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- the stopping search's mark, reading the packed fsgr ------------------ *)

(* RowFold.fmarkn at the folded tables                                        *)
Definition fmarknO (mn : rmap * int) (pg gr bt : int) : rmap * int :=
  let: (m, n) := mn in
  let w := PArray.get fpgi pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12) then 0 else 1) in
  let r := fkpt w in
  let g := sgrmvO u pty gr in
  let v := bitof (fbit (fhlf w) (sbtmv fsbti u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w := Uint63.lor old v in
  if Uint63.eqb w old then mn
  else (PArray.set m c (PArray.set a i w), Uint63.add n 1).

(* ---- the stopping search ---------------------------------------------------- *)

(* RowFoldSrchI.fsrchski                                                      *)
Fixpoint fsrchskiO (cut : bool) (togo : nat) (togoi : int) (c : int)
                   (x : cpos) (msk pv : int) (enough : int) (mn : rmap * int)
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
                        then ~~ Uint63.eqb (Uint63.land ishmi
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
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then fsrchskiO cut togo' togoi' c' (cstepx x k)
                          (mmaskO w (fsslack (Uint63.sub togoi' nd))) k
                          enough a
           else a)
      mn
  else if ycsolvedd c
       then let: (pg, gr, bt) := place24O (cmemb x) in fmarknO mn pg gr bt
       else mn.

(* RowFoldSrchIC.isrchskL                                                     *)
Fixpoint isrchskLO (cut : bool) (togo : nat) (togoi : int) (c : int)
                   (x : cpos) (msk pv : int) (enough : int) (mn : rmap * int)
                   : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      ifoldM RowRun.nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmvO pv k then a
           else if cut && ~~ Uint63.eqb (Uint63.land ishmi (Uint63.lsl 1 k)) 0
           then a
           else fsrchskiO cut 0 0 (cstepO c k) (cstepx x k) 0 k enough a)
        mn
    else
    let togoi' := Uint63.sub togoi 1 in
    ifoldM RowRun.nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmvO pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishmi
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
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then isrchskLO cut togo' togoi' c' (cstepx x k)
                          (mmaskO w (fsslack (Uint63.sub togoi' nd))) k
                          enough a
           else a)
      mn
  else fsrchskiO cut 0 togoi c x msk pv enough mn.

(* ---- the counting search --------------------------------------------------- *)

(* RowFoldN.wleaf                                                             *)
Definition wleafO (c : int) (x : cpos) (a : rmap * int) : rmap * int :=
  if ycsolvedd c then let: (pg, gr, bt) := place24O (cmemb x) in
                      fmarknwO a pg gr bt
  else a.

(* RowFoldN.iwsrchL                                                           *)
Fixpoint iwsrchLO (cut : bool) (togo : nat) (togoi : int) (c : int) (x : cpos)
                  (msk pv : int) (a : rmap * int) : rmap * int :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifoldM RowRun.nmvn 0
        (fun k a' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
           else if ~~ okmvO pv k then a'
           else if cut && ~~ Uint63.eqb (Uint63.land ishmi (Uint63.lsl 1 k)) 0
           then a'
           else wleafO (cstepO c k) (cstepx x k) a')
        a
    else
    let togoi' := Uint63.sub togoi 1 in
    ifoldM RowRun.nmvn 0
      (fun k a' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
         else if ~~ okmvO pv k then a'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishmi
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a'
         else
           let c' := cstepO c k in
           let w := p1gO c' in
           let nd := mdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then iwsrchLO cut togo' togoi' c' (cstepx x k)
                         (mmaskO w (fsslack (Uint63.sub togoi' nd))) k a'
           else a')
      a
  else wleafO c x a.

(* ---- the level and the run -------------------------------------------------- *)

(* RowFoldN.wslv                                                              *)
Definition wslvO (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if (d <= srchd)%N then
    let w := p1gO RowInst.croot in
    let di := of_nat d in
    if (mdist w <=? di) then
      let msk := mmaskO w (fsslack (Uint63.sub di (mdist w))) in
      if (d == srchd)%N then
        let e := Uint63.add enoughb (Uint63.div nb enoughd) in
        isrchskLO cut d di RowInst.croot crootD msk 18 e (m', nb)
      else iwsrchLO cut d di RowInst.croot crootD msk 18 (m', nb)
    else (m', nb)
  else (m', nb).

(* RowFoldN.wrun, the level skipping a word already right                     *)
Fixpoint wrunO (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := flevelg fsrci fsrc2i ffuli fsgri fsloi fshii mgri mswi mloi mhii
                        m dst in
      let a := wslvO true d.+1 m1 (fcount forbi fpopi m1) in
      wrunO n1 d.+1 a.2 a.1 m
    else
      let a := wslvO false d.+1 m n0 in
      wrunO n1 d.+1 a.2 a.1 dst
  else m.

(* ---- the map, the witnesses and the boolean ------------------------------- *)

Definition rowmapiO (n : nat) : rmap :=
  wrunO n 0 0%uint63 (RowFold.mkempty tt) (RowFold.mkempty tt).

Definition ycwitsoiO : rmap :=
  foldr (fun t m =>
           let: (pg, gr, bt, _) := t in fmark fpgi fsgri fsbti m pg gr bt)
        (rowmapiO 20) rowwits.

Definition rowfulliO : bool := mfullf ffuli ycwitsoiO.
