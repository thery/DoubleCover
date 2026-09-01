(* =========================================================================  *)
(*  RowFoldSrchI.v -- the folded search, with the depth left as an int.       *)
(* =========================================================================  *)

(* fsrchk makes a unary nat of the table's distance at every expanding node,  *)
(* and then compares, adds and subtracts in unary.  Here the depth left is    *)
(* carried as an int beside the nat and nothing is converted at all: the nat  *)
(* is only what makes the recursion structural.  Neither subtraction wraps.   *)
(* The invariant is togoi = of_nat togo, and it belongs to the proof.  Why,   *)
(* and what it is worth, is in row.md.                                        *)
(*                                                                            *)
(* A FILE OF ITS OWN so that RowFoldSrch does not move: the folded run's      *)
(* eight hours are banked against it, and they are re-run only on purpose.    *)
(* Nothing here reads the plain side, for the same reason the other way on.   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowRun Fold RowMask RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrchI.

(* ---- RowFoldSrch's own section, declared again --------------------------- *)

Variable e8num e4bit : arr.
Variable fpg fsrc fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation plc := (place e8num e4bit).
Local Notation flev := (flevel fsrc fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).
Local Notation fmkn := (fmarkn fpg fsgr fsbt).
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Variables forb fpop : arr.
Variable ishm : int.

(* ---- the two numbers, on the side they are compared on ------------------- *)

(* Written again rather than shared, as RowFoldSrch writes hcoset's numbers   *)
(* again: neither side may move when the other is edited.                     *)

Definition frcutii : int := 5.

(* mmask asks its slack whether it is two or more and whether it is one, so   *)
(* an int slack picks one of three nats.  RowMask itself is left alone.       *)
Definition fsslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

(* ---- the search, the level and the run ----------------------------------- *)

Fixpoint fsrchki (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (m : rmap) : rmap :=
  if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    ifold RowRun.nmvn 0
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
         else if ~~ okmv pv k then m'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           (* && is a function and native_compute is call by value, so        *)
           (* a conjunction pays all its tests at every node.  Nested,        *)
           (* the cut test is reached only by a node that passes two.         *)
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then fsrchki cut togo' togoi' c' (xstep x k)
                        (wmask w (fsslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

Fixpoint fsrchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    ifold RowRun.nmvn 0
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
         else if ~~ okmv pv k then a
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           (* && is a function and native_compute is call by value, so        *)
           (* a conjunction pays all its tests at every node.  Nested,        *)
           (* the cut test is reached only by a node that passes two.         *)
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then fsrchski cut togo' togoi' c' (xstep x k)
                         (wmask w (fsslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

(* The level converts its own depth once, which is where of_nat belongs.      *)
Definition flvlski (cut : bool) (d : nat) (m dst : rmap) : rmap :=
  let m' := flev m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (fsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (fsrchski cut d di croot sroot msk 18 e (m', n0)).1
      else fsrchki cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint frunski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    let m' := flvlski (Uint63.ltb ncutb n0) d.+1 m dst in
    frunski n1 d.+1 (fcount forb fpop m') m' m
  else m.

End FSrchI.
