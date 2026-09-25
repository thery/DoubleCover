(* =========================================================================  *)
(*  RowShiftRun14.v -- the run to fourteen, the coordinate packed by a shift. *)
(* =========================================================================  *)

(* A BENCH, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* THE RUN PACKS ITS COORDINATE AS twist * nfsi + flip-slice, which is        *)
(* RowInst's coordof, and pays a division and a modulo to step it and a       *)
(* division to read the table, at every candidate move.  Flip-slice is under *)
(* 2^20, so twist << 20 | flip-slice holds the same two numbers and comes     *)
(* apart with a shift and a mask.  Nothing is proved about it: this is the    *)
(* search of RowFoldSrchI copied, with that read, to see what it is worth.    *)
(*                                                                            *)
(* The solved coordinate has twist nought, so it is the same number in both   *)
(* packings and the leaf test is unchanged.  The root is packed again.        *)
(*                                                                            *)
(* RowLeafRun14 runs the same fourteen levels with the run's packing, with    *)
(* the run's leaf and with the straight one.  This file does both leaves with *)
(* the shift, so the two files give the four corners.                         *)
(*                                                                            *)
(*   cd code/Rubik && ulimit -s unlimited                                     *)
(*   /usr/bin/time -v coqc -R . Rubik RowShiftRun14.v                         *)
(*                                                                            *)
(* THE TWO COUNTS MUST BE THE SAME, AND THE SAME AS RowLeafRun14's.  The      *)
(* first Eval pays for the tables arriving and is thrown away.                *)

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
Require Import RowFoldCubDef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- the shift packing --------------------------------------------------- *)

Definition fsbits : int := 20.
Definition fsmask : int := 1048575.            (* 2^20 - 1 > nfsi = 1 013 760 *)

(* RowInst.cstep, with the shift in the place of the product                  *)
Definition scstep (c k : int) : int :=
  Uint63.lor (Uint63.lsl (acttwii (Uint63.lsr c fsbits) k) fsbits)
             (actfsri (Uint63.land c fsmask) k).

(* the root, taken apart once the old way and put back the new one           *)
Definition scroot : int :=
  let tw := Uint63.div RowInst.croot nfsi in
  Uint63.lor (Uint63.lsl tw fsbits)
             (Uint63.sub RowInst.croot (Uint63.mul tw nfsi)).

(* ---- RowFoldSrchI's search, with the one read changed -------------------- *)

Section SSrch.

(* ---- RowFoldSrch's own section, declared again --------------------------- *)

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation plc := (place24 e8num e4bit).
Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).
Local Notation fmkn := (fmarkn fpg fsgr fsbt).
(* THE ONE CHANGE: the coordinate is twist << 20 | flip-slice, so the table   *)
(* read takes it apart with a shift and a mask instead of a division          *)
Definition sp1g (c : int) : int :=
  Dfoldm F frep fsym twsym (Uint63.lsr c fsbits) (Uint63.land c fsmask).
Local Notation p1g := sp1g.
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

Definition srcutii : int := 5.

(* mmask asks its slack whether it is two or more and whether it is one, so   *)
(* an int slack picks one of three nats.  RowMask itself is left alone.       *)
Definition ssslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

(* ---- the search, the level and the run ----------------------------------- *)

Fixpoint ssrchki (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
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
                           else srcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then ssrchki cut togo' togoi' c' (xstep x k)
                        (wmask w (ssslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

Fixpoint ssrchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
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
                           else srcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then ssrchski cut togo' togoi' c' (xstep x k)
                         (wmask w (ssslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

(* The level converts its own depth once, which is where of_nat belongs.      *)
Definition slvlski (cut : bool) (d : nat) (m dst : rmap) : rmap :=
  let m' := flev m dst in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (ssslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (ssrchski cut d di croot sroot msk 18 e (m', n0)).1
      else ssrchki cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint srunski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    let m' := slvlski (Uint63.ltb ncutb n0) d.+1 m dst in
    srunski n1 d.+1 (fcount forb fpop m') m' m
  else m.

End SSrch.

(* ---- the two leaves ------------------------------------------------------ *)

(* RowLeafBench's bitleaf: the ranks straight from the twenty, with a bit     *)
(* mask.  A piece's count is its value less the values already seen below    *)
(* it, one read of a popcount table; the tables make the values 0 .. n-1.    *)
(* Measured there: 1.16 us a leaf against 12.0 for the run's.                *)
Definition lbmkt (f : int -> int) : arr :=
  ifold 24 0 (fun v a => PArray.set a v (f v)) (PArray.make 24 0).
Definition lbcq : arr := Eval vm_compute in lbmkt (fun v => v / 3).
Definition lbeq : arr := Eval vm_compute in lbmkt (fun v => v / 2).
Definition lbmq : arr :=
  Eval vm_compute in lbmkt (fun v => if 16 <=? v then v / 2 - 8 else 0).
Definition lbpop : arr := Eval vm_compute in
  ifold 256 0 (fun s a => PArray.set a s
     (ifold 8 0 (fun b c => c + ((s >> b) land 1)) 0)) (PArray.make 256 0).

Definition lbrank (tbl a : arr) (off : int) (nn : nat) (ni : int) : int :=
  Uint63.lsr
    (ifold nn 0
      (fun i st =>
         let v := PArray.get tbl (PArray.get a (Uint63.add off i)) in
         let bv := Uint63.lsl 1 v in
         let seen := Uint63.land st 255 in
         let c := Uint63.sub v
                    (PArray.get lbpop (Uint63.land seen (Uint63.sub bv 1))) in
         Uint63.lor
           (Uint63.lsl (Uint63.add (Uint63.mul (Uint63.lsr st 8)
                                               (Uint63.sub ni i)) c) 8)
           (Uint63.lor seen bv))
      0) 8.

Definition bitleaf (y : arr) : memb :=
  (lbrank lbcq y 0 8 8, lbrank lbeq y 8 8 8, lbrank lbmq y 16 4 4).

(* rowmapi, with the shift, and the leaf as an argument                       *)
Definition rowmaps (lf : arr -> memb) (n : nat) : rmap :=
  srunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          scstep zstepi lf okmvvd ycsolvedd
          scroot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

Definition dlev : nat := 14.

(* the root must come apart the same both ways                                *)
Eval vm_compute in
  (Uint63.eqb (Uint63.lsr scroot fsbits) (Uint63.div RowInst.croot nfsi),
   Uint63.eqb (Uint63.land scroot fsmask) (Uint63.mod RowInst.croot nfsi)).

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmaps ytomembd dlev).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmaps bitleaf dlev).
