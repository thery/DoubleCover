(* =========================================================================  *)
(*  RowBenchCoord.v -- the position as twenty cubies, and as hcoset's four    *)
(*  small numbers.                                                            *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowBenchTab's search with its R1 tables,  *)
(* the position, its move and its leaf taken as parameters:                   *)
(*                                                                            *)
(*   C1  as now: twenty cubies moved by zstepi, the place from bitleaf        *)
(*   C2  four numbers moved by tables, the place read from tables, no rank    *)
(*       (RowCoord.v, hcoset's permcube)                                      *)
(*   C3  C2 with its five tables packed, four entries of 15 bits a word, or   *)
(*       three of 16 for the corners: the OCaml's 16-bit tables               *)
(*   C4  C3 with the marks queued, 64 at a time, as hcoset writes its bits    *)
(*       (below the last search depth only; the bench stops at 13)            *)
(*                                                                            *)
(* The renaming of the folded map is fmark's in both: the leaf gives the      *)
(* plain place, page group and bit, and fmark folds it.  Each is the whole    *)
(* run to thirteen; the counts must be 14 731 320 both.                       *)

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

Require Import RowFoldCubDefB RowLeafFast.

Require Import RowBenchLast RowCoord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrchC.

(* ---- RowFoldSrch's own section, declared again --------------------------- *)

(* the leaf gives the place, so e8num and e4bit are not asked here           *)
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
(* THE TWO READS ARE PARAMETERS, so the same search runs over each layout    *)
Variable p1gv : int -> int.
Variable wmaskv : int -> nat -> int.

Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).
Local Notation fmkn := (fmarkn fpg fsgr fsbt).
Local Notation p1g := p1gv.
Local Notation wdist := mdist.
Local Notation wmask := wmaskv.

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
(* THE LEAF IS A PARAMETER: the place of the member, page, group and bit      *)
Variable leaf : pst -> int * int * int.
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

Definition crcutii : int := 5.

(* mmask asks its slack whether it is two or more and whether it is one, so   *)
(* an int slack picks one of three nats.  RowMask itself is left alone.       *)
Definition csslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

(* ---- the search, the level and the run ----------------------------------- *)

Fixpoint csrchki (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (m : rmap) : rmap :=
  if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    if togo' is 0 then
      (* hcoset's last level: no table read, no mask, the leaf test alone *)
      ifold RowRun.nmvn 0
        (fun k m' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then m'
           else if ~~ okmv pv k then m'
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then m'
           else
             let c' := cstep c k in
             if csolved c'
             then let: (pg, gr, bt) := leaf (xstep x k) in fmk m' pg gr bt
             else m')
        m
    else
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
                           else crcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then csrchki cut togo' togoi' c' (xstep x k)
                        (wmask w (csslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := leaf x in fmk m pg gr bt
       else m.

Fixpoint csrchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    if togo' is 0 then
      (* hcoset's last level: no table read, no mask, the leaf test alone *)
      ifold RowRun.nmvn 0
        (fun k a =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a
           else if ~~ okmv pv k then a
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then a
           else
             let c' := cstep c k in
             if csolved c'
             then let: (pg, gr, bt) := leaf (xstep x k) in fmkn a pg gr bt
             else a)
        mn
    else
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
                           else crcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then csrchski cut togo' togoi' c' (xstep x k)
                         (wmask w (csslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := leaf x in fmkn mn pg gr bt
       else mn.

Definition clvlski (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (csslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (csrchski cut d di croot sroot msk 18 e (m', n0)).1
      else csrchki cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint crunski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := clvlski true d.+1 (flev m dst) in
      crunski n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := clvlski false d.+1 m in
      crunski n1 d.+1 (fcount forb fpop m') m' dst
  else m.

End FSrchC.

(* ---- C4: the same search, the marks queued ------------------------------- *)

(* The accumulator is the map, the queue and its length.  A mark is packed   *)
(* in the queue as page, group and bit; a full queue is written in one go,   *)
(* and so is what is left at the end of a level.  The queue is one fresh    *)
(* array per level, set in place and never read at an old version.          *)

Section FSrchQ.

Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable p1gv : int -> int.
Variable wmaskv : int -> nat -> int.

Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).
Local Notation p1g := p1gv.
Local Notation wdist := mdist.
Local Notation wmask := wmaskv.

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable leaf : pst -> int * int * int.
Variable okmv : int -> int -> bool.
Variable csolved : int -> bool.

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Variables forb fpop : arr.
Variable ishm : int.

Definition qsize : int := 64.

Definition acc := (rmap * arr * int)%type.

(* the queue written into the map *)
Definition qflush (a : acc) : rmap :=
  let: (m, q, n) := a in
  ifold 64 0
    (fun i m' =>
       if i <? n then
         let v := PArray.get q i in
         fmk m' (Uint63.lsr v 20) (Uint63.land (Uint63.lsr v 5) 32767)
             (Uint63.land v 31)
       else m')
    m.

(* one mark queued, the queue written first when it is full *)
Definition qmark (a : acc) (pg gr bt : int) : acc :=
  let: (m, q, n) := a in
  let v := Uint63.lor (Uint63.lsl pg 20) (Uint63.lor (Uint63.lsl gr 5) bt) in
  if Uint63.eqb n qsize
  then (qflush a, PArray.set q 0 v, 1)
  else (m, PArray.set q n v, Uint63.add n 1).

Fixpoint csrchq (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                (msk pv : int) (a : acc) : acc :=
  if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1 in
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k a' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
           else if ~~ okmv pv k then a'
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then a'
           else
             let c' := cstep c k in
             if csolved c'
             then let: (pg, gr, bt) := leaf (xstep x k) in qmark a' pg gr bt
             else a')
        a
    else
    ifold RowRun.nmvn 0
      (fun k a' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
         else if ~~ okmv pv k then a'
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then a'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else crcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then csrchq cut togo' togoi' c' (xstep x k)
                       (wmask w (csslack (Uint63.sub togoi' nd))) k a'
           else a')
      a
  else if csolved c
       then let: (pg, gr, bt) := leaf x in qmark a pg gr bt
       else a.

(* no early stop: the bench stops below the depth it is used at *)
Definition clvlsq (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (csslack (Uint63.sub di (wdist w))) in
      qflush (csrchq cut d di croot sroot msk 18 (m', PArray.make qsize 0, 0))
    else m'
  else m'.

Fixpoint crunsq (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := clvlsq true d.+1 (flev m dst) in
      crunsq n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := clvlsq false d.+1 m in
      crunsq n1 d.+1 (fcount forb fpop m') m' dst
  else m.

End FSrchQ.

(* ---- the run, over any position ------------------------------------------ *)

(* RowBenchTab's R1 -- the tables as now -- with the position, its move and   *)
(* its leaf given                                                             *)
Definition rowmapK (pst : Type) (xs : pst -> int -> pst)
                   (lf : pst -> int * int * int) (root : pst) (n : nat) : rmap :=
  crunski fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii (fp1g p1ftab frepi fsymi twsymi)
          (mmask dnlo_data dnhi_data fllo_data flhi_data)
          (RowInst.cstep actfsri) xs lf okmvvd ycsolvedd
          RowInst.croot root srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

(* C1: the twenty cubies and bitleaf, as now                                   *)
Definition leaf1 (y : arr) : int * int * int := place24 e8numi e4biti (bitleaf y).

(* C2: the four numbers                                                        *)
Definition e8tabB : arr := mke8tab e8numi.
Definition e4tabB : arr := mke4tab e4biti.
Definition leaf2 (x : cpos) : int * int * int := cleaf e8tabB e4tabB x.
Definition croot2 : cpos := cofy yrooti.

(* C3: the five tables packed                                                  *)

(* four entries of fifteen bits a word: nw words for sz entries             *)
Definition pk4 (nw : nat) (sz : int) (t : arr) : arr :=
  mkT nw
    (fun w =>
       let g j := let i := Uint63.add (Uint63.mul w 4) j in
                  if i <? sz then PArray.get t i else 0 in
       Uint63.lor (Uint63.lor (g 0) (Uint63.lsl (g 1) 15))
                  (Uint63.lor (Uint63.lsl (g 2) 30) (Uint63.lsl (g 3) 45))).
Definition gt4 (t : arr) (i : int) : int :=
  Uint63.land (Uint63.lsr (PArray.get t (Uint63.lsr i 2))
                          (Uint63.mul (Uint63.land i 3) 15)) 32767.

(* the corners need sixteen bits: three a word, six words a rank, the move's *)
(* word and shift read from two small tables                                 *)
Definition kqT : arr := mkT 18 (fun k => Uint63.div k 3).
Definition ksT : arr := mkT 18 (fun k => Uint63.mul (Uint63.mod k 3) 16).
Definition ctabP : arr :=
  mkT (40320 * 6)
    (fun w =>
       let r := Uint63.div w 6 in
       let j := Uint63.sub w (Uint63.mul r 6) in
       let g f := PArray.get ctab (Uint63.add (Uint63.mul r 18)
                                              (Uint63.add (Uint63.mul j 3) f)) in
       Uint63.lor (g 0) (Uint63.lor (Uint63.lsl (g 1) 16) (Uint63.lsl (g 2) 32))).
(* the edges: twenty slots a tuple, eighteen used, five words                *)
Definition etabP : arr :=
  mkT (ntup * 5)
    (fun w =>
       let t := Uint63.div w 5 in
       let j := Uint63.sub w (Uint63.mul t 5) in
       let g f := let k := Uint63.add (Uint63.mul j 4) f in
                  if k <? 18 then PArray.get etab (Uint63.add (Uint63.mul t 18) k)
                  else 0 in
       Uint63.lor (Uint63.lor (g 0) (Uint63.lsl (g 1) 15))
                  (Uint63.lor (Uint63.lsl (g 2) 30) (Uint63.lsl (g 3) 45))).
Definition e8tabP : arr := pk4 705600 2822400 e8tabB.
Definition e4tabP : arr := pk4 5184 20736 e4tabB.
Definition sub8P : arr := pk4 5184 20736 sub8.

Definition cstepP (x : cpos) (k : int) : cpos :=
  let: (c, u, d, m) := x in
  let ek t := Uint63.land
                (Uint63.lsr (PArray.get etabP (Uint63.add (Uint63.mul t 5)
                                                          (Uint63.lsr k 2)))
                            (Uint63.mul (Uint63.land k 3) 15)) 32767 in
  (Uint63.land
     (Uint63.lsr (PArray.get ctabP (Uint63.add (Uint63.mul c 6) (PArray.get kqT k)))
                 (PArray.get ksT k)) 65535,
   ek u, ek d, ek m).
Definition leafP (x : cpos) : int * int * int :=
  let: (c, u, d, m) := x in
  (c, gt4 e8tabP (Uint63.add (Uint63.mul (gt4 sub8P u) n8t) (gt4 sub8P d)),
   gt4 e4tabP m).

(* C4: C3, the marks queued                                                  *)
Definition rowmapQ (pst : Type) (xs : pst -> int -> pst)
                   (lf : pst -> int * int * int) (root : pst) (n : nat) : rmap :=
  crunsq fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
         mgri mswi mloi mhii (fp1g p1ftab frepi fsymi twsymi)
         (mmask dnlo_data dnhi_data fllo_data flhi_data)
         (RowInst.cstep actfsri) xs lf okmvvd ycsolvedd
         RowInst.croot root srchd forbi fpopi ishmi
         n 0 0%uint63 (mkempty tt) (mkempty tt).

(* ---- the runs ------------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

(* building the tables of C2, timed apart from the runs                       *)
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctab 5) (PArray.get etab 5))
    (Uint63.add (Uint63.add (PArray.get e8tabB 5) (PArray.get e4tabB 5))
       (Uint63.add (PArray.get sub8 5) (croot2.1.1.1))).

(* and of C3                                                                   *)
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get ctabP 5) (PArray.get etabP 5))
    (Uint63.add (PArray.get e8tabP 5)
       (Uint63.add (PArray.get e4tabP 5) (PArray.get sub8P 5))).

(* the two runs agree at a small depth, where they cost nothing                *)
Time Eval native_compute in
  (fcount48 ffuli forbi fpopi (rowmapK zstepi leaf1 yrooti 6),
   fcount48 ffuli forbi fpopi (rowmapK cstepx leaf2 croot2 6),
   fcount48 ffuli forbi fpopi (rowmapK cstepP leafP croot2 6),
   fcount48 ffuli forbi fpopi (rowmapQ cstepP leafP croot2 6)).

(* C1: twenty cubies, as now                                                   *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapK zstepi leaf1 yrooti 13).
(* C2: four numbers                                                            *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapK cstepx leaf2 croot2 13).
(* C3: four numbers, tables packed                                             *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapK cstepP leafP croot2 13).
(* C4: C3, the marks queued                                                    *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapQ cstepP leafP croot2 13).
