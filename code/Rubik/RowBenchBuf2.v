(* =========================================================================  *)
(*  RowBenchBuf2.v -- the position in one buffer per depth, as the OCaml.     *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowBenchLast's search (prepass as the     *)
(* OCaml, hcoset's last level) with ONE change: a child at depth d is written *)
(* into buffer d, made once per level, instead of a new array -- the OCaml's  *)
(* cps.(d') / eps.(d').  Nothing else differs.                                *)
(*                                                                            *)
(*   D1  rowmapL 13     RowBenchLast's run, a new array per child  14 731 320 *)
(*   D2  rowmapD 13     one buffer per depth                        14 731 320 *)
(*                                                                            *)
(* The first line checks the buffer step against zstepi: IT MUST PRINT true.  *)

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

Require Import RowBenchLast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrchD.

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
Local Notation p1g := (fp1g F frep fsym twsym).
Local Notation wdist := mdist.
Local Notation wmask := (mmask dnlo dnhi fllo flhi).

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
(* the step written into a buffer: the OCaml's buffer per depth               *)
Variable xstepb : pst -> int -> pst -> pst.
(* the buffers, one per depth, made once                                      *)
Variable mkbufs : unit -> PArray.array pst.
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

Definition drcutii : int := 5.

(* mmask asks its slack whether it is two or more and whether it is one, so   *)
(* an int slack picks one of three nats.  RowMask itself is left alone.       *)
Definition dsslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

(* ---- the search, the level and the run ----------------------------------- *)

Fixpoint dsrchki (bufs : PArray.array pst) (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
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
             then let: (pg, gr, bt) := plc (tomemb (xstepb x k (PArray.get bufs 0))) in fmk m' pg gr bt
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
                           else drcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then dsrchki bufs cut togo' togoi' c' (xstepb x k (PArray.get bufs togoi'))
                        (wmask w (dsslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

Fixpoint dsrchski (bufs : PArray.array pst) (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
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
             then let: (pg, gr, bt) := plc (tomemb (xstepb x k (PArray.get bufs 0))) in fmkn a pg gr bt
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
                           else drcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then dsrchski bufs cut togo' togoi' c' (xstepb x k (PArray.get bufs togoi'))
                         (wmask w (dsslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

Definition dlvlski (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (dsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (dsrchski (mkbufs tt) cut d di croot sroot msk 18 e (m', n0)).1
      else dsrchki (mkbufs tt) cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint drunski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := dlvlski true d.+1 (flev m dst) in
      drunski n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := dlvlski false d.+1 m in
      drunski n1 d.+1 (fcount forb fpop m') m' dst
  else m.

End FSrchD.

(* zstepi, written into a given buffer: the same twenty writes, no make       *)
Definition zstepd (x : arr) (k : int) (b : arr) : arr :=
  let base := k * nsmli in
  Tabi.foldi 20 0
    (setf (fun j => PArray.get tturni
                      (PArray.get offi (base + j)
                       + PArray.get x (PArray.get ymvpi (base + j)))))
    b.

(* twenty one DIFFERENT buffers: PArray.make would share one                  *)
Definition mkbufs21 (_ : unit) : PArray.array arr :=
  ifold 21 0 (fun i bs => PArray.set bs i (PArray.make nsmli 0))
        (PArray.make 21 (PArray.make nsmli 0)).

Definition rowmapD (n : nat) : rmap :=
  drunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepd mkbufs21 bitleaf okmvvd ycsolvedd
          RowInst.croot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

Eval vm_compute in
  alli 18 0 (fun k => alli 20 0 (fun j =>
     PArray.get (zstepd yrooti k (PArray.make nsmli 7)) j
     =? PArray.get (zstepi yrooti k) j)).

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapL 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapD 13).
