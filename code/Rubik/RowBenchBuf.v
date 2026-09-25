(* =========================================================================  *)
(*  RowBenchBuf.v -- the position written into a reused buffer, timed.        *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowBenchLast's search (the prepass only    *)
(* when the cuts are on, hcoset's last level) with one change: a child that   *)
(* passes the table test is written into the array of the previous child,    *)
(* whose subtree is done, instead of a new one -- as the OCaml writes into    *)
(* one buffer per depth.  One array is made per node instead of per child.    *)
(*                                                                            *)
(*   B1  rowmapL 13     RowBenchLast's L2, again                  14 731 320  *)
(*   B2  rowmapLB 13    the same with the buffer                  14 731 320  *)
(*                                                                            *)
(* RUN IT UNDER /usr/bin/time -v: the peak memory must not grow -- a version  *)
(* of the buffer kept by mistake would show there.  The first line checks     *)
(* the buffer step against zstepi and must print true.                        *)

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

Section FSrchB.

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
(* the step written into a buffer that may be overwritten                     *)
Variable xstepb : pst -> int -> pst -> pst.
(* a fresh buffer, made once per node rather than once per child              *)
Variable mkbuf : unit -> pst.
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

Definition brcutii : int := 5.

Definition bsslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

(* THE LOOP CARRIES THE MAP AND A BUFFER.  A child that passes is written     *)
(* into the buffer; once its subtree has returned nothing points at it, and   *)
(* the next child is written into it again.  Only the latest version is ever  *)
(* read, so the old ones are garbage at once.                                 *)
Fixpoint bsrchki (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                 (msk pv : int) (m : rmap) : rmap :=
  if togo is togo'.+1 then
    if togo' is 0 then
      (ifold RowRun.nmvn 0
        (fun k mb =>
           let: (m', b) := mb in
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then mb
           else if ~~ okmv pv k then mb
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then mb
           else
             let c' := cstep c k in
             if csolved c'
             then let x' := xstepb x k b in
                  let: (pg, gr, bt) := plc (tomemb x') in (fmk m' pg gr bt, x')
             else mb)
        (m, mkbuf tt)).1
    else
    let togoi' := Uint63.sub togoi 1 in
    (ifold RowRun.nmvn 0
      (fun k mb =>
         let: (m', b) := mb in
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then mb
         else if ~~ okmv pv k then mb
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then mb
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else brcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then let x' := xstepb x k b in
                (bsrchki cut togo' togoi' c' x'
                         (wmask w (bsslack (Uint63.sub togoi' nd))) k m', x')
           else mb)
      (m, mkbuf tt)).1
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

Fixpoint bsrchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (enough : int) (mn : rmap * int)
                  : rmap * int :=
  if Uint63.leb enough mn.2 then mn
  else if togo is togo'.+1 then
    if togo' is 0 then
      (ifold RowRun.nmvn 0
        (fun k ab =>
           let: (a, b) := ab in
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then ab
           else if ~~ okmv pv k then ab
           else if (if cut then ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
                    else false)
           then ab
           else
             let c' := cstep c k in
             if csolved c'
             then let x' := xstepb x k b in
                  let: (pg, gr, bt) := plc (tomemb x') in (fmkn a pg gr bt, x')
             else ab)
        (mn, mkbuf tt)).1
    else
    let togoi' := Uint63.sub togoi 1 in
    (ifold RowRun.nmvn 0
      (fun k ab =>
         let: (a, b) := ab in
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then ab
         else if ~~ okmv pv k then ab
         else if (if cut
                  then (if (togo' == 0)%N
                        then ~~ Uint63.eqb (Uint63.land ishm
                                              (Uint63.lsl 1 k)) 0
                        else false)
                  else false)
         then ab
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := wdist w in
           if (if nd <=? togoi'
               then (if cut
                     then (if nd =? togoi' then true
                           else brcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then let x' := xstepb x k b in
                (bsrchski cut togo' togoi' c' x'
                          (wmask w (bsslack (Uint63.sub togoi' nd))) k enough a, x')
           else ab)
      (mn, mkbuf tt)).1
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

Definition blvlski (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (bsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (bsrchski cut d di croot sroot msk 18 e (m', n0)).1
      else bsrchki cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint brunski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := blvlski true d.+1 (flev m dst) in
      brunski n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := blvlski false d.+1 m in
      brunski n1 d.+1 (fcount forb fpop m') m' dst
  else m.

End FSrchB.

(* zstepi, written into a given buffer instead of a new array: the same       *)
(* twenty writes, and no make                                                 *)
Definition zstepb (x : arr) (k : int) (b : arr) : arr :=
  let base := k * nsmli in
  foldi 20 0
    (setf (fun j => PArray.get tturni
                      (PArray.get offi (base + j)
                       + PArray.get x (PArray.get ymvpi (base + j)))))
    b.

Definition mkbuf20 (_ : unit) : arr := PArray.make nsmli 0.

Definition rowmapLB (n : nat) : rmap :=
  brunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii
          p1ftab frepi fsymi twsymi
          dnlo_data dnhi_data fllo_data flhi_data
          (RowInst.cstep actfsri) zstepb mkbuf20 bitleaf okmvvd ycsolvedd
          RowInst.croot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

(* the buffer version gives the same twenty as zstepi, on the root and every  *)
(* move of it, into a buffer full of rubbish: IT MUST PRINT true              *)
Eval vm_compute in
  alli 18 0 (fun k => alli 20 0 (fun j =>
     PArray.get (zstepb yrooti k (PArray.make nsmli 7)) j
     =? PArray.get (zstepi yrooti k) j)).

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapL 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapLB 13).
