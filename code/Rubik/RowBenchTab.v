(* =========================================================================  *)
(*  RowBenchTab.v -- the table reads: packed with divisions, one value a      *)
(*  slot, and packed a power of two a word.                                   *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  RowBenchLast's search (prepass as the     *)
(* OCaml, hcoset's last level), with the table read and the mask decoding     *)
(* taken as parameters, and three ways of reading the same tables:            *)
(*                                                                            *)
(*   R1  as now: 3 or 15 values a word, a division at every read              *)
(*   R2  one value a slot: no division (the distance table's /2 a shift)      *)
(*   R3  packed a power of two a word -- twenty bits two a word, four bits    *)
(*       eight a word -- so a read is a shift and a mask                      *)
(*                                                                            *)
(* Each is the whole run to thirteen; the counts must be 14 731 320 all       *)
(* three.  The tables of R2 and R3 are built first, in two Evals timed apart. *)
(* The coordinate is still twist * nfsi + flip-slice in all three.            *)

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

Section FSrchT.

(* ---- RowFoldSrch's own section, declared again --------------------------- *)

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
(* THE TWO READS ARE PARAMETERS, so the same search runs over each layout    *)
Variable p1gv : int -> int.
Variable wmaskv : int -> nat -> int.

Local Notation plc := (place24 e8num e4bit).
Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).
Local Notation fmkn := (fmarkn fpg fsgr fsbt).
Local Notation p1g := p1gv.
Local Notation wdist := mdist.
Local Notation wmask := wmaskv.

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

Definition trcutii : int := 5.

(* mmask asks its slack whether it is two or more and whether it is one, so   *)
(* an int slack picks one of three nats.  RowMask itself is left alone.       *)
Definition tsslack (s : int) : nat :=
  if (2 <=? s) then 2%N else if (s =? 1) then 1%N else 0%N.

(* ---- the search, the level and the run ----------------------------------- *)

Fixpoint tsrchki (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
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
             then let: (pg, gr, bt) := plc (tomemb (xstep x k)) in fmk m' pg gr bt
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
                           else trcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then tsrchki cut togo' togoi' c' (xstep x k)
                        (wmask w (tsslack (Uint63.sub togoi' nd))) k m'
           else m')
      m
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

Fixpoint tsrchski (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
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
             then let: (pg, gr, bt) := plc (tomemb (xstep x k)) in fmkn a pg gr bt
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
                           else trcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then tsrchski cut togo' togoi' c' (xstep x k)
                         (wmask w (tsslack (Uint63.sub togoi' nd))) k enough a
           else a)
      mn
  else if csolved c
       then let: (pg, gr, bt) := plc (tomemb x) in fmkn mn pg gr bt
       else mn.

Definition tlvlski (cut : bool) (d : nat) (m' : rmap) : rmap :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (tsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let n0 := fcount forb fpop m' in
        let e := Uint63.add enoughb (Uint63.div n0 enoughd) in
        (tsrchski cut d di croot sroot msk 18 e (m', n0)).1
      else tsrchki cut d di croot sroot msk 18 m'
    else m'
  else m'.

Fixpoint trunski (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m' := tlvlski true d.+1 (flev m dst) in
      trunski n1 d.+1 (fcount forb fpop m') m' m
    else
      let m' := tlvlski false d.+1 m in
      trunski n1 d.+1 (fcount forb fpop m') m' dst
  else m.

End FSrchT.

Definition rowmapT (p1 : int -> int) (wm : int -> nat -> int)
                   (cs : int -> int -> int) (n : nat) : rmap :=
  trunski e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
          mgri mswi mloi mhii p1 wm
          cs zstepi bitleaf okmvvd ycsolvedd
          RowInst.croot yrooti srchd forbi fpopi ishmi
          n 0 0%uint63 (mkempty tt) (mkempty tt).

(* ---- building a table ----------------------------------------------------- *)

Definition mk1 (sz : nat) (f : int -> int) : arr :=
  ifold sz 0 (fun i a => PArray.set a i (f i)) (PArray.make (of_nat sz) 0).

(* past the four million entries an array may hold: chunks of 2 ^ 21          *)
Definition csz : nat := 2097152.
Definition mkC (nch : nat) (f : int -> int) : PArray.array arr :=
  ifold nch 0
    (fun c t => PArray.set t c
                  (ifold csz 0
                     (fun o a => PArray.set a o
                                   (f (Uint63.add (Uint63.lsl c 21) o)))
                     (PArray.make (of_nat csz) 0)))
    (PArray.make (of_nat nch) (PArray.make 1 0)).
Definition getC (t : PArray.array arr) (i : int) : int :=
  PArray.get (PArray.get t (Uint63.lsr i 21)) (Uint63.land i 2097151).

(* the flip-slice move table read the run's way, entry i = 18 r + k           *)
Definition fsmv (i : int) : int :=
  actfsri (Uint63.div i 18) (Uint63.sub i (Uint63.mul (Uint63.div i 18) 18)).

(* the distance table, whose two a word is a shift and a mask, not a division *)
Definition p1getmS (i : int) : int :=
  let w := Uint63.lsr i 1 in
  let r := Uint63.land i 1 in
  let c := Uint63.lsr w cwlogi in
  let o := Uint63.land w cwmaski in
  Uint63.land
    (Uint63.lsr (PArray.get (PArray.get p1ftab c) o) (Uint63.mul r mbits))
    mmaski.

(* ---- R2: one value a slot -------------------------------------------------- *)

Definition frepU : arr := mk1 1013760 frepi.
Definition fsymU : arr := mk1 1013760 fsymi.
Definition twsymU : arr := mk1 34992 (get20 twsyma).
Definition dnloU : arr := mk1 65536 (get20 dnlo_data).
Definition dnhiU : arr := mk1 65536 (get20 dnhi_data).
Definition flloU : arr := mk1 65536 (get20 fllo_data).
Definition flhiU : arr := mk1 65536 (get20 flhi_data).
Definition fsmU : PArray.array arr := mkC 9 fsmv.

Definition cstepU (c k : int) : int :=
  let tw := Uint63.div c nfsi in
  let r := Uint63.sub c (Uint63.mul tw nfsi) in
  Uint63.add (Uint63.mul (acttwii tw k) nfsi)
             (getC fsmU (Uint63.add (Uint63.mul r 18) k)).

Definition p1gU (c : int) : int :=
  let tw := Uint63.div c nfsi in
  let r := Uint63.sub c (Uint63.mul tw nfsi) in
  let y := PArray.get fsymU r in
  Uint63.lor
    (p1getmS (Uint63.add (Uint63.mul (PArray.get frepU r) ntwisti)
                         (PArray.get twsymU (Uint63.add (Uint63.mul tw 16) y))))
    (Uint63.lsl y mbits).

Definition mmaskU (w : int) (s : nat) : int :=
  if (2 <= s)%N then allmvi
  else
    let b := Uint63.mul (Uint63.land (Uint63.lsr w mbits) msmask) ndeci in
    let c := Uint63.lsr w mdbits in
    let lo := Uint63.add b (Uint63.land c mfmask) in
    let hi := Uint63.add b (Uint63.land (Uint63.lsr c mfbits) mfmask) in
    if s is 1%N
    then Uint63.lor (PArray.get flloU lo) (PArray.get flhiU hi)
    else Uint63.lor (PArray.get dnloU lo) (PArray.get dnhiU hi).

(* ---- R3: packed, a power of two a word ------------------------------------- *)

(* twenty bits, two a word                                                    *)
Definition pk20 (sz : nat) (f : int -> int) : arr :=
  mk1 sz (fun w => Uint63.lor (f (Uint63.lsl w 1))
                              (Uint63.lsl (f (Uint63.add (Uint63.lsl w 1) 1)) 20)).
Definition get2 (a : arr) (i : int) : int :=
  Uint63.land (Uint63.lsr (PArray.get a (Uint63.lsr i 1))
                          (Uint63.mul (Uint63.land i 1) 20)) wmaski.
(* four bits, eight a word                                                    *)
Definition pk4 (sz : nat) (f : int -> int) : arr :=
  mk1 sz (fun w => ifold 8 0
                     (fun j a => Uint63.lor a
                        (Uint63.lsl (f (Uint63.add (Uint63.lsl w 3) j))
                                    (Uint63.lsl j 2))) 0).
Definition get8 (a : arr) (i : int) : int :=
  Uint63.land (Uint63.lsr (PArray.get a (Uint63.lsr i 3))
                          (Uint63.lsl (Uint63.land i 7) 2)) 15.

Definition frepP : arr := pk20 506880 frepi.
Definition fsymP : arr := pk4 126720 fsymi.
Definition twsymP : arr := pk20 17496 (get20 twsyma).
Definition dnloP : arr := pk20 32768 (get20 dnlo_data).
Definition dnhiP : arr := pk20 32768 (get20 dnhi_data).
Definition flloP : arr := pk20 32768 (get20 fllo_data).
Definition flhiP : arr := pk20 32768 (get20 flhi_data).
Definition fsmP : PArray.array arr :=
  mkC 5 (fun w => Uint63.lor (fsmv (Uint63.lsl w 1))
                             (Uint63.lsl (fsmv (Uint63.add (Uint63.lsl w 1) 1)) 20)).

Definition cstepP (c k : int) : int :=
  let tw := Uint63.div c nfsi in
  let r := Uint63.sub c (Uint63.mul tw nfsi) in
  let i := Uint63.add (Uint63.mul r 18) k in
  Uint63.add (Uint63.mul (acttwii tw k) nfsi)
    (Uint63.land (Uint63.lsr (getC fsmP (Uint63.lsr i 1))
                             (Uint63.mul (Uint63.land i 1) 20)) wmaski).

Definition p1gP (c : int) : int :=
  let tw := Uint63.div c nfsi in
  let r := Uint63.sub c (Uint63.mul tw nfsi) in
  let y := get8 fsymP r in
  Uint63.lor
    (p1getmS (Uint63.add (Uint63.mul (get2 frepP r) ntwisti)
                         (get2 twsymP (Uint63.add (Uint63.mul tw 16) y))))
    (Uint63.lsl y mbits).

Definition mmaskP (w : int) (s : nat) : int :=
  if (2 <= s)%N then allmvi
  else
    let b := Uint63.mul (Uint63.land (Uint63.lsr w mbits) msmask) ndeci in
    let c := Uint63.lsr w mdbits in
    let lo := Uint63.add b (Uint63.land c mfmask) in
    let hi := Uint63.add b (Uint63.land (Uint63.lsr c mfbits) mfmask) in
    if s is 1%N
    then Uint63.lor (get2 flloP lo) (get2 flhiP hi)
    else Uint63.lor (get2 dnloP lo) (get2 dnhiP hi).

(* ---- the runs ------------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

(* building the tables of R2 and R3, timed apart from the runs               *)
Time Eval native_compute in
  Uint63.add (Uint63.add (PArray.get frepU 5) (PArray.get fsymU 5))
    (Uint63.add (Uint63.add (PArray.get twsymU 5) (PArray.get dnloU 5))
       (Uint63.add (Uint63.add (PArray.get dnhiU 5) (PArray.get flloU 5))
          (Uint63.add (PArray.get flhiU 5) (getC fsmU 5)))).
Time Eval native_compute in
  Uint63.add (Uint63.add (get2 frepP 5) (get8 fsymP 5))
    (Uint63.add (Uint63.add (get2 twsymP 5) (get2 dnloP 5))
       (Uint63.add (Uint63.add (get2 dnhiP 5) (get2 flloP 5))
          (Uint63.add (get2 flhiP 5) (getC fsmP 5)))).

(* R1: as now                                                                  *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapT (fp1g p1ftab frepi fsymi twsymi)
           (mmask dnlo_data dnhi_data fllo_data flhi_data)
           (RowInst.cstep actfsri) 13).
(* R2: one value a slot                                                        *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapT p1gU mmaskU cstepU 13).
(* R3: packed, a power of two a word                                           *)
Time Eval native_compute in fcount48 ffuli forbi fpopi
  (rowmapT p1gP mmaskP cstepP 13).
