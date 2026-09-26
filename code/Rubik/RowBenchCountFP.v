(* =========================================================================  *)
(*  RowBenchCountFP.v -- RowFoldCubDefD's run, its mark reading fsgr packed.  *)
(* =========================================================================  *)

(* A BENCH, not part of any proof.  The folded run of RowFoldCubDefD, timed   *)
(* to thirteen beside the same run whose mark reads fsgr four entries of      *)
(* fifteen bits a word, as RowBenchCoord's pk4 packs.  fsgr is 645 120        *)
(* entries under 20160: 5 MB a word each, 1.3 MB packed, and the mark reads   *)
(* it once, at random.  The OCaml translation (ocaml/rubik_row_rocq.ml)       *)
(* measured the packing at 2.3 s of 24.                                       *)
(*                                                                            *)
(* Only the counting search is copied: wleaf, iwsrchL, wslv, wrun of          *)
(* RowFoldN, with the mark reading the packed table.  The level and the       *)
(* stopping level keep the plain one, so the copy is right past thirteen.     *)
(* The counts must be 14 731 320 both.                                        *)

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
Require Import RowCoord RowCoordLeaf RowFoldN RowFoldCubDefD.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- fsgr, four entries of fifteen bits a word --------------------------- *)

(* RowBenchCoord's pk4 and gt4                                                *)
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

Definition nfsgrw : nat := 161280.            (* 645120 entries, four a word  *)

Definition fsgrP : arr := Eval vm_compute in pk4 nfsgrw nfsgri fsgri.

(* every entry reads back                                                     *)
Definition fsgrPok : bool :=
  iter (to_nat nfsgri) 0 (fun i => Uint63.eqb (gt4 fsgrP i) (PArray.get fsgri i)).

(* ---- the counting mark, reading the packed table ------------------------- *)

(* RowFoldN.fmarknw, sgrmv's read replaced by gt4 on fsgrP                    *)
Definition fmarknwP (fpg fsbt forb : arr) (mn : rmap * int)
                    (pg gr bt : int) : rmap * int :=
  let: (m, n) := mn in
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  let r := fkpt w in
  let g := gt4 fsgrP
             (Uint63.add (Uint63.mul (Uint63.add (Uint63.mul u 2) pty) ngroupi)
                         gr) in
  let v := bitof (fbit (fhlf w) (sbtmv fsbt u bt)) in
  let c := pchk r in
  let i := Uint63.add (poff r) g in
  let a := PArray.get m c in
  let old := PArray.get a i in
  let w' := Uint63.lor old v in
  if Uint63.eqb w' old then mn
  else (PArray.set m c (PArray.set a i w'),
        if Uint63.eqb (fhlf w) 0 then Uint63.add n (PArray.get forb r) else n).

(* ---- RowFoldN's section, the mark changed and nothing else --------------- *)

Section FNP.

Variable e8num e4bit : arr.
Variable fpg fsrc fsrc2 fful fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.
Variables dnlo dnhi fllo flhi : arr.

Local Notation plc := (place24 e8num e4bit).
Local Notation flev := (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi).
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

Local Notation fmknwP := (fmarknwP fpg fsbt forb).
Local Notation isrskL :=
  (isrchskL e8num e4bit fpg fsgr fsbt F frep fsym twsym dnlo dnhi fllo flhi
     cstep xstep tomemb okmv csolved ishm).

(* RowFoldN.wleaf                                                             *)
Definition wleafP (c : int) (x : pst) (a : rmap * int) : rmap * int :=
  if csolved c then let: (pg, gr, bt) := plc (tomemb x) in fmknwP a pg gr bt
  else a.

(* RowFoldN.iwsrchL                                                           *)
Fixpoint iwsrchLP (cut : bool) (togo : nat) (togoi : int) (c : int) (x : pst)
                  (msk pv : int) (a : rmap * int) : rmap * int :=
  if togo is togo'.+1 then
    if togo' is 0 then
      ifold RowRun.nmvn 0
        (fun k a' =>
           if Uint63.eqb (Uint63.land msk (Uint63.lsl 1 k)) 0 then a'
           else if ~~ okmv pv k then a'
           else if cut && ~~ Uint63.eqb (Uint63.land ishm (Uint63.lsl 1 k)) 0
           then a'
           else wleafP (cstep c k) (xstep x k) a')
        a
    else
    let togoi' := Uint63.sub togoi 1 in
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
                           else frcutii <=? Uint63.add togoi' nd)
                     else true)
               else false)
           then iwsrchLP cut togo' togoi' c' (xstep x k)
                         (wmask w (fsslack (Uint63.sub togoi' nd))) k a'
           else a')
      a
  else wleafP c x a.

(* RowFoldN.wslv                                                              *)
Definition wslvP (cut : bool) (d : nat) (m' : rmap) (nb : int) : rmap * int :=
  if (d <= dsrch)%N then
    let w := p1g croot in
    let di := of_nat d in
    if (wdist w <=? di) then
      let msk := wmask w (fsslack (Uint63.sub di (wdist w))) in
      if (d == dsrch)%N then
        let e := Uint63.add enoughb (Uint63.div nb enoughd) in
        isrskL cut d di croot sroot msk 18 e (m', nb)
      else iwsrchLP cut d di croot sroot msk 18 (m', nb)
    else (m', nb)
  else (m', nb).

(* RowFoldN.wrun                                                              *)
Fixpoint wrunP (n : nat) (d : nat) (n0 : int) (m dst : rmap) : rmap :=
  if n is n1.+1 then
    if Uint63.ltb ncutb n0 then
      let m1 := flev m dst in
      let a := wslvP true d.+1 m1 (fcount forb fpop m1) in
      wrunP n1 d.+1 a.2 a.1 m
    else
      let a := wslvP false d.+1 m n0 in
      wrunP n1 d.+1 a.2 a.1 dst
  else m.

End FNP.

(* RowFoldCubDefD.rowmapiD, over wrunP                                        *)
Definition rowmapiDP (n : nat) : rmap :=
  wrunP e8numi e4biti fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti
        mgri mswi mloi mhii
        p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
        (RowInst.cstep actfsri) cstepx cmemb okmvvd ycsolvedd
        RowInst.croot crootD srchd forbi fpopi ishmi
        n 0 0%uint63 (mkempty tt) (mkempty tt).

(* ---- the bench ------------------------------------------------------------ *)

(* thrown away: the tables arriving *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (mkempty tt).

(* the packed table reads back: must be true *)
Time Eval native_compute in fsgrPok.

(* the run as it is, then the run with fsgr packed: 14 731 320 both *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiD 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiDP 13).

(* and once more each, the other way round                                    *)
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiDP 13).
Time Eval native_compute in fcount48 ffuli forbi fpopi (rowmapiD 13).
