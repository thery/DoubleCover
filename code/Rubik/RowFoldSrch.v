(* =========================================================================  *)
(*  RowFoldSrch.v -- the row's run, on the folded map.                        *)
(* =========================================================================  *)

(* NOT PART OF THE PROOF.  This is RowRun.v's search, level and run with two  *)
(* words changed:                                                             *)
(*                                                                            *)
(*    prep   becomes  flevel     the level, on one page of each orbit         *)
(*    mmark  becomes  fmark      a member, marked where the fold keeps it     *)
(*    p1get  becomes  fp1g       the pruning table, read through the fold     *)
(*                                                                            *)
(* The search itself is untouched -- it reaches the map only at a leaf, and   *)
(* only to mark one bit.  Everything else is copied so that RowRun.v, which   *)
(* is proved, is not disturbed.  The proofs are NOT redone here: this file is *)
(* for measuring what the folded row costs.                                   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Coordfs Coordfsi Phase1.
Require Import Row RowMap RowFold RowRun Fold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

Section FSrch.

(* ---- the layout, to read a member's place -------------------------------- *)

Variable e8num e4bit : arr.

Local Notation plc := (place e8num e4bit).

(* ---- the fold, and the move on groups and bits --------------------------- *)

Variable fpg fsrc fsgr fslo fshi fsbt : arr.
Variable mgr msw mlo mhi : arr.

Local Notation flev := (flevel fsrc fsgr fslo fshi mgr msw mlo mhi).
Local Notation fmk := (fmark fpg fsgr fsbt).

(* ---- the phase one table, folded ----------------------------------------- *)

(* THE OTHER FOLD.  The sixteen symmetries act on the flip and slice rank     *)
(* too, so only one rank of each orbit is stored: 64 430 against 1 013 760.   *)
(* A read folds the rank to its orbit and carries the twist through the same  *)
(* symmetry, which is Fold.Dfoldi.                                            *)
(*                                                                            *)
(* THE SEARCH CARRIES ONE NUMBER AND THE FOLD WANTS TWO.  RowInst's           *)
(* coordinate is the twist times the number of ranks plus the rank, so the    *)
(* two come back by one division -- the same number the search already steps, *)
(* read the other way round.                                                  *)
Variable F : PArray.array arr.
Variables frep fsym : int -> int.
Variable twsym : int -> int -> int.

Definition fp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldi F frep fsym twsym tw (Uint63.sub c (Uint63.mul tw nfsi)).

Local Notation p1g := fp1g.

Variable pst : Type.
Variable cstep : int -> int -> int.
Variable xstep : pst -> int -> pst.
Variable tomemb : pst -> memb.
Variable okmv : int -> int -> bool.
Variable csolved : int -> pst -> bool.

(* ---- the search ---------------------------------------------------------- *)

(* RowRun.srch, mark for mark, with fmk at the leaf.                          *)
Fixpoint fsrch (togo : nat) (c : int) (x : pst) (msk : int) (pv : int)
               (m : rmap) : rmap :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k m' =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then m'
         else if ~~ okmv pv k then m'
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then fsrch togo' c' (xstep x k) (wmask w (togo' - nd)) k m'
           else m')
      m
  else if csolved c x
       then let: (pg, gr, bt) := plc (tomemb x) in fmk m pg gr bt
       else m.

(* NOT PART OF THE RUN.  The same search, counting the leaves it reaches       *)
(* instead of marking them, so that a search which finds nothing can be told  *)
(* from a mark that is lost on the way to the map.                            *)
Fixpoint fsrchn (togo : nat) (c : int) (x : pst) (msk : int) (pv : int)
                (n : int) : int :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmv pv k then a
         else
           let c' := cstep c k in
           let w := p1g c' in
           let nd := Uint63.to_nat (wdist w) in
           if (nd <= togo')%N
           then fsrchn togo' c' (xstep x k) (wmask w (togo' - nd)) k a
           else a)
      n
  else if csolved c x then Uint63.add n 1 else n.

(* ---- one level, and the run ---------------------------------------------- *)

Variable croot : int.
Variable sroot : pst.
Variable dsrch : nat.

Definition flvl (d : nat) (m : rmap) : rmap :=
  let m' := flev m in
  if (d <= dsrch)%N then
    let w := p1g croot in
    let nd := Uint63.to_nat (wdist w) in
    if (nd <= d)%N then fsrch d croot sroot (wmask w (d - nd)) 18%uint63 m'
    else m'
  else m'.

Fixpoint frun (n : nat) (d : nat) (m : rmap) : rmap :=
  if n is n1.+1 then frun n1 d.+1 (flvl d.+1 m) else m.

End FSrch.
