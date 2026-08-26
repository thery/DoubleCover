(* =========================================================================  *)
(*  RowFoldFast.v -- what the int63 tomemb is worth.                          *)
(* =========================================================================  *)

(* MEASURED, depth eleven, 86 144 answers: the search alone 2.5 s, the same   *)
(* search turning each answer into ranks 12.0, into a place 12.1, and into a  *)
(* bit in the map 12.3.  So the conversion is 110 microseconds of the 113 an  *)
(* answer costs, and it is three quarters of the whole thirteen level run.    *)
(*                                                                            *)
(* RowMembi.tomembi is that conversion with no nat in it.  The old and the    *)
(* new are run side by side here, in one warm file, and the last two runs put *)
(* the answers in the map: BOTH MUST PRINT 71 296.  A faster wrong count is   *)
(* worth nothing, and the bridge between the two is admitted, so the count is *)
(* the only thing standing between this and a wrong definition.               *)
(*                                                                            *)
(* The first Eval is a copy of the second and is thrown away: the first of a  *)
(* file pays for the tables arriving.                                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf RowMembi.
Require Import RowWits RowReal.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* RowInst's own step and leaf test, spelt out as the other files spell them  *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedci, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) coordfs1i].

Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

Definition dlow : nat := 11.

(* ---- the search, with what happens at an answer handed in ---------------- *)

Fixpoint lsrch (lf : pstt -> int -> int) (togo : nat) (c : int) (x : pstt)
               (msk pv n : int) : int :=
  if togo is togo'.+1 then
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmvv pv k then a
         else
           let c' := fstep c k in
           let w := wp1g c' in
           let nd := Uint63.to_nat (mdist w) in
           if (nd <= togo')%N
           then lsrch lf togo' c' (xstep x k) (wmsk w (togo' - nd)) k a
           else a)
      n
  else if fsolved c x then lf x n else n.

Definition lnone (_ : pstt) (n : int) : int := Uint63.add n 1%uint63.
Definition lmemb (x : pstt) (n : int) : int := Uint63.add n (mcp (tomemb x)).
Definition lmembi (x : pstt) (n : int) : int := Uint63.add n (mcp (tomembi x)).

(* ---- what is asked ------------------------------------------------------- *)

(* thrown away: the tables arriving *)
Time Eval native_compute in lsrch lnone dlow croot sroot allmv 18 0.

(* the search alone: 86 144 answers, none of them looked at *)
Time Eval native_compute in lsrch lnone dlow croot sroot allmv 18 0.

(* each answer turned into ranks, the old way and the new.  The two totals    *)
(* must agree: they are the same number added up.                            *)
Time Eval native_compute in lsrch lmemb dlow croot sroot allmv 18 0.
Time Eval native_compute in lsrch lmembi dlow croot sroot allmv 18 0.

(* the sweep that counts the map, on its own *)
Time Eval native_compute in fcount forbi fpopi (mkempty tt).

(* and the run itself, old and new.  BOTH MUST PRINT 71 296. *)

Time Eval native_compute in
  fcount forbi fpopi
    (fsrch e8numi e4biti fpgi fsgri fsbti
       p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
       fstep xstep tomemb okmvv fsolved dlow croot sroot allmv 18
       (mkempty tt)).

Time Eval native_compute in
  fcount forbi fpopi
    (fsrch e8numi e4biti fpgi fsgri fsbti
       p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
       fstep xstep tomembi okmvv fsolved dlow croot sroot allmv 18
       (mkempty tt)).
