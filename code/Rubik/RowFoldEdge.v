(* =========================================================================  *)
(*  RowFoldEdge.v -- what one step of the search costs, on its own.           *)
(* =========================================================================  *)

(* WHERE THIS COMES FROM.  RowFoldWhy.v measured the search at twelve         *)
(* microseconds a position: four of them building the cube afresh, one on     *)
(* Rocq's slow numbers, and SEVEN on looking a position up in the table.      *)
(* Seven is the one that makes no sense -- the lookup is a handful of array   *)
(* reads and a read was measured at 0.04 -- so it is taken apart here.        *)
(*                                                                            *)
(* A position offers three or four moves, so each of them costs about two     *)
(* microseconds, and each does three things: it steps the coordinate, it      *)
(* looks the new one up in the table, and it decodes the moves stored beside  *)
(* the distance.  One loop is run for each, and each is the one before it     *)
(* with one thing added, so a difference is what that thing costs.            *)
(*                                                                            *)
(* WHERE THE READS LAND MATTERS AS MUCH AS HOW MANY.  The table is 563 MB,    *)
(* far past any cache, so a read of a fresh place is a trip to memory and a   *)
(* read of a near one is not.  The same four loops are therefore run twice:   *)
(* once walking across the table in big strides, which is the worst case, and *)
(* once walking one coordinate at a time, which is the best.  The search      *)
(* itself is somewhere between, and the two runs say between what and what.   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import Fold FoldTables P1Fdec P1FTable RowMask.
Require Import RowFold RowTabF RowFoldTab RowFoldSrch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the three things a step does, spelt out ----------------------------- *)

(* RowInst's own step: the twist by one table, the flip and slice by another  *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

(* the table read through the fold: the coordinate carries one number and the *)
(* fold wants two, so one division gives both                                 *)
Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

(* the moves stored beside the distance, decoded and renamed back.  The       *)
(* tightest case is asked for: nothing to spare, so only the moves that bring *)
(* the state nearer are wanted, which is two reads of the decoding tables.    *)
Definition mtight : int := 0%uint63.
Definition mspare : int := 2%uint63.
Definition mnear  : int := 1%uint63.

Definition wmski (w si : int) : int :=
  if Uint63.leb mspare si then allmvi
  else
    let b := Uint63.mul (Uint63.land (Uint63.lsr w mbits) msmask) ndeci in
    let c := Uint63.lsr w mdbits in
    let lo := Uint63.add b (Uint63.land c mfmask) in
    let hi := Uint63.add b (Uint63.land (Uint63.lsr c mfbits) mfmask) in
    if Uint63.eqb si mnear
    then Uint63.lor (get20 fllo_data lo) (get20 flhi_data hi)
    else Uint63.lor (get20 dnlo_data lo) (get20 dnhi_data hi).

(* ---- where the next coordinate comes from -------------------------------- *)

(* the whole of phase one: the twists times the flip and slice ranks          *)
Definition ncoordi : int := 2217093120%uint63.

(* a stride that lands far away every time, so every read is a fresh place    *)
Definition farstep : int := 1234567891%uint63.

(* and the smallest step there is, so every read is beside the last           *)
Definition nearstep : int := 1%uint63.

Definition nxtby (s c : int) : int :=
  let c' := Uint63.add c s in
  if Uint63.leb ncoordi c' then Uint63.sub c' ncoordi else c'.

Definition nxtfar (c : int) : int := nxtby farstep c.
Definition nxtnear (c : int) : int := nxtby nearstep c.

(* ---- the loop ------------------------------------------------------------ *)

(* A MILLION TIMES, AS TWO LOOPS OF A THOUSAND.  A nat is written out one     *)
(* step at a time, so a million as a single count would be a million          *)
(* constructors in the file; a thousand of a thousand is two small ones.      *)
Definition nout : nat := 1000.
Definition nin  : nat := 1000.

(* the coordinate and the running sum travel together; the sum is there only  *)
(* so that the work cannot be thrown away                                     *)
Fixpoint iter (n : nat) (nx : int -> int) (f : int -> int -> int)
              (ca : int * int) : int * int :=
  if n is n1.+1 then
    let: (c, a) := ca in iter n1 nx f (nx c, f c a)
  else ca.

Fixpoint iters (n : nat) (nx : int -> int) (f : int -> int -> int)
               (ca : int * int) : int * int :=
  if n is n1.+1 then iters n1 nx f (iter nin nx f ca) else ca.

Definition runw (nx : int -> int) (f : int -> int -> int) : int :=
  (iters nout nx f (croot, 0%uint63)).2.

(* ---- the four bodies, each the one before it with one thing added -------- *)

(* the move played is fixed: which one is played changes nothing here         *)
Definition kfix : int := 0%uint63.

Definition bnone (c a : int) : int := Uint63.add a c.
Definition bstep (c a : int) : int := Uint63.add a (fstep c kfix).
Definition bread (c a : int) : int := Uint63.add a (wp1g c).
Definition bmask (c a : int) : int :=
  Uint63.add a (wmski (wp1g c) mtight).

(* ---- what is asked ------------------------------------------------------- *)

(* Eight runs of a million.  The first four walk across the table, the last   *)
(* four walk along it.  In each four: the loop alone, the loop and the        *)
(* coordinate step, the loop and the table read, and the loop, the read and   *)
(* the decoding.  Subtract each from the next and the piece is named.         *)

(* --- across the table --- *)

Time Eval native_compute in runw nxtfar bnone.
Time Eval native_compute in runw nxtfar bstep.
Time Eval native_compute in runw nxtfar bread.
Time Eval native_compute in runw nxtfar bmask.

(* --- along the table --- *)

Time Eval native_compute in runw nxtnear bnone.
Time Eval native_compute in runw nxtnear bstep.
Time Eval native_compute in runw nxtnear bread.
Time Eval native_compute in runw nxtnear bmask.
