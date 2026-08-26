(* =========================================================================  *)
(*  RowFoldWhy.v -- where the search's time goes, one piece taken out at a    *)
(*  time.                                                                     *)
(* =========================================================================  *)

(* THE HUNDRED IS THE SEARCH, NOT THE RUN.  Ten levels and their counts cost  *)
(* 170.9 s here against about a second a level for the prototype, which is    *)
(* fifteen.  Depth thirteen costs 2 904.8 s against the prototype's 27.7, and *)
(* the three levels between the two account for about a minute of the         *)
(* difference.  So the searches at eleven, twelve and thirteen carry it.      *)
(*                                                                            *)
(* THE TREE DOES NOT DEPEND ON THE POSITION.  Which moves a node tries is     *)
(* decided by the coordinate, the mask read beside the distance and the move  *)
(* test -- never by the forty eight entry table the search also carries.  So  *)
(* a piece can be taken out and the SAME tree is walked; what changes is the  *)
(* time, and that difference is what the piece costs.                         *)
(*                                                                            *)
(* Three pieces are asked about here:                                         *)
(*                                                                            *)
(*   the position   a move composes a fresh forty eight entry table at every  *)
(*                  node, and only a leaf ever reads it                       *)
(*   the unary nat  the distance is turned into a nat and compared with one   *)
(*                  at every node, and the mask is chosen by a nat too        *)
(*   the leaves     how many nodes there are, so that a time can be read as   *)
(*                  a time per node and put beside the prototype's            *)

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

(* ---- RowInst's own step and leaf test, spelt out ------------------------- *)

(* Written out as RowFoldSrch10.v writes them, so that this file does not     *)
(* depend on how a section discharged them.                                   *)
Definition fstep (c k : int) : int :=
  Uint63.add (Uint63.mul (acttwii (Uint63.div c nfsi) k) nfsi)
             (actfsri (Uint63.mod c nfsi) k).

(* the leaf test meets no permutation: three numbers compared                 *)
Definition fsolved (c : int) (x : pstt) : bool :=
  [&& Uint63.eqb c csolvedci, Uint63.eqb (ctwisti x) 0%uint63
    & Uint63.eqb (coordi x) coordfs1i].

(* ---- the two depths asked about ------------------------------------------ *)

(* Eleven is the first depth whose search costs anything -- ten is eight      *)
(* thousand positions -- and twelve is about ten times eleven, which is as    *)
(* far as a probe need go.                                                    *)
Definition dlow  : nat := 11.
Definition dhigh : nat := 12.

(* the same two as numbers, for the search that keeps the depth left a       *)
(* number instead of a nat                                                    *)
Definition dlowi  : int := 11%uint63.
Definition dhighi : int := 12%uint63.

(* ---- the pieces the search is made of ------------------------------------ *)

(* the pruning table read through the fold: the search carries one number     *)
(* and the fold wants two, so one division gives both                         *)
Definition wp1g (c : int) : int :=
  let tw := Uint63.div c nfsi in
  Dfoldm p1ftab frepi fsymi twsymi tw (Uint63.sub c (Uint63.mul tw nfsi)).

Notation wmsk := (mmask dnlo_data dnhi_data fllo_data flhi_data).

(* the position, kept instead of stepped.  The tree is untouched: nothing     *)
(* above a leaf looks at it.  The leaf test then fails everywhere and the     *)
(* count is nought, WHICH IS EXPECTED -- this run is a time, not an answer.   *)
Definition xkeep (x : pstt) (_ : int) : pstt := x.

(* ---- the same search, counting nodes rather than leaves ------------------ *)

(* A time is worth little without the number of nodes it covers, and the      *)
(* prototype prints its own.  One is added at every descent, so the count is  *)
(* the nodes below the root.  The leaf test is left in: it is part of what a  *)
(* leaf costs.                                                                *)
Fixpoint wsrch (togo : nat) (c : int) (x : pstt) (msk pv n : int) : int :=
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
           then wsrch togo' c' (xstep x k) (wmsk w (togo' - nd)) k
                  (Uint63.add a 1%uint63)
           else a)
      n
  else if fsolved c x then n else n.

(* ---- and the same again with the distance kept a number ------------------ *)

(* THE DISTANCE IS FOUR BITS AND IT IS COMPARED AS A UNARY NAT.  to_nat walks *)
(* the value out one constructor at a time, the test walks it back, and the   *)
(* subtraction that chooses the mask walks it a third time -- at every node.  *)
(* Here the depth left is carried as a number beside the nat that makes the   *)
(* recursion stop, and the three walks go.  Nothing else moves.               *)

Definition mspare : int := 2%uint63.   (* two to spare, and any move will do  *)
Definition mnear  : int := 1%uint63.   (* one, and a move that does not lose  *)

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

Fixpoint wsrchi (togo : nat) (togoi c : int) (x : pstt)
                (msk pv n : int) : int :=
  if togo is togo'.+1 then
    let togoi' := Uint63.sub togoi 1%uint63 in
    ifold nmvn 0%uint63
      (fun k a =>
         if Uint63.eqb (Uint63.land msk (Uint63.lsl 1%uint63 k)) 0%uint63
         then a
         else if ~~ okmvv pv k then a
         else
           let c' := fstep c k in
           let w := wp1g c' in
           let d := mdist w in
           if Uint63.leb d togoi'
           then wsrchi togo' togoi' c' (xstep x k)
                  (wmski w (Uint63.sub togoi' d)) k (Uint63.add a 1%uint63)
           else a)
      n
  else if fsolved c x then n else n.

(* ---- what is asked, cheapest first --------------------------------------- *)

(* Each block is the same tree at the same depth.  The first says what the    *)
(* search costs as it stands and how many leaves it reaches; the second what  *)
(* it costs with no position built; the third gives the nodes; the fourth     *)
(* what it costs with the distance kept a number.  The third and the fourth   *)
(* differ in that one thing alone and are the pair to read together.          *)

(* --- eleven --- *)

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved dlow croot sroot allmv 18 0.

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xkeep okmvv fsolved dlow croot sroot allmv 18 0.

Time Eval native_compute in wsrch dlow croot sroot allmv 18 0.

Time Eval native_compute in wsrchi dlow dlowi croot sroot allmv 18 0.

(* --- twelve --- *)

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xstep okmvv fsolved dhigh croot sroot allmv 18 0.

Time Eval native_compute in
  fsrchn p1ftab frepi fsymi twsymi dnlo_data dnhi_data fllo_data flhi_data
    fstep xkeep okmvv fsolved dhigh croot sroot allmv 18 0.

Time Eval native_compute in wsrch dhigh croot sroot allmv 18 0.

Time Eval native_compute in wsrchi dhigh dhighi croot sroot allmv 18 0.
