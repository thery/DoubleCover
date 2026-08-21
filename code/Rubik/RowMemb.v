(* =========================================================================  *)
(*  RowMemb.v -- the cube a member names, and the member a cube gives.        *)
(* =========================================================================  *)

(* THIS IS THE ONE PLACE WHERE THREE RANKS MEET FORTY EIGHT FACELETS, and     *)
(* neither half of it is new: the corners are Phase1's -- ctrip is the eight  *)
(* as facelet triples, cpos and cslot say which corner a facelet belongs to   *)
(* and how far round -- and the edges are Coordfs's, eprim and esec, in the   *)
(* order the prototype uses, so the outer eight are the first eight and the   *)
(* middle four the last.                                                      *)
(*                                                                            *)
(* WHAT IS BUILT IS THE INVERSE, because that is the direction that needs no  *)
(* search: at the facelet of slot p, the position's inverse gives the home    *)
(* facelet of whatever cubie sits at p, and the tables say which cubie that   *)
(* is.  The member's own table is that inverted, which Table.inv_tab does.    *)
(*                                                                            *)
(* Nothing here is turned or flipped: a member of H is three permutations and *)
(* nothing else, which is exactly why three ranks are enough.                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabP.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

(* ---- the permutation of a rank ------------------------------------------- *)

(* Unranking is a computation and the layout tables are written in terms of   *)
(* it, so the prototype writes it out: eight numbers to a corner rank, four   *)
(* to a middle one.                                                           *)

Definition up8i : arr := Eval vm_compute in
  mkarr 322560%uint63 0%uint63 up8_data.
Definition up4i : arr := Eval vm_compute in
  mkarr 96%uint63 0%uint63 up4_data.

Definition up8 (r : int) (p : nat) : nat :=
  to_nat (PArray.get up8i (Uint63.add (Uint63.mul r 8%uint63) (of_nat p))).

Definition up4 (r : int) (p : nat) : nat :=
  to_nat (PArray.get up4i (Uint63.add (Uint63.mul r 4%uint63) (of_nat p))).

(* ---- the cube a member names --------------------------------------------- *)

(* which cubie is at edge place p: the outer eight come from the outer rank   *)
(* and the middle four from the middle one, which is what makes the middle a  *)
(* separate rank at all                                                       *)
Definition eat (x : memb) (p : nat) : nat :=
  if (p < 8)%N then up8 (mud x) p else 8 + up4 (mmp x) (p - 8).

(* the inverse: at the facelet of a place, the home facelet of what sits      *)
(* there                                                                      *)
Definition membinv (x : memb) : seq nat :=
  mkseq (fun f =>
     if (f \in cflat) then
       nth 0%N cflat (3 * up8 (mcp x) (cpos (inord f)) + cslot (inord f))%N
     else if (f \in eprim) then nth 0%N eprim (eat x (epos (inord f)))
     else nth 0%N esec (eat x (epos (inord f))))
   48.

Definition memb2tab (x : memb) : seq nat := inv_tab flast (membinv x).

(* ---- and the member a cube gives ----------------------------------------- *)

(* The three ranks read off a position, which is what the search does at a    *)
(* leaf.  It is only meant for a position of H: outside it the edges are      *)
(* mixed between the outer eight and the middle four and there is no outer    *)
(* permutation to rank.                                                       *)
(* the rank of a permutation, the prototype's own: fold over the places, and *)
(* at each one count how many later places hold something smaller.  It is a  *)
(* computation over eight numbers, so no table is wanted.                    *)
Definition lrank (n : nat) (f : nat -> nat) : nat :=
  foldl (fun r i =>
           (r * (n - i)
            + count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1)))%N)
        0%N (iota 0 n).

Definition rank8 (f : nat -> nat) : int := of_nat (lrank 8 f).
Definition rank4 (f : nat -> nat) : int := of_nat (lrank 4 f).

Definition tomemb (a : arr) : memb :=
  (rank8 (fun p => cpos ((pt flast (ti2t flast a))^-1 (cprimf p))),
   rank8 (fun p => epos ((pt flast (ti2t flast a))^-1 (eprimf p))),
   rank4 (fun p =>
      (epos ((pt flast (ti2t flast a))^-1 (eprimf (8 + p))) - 8)%N)).
