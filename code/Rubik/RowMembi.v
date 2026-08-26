(* =========================================================================  *)
(*  RowMembi.v -- where a position stands, without leaving int63.             *)
(* =========================================================================  *)

(* WHY.  MEASURED at depth eleven: the search finds 86 144 answers in 2.5 s   *)
(* and RowMemb's tomemb turns them into ranks in 12.0 -- 110 microseconds an  *)
(* answer, against 0.5 for the place that follows it and 2.4 for the write    *)
(* into the map.  Three quarters of the whole thirteen level run is that one  *)
(* function.                                                                  *)
(*                                                                            *)
(* WHAT IS IN IT.  `ti2t' writes the forty eight entry table out as a LIST OF *)
(* UNARY NUMBERS, and every entry costs an of_nat -- measured elsewhere in    *)
(* this development at 1.53 microseconds for a value of twenty one, against   *)
(* 0.04 for the array read it stands in for.  The two ranks then ask for      *)
(* forty more.  Ninety unary numbers an answer is the hundred and ten.        *)
(*                                                                            *)
(* WHAT IS HERE.  The same three ranks with no nat anywhere: the inverse      *)
(* table stays an array, the three lookup tables are arrays, and the rank is  *)
(* the same mixed radix fold done on int63.  NOTHING IS PROVED YET -- the     *)
(* bridge at the bottom is admitted on purpose, so that what it is worth can  *)
(* be measured before it is paid for.                                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Lehmer RowTabP RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

(* ---- the lookup tables, as arrays ---------------------------------------- *)

Definition nfacei : int := 48.        (* the facelets                         *)
Definition ncorni : int := 8.         (* the corners, and the outer edges     *)
Definition nmidi  : int := 4.         (* the middle edges                     *)

(* which corner place a facelet belongs to, and which edge place              *)
Definition cposia : arr :=
  Eval vm_compute in mkarrn nfacei [seq of_nat v | v <- cposv].
Definition eposia : arr :=
  Eval vm_compute in mkarrn nfacei [seq of_nat v | v <- eposv].

(* the primary facelet of each corner place; the edges have eprimi already    *)
Definition cprimia : arr :=
  Eval vm_compute in mkarrn ncorni [seq of_nat v | v <- cprimp].

(* ---- the rank, on int63 -------------------------------------------------- *)

(* Lehmer's digit: at place i, how many later places hold a smaller value.    *)
(* The walk is over all n places rather than the ones after i, because n is   *)
(* eight or four and the count that a nat walk needs is then a constant.      *)
Definition lcodei (nn : nat) (f : int -> int) (i : int) : int :=
  ifold nn 0
    (fun j c =>
       if (Uint63.ltb i j) && (Uint63.ltb (f j) (f i))
       then Uint63.add c 1 else c)
    0.

(* and the mixed radix fold RowMemb's lranki does, with the of_nat gone       *)
Definition lrankii (nn : nat) (ni : int) (f : int -> int) : int :=
  ifold nn 0
    (fun i r => Uint63.add (Uint63.mul r (Uint63.sub ni i)) (lcodei nn f i))
    0.

Definition rank8i (f : int -> int) : int := lrankii 8 ncorni f.
Definition rank4i (f : int -> int) : int := lrankii 4 nmidi f.

(* ---- where a position stands --------------------------------------------- *)

(* RowMemb.tomemb, read the same way: the inverse table says, at the primary  *)
(* facelet of a place, the home facelet of whatever sits there; the tables    *)
(* turn that facelet into the place it came from; the three ranks follow.     *)
Definition tomembi (a : arr) : memb :=
  let u := inv_tabi flast a in
  (rank8i (fun p => PArray.get cposia (PArray.get u (PArray.get cprimia p))),
   rank8i (fun p => PArray.get eposia (PArray.get u (PArray.get eprimi p))),
   rank4i (fun p =>
             Uint63.sub
               (PArray.get eposia
                  (PArray.get u (PArray.get eprimi (Uint63.add ncorni p))))
               ncorni)).

(* ---- the bridge, ADMITTED ------------------------------------------------ *)

(* ON PURPOSE, and it is the only thing this file owes.  Everything above is  *)
(* a rewriting of RowMemb.tomemb with the nats taken out, and whether it is   *)
(* worth proving is a question about how much time it saves.  The measurement *)
(* does not need the proof: the run prints the same count as before or it     *)
(* does not, and if it does not the definition is wrong whatever is claimed   *)
(* here.                                                                      *)
Lemma tomembiE a : tomembi a = tomemb a.
Admitted.
