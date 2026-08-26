(* =========================================================================  *)
(*  RowOkm.v -- the moves a node may play, read instead of worked out.        *)
(* =========================================================================  *)

(* WHY.  RowReal's okmvv asks whether a move may follow another, and it       *)
(* divides the PREVIOUS move by three to do it -- inside the loop, so once    *)
(* for each of the eighteen, though the previous move does not change while   *)
(* the node is being looked at.  The prototype works its own out once a node  *)
(* and then only compares.  Seventeen divisions a node buy nothing.           *)
(*                                                                            *)
(* WHAT IS HERE.  For each of the nineteen previous moves -- the eighteen and *)
(* the one that means `no previous move' -- the moves it allows, as a word of *)
(* eighteen bits.  A node then reads one word and the loop only tests bits,   *)
(* which is what it already does for the pruning table's own mask.            *)
(*                                                                            *)
(* The table is built from okmvv itself, so there is nothing to trust, and    *)
(* okmviE checks all nineteen by eighteen of it by computation.               *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowWits RowReal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Local Open Scope uint63_scope.

Definition nmvi : int := 18.
Definition npvi : int := 19.

Definition okrow (pv : int) : int :=
  ifold 18 0
    (fun k a => if okmvv pv k then Uint63.lor a (Uint63.lsl 1 k) else a) 0.

Definition okmvi : arr :=
  Eval vm_compute in mkarrn npvi [seq okrow (of_nat p) | p <- iota 0 19].

Definition okmviok : bool :=
  alli 19 0 (fun pv => alli 18 0 (fun k =>
    Uint63.eqb (Uint63.land (PArray.get okmvi pv) (Uint63.lsl 1 k)) 0
    == ~~ okmvv pv k)).

Lemma okmviokE : okmviok. Proof. by vm_compute. Qed.

Lemma h0 : to_nat 0 = 0%N. Proof. by []. Qed.

Lemma alliN (n : nat) (f : int -> bool) : (n < nwB)%N -> alli n 0 f ->
  forall i, (to_nat i < n)%N -> f i.
Proof.
move=> hn.
have hw : (to_nat 0 + n < nwB)%N by rewrite h0 add0n.
rewrite (alliE f hw) h0 => /allP hall i hi.
by rewrite -[i]to_natK; apply: hall; rewrite mem_iota add0n hi.
Qed.

Lemma n19_lt : (19 < nwB)%N. Proof. by apply: (@ltn_nwB 5). Qed.
Lemma n18_lt : (18 < nwB)%N. Proof. by apply: (@ltn_nwB 5). Qed.

Lemma okmviE pv k : (to_nat pv < 19)%N -> (to_nat k < 18)%N ->
  Uint63.eqb (Uint63.land (PArray.get okmvi pv) (Uint63.lsl 1 k)) 0
  = ~~ okmvv pv k.
Proof.
move=> hpv hk; move: okmviokE; rewrite /okmviok => hok.
have h1 := alliN n19_lt hok hpv.
by have /eqP := alliN n18_lt h1 hk.
Qed.
