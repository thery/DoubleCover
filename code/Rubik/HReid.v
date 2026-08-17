(* =========================================================================  *)
(*  HReid.v -- what Proposition 2 of Reid's post rests on.                    *)
(* =========================================================================  *)

(* The six positions the run searches are the right six because of Reid's     *)
(* Proposition 2: every maneuver for superflip composed with fourspot can be  *)
(* turned into one beginning with one of six sequences.  His proof uses three *)
(* transformations of a maneuver -- conjugate by a symmetry keeping the axis, *)
(* shift it cyclically, invert it -- and one fact about the twelve turns: they*)
(* fall into a four and an eight, and a maneuver for the position must use    *)
(* both, since the four alone reach only sixteen positions and the eight alone*)
(* cannot flip an edge.                                                       *)
(*                                                                            *)
(* This file proves that fact and the engine the shifting runs on.  The word  *)
(* argument on top of them is NOT here -- see the end of the file for what is *)
(* left.                                                                      *)
(*                                                                            *)
(* THE POSITION IS TURNED ONTO THE FRONT-BACK AXIS, and that is not a detail. *)
(* Reid's eight is {R, R', F, F', L, L', B, B'} and his claim is that they    *)
(* cannot flip an edge, which is true where U and D are the flipping turns and*)
(* FALSE here, where F and B are.  He says himself that the orientation of    *)
(* fourspot is a choice, so the position is turned instead of the convention: *)
(* then the four are {F, F', B, B'} and the eight are {U, U', D, D', R, R', L,*)
(* L'}, which carry no flip here.  ocaml/rubik_reid.ml rephrase is the        *)
(* specification, and reid_eight_flips below is the check that the turn is    *)
(* doing real work.                                                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Coordfs Phase1 HRoot HCoord.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the position, turned onto the front-back axis ----------------------- *)

(* Reid's fourspot word F2 B2 U D' R2 L2 U D', with U -> F -> D -> B -> U and *)
(* R and L fixed, is D2 U2 F B' R2 L2 F B'.                                   *)
Definition fsfbw : seq nat := [:: 10; 1; 6; 17; 4; 13; 6; 17]%N.

Definition pfb : arr := appw idi (sfw ++ fsfbw).

Definition ufb : arr := inv_tabi flast pfb.

(* one quarter turn, as a table                                               *)
Definition mvq (m : nat) : arr := mvi (qt18 m).

(* ---- the engine: the half turn about the front-back axis ----------------- *)

(* Conjugation by that half turn swaps U with D and R with L, and fixes F and *)
(* B.  It is what a cyclic shift of a maneuver conjugates the shifted part by,*)
(* and the reason the shift gives a maneuver for the same position is exactly *)
(* the identity below.                                                        *)
Definition sigface : seq nat := [:: 3; 4; 2; 0; 1; 5]%N.

Definition sigq (m : nat) : nat := (2 * nth 0%N sigface (m %/ 2) + odd m)%N.

Lemma pfb_sigma :
  all (fun m => eq_tabi flast
                  (comp_tabi flast (comp_tabi flast ufb (mvq m)) pfb)
                  (mvq (sigq m)))
      (iota 0 12) = true.
Proof. by vm_compute. Qed.

(* ---- the eight cannot flip an edge --------------------------------------  *)

(* U U' D D' R R' L L' in this file's numbering                               *)
Definition eightm : seq nat := [:: 0; 1; 6; 7; 2; 3; 8; 9]%N.

(* F F' B B'                                                                  *)
Definition fourm : seq nat := [:: 4; 5; 10; 11]%N.

(* A turn carries no flip when it leaves every edge's primary sticker primary.*)
Definition noflip (m : nat) : bool :=
  all (fun j => eflipn (inv_tabi flast (mvq m)) j == 0%N) (iota 0 nedge).

Lemma eight_noflip : all noflip eightm = true.
Proof. by vm_compute. Qed.

(* AND THE SAME READ LITERALLY OFF REID DOES NOT HOLD, which is what the turn *)
(* of the position buys.  R R' F F' L L' B B' is his eight.                   *)
Definition reid_eightm : seq nat := [:: 2; 3; 4; 5; 8; 9; 10; 11]%N.

Lemma reid_eight_flips : all noflip reid_eightm = false.
Proof. by vm_compute. Qed.

(* and the position has every edge flipped, so no product of the eight is it  *)
Lemma pfb_allflip :
  all (fun j => eflipn ufb j == 1%N) (iota 0 nedge) = true.
Proof. by vm_compute. Qed.

(* ---- the four reach only sixteen positions ------------------------------- *)

(* On tables as lists, because a list of those has an equality and a list of  *)
(* arrays does not: sixteen positions have to be told apart.                  *)
Definition mvt (m : nat) : seq nat := nth (id_tab flast) mtabs (qt18 m).

Definition grow (l : seq (seq nat)) : seq (seq nat) :=
  undup (l ++ flatten [seq [seq comp_tab t (mvt m) | m <- fourm] | t <- l]).

Definition gen4 : seq (seq nat) := Eval vm_compute in
  iter 5 grow [:: id_tab flast].

Lemma gen4_size : seq.size gen4 = 16.
Proof. by vm_compute. Qed.

(* and it is a group, not merely a ball: nothing leaves it                    *)
Lemma gen4_closed :
  all (fun t => all (fun m => comp_tab t (mvt m) \in gen4) fourm) gen4 = true.
Proof. by vm_compute. Qed.

Lemma pfb_not_gen4 : (ti2t flast pfb \in gen4) = false.
Proof. by vm_compute. Qed.

(* ---- the corner parity that rules out twenty five -----------------------  *)

(* A quarter turn is an odd permutation of the corners, so the distance of a  *)
(* position has the parity of its corner permutation.  This one is even, which*)
(* is what takes "nothing at 24" to "exactly 26" -- a step Reid leaves        *)
(* implicit.                                                                  *)
Definition invcount (f : nat -> nat) (n : nat) : nat :=
  sumn [seq count (fun j => (f j < f i)%N) (iota (i + 1) (n - i - 1))
       | i <- iota 0 n].

Definition cparity (u : arr) : bool := odd (invcount (cplace u) 8).

Lemma pfb_even : cparity ufb = false.
Proof. by vm_compute. Qed.

(* ---- what is left -------------------------------------------------------  *)

(* The facts above are the whole of the arithmetic in Proposition 2.  What is *)
(* left is a statement about WORDS, and it needs no machine:                  *)
(*                                                                            *)
(*   1. the three transformations keep both "is a maneuver for the position"  *)
(*      and its length: conjugation by one of the sixteen symmetries, the     *)
(*      cyclic shift whose engine is pfb_sigma, and inversion;               *)
(*   2. a maneuver uses both kinds of turn -- from pfb_allflip with           *)
(*      eight_noflip, and from gen4_size with pfb_not_gen4;                   *)
(*   3. so two kinds are adjacent somewhere, and shifting brings that pair to *)
(*      the front, where symmetry names it R U or R' U;                       *)
(*   4. the eleven third turns after R' U reduce to five, the other six going *)
(*      to the R U case by symmetry or by inversion.                          *)
(*                                                                            *)
(* None of that is proved yet, and until it is, the run establishes only that *)
(* those six positions have no maneuver at those depths.                      *)
