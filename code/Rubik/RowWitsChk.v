(* =========================================================================  *)
(*  RowWitsChk.v -- the witnesses, played back.                              *)
(* =========================================================================  *)

(* Thirty two members the row left over, each with a word of twenty.  This    *)
(* plays every one of them: compose the member's table with the word's and    *)
(* ask for the identity.  Whatever found the words is not mentioned and not   *)
(* believed -- ours found twenty eight and four more one at a time, and it    *)
(* would make no difference if Rokicki's had found them all.                  *)
(*                                                                            *)
(* IT IS ALSO THE FIRST REAL TEST OF memb2tab.  The words were found by the   *)
(* prototype, which has its own idea of which facelet is which; the member's  *)
(* table is built here from Phase1's corners and Coordfs's edges.  If the two *)
(* ideas disagree the replay fails, and nothing else in the development would *)
(* have caught it.                                                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowPrep RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowWits.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the list, read at the corner pair ----------------------------------- *)

(* THE GENERATED LIST IS A LIST OF TWENTY FOUR BIT PLACES, and a page in it   *)
(* is a corner RANK.  The map is indexed by the corner PAIR, so the same      *)
(* member stands at another place: the rank n splits into the pair n / 2 and  *)
(* the parity odd n, and the parity is the high half of the bit.  That is     *)
(* wconv, and the word is not touched -- it solves the member, and the member *)
(* has not changed.                                                          *)
(*                                                                            *)
(* FED THE LIST UNCONVERTED, the kernel goes off trying to reconcile two      *)
(* lists that do not match and does not come back.                            *)
Definition rowwits48 : seq (int * int * int * seq nat) :=
  Eval vm_compute in [seq wconv e8numi par8i t | t <- rowwits].

Lemma witsokC :
  witsok e8invi e4ofi par8i par4i (ptab memb2tab) rowwits48.
Proof. by vm_compute. Qed.

(* and the list as it comes, at the narrow place, which is what the fold      *)
(* marks into its own map                                                     *)
Lemma wits24C :
  wgood24 e8invi e4ofi par8i par4i (ptab memb2tab) rowwits.
Proof. by vm_compute. Qed.
