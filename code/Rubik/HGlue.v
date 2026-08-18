(* =========================================================================  *)
(*  HGlue.v -- what C has to give D and E, in the shape they take it.        *)
(* =========================================================================  *)

(* HRunS.hsearch_complete asks for a pok and a stt: the positions the search  *)
(* meets, and the triples it carries.  This file fixes what those are, so     *)
(* that what obligation C still owes is a statement and not a guess.         *)
(*                                                                            *)
(* THE THREE AXES ARE CONJUGATIONS, and that is what makes stt a function of  *)
(* the position at all.  A viewing angle relabels the faces, so the position  *)
(* seen along it is the position conjugated by a rotation -- and the rotation *)
(* is in sym48, at 23, 26 and 39, which is a computation.  Conjugation is a   *)
(* homomorphism, so a turn seen along an axis is that axis's turn, which is   *)
(* exactly the cmv the search steps with.                                     *)
(*                                                                            *)
(* Without this the interface would not fit: rooti_ax replays a relabelled    *)
(* word from the identity, and a state built that way is not a function of    *)
(* the position, which is what hsearch_complete needs.                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Coordfsi
        Phase1 HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound
        HEdge HRunS.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the rotation of each axis ------------------------------------------- *)

(* which of the forty eight symmetries turns the cube onto each axis          *)
Definition axsel : seq nat := [:: 23; 26; 39]%N.

Definition axtab (i : nat) : seq nat := nth [::] sym48 (nth 0%N axsel i).

(* THE COMPUTATION THAT SETTLES THE SHAPE: conjugating a turn by the axis's   *)
(* rotation gives that axis's turn, for all three axes and all twelve turns.  *)
Lemma axtab_cmv :
  all (fun i => all (fun m => conjt (axtab i) (mvt m) == mvt (cmv i m))
                    (iota 0 nq)) (iota 0 nax).
Proof. by vm_compute. Qed.

Lemma axtab_ok : all (fun i => tab_ok flast (axtab i)) (iota 0 nax).
Proof. by vm_compute. Qed.

(* ---- what is owed, and to whom ------------------------------------------- *)

(* With the rotations in hand the two sides fit together like this.           *)
(*                                                                            *)
(*   pok a  is  tabi_ok flast a && cubti a -- well formed, and keeping the    *)
(*     two facelets of an edge together.  HRunS.pok_step is HEdge.cubt_step,  *)
(*     which is proved.                                                       *)
(*   stt a  is  the triple of a along each axis, the axis view being the      *)
(*     conjugation by axtab i.                                               *)
(*                                                                            *)
(* Then hsearch_complete's four hypotheses come to:                           *)
(*                                                                            *)
(*   stt_step -- htriple (view i a * m) = stepa (htriple (view i a)) (cmv i m)*)
(*     which is axtab_cmv above and OBLIGATION C, once per coordinate.  The   *)
(*     edge half of C is HEdge.eslot_step and its sweep, which HEdgeChk runs; *)
(*     the corners are the same argument twice more.                          *)
(*   stt_sol -- the solved position has the solved triple, one lookup.        *)
(*   stt_cut -- HAdmis.h_cut with h the table read through the coordinates,   *)
(*     over HSweep.admis, which is proved.  That is obligation D, and what it *)
(*     needs of C is stt_step again.                                          *)
(*   pok_step -- HEdge.cubt_step, proved.                                     *)
(*                                                                            *)
(* So C is the only thing owed, and it is owed once: stt_step.                *)
