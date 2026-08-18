(* =========================================================================  *)
(*  HAdmis.v -- obligation D: what the sweep has to give, and what it buys.   *)
(* =========================================================================  *)

(* The search prunes with the table: a branch is cut when the table says the  *)
(* position is further from solved than the depth left.  That is sound only   *)
(* if the table never says MORE than the truth -- if h of a coset never       *)
(* exceeds the distance of any position in it.                               *)
(*                                                                            *)
(* This file is the top of that: given the one property a sweep can check,    *)
(*                                                                            *)
(*   h g <= (h (g * m)).+1   for every position g and every quarter turn m    *)
(*                                                                            *)
(* a word of length n cannot reach anything the table scores above h 1 + n.   *)
(* With h 1 = 0 that is admissibility, and it is what the search needs.       *)
(*                                                                            *)
(* WHAT THE SWEEP IS.  h is a lookup through the coordinates and the fold,   *)
(* the property above is 2.9e10 cosets times twelve moves -- about twelve     *)
(* CPU-hours by the phase 1 scaling.  It is NOT written yet, and neither is   *)
(* the step from `the table as a function of cosets' to `h as a function of   *)
(* positions', which is obligation C.                                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Admis.

Variable h : {perm facelet} -> nat.

(* the one thing the sweep checks                                            *)
Hypothesis hstep : forall g m, (m < nq)%N -> (h g <= (h (g * qmv m)).+1)%N.

(* Read the word backwards: the last turn undone is one of the twelve too, so *)
(* each letter can cost the table at most one.                               *)
Lemma h_le_word (w : seq nat) : qw w -> (h (wp w) <= h 1 + seq.size w)%N.
Proof.
elim/last_ind: w => [_|w m ih]; first by rewrite wp_nil addn0.
rewrite -cats1 /qw all_cat => /andP[wq]; rewrite /= andbT => mL.
have qL : (qinv m < nq)%N by apply: qinv_lt.
have hE : wp (w ++ [:: m]) * qmv (qinv m) = wp w.
  by rewrite wp_cat wp_one -qmvV // -mulgA mulgV mulg1.
have := hstep (wp (w ++ [:: m])) qL; rewrite hE => hle.
apply: leq_trans hle _.
rewrite size_cat /= addn1 addnS ltnS.
by apply: ih.
Qed.

(* the same, as a statement about the ball the search works in               *)
Lemma h_le_ball n g : g \in ball Sq n -> (h g <= h 1 + n)%N.
Proof.
case/ball_wp => w [wq ws <-].
by apply: leq_trans (h_le_word wq) _; rewrite leq_add2l.
Qed.

End Admis.
