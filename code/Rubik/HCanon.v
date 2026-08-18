(* =========================================================================  *)
(*  HCanon.v -- obligation B: the search's rule loses no maneuver.            *)
(* =========================================================================  *)

(* WHAT IS OWED.  HBound.targ_far takes this as a hypothesis:                 *)
(*                                                                            *)
(*   forall v, qw v -> exists v', [/\ qw v', wp v' = wp v,                    *)
(*                                  size v' <= size v & okw 0 v']             *)
(*                                                                            *)
(* -- every element a word reaches is reached by a word the rule accepts, no  *)
(* longer.  Searchr.v IS this theorem, abstractly, for a group with a face    *)
(* structure, and it is proved there: reduce_word, ball_reduced, ball_searchr.*)
(* It does not instantiate here because of one hypothesis:                    *)
(*                                                                            *)
(*   fc_close : m1 * m2 = 1 \/ exists m3 in S, fc m3 = fc m1 /\ m1 * m2 = m3  *)
(*                                                                            *)
(* which says two turns of a face collapse into one turn OF THE SET.  For the *)
(* eighteen moves U * U = U2 is in the set; for the twelve quarter turns it is*)
(* not, which is exactly why the quarter-turn rule allows U U and forbids only*)
(* the third.  So B is Searchr.v generalised: two may stand, three collapse.  *)
(*                                                                            *)
(* This file has the parts of that which are specific to the quarter turns and*)
(* cheap: the three rewrites and the measure that makes them terminate.  The  *)
(* generalisation of Searchr.v itself is not here.                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Moves Coordfs Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the three rewrites -------------------------------------------------  *)

(* Two of them are already proved, for any target, in HProp2: man_cancel takes*)
(* out a turn and its inverse, and qmv_cube turns three of a face into one.   *)
(* The third is the swap of two opposite faces, and that is here.             *)

Definition fce (m : nat) : nat := (m %/ 2)%N.

Definition oppq (a b : nat) : bool := (fce b == (fce a + 3) %% 6)%N.

Lemma comm_opp_tab :
  all (fun a => all (fun b => oppq a b ==>
         (comp_tab (mvt a) (mvt b) == comp_tab (mvt b) (mvt a))) (iota 0 nq))
      (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma qmv_comm_opp a b : (a < nq)%N -> (b < nq)%N -> oppq a b ->
  qmv a * qmv b = qmv b * qmv a.
Proof.
move=> aL bL ab.
have /implyP/(_ ab)/eqP h :=
  allP (allP comm_opp_tab _ (mem_iota0 aL)) _ (mem_iota0 bL).
by rewrite !qmvE // !ptM ?mvt_ok //; congr pt.
Qed.

Lemma man_swap (a b : nat) (u v : seq nat) (g : {perm facelet}) :
  (a < nq)%N -> (b < nq)%N -> oppq a b ->
  wp (u ++ a :: b :: v) = g -> wp (u ++ b :: a :: v) = g.
Proof. by move=> aL bL ab; rewrite !wp_pair qmv_comm_opp. Qed.

(* ---- the measure --------------------------------------------------------  *)

(* A cancel and a collapse make the word shorter; a swap does not, so on its  *)
(* own it could go round for ever.  What stops it: of two opposite faces the  *)
(* rule keeps the larger index first, and every swap moves one such pair the  *)
(* right way round.  phi counts the pairs still the wrong way round, and      *)
(* size + phi falls at every rewrite -- the shortenings cannot raise phi,     *)
(* since taking letters out only takes pairs out.                             *)

Definition ohi (a b : nat) : bool := oppq a b && (fce a < fce b)%N.

Fixpoint phi (w : seq nat) : nat :=
  if w is m :: w' then (count (ohi m) w' + phi w')%N else 0%N.

Lemma phi_cat (u s : seq nat) :
  phi (u ++ s) = (phi u + sumn [seq count (ohi m) s | m <- u] + phi s)%N.
Proof.
elim: u => [|m u ih] /=; first by rewrite add0n.
rewrite count_cat ih !addnA.
by rewrite [(count (ohi m) u + count (ohi m) s + phi u)%N]addnAC.
Qed.

(* phi_swap -- that a swap of an opposite pair drops phi by exactly one -- is
   the next step and the reason the measure works: the pairs other than the
   swapped one are untouched, since the two letters only trade places between
   the same neighbours.  It goes through interactively and is not in the file
   yet; the arithmetic shape at the end needs one more look.                 *)

(* ---- what is left -------------------------------------------------------  *)

(* With the three rewrites and this measure, the shape of the argument is     *)
(* Searchr.v's: while the word breaks the rule somewhere, rewrite there; the  *)
(* measure falls, so it stops; and it stops at a word the rule accepts.  Two  *)
(* pieces are missing:                                                        *)
(*                                                                            *)
(*   the analysis of a violation -- from ~~ okw 0 w, produce the place and    *)
(*     which of the three rewrites applies, which needs the class to be read  *)
(*     back as `the last turn and how long its run is';                       *)
(*   the induction on size + phi.                                             *)
(*                                                                            *)
(* Doing it by generalising Searchr.v rather than here is the better route:   *)
(* its inv/nosame/reduce machinery is this argument already, and only the     *)
(* merge case changes.                                                        *)
