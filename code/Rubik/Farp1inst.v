(* =========================================================================  *)
(*  Farp1inst.v -- Farp1main at the real table and the eighteen real          *)
(*     searches.                                                              *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Farp1main P1TsChk P1FTable Runp1 FsmChk FsrChk SlrChk
        FoldAtTable.
Require Import Runp1_03 Runp1_04 Runp1_05 Runp1_06 Runp1_07 Runp1_08.
Require Import Runp1_09a Runp1_09b Runp1_10 Runp1_11a Runp1_11b Runp1_12.
Require Import Runp1_13 Runp1_14 Runp1_15 Runp1_16 Runp1_17.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* all over jsnd is a fifteen fold conjunction, but it has to be unfolded
   with f ABSTRACT.  Unfolding it on the goal itself puts /= next to a term
   holding a searchz3, and simpl then starts unfolding the search rather than
   the all, which does not come back.

   Stated here rather than imported: the only other copy sat above the
   search runs.                                                               *)
Lemma all_jsndp1 (f : nat -> bool) :
  f 3%N -> f 4%N -> f 5%N -> f 6%N -> f 7%N -> f 8%N -> f 9%N -> f 10%N ->
  f 11%N -> f 12%N -> f 13%N -> f 14%N -> f 15%N -> f 16%N -> f 17%N ->
  all f jsnd.
Proof.
move=> h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15 h16 h17.
by rewrite /jsnd /= h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14
           h15 h16 h17.
Qed.

(* and the two root moves of a piece, split for the two that set the
   makespan.  Same reason for the abstract f.                                 *)
Lemma all_rootp1 (f : nat -> bool) : f 0%N -> f 1%N -> all f (iota 0 nroot).
Proof. by move=> h0 h1; rewrite /= h0 h1. Qed.

Lemma p1searchd :
  all (fun j => all (fun i => ~~ searchz3 p1ftab p1droot (prefixi i j)
                                          (init3 (prefixi i j)) (fcpos j))
                    (iota 0 nroot))
      jsnd.
Proof.
by apply: all_jsndp1;
   [exact: p1searchd_03 | exact: p1searchd_04 | exact: p1searchd_05 |
    exact: p1searchd_06 | exact: p1searchd_07 | exact: p1searchd_08 |
    apply: all_rootp1; [exact: p1searchd_09a | exact: p1searchd_09b] |
    exact: p1searchd_10 |
    apply: all_rootp1; [exact: p1searchd_11a | exact: p1searchd_11b] |
    exact: p1searchd_12 | exact: p1searchd_13 | exact: p1searchd_14 |
    exact: p1searchd_15 | exact: p1searchd_16 | exact: p1searchd_17].
Qed.

(* HOISTED, and not proved inside the theorem: there the context holds
   p1checkStep, fsmoveC, fsrC and slrC, and a trailing `done' then unifies
   its goal against one of them and unfolds an all_pow at ncoord = 24.  Even
   `12 <= 63' stops returning.                                                *)
Lemma p1droot_small : (p1droot <= 63)%N.
Proof. by []. Qed.

(* THE THEOREM, with the certificates that are still computations left
   standing in its type.  Discharging them is what remains: fsmoveCP, fsrCP
   and slrCP are stated in Farp1.v and admitted there, and p1check0 and
   p1checkStep have to be run on the emitted table.                           *)
(* NO HYPOTHESES.  Every one of the six computations has its own file and
   its own Qed: FoldAtTable for the phase 1 table, P1TsChk for the twist x slice
   one, FsmChk, FsrChk and SlrChk for the three move and distance tables.
   Print Assumptions shows only the int63 and PArray primitives.

   THE PHASE 1 CERTIFICATE COMES FROM THE FOLD.  FoldAtTable checks the 64 430
   orbit representatives, in place of a sweep over all 1 013 760 ranks.       *)
Theorem superflip_p1far_real : superflip \notin ball Sset p1depth.
Proof.
(* every argument pinned: closing a Section turns its Variables and
   Hypotheses into EXPLICIT arguments, in declaration order, so a partial
   application silently binds p1ftab to the wrong slot.                       *)
exact: (@superflip_p1far p1ftab p1droot p1droot_small p1check0P
                         (p1checkStepr_ok fsmoveCP p1checkSteprP)
                         ts_checkStepP fsmoveCP fsrCP slrCP p1searchd).
Qed.
