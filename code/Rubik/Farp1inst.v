(* =========================================================================  *)
(*  Farp1inst.v                                                               *)
(*                                                                            *)
(*  Farp1main at the real table and the eighteen real searches.               *)
(*                                                                            *)
(*  THE ONLY FILE IN THE PHASE 1 DEVELOPMENT THAT NEEDS THE DATA.  Everything *)
(*  above it -- Farp1.v and Farp1main.v -- is abstract over the table, so the *)
(*  proofs check without the 4.5 GB of chunks and without the eighteen search *)
(*  runs.  Build this one last.                                               *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Farp1main P1TsChk P1Table Runp1.
Require Import Runp1_00 Runp1_01 Runp1_02 Runp1_03 Runp1_04 Runp1_05.
Require Import Runp1_06 Runp1_07 Runp1_08 Runp1_09 Runp1_10 Runp1_11.
Require Import Runp1_12 Runp1_13 Runp1_14 Runp1_15 Runp1_16 Runp1_17.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* all over iota 0 18 is an eighteen fold conjunction, but it has to be
   unfolded with f ABSTRACT.  Unfolding it on the goal itself puts /= next to
   a term holding a searchz3, and simpl then starts unfolding the search
   rather than the all, which does not come back.

   COPIED from Farmain.v rather than imported: Farmain requires Far_00 ..
   Far_17, and each of those is a 65 hour depth 15 run of the OLD five view
   search.  Importing it for one three line lemma would make this file
   unbuildable. *)
Lemma all_iota18p1 (f : nat -> bool) :
  f 0%N -> f 1%N -> f 2%N -> f 3%N -> f 4%N -> f 5%N -> f 6%N -> f 7%N ->
  f 8%N -> f 9%N -> f 10%N -> f 11%N -> f 12%N -> f 13%N -> f 14%N ->
  f 15%N -> f 16%N -> f 17%N -> all f (iota 0 18).
Proof.
move=> h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15 h16 h17.
by rewrite /= h00 h01 h02 h03 h04 h05 h06 h07 h08 h09 h10 h11 h12 h13 h14 h15
           h16 h17.
Qed.

Lemma p1searchd :
  all (fun j => all (fun i => ~~ searchz3 p1tab p1droot (prefixi i j)
                                          (init3 (prefixi i j)) nfcube)
                    (iota 0 nroot))
      (iota 0 nmoves).
Proof.
by apply: all_iota18p1;
   [exact: p1searchd_00 | exact: p1searchd_01 | exact: p1searchd_02 |
    exact: p1searchd_03 | exact: p1searchd_04 | exact: p1searchd_05 |
    exact: p1searchd_06 | exact: p1searchd_07 | exact: p1searchd_08 |
    exact: p1searchd_09 | exact: p1searchd_10 | exact: p1searchd_11 |
    exact: p1searchd_12 | exact: p1searchd_13 | exact: p1searchd_14 |
    exact: p1searchd_15 | exact: p1searchd_16 | exact: p1searchd_17].
Qed.

(* HOISTED, and not proved inside the theorem: there the context holds
   p1checkStep, fsmoveC, fsrC and slrC, and a trailing `done' then unifies
   its goal against one of them and unfolds an all_pow at ncoord = 24.  Even
   `12 <= 63' stops returning. *)
Lemma p1droot_small : (p1droot <= 63)%N.
Proof. by []. Qed.

(* THE THEOREM, with the certificates that are still computations left
   standing in its type.  Discharging them is what remains: fsmoveCP, fsrCP
   and slrCP are stated in Farp1.v and admitted there, and p1check0 and
   p1checkStep have to be run on the emitted table. *)
Theorem superflip_p1far_real :
  p1check0 p1tab -> p1checkStep p1tab ->
  fsmoveC -> fsrC -> slrC ->
  superflip \notin ball Sset p1depth.
Proof.
move=> hc0 hcS hfm hfr hsl.
(* every argument pinned: closing a Section turns its Variables and
   Hypotheses into EXPLICIT arguments, in declaration order, so a partial
   application silently binds p1tab to the wrong slot. *)
exact: (@superflip_p1far p1tab p1droot p1droot_small hc0 hcS ts_checkStepP
                         hfm hfr hsl p1searchd).
Qed.
