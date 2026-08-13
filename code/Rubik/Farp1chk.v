(* =========================================================================  *)
(*  Farp1chk.v -- Farp1inst's instantiation, type checked against p1dummy.    *)
(* =========================================================================  *)
From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1
        Farp1main Runp1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GroupScope.

Lemma p1droot_small : (p1droot <= 63)%N.
Proof. by []. Qed.

Theorem superflip_p1far_dummy :
  all (fun j => all (fun i => ~~ searchz3 p1dummy p1droot (prefixi i j)
                                          (init3 (prefixi i j)) (fcpos j))
                    (iota 0 nroot))
      jsnd ->
  ts_checkStep -> fsmoveC -> fsrC -> slrC ->
  superflip \notin ball Sset p1depth.
Proof.
move=> hsearch hts hfm hfr hsl.
exact: (@superflip_p1far p1dummy p1droot p1droot_small
                         (p1check0_dummy) (p1checkStep_dummy) hts
                         hfm hfr hsl hsearch).
Qed.

(* THE SAME, THROUGH THE FOLD.  Farp1inst no longer passes a p1checkStep
   proved over the ranks: it passes p1checkStepr_ok applied to the orbit
   certificate.  That is one more argument position to get wrong, and the
   dummy catches it here in seconds rather than after the searches.           *)
Theorem superflip_p1far_dummy_folded :
  all (fun j => all (fun i => ~~ searchz3 p1dummy p1droot (prefixi i j)
                                          (init3 (prefixi i j)) (fcpos j))
                    (iota 0 nroot))
      jsnd ->
  p1check0 p1dummy -> p1checkStepr p1dummy ->
  ts_checkStep -> fsmoveC -> fsrC -> slrC ->
  superflip \notin ball Sset p1depth.
Proof.
move=> hsearch h0 hstepr hts hfm hfr hsl.
exact: (@superflip_p1far p1dummy p1droot p1droot_small h0
                         (p1checkStepr_ok hfm hstepr) hts
                         hfm hfr hsl hsearch).
Qed.
