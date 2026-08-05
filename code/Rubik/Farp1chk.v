(* =========================================================================  *)
(*  Farp1chk.v                                                                *)
(*                                                                            *)
(*  Farp1inst's instantiation, type checked against p1dummy.                  *)
(*                                                                            *)
(*  NOT A RESULT: with the dummy table every distance is 0, so the searches   *)
(*  it hypothesises do not in fact return false.  What it checks is the       *)
(*  SHAPE -- that superflip_p1far is applied with the right arguments in the  *)
(*  right order, and that p1droot.+2 really is p1depth.                       *)
(*                                                                            *)
(*  It costs seconds and needs NO DATA, where Farp1inst needs the 4.5 GB      *)
(*  table and the eighteen search runs.  Closing a Section turns its          *)
(*  Variables and Hypotheses into explicit arguments in declaration order,    *)
(*  so a partial application binds them silently to the wrong slots -- this   *)
(*  file is what catches that before a build that costs hours.                *)
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
                                          (init3 (prefixi i j)) nfcube)
                    (iota 0 nroot))
      (iota 0 nmoves) ->
  ts_checkStep -> fsmoveC -> fsrC -> slrC ->
  superflip \notin ball Sset p1depth.
Proof.
move=> hsearch hts hfm hfr hsl.
exact: (@superflip_p1far p1dummy p1droot p1droot_small
                         (p1check0_dummy) (p1checkStep_dummy) hts
                         hfm hfr hsl hsearch).
Qed.
