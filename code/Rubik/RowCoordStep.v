(* =========================================================================  *)
(*  RowCoordStep.v -- the four numbers of a moved position.                   *)
(* =========================================================================  *)

(* The corners (RowCoordOk) and the three groups of edges (RowCoordEdge) put  *)
(* together: moving the four numbers by the tables gives the four numbers of  *)
(* the moved position.                                                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Tabi Row RowMap RowCub RowCubi RowCubInst.
Require Import RowLeafFast RowCoord RowCoordOk RowCoordEdge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma cofy_step y k : (k < 18)%N -> ypstok y ->
  cstepx (cofy y) (of_nat k) = cofy (zstepi y (of_nat k)).
Proof.
move=> hk hy.
have e1 := corner_step hk hy.
have e2 := etup_step hk hy (or_introl erefl).
have e3 := etup_step hk hy (or_intror (or_introl erefl)).
have e4 := etup_step hk hy (or_intror (or_intror erefl)).
rewrite [cofy y]cofyE [cofy (zstepi _ _)]cofyE.
(* the step of a four-tuple is four table reads, one lemma each, put        *)
(* together by hand: a rewrite or congr searching the goal for a table read *)
(* unfolds the tables                                                        *)
exact: (f_equal2 pair (f_equal2 pair (f_equal2 pair e1 e2) e3) e4).
Qed.
