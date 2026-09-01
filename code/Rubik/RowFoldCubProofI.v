(* =========================================================================  *)
(*  RowFoldCubProofI.v -- the int run answers the same boolean.               *)
(* =========================================================================  *)

(* rowmapi is rowmap: RowFoldSrchIP proves the two searches equal.  So the    *)
(* certificate is RowFoldCubProof's, unchanged, and nothing about the cube    *)
(* is proved twice.                                                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row RowMap RowFold.
Require Import RowFoldSrch RowFoldSrchI RowFoldSrchIP.
Require Import RowFoldCubDef RowFoldCubDefI RowFoldCubProof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma rowmapiE : rowmapi 20 = rowmap 20.
Proof. by apply: frunski_eq. Qed.

Lemma rowfulliEq : rowfulli = rowfull.
Proof. by rewrite /rowfulli /rowfull /ycwitsoi /ycwitso rowmapiE. Qed.

Theorem row_of_runi : rowfulli = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof. by rewrite rowfulliEq; exact: row_of_run. Qed.

Corollary row_of_runi_superflip : rowfulli = true ->
  forall m, m \in H -> superflip * m \in ball Sset 20.
Proof. by rewrite rowfulliEq; exact: row_of_run_superflip. Qed.
