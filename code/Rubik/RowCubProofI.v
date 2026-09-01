(* =========================================================================  *)
(*  RowCubProofI.v -- the int run answers the same boolean.                   *)
(* =========================================================================  *)

(* rowmappi is rowmapp: RowSrchP proves the two searches equal and            *)
(* RowCubInst carries that to the run.  So the certificate is RowCubProof's,  *)
(* unchanged, and nothing about the cube is proved twice.                     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row RowMap.
Require Import RowCubDef RowCubInst RowCubProof.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma rowmappiE : rowmappi 20 = rowmapp 20.
Proof. by apply: ymfinskiE. Qed.

Lemma rowfullpiEq : rowfullpi = rowfullp.
Proof. by rewrite /rowfullpi /rowfullp /rowwitspi /rowwitsp rowmappiE. Qed.

Theorem row_of_runpi : rowfullpi = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof. by rewrite rowfullpiEq; exact: row_of_runp. Qed.

Corollary row_of_runpi_superflip : rowfullpi = true ->
  forall m, m \in H -> superflip * m \in ball Sset 20.
Proof. by rewrite rowfullpiEq; exact: row_of_runp_superflip. Qed.
