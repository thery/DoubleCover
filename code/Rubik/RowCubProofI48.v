(* =========================================================================  *)
(*  RowCubProofI48.v -- the int run answers the same boolean.                 *)
(* =========================================================================  *)

(* rowmappi48 is rowmapp48: RowSrchP48 proves the two searches equal and     *)
(* RowCubInst48 carries that to the run.  So the certificate is              *)
(* RowCubProof48's, unchanged, and nothing about the cube is proved twice.   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
Require Import Rubik333 Ball Diameter Moves Row RowMap.
Require Import Row48 RowMap48 RowRun48 RowCubInst48 RowCubDef48 RowCubProof48.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma rowmappiE48 : rowmappi48 20 = rowmapp48 20.
Proof. by apply: ymfinskiE. Qed.

Lemma rowfullpiEq48 : rowfullpi48 = rowfullp48.
Proof.
by rewrite /rowfullpi48 /rowfullp48 /rowwitspi48 /rowwitsp48 rowmappiE48.
Qed.

Theorem row_of_runpi48 : rowfullpi48 = true ->
  forall h, h \in H -> superflip^-1 * h \in ball Sset 20.
Proof. by rewrite rowfullpiEq48; exact: row_of_runp48. Qed.

Corollary row_of_runpi48_superflip : rowfullpi48 = true ->
  forall m, m \in H -> superflip * m \in ball Sset 20.
Proof. by rewrite rowfullpiEq48; exact: row_of_runp48_superflip. Qed.
