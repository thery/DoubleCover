(* =========================================================================  *)
(*  RowDummy.v -- the instance run on a dummy table, to see it close.         *)
(* =========================================================================  *)

(* THIS FILE PROVES NOTHING ABOUT THE CUBE and is not meant to.  Every table  *)
(* here is one entry of nought, so none of the checks holds: e8ok, e4ok and   *)
(* the two about the bits are ADMITTED, and so are the two the run and the    *)
(* witnesses would have to compute.  What it settles is that the instance     *)
(* closes -- that the things an instance supplies really do determine the     *)
(* theorem, with nothing left dangling and no shape mismatched.               *)
(*                                                                            *)
(* When the real tables arrive they take the place of the dummies here and    *)
(* the four checks become vm_computes.  Nothing else in the file changes.     *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the dummies --------------------------------------------------------- *)

Definition d1 : arr := PArray.make 1%uint63 0%uint63.
Definition dm : PArray.array arr := PArray.make 1%uint63 d1.

Definition dmemb (x : memb) : seq nat := id_tab flast.
Definition dtomemb (x : pstt) : memb := (0%uint63, 0%uint63, 0%uint63).
Definition dstep (a b : int) : int := 0%uint63.
Definition dokmv (a b : int) : bool := true.

Definition dsrch : nat := 16.
Definition dwl : seq (int * int * int * seq nat) := [::].

Definition dfin : rmap :=
  mfin d1 d1 d1 d1 d1 d1 d1 dm dstep dtomemb dokmv dsrch 20.

(* ---- what a dummy cannot do ---------------------------------------------- *)

(* The four checks.  On the real tables each is one walk and one vm_compute;  *)
(* on a dummy each is false, so each is admitted here and nowhere else.       *)

Lemma d_e8ok : e8ok d1 d1 d1.
Proof. Admitted.

Lemma d_e4ok : e4ok d1 d1 d1.
Proof. Admitted.

Lemma d_srcok : srcok d1 d1.
Proof. Admitted.

Lemma d_halfok : halfok d1 d1 d1 d1.
Proof. Admitted.

(* the member's table is a permutation of the forty eight facelets            *)
Lemma d_memb2tab_ok x : tab_ok flast (dmemb x).
Proof. Admitted.

(* ---- and the five the tables would settle -------------------------------- *)

(* What a leaf is, what the fs step table does, and what the prepass tables   *)
(* do.  On the real tables the first is a certificate the lower bound has     *)
(* already run and the others are the cubie to facelet bridge; on a dummy     *)
(* none of them holds.                                                        *)

Lemma d_fsstepP x k : (to_nat k < RowRun.nmvn)%N -> pstok x ->
  dstep (fsidx (coordi x)) k = fsidx (coordi (xstep x k)).
Proof. Admitted.

Lemma d_leaf_memb c x : coordP c x -> pstok x ->
  wdist (p1get dm c) = 0%uint63 -> membok d1 d1 (dtomemb x).
Proof. Admitted.

Lemma d_tomemb_tab c x : coordP c x -> pstok x ->
  wdist (p1get dm c) = 0%uint63 ->
  pt flast (dmemb (dtomemb x)) = pt flast (ti2t flast x).
Proof. Admitted.

Lemma d_pgok : pgok d1.
Proof. Admitted.

Lemma d_grok : grok d1.
Proof. Admitted.

Lemma d_btok : btok d1.
Proof. Admitted.

Lemma d_memb2tab_move k pg gr bt : (to_nat k < nhn)%N -> inrange pg gr bt ->
  pt flast (dmemb (unplace d1 d1 d1 d1
                     (pgmv d1 k pg) (grmv d1 k gr) (btmv d1 k bt)))
  = pt flast (dmemb (unplace d1 d1 d1 d1 pg gr bt)) * hmv k.
Proof. Admitted.

(* and the two the computation would settle: the witnesses do what they say,  *)
(* and the map and they together leave no bit clear                           *)
Lemma d_witsok : witsok d1 d1 d1 d1 (ptab dmemb) dwl.
Proof. Admitted.

Lemma d_full : mfull (mor dfin (wmap dwl)).
Proof. Admitted.

(* ---- and the row ----------------------------------------------------------*)

Theorem dummy_row_within_20 x :
  membok d1 d1 x -> wthn (RowFinal.pos (ptab dmemb)) 20 x.
Proof.
apply: (row_within_20_inst d_e8ok d_e4ok d_memb2tab_ok d_srcok d_halfok
                           d_fsstepP d_leaf_memb d_tomemb_tab
                           d_pgok d_grok d_btok d_memb2tab_move
                           (erefl 20%N) d_witsok d_full).
Qed.
