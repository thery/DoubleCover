(* =========================================================================  *)
(*  RowFoldLvlG.v -- the level that skips a write is the level.               *)
(* =========================================================================  *)

(* RowFold's flevelg is flevel with every write tested first: a word that    *)
(* already holds its value is not written, so no difference is made for it.  *)
(* Skipping such a write gives back an array equal to the one written, so    *)
(* the two levels give the same map, for every source and destination.       *)

From mathcomp Require Import all_ssreflect.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Row RowMap RowFold.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* ---- a walk, and a write that is skipped ---------------------------------- *)

(* two walks whose steps agree everywhere are the same walk                  *)
Lemma ifold_ext (A : Type) n x (f g : int -> A -> A) a :
  (forall k b, f k b = g k b) -> ifold n x f a = ifold n x g a.
Proof.
move=> hfg; elim: n x a => [|n ih] x a; first by [].
by rewrite /= hfg ih.
Qed.

(* writing a word what it holds leaves the array as it was, in range or not  *)
Lemma set_getI (t : arr) (i : int) : PArray.set t i (PArray.get t i) = t.
Proof.
apply: PArray.array_ext.
- exact: (@PArray.length_set int t i (PArray.get t i)).
- move=> j hj; have [hij|hij] := boolP (i =? j).
    have hije : i = j by apply: to_nat_inj; apply/neqbP.
    rewrite -hije in hj *.
    rewrite (@PArray.length_set int t i (PArray.get t i)) in hj.
    by rewrite get_setE.
  have hne : i <> j by move=> he; move: hij; rewrite he; case: neqbP.
  by rewrite get_set_otherE.
- exact: (@PArray.default_set int t i (PArray.get t i)).
Qed.

(* a write skipped when the word already holds its value is the write        *)
Lemma set_skipE (b : arr) (j v : int) :
  (if Uint63.eqb (PArray.get b j) v then b else PArray.set b j v)
  = PArray.set b j v.
Proof.
case: ifP => h; last by [].
by rewrite -(eqb_correct _ _ h) set_getI.
Qed.

(* ---- the level, piece by piece -------------------------------------------- *)

Section LvlG.

Variables fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi : arr.

(* one half of a cell, moved                                                  *)
Lemma flevmvhE mgr' fsgr' v dh doff glo ghi ub kb k sw b :
  flevmvh fslo fshi mlo mhi mgr' fsgr' v dh doff glo ghi ub kb k sw b
  = flevmvu fslo fshi mlo mhi mgr' fsgr' v dh doff glo ghi ub kb k sw b.
Proof.
rewrite /flevmvh /flevmvu; cbv zeta.
rewrite !set_skipE.
reflexivity.
Qed.

(* one move of H over a kept page                                             *)
Lemma flevmvgE src r k doff a :
  flevmvg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r k doff a
  = flevmv fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r k doff a.
Proof.
rewrite /flevmvg /flevmv; cbv zeta.
apply: ifold_ext => g b.
rewrite !flevmvhE.
reflexivity.
Qed.

(* the carry, a word at a time                                                *)
Lemma carryE doff (sa a : arr) :
  ifold ngroupn 0
    (fun g b =>
       if Uint63.eqb (PArray.get b (Uint63.add doff g))
                     (PArray.get sa (Uint63.add doff g))
       then b
       else PArray.set b (Uint63.add doff g) (PArray.get sa (Uint63.add doff g)))
    a
  = ifold ngroupn 0
      (fun g b =>
         PArray.set b (Uint63.add doff g) (PArray.get sa (Uint63.add doff g)))
      a.
Proof. by apply: ifold_ext => g b; rewrite set_skipE. Qed.

(* the ten moves over a kept page                                             *)
Lemma movesE src r doff a :
  ifold nhn 0
    (fun k b =>
       flevmvg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r k doff b) a
  = ifold nhn 0
      (fun k b =>
         flevmv fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r k doff b)
      a.
Proof. by apply: ifold_ext => k b; rewrite flevmvgE. Qed.

(* one kept page                                                              *)
Lemma flevpggE src r d :
  flevpgg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r d
  = flevpg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src r d.
Proof.
rewrite /flevpgg /flevpg; cbv zeta.
rewrite carryE movesE.
reflexivity.
Qed.

(* THE LEVEL: the one that skips is the one that writes                      *)
Lemma flevelgE src dst :
  flevelg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src dst
  = flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi src dst.
Proof.
rewrite /flevelg /flevel.
by apply: ifold_ext => r d; rewrite flevpggE.
Qed.

(* and n levels                                                               *)
Lemma flevngE n m d :
  flevng fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi n m d
  = flevn fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi n m d.
Proof.
elim: n m d => [|n ih] m d; first by [].
(* one step of each, NOT by `/=': simpl walks ifold nrepn in unary          *)
have eg : flevng fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi n.+1 m d
  = flevng fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi n
      (flevelg fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi m d) m.
  reflexivity.
have ep : flevn fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi n.+1 m d
  = flevn fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi n
      (flevel fsrc fsrc2 fful fsgr fslo fshi mgr msw mlo mhi m d) m.
  reflexivity.
by rewrite eg ep flevelgE ih.
Qed.

End LvlG.
