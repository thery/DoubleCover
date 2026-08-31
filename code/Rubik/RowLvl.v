(* =========================================================================  *)
(*  RowLvl.v -- the prepass, reading the move's groups by one addition.       *)
(* =========================================================================  *)

(* RowMap's prepass reads the move's new group as mgr[gr * 10 + k]: a         *)
(* multiply and an add for every word of the map, 813 million words a move,   *)
(* ten moves a level.  rubik_row_nofold.ml does not: it copies the move's     *)
(* whole column into a flat array once, and the inner loop is one indexed     *)
(* read.                                                                      *)
(*                                                                            *)
(* THE COLUMN IS NOT BUILT AT RUN TIME HERE.  It is the same table            *)
(* transposed -- mgrT[k * 20160 + gr] -- so the instance builds it once and   *)
(* checks it once, and the loop reads mgrT[base + gr] with base fixed for the *)
(* move.  One addition a word.                                                *)
(*                                                                            *)
(* NOTHING NEW IS PROVED ABOUT THE CUBE.  The new prepass is shown EQUAL to   *)
(* RowMap's, so RowRun.prepass_sound carries straight over.                   *)
(*                                                                            *)
(* A file of its own because RowMap is read by the folded run.                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap RowRun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- two walks that take the same step are the same walk ----------------- *)

Lemma ifold_eqg (A : Type) n j (f g : int -> A -> A) a :
  (j + n <= nwB)%N ->
  (forall k b, (to_nat k < j + n)%N -> f k b = g k b) ->
  ifold n (advn j 0) f a = ifold n (advn j 0) g a.
Proof.
elim: n j a => [|n ih] j a hb hf //=.
have -> : Uint63.add (advn j 0) 1 = advn j.+1 0 by rewrite advnS.
have hj : (to_nat (advn j 0) < j + n.+1)%N.
  rewrite to_nat_advn0; first by rewrite addnS ltnS leq_addr.
  by apply: leq_trans hb; rewrite addnS ltnS leq_addr.
rewrite hf //; apply: ih; first by rewrite addSnnS.
by move=> k b hk; apply: hf; rewrite -addSnnS.
Qed.

Lemma ifold_eqi (A : Type) n (f g : int -> A -> A) a :
  (n <= nwB)%N ->
  (forall k b, (to_nat k < n)%N -> f k b = g k b) ->
  ifold n 0 f a = ifold n 0 g a.
Proof. by move=> hb hf; apply: (@ifold_eqg _ n 0). Qed.

Section Lvl.

(* ---- the ten moves of H, as RowMap reads them ---------------------------- *)

Variable mpg mgr msw mlo mhi : arr.

Local Notation pgm := (pgmv mpg).
Local Notation grm := (grmv mgr).
Local Notation grpm := (grpmv msw mlo mhi).

(* ---- and the same group table, transposed -------------------------------- *)

(* mgrT[k * 20160 + gr] is what mgr[gr * 10 + k] is.  The instance builds it  *)
(* and checks it; nothing here says where it comes from.                      *)
Variable mgrT : arr.

Definition grmT (base gr : int) : int := PArray.get mgrT (Uint63.add base gr).

Hypothesis mgrT_ok : forall k gr, (to_nat k < nhn)%N ->
  (to_nat gr < ngroupn)%N ->
  grmT (Uint63.mul k ngroupi) gr = grm k gr.

(* ---- one move over the whole map, the base fixed for the move ------------ *)

Definition prepmvT (k : int) (src : rmap) (dst : rmap) : rmap :=
  let base := Uint63.mul k ngroupi in
  ifold npagen 0
    (fun pg d =>
       let pg' := pgm k pg in
       ifold ngroupn 0
         (fun gr d' =>
            let v := gget src (grpof pg gr) in
            if Uint63.eqb v 0 then d'
            else gor d' (grpof pg' (grmT base gr)) (grpm k v))
         d)
    dst.

Definition prepmv0T (k : int) (src : rmap) (dst : rmap) : rmap :=
  let base := Uint63.mul k ngroupi in
  ifold npagen 0
    (fun pg d =>
       let pg' := pgm k pg in
       ifold ngroupn 0
         (fun gr d' =>
            let g := grpof pg gr in
            let v := gget src g in
            if Uint63.eqb v 0 then d'
            else gor (gor d' g v) (grpof pg' (grmT base gr)) (grpm k v))
         d)
    dst.

Definition prepassT (src dst : rmap) : rmap :=
  ifold nhn 0
    (fun k d => if Uint63.eqb k 0 then prepmv0T k src d else prepmvT k src d)
    dst.

(* ---- and it is RowMap's prepass ------------------------------------------ *)

Lemma prepmvT_eq k src dst : (to_nat k < nhn)%N ->
  prepmvT k src dst = prepmv mpg mgr msw mlo mhi k src dst.
Proof.
move=> hk; rewrite /prepmvT /prepmv; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: npagen_nwB.
move=> pg d _; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: ngroupn_nwB.
by move=> gr d' hgr; rewrite mgrT_ok.
Qed.

Lemma prepmv0T_eq k src dst : (to_nat k < nhn)%N ->
  prepmv0T k src dst = prepmv0 mpg mgr msw mlo mhi k src dst.
Proof.
move=> hk; rewrite /prepmv0T /prepmv0; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: npagen_nwB.
move=> pg d _; cbv zeta.
apply: ifold_eqi; first by apply: ltnW; exact: ngroupn_nwB.
by move=> gr d' hgr; rewrite mgrT_ok.
Qed.

Lemma prepassT_eq src dst :
  prepassT src dst = prepass mpg mgr msw mlo mhi src dst.
Proof.
rewrite /prepassT /prepass.
apply: ifold_eqi; first by apply: ltnW; apply: (@ltn_nwB 4).
(* NOT `case: ifP'.  The two branches are whole prepasses and ifP reduces    *)
(* them: the stack overflows.  A plain case on the boolean only splits.      *)
move=> k d hk; case: (Uint63.eqb k 0).
  by rewrite prepmv0T_eq.
by rewrite prepmvT_eq.
Qed.

End Lvl.
