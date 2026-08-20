(* =========================================================================  *)
(*  RowMap.v -- the map of a row, and the prepass.                            *)
(* =========================================================================  *)

(* A GROUP is twenty four bits and fits in one word, so the map is one word a *)
(* group: 40320 * 20160 words, 6.5 GB.  PArray.max_length is 4 194 303, so it *)
(* is cut into chunks of two million, the shape the folded tables already use.*)
(*                                                                            *)
(* THE PREPASS is one move of H played on the whole map at once.  A page goes *)
(* to a page, a group to a group, and the twenty four bits of a group are     *)
(* rearranged by a table -- six of the ten moves leave the middle four alone  *)
(* and so leave all twenty four bits where they are.  No member is ever taken *)
(* apart, and that is what makes a whole row affordable.                      *)
(*                                                                            *)
(* THE LOOP IS NESTED ON PURPOSE: 812 851 200 as a unary nat does not exist,  *)
(* but 40320 pages of 20160 groups do, and each is the size of nat the        *)
(* existing sweeps already walk.                                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

(* the two loop bounds, and they are the only nats of any size in the file    *)
Definition npagen : nat := 40320.
Definition ngroupn : nat := 20160.

(* walk n consecutive ints, carrying something along                          *)
Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  if n is n1.+1 then ifold n1 (Uint63.add x 1%uint63) f (f x a) else a.

(* ---- the map ------------------------------------------------------------- *)

Definition cshft  : int := 21%uint63.          (* two million a chunk         *)
Definition cmskw  : int := 2097151%uint63.
Definition csize  : int := 2097152%uint63.
Definition nchunk : int := 388%uint63.         (* 40320 * 20160 / 2 ^ 21      *)

Definition gget (m : rmap) (g : int) : int :=
  PArray.get (PArray.get m (Uint63.lsr g cshft)) (Uint63.land g cmskw).

Definition gset (m : rmap) (g v : int) : rmap :=
  let c := Uint63.lsr g cshft in
  PArray.set m c (PArray.set (PArray.get m c) (Uint63.land g cmskw) v).

Definition gor (m : rmap) (g v : int) : rmap :=
  gset m g (Uint63.lor (gget m g) v).

Definition mempty : rmap :=
  PArray.make nchunk (PArray.make csize 0%uint63).

(* a member's group, and its bit inside it                                    *)
Definition grpof (pg gr : int) : int := Uint63.add (Uint63.mul pg ngroupi) gr.
Definition bitof (bt : int) : int := Uint63.lsl 1%uint63 bt.

Definition mtest (m : rmap) (pg gr bt : int) : bool :=
  negb (Uint63.eqb (Uint63.land (gget m (grpof pg gr)) (bitof bt)) 0%uint63).

Definition mmark (m : rmap) (pg gr bt : int) : rmap :=
  gor m (grpof pg gr) (bitof bt).

(* the map is full when every group has all twenty four bits                  *)
Definition allbits : int := 16777215%uint63.

Definition mfull (m : rmap) : bool :=
  ifold npagen 0%uint63
    (fun pg b => b && ifold ngroupn 0%uint63
       (fun gr c => c && Uint63.eqb (gget m (grpof pg gr)) allbits) true)
    true.

(* the two maps together                                                      *)
Definition mor (m1 m2 : rmap) : rmap :=
  ifold npagen 0%uint63
    (fun pg a =>
       ifold ngroupn 0%uint63
         (fun gr a' =>
            let g := grpof pg gr in
            gset a' g (Uint63.lor (gget m1 g) (gget m2 g)))
         a)
    m1.

(* ---- what the map owes --------------------------------------------------- *)

(* Four small facts, and they are all anything above this file needs.  Each  *)
(* is about PArray and the chunking and nothing else -- no cube, no row.     *)

Lemma memptyP pg gr bt : mtest mempty pg gr bt = false.
Proof. Admitted.

Lemma mfullP m pg gr bt : mfull m -> inrange pg gr bt -> mtest m pg gr bt.
Proof. Admitted.

Lemma morP m1 m2 pg gr bt :
  inrange pg gr bt ->
  mtest (mor m1 m2) pg gr bt = mtest m1 pg gr bt || mtest m2 pg gr bt.
Proof. Admitted.

Lemma mmarkP m p g b pg gr bt :
  mtest (mmark m p g b) pg gr bt ->
  [/\ p = pg, g = gr & b = bt] \/ mtest m pg gr bt.
Proof. Admitted.

Section Pre.

(* ---- the ten moves of H, on pages, on groups and on bits ----------------- *)

(* mpg and mgr are permutations of the pages and of the groups; msw says      *)
(* whether a move exchanges the two halves of a group, and mlo, mhi rearrange *)
(* the twelve bits of each half.  Six of the ten leave the bits alone, and    *)
(* for those mlo and mhi are the identity.                                    *)
Variable mpg : arr.                 (* 40320 * 10                            *)
Variable mgr : arr.                 (* 20160 * 10                            *)
Variable msw : arr.                 (* 10                                    *)
Variable mlo mhi : arr.             (* 10 * 4096                             *)

Definition nhi : int := 10%uint63.
Definition nhn : nat := 10.

Definition pgmv (k pg : int) : int :=
  PArray.get mpg (Uint63.add (Uint63.mul pg nhi) k).
Definition grmv (k gr : int) : int :=
  PArray.get mgr (Uint63.add (Uint63.mul gr nhi) k).

Definition lomv (k v : int) : int :=
  PArray.get mlo (Uint63.add (Uint63.lsl k 12%uint63) v).
Definition himv (k v : int) : int :=
  PArray.get mhi (Uint63.add (Uint63.lsl k 12%uint63) v).

Definition lo12 : int := 4095%uint63.

(* one group, moved                                                          *)
Definition grpmv (k v : int) : int :=
  let l := lomv k (Uint63.land v lo12) in
  let h := himv k (Uint63.lsr v 12%uint63) in
  if Uint63.eqb (PArray.get msw k) 0%uint63
  then Uint63.lor l (Uint63.lsl h 12%uint63)
  else Uint63.lor h (Uint63.lsl l 12%uint63).

(* ---- one move over the whole map ----------------------------------------- *)

(* The source is read and the destination written, which is why there are two *)
(* maps: playing a move on what a move has just reached would count a member  *)
(* a level too soon.                                                          *)
Definition prepmv (k : int) (src : rmap) (dst : rmap) : rmap :=
  ifold npagen 0%uint63
    (fun pg d =>
       let pg' := pgmv k pg in
       ifold ngroupn 0%uint63
         (fun gr d' =>
            let v := gget src (grpof pg gr) in
            if Uint63.eqb v 0%uint63 then d'
            else gor d' (grpof pg' (grmv k gr)) (grpmv k v))
         d)
    dst.

(* the whole prepass: carry the map over, then play the ten moves on it       *)
Definition prepass (src : rmap) : rmap :=
  ifold nhn 0%uint63 (fun k d => prepmv k src d) src.

End Pre.
