(* =========================================================================  *)
(*  RowFold.v -- the map of a row, folded by the sixteen renamings.           *)
(* =========================================================================  *)

(* Turning or reflecting the whole cube renames the faces.  The sixteen       *)
(* renamings that leave the pair U/D where it is send H to H and a move of H  *)
(* to a move of H, and they leave the superflip alone.  So a member of the    *)
(* superflip's row carries fifteen others with it, all reached by a word of   *)
(* the same length, and ONE PAGE OF EACH ORBIT IS ENOUGH TO KEEP.             *)
(*                                                                            *)
(*   the whole map   40320 pages of 20160 words   812 851 200   6.5 GB        *)
(*   folded           2768 pages of 20160 words    55 808 880   0.45 GB       *)
(*                                                                            *)
(* Fifteen times less memory, and a level is a sweep of the map, so it is     *)
(* fifteen times less work as well.  Measured in the prototype on one         *)
(* machine: the ball of H to depth sixteen, 61 s folded against 18 to 33 s a  *)
(* level unfolded.                                                            *)
(*                                                                            *)
(* THE LEVEL GATHERS, IT DOES NOT SCATTER.  Every page written is a kept one, *)
(* and every page read is a kept one read through the renaming that folds it, *)
(* so no page outside the folded map is ever named.  RowMap.v's level does    *)
(* the opposite -- it reads a page and writes where the move sends it -- and  *)
(* that cannot be folded, because where a move sends a kept page is usually   *)
(* not kept.                                                                  *)
(*                                                                            *)
(* A GROUP IS NOT SENT TO A GROUP.  A group is a pair of outer edge           *)
(* permutations that differ by exchanging two cubies, and a renaming          *)
(* exchanges two OTHER cubies, so the two members of a pair land in two       *)
(* different pairs.  They are told apart by their parity, which no renaming   *)
(* changes: the low half of a word is one parity and the high half the other, *)
(* and the two halves go to two different words.                              *)
(*                                                                            *)
(* NOT PROVED HERE.  This file is the algorithm, mimicking ocaml/rubik_row.ml *)
(* word for word; what it computes is checked against the prototype's own     *)
(* numbers.                                                                   *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Ball Row RowMap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Local Open Scope uint63_scope.

(* ---- the folded map ------------------------------------------------------ *)

Definition nsymi : int := 16.               (* renamings that keep U/D        *)
Definition nrepi : int := 2768.             (* pages kept, of the 40320       *)
Definition nrepn : nat := to_nat nrepi.

(* 2768 * 20160 words, in chunks of two million                               *)
Definition nchunkf : int := 27.

Definition memptyf : rmap :=
  PArray.make nchunkf (PArray.make csize 0).

(* the map is full when every kept page has all twenty four bits              *)
Definition mfullf (m : rmap) : bool :=
  iter nrepn 0
    (fun r => iter ngroupn 0
       (fun g => Uint63.eqb (gget m (grpof r g)) allbits)).

Section PreF.

(* ---- what the fold reads ------------------------------------------------- *)

(* fpg  : a page -- where it is kept, the renaming that folds it, its parity  *)
(* fsrc : a kept page and a move -- the kept page it gathers from, the        *)
(*        renaming to read that page through, and that page's parity          *)
(* fsgr : a renaming on a group, the two parities apart                       *)
(* fslo : a renaming on the twelve bits of the low half, fshi the high        *)
(* fsbt : a renaming on one of the twenty four bits                           *)
(*                                                                            *)
(* A PAGE AND ITS RENAMING ARE ONE NUMBER, and so are a source and its        *)
(* parity: the level reads one word where it would otherwise read three.      *)
Variable fpg : arr.                 (* 40320                                  *)
Variable fsrc : arr.                (* 2768 * 10                              *)
Variable fsgr : arr.                (* 16 * 2 * 20160                         *)
Variable fslo fshi : arr.           (* 16 * 4096                              *)
Variable fsbt : arr.                (* 16 * 24                                *)

(* and what RowMap.v's level reads: the move on groups, halves and bits       *)
Variable mgr msw mlo mhi : arr.

(* forb : a kept page -- how many pages its orbit has                         *)
(* fpop : the bits of a half, counted                                         *)
Variable forb fpop : arr.           (* 2768, 4096                             *)

(* the three fields of a folded word                                          *)
Definition fpar (w : int) : int := Uint63.land w 1.
Definition fren (w : int) : int := Uint63.land (Uint63.lsr w 1) 15.
Definition fkpt (w : int) : int := Uint63.lsr w 5.

Definition sgrmv (u pty g : int) : int :=
  PArray.get fsgr
    (Uint63.add (Uint63.mul (Uint63.add (Uint63.mul u 2) pty) ngroupi) g).

Definition slomv (u v : int) : int :=
  PArray.get fslo (Uint63.add (Uint63.lsl u 12) v).
Definition shimv (u v : int) : int :=
  PArray.get fshi (Uint63.add (Uint63.lsl u 12) v).

Definition sbtmv (u bt : int) : int :=
  PArray.get fsbt (Uint63.add (Uint63.mul u nbiti) bt).

(* ---- where a member stands ----------------------------------------------- *)

(* The page is folded to the kept page of its orbit and the renaming that      *)
(* folds it is played on the rest of the member.  WHICH PARITY THE GROUP IS    *)
(* READ AT is the page's parity turned over by the bit's: the low half of a    *)
(* word is the even middle permutations and the high half the odd ones.        *)
Definition fmark (m : rmap) (pg gr bt : int) : rmap :=
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  gor m (grpof (fkpt w) (sgrmv u pty gr)) (bitof (sbtmv u bt)).

Definition ftest (m : rmap) (pg gr bt : int) : bool :=
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  negb (Uint63.eqb
          (Uint63.land (gget m (grpof (fkpt w) (sgrmv u pty gr)))
                       (bitof (sbtmv u bt))) 0).

(* ---- one level ----------------------------------------------------------- *)

(* THE DESTINATION IS A MAP OF ITS OWN, which is the prototype's blit.  The   *)
(* level reads the map of the last level and writes the map of this one, and  *)
(* no array is read that is also being written -- a map kept alive while      *)
(* another version of it is written is what makes a persistent array slow.    *)
(* A group that is nought is skipped: the destination starts empty.           *)
Definition mcopyf (src : rmap) : rmap :=
  ifold nrepn 0
    (fun r d =>
       ifold ngroupn 0
         (fun g d' =>
            let i := grpof r g in
            let v := gget src i in
            if Uint63.eqb v 0 then d' else gset d' i v)
         d)
    memptyf.

(* one move of H, gathered into one kept page                                 *)
Definition flevmv (k r : int) (src : rmap) (dst : rmap) : rmap :=
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let u := fren w in
  let pc := fpar w in
  let p := fkpt w in
  let sw := Uint63.eqb (PArray.get msw k) 0 in
  ifold ngroupn 0
    (fun g d =>
       let v := gget src (grpof p g) in
       if Uint63.eqb v 0 then d
       else
         let l := slomv u (Uint63.land v lo12) in
         let h := shimv u (Uint63.land (Uint63.lsr v 12) lo12) in
         let d1 :=
           if Uint63.eqb l 0 then d
           else
             let l' := lomv mlo k l in
             gor d (grpof r (grmv mgr k (sgrmv u pc g)))
               (if sw then l' else Uint63.lsl l' 12) in
         if Uint63.eqb h 0 then d1
         else
           let h' := himv mhi k h in
           gor d1 (grpof r (grmv mgr k (sgrmv u (Uint63.sub 1 pc) g)))
             (if sw then Uint63.lsl h' 12 else h'))
    dst.

(* the ten moves of H, into one kept page                                     *)
Definition flevpg (r : int) (src dst : rmap) : rmap :=
  ifold nhn 0 (fun k d => flevmv k r src d) dst.

(* the whole level: the map carried over, then every kept page gathered       *)
Definition flevel (src : rmap) : rmap :=
  ifold nrepn 0 (fun r d => flevpg r src d) (mcopyf src).

Fixpoint flevn (n : nat) (m : rmap) : rmap :=
  if n is n1.+1 then flevn n1 (flevel m) else m.

(* ---- the members, counted ------------------------------------------------ *)

(* NOT PART OF THE ROW, which only ever asks whether the map is full.  This   *)
(* is what the prototype's own numbers can be compared with, level by level:  *)
(* a bit of a kept page stands for as many members as its orbit has pages.    *)
Definition fcount (m : rmap) : int :=
  ifold nrepn 0
    (fun r a =>
       let o := PArray.get forb r in
       ifold ngroupn 0
         (fun g b =>
            let v := gget m (grpof r g) in
            if Uint63.eqb v 0 then b
            else
              Uint63.add b
                (Uint63.mul o
                   (Uint63.add (PArray.get fpop (Uint63.land v lo12))
                      (PArray.get fpop
                         (Uint63.land (Uint63.lsr v 12) lo12)))))
         a)
    0.

End PreF.
