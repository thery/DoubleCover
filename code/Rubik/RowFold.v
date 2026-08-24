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

(* ---- A CHUNK HOLDS WHOLE PAGES ------------------------------------------- *)

(* RowMap.v cuts the map into chunks of two million words and finds a word by *)
(* splitting its number, which costs a shift, a mask AND A SECOND ARRAY READ  *)
(* at every single word: the chunk first, then the word inside it.            *)
(*                                                                            *)
(* Here a chunk holds sixty four kept pages exactly, so a page never straddles*)
(* two chunks.  The level then reads the chunk ONCE a page and walks inside   *)
(* it, and the second read is gone from the inner loop.  Sixty four is a      *)
(* power of two, so which chunk and where in it are a shift and a mask.       *)

Definition ppcshft : int := 6.                 (* 64 pages a chunk            *)
Definition ppcmask : int := 63.
Definition csizef  : int := 1290240.           (* 64 * 20160                  *)
Definition nchunkf : int := 44.                (* 2768 pages, 64 at a time    *)

(* EVERY CHUNK ITS OWN ARRAY.  `PArray.make nchunkf (PArray.make csizef 0)'   *)
(* runs the inner make ONCE and hands the same array to all forty four slots,  *)
(* so a write to any chunk chains a difference onto that one array -- and it   *)
(* is a global, which nothing ever collects.  Built chunk by chunk instead,    *)
(* each make is under a lambda and runs afresh.                               *)
Definition nchunkn : nat := 44.

Definition mkempty (u : unit) : rmap :=
  ifold nchunkn 0
    (fun c a => PArray.set a c (PArray.make csizef 0))
    (PArray.make nchunkf (PArray.make 1 0)).

(* NEVER START A RUN FROM THIS ONE.  A persistent array keeps its whole       *)
(* history behind any pointer that is still held, and a global is held for    *)
(* ever: every map written from memptyf would keep every difference ever made *)
(* to it alive.  Runs call mkempty tt, which nothing holds.  This one is for  *)
(* reading -- mfullf memptyf and the like -- and for nothing that writes.     *)
Definition memptyf : rmap := mkempty tt.

(* the chunk a kept page lives in, and where the page starts inside it        *)
Definition pchk (r : int) : int := Uint63.lsr r ppcshft.
Definition poff (r : int) : int :=
  Uint63.mul (Uint63.land r ppcmask) ngroupi.

(* one word, for the marking: the level does not go through these            *)
Definition fget (m : rmap) (r g : int) : int :=
  PArray.get (PArray.get m (pchk r)) (Uint63.add (poff r) g).

Definition fset (m : rmap) (r g v : int) : rmap :=
  let c := pchk r in
  PArray.set m c (PArray.set (PArray.get m c) (Uint63.add (poff r) g) v).

Definition ffor (m : rmap) (r g v : int) : rmap :=
  fset m r g (Uint63.lor (fget m r g) v).

(* the map is full when every kept page has all twenty four bits              *)
Definition mfullf (m : rmap) : bool :=
  iter nrepn 0
    (fun r =>
       let a := PArray.get m (pchk r) in
       let o := poff r in
       iter ngroupn 0
         (fun g => Uint63.eqb (PArray.get a (Uint63.add o g)) allbits)).

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
  ffor m (fkpt w) (sgrmv u pty gr) (bitof (sbtmv u bt)).

Definition ftest (m : rmap) (pg gr bt : int) : bool :=
  let w := PArray.get fpg pg in
  let u := fren w in
  let pty := Uint63.lxor (fpar w) (if (bt <? 12)%uint63 then 0 else 1) in
  negb (Uint63.eqb
          (Uint63.land (fget m (fkpt w) (sgrmv u pty gr))
                       (bitof (sbtmv u bt))) 0).

(* ---- one level ----------------------------------------------------------- *)

(* THE DESTINATION IS A MAP OF ITS OWN, which is the prototype's blit: the    *)
(* level reads the map of the last level and writes the map of this one, and  *)
(* no array is read that is also being written.                               *)
(*                                                                            *)
(* A KEPT PAGE IS FILLED IN ONE GO.  Every write this level makes to a page   *)
(* is made here, so the page's chunk is read ONCE, the carry and the ten      *)
(* moves are poured into it, and it is put back once.  The inner loop then    *)
(* holds one array and reaches a word by adding, where RowMap.v's level reads *)
(* the chunk again at every word.                                             *)
(*                                                                            *)
(* The low half of a word and the high half are two outer edge permutations   *)
(* that a renaming sends to two different pairs, so the two halves go to two  *)
(* different words.  Each is twelve bits moved as a block, twice: once for    *)
(* the renaming and once for the move.                                        *)

(* one move of H, gathered into the page being filled                         *)
Definition flevmv (src : rmap) (r k doff : int) (a : arr) : arr :=
  let w := PArray.get fsrc (Uint63.add (Uint63.mul r nhi) k) in
  let u := fren w in
  let pc := fpar w in
  let p := fkpt w in
  let sa := PArray.get src (pchk p) in
  let soff := poff p in
  let glo := Uint63.mul (Uint63.add (Uint63.mul u 2) pc) ngroupi in
  let ghi :=
    Uint63.mul (Uint63.add (Uint63.mul u 2) (Uint63.sub 1 pc)) ngroupi in
  let ub := Uint63.lsl u 12 in
  let kb := Uint63.lsl k 12 in
  let sw := Uint63.eqb (PArray.get msw k) 0 in
  ifold ngroupn 0
    (fun g b =>
       let v := PArray.get sa (Uint63.add soff g) in
       if Uint63.eqb v 0 then b
       else
         let lo := Uint63.land v lo12 in
         let hi := Uint63.land (Uint63.lsr v 12) lo12 in
         let b1 :=
           if Uint63.eqb lo 0 then b
           else
             let l := PArray.get mlo
                        (Uint63.add kb (PArray.get fslo (Uint63.add ub lo))) in
             let j := Uint63.add doff
                        (PArray.get mgr
                           (Uint63.add
                              (Uint63.mul
                                 (PArray.get fsgr (Uint63.add glo g)) nhi) k)) in
             PArray.set b j
               (Uint63.lor (PArray.get b j)
                  (if sw then l else Uint63.lsl l 12)) in
         if Uint63.eqb hi 0 then b1
         else
           let h := PArray.get mhi
                      (Uint63.add kb (PArray.get fshi (Uint63.add ub hi))) in
           let j := Uint63.add doff
                      (PArray.get mgr
                         (Uint63.add
                            (Uint63.mul
                               (PArray.get fsgr (Uint63.add ghi g)) nhi) k)) in
           PArray.set b1 j
             (Uint63.lor (PArray.get b1 j)
                (if sw then Uint63.lsl h 12 else h)))
    a.

(* one kept page: the carry, then the ten moves, then the chunk put back      *)
(* THE CARRY OVERWRITES.  The destination is a map of two levels ago, so its  *)
(* words are stale and every one of them is written, nought or not.  That is  *)
(* what lets the two maps be reused instead of a new one being made a level:  *)
(* a map made a level is 454 MB, and the old ones are held long enough to     *)
(* pile up.                                                                   *)
Definition flevpg (src : rmap) (r : int) (d : rmap) : rmap :=
  let c := pchk r in
  let doff := poff r in
  let sa := PArray.get src c in
  let a0 := PArray.get d c in
  let a1 :=
    ifold ngroupn 0
      (fun g b =>
         let j := Uint63.add doff g in
         PArray.set b j (PArray.get sa j))
      a0 in
  let a2 := ifold nhn 0 (fun k b => flevmv src r k doff b) a1 in
  PArray.set d c a2.

(* THE TWO MAPS ARE HANDED IN AND HANDED BACK.  Nothing is allocated a level: *)
(* the level reads one and fills the other, and the caller swaps them.        *)
Definition flevel (src : rmap) (dst : rmap) : rmap :=
  ifold nrepn 0 (fun r d => flevpg src r d) dst.

(* n levels, the two maps swapping at each one                                *)
Fixpoint flevn (n : nat) (m d : rmap) : rmap :=
  if n is n1.+1 then flevn n1 (flevel m d) m else m.

(* ---- the members, counted ------------------------------------------------ *)

(* NOT PART OF THE ROW, which only ever asks whether the map is full.  This   *)
(* is what the prototype's own numbers can be compared with, level by level:  *)
(* a bit of a kept page stands for as many members as its orbit has pages.    *)
Definition fcount (m : rmap) : int :=
  ifold nrepn 0
    (fun r acc =>
       let orb := PArray.get forb r in
       let ca := PArray.get m (pchk r) in
       let co := poff r in
       ifold ngroupn 0
         (fun g b =>
            let v := PArray.get ca (Uint63.add co g) in
            if Uint63.eqb v 0 then b
            else
              Uint63.add b
                (Uint63.mul orb
                   (Uint63.add (PArray.get fpop (Uint63.land v lo12))
                      (PArray.get fpop
                         (Uint63.land (Uint63.lsr v 12) lo12)))))
         acc)
    0.

End PreF.
