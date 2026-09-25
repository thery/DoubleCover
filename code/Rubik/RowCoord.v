(* =========================================================================  *)
(*  RowCoord.v -- the position as hcoset's small coordinates: the corners as  *)
(*  their rank, each group of four edges as the places of its four cubies.    *)
(* =========================================================================  *)

(* FOR A BENCH, not part of any proof.  hcoset's permcube, as the OCaml       *)
(* EXP_COORD does it.  A position is four numbers, each moved by a table:     *)
(*                                                                            *)
(*   the corner permutation, by its rank (40320 x 18)                         *)
(*   the places of the cubies 0-3, of 4-7 and of 8-11, each four places in    *)
(*   base twelve (20736 x 18, one table for the three)                        *)
(*                                                                            *)
(* and a member of H reads its page, group and bit from three tables, with   *)
(* no ranking.  The twists and flips are not carried: the search reads them   *)
(* from the phase one coordinate, which it carries anyway.                    *)
(*                                                                            *)
(* The tables are built by computation.  The checks at the end compare the    *)
(* four numbers with RowCubi's twenty cubies, move by move, and the place     *)
(* with bitleaf's on members of H.                                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Tabi Phase1 Row RowMap RowCubi RowLeafFast RowTabL.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

(* ---- building a table ----------------------------------------------------- *)

Definition mkT (sz : nat) (f : int -> int) : arr :=
  ifold sz 0 (fun i a => PArray.set a i (f i)) (PArray.make (of_nat sz) 0).

(* ---- the corners ---------------------------------------------------------- *)

(* 0! .. 7!                                                                    *)
Definition factA : arr := mkT 8 (fun i => ifold (to_nat i) 1 Uint63.mul 1).

(* the c-th value, from 0, that the mask s does not hold                      *)
Definition nthfree (s c : int) : int :=
  (ifold 8 0
     (fun v (st : int * int) =>
        let: (res, cnt) := st in
        if Uint63.eqb (Uint63.land s (Uint63.lsl 1 v)) 0
        then (if Uint63.eqb cnt c then v else res, Uint63.add cnt 1)
        else st)
     (0, 0)).1.

(* the corner permutation of rank r, as lbrank ranks it: place -> cubie       *)
Definition cunrank (r : int) : arr :=
  let: (a, _, _) :=
    ifold 8 0
      (fun i (st : arr * int * int) =>
         let: (a, r, s) := st in
         let f := PArray.get factA (Uint63.sub 7 i) in
         let c := Uint63.div r f in
         let v := nthfree s c in
         (PArray.set a i v, Uint63.sub r (Uint63.mul c f),
          Uint63.lor s (Uint63.lsl 1 v)))
      (PArray.make 8 0, r, 0) in a.

(* the move k played on the corner rank r, at 18 r + k                        *)
Definition ctab : arr :=
  mkT (40320 * 18)
    (fun i =>
       let r := Uint63.div i 18 in
       let k := Uint63.sub i (Uint63.mul r 18) in
       let a := cunrank r in
       lbrank (fun j => PArray.get a (PArray.get ymvpi (Uint63.add (Uint63.mul k 20) j)))
              8 8).

(* ---- the edges ------------------------------------------------------------ *)

(* where the move k sends the edge place q, at 12 k + q                       *)
Definition einvT : arr :=
  ifold (18 * 12) 0
    (fun i a =>
       let k := Uint63.div i 12 in
       let j := Uint63.sub i (Uint63.mul k 12) in
       PArray.set a
         (Uint63.add (Uint63.mul k 12)
            (Uint63.sub (PArray.get ymvpi (Uint63.add (Uint63.mul k 20)
                                                      (Uint63.add 8 j))) 8))
         j)
    (PArray.make (18 * 12) 0).

(* four places in base twelve                                                 *)
Definition ntup : nat := 20736.
Definition enc (p0 p1 p2 p3 : int) : int :=
  Uint63.add (Uint63.mul (Uint63.add (Uint63.mul (Uint63.add (Uint63.mul p0 12) p1)
                                                 12) p2) 12) p3.
Definition tp0 (t : int) : int := Uint63.div t 1728.
Definition tp1 (t : int) : int := Uint63.mod (Uint63.div t 144) 12.
Definition tp2 (t : int) : int := Uint63.mod (Uint63.div t 12) 12.
Definition tp3 (t : int) : int := Uint63.mod t 12.

(* the move k played on the four places t, at 18 t + k                        *)
Definition etab : arr :=
  mkT (ntup * 18)
    (fun i =>
       let t := Uint63.div i 18 in
       let k := Uint63.sub i (Uint63.mul t 18) in
       let inv q := PArray.get einvT (Uint63.add (Uint63.mul k 12) q) in
       enc (inv (tp0 t)) (inv (tp1 t)) (inv (tp2 t)) (inv (tp3 t))).

(* ---- the leaf ------------------------------------------------------------- *)

Definition all4 (f : int -> bool) (t : int) : bool :=
  f (tp0 t) && f (tp1 t) && f (tp2 t) && f (tp3 t).

(* four places, distinct                                                      *)
Definition dist4 (t : int) : bool :=
  let a := tp0 t in let b := tp1 t in let c := tp2 t in let d := tp3 t in
  ~~ [|| a =? b, a =? c, a =? d, b =? c, b =? d | c =? d].

(* four distinct places all outer: their number among the 1680 such, and back *)
Definition n8t : int := 1680.
Definition sub8tup : arr * arr :=
  let: (s, u, _) :=
    ifold ntup 0
      (fun t (st : arr * arr * int) =>
         let: (s, u, n) := st in
         if all4 (fun p => p <? 8) t && dist4 t
         then (PArray.set s t n, PArray.set u n t, Uint63.add n 1)
         else st)
      (PArray.make (of_nat ntup) 0, PArray.make n8t 0, 0) in (s, u).
Definition sub8 : arr := sub8tup.1.
Definition tup8 : arr := sub8tup.2.

(* the group of the cubies 0-3 at the places u and 4-7 at v, both outer; a    *)
(* pair of places that overlap is never read and gets 0                        *)
Definition mke8tab (e8num : arr) : arr :=
  mkT (1680 * 1680)
    (fun i =>
       let a := Uint63.div i n8t in
       let b := Uint63.sub i (Uint63.mul a n8t) in
       let u := PArray.get tup8 a in
       let v := PArray.get tup8 b in
       let e0 := PArray.make 8 8 in
       let e1 := PArray.set (PArray.set (PArray.set (PArray.set e0
                   (tp0 u) 0) (tp1 u) 1) (tp2 u) 2) (tp3 u) 3 in
       if all4 (fun p => PArray.get e1 p =? 8) v then
         let e := PArray.set (PArray.set (PArray.set (PArray.set e1
                    (tp0 v) 4) (tp1 v) 5) (tp2 v) 6) (tp3 v) 7 in
         Uint63.div (PArray.get e8num (lbrank (PArray.get e) 8 8)) 2
       else 0).

(* the bit of the cubies 8-11 at the places t, all middle                      *)
Definition mke4tab (e4bit : arr) : arr :=
  mkT ntup
    (fun t =>
       if all4 (fun p => 8 <=? p) t then
         let e := PArray.set (PArray.set (PArray.set (PArray.set (PArray.make 4 0)
                    (Uint63.sub (tp0 t) 8) 0) (Uint63.sub (tp1 t) 8) 1)
                    (Uint63.sub (tp2 t) 8) 2) (Uint63.sub (tp3 t) 8) 3 in
         PArray.get e4bit (lbrank (PArray.get e) 4 4)
       else 0).

(* ---- the position --------------------------------------------------------- *)

Definition cpos := (int * int * int * int)%type.

Definition cstepx (x : cpos) (k : int) : cpos :=
  let: (c, u, d, m) := x in
  (PArray.get ctab (Uint63.add (Uint63.mul c 18) k),
   PArray.get etab (Uint63.add (Uint63.mul u 18) k),
   PArray.get etab (Uint63.add (Uint63.mul d 18) k),
   PArray.get etab (Uint63.add (Uint63.mul m 18) k)).

(* page, group and bit, the plain place24 of the member                       *)
Definition cleaf (e8t e4t : arr) (x : cpos) : int * int * int :=
  let: (c, u, d, m) := x in
  (c, PArray.get e8t (Uint63.add (Uint63.mul (PArray.get sub8 u) n8t)
                                 (PArray.get sub8 d)),
   PArray.get e4t m).

(* ---- from twenty cubies --------------------------------------------------- *)

(* the edge place of the cubie b                                              *)
Definition eplace (y : arr) (b : int) : int :=
  ifold 12 0
    (fun p r => if Uint63.eqb (PArray.get lbeq (PArray.get y (Uint63.add 8 p))) b
                then p else r) 0.

Definition cofy (y : arr) : cpos :=
  let tup b := enc (eplace y b) (eplace y (Uint63.add b 1))
                   (eplace y (Uint63.add b 2)) (eplace y (Uint63.add b 3)) in
  (lbrank (fun p => PArray.get lbcq (PArray.get y p)) 8 8, tup 0, tup 4, tup 8).

(* ---- the checks ----------------------------------------------------------- *)

Definition e8numL : arr := mkarr npagei 0 e8num_data.
Definition e4bitL : arr := mkarr nbiti 0 e4bit_data.

Definition cposeqb (x y : cpos) : bool :=
  let: (a, b, c, d) := x in let: (a', b', c', d') := y in
  [&& a =? a', b =? b', c =? c' & d =? d'].

Definition p3eqb (x y : int * int * int) : bool :=
  let: (a, b, c) := x in let: (a', b', c') := y in
  [&& a =? a', b =? b' & c =? c'].

Definition mv18 : seq int := [seq of_nat k | k <- iota 0 18].

(* the rank undoes cunrank                                                     *)
Definition unrankC : bool :=
  ifold 40320 0 (fun r b => b && (lbrank (PArray.get (cunrank r)) 8 8 =? r)) true.

(* the four numbers follow the twenty cubies: every move, from every position *)
(* two moves from the root                                                    *)
Definition near : seq arr :=
  let l1 := [seq zstepi yrooti k | k <- mv18] in
  yrooti :: l1 ++ flatten [seq [seq zstepi y k | k <- mv18] | y <- l1].

Definition stepC : bool :=
  all (fun y => all (fun k => cposeqb (cofy (zstepi y k)) (cstepx (cofy y) k))
                    mv18) near.

(* the solved position, and the moves of H: those that keep it in H           *)
Definition ysolved : arr :=
  mkT 20 (fun p => if p <? 8 then Uint63.mul p 3 else Uint63.mul (Uint63.sub p 8) 2).

Definition inH (y : arr) : bool :=
  ifold 8 0 (fun p b => b && (Uint63.mod (PArray.get y p) 3 =? 0)) true &&
  ifold 12 0 (fun p b => b && (Uint63.mod (PArray.get y (Uint63.add 8 p)) 2 =? 0)
                          && ((p <? 8) =? (PArray.get y (Uint63.add 8 p) <? 16)))
        true.

Definition hmv : seq int := [seq k <- mv18 | inH (zstepi ysolved k)].

(* the members of H three moves of H from the solved one                      *)
Definition hnear : seq arr :=
  let st l := flatten [seq [seq zstepi y k | k <- hmv] | y <- l] in
  let l1 := st [:: ysolved] in let l2 := st l1 in
  ysolved :: l1 ++ l2 ++ st l2.

Definition leafC : bool :=
  let e8t := mke8tab e8numL in
  let e4t := mke4tab e4bitL in
  all (fun y => inH y &&
         p3eqb (cleaf e8t e4t (cofy y)) (place24 e8numL e4bitL (bitleaf y)))
      hnear.

Time Eval native_compute in (unrankC, seq.size hmv).
Time Eval native_compute in (seq.size near, stepC).
Time Eval native_compute in (seq.size hnear, leafC).
