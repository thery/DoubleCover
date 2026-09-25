(* =========================================================================  *)
(*  RowLeafBench.v -- what one leaf costs, now and ranked straight.           *)
(* =========================================================================  *)

(* A BENCH, not part of any proof, and not in _CoqProject.                    *)
(*                                                                            *)
(* THE LEAF THE RUN USES, ytomembd in RowFoldCubDef, turns the twenty cubies  *)
(* back into the forty eight entry table (y2ti), inverts that table and then  *)
(* ranks.  The twenty already say which cubie sits at each place, and that is *)
(* what the three ranks read, so `dirleaf' ranks them straight.  No proof     *)
(* here that the two agree: `agree' checks it on ten thousand members of H.   *)
(*                                                                            *)
(*   cd code/Rubik && ulimit -s unlimited                                     *)
(*   /usr/bin/time -v coqc -R . Rubik RowLeafBench.v                          *)
(*                                                                            *)
(* IT MUST PRINT true FIRST.  Then each leaf at two sizes, 1 and 3 million    *)
(* leaves; the DIFFERENCE over 2 million is the cost of one leaf, and the     *)
(* constant cancels.  The first Eval of a native_compute file pays for the    *)
(* tables arriving and is thrown away.                                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Tabi Coordfsi Row RowMemb RowMembi RowCub RowCubi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

(* ---- the two leaves ------------------------------------------------------ *)

(* the run's, as RowFoldCubDef writes it                                      *)
Definition oldleaf (y : arr) : memb := tomembi (y2ti y).

(* straight from the twenty: a corner is 3 * cubie + twist, an edge          *)
(* 2 * cubie + flip, the middle places are the last four                     *)
Definition dirleaf (y : arr) : memb :=
  (rank8i (fun p => PArray.get y p / 3),
   rank8i (fun p => PArray.get y (8 + p) / 2),
   rank4i (fun p => PArray.get y (16 + p) / 2 - 8)).

(* ---- members of H to feed them ------------------------------------------- *)

Definition yid : arr :=
  foldi 20 0 (fun p a => PArray.set a p (if p <? 8 then 3 * p else 2 * (p - 8)))
        (PArray.make 20 0).

(* the ten moves of H, read off zstepi on the identity                        *)
Definition hmv : seq int := [:: 0; 1; 2; 4; 7; 9; 10; 11; 13; 16].

Fixpoint wordsH (n : nat) (ys : seq arr) : seq arr :=
  if n is n1.+1
  then wordsH n1 (flatten [seq [seq zstepi y k | k <- hmv] | y <- ys])
  else ys.

(* every word of four moves of H: ten thousand members                        *)
Definition nsample : int := 10000.
Definition sample : PArray.array arr :=
  Eval vm_compute in
  let l := wordsH 4 [:: yid] in
  snd (foldl (fun (ia : int * PArray.array arr) y =>
                let: (i, a) := ia in (i + 1, PArray.set a i y))
             (0, PArray.make nsample yid) l).

(* ---- the check ----------------------------------------------------------- *)

Definition eqm (a b : memb) : bool :=
  let: (a1, a2, a3) := a in
  let: (b1, b2, b3) := b in (a1 =? b1) && (a2 =? b2) && (a3 =? b3).

Definition agree : bool :=
  alli 10000 0 (fun i => eqm (dirleaf (PArray.get sample i))
                             (oldleaf (PArray.get sample i))).

Eval vm_compute in agree.

(* ---- the loop ------------------------------------------------------------ *)

(* r rounds over the sample, the three ranks added up so nothing is dropped   *)
Definition msum (m : memb) : int := let: (a, b, c) := m in a + b + c.

(* RowMap's, written again so as not to load the map                          *)
Fixpoint ifold (A : Type) (n : nat) (x : int) (f : int -> A -> A) (a : A) : A :=
  if n is n1.+1 then ifold n1 (x + 1) f (f x a) else a.

Fixpoint bench (f : arr -> memb) (r : nat) (acc : int) : int :=
  if r is r1.+1
  then bench f r1 (ifold 10000 0
                     (fun i s => s + msum (f (PArray.get sample i))) acc)
  else acc.

(* ---- two more leaves: no division, and no closure ----------------------- *)

(* A RANK ONLY COMPARES.  3 * cubie + twist orders two different cubies the   *)
(* way the cubies do, and so does 2 * cubie + flip, and taking 8 off the      *)
(* middle four moves none of them past another.  So the ranks can be read on  *)
(* the twenty as they are: no division at all.                               *)
Definition rawleaf (y : arr) : memb :=
  (rank8i (fun p => PArray.get y p),
   rank8i (fun p => PArray.get y (8 + p)),
   rank4i (fun p => PArray.get y (16 + p))).

(* and the same rank as the OCaml's: the array read in place, no function     *)
(* called for each comparison                                                 *)
Definition rankA (a : arr) (off : int) (nn : nat) (ni : int) : int :=
  ifold nn 0
    (fun i r =>
       let ai := PArray.get a (off + i) in
       let c := ifold nn 0
                  (fun j c => if i <? j then
                                (if PArray.get a (off + j) <? ai then c + 1 else c)
                              else c) 0 in
       r * (ni - i) + c) 0.

Definition arrleaf (y : arr) : memb :=
  (rankA y 0 8 8, rankA y 8 8 8, rankA y 16 4 4).

Definition agree2 : bool :=
  alli 10000 0 (fun i => eqm (rawleaf (PArray.get sample i))
                             (oldleaf (PArray.get sample i)))
  && alli 10000 0 (fun i => eqm (arrleaf (PArray.get sample i))
                                (oldleaf (PArray.get sample i))).

(* IT MUST PRINT true TOO *)
Eval vm_compute in agree2.

(* ---- and the rank with a bit mask ---------------------------------------- *)

(* A piece's count is its value less the values already seen below it.  The  *)
(* values seen are a mask of eight bits, so that count is one read of a       *)
(* popcount table, and a rank is n steps with no inner loop.  It needs the    *)
(* values to be 0 .. n-1, which the three tables below make them: the cubie   *)
(* of a corner, of an outer edge, of a middle edge less eight.  The mask and  *)
(* the rank so far share one int, the mask in the low eight bits.            *)
Definition mkt (f : int -> int) : arr :=
  ifold 24 0 (fun v a => PArray.set a v (f v)) (PArray.make 24 0).
Definition cq : arr := Eval vm_compute in mkt (fun v => v / 3).
Definition eq2 : arr := Eval vm_compute in mkt (fun v => v / 2).
Definition mq : arr :=
  Eval vm_compute in mkt (fun v => if 16 <=? v then v / 2 - 8 else 0).
Definition pop8 : arr := Eval vm_compute in
  ifold 256 0 (fun s a => PArray.set a s
     (ifold 8 0 (fun b c => c + ((s >> b) land 1)) 0)) (PArray.make 256 0).

Definition rankB (tbl a : arr) (off : int) (nn : nat) (ni : int) : int :=
  Uint63.lsr
    (ifold nn 0
      (fun i st =>
         let v := PArray.get tbl (PArray.get a (Uint63.add off i)) in
         let bv := Uint63.lsl 1 v in
         let seen := Uint63.land st 255 in
         let c := Uint63.sub v
                    (PArray.get pop8 (Uint63.land seen (Uint63.sub bv 1))) in
         Uint63.lor
           (Uint63.lsl (Uint63.add (Uint63.mul (Uint63.lsr st 8)
                                               (Uint63.sub ni i)) c) 8)
           (Uint63.lor seen bv))
      0) 8.

Definition bitleaf (y : arr) : memb :=
  (rankB cq y 0 8 8, rankB eq2 y 8 8 8, rankB mq y 16 4 4).

Definition agree3 : bool :=
  alli 10000 0 (fun i => eqm (bitleaf (PArray.get sample i))
                             (oldleaf (PArray.get sample i))).

(* IT MUST PRINT true TOO *)
Eval vm_compute in agree3.

(* the floor: the same loop, a leaf that reads one entry                      *)
Definition noleaf (y : arr) : memb := (PArray.get y 0, 0, 0).

(* thrown away: the tables arriving *)
Time Eval native_compute in bench oldleaf 100 0.

Time Eval native_compute in bench noleaf 100 0.
Time Eval native_compute in bench noleaf 300 0.

Time Eval native_compute in bench oldleaf 100 0.
Time Eval native_compute in bench oldleaf 300 0.

Time Eval native_compute in bench dirleaf 100 0.
Time Eval native_compute in bench dirleaf 300 0.

Time Eval native_compute in bench rawleaf 100 0.
Time Eval native_compute in bench rawleaf 300 0.

Time Eval native_compute in bench arrleaf 100 0.
Time Eval native_compute in bench arrleaf 300 0.

Time Eval native_compute in bench bitleaf 100 0.
Time Eval native_compute in bench bitleaf 300 0.
