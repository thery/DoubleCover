(* =========================================================================  *)
(*  RowCubi.v -- the twenty cubies as twenty int63, the way the search runs.  *)
(* =========================================================================  *)

(* RowCub.v CARRIES A LIST OF nat, which is where the proofs are stated, and  *)
(* a nat operation costs a microsecond where an int63 one costs a twentieth.  *)
(* So the search cannot run on it, exactly as it cannot run on Table.v's      *)
(* lists: Tabi.v is the int63 twin there, and this file is the twin here.     *)
(*                                                                           *)
(* A MOVE IS THREE TABLE READS AND ONE ARRAY READ PER PLACE, AND NO           *)
(* ARITHMETIC.  The move's own twenty say, for each place, which place the    *)
(* cubie comes from and how far it is turned on the way.  ymvpi holds the     *)
(* first, with the offset of eight for an edge already in it.  The second is  *)
(* not added but looked up: tturni holds, for every cubie and every turn,     *)
(* the cubie turned, and offi holds where in it this move's place looks.      *)
(*                                                                           *)
(* MEASURED at depth twelve on gukesh: the forty eight entry table 17.9 s,    *)
(* the twenty 11.5 s when the turn was three arithmetic operations, and no    *)
(* position at all 5.4 s.                                                     *)
(*                                                                           *)
(* THE MOVE UNDONE IS WHAT IS TABULATED, since that is what composes the      *)
(* move on the right -- see RowCub's zstep.                                   *)
(*                                                                           *)
(* WHAT IS CHECKED: the int63 step and the list step agree, on every position *)
(* two moves from the root.  The bridge lemma itself is not proved yet.       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Lehmer RowTabP RowMemb RowCub.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

Local Open Scope uint63_scope.

Definition nsmli : int := 20.               (* eight corners and twelve edges *)
Definition nmvni : int := 18.               (* the moves                      *)

(* ---- the move's twenty, split into a place and a turn -------------------- *)

(* where place p reads from: a corner place under eight, an edge place with   *)
(* the offset of eight already in it                                          *)
Definition ymvpn (k : nat) : seq nat :=
  [seq (let v := nth 0%N (ymvv k) p in
        if (p < 8)%N then (v %/ 3)%N else (8 + v %/ 2)%N) | p <- iota 0 20].

(* and how far it is turned on the way *)
Definition ymvtn (k : nat) : seq nat :=
  [seq (let v := nth 0%N (ymvv k) p in
        if (p < 8)%N then (v %% 3)%N else (v %% 2)%N) | p <- iota 0 20].

(* the places, flat: move k at k * 20 *)
Definition ymvpi : arr := Eval vm_compute in
  mkarrn (nmvni * nsmli)
    [seq of_nat v | v <- flatten [seq ymvpn k | k <- iota 0 18]].

(* ---- the turn, looked up rather than added ------------------------------ *)

(* a cubie is three times its place plus its turn, so turning it by u is an   *)
(* operation on a number under twenty four.  There are two of them, three     *)
(* turns for a corner and two for an edge, and 2 * 3 * 24 is a small table.   *)
Definition tturnn : seq nat :=
  [seq (let g := (i %% 24)%N in let u := (i %/ 24 %% 3)%N in
        let m := (if (i < 72)%N then 3 else 2)%N in
        (g - g %% m + (g %% m + u) %% m)%N) | i <- iota 0 144].

Definition tturni : arr := Eval vm_compute in
  mkarrn 144 [seq of_nat v | v <- tturnn].

(* and where in it place j of move k looks: the corner half or the edge half, *)
(* at this move's turn                                                        *)
Definition offn (k : nat) : seq nat :=
  [seq (let u := nth 0%N (ymvtn k) j in
        ((if (j < 8)%N then 0 else 72) + u * 24)%N) | j <- iota 0 20].

Definition offi : arr := Eval vm_compute in
  mkarrn (nmvni * nsmli)
    [seq of_nat v | v <- flatten [seq offn k | k <- iota 0 18]].

Definition yrooti : arr := Eval vm_compute in
  mkarrn nsmli [seq of_nat v | v <- yroot].

(* ---- a move ------------------------------------------------------------- *)

(* twenty places, and for each of them three table reads, one array read and  *)
(* one write into a fresh twenty.  The forty eight entry table is forty       *)
(* eight of each.                                                             *)
Definition zstepi (x : arr) (k : int) : arr :=
  let b := k * nsmli in
  foldi 20 0
    (setf (fun j => PArray.get tturni
                      (PArray.get offi (b + j)
                       + PArray.get x (PArray.get ymvpi (b + j)))))
    (PArray.make nsmli 0).

(* ---- and that it is RowCub's step --------------------------------------- *)

Definition a2y (x : arr) : seq nat :=
  [seq to_nat (PArray.get x (of_nat j)) | j <- iota 0 20].

(* the root, every move of it, and every move of those: the int63 twenty and  *)
(* the list twenty are the same twenty.                                       *)
Definition zstepiC : bool :=
  (a2y yrooti == yroot) &&
  all (fun k =>
        (a2y (zstepi yrooti (of_nat k)) == zstep yroot k)
        && all (fun l => a2y (zstepi (zstepi yrooti (of_nat k)) (of_nat l))
                         == zstep (zstep yroot k) l)
              (iota 0 18))
      (iota 0 18).

Lemma zstepiCP : zstepiC. Proof. by vm_compute. Qed.

(* ---- the int63 step IS the list step ------------------------------------- *)

(* WHAT IS LEFT TO SAY, and it is the only thing that connects the search to  *)
(* the proof: reading the int63 twenty back as a list turns a move of this    *)
(* file into a move of RowCub's.  Everything below is bookkeeping for that.   *)

Lemma n360_small : 360 < nwB. Proof. by apply: (@ltn_nwB 9). Qed.
Lemma n20_small : (20 < nwB)%N. Proof. by apply: (@ltn_nwB 9). Qed.
Lemma to_nat_nsmli : to_nat nsmli = 20%N. Proof. by vm_compute. Qed.

Lemma len_mk : to_nat (PArray.length (PArray.make nsmli 0)) = 20%N.
Proof. by rewrite length_makeE; vm_compute. Qed.

(* place j of move k sits at k * 20 + j, in the int63 index and in the list  *)
Lemma bjE k j : (k < 18)%N -> (j < 20)%N ->
  of_nat k * nsmli + of_nat j = of_nat (k * 20 + j)%N.
Proof.
move=> hk hj.
have hk17 : (k <= 17)%N by rewrite -ltnS.
have hkj : (k * 20 + j < 360)%N.
  by apply: (@leq_ltn_trans (17 * 20 + 19)%N);
     [apply: leq_add; [apply: leq_mul | rewrite -ltnS] | ].
have hb : (k * 20 + j < nwB)%N by apply: (ltn_trans hkj n360_small).
have h360 : (360 < nwB)%N := n360_small.
have hkb : (k < nwB)%N by apply: (ltn_trans hk); apply: (ltn_trans _ h360).
have hjb : (j < nwB)%N by apply: (ltn_trans hj); apply: (ltn_trans _ h360).
have hm : to_nat (of_nat k * nsmli) = (k * 20)%N.
  rewrite to_nat_mul ?to_nat_nsmli ?of_natK //.
  by apply: (leq_ltn_trans _ hb); rewrite leq_addr.
apply: to_nat_inj; rewrite of_natK // to_nat_add hm ?of_natK //.
Qed.

(* what the turn table holds, read as arithmetic *)
Lemma tturnnE i : (i < 144)%N ->
  nth 0%N tturnn i =
  (let g := (i %% 24)%N in let u := (i %/ 24 %% 3)%N in
   let m := (if (i < 72)%N then 3 else 2)%N in
   g - g %% m + (g %% m + u) %% m)%N.
Proof. by move=> hi; rewrite /tturnn (nth_map 0%N) ?size_iota // nth_iota. Qed.

Lemma tturn_val kind u g : (kind < 2)%N -> (u < 3)%N -> (g < 24)%N ->
  nth 0%N tturnn (kind * 72 + u * 24 + g)%N
  = (let m := (if kind == 0%N then 3 else 2)%N in
     g - g %% m + (g %% m + u) %% m)%N.
Proof.
move=> hk hu hg.
have hi : (kind * 72 + u * 24 + g < 144)%N.
  apply: (@leq_ltn_trans (1 * 72 + 2 * 24 + 23)%N).
    by apply: leq_add; [apply: leq_add; apply: leq_mul => //; rewrite -ltnS |
                        rewrite -ltnS].
  by [].
have he : (kind * 72 + u * 24 + g = (kind * 3 + u) * 24 + g)%N.
  by rewrite mulnDl -mulnA.
rewrite tturnnE // he modnMDl (modn_small hg) divnMDl // (divn_small hg) addn0.
rewrite modnMDl (modn_small hu).
have hc : ((kind * 3 + u) * 24 + g < 72)%N = (kind == 0%N).
  case: kind hk {hi he} => [|[|//]] _ /=.
    rewrite mul0n add0n; apply: (@leq_ltn_trans (2 * 24 + 23)%N) => //.
    by apply: leq_add; [apply: leq_mul => //; rewrite -ltnS | rewrite -ltnS].
  by rewrite mul1n ltnNge (leq_trans _ (leq_addr _ _)) // -[72]/(3 * 24)%N
             leq_mul2r /= leq_addr.
by rewrite /= hc.
Qed.

(* one place of one step, read off the array *)
Lemma get_zstepi x k j : (k < 18)%N -> (j < 20)%N ->
  PArray.get (zstepi x (of_nat k)) (of_nat j)
  = PArray.get tturni (PArray.get offi (of_nat (k * 20 + j))
                       + PArray.get x (PArray.get ymvpi (of_nat (k * 20 + j)))).
Proof.
move=> hk hj.
have hjb : (j < nwB)%N by apply: (ltn_trans hj n20_small).
rewrite /zstepi; cbv zeta.
rewrite (@get_foldi_in
   (fun i => PArray.get tturni
               (PArray.get offi (of_nat k * nsmli + i)
                + PArray.get x (PArray.get ymvpi (of_nat k * nsmli + i))))
   20 0 (of_nat j) (PArray.make nsmli 0));
  rewrite ?to_nat_0 ?add0n ?len_mk ?of_natK //.
  by rewrite bjE.
exact: n20_small.
Qed.

(* ---- and the three tables hold what the lists say ------------------------ *)

Definition ycubiC : bool :=
  all (fun k =>
        let p := ymvpn k in
        let o := offn k in
        all (fun j =>
          [&& PArray.get ymvpi (of_nat (k * 20 + j)) == of_nat (nth 0%N p j),
              (nth 0%N p j < 20)%N,
              PArray.get offi (of_nat (k * 20 + j)) == of_nat (nth 0%N o j)
            & (nth 0%N o j <= 120)%N])
          (iota 0 20))
      (iota 0 18)
  && (let t := tturnn in
      all (fun i => (PArray.get tturni (of_nat i) == of_nat (nth 0%N t i))
                    && (nth 0%N t i < 24)%N)
          (iota 0 144)).

Lemma ycubiCP : ycubiC. Proof. by vm_compute. Qed.

Lemma ycubiE k j : (k < 18)%N -> (j < 20)%N ->
  [&& PArray.get ymvpi (of_nat (k * 20 + j)) == of_nat (nth 0%N (ymvpn k) j),
      (nth 0%N (ymvpn k) j < 20)%N,
      PArray.get offi (of_nat (k * 20 + j)) == of_nat (nth 0%N (offn k) j)
    & (nth 0%N (offn k) j <= 120)%N].
Proof.
move=> hk hj; have /andP[/allP h _] := ycubiCP.
have hkm : k \in iota 0 18 by rewrite mem_iota add0n leq0n hk.
have hjm : j \in iota 0 20 by rewrite mem_iota add0n leq0n hj.
by have /allP h2 := h _ hkm; apply: h2.
Qed.

Lemma tturniE i : (i < 144)%N ->
  (PArray.get tturni (of_nat i) == of_nat (nth 0%N tturnn i))
  && (nth 0%N tturnn i < 24)%N.
Proof.
move=> hi; have /andP[_ /allP h] := ycubiCP.
by apply: h; rewrite mem_iota add0n leq0n hi.
Qed.
