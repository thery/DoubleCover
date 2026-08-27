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
(* AND IT IS THE SAME STEP: a2y_zstepi says a move here, read back as a      *)
(* list, is a move of RowCub's, for every twenty that hold cubies.  So what   *)
(* is proved there of a step holds of the step the search runs.               *)

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

(* ---- reading the array back as a list ------------------------------------ *)

Lemma a2y_nth x q : (q < 20)%N ->
  nth 0%N (a2y x) q = to_nat (PArray.get x (of_nat q)).
Proof.
move=> hq; rewrite /a2y (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma ymvpnE k j : (j < 20)%N ->
  nth 0%N (ymvpn k) j
  = (let v := nth 0%N (ymvv k) j in
     if (j < 8)%N then (v %/ 3)%N else (8 + v %/ 2)%N).
Proof.
move=> hj; rewrite /ymvpn (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma ymvtnE k j : (j < 20)%N ->
  nth 0%N (ymvtn k) j
  = (let v := nth 0%N (ymvv k) j in
     if (j < 8)%N then (v %% 3)%N else (v %% 2)%N).
Proof.
move=> hj; rewrite /ymvtn (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma offnE k j : (j < 20)%N ->
  nth 0%N (offn k) j
  = ((if (j < 8)%N then 0 else 72) + nth 0%N (ymvtn k) j * 24)%N.
Proof.
move=> hj; rewrite /offn (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma zstep_nth y k j : (j < 20)%N ->
  nth 0%N (zstep y k) j
  = (let v := nth 0%N (ymvv k) j in
     if (j < 8)%N
     then (3 * ycg y (v %/ 3) + (ytw y (v %/ 3) + v %% 3) %% 3)%N
     else (2 * yeg y (v %/ 2) + (yfl y (v %/ 2) + v %% 2) %% 2)%N).
Proof.
move=> hj; rewrite /zstep /ystepm (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

(* ---- and the bridge itself ----------------------------------------------- *)

(* THE ONLY THING THAT CONNECTS THE SEARCH TO THE PROOF.  A move on the       *)
(* int63 twenty, read back as a list, is a move on RowCub's twenty -- so      *)
(* what is proved there of a step holds of the step the search runs.  The     *)
(* twenty have to hold cubies for it: a place under eight and a turn.         *)
Definition yoki (x : arr) : bool :=
  all (fun q => (to_nat (PArray.get x (of_nat q)) < 24)%N) (iota 0 20).

Lemma a2y_zstepi x k : (k < 18)%N -> yoki x ->
  a2y (zstepi x (of_nat k)) = zstep (a2y x) k.
Proof.
move=> hk /allP hy.
apply: (@eq_from_nth _ 0%N).
  by rewrite /a2y /zstep /ystepm !size_map !size_iota.
rewrite /a2y size_map size_iota => j hj.
rewrite -/(a2y _) (a2y_nth _ hj) (get_zstepi _ hk hj).
have /and4P[/eqP hp hpl /eqP ho hol] := ycubiE hk hj.
rewrite hp ho.
set q := nth 0%N (ymvpn k) j; set off := nth 0%N (offn k) j.
have hg : (to_nat (PArray.get x (of_nat q)) < 24)%N.
  by apply: hy; rewrite mem_iota add0n leq0n hpl.
have hs : (off + to_nat (PArray.get x (of_nat q)) < 144)%N.
  by apply: (@leq_ltn_trans (120 + 23)%N);
     [apply: leq_add => //; rewrite -ltnS | ].
have h144 : (144 < nwB)%N by apply: (@ltn_nwB 8).
have hsb : (off + to_nat (PArray.get x (of_nat q)) < nwB)%N
  by apply: (ltn_trans hs h144).
have hoffb : (off < nwB)%N by apply: (leq_ltn_trans (leq_addr _ _) hsb).
have -> : (of_nat off + PArray.get x (of_nat q))
        = of_nat (off + to_nat (PArray.get x (of_nat q)))%N.
  by apply: to_nat_inj; rewrite of_natK // to_nat_add of_natK.
have /andP[/eqP ht htl] := tturniE hs.
rewrite ht of_natK; last by apply: (ltn_trans htl); apply: (ltn_trans _ h144).
rewrite -/(a2y x) (zstep_nth _ _ hj) /=.
case hj8 : (j < 8)%N.
  have hq : q = (nth 0%N (ymvv k) j %/ 3)%N by rewrite /q ymvpnE // hj8.
  have hoff : off = (0 * 72 + (nth 0%N (ymvv k) j %% 3) * 24)%N.
    by rewrite /off offnE // ymvtnE // hj8 mul0n add0n.
  rewrite hoff tturn_val // ?ltn_pmod //=.
  rewrite /ycg /ytw -hq (a2y_nth _ hpl).
  congr (_ + _)%N.
  by rewrite -/q mulnC {1}(divn_eq (to_nat (PArray.get x (of_nat q))) 3) addnK.
have hq : q = (8 + nth 0%N (ymvv k) j %/ 2)%N by rewrite /q ymvpnE // hj8.
have hoff : off = (1 * 72 + (nth 0%N (ymvv k) j %% 2) * 24)%N.
  by rewrite /off offnE // ymvtnE // hj8 mul1n.
have hu2 : (nth 0%N (ymvv k) j %% 2 < 3)%N.
  by apply: (@leq_trans 2%N) => //; apply: ltn_pmod.
rewrite hoff (tturn_val _ hu2 hg) //=.
rewrite /yeg /yfl -hq (a2y_nth _ hpl).
congr (_ + _)%N.
by rewrite -/q mulnC {1}(divn_eq (to_nat (PArray.get x (of_nat q))) 2) addnK.
Qed.

(* ---- the cube the twenty name, built as an array ------------------------- *)

(* AT AN ANSWER THE RUN STILL WANTS THE FORTY EIGHT ENTRY TABLE, because      *)
(* that is what reads a position into three ranks.  Answers are a hundredth   *)
(* of the nodes, so building it there costs nothing next to a step -- but it  *)
(* has to be built in int63, not through the list.                            *)
(*                                                                            *)
(* AND THE SAME TURN TABLE SERVES.  The cube sends the facelet at place p     *)
(* slot s to the facelet of the place the cubie at p came from, slot s plus   *)
(* its turn -- which is the cubie turned by s, so tturni again.  laycomb is   *)
(* the two layouts end to end, the corners first, and lofsi says which half.  *)
(*                                                                            *)
(* IT WRITES f WHERE THE CUBE SENDS f, so what comes out is the INVERSE       *)
(* table, and that is the one the run carries.                                *)
Definition nfi : int := 48.

Definition laycomb : arr := Eval vm_compute in
  mkarrn nfi [seq of_nat v | v <- cflatp ++ elay].

(* which of the twenty a facelet reads, where in the turn table it looks, and *)
(* which half of the layout it lands in                                       *)
Definition plin : seq nat :=
  [seq (if inC f then cposn f else (8 + eposn f)%N) | f <- iota 0 48].

Definition toffn : seq nat :=
  [seq (if inC f then (cslotn f * 24)%N else (72 + eslt f * 24)%N)
   | f <- iota 0 48].

Definition lofsn : seq nat :=
  [seq (if inC f then 0%N else 24%N) | f <- iota 0 48].

Definition plii : arr := Eval vm_compute in
  mkarrn nfi [seq of_nat v | v <- plin].

Definition toffi : arr := Eval vm_compute in
  mkarrn nfi [seq of_nat v | v <- toffn].

Definition lofsi : arr := Eval vm_compute in
  mkarrn nfi [seq of_nat v | v <- lofsn].

Definition y2ti (y : arr) : arr :=
  foldi 48 0
    (fun f a => PArray.set a
       (PArray.get laycomb
          (PArray.get lofsi f
           + PArray.get tturni (PArray.get toffi f
                                + PArray.get y (PArray.get plii f)))) f)
    (PArray.make nfi 0).

(* the root, every move of it, and every move of those *)
Definition y2tiC : bool :=
  (ti2t flast (y2ti yrooti) == cub2tabR yroot) &&
  all (fun k =>
        (ti2t flast (y2ti (zstepi yrooti (of_nat k)))
         == cub2tabR (zstep yroot k))
        && all (fun l =>
             ti2t flast (y2ti (zstepi (zstepi yrooti (of_nat k)) (of_nat l)))
             == cub2tabR (zstep (zstep yroot k) l))
             (iota 0 18))
      (iota 0 18).

Lemma y2tiCP : y2tiC. Proof. by vm_compute. Qed.

(* ---- what those four tables hold ----------------------------------------- *)

Definition ycubjC : bool :=
  (let p := plin in let t := toffn in let l := lofsn in
   all (fun f =>
     [&& PArray.get plii (of_nat f) == of_nat (nth 0%N p f),
         PArray.get toffi (of_nat f) == of_nat (nth 0%N t f),
         PArray.get lofsi (of_nat f) == of_nat (nth 0%N l f),
         (nth 0%N p f < 20)%N
       & (nth 0%N t f <= 120)%N]) (iota 0 48))
  && (let c := cflatp ++ elay in
      all (fun i => PArray.get laycomb (of_nat i) == of_nat (nth 0%N c i))
          (iota 0 48)).

Lemma ycubjCP : ycubjC. Proof. by vm_compute. Qed.

Lemma ycubjE f : (f < 48)%N ->
  [&& PArray.get plii (of_nat f) == of_nat (nth 0%N plin f),
      PArray.get toffi (of_nat f) == of_nat (nth 0%N toffn f),
      PArray.get lofsi (of_nat f) == of_nat (nth 0%N lofsn f),
      (nth 0%N plin f < 20)%N
    & (nth 0%N toffn f <= 120)%N].
Proof.
move=> hf; have /andP[/allP h _] := ycubjCP.
by apply: h; rewrite mem_iota add0n leq0n hf.
Qed.

Lemma laycombE i : (i < 48)%N ->
  PArray.get laycomb (of_nat i) = of_nat (nth 0%N (cflatp ++ elay) i).
Proof.
move=> hi; have /andP[_ /allP h] := ycubjCP.
by apply/eqP; apply: h; rewrite mem_iota add0n leq0n hi.
Qed.

Definition laycombB : bool :=
  (let c := cflatp ++ elay in
   all (fun i => (nth 0%N c i < 48)%N) (iota 0 48)).

Lemma laycombBP : laycombB. Proof. by vm_compute. Qed.

Lemma laycombBE i : (i < 48)%N -> (nth 0%N (cflatp ++ elay) i < 48)%N.
Proof.
move=> hi; have /allP h := laycombBP.
by apply: h; rewrite mem_iota add0n leq0n hi.
Qed.

Lemma plinE f : (f < 48)%N ->
  nth 0%N plin f = (if inC f then cposn f else (8 + eposn f)%N).
Proof.
move=> hf; rewrite /plin (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma toffnE f : (f < 48)%N ->
  nth 0%N toffn f
  = (if inC f then (cslotn f * 24)%N else (72 + eslt f * 24)%N).
Proof.
move=> hf; rewrite /toffn (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma lofsnE f : (f < 48)%N ->
  nth 0%N lofsn f = (if inC f then 0%N else 24%N).
Proof.
move=> hf; rewrite /lofsn (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

(* the turn table on a corner and on an edge, with the half chosen *)
Lemma tturn_val3 u g : (u < 3)%N -> (g < 24)%N ->
  nth 0%N tturnn (u * 24 + g)%N = (g - g %% 3 + (g %% 3 + u) %% 3)%N.
Proof.
move=> hu hg; have h := @tturn_val 0 u g isT hu hg.
by move: h; rewrite mul0n add0n /= => ->.
Qed.

Lemma tturn_val2 u g : (u < 2)%N -> (g < 24)%N ->
  nth 0%N tturnn (72 + u * 24 + g)%N = (g - g %% 2 + (g %% 2 + u) %% 2)%N.
Proof.
move=> hu hg; have hu3 : (u < 3)%N by apply: (leq_trans hu).
have h := @tturn_val 1 u g isT hu3 hg.
by move: h; rewrite mul1n /= => ->.
Qed.

(* ---- where a facelet is written ------------------------------------------ *)

Definition hpos (y : arr) (f : int) : int :=
  PArray.get laycomb
    (PArray.get lofsi f
     + PArray.get tturni (PArray.get toffi f
                          + PArray.get y (PArray.get plii f))).

Lemma n48_small : (48 < nwB)%N. Proof. by apply: (@ltn_nwB 6). Qed.

(* and it is where the cube the twenty name sends it *)
Lemma hposE y f : (f < 48)%N -> yoki y -> yok (a2y y) ->
  to_nat (hpos y (of_nat f)) = nth 0%N (cub2tab (a2y y)) f.
Proof.
move=> hf /allP hy hyk.
have /and5P[/eqP hpl /eqP htf /eqP hlf hpl20 htf120] := ycubjE hf.
have h144 : (144 < nwB)%N by apply: (@ltn_nwB 8).
have h48 : (48 < nwB)%N := n48_small.
rewrite /hpos hpl htf hlf.
have hg : (to_nat (PArray.get y (of_nat (nth 0%N plin f))) < 24)%N.
  by apply: hy; rewrite mem_iota add0n leq0n hpl20.
have hsum : (nth 0%N toffn f
             + to_nat (PArray.get y (of_nat (nth 0%N plin f))) < 144)%N.
  by apply: (@leq_ltn_trans (120 + 23)%N);
     [apply: leq_add => //; rewrite -ltnS | ].
have hsumb : (nth 0%N toffn f
              + to_nat (PArray.get y (of_nat (nth 0%N plin f))) < nwB)%N
  by apply: (ltn_trans hsum h144).
have htfb : (nth 0%N toffn f < nwB)%N
  by apply: (leq_ltn_trans (leq_addr _ _) hsumb).
have hA : (of_nat (nth 0%N toffn f)
           + PArray.get y (of_nat (nth 0%N plin f)))%uint63
        = of_nat (nth 0%N toffn f
                  + to_nat (PArray.get y (of_nat (nth 0%N plin f))))%N.
  by apply: to_nat_inj; rewrite of_natK // to_nat_add of_natK.
rewrite hA.
have /andP[/eqP ht htl] := tturniE hsum.
rewrite ht.
have hlb : (nth 0%N lofsn f <= 24)%N by rewrite lofsnE //; case: (inC f).
set V := nth 0%N tturnn (nth 0%N toffn f
           + to_nat (PArray.get y (of_nat (nth 0%N plin f)))).
have h24b : (24 < nwB)%N by apply: (ltn_trans (_ : (24 < 48)%N) h48).
have hVb : (V < nwB)%N by apply: (ltn_trans htl h24b).
have hlfb : (nth 0%N lofsn f < nwB)%N by apply: (leq_ltn_trans hlb h24b).
have hl48 : (nth 0%N lofsn f + V < 48)%N.
  by apply: (@leq_ltn_trans (24 + 23)%N);
     [apply: leq_add => //; rewrite -ltnS | ].
have hl48b : (nth 0%N lofsn f + V < nwB)%N by apply: (ltn_trans hl48 h48).
have hB : (of_nat (nth 0%N lofsn f) + of_nat V)%uint63
        = of_nat (nth 0%N lofsn f + V)%N.
  by apply: to_nat_inj; rewrite of_natK // to_nat_add !of_natK.
rewrite hB laycombE // of_natK; last first.
  by apply: (ltn_trans (laycombBE hl48) h48).
rewrite (cub2tab_nth hf hyk).
have hsc : seq.size cflatp = 24%N by vm_compute.
have /andP[/allP hyc /allP hye] := hyk.
case hcf : (inC f).
  have /andP[hp8 hs3] := claybd hf hcf.
  have hp20 : (cposn f < 20)%N by apply: (leq_trans hp8).
  have hg2 : (to_nat (PArray.get y (of_nat (cposn f))) < 24)%N.
    by apply: hy; rewrite mem_iota add0n leq0n hp20.
  rewrite /V (plinE hf) (toffnE hf) (lofsnE hf) hcf add0n (tturn_val3 hs3 hg2).
  rewrite nth_cat hsc.
  have hidx : (to_nat (PArray.get y (of_nat (cposn f)))
               - to_nat (PArray.get y (of_nat (cposn f))) %% 3
               + (to_nat (PArray.get y (of_nat (cposn f))) %% 3 + cslotn f)
                 %% 3
              = ycg (a2y y) (cposn f) * 3
                + (cslotn f + ytw (a2y y) (cposn f)) %% 3)%N.
    rewrite /ycg /ytw (a2y_nth _ hp20); congr (_ + _)%N.
      by rewrite {1}(divn_eq (to_nat (PArray.get y (of_nat (cposn f)))) 3)
                 addnK.
    by rewrite addnC.
  rewrite hidx.
  have hych : (ycg (a2y y) (cposn f) < 8)%N.
    by apply: hyc; rewrite mem_iota add0n leq0n hp8.
  have hix : (ycg (a2y y) (cposn f) * 3
              + (cslotn f + ytw (a2y y) (cposn f)) %% 3 < 24)%N.
    apply: (@leq_trans ((ycg (a2y y) (cposn f)).+1 * 3)%N).
      by rewrite mulSn addnC ltn_add2r ltn_mod.
    by rewrite -[24%N]/(8 * 3)%N leq_mul2r hych orbT.
  by rewrite hix.
have hef : inE f by have /orP[hc|//] := ckindAE hf; rewrite hc in hcf.
have /andP[hq12 hl2] := elaybd hf hef.
have hq20 : (8 + eposn f < 20)%N by rewrite ltn_add2l.
have hg2 : (to_nat (PArray.get y (of_nat (8 + eposn f))) < 24)%N.
  by apply: hy; rewrite mem_iota add0n leq0n hq20.
rewrite /V (plinE hf) (toffnE hf) (lofsnE hf) hcf (tturn_val2 hl2 hg2).
rewrite nth_cat hsc.
have hidx : (to_nat (PArray.get y (of_nat (8 + eposn f)))
             - to_nat (PArray.get y (of_nat (8 + eposn f))) %% 2
             + (to_nat (PArray.get y (of_nat (8 + eposn f))) %% 2 + eslt f)
               %% 2
            = yeg (a2y y) (eposn f) * 2
              + (eslt f + yfl (a2y y) (eposn f)) %% 2)%N.
  rewrite /yeg /yfl (a2y_nth _ hq20); congr (_ + _)%N.
    by rewrite {1}(divn_eq (to_nat (PArray.get y (of_nat (8 + eposn f)))) 2)
               addnK.
  by rewrite addnC.
rewrite hidx.
have -> : (24 + (yeg (a2y y) (eposn f) * 2
                 + (eslt f + yfl (a2y y) (eposn f)) %% 2) < 24)%N = false
  by rewrite ltnNge leq_addr.
by rewrite addKn.
Qed.

(* ---- and the array IS the table the run carries -------------------------- *)

Lemma y2tiE y : y2ti y = foldi 48 0%uint63
                          (fun f a => PArray.set a (hpos y f) f)
                          (PArray.make nfi 0%uint63).
Proof. by []. Qed.

Lemma len_mk48 : to_nat (PArray.length (PArray.make nfi 0%uint63)) = 48%N.
Proof. by rewrite length_makeE; vm_compute. Qed.

(* WRITING f WHERE THE CUBE SENDS IT GIVES THE INVERSE, and that is sound     *)
(* because the cube is a permutation -- which is the half of cubok that is    *)
(* not about places.  Every facelet is hit exactly once, so nothing is left   *)
(* at its default.                                                            *)
Lemma ti2t_y2ti y : yoki y -> cubok (a2y y) ->
  ti2t flast (y2ti y) = cub2tabR (a2y y).
Proof.
move=> hyi /andP[hyk htok].
have h48 : (48 < nwB)%N := n48_small.
have /and3P[/eqP hsz hall hu] := htok.
have hcl : forall i : int, (to_nat i < 48)%N -> (to_nat (hpos y i) < 48)%N.
  move=> i hi.
  have hib : (to_nat i < nwB)%N by apply: (ltn_trans hi).
  have he : i = of_nat (to_nat i) by apply: to_nat_inj; rewrite of_natK.
  rewrite {1}he (hposE hi hyi hyk).
  by have /allP h := hall; apply: h; rewrite mem_nth // hsz.
have hinj : forall i j : int, (to_nat i < 48)%N -> (to_nat j < 48)%N ->
    hpos y i = hpos y j -> i = j.
  move=> i j hi hj he.
  have hib : (to_nat i < nwB)%N by apply: (ltn_trans hi).
  have hjb : (to_nat j < nwB)%N by apply: (ltn_trans hj).
  have e1 : i = of_nat (to_nat i) by apply: to_nat_inj; rewrite of_natK.
  have e2 : j = of_nat (to_nat j) by apply: to_nat_inj; rewrite of_natK.
  have ha := hposE hi hyi hyk.
  have hb := hposE hj hyi hyk.
  rewrite -e1 in ha; rewrite -e2 in hb.
  apply: to_nat_inj; apply/eqP.
  rewrite -(nth_uniq 0%N _ _ hu) ?hsz //.
  by rewrite -ha -hb he.
apply: (@eq_from_nth _ 0%N).
  by rewrite size_ti2t /cub2tabR /inv_tab seq.size_map size_iota.
rewrite size_ti2t => p hp.
have hpb : (p < nwB)%N by apply: (ltn_trans hp).
have hmem : p \in cub2tab (a2y y) by apply: (tab_memE htok hp).
set f := index p (cub2tab (a2y y)).
have hf48 : (f < 48)%N by rewrite /f -hsz index_mem.
have hfb : (f < nwB)%N by apply: (ltn_trans hf48).
have hnf : nth 0%N (cub2tab (a2y y)) f = p by rewrite /f nth_index.
have hhf : hpos y (of_nat f) = of_nat p.
  apply: to_nat_inj; rewrite of_natK //.
  by rewrite (hposE hf48 hyi hyk) hnf.
rewrite nth_ti2t // -hhf y2tiE.
rewrite (@get_foldi_wr (hpos y) 48 0%uint63 (of_nat f)
                       (PArray.make nfi 0%uint63)).
- rewrite (of_natK f hfb) /cub2tabR /inv_tab (nth_map 0%N);
    last by rewrite size_iota.
  by rewrite nth_iota ?add0n.
- by rewrite to_nat_0 add0n; exact: h48.
- move=> i; rewrite to_nat_0 add0n => /andP[_ hi].
  by apply/nltbP; rewrite len_mk48; apply: hcl.
- move=> i j; rewrite to_nat_0 add0n => /andP[_ hi] /andP[_ hj].
  by apply: hinj.
by rewrite to_nat_0 add0n (of_natK f hfb) leq0n hf48.
Qed.
