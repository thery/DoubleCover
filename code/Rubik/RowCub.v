(* =========================================================================  *)
(*  RowCub.v -- a position as twenty cubies, and the cube it names.           *)
(* =========================================================================  *)

(* WHY.  MEASURED at depth twelve: the search is 17.8 s carrying the forty    *)
(* eight entry facelet table, 8.4 carrying twenty numbers, and 5.2 carrying   *)
(* nothing.  So the position is 12.6 s of the 17.8 and two thirds of that     *)
(* would go.                                                                  *)
(*                                                                            *)
(* WHAT IS NEEDED.  RowRun asks seven things of whatever the search carries,  *)
(* and the one that bites is that a move on the position is the move on the   *)
(* cube it names.  So the twenty numbers have to NAME a cube, which means     *)
(* orientation: a corner sits at a place turned by nought, one or two, and an *)
(* edge flipped or not.                                                       *)
(*                                                                            *)
(* AND THE BUILDER IS ALREADY HERE.  RowMemb's `part' sends the facelet at    *)
(* place p, slot s, to the facelet at place u p, SAME SLOT.  Turning is that  *)
(* with the slot moved on: s becomes s + the turn, round the place.  `partt'  *)
(* below is `part' with that one argument added.                              *)
(*                                                                            *)
(* THE EDGES NEEDED A NEW LAYOUT.  RowMemb splits them into the outer eight   *)
(* and the middle four, which only means anything inside H -- a move takes an *)
(* edge from one to the other.  elay is the twelve in one.                    *)
(*                                                                            *)
(* NOTHING HERE IS PROVED YET.  What is checked is that reading a table into  *)
(* twenty numbers and building it back gives the table again, for the         *)
(* identity and for all eighteen moves.                                       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import Lehmer RowTabP RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation arr := (PArray.array int).

(* ---- the twelve edges as one layout -------------------------------------- *)

Definition elay : seq nat :=
  flatten [seq [:: nth 0%N eprim p; nth 0%N esec p] | p <- iota 0 12].

Definition inE (f : nat) : bool := inU f || inM f.

Definition elayok : bool := layok elay 2 12 inE eposn eslt.

Lemma elayokC : elayok. Proof. by vm_compute. Qed.

(* ---- a part, with the slot turned ---------------------------------------- *)

(* RowMemb's part, with tw added: the facelet at place p slot s goes to the   *)
(* facelet at place u p, slot s plus the turn of p, round the place.          *)
Definition partt (lay : seq nat) (nsl : nat) (inL : nat -> bool)
                 (plc slt u tw : nat -> nat) : seq nat :=
  mkseq (fun f =>
           if inL f
           then nth 0%N lay (u (plc f) * nsl + (slt f + tw (plc f)) %% nsl)%N
           else f)
        48.

(* ---- twenty numbers ------------------------------------------------------ *)

(* place p under eight holds three times a corner plus its turn; place eight  *)
(* plus q holds twice an edge plus its flip.                                  *)
Definition ycg (y : seq nat) (p : nat) : nat := (nth 0%N y p %/ 3)%N.
Definition ytw (y : seq nat) (p : nat) : nat := (nth 0%N y p %% 3)%N.
Definition yeg (y : seq nat) (q : nat) : nat := (nth 0%N y (8 + q)%N %/ 2)%N.
Definition yfl (y : seq nat) (q : nat) : nat := (nth 0%N y (8 + q)%N %% 2)%N.

(* the cube the twenty name: the corners moved and turned, then the edges     *)
Definition cub2tab (y : seq nat) : seq nat :=
  comp_tab (partt cflatp 3 inC cposn cslotn (ycg y) (ytw y))
           (partt elay 2 inE eposn eslt (yeg y) (yfl y)).

(* and the twenty a cube gives: at the primary facelet of each place, which   *)
(* cubie is there and how it lies                                             *)
Definition tab2cub (t : seq nat) : seq nat :=
  [seq (if p < 8 then
          let f := nth 0%N t (nth 0%N cflatp (3 * p)%N) in
          (3 * cposn f + cslotn f)%N
        else
          let f := nth 0%N t (nth 0%N eprim (p - 8)%N) in
          (2 * eposn f + eslt f)%N)
   | p <- iota 0 20].

(* ---- what is checked ----------------------------------------------------- *)

(* read a table into twenty numbers and build it back: the identity, and all  *)
(* eighteen moves.                                                            *)
Definition cubrtC : bool :=
  all (fun k => cub2tab (tab2cub (ti2t flast (mvi (of_nat k))))
                == ti2t flast (mvi (of_nat k)))
      (iota 0 18).

Lemma cubrtCP : cubrtC. Proof. by vm_compute. Qed.

(* ---- a move on the twenty ------------------------------------------------ *)

(* A MOVE'S OWN TWENTY ARE THE STEP TABLE.  At place p it says which place    *)
(* the cubie comes from and how far it is turned on the way, and that is      *)
(* what tab2cub reads off it.  Stepping is then one lookup and one addition   *)
(* round the place, twenty of each, where the table is forty eight of each.   *)
(*                                                                            *)
(* IT IS THE INVERSE THAT IS WANTED.  comp_tab t1 t2 is t2 after t1 and ptM   *)
(* turns it into pt t1 * pt t2, so composing the move ON THE RIGHT -- which   *)
(* is what RowRun asks -- means looking the cubie up through the move undone. *)
Definition ystepm (m y : seq nat) : seq nat :=
  [seq (if p < 8 then
          let v := nth 0%N m p in
          (3 * ycg y (v %/ 3)%N + (ytw y (v %/ 3)%N + v %% 3) %% 3)%N
        else
          let v := nth 0%N m p in
          (2 * yeg y (v %/ 2)%N + (yfl y (v %/ 2)%N + v %% 2) %% 2)%N)
   | p <- iota 0 20].

Definition ymv  (k : nat) : seq nat := tab2cub (ti2t flast (mvi (of_nat k))).
Definition ymvv (k : nat) : seq nat :=
  tab2cub (inv_tab flast (ti2t flast (mvi (of_nat k)))).

Definition ystep (y : seq nat) (k : nat) : seq nat := ystepm (ymv k) y.
Definition zstep (y : seq nat) (k : nat) : seq nat := ystepm (ymvv k) y.

(* ---- and the check that it is the move, on all eighteen by eighteen ------- *)

Definition ystepC : bool :=
  all (fun j => all (fun k =>
      cub2tab (ystep (tab2cub (ti2t flast (mvi (of_nat j)))) k)
      == comp_tab (ti2t flast (mvi (of_nat k))) (ti2t flast (mvi (of_nat j))))
      (iota 0 18)) (iota 0 18).

Definition zstepC : bool :=
  all (fun j => all (fun k =>
      cub2tab (zstep (tab2cub (ti2t flast (mvi (of_nat j)))) k)
      == comp_tab (ti2t flast (mvi (of_nat j))) (ti2t flast (mvi (of_nat k))))
      (iota 0 18)) (iota 0 18).

(* the move played on the labels rather than on the places *)
Definition ystepl (m y : seq nat) : seq nat :=
  [seq (if p < 8 then
          let v := nth 0%N m p in
          (3 * ycg y p + (ytw y p + v %% 3) %% 3)%N
        else
          let v := nth 0%N m p in
          (2 * yeg y (p - 8)%N + (yfl y (p - 8)%N + v %% 2) %% 2)%N)
   | p <- iota 0 20].

Definition wstepC : bool :=
  all (fun j => all (fun k =>
      cub2tab (ystepl (ymv k) (tab2cub (ti2t flast (mvi (of_nat j)))))
      == comp_tab (ti2t flast (mvi (of_nat j))) (ti2t flast (mvi (of_nat k))))
      (iota 0 18)) (iota 0 18).

Definition vstepC : bool :=
  all (fun j => all (fun k =>
      cub2tab (ystepl (ymvv k) (tab2cub (ti2t flast (mvi (of_nat j)))))
      == comp_tab (ti2t flast (mvi (of_nat j))) (ti2t flast (mvi (of_nat k))))
      (iota 0 18)) (iota 0 18).

(* THE BUILDER IS THE INVERSE ONE, as memb2tab is inv_tab of membinv.  From  *)
(* cub2tab (ystep y k) = comp_tab (move k) (cub2tab y), inverting both sides  *)
(* turns the move round: inv (cub2tab (ystep y k)) = comp_tab (inv (cub2tab   *)
(* y)) (inv (move k)).  So stepping by the move UNDONE composes the move on   *)
(* the right, which is what RowRun asks.                                     *)
Definition cub2tabR (y : seq nat) : seq nat := inv_tab flast (cub2tab y).
Definition tab2cubR (t : seq nat) : seq nat := tab2cub (inv_tab flast t).

Definition rstepC : bool :=
  all (fun j => all (fun k =>
      cub2tabR (zstep (tab2cubR (ti2t flast (mvi (of_nat j)))) k)
      == comp_tab (ti2t flast (mvi (of_nat j))) (ti2t flast (mvi (of_nat k))))
      (iota 0 18)) (iota 0 18).

Eval vm_compute in (ystepC, rstepC).

(* ---- reading a part, and reading the cube ------------------------------- *)

(* the foundation of everything below: what a part does to one facelet *)
Lemma parttE lay nsl inL plc slt u tw f : (f < 48)%N ->
  nth 0%N (partt lay nsl inL plc slt u tw) f
  = if inL f
    then nth 0%N lay (u (plc f) * nsl + (slt f + tw (plc f)) %% nsl)%N
    else f.
Proof. by move=> hf; rewrite /partt nth_mkseq. Qed.

Lemma size_partt lay nsl inL plc slt u tw :
  seq.size (partt lay nsl inL plc slt u tw) = 48%N.
Proof. by rewrite /partt size_mkseq. Qed.

(* and what the two parts together do to one facelet *)
Lemma cub2tabE y f : (f < 48)%N ->
  nth 0%N (cub2tab y) f
  = nth 0%N (partt elay 2 inE eposn eslt (yeg y) (yfl y))
            (nth 0%N (partt cflatp 3 inC cposn cslotn (ycg y) (ytw y)) f).
Proof.
move=> hf; rewrite /cub2tab /comp_tab (nth_map 0%N) ?size_partt //.
Qed.

(* ---- what a move does to a place, and to a slot -------------------------- *)

(* THE TWO FACTS THE STEP LEMMA NEEDS.  A move sends the three facelets of a  *)
(* corner place to the three of one place, and shifts their slot by the same  *)
(* amount; and the same for the two facelets of an edge place.  HCorner and   *)
(* HEdge prove this in general; here it is eighteen moves by forty eight      *)
(* facelets, so it is asked rather than argued.                               *)
Definition mvt' (k : nat) : seq nat := ti2t flast (mvi (of_nat k)).

Definition cmvC : bool :=
  all (fun k =>
    all (fun f =>
      inC f ==>
      (let g := nth 0%N (mvt' k) f in
       let h := nth 0%N (mvt' k) (nth 0%N cflatp (3 * cposn f)%N) in
       (cposn g == cposn h) && (cslotn g == (cslotn f + cslotn h) %% 3)%N))
      (iota 0 48))
    (iota 0 18).

Definition emvC : bool :=
  all (fun k =>
    all (fun f =>
      inE f ==>
      (let g := nth 0%N (mvt' k) f in
       let h := nth 0%N (mvt' k) (nth 0%N eprim (eposn f)) in
       (eposn g == eposn h) && (eslt g == (eslt f + eslt h) %% 2)%N))
      (iota 0 48))
    (iota 0 18).

Lemma cmvCP : cmvC. Proof. by vm_compute. Qed.
Lemma emvCP : emvC. Proof. by vm_compute. Qed.

(* ---- what the layouts say, one index at a time --------------------------- *)

(* the layout read forwards: index i holds a facelet of place i / nsl at slot *)
(* i mod nsl                                                                  *)
Lemma clayE i : (i < 24)%N ->
  [&& (nth 0%N cflatp i < 48)%N, inC (nth 0%N cflatp i),
      cposn (nth 0%N cflatp i) == (i %/ 3)%N
    & cslotn (nth 0%N cflatp i) == (i %% 3)%N].
Proof.
move=> hi; have /and4P[_ /allP h _ _] := clayokC.
by apply: h; rewrite mem_iota add0n leq0n hi.
Qed.

Lemma elayE i : (i < 24)%N ->
  [&& (nth 0%N elay i < 48)%N, inE (nth 0%N elay i),
      eposn (nth 0%N elay i) == (i %/ 2)%N
    & eslt (nth 0%N elay i) == (i %% 2)%N].
Proof.
move=> hi; have /and4P[_ /allP h _ _] := elayokC.
by apply: h; rewrite mem_iota add0n leq0n hi.
Qed.

(* and backwards: a facelet is at its own place and slot *)
Lemma clayB f : (f < 48)%N -> inC f ->
  nth 0%N cflatp (cposn f * 3 + cslotn f)%N = f.
Proof.
move=> hf hc; have /and4P[_ _ /allP h _] := clayokC.
have hm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
by have /implyP/(_ hc)/eqP := h _ hm.
Qed.

Lemma elayB f : (f < 48)%N -> inE f ->
  nth 0%N elay (eposn f * 2 + eslt f)%N = f.
Proof.
move=> hf hc; have /and4P[_ _ /allP h _] := elayokC.
have hm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
by have /implyP/(_ hc)/eqP := h _ hm.
Qed.

(* and the bounds a facelet's place and slot obey *)
Lemma claybd f : (f < 48)%N -> inC f -> (cposn f < 8)%N && (cslotn f < 3)%N.
Proof.
move=> hf hc; have /and4P[_ _ _ /allP h] := clayokC.
have hm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
by have /implyP/(_ hc) := h _ hm.
Qed.

Lemma elaybd f : (f < 48)%N -> inE f -> (eposn f < 12)%N && (eslt f < 2)%N.
Proof.
move=> hf hc; have /and4P[_ _ _ /allP h] := elayokC.
have hm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
by have /implyP/(_ hc) := h _ hm.
Qed.

(* ---- a move keeps a corner a corner and an edge an edge ------------------ *)

Definition mvkC : bool :=
  all (fun k =>
    all (fun f => (inC f ==> inC (nth 0%N (mvt' k) f))
               && (inE f ==> inE (nth 0%N (mvt' k) f))
               && (nth 0%N (mvt' k) f < 48)%N)
      (iota 0 48))
    (iota 0 18).

Lemma mvkCP : mvkC. Proof. by vm_compute. Qed.

Lemma mvkE k f : (k < 18)%N -> (f < 48)%N ->
  [&& inC f ==> inC (nth 0%N (mvt' k) f),
      inE f ==> inE (nth 0%N (mvt' k) f)
    & (nth 0%N (mvt' k) f < 48)%N].
Proof.
move=> hk hf; have /allP h := mvkCP.
have hkm : k \in iota 0 18 by rewrite mem_iota add0n leq0n hk.
have hfm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
have /allP h2 := h _ hkm.
by have /andP[/andP[a b] c] := h2 _ hfm; rewrite a b c.
Qed.

(* ---- a facelet is a corner or an edge, never both ------------------------ *)

Definition ckindC : bool :=
  all (fun f => (inC f ==> ~~ inE f) && (inE f ==> ~~ inC f)) (iota 0 48).

Lemma ckindCP : ckindC. Proof. by vm_compute. Qed.

Lemma ckindE f : (f < 48)%N -> (inC f ==> ~~ inE f) && (inE f ==> ~~ inC f).
Proof.
move=> hf; have /allP h := ckindCP.
by apply: h; rewrite mem_iota add0n leq0n hf.
Qed.

(* ---- every facelet is a corner one or an edge one ------------------------ *)

(* eight corners of three and twelve edges of two is forty eight, so there is *)
(* no third kind and the step lemma has two cases and not three.              *)
Definition ckindA : bool := all (fun f => inC f || inE f) (iota 0 48).

Lemma ckindAP : ckindA. Proof. by vm_compute. Qed.

Lemma ckindAE f : (f < 48)%N -> inC f || inE f.
Proof.
move=> hf; have /allP h := ckindAP.
by apply: h; rewrite mem_iota add0n leq0n hf.
Qed.

(* the primary facelet of an edge place is an edge facelet *)
Definition eprimC : bool :=
  all (fun q => (nth 0%N eprim q < 48)%N && inE (nth 0%N eprim q)) (iota 0 12).

Lemma eprimCP : eprimC. Proof. by vm_compute. Qed.

Lemma eprimE q : (q < 12)%N ->
  (nth 0%N eprim q < 48)%N && inE (nth 0%N eprim q).
Proof.
move=> hq; have /allP h := eprimCP.
by apply: h; rewrite mem_iota add0n leq0n hq.
Qed.

(* ---- a move's own twenty name places ------------------------------------- *)

Definition ymvbd : bool :=
  all (fun k => all (fun p => (nth 0%N (ymv k) p < 24)%N) (iota 0 20))
      (iota 0 18).

Lemma ymvbdP : ymvbd. Proof. by vm_compute. Qed.

Lemma ymvbdE k p : (k < 18)%N -> (p < 20)%N -> (nth 0%N (ymv k) p < 24)%N.
Proof.
move=> hk hp; have /allP h := ymvbdP.
have hkm : k \in iota 0 18 by rewrite mem_iota add0n leq0n hk.
have hpm : p \in iota 0 20 by rewrite mem_iota add0n leq0n hp.
by have /allP h2 := h _ hkm; apply: h2.
Qed.

(* ---- the step keeps the twenty naming places ----------------------------- *)

(* the twenty have to name places: a corner place under eight, an edge place  *)
(* under twelve *)
Definition yok (y : seq nat) : bool :=
  all (fun p => ycg y p < 8)%N (iota 0 8)
  && all (fun q => yeg y q < 12)%N (iota 0 12).

Lemma yok_step y k : (k < 18)%N -> yok y -> yok (ystep y k).
Proof.
(* THE LEMMA SUPPLIED, NOT LOOKED FOR.  `apply: ymvbdE' with the bound left  *)
(* to done lets /= unfold ymv k into a twelve entry literal of move reads,   *)
(* and the tactic does not come back.                                        *)
move=> hk /andP[/allP hc /allP he]; apply/andP; split; apply/allP => p;
  rewrite mem_iota add0n leq0n /= => hp; last first.
  have hp20 : (8 + p < 20)%N by rewrite ltn_add2l.
  rewrite /yeg /ystep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n.
  have -> : (8 + p < 8)%N = false by rewrite ltnNge leq_addr.
  rewrite mulnC divnMDl //.
  have -> : (((yfl y (nth 0%N (ymv k) (8 + p) %/ 2)
               + nth 0%N (ymv k) (8 + p) %% 2) %% 2) %/ 2 = 0)%N
    by apply: divn_small; rewrite ltn_mod.
  rewrite addn0; apply: he; rewrite mem_iota add0n leq0n /= ltn_divLR //.
  exact: (ymvbdE hk hp20).
have hp20 : (p < 20)%N by apply: (leq_trans hp).
rewrite /ycg /ystep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n hp.
rewrite mulnC divnMDl //.
have -> : (((ytw y (nth 0%N (ymv k) p %/ 3) + nth 0%N (ymv k) p %% 3) %% 3)
           %/ 3 = 0)%N by apply: divn_small; rewrite ltn_mod.
rewrite addn0; apply: hc; rewrite mem_iota add0n leq0n /= ltn_divLR //.
exact: (ymvbdE hk hp20).
Qed.

(* ---- reading the stepped twenty ------------------------------------------ *)

(* the four halves of the step, read back one place at a time *)
Lemma ycg_step y k p : (k < 18)%N -> (p < 8)%N ->
  ycg (ystep y k) p = ycg y (nth 0%N (ymv k) p %/ 3).
Proof.
move=> hk hp; have hp20 : (p < 20)%N by apply: (leq_trans hp).
rewrite /ycg /ystep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n hp.
rewrite mulnC divnMDl //.
have -> : (((ytw y (nth 0%N (ymv k) p %/ 3) + nth 0%N (ymv k) p %% 3) %% 3)
           %/ 3 = 0)%N by apply: divn_small; rewrite ltn_mod.
by rewrite addn0.
Qed.

Lemma ytw_step y k p : (k < 18)%N -> (p < 8)%N ->
  ytw (ystep y k) p
  = ((ytw y (nth 0%N (ymv k) p %/ 3) + nth 0%N (ymv k) p %% 3) %% 3)%N.
Proof.
move=> hk hp; have hp20 : (p < 20)%N by apply: (leq_trans hp).
rewrite /ytw /ystep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n hp.
by rewrite mulnC modnMDl modn_mod.
Qed.

Lemma yeg_step y k q : (k < 18)%N -> (q < 12)%N ->
  yeg (ystep y k) q = yeg y (nth 0%N (ymv k) (8 + q)%N %/ 2).
Proof.
move=> hk hq; have hq20 : (8 + q < 20)%N by rewrite ltn_add2l.
rewrite /yeg /ystep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n.
have -> : (8 + q < 8)%N = false by rewrite ltnNge leq_addr.
rewrite mulnC divnMDl //.
have -> : (((yfl y (nth 0%N (ymv k) (8 + q) %/ 2)
             + nth 0%N (ymv k) (8 + q) %% 2) %% 2) %/ 2 = 0)%N
  by apply: divn_small; rewrite ltn_mod.
by rewrite addn0.
Qed.

Lemma yfl_step y k q : (k < 18)%N -> (q < 12)%N ->
  yfl (ystep y k) q
  = ((yfl y (nth 0%N (ymv k) (8 + q)%N %/ 2)
      + nth 0%N (ymv k) (8 + q)%N %% 2) %% 2)%N.
Proof.
move=> hk hq; have hq20 : (8 + q < 20)%N by rewrite ltn_add2l.
rewrite /yfl /ystep /ystepm (nth_map 0%N) ?size_iota // nth_iota // add0n.
have -> : (8 + q < 8)%N = false by rewrite ltnNge leq_addr.
by rewrite mulnC modnMDl modn_mod.
Qed.

(* ---- what a move's own twenty say ---------------------------------------- *)

Lemma ymvcE k p : (p < 8)%N ->
  nth 0%N (ymv k) p
  = (3 * cposn (nth 0%N (mvt' k) (nth 0%N cflatp (3 * p)%N))
     + cslotn (nth 0%N (mvt' k) (nth 0%N cflatp (3 * p)%N)))%N.
Proof.
move=> hp; have hp20 : (p < 20)%N by apply: (leq_trans hp).
by rewrite /ymv /tab2cub (nth_map 0%N) ?size_iota // nth_iota // add0n hp.
Qed.

Lemma ymveE k q : (q < 12)%N ->
  nth 0%N (ymv k) (8 + q)%N
  = (2 * eposn (nth 0%N (mvt' k) (nth 0%N eprim q))
     + eslt (nth 0%N (mvt' k) (nth 0%N eprim q)))%N.
Proof.
move=> hq; have hq20 : (8 + q < 20)%N by rewrite ltn_add2l.
rewrite /ymv /tab2cub (nth_map 0%N) ?size_iota // nth_iota // add0n.
have -> : (8 + q < 8)%N = false by rewrite ltnNge leq_addr.
by rewrite addKn.
Qed.

(* ---- and the two move facts, one facelet at a time ----------------------- *)

Lemma cmvE k f : (k < 18)%N -> (f < 48)%N -> inC f ->
  (cposn (nth 0%N (mvt' k) f)
   == cposn (nth 0%N (mvt' k) (nth 0%N cflatp (3 * cposn f)%N)))
  && (cslotn (nth 0%N (mvt' k) f)
      == (cslotn f
          + cslotn (nth 0%N (mvt' k) (nth 0%N cflatp (3 * cposn f)%N))) %% 3)%N.
Proof.
move=> hk hf hc; have /allP h := cmvCP.
have hkm : k \in iota 0 18 by rewrite mem_iota add0n leq0n hk.
have hfm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
by have /allP h2 := h _ hkm; have /implyP/(_ hc) := h2 _ hfm.
Qed.

Lemma emvE k f : (k < 18)%N -> (f < 48)%N -> inE f ->
  (eposn (nth 0%N (mvt' k) f)
   == eposn (nth 0%N (mvt' k) (nth 0%N eprim (eposn f))))
  && (eslt (nth 0%N (mvt' k) f)
      == (eslt f + eslt (nth 0%N (mvt' k) (nth 0%N eprim (eposn f)))) %% 2)%N.
Proof.
move=> hk hf hc; have /allP h := emvCP.
have hkm : k \in iota 0 18 by rewrite mem_iota add0n leq0n hk.
have hfm : f \in iota 0 48 by rewrite mem_iota add0n leq0n hf.
by have /allP h2 := h _ hkm; have /implyP/(_ hc) := h2 _ hfm.
Qed.

(* ---- the step lemma ------------------------------------------------------ *)

(* WHAT THE COMPUTATION ALREADY SAYS on the eighteen by eighteen, now for any *)
(* y that names places.  The move comes out on the LEFT here; cub2tabR turns  *)
(* it round, which is what RowRun asks.                                       *)
Lemma cub2tab_step y k : (k < 18)%N -> yok y ->
  cub2tab (ystep y k) = comp_tab (mvt' k) (cub2tab y).
Proof.
move=> hk hy; apply: (@eq_from_nth _ 0%N).
  by rewrite /cub2tab /comp_tab !size_map !size_iota.
rewrite {1}/cub2tab /comp_tab size_map size_partt => f hf.
rewrite -/(cub2tab _) cub2tabE // /comp_tab (nth_map 0%N)
        ?(size_ti2t flast) // -/(cub2tab _).
rewrite (parttE _ _ _ _ _ _ _ hf).
case hcf : (inC f); last first.
  (* the edge case, the same read with two slots in place of three.  The     *)
  (* corner part was already stripped above, so there is only one layer here. *)
  have hef : inE f by have /orP[hc|//] := ckindAE hf; rewrite hc in hcf.
  have /andP[hq12 hl2] := elaybd hf hef.
  have /andP[he0lt he0E] := eprimE hq12.
  have /and3P[_ hgE hglt] := mvkE hk he0lt.
  have /andP[hhq12 hhl2] := elaybd hglt (implyP hgE he0E).
  rewrite (parttE _ _ _ _ _ _ _ hf) hef.
  rewrite (yeg_step _ hk hq12) (yfl_step _ hk hq12) (ymveE k hq12).
  set h := nth 0%N (mvt' k) (nth 0%N eprim (eposn f)).
  have hdiv : ((2 * eposn h + eslt h) %/ 2 = eposn h)%N.
    by rewrite mulnC divnMDl // (divn_small hhl2) addn0.
  have hmod : ((2 * eposn h + eslt h) %% 2 = eslt h)%N.
    by rewrite mulnC modnMDl (modn_small hhl2).
  rewrite hdiv hmod.
  have /and3P[_ hgEi hglt2] := mvkE hk hf.
  have hgE2 : inE (nth 0%N (mvt' k) f) by apply: (implyP hgEi).
  have /andP[/eqP hgep /eqP hges] := emvE hk hf hef.
  have hgCf : inC (nth 0%N (mvt' k) f) = false.
    by apply/negbTE; have /andP[_ h2] := ckindE hglt2; apply: (implyP h2).
  rewrite (cub2tabE y hglt2) (parttE _ _ _ _ _ _ _ hglt2) hgCf.
  rewrite (parttE _ _ _ _ _ _ _ hglt2) hgE2 hgep hges.
  congr (nth 0%N elay _); congr (_ + _)%N.
  by rewrite modnDmr modnDml addnA addnAC.
have /andP[hp8 hs3] := claybd hf hcf.
have h3p : (3 * cposn f < 24)%N by rewrite -[24]/(3 * 8)%N ltn_mul2l /= hp8.
have /and4P[hc0lt hc0C _ _] := clayE h3p.
have /and3P[hgC _ hglt] := mvkE hk hc0lt.
have /andP[hhp8 hhs3] := claybd hglt (implyP hgC hc0C).
rewrite (ycg_step _ hk hp8) (ytw_step _ hk hp8) (ymvcE k hp8).
set h := nth 0%N (mvt' k) (nth 0%N cflatp (3 * cposn f)%N).
have hdiv : ((3 * cposn h + cslotn h) %/ 3 = cposn h)%N.
  by rewrite mulnC divnMDl // (divn_small hhs3) addn0.
have hmod : ((3 * cposn h + cslotn h) %% 3 = cslotn h)%N.
  by rewrite mulnC modnMDl (modn_small hhs3).
rewrite hdiv hmod.
have /andP[/allP hyc /allP hye] := hy.
have hych : (ycg y (cposn h) < 8)%N.
  by apply: hyc; rewrite mem_iota add0n leq0n hhp8.
have hi : (ycg y (cposn h) * 3
           + (cslotn f + (ytw y (cposn h) + cslotn h) %% 3) %% 3 < 24)%N.
  apply: (@leq_trans ((ycg y (cposn h)).+1 * 3)%N).
    by rewrite mulSn addnC ltn_add2r ltn_mod.
  by rewrite -[24]/(8 * 3)%N leq_mul2r hych orbT.
have /and4P[hilt hiC _ _] := clayE hi.
have /andP[hiE _] := ckindE hilt.
rewrite (parttE _ _ _ _ _ _ _ hilt) (negbTE (implyP hiE hiC)).
(* and now the same read on the other side, at the moved facelet *)
have /and3P[hgCi _ hglt2] := mvkE hk hf.
have hgC2 : inC (nth 0%N (mvt' k) f) by apply: (implyP hgCi); rewrite hcf.
have /andP[hgp8 hgs3] := claybd hglt2 hgC2.
have /andP[/eqP hgcp /eqP hgcs] := cmvE hk hf hcf.
rewrite (cub2tabE y hglt2) (parttE _ _ _ _ _ _ _ hglt2) hgC2 hgcp hgcs.
have hj : (ycg y (cposn h) * 3
           + ((cslotn f + cslotn h) %% 3 + ytw y (cposn h)) %% 3 < 24)%N.
  apply: (@leq_trans ((ycg y (cposn h)).+1 * 3)%N).
    by rewrite mulSn addnC ltn_add2r ltn_mod.
  by rewrite -[24]/(8 * 3)%N leq_mul2r hych orbT.
have /and4P[hjlt hjC _ _] := clayE hj.
have /andP[hjE _] := ckindE hjlt.
rewrite (parttE _ _ _ _ _ _ _ hjlt) (negbTE (implyP hjE hjC)).
(* the two indices are the same number: the turn can be added before or after *)
congr (nth 0%N cflatp _); congr (_ + _)%N.
by rewrite modnDmr modnDml addnA addnAC.
Qed.
