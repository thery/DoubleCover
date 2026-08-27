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
(* WHAT IS PROVED.  A move on the twenty is the move on the cube they name,   *)
(* for every twenty that name places.  The search steps by the move undone,   *)
(* which is again one of the eighteen, and that is the move composed on the   *)
(* right -- the one thing RowRun asks that is not a computation.  The root is *)
(* one computation.  What is checked and not proved is that reading a table   *)
(* into twenty numbers and building it back gives the table again.            *)

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

(* ---- the builder that turns the move round ------------------------------- *)

(* THE BUILDER IS THE INVERSE ONE, as memb2tab is inv_tab of membinv.  From   *)
(* cub2tab (ystep y k) = comp_tab (move k) (cub2tab y), inverting both sides  *)
(* turns the move round: inv (cub2tab (ystep y k)) = comp_tab (inv (cub2tab   *)
(* y)) (inv (move k)).  So stepping by the move UNDONE composes the move on   *)
(* the right, which is what RowRun asks.                                      *)
Definition cub2tabR (y : seq nat) : seq nat := inv_tab flast (cub2tab y).
Definition tab2cubR (t : seq nat) : seq nat := tab2cub (inv_tab flast t).

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

(* ---- one table, under two names ------------------------------------------ *)

(* The search reads a move out of an int63 array and RowFinal names the same  *)
(* eighteen tables as a list; below they are the same table, so the witness   *)
(* lemmas apply here unchanged.                                               *)
Definition mvtC : bool := all (fun k => mvt' k == mvt k) (iota 0 18).

Lemma mvtCP : mvtC. Proof. by vm_compute. Qed.

Lemma mvt'E k : (k < 18)%N -> mvt' k = mvt k.
Proof.
move=> hk; have /allP h := mvtCP.
by apply/eqP; apply: h; rewrite mem_iota add0n leq0n hk.
Qed.

(* ---- the move undone is a move too --------------------------------------- *)

(* THE STEP LEMMA COVERS THE MOVE UNDONE WITH NOTHING NEW.  The three turns   *)
(* of a face are each other's inverses, so undoing a move is playing another  *)
(* one of the eighteen.  kinv says which, and it is read off the tables       *)
(* rather than written down: it comes out swapping the quarter turns of each  *)
(* face and leaving the half turn alone.                                      *)
Definition kinv (k : nat) : nat := index (inv_tab flast (mvt k)) mtabs.

Definition kinvC : bool :=
  all (fun k => (kinv k < 18)%N && (mvt (kinv k) == inv_tab flast (mvt k)))
      (iota 0 18).

Lemma kinvCP : kinvC. Proof. by vm_compute. Qed.

Lemma kinvE k : (k < 18)%N ->
  (kinv k < 18)%N && (mvt (kinv k) == inv_tab flast (mvt k)).
Proof.
move=> hk; have /allP h := kinvCP.
by apply: h; rewrite mem_iota add0n leq0n hk.
Qed.

(* so the twenty of the move undone are the twenty of another move *)
Lemma ymvvE k : (k < 18)%N -> ymvv k = ymv (kinv k).
Proof.
move=> hk; have /andP[hi /eqP he] := kinvE hk.
by rewrite /ymvv /ymv -/(mvt' k) mvt'E // -he -mvt'E.
Qed.

Lemma zstepE y k : (k < 18)%N -> zstep y k = ystep y (kinv k).
Proof. by move=> hk; rewrite /zstep /ystep ymvvE. Qed.

Lemma cub2tab_zstep y k : (k < 18)%N -> yok y ->
  cub2tab (zstep y k) = comp_tab (mvt (kinv k)) (cub2tab y).
Proof.
move=> hk hy; have /andP[hi _] := kinvE hk.
by rewrite zstepE // cub2tab_step // mvt'E.
Qed.

(* ---- what the search carries --------------------------------------------- *)

(* NAMING PLACES IS NOT ENOUGH.  Twenty numbers that name places can name one *)
(* place twice, and then the cube they build is not a permutation and has no  *)
(* position at all.  The table being a permutation is therefore carried too,  *)
(* and a move keeps it because the step lemma makes it a composition.         *)
Definition cubok (y : seq nat) : bool := yok y && tab_ok flast (cub2tab y).

Lemma cubok_zstep y k : (k < 18)%N -> cubok y -> cubok (zstep y k).
Proof.
move=> hk /andP[hy ht]; have /andP[hi _] := kinvE hk.
apply/andP; split; first by rewrite zstepE //; apply: yok_step.
by rewrite cub2tab_zstep //; apply: tab_ok_comp => //; apply: mvt_ok.
Qed.

Import GroupScope.

(* ---- the position the twenty name, and the move on the right ------------- *)

(* WHAT RowRun ASKS OF A STEP, for the twenty.  Its xstep_pos wants the       *)
(* position after a step to be the position before it times the move, and     *)
(* this is that, with the position read through the inverse builder.          *)
Lemma pt_zstep y k : (k < 18)%N -> cubok y ->
  pt flast (cub2tabR (zstep y k)) = pt flast (cub2tabR y) * nth 1 moves k.
Proof.
move=> hk hc; have /andP[hy ht] := hc.
have /andP[hi /eqP hei] := kinvE hk.
have hmi := mvt_ok hi; have hm := mvt_ok hk.
have hcc : tab_ok flast (comp_tab (mvt (kinv k)) (cub2tab y)).
  by apply: tab_ok_comp.
rewrite /cub2tabR cub2tab_zstep // -(ptV hcc) -ptM // invMg -(ptV ht) mvtE //.
by congr (_ * _); rewrite hei -(ptV hm) invgK.
Qed.

(* ---- and where the row starts -------------------------------------------- *)

(* The root is one table, so what a general round trip would say about it is  *)
(* a computation: the twenty read off it are twenty that the step keeps, and  *)
(* they build the table back.                                                 *)
Definition yroot : seq nat := tab2cubR (ti2t flast repi).

Definition yrootC : bool := cubok yroot && (cub2tabR yroot == ti2t flast repi).

Lemma yrootCP : yrootC. Proof. by vm_compute. Qed.

(* ---- the twenty stepped, read back, is the table stepped ----------------- *)

(* TWO TABLES WITH THE SAME PERMUTATION ARE THE SAME TABLE.  Table.v gives    *)
(* pt of a composition and of an inverse but never says pt is injective, and  *)
(* that is what carries the step below from permutations down to tables.      *)
Lemma tab_pt_inj t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  pt flast t1 = pt flast t2 -> t1 = t2.
Proof.
move=> h1 h2 he.
have /and3P[/eqP s1 _ _] := h1; have /and3P[/eqP s2 _ _] := h2.
apply: (@eq_from_nth _ 0%N); first by rewrite s1 s2.
rewrite s1 => i hi.
have hii := inordK hi.
have e1 := ptE (inord i) h1; have e2 := ptE (inord i) h2.
rewrite hii in e1 e2.
have e4 : (inord (nth 0%N t1 i) : 'I_flast.+1) = inord (nth 0%N t2 i).
  by rewrite -e1 -e2 he.
have l1 : (nth 0%N t1 i < flast.+1)%N.
  by have /and3P[_ /allP a _] := h1; apply: a; rewrite mem_nth ?s1.
have l2 : (nth 0%N t2 i < flast.+1)%N.
  by have /and3P[_ /allP a _] := h2; apply: a; rewrite mem_nth ?s2.
by rewrite -(inordK l1) -(inordK l2) e4.
Qed.

(* AND THIS IS WHAT WIRES THE TWENTY IN.  Stepping the twenty and reading     *)
(* the table back is the table composed with the move, which is exactly the   *)
(* step RowInst carries on tables.  So everything RowInst proves of the       *)
(* table state -- the coordinate, the member at a leaf -- transfers by this   *)
(* one equation, and the search itself never builds the table.                *)
Lemma cub2tabR_zstep y k : (k < 18)%N -> cubok y ->
  cub2tabR (zstep y k) = comp_tab (cub2tabR y) (mvt k).
Proof.
move=> hk hc; have /andP[hy ht] := hc.
have /andP[hs hst] := cubok_zstep hk hc.
have hm := mvt_ok hk.
apply: tab_pt_inj; first exact: tab_ok_inv.
  by apply: tab_ok_comp => //; apply: tab_ok_inv.
by rewrite pt_zstep // -ptM ?tab_ok_inv // mvtE.
Qed.

(* ---- the cube the twenty name, one facelet at a time --------------------- *)

(* THE TWO PARTS DO NOT INTERFERE.  A facelet is a corner one or an edge one  *)
(* and never both, and each part leaves the other kind where it is, so the    *)
(* composition reads as one case and not two.                                 *)
Lemma cub2tab_nth Y f : (f < 48)%N -> yok Y ->
  nth 0%N (cub2tab Y) f
  = (if inC f
     then nth 0%N cflatp
            (ycg Y (cposn f) * 3 + (cslotn f + ytw Y (cposn f)) %% 3)
     else nth 0%N elay
            (yeg Y (eposn f) * 2 + (eslt f + yfl Y (eposn f)) %% 2))%N.
Proof.
move=> hf hy; rewrite cub2tabE // (parttE _ _ _ _ _ _ _ hf).
case hcf : (inC f); last first.
  have hef : inE f by have /orP[hc|//] := ckindAE hf; rewrite hc in hcf.
  by rewrite (parttE _ _ _ _ _ _ _ hf) hef.
have /andP[hp8 hs3] := claybd hf hcf.
have /andP[/allP hyc _] := hy.
have hych : (ycg Y (cposn f) < 8)%N.
  by apply: hyc; rewrite mem_iota add0n leq0n hp8.
have hi : (ycg Y (cposn f) * 3 + (cslotn f + ytw Y (cposn f)) %% 3 < 24)%N.
  apply: (@leq_trans ((ycg Y (cposn f)).+1 * 3)%N).
    by rewrite mulSn addnC ltn_add2r ltn_mod.
  by rewrite -[24]/(8 * 3)%N leq_mul2r hych orbT.
have /and4P[hilt hiC _ _] := clayE hi.
have /andP[hiE _] := ckindE hilt.
by rewrite (parttE _ _ _ _ _ _ _ hilt) (negbTE (implyP hiE hiC)).
Qed.
