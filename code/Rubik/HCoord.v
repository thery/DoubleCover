(* =========================================================================  *)
(*  HCoord.v -- Reid's three coordinates of a position, on facelet tables.    *)
(* =========================================================================  *)

(* A coset of Reid's subgroup H is a triple (e, cl, ct): where the four middle*)
(* slice edges sit and how they are flipped, 24 * 22 * 20 * 18 = 190080; which*)
(* four corner places hold the four U corners, 8 choose 4 = 70; and the corner*)
(* orientations, 3 ^ 7 = 2187.  The pruning table holds the distance of each  *)
(* such triple from the solved cube, and this file is how a position is turned*)
(* into its triple.                                                           *)
(*                                                                            *)
(* ocaml/rubik_h.ml is the specification, and hroots below is the check: the  *)
(* eighteen numbers it fixes are what `make hroots' prints.                   *)
(*                                                                            *)
(* THE TWO LABELLINGS ARE NOT THE SAME, and that is the trap this file exists *)
(* to close.  The edges agree: both orders are UR UF UL UB DR DF DL DB FR FL  *)
(* BL BR, and both call an edge flipped when its up-down or front-back sticker*)
(* has moved off that face.  The corners do not.  Reading off which faces move*)
(* each corner place, the places here are ULB UBR UFL URF DLF DFR DBL DRB and *)
(* the prototype's are URF UFL ULB UBR DFR DLF DBL DRB, so a place has to be  *)
(* renumbered by oc2r; and a corner's twist is counted the other way round, so*)
(* a slot d is the prototype's 3 - d.  Neither is a free choice: the table is *)
(* indexed by the prototype's numbers.                                        *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Moves Coordfs Phase1 HRoot.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* the sizes of the three coordinates, and of the flip                        *)
Definition n_e := 190080.
Definition n_cl := 70.
Definition n_ct := 2187.

(* the four slice cubies are the last four, and a corner has three slots      *)
Definition nslicec := 4.
Definition nslot := 3.

(* Every coordinate below reads u, the INVERSE of the position's table: the   *)
(* sticker now at a facelet is what says which cubie is there and how it lies.*)
Definition getn (u : arr) (f : nat) : nat := to_nat (PArray.get u (of_nat f)).

(* ---- the edges ----------------------------------------------------------- *)

(* which of the twelve places a facelet belongs to                            *)
Definition eposn (f : nat) : nat := index f (eprim ++ esec) %% nedge.

(* the cubie at place j, and whether it is flipped                            *)
Definition eplace (u : arr) (j : nat) : nat := eposn (getn u (nth 0%N eprim j)).
Definition eflipn (u : arr) (j : nat) : nat :=
  if getn u (nth 0%N eprim j) \in eprim then 0%N else 1%N.

(* where slice cubie 8 + i sits, twice the place plus its flip                *)
Definition eslot (u : arr) (i : nat) : nat :=
  foldl (fun s j => if eplace u j == (nedge - nslicec + i)%N
                    then (2 * j + eflipn u j)%N else s)
        0%N (iota 0 nedge).

(* The rank of the four places-with-flip, in the order the prototype uses: a  *)
(* place taken by one slice edge is taken in both its readings, which is why  *)
(* the radices fall by two -- 24, 22, 20, 18.                                 *)
Definition ecoordi (u : arr) : int :=
  (foldl (fun ru i => let: (r, used) := ru in
       let s := eslot u i in
       let p := (s %/ 2)%N in
       let idx := (2 * count (fun q => q \notin used) (iota 0 p))%N in
       (Uint63.add (Uint63.add (Uint63.mul r (of_nat (2 * nedge - 2 * i)%N))
                               (of_nat idx))
                   (of_nat (s %% 2)%N), p :: used))
     (0%uint63, [::]) (iota 0 nslicec)).1.

(* ---- the corners --------------------------------------------------------  *)

(* the prototype's corner places, as places here                              *)
Definition oc2r : seq nat := [:: 3; 2; 0; 1; 5; 4; 6; 7]%N.

Definition rplace (j : nat) : nat := nth 0%N oc2r j.

(* the cubie at the prototype's place j, and how far it is rotated there      *)
Definition cplace (u : arr) (j : nat) : nat :=
  cposn (getn u (nth 0%N cprim (rplace j))).
Definition ctwist (u : arr) (j : nat) : nat :=
  ((nslot - cslotn (getn u (nth 0%N cprim (rplace j)))) %% nslot)%N.

(* Which four places hold the U corners, ranked.  The U corners are the cubies*)
(* below four, in both labellings, because both put the U layer first.        *)
Definition clcoordi (u : arr) : int :=
  (foldl (fun ax j => let: (a, x) := ax in
       if (cplace u j < nslicec)%N
       then (Uint63.add a (of_nat 'C(7 - j, x + 1)), (x + 1)%N)
       else (a, x))
     (0%uint63, 0%N) (rev (iota 0 8))).1.

(* The seven free orientations in base three, the eighth being forced.        *)
Definition ctcoordi (u : arr) : int :=
  foldl (fun a j => Uint63.add (Uint63.mul a (of_nat nslot))
                               (of_nat (ctwist u j)))
        0%uint63 (rev (iota 0 7)).

(* ---- the triple of a position -------------------------------------------  *)

Definition htriple (a : arr) : int * int * int :=
  let u := inv_tabi flast a in (ecoordi u, clcoordi u, ctcoordi u).

(* THE CHECK.  These are the eighteen numbers `make hroots' prints for Reid's *)
(* six positions, so the coordinates here and the ones the table is indexed by*)
(* are the same coordinates.                                                  *)
Lemma hroots :
  [seq htriple (rooti k) | k <- iota 0 npfx] =
  [:: (169629%uint63,  51%uint63,   88%uint63);
      (167649%uint63,  31%uint63, 1465%uint63);
      (172970%uint63,  53%uint63,  164%uint63);
      (167759%uint63,  65%uint63,  170%uint63);
      ( 48703%uint63,  22%uint63,  880%uint63);
      (104169%uint63,  13%uint63, 1309%uint63)].
Proof. by vm_compute. Qed.

(* The solved cube's triple, which is what the search is looking for and where*)
(* the sweep that built the table started.  It is NOT the origin, and the     *)
(* prototype's build had to be told so: the two rankings send the solved cube *)
(* to 132784 and to the very last of the seventy.                             *)
Definition h0 : int * int * int := Eval vm_compute in htriple idi.

Lemma h0E : h0 = (132784%uint63, 69%uint63, 0%uint63).
Proof. by vm_compute. Qed.
