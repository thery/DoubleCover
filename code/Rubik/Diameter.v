(* =========================================================================  *)
(*  Diameter.v -- The statement that the diameter of the Rubik's cube group   *)
(*     is twenty.                                                             *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Rubik333 Sym.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Local Notation "n '@'" := (inord n : facelet) (at level 2, format "n '@'").

(* ---- 1. The superflip -----------------------------------------------------*)
(*                                                                            *)
(*  The position with every corner solved and every one of the twelve edges   *)
(*  flipped in place: as a facelet permutation, the two stickers of each      *)
(*  edge cubie are exchanged.  It is the distance-20 position of the paper    *)
(*  (and is fixed by all 48 symmetries, which is why it is so far out).       *)

Definition Spcyc : seq (seq facelet) :=
  [:: [:: 1@; 33@];
      [:: 3@; 9@];
      [:: 4@; 25@];
      [:: 6@; 17@];
      [:: 11@; 36@];
      [:: 12@; 19@];
      [:: 14@; 43@];
      [:: 20@; 27@];
      [:: 22@; 41@];
      [:: 28@; 35@];
      [:: 30@; 44@];
      [:: 38@; 46@] ].

Definition superflip : {perm facelet} := \prod_(l <- Spcyc) cyc l.

Lemma Spcyc_uniq : uniq (flatten Spcyc).
Proof.
by eapply (@uniq_inord _
  [:: 1; 33; 3; 9; 4; 25; 6; 17; 11; 36; 12; 19;
      14; 43; 20; 27; 22; 41; 28; 35; 30; 44; 38; 46])%N.
Qed.

(* The twelve flips are disjoint, so the superflip is an involution.          *)
Lemma superflip2 : superflip ^+ 2 = 1.
Proof. by apply: cyc_prod_expn; [exact: Spcyc_uniq | apply: all_sizeP]. Qed.

(* The superflip is the value of an explicit maneuver,                        *)
(*     U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2                     *)
(* (a 20-move word -- the one that gives the matching upper bound).  Both     *)
(* sides are pushed onto tables, where the equality is one comparison of two  *)
(* literal nat lists.  The tab_ok side conditions are closed by vm_compute    *)
(* rather than by conversion: it takes the proof from 14s to 3s.              *)
Lemma superflipE :
  superflip = Umove * Rmove ^+2 * Fmove * Bmove * Rmove * Bmove ^+2 *
          Rmove * Umove ^+2 * Lmove * Bmove ^+2 * Rmove * Umove ^-1 *
          Dmove ^-1 * Rmove ^+2 * Fmove * Rmove ^-1 * Lmove * Bmove ^+2 *
          Umove ^+ 2 * Fmove ^+2.
Proof.
rewrite UmoveT RmoveT FmoveT BmoveT LmoveT DmoveT !ptV; [|by vm_compute..].
rewrite !ptX; [|by vm_compute..].
rewrite !ptM; [|by vm_compute..].
rewrite /superflip /Spcyc.
pose ll :=
  ([:: [:: 1; 33]; [:: 3; 9]; [:: 4; 25]; [:: 6; 17]; [:: 11; 36];
       [:: 12; 19]; [:: 14; 43]; [:: 20; 27]; [:: 22; 41]; [:: 28; 35];
       [:: 30; 44]; [:: 38; 46]])%N.
by have ->// := @cycs_pt 47%N ll.
Qed.

Lemma in_consr (T : eqType) (x y : T) (s : seq T) : x \in s -> x \in y :: s.
Proof. by rewrite inE => ->; rewrite orbT. Qed.

(* Hence a cube position: the maneuver is a word in the six face turns.  The  *)
(* face branch has to be tried BEFORE groupM -- a face turn is itself a       *)
(* product of cycles, so groupM would happily take the word apart into its    *)
(* 140 cycles instead of stopping at the generators.                          *)
Lemma superflip_in_G : superflip \in G.
Proof.
have faceG g : g \in faces -> g \in G.
  move=> gF; apply: (subsetP (subset_gen _)); rewrite inE /moves.
  by apply/flatten_mapP; exists g => //; rewrite !inE eqxx.
rewrite superflipE.
have Ui : Umove \in G by apply/faceG/mem_head.
have Ri : Rmove \in G by apply/faceG/in_consr/mem_head.
have Fi : Fmove \in G by apply/faceG/in_consr/in_consr/mem_head.
have Di : Dmove \in G by apply/faceG/in_consr/in_consr/in_consr/mem_head.
have Li : Lmove \in G by apply/faceG/in_consr/in_consr/in_consr/in_consr/mem_head.
have Bi : Bmove \in G by apply/faceG/in_consr/in_consr/in_consr/in_consr/in_consr/mem_head.
apply: groupM; last by apply: groupX.
apply: groupM; last by apply: groupX.
apply: groupM; last by apply: groupX.
apply: groupM; last by [].
apply: groupM; last by apply: groupVr.
apply: groupM; last by [].
apply: groupM; last by apply: groupX.
apply: groupM; last by apply: groupVr.
apply: groupM; last by apply: groupVr.
apply: groupM; last by [].
apply: groupM; last by apply: groupX.
apply: groupM; last by [].
apply: groupM; last by apply: groupX.
apply: groupM; last by [].
apply: groupM; last by apply: groupX.
apply: groupM; last by [].
apply: groupM; last by [].
apply: groupM; last by [].
by apply: groupM; last by apply: groupX.
Qed.

(* The lower bound itself is not here: it is the search, which sits at the    *)
(* top of the development while the cube is defined here at the bottom.  See  *)
(* Diam20.v, where the two ends meet.                                         *)

(* ---- 2. The reduction, instantiated on the cube -------------------------- *)

Section Checker.

(* R is what the external search actually verified: a set of position sets,   *)
(* the representatives of the symmetry classes of cosets.                     *)
Variable R : {set {set {perm facelet}}}.

(* First output of the search: the representatives cover everything.  Every   *)
(* coset of H is carried into R by one of the 48 symmetries, possibly after   *)
(* inverting -- the 55.9 million classes of the paper.                        *)
Hypothesis Rcover :
  forall C, C \in cosets ->
    exists2 u, u \in Symg & (C :^ u \in R) || (C^-1 :^ u \in R).

(* Second output of the search: each representative is solvable in 20 moves.  *)
Hypothesis Rsolved : forall D, D \in R -> D \subset ball Sset 20.

Theorem rubik_diam_le_20 : diam_le Sset 20.
Proof.
apply: (@diam_le_reps2 _ Sset H R 20) => //; first exact: HsubG.
  exact: Sset_inv.
move=> C CH; have [u uS uR] := Rcover CH.
by exists u => //; apply: Symg_stab.
Qed.

End Checker.

(* The other half, "19 is not enough", and the two together as the diameter,  *)
(* are in Diam20.v.                                                           *)
