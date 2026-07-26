(* =========================================================================  *)
(*  Diameter.v                                                                *)
(*                                                                            *)
(*  "The diameter of the Rubik's cube group is twenty" (Rokicki, Kociemba,    *)
(*  Davidson, Dethridge), assembled.                                          *)
(*                                                                            *)
(*  Upper bound.  The abstract reduction of Ball.v, instantiated on the cube: *)
(*  the group theory is a real proof (the cosets of H partition G, the 48     *)
(*  symmetries and inversion act on the word metric), and what is left over   *)
(*  is exactly the two outputs of the external search -- that the verified    *)
(*  representatives cover every coset up to symmetry, and that each of them   *)
(*  is solvable in at most 20 moves.  Those two are the section hypotheses    *)
(*  below: this file says "checker => diameter <= 20", it does not run the    *)
(*  10^19-position search in the kernel.                                      *)
(*                                                                            *)
(*  Lower bound.  One position out of reach in 19 moves is enough, and the    *)
(*  classical witness is the superflip.  That it is a cube position, and      *)
(*  that it is not within 19 moves, are again computations [COMPUTATION].     *)
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

(* [COMPUTATION] The superflip is a cube position: it is the value of an      *)
(* explicit maneuver, for instance                                            *)
(*     U R2 F B R B2 R U2 L B2 R U' D' R2 F R' L B2 U2 F2                     *)
(* (a 20-move word -- the one that gives the matching upper bound).           *)
Lemma superflipE : 
  superflip = Umove * Rmove ^+2 * Fmove * Bmove * Rmove * Bmove ^+2 *
          Rmove * Umove ^+2 * Lmove * Bmove ^+2 * Rmove * Umove ^-1 *
          Dmove ^-1 * Rmove ^+2 * Fmove * Rmove ^-1 * Lmove * Bmove ^+2 *
          Umove ^+ 2 * Fmove ^+2.
Proof.
rewrite UmoveT RmoveT FmoveT BmoveT LmoveT DmoveT !ptV // !ptX // !ptM //.
rewrite /superflip /Spcyc.
pose ll := 
  ([:: [:: 1; 33];  [:: 3; 9]; [:: 4; 25]; [:: 6; 17]; [:: 11; 36]; 
      [:: 12; 19]; [:: 14; 43]; [:: 20; 27]; [:: 22; 41]; [:: 28; 35];
      [:: 30; 44];  [:: 38; 46]])%N.
by have ->// := @cycs_pt 47%N ll.
Qed.

Lemma superflip_in_G : superflip \in G.
Proof.
have Ui : Umove \in G.
  by apply: (subsetP (subset_gen _)); rewrite !inE eqxx ?orbT.
have Bi : Bmove \in G.
  by apply: (subsetP (subset_gen _)); rewrite !inE eqxx ?orbT.
have Ri : Rmove \in G.
  by apply: (subsetP (subset_gen _)); rewrite !inE eqxx ?orbT.
have Fi : Fmove \in G.
  by apply: (subsetP (subset_gen _)); rewrite !inE eqxx ?orbT.
have Li : Lmove \in G.
  by apply: (subsetP (subset_gen _)); rewrite !inE eqxx ?orbT.
have Di : Dmove \in G.
  by apply: (subsetP (subset_gen _)); rewrite !inE eqxx ?orbT.
rewrite superflipE.
repeat (apply: groupM; last by first [done || apply groupX || apply: groupVr]).
by first [done || apply groupX || apply: groupVr].
Qed.

(* [COMPUTATION] The lower-bound search: no word of length at most 19 in the  *)
(* eighteen moves reaches the superflip.                                      *)
Lemma superflip_far : superflip \notin ball Sset 19.
Admitted.

Theorem rubik_diam_gt_19 : ~~ diam_le Sset 19.
Proof.
apply/negP => /subsetP Hs; move: superflip_far.
by rewrite (Hs _ superflip_in_G).
Qed.

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

(* The diameter is twenty: reachable in 20, and 19 is not enough.             *)
Theorem rubik_diameter : diam_le Sset 20 /\ ~~ diam_le Sset 19.
Proof. by split; [exact: rubik_diam_le_20 | exact: rubik_diam_gt_19]. Qed.

End Checker.
