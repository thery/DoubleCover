(* =========================================================================  *)
(*  Diam20.v -- God's number is at least 20, at the real search.              *)
(*     OUT OF _CoqProject on purpose: it only says anything when              *)
(*     ./mkrunp1.sh was given 19, and `make test' compiles it then.           *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Rubik333 Sym Diameter Runp1 Farp1inst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* THE GUARD.  Farp1inst proves the superflip out of the ball of radius       *)
(* p1depth, and p1depth is whatever mkrunp1.sh last wrote into Runp1.v.  This *)
(* sentence is what fails, in a second and before anything else, if the       *)
(* eighteen searches were not run at 19.                                      *)
Lemma p1depth_19 : p1depth = 19%N.
Proof. by []. Qed.

(* Diameter.v defines the cube and cannot mention the search, which needs     *)
(* everything; this is where the two ends meet.  Nothing is admitted.         *)
Theorem rubik_diam_gt_19_real : ~~ diam_le Sset 19.
Proof.
apply/negP => /subsetP Hs; move: superflip_p1far_real.
by rewrite p1depth_19 (Hs _ superflip_in_G).
Qed.

(* int63 and PArray primitives only                                           *)
Print Assumptions rubik_diam_gt_19_real.

(* The diameter is twenty: reachable in 20, and 19 is not enough.  The upper  *)
(* half is still what an exhaustive search would have to supply, and is the   *)
(* only thing assumed here.                                                   *)
Theorem rubik_diameter (R : {set {set {perm facelet}}})
  (Rcover : forall C, C \in cosets ->
     exists2 u, u \in Symg & (C :^ u \in R) || (C^-1 :^ u \in R))
  (Rsolved : forall D, D \in R -> D \subset ball Sset 20) :
  diam_le Sset 20 /\ ~~ diam_le Sset 19.
Proof.
by split; [exact: (@rubik_diam_le_20 R Rcover Rsolved) |
           exact: rubik_diam_gt_19_real].
Qed.
