(* =========================================================================  *)
(*  Diam20.v -- God's number is at least 20, at the real search.            *)
(*     OUT OF _CoqProject on purpose: it only says anything when            *)
(*     ./mkrunp1.sh was given 19, and `make test' compiles it then.         *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Cyc Ball Table Rubik333 Sym Diameter Runp1 Farp1inst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* THE GUARD.  Farp1inst proves the superflip out of the ball of radius
   p1depth, and p1depth is whatever mkrunp1.sh last wrote into Runp1.v.  This
   sentence is what fails, in a second and before anything else, if the
   eighteen searches were not run at 19.                                      *)
Lemma p1depth_19 : p1depth = 19%N.
Proof. by []. Qed.

(* Diameter.v states this same theorem from an admitted superflip_far: it sits
   at the bottom of the chain and cannot mention the search, which sits at the
   top.  Here the real theorem is in scope, so the two lines are replayed with
   it and nothing is admitted.                                                *)
Theorem rubik_diam_gt_19_real : ~~ diam_le Sset 19.
Proof.
apply/negP => /subsetP Hs; move: superflip_p1far_real.
by rewrite p1depth_19 (Hs _ superflip_in_G).
Qed.

(* int63 and PArray primitives only *)
Print Assumptions rubik_diam_gt_19_real.
