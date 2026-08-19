(* =========================================================================  *)
(*  HFinal.v -- the bound, assembled.                                        *)
(* =========================================================================  *)

(* Reid's position needs twenty six quarter turns and no fewer, so the        *)
(* quarter-turn diameter of the cube is at least twenty six.  Both halves are *)
(* here: HBound.targ_near is the maneuver, and HSound.targ_far_of is the      *)
(* search, which takes the seventy two run files and run_sound.               *)
(*                                                                            *)
(* Everything below this file is proved.  run_sound is what is left, and what *)
(* it is waiting on is obligation C's three sweeps.                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Coordfsi
        Phase1 HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

Section Final.

Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

(* what the seventy two run files say, and what makes the search mean it     *)
Hypothesis Hs : run_sound mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold.
Hypothesis Hj : forall k w, (k < seq.size rpfx)%N -> w \in hpres ->
  hrun mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold k w (hdepth k) = false.

(* ---- the position is a maneuver ------------------------------------------ *)

(* THE ANGLE NOTATION DOES NOT PARSE HERE: Uint63 takes >> for the shift, and *)
(* Ball.v does not import it.  generated is the same thing spelled out.       *)
Lemma targ_gen : targ \in generated Sq.
Proof.
have := wp_ball targw_qw.
by rewrite wp_targw; apply: (subsetP (ball_sub_gen Sq 40)).
Qed.

(* ---- the two halves ------------------------------------------------------ *)

Theorem targ_dist : targ \in ball Sq 26 /\ targ \notin ball Sq 25.
Proof. by split; [apply: targ_near | apply: targ_far_of Hs Hj]. Qed.

(* ---- and so the diameter ------------------------------------------------- *)

(* diam_le Sq n says every position is within n quarter turns.  Reid's is   *)
(* not within twenty five, so the diameter is more, and targ_near makes it   *)
(* exactly twenty six for that position.                                     *)
Theorem qdiam_gt25 : ~ diam_le Sq 25.
Proof.
move=> /subsetP hsub.
have := hsub _ targ_gen.
by apply/negP; apply: targ_far_of Hs Hj.
Qed.

End Final.
