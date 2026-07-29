(* =========================================================================  *)
(*  Far12main.v                                                               *)
(*                                                                            *)
(*  superflip \notin ball Sset 12, assembled from the eighteen pieces.        *)
(*                                                                            *)
(*  Far12.v has everything but the search itself.  Far12_00 .. Far12_17 each  *)
(*  run one second move over both root moves, on their own core.  Here they   *)
(*  are glued: all over iota 0 18 is a conjunction of eighteen booleans, so   *)
(*  search12 is one rewrite per file and nothing is recomputed -- the pieces  *)
(*  arrive as opaque Qed constants.                                          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root.
From Rubik Require Import Coord Coordfs Coordfsi Fstab FsTable Diameter Toy.
From Rubik Require Import Far12.
From Rubik Require Import Far12_00 Far12_01 Far12_02 Far12_03 Far12_04 Far12_05 Far12_06 Far12_07 Far12_08 Far12_09 Far12_10 Far12_11 Far12_12 Far12_13 Far12_14 Far12_15 Far12_16 Far12_17.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the second move outermost, so that the eighteen pieces are exactly the
   eighteen conjuncts *)
Lemma search12 :
  all (fun j => all (fun i => ~~ searchi 47 mtis Dti12 droot (prefixi i j))
                    (iota 0 nroot))
      (iota 0 nmoves).
Proof. by rewrite /nmoves /= searchj_00 searchj_01 searchj_02 searchj_03 searchj_04 searchj_05 searchj_06 searchj_07 searchj_08 searchj_09 searchj_10 searchj_11 searchj_12 searchj_13 searchj_14 searchj_15 searchj_16 searchj_17. Qed.

(* ---- 5. The theorem ------------------------------------------------------ *)

(* one prefix is out of the ball, by Coordfsi.far_of_searchi                  *)
Lemma prefix_far i j :
  i < nroot -> j < nmoves ->
  superflip * nth 1 moves i * nth 1 moves j \notin ball Sset droot.
Proof.
move=> iL jL; have iL' : i < nmoves by rewrite (leq_trans iL).
rewrite -prefixiE //.
(* the depth is given explicitly so that the term is ground before it meets
   the goal; ball Sset ?d is a finset over {perm 'I_48} and not something to
   leave to unification.                                                   *)
have hs : searchi 47 mtis Dti12 droot (prefixi i j) = false.
  (* no /= anywhere near this goal: it holds a searchi at depth 10 and simpl
     would start unfolding the search itself.                              *)
  have h1 : i \in iota 0 nroot by rewrite mem_iota add0n leq0n.
  have h2 : j \in iota 0 nmoves by rewrite mem_iota add0n leq0n.
  by apply/negbTE; move: search12 => /allP/(_ _ h2)/allP/(_ _ h1).
exact: (far_of_searchi Dfs12_0 Dfs12_step mtis_ok mtisE
          (d := droot) (prefixi_ok iL' jL) hs).
Qed.

Theorem superflip_far12 : superflip \notin ball Sset depth.
Proof.
apply: (ball_root2 superflipJ superflip_neq1 superflip_move_neq1).
move=> m1 m2 m1R m2M.
have [j jL <-] := moves_index m2M.
have [i iL <-] := root_index m1R.
exact: prefix_far.
Qed.
