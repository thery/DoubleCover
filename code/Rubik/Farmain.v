(* =========================================================================  *)
(*  Farmain.v                                                               *)
(*                                                                            *)
(*  superflip \notin ball Sset depth, assembled from the eighteen pieces.     *)
(*                                                                            *)
(*  Far.v has everything but the search itself.  Far_00 .. Far_17 each  *)
(*  run one second move over both root moves, on their own core.  Here they   *)
(*  are glued: all over iota 0 18 is a conjunction of eighteen booleans, so   *)
(*  searchd is one rewrite per file and nothing is recomputed -- the pieces  *)
(*  arrive as opaque Qed constants.                                          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root.
From Rubik Require Import Coord Coordfs Coordfsi Fstab FsTable Diameter Toy.
From Rubik Require Import Far.
From Rubik Require Import Far_00 Far_01 Far_02 Far_03 Far_04 Far_05 Far_06 Far_07 Far_08 Far_09 Far_10 Far_11 Far_12 Far_13 Far_14 Far_15 Far_16 Far_17.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* the second move outermost, so that the eighteen pieces are exactly the
   eighteen conjuncts *)
Lemma searchd :
  all (fun j => all (fun i => ~~ searchi 47 mtis Dtid droot (prefixi i j))
                    (iota 0 nroot))
      (iota 0 nmoves).
Proof. by rewrite /nmoves /= searchd_00 searchd_01 searchd_02 searchd_03 searchd_04 searchd_05 searchd_06 searchd_07 searchd_08 searchd_09 searchd_10 searchd_11 searchd_12 searchd_13 searchd_14 searchd_15 searchd_16 searchd_17. Qed.

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
have hs : searchi 47 mtis Dtid droot (prefixi i j) = false.
  (* no /= anywhere near this goal: it holds a searchi at depth droot and simpl
     would start unfolding the search itself.                              *)
  have h1 : i \in iota 0 nroot by rewrite mem_iota add0n leq0n.
  have h2 : j \in iota 0 nmoves by rewrite mem_iota add0n leq0n.
  by apply/negbTE; move: searchd => /allP/(_ _ h2)/allP/(_ _ h1).
exact: (far_of_searchi Dfsd_0 Dfsd_step mtis_ok mtisE
          (d := droot) (prefixi_ok iL' jL) hs).
Qed.

Theorem superflip_fard : superflip \notin ball Sset depth.
Proof.
apply: (ball_root2 superflipJ superflip_neq1 superflip_move_neq1).
move=> m1 m2 m1R m2M.
have [j jL <-] := moves_index m2M.
have [i iL <-] := root_index m1R.
exact: prefix_far.
Qed.
