(* =========================================================================  *)
(*  Farp1main.v -- superflip \notin ball Sset d.+2, over an abstract table. *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Farp1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- 1. Two facts, hoisted ----------------------------------------------- *)

(* OUTSIDE the section below, and that is not tidiness.  Inside it the
   context holds p1checkStep, fsmoveC, fsrC and slrC, and every trailing
   `done' then tries `assumption', unifies its goal against one of them --
   same is_true head -- and unfolds an all_pow at ncoord = 24.  the master file
   proves both of these inline because its context is clean; here even
   `i < nmoves' does not return. *)
Lemma nroot_leq : (nroot <= nmoves)%N.
Proof. by []. Qed.

(* mem_iota0 now lives in Farp1.v, proved outside those proofs for this
   same reason and
   used at its eight sites; keeping a second copy here would clash. *)

(* ---- 2. The assembly ------------------------------------------------------ *)

Section P1Far.

Variable T : PArray.array arr.
Variable d : nat.

(* the search compares the heuristic with the depth in int63 now, and the
   bridge to the nat comparison needs the depth to fit -- it is at most 19 *)
Hypothesis dL : (d <= 63)%N.

(* the five computations, and the twist x slice check *)
Hypothesis hc0 : p1check0 T.
Hypothesis hcS : p1checkStep T.
Hypothesis hts : ts_checkStep.
Hypothesis hfm : fsmoveC.
Hypothesis hfr : fsrC.
Hypothesis hsl : slrC.

(* the eighteen pieces, glued: the second move outermost, so that the
   eighteen conjuncts are exactly the eighteen files *)
Hypothesis hsearch :
  all (fun j => all (fun i => ~~ searchz3 T d (prefixi i j)
                                          (init3 (prefixi i j)) nfcube)
                    (iota 0 nroot))
      (iota 0 nmoves).

Lemma p1prefix_far i j :
  (i < nroot)%N -> (j < nmoves)%N ->
  superflip * nth 1%g moves i * nth 1%g moves j \notin ball Sset d.
Proof.
move=> iL jL.
have iL' : (i < nmoves)%N := leq_trans iL nroot_leq.
(* the depth is given explicitly so the term is ground before it meets the
   goal: ball Sset ?d is a finset over {perm 'I_48}, not something to leave
   to unification. *)
rewrite -(prefixiE iL' jL).
have hs : searchz3 T d (prefixi i j) (init3 (prefixi i j)) nfcube = false.
  (* no /= anywhere near this: it holds a searchz3 at depth d, and simpl
     would start unfolding the search itself *)
  move: hsearch => /allP/(_ _ (mem_iota0 jL))/allP/(_ _ (mem_iota0 iL)) h.
  exact: negbTE h.
exact: (far_of_searchz3 (d := d) dL hc0 hcS hts hfm hfr hsl
                        (prefixi_ok iL' jL) (prefixi_cub iL' jL)
                        (prefixi_twP3 iL' jL) hs).
Qed.

(* ---- 3. The theorem ------------------------------------------------------ *)

Theorem superflip_p1far : superflip \notin ball Sset d.+2.
Proof.
apply: (ball_root2 superflipJ superflip_neq1 superflip_move_neq1).
move=> m1 m2 m1R m2M.
have [j jL <-] := moves_index m2M.
have [i iL <-] := root_index m1R.
exact: p1prefix_far.
Qed.

End P1Far.
