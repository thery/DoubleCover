(* =========================================================================  *)
(*  Farp1main.v -- superflip \notin ball Sset d.+2, over an abstract table.   *)
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

(* OUTSIDE the section below, and that is not tidiness.  In it, a             *)
(* trailing `done' unifies its goal with p1checkStep -- same is_true          *)
(* head -- and unfolds an all_pow at ncoord = 24.  Even `i < nmoves'          *)
(* does not return.                                                           *)
Lemma nroot_leq : (nroot <= nmoves)%N.
Proof. by []. Qed.

(* the root moves are on the U face, whose fcpos is 0                         *)
Lemma fcpos_root i : (i < nroot)%N -> fcpos i = 0%N.
Proof. by case: i => [|[|]]. Qed.

(* and a second move on any other face is one jsnd keeps                      *)
Lemma mem_jsnd j : (j < nmoves)%N -> fcpos j != 0%N -> j \in jsnd.
Proof. by move=> jL jne; rewrite mem_filter jne (mem_iota0 jL). Qed.

(* mem_iota0 lives in Farp1.v for the same reason.  A second copy here        *)
(* would clash with it.                                                       *)

(* ---- 2. The assembly ------------------------------------------------------*)

Section P1Far.

Variable T : PArray.array arr.
Variable d : nat.

(* The search compares the heuristic with the depth in int63, and the         *)
(* bridge to the nat comparison needs the depth to fit.  It is at most 19.    *)
Hypothesis dL : (d <= 63)%N.

(* the five computations, and the twist x slice check                         *)
Hypothesis hc0 : p1check0 T.
Hypothesis hcS : p1checkStep T.
Hypothesis hts : ts_checkStep.
Hypothesis hfm : fsmoveC.
Hypothesis hfr : fsrC.
Hypothesis hsl : slrC.

(* The fifteen pieces, glued.  The second move is outermost, so the           *)
(* conjuncts are the files.                                                   *)
(*                                                                            *)
(* TWO GUARDS, AND THEY REST ON DIFFERENT ARGUMENTS.                          *)
(*                                                                            *)
(* The list is jsnd, not every move: a second move on the U face merges       *)
(* with the first, so those three belong at a smaller depth.  That is         *)
(* searchr_root2m, and it needs the search sound as well as complete.         *)
(*                                                                            *)
(* Each piece is guarded against fcpos j, the face of its second move.        *)
(* It used to start at nfcube, no previous move, and try all eighteen         *)
(* third moves where the rules leave thirteen.  Nothing new is needed         *)
(* there: the word after the second move is reduced like any other.           *)
Hypothesis hsearch :
  all (fun j => all (fun i => ~~ searchz3 T d (prefixi i j)
                                          (init3 (prefixi i j)) (fcpos j))
                    (iota 0 nroot))
      jsnd.

(* The piece as a searchr that failed, not as a ball membership:              *)
(* searchrN wants nfcube and would throw the guard away again.                *)
Lemma p1prefix_searchr i j :
  (i < nroot)%N -> (j < nmoves)%N -> fcpos j != 0%N ->
  searchr moves (hsym3 T) nfcube fcube oppf d
          (superflip * nth 1%g moves i * nth 1%g moves j) (fcpos j) = false.
Proof.
move=> iL jL jne.
have iL' : (i < nmoves)%N := leq_trans iL nroot_leq.
have jS := mem_jsnd jL jne.
(* The depth is given, so the term is ground before it meets the goal:        *)
(* ball Sset ?d is a finset over {perm 'I_48}, not one to unify.              *)
rewrite -(prefixiE iL' jL).
have hs : searchz3 T d (prefixi i j) (init3 (prefixi i j)) (fcpos j) = false.
  (* No /= near this: it holds a searchz3 at depth d, and simpl would         *)
  (* start unfolding the search itself.                                       *)
  move: hsearch => /allP/(_ _ jS)/allP/(_ _ (mem_iota0 iL)) h.
  exact: negbTE h.
exact: (searchr_of_searchz3 (d := d) dL hfm hfr
                            (prefixi_ok iL' jL) (prefixi_cub iL' jL)
                            (prefixi_twP3 iL' jL) hs).
Qed.

(* ---- 3. The theorem ------------------------------------------------------ *)

Theorem superflip_p1far : superflip \notin ball Sset d.+2.
Proof.
have hstep : forall g m, m \in Sset -> hsym3 T g <= (hsym3 T (g * m)).+1.
  by move=> g m mS; exact: (@hsym3S T g m hcS hts hsl mS).
apply: (searchr_root2m Sset_inv (hsym30 hc0) hstep
                       fcube_ltS oppfK fcube_close fcube_comm (Sr := Sroot)).
- exact: Sroot_moves.
- exact: superflip_neq1.
- move=> k gB; case: (ball_root superflipJ gB) => [gE|[m1 m1R hm1]].
    by move: superflip_neq1; rewrite gE eqxx.
  by exists m1.
- by move=> m1 m1R; exact: superflip_move_neq1 (Sroot_moves m1R).
move=> m1 m2 m1R m2M fne.
(* fne GOES BACK IN THE GOAL FIRST.  The two patterns below substitute        *)
(* m1 and m2 away, and a standing hypothesis does not follow them.            *)
move: fne.
have [j jL <-] := moves_index m2M.
have [i iL <-] := root_index m1R.
(* The root is on the U face, so fcpos i = 0, and what is left says the       *)
(* second move is on another.  NO TRAILING `by' HERE -- see nroot_leq.        *)
rewrite (fcpos_moves jL) (fcpos_moves (leq_trans iL nroot_leq)).
rewrite (fcpos_root iL) => jne.
exact: (p1prefix_searchr iL jL jne).
Qed.

End P1Far.
