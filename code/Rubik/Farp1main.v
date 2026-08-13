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
   eighteen conjuncts are exactly the eighteen files.

   EACH PIECE STARTS GUARDED AGAINST fcpos j, THE FACE OF ITS SECOND MOVE.
   It used to start at nfcube, meaning "no previous move", which let the
   piece try all eighteen third moves where the rules leave about thirteen --
   one whole level of the search given away.  The guard is legitimate here
   because the word after the second move is reduced like any other; what
   cannot be guarded is the second move itself, whose face is fixed by the
   symmetry argument and not by the rules.  See Searchr.searchr_root2.      *)
Hypothesis hsearch :
  all (fun j => all (fun i => ~~ searchz3 T d (prefixi i j)
                                          (init3 (prefixi i j)) (fcpos j))
                    (iota 0 nroot))
      (iota 0 nmoves).

(* the piece as a searchr that came back false, NOT as a ball membership:
   searchrN would want nfcube and would throw the guard away again *)
Lemma p1prefix_searchr i j :
  (i < nroot)%N -> (j < nmoves)%N ->
  searchr moves (hsym3 T) nfcube fcube oppf d
          (superflip * nth 1%g moves i * nth 1%g moves j) (fcpos j) = false.
Proof.
move=> iL jL.
have iL' : (i < nmoves)%N := leq_trans iL nroot_leq.
(* the depth is given explicitly so the term is ground before it meets the
   goal: ball Sset ?d is a finset over {perm 'I_48}, not something to leave
   to unification. *)
rewrite -(prefixiE iL' jL).
have hs : searchz3 T d (prefixi i j) (init3 (prefixi i j)) (fcpos j) = false.
  (* no /= anywhere near this: it holds a searchz3 at depth d, and simpl
     would start unfolding the search itself *)
  move: hsearch => /allP/(_ _ (mem_iota0 jL))/allP/(_ _ (mem_iota0 iL)) h.
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
apply: (searchr_root2 Sset_inv (hsym30 hc0) hstep
                      fcube_ltS oppfK fcube_close fcube_comm (Sr := Sroot)).
- move=> gB; case: (ball_root superflipJ gB) => [gE|[m1 m1R hm1]].
    by move: superflip_neq1; rewrite gE eqxx.
  by exists m1.
- by move=> m1 m1R; exact: superflip_move_neq1 (Sroot_moves m1R).
move=> m1 m2 m1R m2M.
have [j jL <-] := moves_index m2M.
have [i iL <-] := root_index m1R.
by rewrite (fcpos_moves jL) p1prefix_searchr.
Qed.

End P1Far.
