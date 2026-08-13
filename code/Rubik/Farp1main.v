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

(* the root moves are on the U face, whose fcpos is 0 *)
Lemma fcpos_root i : (i < nroot)%N -> fcpos i = 0%N.
Proof. by case: i => [|[|]]. Qed.

(* and a second move on any other face is one jsnd keeps *)
Lemma mem_jsnd j : (j < nmoves)%N -> fcpos j != 0%N -> j \in jsnd.
Proof. by move=> jL jne; rewrite mem_filter jne (mem_iota0 jL). Qed.

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

(* the fifteen pieces, glued: the second move outermost, so that the fifteen
   conjuncts are exactly the fifteen files.

   TWO GUARDS, AND THEY ARE NOT THE SAME ARGUMENT.

   The list is jsnd, not iota 0 nmoves: a second move on the U face merges
   with the first into one move, so those three are covered at a smaller
   depth rather than by a file.  That is searchr_root2m's induction, and it
   needs the search to be sound as well as complete.

   Each piece starts guarded against fcpos j, the face of its second move,
   where it used to start at nfcube, "no previous move" -- which let it try
   all eighteen third moves where the rules leave about thirteen.  That one
   needs nothing new: the word after the second move is reduced like any
   other, and the old code simply discarded the fact.                       *)
Hypothesis hsearch :
  all (fun j => all (fun i => ~~ searchz3 T d (prefixi i j)
                                          (init3 (prefixi i j)) (fcpos j))
                    (iota 0 nroot))
      jsnd.

(* the piece as a searchr that came back false, NOT as a ball membership:
   searchrN would want nfcube and would throw the guard away again *)
Lemma p1prefix_searchr i j :
  (i < nroot)%N -> (j < nmoves)%N -> fcpos j != 0%N ->
  searchr moves (hsym3 T) nfcube fcube oppf d
          (superflip * nth 1%g moves i * nth 1%g moves j) (fcpos j) = false.
Proof.
move=> iL jL jne.
have iL' : (i < nmoves)%N := leq_trans iL nroot_leq.
have jS := mem_jsnd jL jne.
(* the depth is given explicitly so the term is ground before it meets the
   goal: ball Sset ?d is a finset over {perm 'I_48}, not something to leave
   to unification. *)
rewrite -(prefixiE iL' jL).
have hs : searchz3 T d (prefixi i j) (init3 (prefixi i j)) (fcpos j) = false.
  (* no /= anywhere near this: it holds a searchz3 at depth d, and simpl
     would start unfolding the search itself *)
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
(* fne GOES BACK IN THE GOAL FIRST.  The two intro patterns below substitute
   m1 and m2 away, and a hypothesis left standing does not follow them, so
   the rewrite finds fcube m1 where it expects fcube moves`_i. *)
move: fne.
have [j jL <-] := moves_index m2M.
have [i iL <-] := root_index m1R.
(* the root is on the U face, so fcpos i = 0 and what is left says the second
   move is on another one.  NO TRAILING `by' ANYWHERE IN HERE: the context
   holds p1checkStep, and a `done' that unifies against it unfolds an all_pow
   at ncoord = 24 -- the reason nroot_leq sits outside the section. *)
rewrite (fcpos_moves jL) (fcpos_moves (leq_trans iL nroot_leq)).
rewrite (fcpos_root iL) => jne.
exact: (p1prefix_searchr iL jL jne).
Qed.

End P1Far.
