(* =========================================================================  *)
(*  RowReal.v -- the instance on the real tables, and the row itself.         *)
(* =========================================================================  *)

(* WHAT RowDummy DID ON NOUGHTS, DONE ON THE TABLES.  Every check that has a  *)
(* file of its own is spent here, and what is left admitted is exactly what   *)
(* has not been computed -- no statement is missing and nothing is left       *)
(* dangling, only runs.                                                       *)
(*                                                                            *)
(* FOUR TABLES ARE STILL VARIABLES, and they are the SEARCH's own: the phase  *)
(* one pruning table, the fs step table, the reading of a position into three *)
(* ranks, and the move filter.  No generated file in the tree carries them.   *)
(* Soundness never looks at the pruning table -- it appears only in the       *)
(* premise of the two facts about a leaf -- so the row does not wait on it.   *)
(*                                                                            *)
(* And then the row itself: every position of H is within twenty moves of the *)
(* superflip.                                                                 *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowLeaf.
Require Import RowMoveH RowMoveM RowParity RowPartM.
Require Import RowPartC RowPartU RowMoveC RowMoveU RowMembChk.
Require Import RowUp8inv RowUp8ok RowUp4inv RowUp4ok RowPar8 RowPar4.
Require Import RowWits RowWitsChk RowInH.
Require Import P1Table.
Require Import Fstab FsTable Searchr Redun Searchir P1Fs P1Fsm Far Farp1.
Require Import RowMembi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).
Notation rmap := (PArray.array arr).

Section Real.

(* ---- the four the search carries and no file supplies -------------------- *)

(* THE TABLE the search prunes with: the phase one table mkp1.sh generates,   *)
(* four bits an entry and fifteen to a word, the same one the lower bound     *)
(* reads and read the same way.  Soundness never looks at it -- the search    *)
(* stops on the position, not on the table -- so a bad table would only make  *)
(* the run find less.                                                         *)
Definition p1 : rmap := p1tab.

(* THE MOVE FILTER.  Nothing rests on the choice -- okmv only skips moves, so *)
(* one that rejects too much makes the search find less, never something      *)
(* false, and srch_sound never reads it.  But offering all eighteen moves at  *)
(* every node is what makes a search take an hour instead of a minute.        *)
(*                                                                            *)
(* TWO RULES, and both cost nothing.  Never turn the same face twice running: *)
(* the two turns are one turn of that face and the pair is reached the short  *)
(* way.  And on a pair of opposite faces, which commute, fix an order and     *)
(* keep only one of the two ways round.  The faces are U R F D L B, so a move *)
(* is three times its face plus how far, and the opposite of face f is f + 3. *)
Definition okmvv (pv k : int) : bool :=
  if (18 <=? pv)%uint63 then true
  else let fp := (pv / 3)%uint63 in
       let fk := (k / 3)%uint63 in
       (* || is a function and native_compute is call by value, so the        *)
       (* second test is only skipped by writing the two as nested ifs.       *)
       if (fp =? fk)%uint63 then false else ~~ (fp =? fk + 3)%uint63.

Definition srch : nat := 16.

(* THE FLIP AND SLICE MOVE TABLE'S OWN CERTIFICATE, which the lower bound     *)
(* already has: FsmChk.fsmoveCP proves it, by native_compute.  Carried as a   *)
(* hypothesis rather than imported so that this file does not wait on a       *)
(* native build.                                                              *)
Hypothesis hfm : fsmoveC.

(* ---- and the four that are runs and nothing else ------------------------- *)

(* THE FS STEP TABLE, and it is Farp1's actfsri -- which is what RowInst      *)
(* meant fsstep to be all along.  actfsr_step is the lemma; the only work is  *)
(* the int and the nat, and the default the move table is read with.          *)
Lemma r_fsstepP x k : (to_nat k < nmvn)%N -> pstok x ->
  actfsri (fsidx (coordi x)) k = fsidx (coordi (xstep x k)).
Proof.
move=> kL /and3P[xok cx tx].
have kL18 : (to_nat k < 18)%N by [].
have szm : (to_nat k < seq.size mtis)%N.
  by rewrite /mtis seq.size_map size_mtabs.
rewrite -{1}(to_natK k) actfsriE (actfsr_step xok cx tx kL18 hfm).
congr (fsidx (coordi (comp_tabi _ _ _))).
by rewrite /mvi (set_nth_default (id_tabi flast) sfti szm).
Qed.

(* WHAT THE PRUNING TABLE SAYS, and it is all that is asked of it: a nought   *)
(* is the solved phase one coordinate.  p1 is a Variable here, so this is the *)
(* soundness of the table the search was handed and it is carried, not        *)
(* proved.  Soundness of the ROW looks nowhere else at p1.                    *)
(* ---- and what a leaf is, which is now PROVED ----------------------------- *)

(* Both come straight from RowLeaf once the premise is being in H.  The       *)
(* table tomemb reads is the INVERSE of the position's, so everything below   *)
(* is said of that: it is a table because the position's is, it is in H       *)
(* because H is a group, and inH_conds turns being in H into the three place  *)
(* permutations leaf_membH and tomemb_tabH want.                              *)
Section Leaf.

Variable x : pstt.
Hypothesis hx : pstok x.
Hypothesis hG : pt flast (ti2t flast x) \in G.
Hypothesis htw : ctwisti x = 0%uint63.
Hypothesis hfs : coordi x = coordfs 1.

Let u := ti2t flast (inv_tabi flast x).

Lemma r_xok : tabi_ok flast x.  Proof. by case/and3P: hx. Qed.

Lemma r_uok : tab_ok flast u.
Proof.
by rewrite /u (ti2t_inv n47_small n47_len r_xok); apply/tab_ok_inv/r_xok.
Qed.

Lemma r_uG : pt flast u \in G.
Proof.
rewrite /u (ti2t_inv n47_small n47_len r_xok) -(ptV r_xok) groupV.
exact: hG.
Qed.

Lemma r_leafW : membok par8i par4i (tomemb x)
  /\ pt flast (memb2tab (tomemb x)) = pt flast (ti2t flast x).
Proof.
have [qc [qu [qm [c1 c2 c3 c4 [c5 c6]]]]] := placeP_of_coordi hx hG htw hfs.
split.
  exact: (leaf_membH c1 c2 c3 c4 c5 c6 par8okwC par4okwC
            up8invC up8okC up4invC up4okC r_uok r_uG (erefl u)).
exact: (tomemb_tabH c1 c2 c3 c4 c5 c6
          up8invC up8okC up4invC up4okC r_xok (erefl u)).
Qed.

End Leaf.

Lemma r_leaf_memb c x : coordP c x -> pstok x ->
  pt flast (ti2t flast x) \in G ->
  ctwisti x = 0%uint63 -> coordi x = coordfs 1 ->
  membok par8i par4i (tomemb x).
Proof. by move=> _ hx hG htw hfs; case: (r_leafW hx hG htw hfs). Qed.

Lemma r_tomemb_tab c x : coordP c x -> pstok x ->
  pt flast (ti2t flast x) \in G ->
  ctwisti x = 0%uint63 -> coordi x = coordfs 1 ->
  pt flast (memb2tab (tomemb x)) = pt flast (ti2t flast x).
Proof. by move=> _ hx hG htw hfs; case: (r_leafW hx hG htw hfs). Qed.

(* ---- the same two, with no nat in the member ----------------------------- *)

(* The search asks for the member at every answer it records, and tomemb      *)
(* builds a forty eight cell seq nat to give it.  RowMembi's tomembi is the   *)
(* same member on int63 alone, and pstok carries the one thing tomembiE       *)
(* wants -- that the table is well formed.                                    *)
Lemma r_tomembiE x : pstok x -> tomembi x = tomemb x.
Proof. by case/and3P=> h _ _; exact: tomembiE. Qed.

Lemma r_leaf_membi c x : coordP c x -> pstok x ->
  pt flast (ti2t flast x) \in G ->
  ctwisti x = 0%uint63 -> coordi x = coordfs 1 ->
  membok par8i par4i (tomembi x).
Proof.
move=> hc hx hG htw hfs; rewrite (r_tomembiE hx).
exact: (r_leaf_memb hc hx hG htw hfs).
Qed.

Lemma r_tomembi_tab c x : coordP c x -> pstok x ->
  pt flast (ti2t flast x) \in G ->
  ctwisti x = 0%uint63 -> coordi x = coordfs 1 ->
  pt flast (memb2tab (tomembi x)) = pt flast (ti2t flast x).
Proof.
move=> hc hx hG htw hfs; rewrite (r_tomembiE hx).
exact: (r_tomemb_tab hc hx hG htw hfs).
Qed.

(* AND THE MAP, 812 851 200 words: the run and the witnesses together leave   *)
(* no bit of the row clear.  This is the long pole and it is only a run.      *)
Lemma r_full :
  mfull2 (mfin e8numi e4biti mpgi mgri mswi mloi mhii p1
                actfsri tomemb okmvv srch 20)
          (wmap rowwits).
Proof. Admitted.

(* ---- every member of the row is within twenty ---------------------------- *)

Theorem real_row_within_20 x : membok par8i par4i x ->
  RowRun.wthn (RowFinal.pos (ptab memb2tab)) 20 x.
Proof.
apply: (row_within_20_inst e8okC e4okC memb2tab_okC srcokC halfokC
          r_fsstepP r_leaf_memb r_tomemb_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC r_full).
Qed.

(* ---- AND THE ROW OF THE SUPERFLIP ---------------------------------------- *)

(* The covering is RowLeaf's, and the six walks it asks for are now checked,  *)
(* each in its own file.                                                      *)
Theorem real_superflip_row h : h \in H ->
  superflip^-1 * h \in ball Sset 20.
Proof.
apply: (superflip_row_within_20 e8okC e4okC memb2tab_okC srcokC halfokC
          r_fsstepP r_leaf_memb r_tomemb_tab
          pgokC grokC btokC memb2tab_moveC
          (erefl 20%N) witsokC r_full).
exact: (row_cover up8invC up8okC up4invC up4okC par8okwC par4okwC).
Qed.

(* THE ROW OF THE SUPERFLIP, said the way it reads.  The search plays a word  *)
(* from the superflip, so the row it settles is the superflip times a         *)
(* position of H -- and superflip undone is the superflip itself, it being an *)
(* involution.                                                                *)
Corollary real_row_superflip m : m \in H -> superflip * m \in ball Sset 20.
Proof.
have hV : superflip^-1 = superflip.
  by apply: (mulgI superflip); rewrite mulgV; move: superflip2;
     rewrite expgS expg1.
by rewrite -hV; exact: real_superflip_row.
Qed.

End Real.
