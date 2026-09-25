(* =========================================================================  *)
(*  RowCoordGuard.v -- at a leaf of the run, bitleaf takes its fast branch.   *)
(* =========================================================================  *)

(* bitleaf tests that the eight outer edge places hold outer edges, and falls *)
(* back on the old leaf otherwise.  At a leaf of the run the test always      *)
(* passes: a solved coordinate keeps each edge place in its own half of the   *)
(* slice (RowInH's fifth condition), and read on the twenty that is the test. *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst RowMemb RowLeaf RowInH.
Require Import Lehmer RowCub RowCubi RowCubInst RowLeafFast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Lemma leaf_guard c y : ycoordP c y -> ypstok y -> yposp y \in G ->
  ycsolved c -> lbguard y.
Proof.
move=> hc hy hG hs.
have hx : RowInst.pstok (y2ti y) by case/andP: hy.
have [htw hfs] := RowInst.csolvedbP hc hx hs.
have xok : tabi_ok flast (y2ti y) := ypstok_tabi hy.
have tok : tab_ok flast (ti2t flast (y2ti y)) := xok.
have hG' := RowInst.posp_G hG.
have hok := G_coord_solved_hok tok hG'.
have htw' : coordtw (pt flast (ti2t flast (y2ti y))) = 0%uint63.
  by rewrite (ctwisttE xok) -(ctwistiE xok) htw.
have hfs' : coordfs (pt flast (ti2t flast (y2ti y))) = coordfs 1.
  by rewrite (coordtE xok) -(coordiE xok) hfs.
have := hok htw' hfs'.
have /andP[/andP[hyok htab] _] := hy.
rewrite (ypstok_ti hy) /cub2tabR (inv_tabK htab).
case/and5P => _ _ _ _ /allP h5.
set Y := a2y y.
(* the eight outer places hold outer edges *)
have hout q : (q < 8)%N -> (yeg Y q < 8)%N.
  move=> hq; have hq12 : (q < 12)%N by apply: ltn_trans hq _.
  have := h5 q; rewrite mem_iota add0n hq12 => /(_ isT) /eqP.
  rewrite (eposn_prim hyok hq12) leqNgt [(8 <= q)%N]leqNgt hq /=.
  by move/negbT; rewrite negbK.
(* read on the twenty, the entry is below sixteen *)
have hl q : (q < 8)%N -> (PArray.get y (of_nat (8 + q)) <? 16)%uint63.
  move=> hq; apply/nltbP.
  have hq20 : (8 + q < 20)%N.
    by rewrite -[20%N]/(8 + 12)%N ltn_add2l; apply: ltn_trans hq _.
  rewrite -(a2y_nth y hq20).
  by have := hout q hq; rewrite /yeg ltn_divLR.
(* and the test is the eight of them *)
rewrite /lbguard.
move: (hl 0%N isT) (hl 1%N isT) (hl 2%N isT) (hl 3%N isT)
      (hl 4%N isT) (hl 5%N isT) (hl 6%N isT) (hl 7%N isT).
by move=> -> -> -> -> -> -> -> ->.
Qed.
