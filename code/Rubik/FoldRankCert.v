(* =========================================================================  *)
(*  FoldRankCert.v -- The orbit check, rebuilt as Farp1's certificate over    *)
(*     ranks.                                                                 *)
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

(* the rank loop's guard, read the other way round.  Stated on int63 and
   proved through nltbP and nlebP: the nat value of nfsi never appears.       *)
Lemma ltb_of_leb r : (nfsi <=? r)%uint63 = false -> (r <? nfsi)%uint63.
Proof.
move=> h; apply/nltbP; rewrite ltnNge; apply/negP => hle.
by move: h; rewrite (introT (nlebP _ _) hle).
Qed.

Section Bridge.

Variable T : PArray.array arr.

(* what Fold.Dfoldi_step_of_check hands over, at Phase1's own folded read:
   Dp1ri IS Dfoldi at frep, fsym and twsym read from the table's slots        *)
Hypothesis hstep : forall tw r k,
  (to_nat tw < ntwist)%N -> (r <? nfsi)%uint63 -> (k < 18)%N ->
  (Dp1ri T tw r <=? incr (Dp1ri T (acttwi tw k) (actfsr r k)))%uint63.

(* the eighteen moves, at one rank                                            *)
Lemma p1stepRk_of_step tw r : (to_nat tw < ntwist)%N -> (r <? nfsi)%uint63 ->
  p1stepRk T tw r.
Proof.
move=> twL rL; rewrite /p1stepRk.
apply/allP => ki; rewrite midxiE => /mapP[k]; rewrite mem_iota add0n leq0n.
by move=> kL ->; rewrite acttwiiE actfsriE; exact: hstep.
Qed.

(* every rank, by rebuilding the 2 ^ 20 loop from the pointwise fact          *)
Lemma p1checkTwr_of_step tw : (to_nat tw < ntwist)%N -> p1checkTwr T tw.
Proof.
move=> twL; rewrite /p1checkTwr all_powiE; last by vm_compute.
apply: all_pow_all => r.
(* boolP SUBSTITUTES: in each branch the guard in the goal is already the
   constant, so there is nothing left to rewrite                              *)
have [hle|hlt] := boolP (nfsi <=? r)%uint63 => //.
exact: p1stepRk_of_step twL (ltb_of_leb (negPf hlt)).
Qed.

(* and every twist                                                            *)
Lemma p1checkStepr_of_step : p1checkStepr T.
Proof.
rewrite /p1checkStepr; apply/allP => t.
rewrite mem_iota add0n leq0n => tL.
apply: p1checkTwr_of_step.
(* of_natK needs t < nwB, and a bare `_ < nwB' goal is 2 ^ 63 in successors:
   bound by a power of two first, then nwB_pow                                *)
have tB : (t < nwB)%N.
  apply: leq_trans (_ : (2 ^ 12 <= nwB)%N); last by rewrite nwB_pow leq_exp2l.
  by apply: leq_trans tL _; vm_compute.
by rewrite of_natK.
Qed.

End Bridge.
