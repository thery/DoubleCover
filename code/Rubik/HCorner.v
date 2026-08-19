(* =========================================================================  *)
(*  HCorner.v -- obligation C for the corners.                               *)
(* =========================================================================  *)

(* The same argument as HEdge.v, twice more and simpler.  Two coordinates    *)
(* read the corners: which four places hold the U corners, seventy of them,  *)
(* and the seven free twists, 2187.  Both are functions of the same datum --  *)
(* where each corner sits and how it is turned -- and a turn moves that datum *)
(* by a rule with no position in it.                                         *)
(*                                                                            *)
(* WHAT REPLACES THE PAIRING.  An edge place has two facelets and a corner    *)
(* place has three, and what says a position keeps them together is that it   *)
(* commutes with ccyc, the turn of every corner in place.  Phase1 has that as *)
(* cubcP, with everything needed of it; what is missing is the table form,    *)
(* and cubctE below is it, the mirror of Coordfsi.cubtE.                      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound HEdge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the guard, on a table ----------------------------------------------- *)

Definition cubct (t : seq nat) : bool :=
  all (fun f => nth 0%N ccyct (nth 0%N t f) == nth 0%N t (nth 0%N ccyct f))
      (iota 0 nfacelet).

Lemma ccyct_ltn m : (m < nfacelet)%N -> (nth 0%N ccyct m < nfacelet)%N.
Proof. by apply: ccyct_lt. Qed.

Lemma ccycnE (t : seq nat) m : tab_ok flast t -> (m < nfacelet)%N ->
  ccyc (pt flast t (inord m)) = inord (nth 0%N ccyct (nth 0%N t m)).
Proof.
move=> tok mL.
have /and3P[/eqP sz /allP hall _] := tok.
have tlt : (nth 0%N t m < nfacelet)%N by apply: hall; rewrite mem_nth // sz.
by rewrite ptE // inordK // ccycE inordK.
Qed.

Lemma cubctE t : tab_ok flast t -> cubcP (pt flast t) = cubct t.
Proof.
move=> tok; have /and3P[/eqP sz /allP hall _] := tok.
have tlt m : (m < nfacelet)%N -> (nth 0%N t m < nfacelet)%N.
  by move=> mL; apply: hall; rewrite mem_nth // sz.
have key m : (m < nfacelet)%N ->
    (ccyc (pt flast t (inord m)) == pt flast t (ccyc (inord m)))
      = (nth 0%N ccyct (nth 0%N t m) == nth 0%N t (nth 0%N ccyct m)).
  move=> mL; have clt : (nth 0%N ccyct m < nfacelet)%N by apply: ccyct_ltn.
  rewrite (ccycnE tok mL) ccycE inordK // ptE // inordK //.
  by rewrite inord_eq ?ccyct_ltn ?tlt.
apply/forallP/allP => [h m|h f].
  by rewrite mem_iota add0n => /andP[_ mL]; rewrite -key //; exact: h.
rewrite -(inord_val f) key ?ltn_ord //.
by apply: h; rewrite mem_iota add0n ltn_ord.
Qed.

(* ---- and it survives a turn ---------------------------------------------- *)

Lemma cubct_mvt : all (fun m => cubct (mvt m)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma cubct_comp t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  cubct t1 -> cubct t2 -> cubct (comp_tab t1 t2).
Proof.
move=> ok1 ok2 c1 c2.
rewrite -(cubctE (tab_ok_comp ok1 ok2)) -ptM //.
by apply: cubcPM; rewrite cubctE.
Qed.

Lemma cubct_inv t : tab_ok flast t -> cubct t -> cubct (inv_tab flast t).
Proof.
move=> tok ct.
rewrite -(cubctE (tab_ok_inv tok)) -ptV //.
by apply: cubcPI; rewrite cubctE.
Qed.

Lemma cubct_step (a : arr) m : tabi_ok flast a -> (m < nq)%N ->
  cubct (ti2t flast a) -> cubct (ti2t flast (comp_tabi flast a (mvq m))).
Proof.
move=> aok mL ca.
have /eqP mE := allP ti2t_mvq _ (mem_iota0 mL).
rewrite (ti2t_comp n47_small n47_len aok (tabi_ok_mvq mL)) mE.
by apply: cubct_comp => //; [apply: mvt_ok | apply: (allP cubct_mvt);
   apply: mem_iota0].
Qed.

Lemma cubct_invi a : tabi_ok flast a -> cubct (ti2t flast a) ->
  cubct (ti2t flast (inv_tabi flast a)).
Proof.
by move=> aok ca; rewrite (ti2t_inv n47_small n47_len aok); apply: cubct_inv.
Qed.

(* ---- what a turn does to a corner place ---------------------------------- *)

(* Where the sticker at the primary facelet of the prototype's place j comes  *)
(* from: a corner facelet, so a place and a slot.  cplc is that place, back   *)
(* in the prototype's numbering, and ctw the slot, which is the twist the     *)
(* cubie picks up on the way.                                                 *)
Definition cidx (m j : nat) : nat :=
  index (nth 0%N (inv_tab flast (mvt m)) (nth 0%N cprim (rplace j))) cflat.

Definition cplc (m j : nat) : nat := index (cidx m j %/ 3)%N oc2r.
Definition ctw  (m j : nat) : nat := (cidx m j %% 3)%N.

Lemma cmv_tab :
  all (fun m => all (fun j =>
        [&& cidx m j < 24, cplc m j < 8 &
            rplace (cplc m j) == (cidx m j %/ 3)%N]%N) (iota 0 8))
      (iota 0 nq).
Proof. by vm_compute. Qed.

(* ---- what is left -------------------------------------------------------- *)

(* From here it is HEdge.v again: read the place and the twist off the       *)
(* sticker -- getn_step gives the sticker, and the guard says the cubie is   *)
(* the same whichever of the three facelets of its place it is read from --  *)
(* then the datum, then the two rankings, then the sweeps, which are 70 x 12 *)
(* and 2187 x 12 and so smaller than the edges'.                             *)
