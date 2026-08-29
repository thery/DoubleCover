(* =========================================================================  *)
(*  RowFoldWrite.v -- what one write of the folded level is worth.            *)
(* =========================================================================  *)

(* RowFoldLvl.v proves the folded level and the folded run sound, on two      *)
(* hypotheses: Qlo_st and Qhi_st, one for each half of a source word.  They   *)
(* say that a member reading a bit of what the level ors in is one move of H  *)
(* out from a member the source had.  This file discharges them.              *)
(*                                                                            *)
(* THE GATHER IS THE PLAIN WRITE ON THE RENAMED SOURCE, and every leg of that *)
(* is now a fact: the page leg is RowFoldSrc.gathM, the group leg is the way  *)
(* the tables are indexed and needs no lemma at all, and the bit leg is       *)
(* RowFoldGath.cloX_bit.  What the member does under the two is               *)
(* RowFoldSrc.gather_conj_memb for the renaming and RowMembChk.memb2tab_moveC *)
(* for the move.                                                              *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Root Coord.
Require Import Diameter Moves Sym16 Sym16Row.
Require Import Row RowMap RowRun RowFinal RowInst.
Require Import RowTabL RowTabP RowTab RowMemb RowMembChk.
Require Import RowFold RowFoldOk RowFoldMem RowFoldPart.
Require Import RowTabF RowFoldTab RowFoldSym RowFoldConj RowFoldGath RowFoldSrc.
Require Import RowFoldLvl.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- where a member of the row stands ------------------------------------ *)

(* The row is the superflip coset, so the position a member stands for is the *)
(* superflip undone and then the member's own permutation.  It is RowInst's   *)
(* pos, written out on the real tables.                                       *)
Definition mposC (pg gr bt : int) : {perm facelet} :=
  superflip^-1 * pt flast (memb2tab (unplace e8invi e4ofi par8i par4i pg gr bt)).

Definition PdC (d : nat) (pg gr bt : int) : Prop :=
  mposC pg gr bt \in ball Sset d.

Lemma PdCW d pg gr bt : PdC d pg gr bt -> PdC d.+1 pg gr bt.
Proof. by apply: (subsetP (ball_mono Sset d)). Qed.

(* ---- the sixteen do not move the row, at any depth ----------------------- *)

(* Sym16Row.sym16_row says this at twenty; the run needs it at every depth,   *)
(* and needs it both ways round, because two members that fold together are   *)
(* each other's image under two of the sixteen.                               *)
Lemma sym16_rown i n h : (i < 16)%N ->
  superflip^-1 * h \in ball Sset n ->
  superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i)) \in ball Sset n.
Proof.
move=> hi hb; have := sym16_ball hi hb.
by rewrite conjMg conjVg (sym16_sf hi).
Qed.

Lemma sym16_rownV i n h : (i < 16)%N ->
  superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i)) \in ball Sset n ->
  superflip^-1 * h \in ball Sset n.
Proof.
move=> hi hb.
have he : superflip^-1 * (h ^ pt 47 (nth [::] sym16ts i))
        = (superflip^-1 * h) ^ pt 47 (nth [::] sym16ts i).
  by rewrite conjMg conjVg (sym16_sf hi).
rewrite he in hb.
by have := sym16_ballV hi hb; rewrite conjgK.
Qed.

(* ---- so a member and the place it folds to stand or fall together -------- *)

Lemma fold_conjC pg gr bt : inrange pg gr bt ->
  exists2 i, (i < 16)%N &
    mposC (PArray.get fkeepi (fkpt (PArray.get fpgi pg)))
          (sgrmv fsgri (fren (PArray.get fpgi pg))
             (Uint63.lxor (fpar (PArray.get fpgi pg))
                (if (bt <? 12)%uint63 then 0%uint63 else 1%uint63)) gr)
          (sbtmv fsbti (fren (PArray.get fpgi pg)) bt)
    = mposC pg gr bt ^ pt 47 (nth [::] sym16ts i).
Proof.
move=> hr; have [i hi he] := fold_conj_memb hr.
exists i; first exact: hi.
by rewrite /mposC he conjMg conjVg (sym16_sf hi).
Qed.

(* ---- one source bit is a member the source claims ------------------------ *)

(* The gather reads the source at a KEPT page, and RowFoldGath.keep_ftest     *)
(* says the folded map read there is the slot itself -- no renaming to undo.  *)
(* So a bit of the word the level reads is a member the source map claims.    *)
Lemma gsrc_memb src r k g i d :
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat g < ngroupn)%N ->
  (to_nat i < nbitn)%N ->
  soundatf fpgi fsgri fsbti (PdC d) src ->
  ~~ (Uint63.land (fget src (fkpt (gw r k)) g) (bitof i) =? 0)%uint63 ->
  PdC d (gp r k) g i.
Proof.
move=> hr hk hg hi hsrc hb.
have [_ hkp _ _ _] := gathR hr hk.
have hp : (PArray.get fkeepi (fkpt (gw r k)) <? npagei)%uint63.
  exact: (Row.iter_at keepRCP hkp).
have hin : inrange (gp r k) g i.
  by apply/and3P; split; [exact: hp | apply/nltbP; exact: hg |
                          apply/nltbP; exact: hi].
apply: (hsrc _ _ _ hin).
by rewrite (@keep_ftest src (fkpt (gw r k)) g i hkp hg hi).
Qed.

(* ---- the renamed source member is a member ------------------------------- *)

Lemma gather_inrange r k g i : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  (to_nat g < ngroupn)%N -> (to_nat i < nbitn)%N ->
  inrange (gq r k) (sgrmv fsgri (gu r k) (Ptyof (gp r k) i) g)
          (sbtmv fsbti (gu r k) i).
Proof.
move=> hr hk hg hi.
have [hu hkp hq _ _] := gathR hr hk.
have hpk : (to_nat (gp r k) < npagen)%N.
  by apply/nltbP; exact: (Row.iter_at keepRCP hkp).
have hp : (to_nat (Ptyof (gp r k) i) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP hpk) hi).
apply/and3P; split.
- by apply/nltbP; exact: hq.
- exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hp) hg).
exact: (Row.iter_at (Row.iter_at sbtRCP hu) hi).
Qed.

(* ---- and the member the gather writes is one move of H further out ------- *)

(* THE GATHER IS THE PLAIN WRITE ON THE RENAMED SOURCE, and this is that      *)
(* sentence as a lemma: the renaming costs nothing because the sixteen keep   *)
(* the row, and the move costs one because it is a move of H.                 *)
Lemma gdst_memb r k g i d : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  (to_nat g < ngroupn)%N -> (to_nat i < nbitn)%N ->
  inrange (gp r k) g i -> PdC d (gp r k) g i ->
  PdC d.+1 (PArray.get fkeepi r)
       (grmv mgri k (sgrmv fsgri (gu r k) (Ptyof (gp r k) i) g))
       (btmv btmvi k (sbtmv fsbti (gu r k) i)).
Proof.
move=> hr hk hg hi hin hP.
have hin' := gather_inrange hr hk hg hi.
have [j hj hje] := gather_conj_memb hr hk hin.
have hQ : mposC (gq r k) (sgrmv fsgri (gu r k) (Ptyof (gp r k) i) g)
                (sbtmv fsbti (gu r k) i) \in ball Sset d.
  by rewrite /mposC hje; apply: sym16_rown; [exact: hj | exact: hP].
have -> : PArray.get fkeepi r = pgmv mpgi k (gq r k).
  by rewrite /pgmv (gathM hr hk).
rewrite /PdC /mposC (memb2tab_moveC hk hin') mulgA.
by apply: ball_step; [exact: hQ | exact: (hmv_Sset hk)].
Qed.

(* ---- the parity fsrc carries is a parity --------------------------------- *)

Definition gparC : bool :=
  iter nrepn 0%uint63
    (fun r => iter nhn 0%uint63 (fun k => (fpar (gw r k) <? 2)%uint63)).
Lemma gparCP : gparC. Proof. by vm_compute. Qed.

Lemma gparCE : gparC =
  iter nrepn 0%uint63
    (fun r => iter nhn 0%uint63 (fun k => (fpar (gw r k) <? 2)%uint63)).
Proof. by []. Qed.

Lemma gparP r k : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  (to_nat (fpar (gw r k)) < 2)%N.
Proof.
move=> hr hk.
have h1 := gparCP; rewrite gparCE in h1.
have /nltbP h2 := Row.iter_at (Row.iter_at h1 hr) hk.
by move: h2; rewrite to_nat_two.
Qed.

(* the low half of a word is read at the parity fsrc carries, unturned *)
Lemma glo_pty r k i : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  (i <? 12)%uint63 -> Ptyof (gp r k) i = fpar (gw r k).
Proof.
move=> hr hk hi.
have hfp := gparP hr hk.
have [_ hkp _ _ hw] := gathR hr hk.
have hpk : (to_nat (gp r k) < npagen)%N.
  by apply/nltbP; exact: (Row.iter_at keepRCP hkp).
have hf : fpar (PArray.get fpgi (gp r k)) = fpar (gw r k).
  by rewrite hw; apply/eqP; have /andP[_ h] := Row.iter_at fpgCP hpk; exact: h.
rewrite hi hf.
by case: (int_lt2 hfp) => ->; vm_compute.
Qed.

(* ---- undoing one of the sixteen ------------------------------------------ *)

Lemma ball_conjV i n (h : {perm facelet}) : (i < 16)%N ->
  h ^ pt 47 (nth [::] sym16ts i) \in ball Sset n -> h \in ball Sset n.
Proof. by move=> hi hb; have := sym16_ballV hi hb; rewrite conjgK. Qed.

(* =========================================================================  *)
(*  Qlo -- one write for the low half of a source word.                       *)
(* =========================================================================  *)

(* The write goes to one group of the page being filled, at the bits the low  *)
(* half of a source word is carried to.  A member that reads one of those     *)
(* bits folds to exactly that slot -- fslot_inj -- so it is the source member *)
(* renamed and then moved, and that is one move of H further out.             *)
Lemma QloC d : Qlo_st fpgi fsrci fsgri fsloi fshii fsbti mgri mswi mloi mhii
                      (PdC d) (PdC d.+1).
Proof.
move=> src r k g pg gr bt hr hk hg hsrc.
cbv zeta.
move=> hin h1 h2 h3.
have [hu hkp _ _ _] := gathR hr hk.
have /and3P[hpg hgr hbt] := hin.
have hpgn : (to_nat pg < npagen)%N by apply/nltbP; exact: hpg.
have hbtn : (to_nat bt < nbitn)%N by apply/nltbP; exact: hbt.
have hgrn : (to_nat gr < ngroupn)%N by apply/nltbP; exact: hgr.
have hfr : (to_nat (fren (PArray.get fpgi pg)) < nsymn)%N.
  by apply/nltbP; exact: (Row.iter_at frnRCP hpgn).
have hjb : (sbtmv fsbti (fren (PArray.get fpgi pg)) bt <? nbiti)%uint63.
  exact: (Row.iter_at (Row.iter_at sbtRCP hfr) hbtn).
have hlo : (to_nat (Uint63.land (fget src (fkpt (gw r k)) g) lo12)
              < RowFoldSym.nhalfn)%N.
  by apply/nltbP; exact: lo12_lt _.
(* THE WORD THE LEVEL ORS IN, NAMED.  Left as it stands the unifier cannot   *)
(* see cloX in it, and every lemma about the write is stated on cloX.        *)
have h3' : ~~ (Uint63.land
                 (cloX (gu r k) k
                    (Uint63.land (fget src (fkpt (gw r k)) g) lo12))
                 (bitof (sbtmv fsbti (fren (PArray.get fpgi pg)) bt))
               =? 0)%uint63 := h3.
have [i hi [hbi hje]] := cloX_bit hu hk hlo hjb h3'.
have hi12 : (i <? 12)%uint63 by apply/nltbP; exact: hi.
have hin24 : (to_nat i < nbitn)%N by apply: (leq_trans hi); vm_compute.
(* the bit came from a bit of the source word *)
have hbv : ~~ (Uint63.land (fget src (fkpt (gw r k)) g) (bitof i) =? 0)%uint63.
  rewrite (@test_bit (fget src (fkpt (gw r k)) g) i (lt_half_digits hi12)).
  rewrite -(@bit_lohalf (fget src (fkpt (gw r k)) g) i hi12).
  rewrite -(@test_bit (Uint63.land (fget src (fkpt (gw r k)) g) lo12) i
              (lt_half_digits hi12)).
  by rewrite hbi.
(* and a bit of the source word is a member the source claims *)
have hinsrc : inrange (gp r k) g i.
  have hp : (PArray.get fkeepi (fkpt (gw r k)) <? npagei)%uint63.
    exact: (Row.iter_at keepRCP hkp).
  by apply/and3P; split; [exact: hp | apply/nltbP; exact: hg |
                          apply/nltbP; exact: hin24].
have hPsrc := gsrc_memb hr hk hg hin24 hsrc hbv.
have hPdst := gdst_memb hr hk hg hin24 hinsrc hPsrc.
rewrite (glo_pty hr hk hi12) in hPdst.
(* the slot the write goes to is the slot the member folds to *)
have hpty : (to_nat (fpar (gw r k)) < nptyn)%N := gparP hr hk.
have hsg : (sgrmv fsgri (gu r k) (fpar (gw r k)) g <? ngroupi)%uint63 :=
  Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hpty) hg.
have hsgn : (to_nat (sgrmv fsgri (gu r k) (fpar (gw r k)) g) < ngroupn)%N.
  by apply/nltbP; exact: hsg.
have hG : (grmv mgri k (sgrmv fsgri (gu r k) (fpar (gw r k)) g)
            <? ngroupi)%uint63.
  exact: (Row.iter_at (Row.iter_at grokC hk) hsgn).
have hp2 : (to_nat (Ptyof pg bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP hpgn) hbtn).
have hGof : (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr
              <? ngroupi)%uint63.
  exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hfr) hp2) hgrn).
have h2' : Uint63.add (poff r)
             (grmv mgri k (sgrmv fsgri (gu r k) (fpar (gw r k)) g))
         = Uint63.add (poff (fkpt (PArray.get fpgi pg)))
             (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr) := h2.
have [hReq hGeq] := fslot_inj hG hGof h1 h2'.
(* THE THREE EQUATIONS PUT INTO THE GOAL, not into the hypothesis: r occurs *)
(* inside the source word too, and rewriting it there loses the bit.         *)
have hPdst2 : PdC d.+1 (PArray.get fkeepi (fkpt (PArray.get fpgi pg)))
                (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr)
                (sbtmv fsbti (fren (PArray.get fpgi pg)) bt).
  by rewrite -hReq -hGeq hje; exact: hPdst.
(* and the place a member folds to holds that member renamed *)
have [j hj hje2] := fold_conjC hin.
rewrite /PdC hje2 in hPdst2.
by apply: (ball_conjV hj hPdst2).
Qed.
