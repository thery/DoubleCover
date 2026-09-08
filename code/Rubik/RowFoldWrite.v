(* =========================================================================  *)
(*  RowFoldWrite.v -- what one write of the folded level is worth.            *)
(* =========================================================================  *)

(* QloC and QhiC, the two hypotheses RowFoldLvl leaves open, one for each     *)
(* half of a source word: a member reading a bit the level sets is one move   *)
(* of H out from a member the source had.                                     *)

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
  superflip^-1 * pt flast (memb2tab (unplace24 e8invi e4ofi par8i par4i pg gr bt)).

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

Lemma fold_conjC pg gr bt : inrange24 pg gr bt ->
  exists2 i, (i < 16)%N &
    mposC (fkeep2 (fkpt (PArray.get fpgi pg)) (fhlf (PArray.get fpgi pg)))
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
Lemma gsrc_memb src r k h g i d :
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) -> (to_nat g < ngroupn)%N ->
  (to_nat i < nbitn)%N ->
  soundatf fpgi fsgri fsbti (PdC d) src ->
  ~~ (Uint63.land (fget src (fkpt (gw r k)) g)
        (bitof (fbit (gsh r k h) i)) =? 0)%uint63 ->
  PdC d (gp r k h) g i.
Proof.
move=> hr hk hh hgo hg hi hsrc hb.
have [_ hkp _ _ _] := gathR hr hk hh hgo.
have hS := gathS hr hk hh hgo.
(* THE SOURCE HALF, and it is a half: either the one fpg names or the low bit *)
(* of fsrc2, and both are one bit.                                            *)
have hsh : (to_nat (gsh r k h) < 2)%N.
  case: (Uint63.eqb h 0); first exact: fhlf_lt2.
  rewrite landC; have -> : (2 = 2 ^ 1)%N by [].
  by apply: to_nat_land_bound; rewrite to_nat_1.
have hp : (gp r k h <? npagei)%uint63.
  exact: (Row.iter_at (Row.iter_at keepRCP hkp) hsh).
have hin : inrange24 (gp r k h) g i.
  by apply/and3P; split; [exact: hp | apply/nltbP; exact: hg |
                          apply/nltbP; exact: hi].
apply: (hsrc _ _ _ hin).
by rewrite (@keep_ftest src (fkpt (gw r k)) (gsh r k h) g i hkp hsh hS hg hi).
Qed.

(* ---- the renamed source member is a member ------------------------------- *)

Lemma gather_inrange r k h g i : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  (to_nat g < ngroupn)%N -> (to_nat i < nbitn)%N ->
  inrange24 (gq r k h) (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) i) g)
          (sbtmv fsbti (gu r k h) i).
Proof.
move=> hr hk hh hgo hg hi.
have [hu hkp hq _ _] := gathR hr hk hh hgo.
have hsh : (to_nat (gsh r k h) < 2)%N.
  case: (Uint63.eqb h 0); first exact: fhlf_lt2.
  rewrite landC; have -> : (2 = 2 ^ 1)%N by [].
  by apply: to_nat_land_bound; rewrite to_nat_1.
have hpk : (to_nat (gp r k h) < npagen)%N.
  by apply/nltbP; exact: (Row.iter_at (Row.iter_at keepRCP hkp) hsh).
have hp : (to_nat (Ptyof (gp r k h) i) < nptyn)%N.
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
Lemma gdst_memb r k h g i d : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  (to_nat g < ngroupn)%N -> (to_nat i < nbitn)%N ->
  inrange24 (gp r k h) g i -> PdC d (gp r k h) g i ->
  PdC d.+1 (fkeep2 r h)
       (grmv mgri k (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) i) g))
       (btmv btmvi k (sbtmv fsbti (gu r k h) i)).
Proof.
move=> hr hk hh hgo hg hi hin hP.
have hin' := gather_inrange hr hk hh hgo hg hi.
have [j hj hje] := gather_conj_memb hr hk hh hgo hin.
have hQ : mposC (gq r k h) (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) i) g)
                (sbtmv fsbti (gu r k h) i) \in ball Sset d.
  by rewrite /mposC hje; apply: sym16_rown; [exact: hj | exact: hP].
have -> : fkeep2 r h = pgmv mpgi k (gq r k h).
  by rewrite /pgmv (gathM hr hk hh hgo).
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

Lemma gparP r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  (to_nat (fpar (gw r k)) < 2)%N.
Proof.
move=> hr hk hh hgo.
have h1 := gparCP; rewrite gparCE in h1.
have /nltbP h2 := Row.iter_at (Row.iter_at h1 hr) hk.
by move: h2; rewrite to_nat_two.
Qed.

(* the low half of a word is read at the parity fsrc carries, unturned *)
Lemma glo_pty r k h i : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  (i <? 12)%uint63 -> Ptyof (gp r k h) i = fpar (gw r k).
Proof.
move=> hr hk hh hgo hi.
have hfp := gparP hr hk hh hgo.
have [_ hkp _ _ hw] := gathR hr hk hh hgo.
have hsh : (to_nat (gsh r k h) < 2)%N.
  case: (Uint63.eqb h 0); first exact: fhlf_lt2.
  rewrite landC; have -> : (2 = 2 ^ 1)%N by [].
  by apply: to_nat_land_bound; rewrite to_nat_1.
have hpk : (to_nat (gp r k h) < npagen)%N.
  by apply/nltbP; exact: (Row.iter_at (Row.iter_at keepRCP hkp) hsh).
have hf : fpar (PArray.get fpgi (gp r k h)) = fpar (gw r k).
  by rewrite hw; apply/eqP; have /andP[_ hq] := Row.iter_at fpgCP hpk; exact: hq.
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
Lemma QloC d : Qlo_st fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti mgri mswi mloi mhii
                      (PdC d) (PdC d.+1).
Proof.
move=> src r k h g pg gr bt hr hk hh hg hgo hsrc.
cbv zeta.
move=> hin h1 h2 h3.
have [hu hkp _ _ _] := gathR hr hk hh hgo.
have /and3P[hpg hgr hbt] := hin.
have hpgn : (to_nat pg < npagen)%N by apply/nltbP; exact: hpg.
have hbtn : (to_nat bt < nbitn)%N by apply/nltbP; exact: hbt.
have hgrn : (to_nat gr < ngroupn)%N by apply/nltbP; exact: hgr.
have hfr : (to_nat (fren (PArray.get fpgi pg)) < nsymn)%N.
  by apply/nltbP; exact: (Row.iter_at frnRCP hpgn).
have hjb : (sbtmv fsbti (fren (PArray.get fpgi pg)) bt <? nbiti)%uint63.
  exact: (Row.iter_at (Row.iter_at sbtRCP hfr) hbtn).
(* THE SOURCE HALF, and it is a half *)
have hsh : (to_nat (gsh r k h) < 2)%N.
  case: (Uint63.eqb h 0); first exact: fhlf_lt2.
  rewrite landC; have -> : (2 = 2 ^ 1)%N by [].
  by apply: to_nat_land_bound; rewrite to_nat_1.
have hlo : (to_nat (Uint63.land
                      (if Uint63.eqb (gsh r k h) 0
                       then Uint63.land (fget src (fkpt (gw r k)) g) allbits24
                       else Uint63.land
                              (Uint63.lsr (fget src (fkpt (gw r k)) g) nbiti)
                              allbits24) lo12)
              < RowFoldSym.nhalfn)%N.
  by apply/nltbP; exact: lo12_lt _.
(* THE WORD THE LEVEL ORS IN, NAMED, AND PUT IN ITS HALF.  Left as it stands  *)
(* the unifier cannot see cloX in it, and every lemma about the write is      *)
(* stated on cloX; the outer shift is what picks the destination half.        *)
have h3a : ~~ (Uint63.land
                 (Uint63.lsl
                    (clo (gu r k h) k
                       (Uint63.land
                          (if Uint63.eqb (gsh r k h) 0
                           then Uint63.land (fget src (fkpt (gw r k)) g) allbits24
                           else Uint63.land
                                  (Uint63.lsr (fget src (fkpt (gw r k)) g) nbiti)
                                  allbits24) lo12))
                    (fofs h (if Uint63.eqb (PArray.get mswi k) 0
                             then 0 else 12)))
                 (bitof (fbit (fhlf (PArray.get fpgi pg))
                     (sbtmv fsbti (fren (PArray.get fpgi pg)) bt)))
               =? 0)%uint63 := h3.
rewrite (cloX_fofs _ _ _ hh) in h3a.
(* THE DESTINATION HALF IS THE HALF THE PAGE NAMES.  Two halves share no bit, *)
(* so a member reading what was written reads the half it was written into.   *)
have [hhE h3b] := fbit_half (cloX_lt24 hu hk hlo) (fhlf_lt2 _) hh hjb h3a.
have [i hi [hbi hje]] := cloX_bit hu hk hlo hjb h3b.
have hi12 : (i <? 12)%uint63 by apply/nltbP; exact: hi.
have hin24 : (to_nat i < nbitn)%N by apply: (leq_trans hi); vm_compute.
have hib : (i <? nbiti)%uint63 by apply/nltbP.
(* the bit came from a bit of the half the level read, so from a bit of the   *)
(* source cell, at the place that half puts it                               *)
have hbv : ~~ (Uint63.land (fget src (fkpt (gw r k)) g)
                 (bitof (fbit (gsh r k h) i)) =? 0)%uint63.
  have hfd : (fbit (gsh r k h) i <? digits)%uint63.
    by apply: lt_digits; apply: fbit_lt.
  rewrite (test_bit _ hfd) -(bit_fhalf _ hsh hib) -(bit_lohalf _ hi12).
  by rewrite -(test_bit _ (lt_half_digits hi12)) hbi.
(* and a bit of the source cell is a member the source claims *)
have hinsrc : inrange24 (gp r k h) g i.
  have hp : (gp r k h <? npagei)%uint63.
    exact: (Row.iter_at (Row.iter_at keepRCP hkp) hsh).
  by apply/and3P; split; [exact: hp | apply/nltbP; exact: hg |
                          apply/nltbP; exact: hin24].
have hPsrc := gsrc_memb hr hk hh hgo hg hin24 hsrc hbv.
have hPdst := gdst_memb hr hk hh hgo hg hin24 hinsrc hPsrc.
rewrite (glo_pty hr hk hh hgo hi12) in hPdst.
(* the slot the write goes to is the slot the member folds to *)
have hpty : (to_nat (fpar (gw r k)) < nptyn)%N := gparP hr hk hh hgo.
have hsg : (sgrmv fsgri (gu r k h) (fpar (gw r k)) g <? ngroupi)%uint63 :=
  Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hpty) hg.
have hsgn : (to_nat (sgrmv fsgri (gu r k h) (fpar (gw r k)) g) < ngroupn)%N.
  by apply/nltbP; exact: hsg.
have hG : (grmv mgri k (sgrmv fsgri (gu r k h) (fpar (gw r k)) g)
            <? ngroupi)%uint63.
  exact: (Row.iter_at (Row.iter_at grokC hk) hsgn).
have hp2 : (to_nat (Ptyof pg bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP hpgn) hbtn).
have hGof : (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr
              <? ngroupi)%uint63.
  exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hfr) hp2) hgrn).
have h2' : Uint63.add (poff r)
             (grmv mgri k (sgrmv fsgri (gu r k h) (fpar (gw r k)) g))
         = Uint63.add (poff (fkpt (PArray.get fpgi pg)))
             (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr) := h2.
have [hReq hGeq] := fslot_inj hG hGof h1 h2'.
(* THE THREE EQUATIONS PUT INTO THE GOAL, not into the hypothesis: r occurs *)
(* inside the source word too, and rewriting it there loses the bit.         *)
have hPdst2 : PdC d.+1 (fkeep2 (fkpt (PArray.get fpgi pg)) (fhlf (PArray.get fpgi pg)))
                (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr)
                (sbtmv fsbti (fren (PArray.get fpgi pg)) bt).
  by rewrite -hReq hhE -hGeq hje; exact: hPdst.
(* and the place a member folds to holds that member renamed *)
have [j hj hje2] := fold_conjC hin.
rewrite /PdC hje2 in hPdst2.
by apply: (ball_conjV hj hPdst2).
Qed.

(* =========================================================================  *)
(*  Qhi -- one write for the high half of a source word.                      *)
(* =========================================================================  *)

(* The same, with three differences: the half is the word twelve places up,   *)
(* the parity the group is read at is turned over, and the bit of the source  *)
(* is twelve places up too.  The twelve place arithmetic is one small walk.   *)

Definition ghiC : bool :=
  iter nlon 0%uint63 (fun i =>
    [&& (Uint63.sub (Uint63.add nloi i) nloi =? i)%uint63,
        (nloi <=? Uint63.add nloi i)%uint63,
        (Uint63.add nloi i <? nbiti)%uint63 &
        ~~ (Uint63.add nloi i <? 12)%uint63]).
Lemma ghiCP : ghiC. Proof. by vm_compute. Qed.

Lemma ghiCE : ghiC =
  iter nlon 0%uint63 (fun i =>
    [&& (Uint63.sub (Uint63.add nloi i) nloi =? i)%uint63,
        (nloi <=? Uint63.add nloi i)%uint63,
        (Uint63.add nloi i <? nbiti)%uint63 &
        ~~ (Uint63.add nloi i <? 12)%uint63]).
Proof. by []. Qed.

Lemma ghiP i : (to_nat i < nlon)%N ->
  [/\ Uint63.sub (Uint63.add nloi i) nloi = i,
      (nloi <=? Uint63.add nloi i)%uint63,
      (Uint63.add nloi i <? nbiti)%uint63 &
      (Uint63.add nloi i <? 12)%uint63 = false].
Proof.
move=> hi.
have h1 := ghiCP; rewrite ghiCE in h1.
have /and4P[e1 e2 e3 e4] := Row.iter_at h1 hi.
split.
- by apply/eqP; exact: e1.
- exact: e2.
- exact: e3.
by apply/negbTE; exact: e4.
Qed.

(* the high half of a word is read at the parity fsrc carries, turned over *)
Lemma ghi_pty r k h i : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  (to_nat i < nlon)%N ->
  Ptyof (gp r k h) (Uint63.add nloi i) = Uint63.sub 1 (fpar (gw r k)).
Proof.
move=> hr hk hh hgo hi.
have hfp := gparP hr hk hh hgo.
have [_ hkp _ _ hw] := gathR hr hk hh hgo.
have [_ _ _ e4] := ghiP hi.
have hsh : (to_nat (gsh r k h) < 2)%N.
  case: (Uint63.eqb h 0); first exact: fhlf_lt2.
  rewrite landC; have -> : (2 = 2 ^ 1)%N by [].
  by apply: to_nat_land_bound; rewrite to_nat_1.
have hpk : (to_nat (gp r k h) < npagen)%N.
  by apply/nltbP; exact: (Row.iter_at (Row.iter_at keepRCP hkp) hsh).
have hf : fpar (PArray.get fpgi (gp r k h)) = fpar (gw r k).
  by rewrite hw; apply/eqP; have /andP[_ hq] := Row.iter_at fpgCP hpk; exact: hq.
rewrite e4 hf.
by case: (int_lt2 hfp) => ->; vm_compute.
Qed.

Lemma QhiC d : Qhi_st fpgi fsrci fsrc2i ffuli fsgri fsloi fshii fsbti mgri mswi mloi mhii
                      (PdC d) (PdC d.+1).
Proof.
move=> src r k h g pg gr bt hr hk hh hg hgo hsrc.
cbv zeta.
move=> hin h1 h2 h3.
have [hu hkp _ _ _] := gathR hr hk hh hgo.
have /and3P[hpg hgr hbt] := hin.
have hpgn : (to_nat pg < npagen)%N by apply/nltbP; exact: hpg.
have hbtn : (to_nat bt < nbitn)%N by apply/nltbP; exact: hbt.
have hgrn : (to_nat gr < ngroupn)%N by apply/nltbP; exact: hgr.
have hfr : (to_nat (fren (PArray.get fpgi pg)) < nsymn)%N.
  by apply/nltbP; exact: (Row.iter_at frnRCP hpgn).
have hjb : (sbtmv fsbti (fren (PArray.get fpgi pg)) bt <? nbiti)%uint63.
  exact: (Row.iter_at (Row.iter_at sbtRCP hfr) hbtn).
have hsh : (to_nat (gsh r k h) < 2)%N.
  case: (Uint63.eqb h 0); first exact: fhlf_lt2.
  rewrite landC; have -> : (2 = 2 ^ 1)%N by [].
  by apply: to_nat_land_bound; rewrite to_nat_1.
have hhi : (to_nat (Uint63.land (Uint63.lsr (if Uint63.eqb (gsh r k h) 0
                       then Uint63.land (fget src (fkpt (gw r k)) g) allbits24
                       else Uint63.land
                              (Uint63.lsr (fget src (fkpt (gw r k)) g) nbiti)
                              allbits24) 12) lo12)
              < RowFoldSym.nhalfn)%N.
  by apply/nltbP; exact: lo12_lt _.
have h3a : ~~ (Uint63.land
                 (Uint63.lsl
                    (chi (gu r k h) k
                       (Uint63.land (Uint63.lsr (if Uint63.eqb (gsh r k h) 0
                       then Uint63.land (fget src (fkpt (gw r k)) g) allbits24
                       else Uint63.land
                              (Uint63.lsr (fget src (fkpt (gw r k)) g) nbiti)
                              allbits24) 12) lo12))
                    (fofs h (if Uint63.eqb (PArray.get mswi k) 0
                             then 12 else 0)))
                 (bitof (fbit (fhlf (PArray.get fpgi pg))
                     (sbtmv fsbti (fren (PArray.get fpgi pg)) bt)))
               =? 0)%uint63 := h3.
rewrite (chiX_fofs _ _ _ hh) in h3a.
have [hhE h3b] := fbit_half (chiX_lt24 hu hk hhi) (fhlf_lt2 _) hh hjb h3a.
have [i hi [hbi hje]] := chiX_bit hu hk hhi hjb h3b.
have hi12 : (i <? 12)%uint63 by apply/nltbP; exact: hi.
have [hsub hle hs24 he12] := ghiP hi.
have hs24n : (to_nat (Uint63.add nloi i) < nbitn)%N.
  by apply/nltbP; exact: hs24.
(* the bit came from a bit of the half the level read, twelve places up *)
have hbv : ~~ (Uint63.land (fget src (fkpt (gw r k)) g)
                 (bitof (fbit (gsh r k h) (Uint63.add nloi i))) =? 0)%uint63.
  have hfd : (fbit (gsh r k h) (Uint63.add nloi i) <? digits)%uint63.
    by apply: lt_digits; apply: fbit_lt.
  rewrite (test_bit _ hfd) -(bit_fhalf _ hsh hs24).
  rewrite -(@bit_hihalf (if Uint63.eqb (gsh r k h) 0
                       then Uint63.land (fget src (fkpt (gw r k)) g) allbits24
                       else Uint63.land
                              (Uint63.lsr (fget src (fkpt (gw r k)) g) nbiti)
                              allbits24) (Uint63.add nloi i) hle hs24) hsub.
  by rewrite -(test_bit _ (lt_half_digits hi12)) hbi.
have hinsrc : inrange24 (gp r k h) g (Uint63.add nloi i).
  have hp : (gp r k h <? npagei)%uint63.
    exact: (Row.iter_at (Row.iter_at keepRCP hkp) hsh).
  by apply/and3P; split; [exact: hp | apply/nltbP; exact: hg | exact: hs24].
have hPsrc := gsrc_memb hr hk hh hgo hg hs24n hsrc hbv.
have hPdst := gdst_memb hr hk hh hgo hg hs24n hinsrc hPsrc.
rewrite (ghi_pty hr hk hh hgo hi) in hPdst.
(* the slot the write goes to is the slot the member folds to *)
have hpty : (to_nat (Uint63.sub 1 (fpar (gw r k))) < nptyn)%N.
  have hfp := gparP hr hk hh hgo.
  by case: (int_lt2 hfp) => ->; vm_compute.
have hsg : (sgrmv fsgri (gu r k h) (Uint63.sub 1 (fpar (gw r k))) g
             <? ngroupi)%uint63 :=
  Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hpty) hg.
have hsgn : (to_nat (sgrmv fsgri (gu r k h) (Uint63.sub 1 (fpar (gw r k))) g)
              < ngroupn)%N.
  by apply/nltbP; exact: hsg.
have hG : (grmv mgri k (sgrmv fsgri (gu r k h) (Uint63.sub 1 (fpar (gw r k))) g)
            <? ngroupi)%uint63.
  exact: (Row.iter_at (Row.iter_at grokC hk) hsgn).
have hp2 : (to_nat (Ptyof pg bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP hpgn) hbtn).
have hGof : (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr
              <? ngroupi)%uint63.
  exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hfr) hp2) hgrn).
have h2' : Uint63.add (poff r)
             (grmv mgri k
                (sgrmv fsgri (gu r k h) (Uint63.sub 1 (fpar (gw r k))) g))
         = Uint63.add (poff (fkpt (PArray.get fpgi pg)))
             (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr) := h2.
have [hReq hGeq] := fslot_inj hG hGof h1 h2'.
have hPdst2 : PdC d.+1 (fkeep2 (fkpt (PArray.get fpgi pg)) (fhlf (PArray.get fpgi pg)))
                (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr)
                (sbtmv fsbti (fren (PArray.get fpgi pg)) bt).
  by rewrite -hReq hhE -hGeq hje; exact: hPdst.
have [j hj hje2] := fold_conjC hin.
rewrite /PdC hje2 in hPdst2.
by apply: (ball_conjV hj hPdst2).
Qed.
