(* =========================================================================  *)
(*  RowFoldSrc.v -- the page the gather reads, renamed and then moved.        *)
(* =========================================================================  *)

(* RowFoldConj.v conjugates a page by the renaming that FOLDS it, which is    *)
(* the renaming fpg names.  The gather reads a source page through a          *)
(* different renaming -- the one fsrc names -- and then moves it, so the      *)
(* corner leg has to be had at that renaming too.                             *)
(*                                                                            *)
(* IT IS NOT A SWEEP OVER ALL SIXTEEN RENAMINGS AND ALL FORTY THOUSAND PAGES. *)
(* Only the pairs the level actually gathers are needed: a kept page and one  *)
(* of the ten moves, which is 27 680 of them.                                 *)
(*                                                                            *)
(* What the sweep says, at each pair: the renaming is one of the sixteen, the *)
(* source is a kept page, the renamed page is a page, the renaming keeps its  *)
(* parity, the parity fsrc carries is the source page's, the move sends the   *)
(* renamed page to the page being filled, and the renaming conjugates the     *)
(* eight corner places -- which is what part_conj asks.                       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Sym16 Moves.
Require Import Row RowMap RowFold RowMemb RowFoldPart RowTab.
Require Import RowTabF RowFoldTab RowFoldSym RowFoldConj.
Require Import RowPartC RowPartU RowPartM RowMoveH RowUp8ok RowUp4ok.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope uint63_scope.

(* ---- the source of one gather -------------------------------------------- *)

(* the word fsrc holds for a kept page and a move, and the three things it    *)
(* carries: which page to read, through which renaming, at which parity       *)
(* A CELL IS TWO PAGES, so a gather is two gathers into one word: the         *)
(* destination's half nought is read from the source cell's half `gsh r k 0'  *)
(* through `gu r k 0', and its half one from `gsh r k 1' through `gu r k 1'.  *)
(* fsrc carries the first pair and fsrc2 the second.  The source CELL is the  *)
(* same for both, which is what lets one read serve both halves.              *)
Notation gw r k := (PArray.get fsrci (Uint63.add (Uint63.mul r nhi) k)).
Notation gw2 r k := (PArray.get fsrc2i (Uint63.add (Uint63.mul r nhi) k)).
Notation gsh r k h :=
  (if Uint63.eqb h 0 then fhlf (gw r k) else Uint63.land (gw2 r k) 1).
Notation gu r k h :=
  (if Uint63.eqb h 0 then fren (gw r k) else Uint63.lsr (gw2 r k) 1).
Notation gp r k h := (fkeep2 (fkpt (gw r k)) (gsh r k h)).
Notation gq r k h := (pgexp (gu r k h) (gp r k h)).

(* a cell with one half has no half one, and nothing is asked of it           *)
Notation gone r := (Uint63.eqb (PArray.get ffuli r) allbits24).

Definition gathC1 (r k h : int) : bool :=
  if (Uint63.eqb h 1) && gone r then true else
  let w := PArray.get fsrci (Uint63.add (Uint63.mul r nhi) k) in
  let u := gu r k h in
  let p := gp r k h in
  let q := pgexp u p in
  let lp := nth [::] lpcs (nth 0%N fren2sym (to_nat u)) in
  [&& (u <? nsymi), (fkpt w <? nrepi), (q <? npagei),
      (PArray.get par8i q =? PArray.get par8i p) &
      (fpar w =? PArray.get par8i p)]
  && ((PArray.get mpgi (Uint63.add (Uint63.mul q nhi) k)
         =? fkeep2 r h)
      && all (fun j => nth 0%N lp (up8 p j) == up8 q (nth 0%N lp j))
             (iota 0 8))
  (* AND THE SOURCE HALF IS A HALF THE SOURCE CELL HAS.  A page sits in half  *)
  (* one only where the cell has one, so this is true; it has to be READ off  *)
  (* the tables rather than argued, because it is the tables that say which   *)
  (* half a gather reads.                                                     *)
  && ~~ ((Uint63.eqb (gsh r k h) 1) && gone (fkpt w)).

Definition gathC : bool :=
  iter nrepn 0 (fun r => iter nhn 0 (fun k => iter 2 0 (gathC1 r k))).
Lemma gathCP : gathC. Proof. by vm_compute. Qed.

(* read through an equation, never straight -- see RowFoldGath.caddCE *)
Lemma gathCE : gathC =
  iter nrepn 0 (fun r => iter nhn 0 (fun k => iter 2 0 (gathC1 r k))).
Proof. by []. Qed.

Lemma gathP r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) -> gathC1 r k h.
Proof.
move=> hr hk hh hgo; have h1 := gathCP; rewrite gathCE in h1.
have h2 := Row.iter_at (Row.iter_at (Row.iter_at h1 hr) hk) hh.
by move: h2; rewrite /gathC1 (negbTE hgo).
Qed.

(* ---- what the sweep says, one fact at a time ----------------------------- *)

Lemma gathR r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  [/\ (to_nat (gu r k h) < nsymn)%N, (to_nat (fkpt (gw r k)) < nrepn)%N,
      (to_nat (gq r k h) < npagen)%N,
      PArray.get par8i (gq r k h) = PArray.get par8i (gp r k h)
    & fpar (gw r k) = PArray.get par8i (gp r k h)].
Proof.
move=> hr hk hh hgo; have hgc := gathP hr hk hh hgo.
rewrite /gathC1 in hgc; cbv zeta in hgc.
move: hgc; rewrite (negbTE hgo) => hgc.
have /andP[/andP[/and5P[h1 h2 h3 h4 h5] _] _] := hgc.
(* the five named one by one: a goal left to `done' is evaluated *)
split.
- by apply/nltbP; exact: h1.
- by apply/nltbP; exact: h2.
- by apply/nltbP; exact: h3.
- by apply/eqP; exact: h4.
by apply/eqP; exact: h5.
Qed.

Lemma gathM r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  PArray.get mpgi (Uint63.add (Uint63.mul (gq r k h) nhi) k)
  = fkeep2 r h.
Proof.
move=> hr hk hh hgo; have hgc := gathP hr hk hh hgo.
rewrite /gathC1 in hgc; cbv zeta in hgc.
move: hgc; rewrite (negbTE hgo) => hgc.
by have /andP[/andP[_ /andP[h1 _]] _] := hgc; apply/eqP.
Qed.

Lemma gathJ r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  let lp := nth [::] lpcs (nth 0%N fren2sym (to_nat (gu r k h))) in
  all (fun j => nth 0%N lp (up8 (gp r k h) j) == up8 (gq r k h) (nth 0%N lp j))
      (iota 0 8).
Proof.
move=> hr hk hh hgo; have hgc := gathP hr hk hh hgo.
rewrite /gathC1 in hgc; cbv zeta in hgc.
move: hgc; rewrite (negbTE hgo) => hgc.
by have /andP[/andP[_ /andP[_ h1]] _] := hgc.
Qed.

(* the source half is one the source cell has                                 *)
Lemma gathS r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  (to_nat h < 2)%N -> ~~ ((Uint63.eqb h 1) && gone r) ->
  ~~ ((Uint63.eqb (gsh r k h) 1) && gone (fkpt (gw r k))).
Proof.
move=> hr hk hh hgo; have hgc := gathP hr hk hh hgo.
rewrite /gathC1 in hgc; cbv zeta in hgc.
move: hgc; rewrite (negbTE hgo) => hgc.
by have /andP[_ h1] := hgc.
Qed.

(* ---- THE CORNER PART, CONJUGATED BY THE GATHER'S RENAMING ---------------- *)

(* RowFoldConj.cpart_conj, with the renaming fsrc names in place of the one   *)
(* fpg names and the renamed page in place of the kept page.  Nothing else    *)
(* changes: part_conj asks the same six things and the sweep above has them.  *)
Lemma gcpart_conj r k h : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  up8ok1 (gp r k h) ->
  comp_tab (part cflatp 3 inC cposn cslotn (up8 (gp r k h)))
           (restr inC (sy (nth 0%N fren2sym (to_nat (gu r k h)))))
  = comp_tab (restr inC (sy (nth 0%N fren2sym (to_nat (gu r k h)))))
             (part cflatp 3 inC cposn cslotn (up8 (gq r k h))).
Proof.
move=> hr hk hh hgo hok.
have [hu _ _ _ _] := gathR hr hk hh hgo.
set s := nth 0%N fren2sym _.
have hs : (s < 16)%N by apply: (aiota_lt f2sCP hu).
apply: (@part_conj cflatp 3 8 inC cposn cslotn _ _ (swc s)).
- exact: clayokC.
- by apply: (aiota_lt csymCP hs).
- rewrite -(lpcsE hs); exact: (gathJ hr hk hh hgo).
- exact: up8_rng hok.
- by rewrite -(lpcsE hs); apply: (aiota_lt lpcrngCP hs).
by have /and3P[hw _ _] := aiota_lt swrngCP hs.
Qed.

(* =========================================================================  *)
(*  The source member, renamed: RowFoldConj.fold_conj_pt at the gather.       *)
(* =========================================================================  *)

(* Word for word RowFoldConj.fold_conj_pt, with the renaming fsrc names and   *)
(* the page it sends the source to.  The three parts are conjugated by their  *)
(* own piece and memb_conj_pt puts them back: the corner leg is gcpart_conj   *)
(* above, and the outer edge and middle legs are already stated at any of the *)
(* sixteen, so they are used unchanged.                                       *)
Lemma gather_conj_pt r k h gr bt : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) ->
  inrange24 (gp r k h) gr bt ->
  pt 47 (membinv (unplace24 e8invi e4ofi par8i par4i (gq r k h)
                    (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) bt) gr)
                    (sbtmv fsbti (gu r k h) bt)))
  = ((pt 47 (membinv (unplace24 e8invi e4ofi par8i par4i (gp r k h) gr bt)))
      ^ pt 47 (sy (nth 0%N fren2sym (to_nat (gu r k h)))))%g.
Proof.
move=> hr hk hh hgo hin.
have [hu _ hq hpar8 _] := gathR hr hk hh hgo.
have /and3P[hpg hgr hbt] := hin.
have b0 : (to_nat (gp r k h) < npagen)%N by apply/nltbP.
have hb : (to_nat bt < nbitn)%N by apply/nltbP.
have hg : (to_nat gr < ngroupn)%N by apply/nltbP.
have hp : (to_nat (Ptyof (gp r k h) bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP b0) hb).
have hin' : inrange24 (gq r k h)
              (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) bt) gr)
              (sbtmv fsbti (gu r k h) bt).
  apply/and3P; split.
  - by apply/nltbP.
  - exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hp) hg).
  exact: (Row.iter_at (Row.iter_at sbtRCP hu) hb).
have /and3P[hQ hG hB] := hin'.
have hGn : (to_nat (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) bt) gr) < ngroupn)%N.
  by apply/nltbP.
have hBn : (to_nat (sbtmv fsbti (gu r k h) bt) < nbitn)%N by apply/nltbP.
have hs : (nth 0%N fren2sym (to_nat (gu r k h)) < 16)%N.
  by apply: (aiota_lt f2sCP hu).
have epty : Ptyof (gp r k h) bt
          = Uint63.lxor (PArray.get par8i (gp r k h))
                        (PArray.get par4i (PArray.get e4ofi bt)).
  by rewrite (eqP (Row.iter_at parbtCP hb));
     have /andP[_ /eqP ->] := Row.iter_at fpgCP b0.
have epB : PArray.get par4i (PArray.get e4ofi (sbtmv fsbti (gu r k h) bt))
         = PArray.get par4i (PArray.get e4ofi bt).
  by apply/eqP; apply: (Row.iter_at (Row.iter_at parBCP hu) hb).
have o1 : up8ok1 (gp r k h) by apply: (Row.iter_at up8okC b0).
have o2 : up8ok1 (gq r k h) by apply: (Row.iter_at up8okC hq).
have o3 : up8ok1 (PArray.get e8invi
            (Uint63.add (Uint63.mul gr 2) (Ptyof (gp r k h) bt))).
  apply: (Row.iter_at up8okC); apply/nltbP.
  exact: (Row.iter_at (Row.iter_at ugrpRCP hg) hp).
have o4 : up8ok1 (PArray.get e8invi
            (Uint63.add
               (Uint63.mul (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) bt) gr) 2)
               (Ptyof (gp r k h) bt))).
  apply: (Row.iter_at up8okC); apply/nltbP.
  exact: (Row.iter_at (Row.iter_at ugrpRCP hGn) hp).
have o5 : up4ok1 (PArray.get e4ofi bt).
  by apply: (Row.iter_at up4okC); apply/nltbP; exact: (Row.iter_at e4ofRCP hb).
have o6 : up4ok1 (PArray.get e4ofi (sbtmv fsbti (gu r k h) bt)).
  by apply: (Row.iter_at up4okC); apply/nltbP; exact: (Row.iter_at e4ofRCP hBn).
rewrite (pt_membinv e8okC e4okC cpartokC upartokC mpartokC hmvokC hin').
rewrite (pt_membinv e8okC e4okC cpartokC upartokC mpartokC hmvokC hin).
rewrite /mcp /mud /mmp /unplace24 hpar8 epB -epty.
apply: (memb_conj_pt hs o1 o2 o3 o4 o5 o6).
- exact: (gcpart_conj hr hk hh hgo o1).
- exact: (upart_conj hu hp hg o3).
exact: (mpart_conj hu hb o5).
Qed.

(* ---- and in the shape the ball asks for ---------------------------------- *)

(* RowFoldConj.fold_conj_memb, at the gather: membinv inverted is memb2tab,   *)
(* and a conjugate inverted is the inverse conjugated, so the statement comes *)
(* across unchanged.                                                          *)
Lemma gather_conj_memb r k h gr bt :
  (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> (to_nat h < 2)%N ->
  ~~ ((Uint63.eqb h 1) && gone r) -> inrange24 (gp r k h) gr bt ->
  exists2 i, (i < 16)%N &
    pt 47 (memb2tab (unplace24 e8invi e4ofi par8i par4i (gq r k h)
                       (sgrmv fsgri (gu r k h) (Ptyof (gp r k h) bt) gr)
                       (sbtmv fsbti (gu r k h) bt)))
    = ((pt 47 (memb2tab (unplace24 e8invi e4ofi par8i par4i (gp r k h) gr bt)))
        ^ pt 47 (nth [::] sym16ts i))%g.
Proof.
move=> hr hk hh hgo hin.
have [hu _ _ _ _] := gathR hr hk hh hgo.
exists (nth 0%N fren2sym (to_nat (gu r k h))); first by apply: (aiota_lt f2sCP hu).
have E : forall x, pt 47 (memb2tab x) = ((pt 47 (membinv x))^-1)%g.
  by move=> x; rewrite /memb2tab (ptV (membinv_ok cpartokC upartokC mpartokC x)).
by rewrite !E (gather_conj_pt hr hk hh hgo hin) conjVg.
Qed.
