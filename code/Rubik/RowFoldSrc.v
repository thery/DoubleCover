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
Notation gw r k := (PArray.get fsrci (Uint63.add (Uint63.mul r nhi) k)).
Notation gp r k := (PArray.get fkeepi (fkpt (gw r k))).
Notation gu r k := (fren (gw r k)).
Notation gq r k := (pgexp (gu r k) (gp r k)).

Definition gathC1 (r k : int) : bool :=
  let w := PArray.get fsrci (Uint63.add (Uint63.mul r nhi) k) in
  let u := fren w in
  let p := PArray.get fkeepi (fkpt w) in
  let q := pgexp u p in
  let lp := nth [::] lpcs (nth 0%N fren2sym (to_nat u)) in
  [&& (u <? nsymi), (fkpt w <? nrepi), (q <? npagei),
      (PArray.get par8i q =? PArray.get par8i p) &
      (fpar w =? PArray.get par8i p)]
  && ((PArray.get mpgi (Uint63.add (Uint63.mul q nhi) k)
         =? PArray.get fkeepi r)
      && all (fun j => nth 0%N lp (up8 p j) == up8 q (nth 0%N lp j))
             (iota 0 8)).

Definition gathC : bool := iter nrepn 0 (fun r => iter nhn 0 (gathC1 r)).
Lemma gathCP : gathC. Proof. by vm_compute. Qed.

(* read through an equation, never straight -- see RowFoldGath.caddCE *)
Lemma gathCE : gathC = iter nrepn 0 (fun r => iter nhn 0 (gathC1 r)).
Proof. by []. Qed.

Lemma gathP r k : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N -> gathC1 r k.
Proof.
move=> hr hk; have h1 := gathCP; rewrite gathCE in h1.
exact: (Row.iter_at (Row.iter_at h1 hr) hk).
Qed.

(* ---- what the sweep says, one fact at a time ----------------------------- *)

Lemma gathR r k : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  [/\ (to_nat (gu r k) < nsymn)%N, (to_nat (fkpt (gw r k)) < nrepn)%N,
      (to_nat (gq r k) < npagen)%N,
      PArray.get par8i (gq r k) = PArray.get par8i (gp r k)
    & fpar (gw r k) = PArray.get par8i (gp r k)].
Proof.
move=> hr hk; have h := gathP hr hk.
rewrite /gathC1 in h; cbv zeta in h.
have /andP[/and5P[h1 h2 h3 h4 h5] _] := h.
(* the five named one by one: a goal left to `done' is evaluated *)
split.
- by apply/nltbP; exact: h1.
- by apply/nltbP; exact: h2.
- by apply/nltbP; exact: h3.
- by apply/eqP; exact: h4.
by apply/eqP; exact: h5.
Qed.

Lemma gathM r k : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  PArray.get mpgi (Uint63.add (Uint63.mul (gq r k) nhi) k)
  = PArray.get fkeepi r.
Proof.
move=> hr hk; have h := gathP hr hk.
rewrite /gathC1 in h; cbv zeta in h.
by have /andP[_ /andP[h1 _]] := h; apply/eqP.
Qed.

Lemma gathJ r k : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  let lp := nth [::] lpcs (nth 0%N fren2sym (to_nat (gu r k))) in
  all (fun j => nth 0%N lp (up8 (gp r k) j) == up8 (gq r k) (nth 0%N lp j))
      (iota 0 8).
Proof.
move=> hr hk; have h := gathP hr hk.
rewrite /gathC1 in h; cbv zeta in h.
by have /andP[_ /andP[_ h1]] := h.
Qed.

(* ---- THE CORNER PART, CONJUGATED BY THE GATHER'S RENAMING ---------------- *)

(* RowFoldConj.cpart_conj, with the renaming fsrc names in place of the one   *)
(* fpg names and the renamed page in place of the kept page.  Nothing else    *)
(* changes: part_conj asks the same six things and the sweep above has them.  *)
Lemma gcpart_conj r k : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  up8ok1 (gp r k) ->
  comp_tab (part cflatp 3 inC cposn cslotn (up8 (gp r k)))
           (restr inC (sy (nth 0%N fren2sym (to_nat (gu r k)))))
  = comp_tab (restr inC (sy (nth 0%N fren2sym (to_nat (gu r k)))))
             (part cflatp 3 inC cposn cslotn (up8 (gq r k))).
Proof.
move=> hr hk hok.
have [hu _ _ _ _] := gathR hr hk.
set s := nth 0%N fren2sym _.
have hs : (s < 16)%N by apply: (aiota_lt f2sCP hu).
apply: (@part_conj cflatp 3 8 inC cposn cslotn _ _ (swc s)).
- exact: clayokC.
- by apply: (aiota_lt csymCP hs).
- rewrite -(lpcsE hs); exact: (gathJ hr hk).
- exact: up8_rng hok.
- by rewrite -(lpcsE hs); apply: (aiota_lt lpcrngCP hs).
by have /and3P[h _ _] := aiota_lt swrngCP hs.
Qed.

(* =========================================================================  *)
(*  The source member, renamed: RowFoldConj.fold_conj_pt at the gather.       *)
(* =========================================================================  *)

(* Word for word RowFoldConj.fold_conj_pt, with the renaming fsrc names and   *)
(* the page it sends the source to.  The three parts are conjugated by their  *)
(* own piece and memb_conj_pt puts them back: the corner leg is gcpart_conj   *)
(* above, and the outer edge and middle legs are already stated at any of the *)
(* sixteen, so they are used unchanged.                                       *)
Lemma gather_conj_pt r k gr bt : (to_nat r < nrepn)%N -> (to_nat k < nhn)%N ->
  inrange (gp r k) gr bt ->
  pt 47 (membinv (unplace e8invi e4ofi par8i par4i (gq r k)
                    (sgrmv fsgri (gu r k) (Ptyof (gp r k) bt) gr)
                    (sbtmv fsbti (gu r k) bt)))
  = ((pt 47 (membinv (unplace e8invi e4ofi par8i par4i (gp r k) gr bt)))
      ^ pt 47 (sy (nth 0%N fren2sym (to_nat (gu r k)))))%g.
Proof.
move=> hr hk hin.
have [hu _ hq hpar8 _] := gathR hr hk.
have /and3P[hpg hgr hbt] := hin.
have b0 : (to_nat (gp r k) < npagen)%N by apply/nltbP.
have hb : (to_nat bt < nbitn)%N by apply/nltbP.
have hg : (to_nat gr < ngroupn)%N by apply/nltbP.
have hp : (to_nat (Ptyof (gp r k) bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP b0) hb).
have hin' : inrange (gq r k)
              (sgrmv fsgri (gu r k) (Ptyof (gp r k) bt) gr)
              (sbtmv fsbti (gu r k) bt).
  apply/and3P; split.
  - by apply/nltbP.
  - exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hp) hg).
  exact: (Row.iter_at (Row.iter_at sbtRCP hu) hb).
have /and3P[hQ hG hB] := hin'.
have hGn : (to_nat (sgrmv fsgri (gu r k) (Ptyof (gp r k) bt) gr) < ngroupn)%N.
  by apply/nltbP.
have hBn : (to_nat (sbtmv fsbti (gu r k) bt) < nbitn)%N by apply/nltbP.
have hs : (nth 0%N fren2sym (to_nat (gu r k)) < 16)%N.
  by apply: (aiota_lt f2sCP hu).
have epty : Ptyof (gp r k) bt
          = Uint63.lxor (PArray.get par8i (gp r k))
                        (PArray.get par4i (PArray.get e4ofi bt)).
  by rewrite (eqP (Row.iter_at parbtCP hb));
     have /andP[_ /eqP ->] := Row.iter_at fpgCP b0.
have epB : PArray.get par4i (PArray.get e4ofi (sbtmv fsbti (gu r k) bt))
         = PArray.get par4i (PArray.get e4ofi bt).
  by apply/eqP; apply: (Row.iter_at (Row.iter_at parBCP hu) hb).
have o1 : up8ok1 (gp r k) by apply: (Row.iter_at up8okC b0).
have o2 : up8ok1 (gq r k) by apply: (Row.iter_at up8okC hq).
have o3 : up8ok1 (PArray.get e8invi
            (Uint63.add (Uint63.mul gr 2) (Ptyof (gp r k) bt))).
  apply: (Row.iter_at up8okC); apply/nltbP.
  exact: (Row.iter_at (Row.iter_at ugrpRCP hg) hp).
have o4 : up8ok1 (PArray.get e8invi
            (Uint63.add
               (Uint63.mul (sgrmv fsgri (gu r k) (Ptyof (gp r k) bt) gr) 2)
               (Ptyof (gp r k) bt))).
  apply: (Row.iter_at up8okC); apply/nltbP.
  exact: (Row.iter_at (Row.iter_at ugrpRCP hGn) hp).
have o5 : up4ok1 (PArray.get e4ofi bt).
  by apply: (Row.iter_at up4okC); apply/nltbP; exact: (Row.iter_at e4ofRCP hb).
have o6 : up4ok1 (PArray.get e4ofi (sbtmv fsbti (gu r k) bt)).
  by apply: (Row.iter_at up4okC); apply/nltbP; exact: (Row.iter_at e4ofRCP hBn).
rewrite (pt_membinv e8okC e4okC cpartokC upartokC mpartokC hmvokC hin').
rewrite (pt_membinv e8okC e4okC cpartokC upartokC mpartokC hmvokC hin).
rewrite /mcp /mud /mmp /unplace hpar8 epB -epty.
apply: (memb_conj_pt hs o1 o2 o3 o4 o5 o6).
- exact: (gcpart_conj hr hk o1).
- exact: (upart_conj hu hp hg o3).
exact: (mpart_conj hu hb o5).
Qed.
