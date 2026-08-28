(* =========================================================================  *)
(*  RowFoldConj.v -- the fold's tables really do conjugate the places.        *)
(* =========================================================================  *)

(* RowFoldPart.part_conj says a part conjugated by a renaming is the part of  *)
(* the conjugated places, and what it asks of the places is                   *)
(*                                                                            *)
(*     lperm t (v p) = u (lperm t p)                                          *)
(*                                                                            *)
(* This file asks that of the fold's own tables, by walking them.  The page   *)
(* is done here; the outer edges and the middle follow the same shape.        *)
(*                                                                            *)
(* EVERY INDEX IS AN int63, for the reason RowFoldSym gives: of_nat walks its *)
(* argument, and naming forty thousand pages in nat does not finish.  In      *)
(* int63 the sweep is five and a half seconds.                                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Tabi Rubik333 Sym Sym16 Moves.
Require Import Row RowMap RowFold RowMemb RowFoldPart RowTab.
Require Import RowTabF RowFoldTab RowFoldSym.
Require Import RowPartC RowPartU RowPartM RowMoveH RowUp8ok RowUp4ok.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ---- the renaming, on the eight corner places ---------------------------- *)

(* lperm reads the place a table sends a place to, off the first slot.  The   *)
(* sixteen are worked out once, as values, so a sweep over forty thousand     *)
(* pages does not rebuild them.                                               *)
Definition lpc (s : nat) : seq nat := lperm cflatp 3 8 cposn (sy s).

Definition lpcs : seq (seq nat) := Eval vm_compute in [seq lpc s | s <- iota 0 16].

(* the renaming a page names, in Sym16's numbering *)
Notation psym w := (nth [::] lpcs (nth 0%N fren2sym (to_nat (fren w)))).

(* ---- and it does conjugate the page ------------------------------------- *)

(* For every one of the forty thousand pages: the KEPT page's permutation is  *)
(* the page's, conjugated by the renaming that folds it.  This is what        *)
(* part_conj asks, at u := the kept page and v := the page.                   *)
Definition pgconjC : bool :=
  iter npagen 0%uint63 (fun pg =>
     let w := PArray.get fpgi pg in
     let lp := psym w in
     let k := PArray.get fkeepi (fkpt w) in
     all (fun p => nth 0%N lp (up8 pg p) == up8 k (nth 0%N lp p)) (iota 0 8)).

Lemma pgconjCP : pgconjC. Proof. by vm_compute. Qed.

(* and the two ranges part_conj asks beside it: the places a renaming names,  *)
(* and the places a page's permutation names                                  *)
Definition lpcrngC : bool :=
  all (fun s => all (fun p => (nth 0%N (nth [::] lpcs s) p < 8)%N) (iota 0 8))
      (iota 0 16).

Lemma lpcrngCP : lpcrngC. Proof. by vm_compute. Qed.

(* the sixteen worked out as values are the sixteen lperm reads *)
Definition lpcsC : bool :=
  all (fun s => nth [::] lpcs s == lperm cflatp 3 8 cposn (sy s)) (iota 0 16).

Lemma lpcsCP : lpcsC. Proof. by vm_compute. Qed.

Lemma lpcsE s : (s < 16)%N -> nth [::] lpcs s = lperm cflatp 3 8 cposn (sy s).
Proof. by move=> hs; apply/eqP; apply: (aiota_lt lpcsCP hs). Qed.

(* and a page names one of the sixteen *)
Definition frnC : bool :=
  iter npagen 0%uint63
    (fun pg => (nth 0%N fren2sym (to_nat (fren (PArray.get fpgi pg))) < 16)%N).

Lemma frnCP : frnC. Proof. by vm_compute. Qed.

(* ---- THE CORNER PART, CONJUGATED --------------------------------------- *)

(* The corner part of the kept page is the corner part of the page,          *)
(* conjugated by the renaming that folds it.  Every ingredient part_conj     *)
(* asks for is a sweep that has been run: the layout, the slot map, the      *)
(* places, and the three ranges.                                            *)
Lemma cpart_conj pg : (to_nat pg < npagen)%N -> up8ok1 pg ->
  comp_tab (part cflatp 3 inC cposn cslotn (up8 pg))
           (restr inC (sy (nth 0%N fren2sym (to_nat (fren (PArray.get fpgi pg))))))
  = comp_tab (restr inC (sy (nth 0%N fren2sym (to_nat (fren (PArray.get fpgi pg))))))
             (part cflatp 3 inC cposn cslotn
                (up8 (PArray.get fkeepi (fkpt (PArray.get fpgi pg))))).
Proof.
move=> hpg hok.
set s := nth 0%N fren2sym _.
have hs : (s < 16)%N by apply: (Row.iter_at frnCP hpg).
apply: (@part_conj cflatp 3 8 inC cposn cslotn _ _ (swc s)).
- exact: clayokC.
- by apply: (aiota_lt csymCP hs).
- rewrite -(lpcsE hs); exact: (Row.iter_at pgconjCP hpg).
- exact: up8_rng hok.
- by rewrite -(lpcsE hs); apply: (aiota_lt lpcrngCP hs).
by have /and3P[h _ _] := aiota_lt swrngCP hs.
Qed.

(* ---- the outer edges and the middle, the same way ------------------------ *)

(* The outer edge part and the middle part of a member are ranks too, and the *)
(* renaming conjugates them the same way.  THE SWEEP IS NOT OVER MEMBERS: the *)
(* outer part depends on a member only through its group and its parity, and  *)
(* the middle only through its bit, so the two walks are the size of the      *)
(* tables they are about and not of the row.                                  *)
(*                                                                            *)
(* AND THE PARITY DOES NOT MOVE.  A renaming conjugates, so it keeps the      *)
(* parity of a permutation -- which is why the same pty indexes both sides.   *)
(* That is what the sweep says; it was not assumed.                           *)

Definition lpu (s : nat) : seq nat := lperm ulay 2 8 eposn (sy s).
Definition lpus : seq (seq nat) := Eval vm_compute in [seq lpu s | s <- iota 0 16].

Definition lpm (s : nat) : seq nat := lperm mlay 2 4 mplc (sy s).
Definition lpms : seq (seq nat) := Eval vm_compute in [seq lpm s | s <- iota 0 16].

Definition lpusC : bool :=
  all (fun s => nth [::] lpus s == lperm ulay 2 8 eposn (sy s)) (iota 0 16).
Lemma lpusCP : lpusC. Proof. by vm_compute. Qed.
Lemma lpusE s : (s < 16)%N -> nth [::] lpus s = lperm ulay 2 8 eposn (sy s).
Proof. by move=> hs; apply/eqP; apply: (aiota_lt lpusCP hs). Qed.

Definition lpmsC : bool :=
  all (fun s => nth [::] lpms s == lperm mlay 2 4 mplc (sy s)) (iota 0 16).
Lemma lpmsCP : lpmsC. Proof. by vm_compute. Qed.
Lemma lpmsE s : (s < 16)%N -> nth [::] lpms s = lperm mlay 2 4 mplc (sy s).
Proof. by move=> hs; apply/eqP; apply: (aiota_lt lpmsCP hs). Qed.

Definition lpurngC : bool :=
  all (fun s => all (fun p => (nth 0%N (nth [::] lpus s) p < 8)%N) (iota 0 8))
      (iota 0 16).
Lemma lpurngCP : lpurngC. Proof. by vm_compute. Qed.

Definition lpmrngC : bool :=
  all (fun s => all (fun p => (nth 0%N (nth [::] lpms s) p < 4)%N) (iota 0 4))
      (iota 0 16).
Lemma lpmrngCP : lpmrngC. Proof. by vm_compute. Qed.

Notation ugrp gr pty := (PArray.get e8invi (Uint63.add (Uint63.mul gr 2) pty)).

(* the outer eight: sixteen renamings, two parities, twenty thousand groups *)
Definition uconjC : bool :=
  iter 16 0%uint63 (fun u =>
    let lp := nth [::] lpus (nth 0%N fren2sym (to_nat u)) in
    iter 2 0%uint63 (fun pty =>
      iter ngroupn 0%uint63 (fun gr =>
        all (fun q => nth 0%N lp (up8 (ugrp gr pty) q)
                      == up8 (ugrp (sgrmv fsgri u pty gr) pty) (nth 0%N lp q))
            (iota 0 8)))).

Lemma uconjCP : uconjC. Proof. by vm_compute. Qed.

(* and the middle four: sixteen renamings, twenty four bits *)
Definition mconjC : bool :=
  iter 16 0%uint63 (fun u =>
    let lp := nth [::] lpms (nth 0%N fren2sym (to_nat u)) in
    iter nbitn 0%uint63 (fun bt =>
      all (fun q => nth 0%N lp (up4 (PArray.get e4ofi bt) q)
                    == up4 (PArray.get e4ofi (sbtmv fsbti u bt)) (nth 0%N lp q))
          (iota 0 4))).

Lemma mconjCP : mconjC. Proof. by vm_compute. Qed.

(* a page's renaming number names one of the sixteen of Sym16 *)
Definition f2sC : bool := all (fun s => (nth 0%N fren2sym s < 16)%N) (iota 0 16).
Lemma f2sCP : f2sC. Proof. by vm_compute. Qed.

(* ---- THE OUTER EDGE PART, CONJUGATED ------------------------------------ *)

Lemma upart_conj u pty gr : (to_nat u < 16)%N -> (to_nat pty < 2)%N ->
  (to_nat gr < ngroupn)%N ->
  up8ok1 (PArray.get e8invi (Uint63.add (Uint63.mul gr 2) pty)) ->
  comp_tab (part ulay 2 inU eposn eslt
              (up8 (PArray.get e8invi (Uint63.add (Uint63.mul gr 2) pty))))
           (restr inU (sy (nth 0%N fren2sym (to_nat u))))
  = comp_tab (restr inU (sy (nth 0%N fren2sym (to_nat u))))
             (part ulay 2 inU eposn eslt
                (up8 (PArray.get e8invi
                        (Uint63.add (Uint63.mul (sgrmv fsgri u pty gr) 2) pty)))).
Proof.
move=> hu hpty hgr hok.
set s := nth 0%N fren2sym (to_nat u).
have hs : (s < 16)%N by apply: (aiota_lt f2sCP hu).
apply: (@part_conj ulay 2 8 inU eposn eslt _ _ (swu s)).
- exact: ulayokC.
- by apply: (aiota_lt usymCP hs).
- (* the let in uconjC is what keeps the sweep to eighty seconds; cbv zeta   *)
  (* takes it out, and nothing else is unfolded.                             *)
  have h1 := Row.iter_at uconjCP hu; cbv zeta in h1.
  have h2 := Row.iter_at h1 hpty.
  by rewrite -(lpusE hs); exact: (Row.iter_at h2 hgr).
- exact: up8_rng hok.
- by rewrite -(lpusE hs); apply: (aiota_lt lpurngCP hs).
by have /and3P[_ h _] := aiota_lt swrngCP hs.
Qed.

(* ---- AND THE MIDDLE PART ------------------------------------------------ *)

Lemma mpart_conj u bt : (to_nat u < 16)%N -> (to_nat bt < nbitn)%N ->
  up4ok1 (PArray.get e4ofi bt) ->
  comp_tab (part mlay 2 inM mplc eslt (up4 (PArray.get e4ofi bt)))
           (restr inM (sy (nth 0%N fren2sym (to_nat u))))
  = comp_tab (restr inM (sy (nth 0%N fren2sym (to_nat u))))
             (part mlay 2 inM mplc eslt
                (up4 (PArray.get e4ofi (sbtmv fsbti u bt)))).
Proof.
move=> hu hbt hok.
set s := nth 0%N fren2sym (to_nat u).
have hs : (s < 16)%N by apply: (aiota_lt f2sCP hu).
apply: (@part_conj mlay 2 4 inM mplc eslt _ _ (swm s)).
- exact: mlayokC.
- by apply: (aiota_lt msymCP hs).
- have h1 := Row.iter_at mconjCP hu; cbv zeta in h1.
  by rewrite -(lpmsE hs); exact: (Row.iter_at h1 hbt).
- exact: up4_rng hok.
- by rewrite -(lpmsE hs); apply: (aiota_lt lpmrngCP hs).
by have /and3P[_ _ h] := aiota_lt swrngCP hs.
Qed.

(* ---- the renaming splits into four commuting pieces ---------------------- *)

(* A member is cut into three parts and a renaming is cut the same way, with  *)
(* the six face centres left over.  Each piece moves only its own class, the  *)
(* four classes are disjoint, and the four pieces compose to the renaming.    *)
(* So conjugating a member by the renaming is conjugating each part by its    *)
(* own piece -- which is what the three part lemmas above give.               *)
Definition inZ (f : nat) : bool := ~~ (inC f || inU f || inM f).

Definition rprtC : bool :=
  all (fun s => [&& partok inC (restr inC (sy s)),
                    partok inU (restr inU (sy s)),
                    partok inM (restr inM (sy s))
                  & partok inZ (restr inZ (sy s))])
      (iota 0 16).
Lemma rprtCP : rprtC. Proof. by vm_compute. Qed.

Definition sfullC : bool :=
  all (fun s => comp_tab (restr inC (sy s))
                  (comp_tab (restr inU (sy s))
                     (comp_tab (restr inM (sy s)) (restr inZ (sy s)))) == sy s)
      (iota 0 16).
Lemma sfullCP : sfullC. Proof. by vm_compute. Qed.

Definition dsjZC : bool := [&& dsj inC inZ, dsj inU inZ & dsj inM inZ].
Lemma dsjZCP : dsjZC. Proof. by vm_compute. Qed.

(* ---- and what that is worth, as a group computation ---------------------- *)

(* Two things commute when neither moves what the other moves, and then       *)
(* conjugating by one leaves the other alone.                                 *)
Lemma cfix (gT : finGroupType) (x y : gT) : commute x y -> (x ^ y)%g = x.
Proof. by move=> h; rewrite conjgE h mulKg. Qed.

(* THE REASSEMBLY, with nothing about the cube in it.  Three parts, each      *)
(* conjugated by its own piece, are the three together conjugated by the      *)
(* three pieces together -- because a piece leaves the other two parts alone. *)
Lemma conj_three (gT : finGroupType) (A B C A' B' C' a b c : gT) :
  (A * a)%g = (a * A')%g -> (B * b)%g = (b * B')%g -> (C * c)%g = (c * C')%g ->
  commute B a -> commute C a -> commute C b ->
  commute A' b -> commute A' c -> commute B' c ->
  (A' * B' * C')%g = ((A * B * C) ^ (a * b * c))%g.
Proof.
move=> hA hB hC hBa hCa hCb hA'b hA'c hB'c.
have eA : (A ^ a)%g = A' by rewrite conjgE hA mulKg.
have eB : (B ^ b)%g = B' by rewrite conjgE hB mulKg.
have eC : (C ^ c)%g = C' by rewrite conjgE hC mulKg.
rewrite !conjMg !conjgM.
rewrite eA (cfix hA'b) (cfix hA'c).
rewrite (cfix hBa) eB (cfix hB'c).
by rewrite (cfix hCa) (cfix hCb) eC.
Qed.

(* and the centres, which the member does not touch, drop out of the end *)
Lemma conj_drop (gT : finGroupType) (X y z : gT) :
  commute (X ^ y)%g z -> (X ^ (y * z))%g = (X ^ y)%g.
Proof. by move=> h; rewrite conjgM (cfix h). Qed.

(* ---- THE THREE PARTS PUT BACK TOGETHER ---------------------------------- *)

(* The three parts of the kept place, multiplied, are the member's three      *)
(* multiplied and conjugated by the renaming.  This is where the four pieces  *)
(* of the renaming are spent: each part is conjugated by its own piece        *)
(* (conj_three), and the piece on the centres is left commuting with all      *)
(* three, so it drops out (conj_drop).                                        *)
Lemma memb_conj_pt s cX cY uX uY mX mY : (s < 16)%N ->
  up8ok1 cX -> up8ok1 cY -> up8ok1 uX -> up8ok1 uY -> up4ok1 mX -> up4ok1 mY ->
  comp_tab (cpart cX) (restr inC (sy s))
    = comp_tab (restr inC (sy s)) (cpart cY) ->
  comp_tab (upart uX) (restr inU (sy s))
    = comp_tab (restr inU (sy s)) (upart uY) ->
  comp_tab (mpart mX) (restr inM (sy s))
    = comp_tab (restr inM (sy s)) (mpart mY) ->
  (pt 47 (cpart cY) * pt 47 (upart uY) * pt 47 (mpart mY))%g
  = ((pt 47 (cpart cX) * pt 47 (upart uX) * pt 47 (mpart mX))
       ^ pt 47 (sy s))%g.
Proof.
move=> hs hcX hcY huX huY hmX hmY hC hU hM.
have /and4P[prC prU prM prZ] := aiota_lt rprtCP hs.
have /and3P[dcz duz dmz] := dsjZCP.
have pcX : partok inC (cpart cX) by apply: (part_partok clayokC hcX).
have pcY : partok inC (cpart cY) by apply: (part_partok clayokC hcY).
have puX : partok inU (upart uX) by apply: (part_partok ulayokC huX).
have puY : partok inU (upart uY) by apply: (part_partok ulayokC huY).
have pmX : partok inM (mpart mX) by apply: (part_partok mlayokC hmX).
have pmY : partok inM (mpart mY) by apply: (part_partok mlayokC hmY).
(* THE TWO TABLES NAMED, NOT LEFT TO BE GUESSED.  A // here sends done away  *)
(* to evaluate the layouts and it does not come back.                        *)
have eC : (pt 47 (cpart cX) * pt 47 (restr inC (sy s)))%g
        = (pt 47 (restr inC (sy s)) * pt 47 (cpart cY))%g.
  rewrite (ptM (partok_tab pcX) (partok_tab prC)).
  by rewrite (ptM (partok_tab prC) (partok_tab pcY)) hC.
have eU : (pt 47 (upart uX) * pt 47 (restr inU (sy s)))%g
        = (pt 47 (restr inU (sy s)) * pt 47 (upart uY))%g.
  rewrite (ptM (partok_tab puX) (partok_tab prU)).
  by rewrite (ptM (partok_tab prU) (partok_tab puY)) hU.
have eM : (pt 47 (mpart mX) * pt 47 (restr inM (sy s)))%g
        = (pt 47 (restr inM (sy s)) * pt 47 (mpart mY))%g.
  rewrite (ptM (partok_tab pmX) (partok_tab prM)).
  by rewrite (ptM (partok_tab prM) (partok_tab pmY)) hM.
have h3 := conj_three eC eU eM
  (pt_comm puX prC dsj_cu) (pt_comm pmX prC dsj_cm) (pt_comm pmX prU dsj_um)
  (pt_comm pcY prU dsj_cu) (pt_comm pcY prM dsj_cm) (pt_comm puY prM dsj_um).
have hsig : pt 47 (sy s)
  = (pt 47 (restr inC (sy s)) * pt 47 (restr inU (sy s))
     * pt 47 (restr inM (sy s)) * pt 47 (restr inZ (sy s)))%g.
  (* only the renaming on the left, not the four copies of it on the right *)
  rewrite -{1}(eqP (aiota_lt sfullCP hs)).
  rewrite -(ptM (partok_tab prC)
              (tab_ok_comp (partok_tab prU)
                 (tab_ok_comp (partok_tab prM) (partok_tab prZ)))).
  rewrite -(ptM (partok_tab prU)
              (tab_ok_comp (partok_tab prM) (partok_tab prZ))).
  by rewrite -(ptM (partok_tab prM) (partok_tab prZ)) !mulgA.
have hcom : commute ((pt 47 (cpart cX) * pt 47 (upart uX) * pt 47 (mpart mX))
                     ^ (pt 47 (restr inC (sy s)) * pt 47 (restr inU (sy s))
                        * pt 47 (restr inM (sy s))))%g
                    (pt 47 (restr inZ (sy s))).
  rewrite -h3; apply: commute_sym; apply: commuteM; last first.
    by apply: commute_sym; apply: (pt_comm pmY prZ dmz).
  apply: commuteM.
    by apply: commute_sym; apply: (pt_comm pcY prZ dcz).
  by apply: commute_sym; apply: (pt_comm puY prZ duz).
by rewrite hsig (conj_drop hcom).
Qed.

(* ---- the parities the two sides are read at ------------------------------ *)

(* `unplace' reads a member's outer edges at the parity par8[pg] xor          *)
(* par4[e4of bt], and the fold writes at fpar w xor the bit's half.  These    *)
(* three say the two are the same number, on both sides of the fold.          *)

(* the half of a word IS the parity of its middle permutation *)
Definition parbtC : bool :=
  iter nbitn 0%uint63 (fun bt =>
    ((if (bt <? 12)%uint63 then 0 else 1)%uint63
      =? PArray.get par4i (PArray.get e4ofi bt))%uint63).
Lemma parbtCP : parbtC. Proof. by vm_compute. Qed.

(* a renaming keeps the parity of a page ... *)
Definition parKC : bool :=
  iter npagen 0%uint63 (fun pg =>
    (PArray.get par8i (PArray.get fkeepi (fkpt (PArray.get fpgi pg)))
      =? PArray.get par8i pg)%uint63).
Lemma parKCP : parKC. Proof. by vm_compute. Qed.

(* ... and of a middle permutation, so the same parity indexes both sides *)
Definition parBC : bool :=
  iter 16 0%uint63 (fun u =>
    iter nbitn 0%uint63 (fun bt =>
      (PArray.get par4i (PArray.get e4ofi (sbtmv fsbti u bt))
        =? PArray.get par4i (PArray.get e4ofi bt))%uint63)).
Lemma parBCP : parBC. Proof. by vm_compute. Qed.

(* ---- everything the fold names lands in range ---------------------------- *)

(* These are the three RowFoldOk asks of the tables -- a page folds to a kept *)
(* page, a group to a group, a bit to one of the twenty four -- plus the two  *)
(* the assembly below needs.  All five together are a tenth of a second.      *)

Definition fkptRC : bool :=
  iter npagen 0%uint63 (fun pg => (fkpt (PArray.get fpgi pg) <? nrepi)%uint63).
Lemma fkptRCP : fkptRC. Proof. by vm_compute. Qed.

Definition keepRC : bool :=
  iter nrepn 0%uint63 (fun r => (PArray.get fkeepi r <? npagei)%uint63).
Lemma keepRCP : keepRC. Proof. by vm_compute. Qed.

Definition sgrRC : bool :=
  iter nsymn 0%uint63 (fun u => iter nptyn 0%uint63 (fun pty =>
    iter ngroupn 0%uint63 (fun gr => (sgrmv fsgri u pty gr <? ngroupi)%uint63))).
Lemma sgrRCP : sgrRC. Proof. by vm_compute. Qed.

Definition sbtRC : bool :=
  iter nsymn 0%uint63 (fun u =>
    iter nbitn 0%uint63 (fun bt => (sbtmv fsbti u bt <? nbiti)%uint63)).
Lemma sbtRCP : sbtRC. Proof. by vm_compute. Qed.

Definition frnRC : bool :=
  iter npagen 0%uint63 (fun pg => (fren (PArray.get fpgi pg) <? nsymi)%uint63).

(* the parity a member is read at is nought or one *)
Definition ptyRC : bool :=
  iter npagen 0%uint63 (fun pg => iter nbitn 0%uint63 (fun bt =>
    (Uint63.lxor (fpar (PArray.get fpgi pg))
       (if (bt <? 12)%uint63 then 0 else 1) <? 2)%uint63)).
Lemma ptyRCP : ptyRC. Proof. by vm_compute. Qed.
Lemma frnRCP : frnRC. Proof. by vm_compute. Qed.

(* ---- so the place a member folds to is a place --------------------------- *)

Notation Kof pg := (PArray.get fkeepi (fkpt (PArray.get fpgi pg))).
Notation Ptyof pg bt :=
  (Uint63.lxor (fpar (PArray.get fpgi pg))
     (if (bt <? 12)%uint63 then 0%uint63 else 1%uint63)).
Notation Gof pg gr bt :=
  (sgrmv fsgri (fren (PArray.get fpgi pg)) (Ptyof pg bt) gr).
Notation Bof pg bt := (sbtmv fsbti (fren (PArray.get fpgi pg)) bt).
Notation Sof pg := (nth 0%N fren2sym (to_nat (fren (PArray.get fpgi pg)))).

Lemma fold_inrange pg gr bt : inrange pg gr bt ->
  inrange (Kof pg) (Gof pg gr bt) (Bof pg bt).
Proof.
move=> hr; have /and3P[hpg hgr hbt] := hr.
have b0 : (to_nat pg < npagen)%N by apply/nltbP.
have hfk : (to_nat (fkpt (PArray.get fpgi pg)) < nrepn)%N.
  by apply/nltbP; apply: (Row.iter_at fkptRCP b0).
have hu : (to_nat (fren (PArray.get fpgi pg)) < nsymn)%N.
  by apply/nltbP; apply: (Row.iter_at frnRCP b0).
have hb : (to_nat bt < nbitn)%N by apply/nltbP.
have hp : (to_nat (Ptyof pg bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP b0) hb).
have hg : (to_nat gr < ngroupn)%N by apply/nltbP.
apply/and3P; split.
- exact: (Row.iter_at keepRCP hfk).
- exact: (Row.iter_at (Row.iter_at (Row.iter_at sgrRCP hu) hp) hg).
exact: (Row.iter_at (Row.iter_at sbtRCP hu) hb).
Qed.

(* ---- three more ranges, so the six unranks are permutations -------------- *)

Definition ugrpRC : bool :=
  iter ngroupn 0%uint63 (fun gr => iter nptyn 0%uint63 (fun pty =>
    (PArray.get e8invi (Uint63.add (Uint63.mul gr 2) pty) <? npagei)%uint63)).
Lemma ugrpRCP : ugrpRC. Proof. by vm_compute. Qed.

Definition e4ofRC : bool :=
  iter nbitn 0%uint63 (fun bt => (PArray.get e4ofi bt <? nbiti)%uint63).
Lemma e4ofRCP : e4ofRC. Proof. by vm_compute. Qed.

Definition keepNC : bool :=
  iter npagen 0%uint63
    (fun pg => (PArray.get fkeepi (fkpt (PArray.get fpgi pg)) <? npagei)%uint63).
Lemma keepNCP : keepNC. Proof. by vm_compute. Qed.

(* =========================================================================  *)
(*  fold_conj -- THE PLACE A MEMBER FOLDS TO HOLDS THAT MEMBER RENAMED.       *)
(* =========================================================================  *)

(* This is what RowFoldMem.fold_Porb was left standing on, and it is where    *)
(* the six sweeps of RowFoldSym are finally spent.  RowMemb.pt_membinv cuts   *)
(* both sides into three parts, the three part lemmas conjugate each, and     *)
(* memb_conj_pt puts them back together.                                      *)
(*                                                                            *)
(* THE PARITY IS THE HINGE.  unplace reads the outer edges at par8[pg] xor    *)
(* par4[e4of bt] and the fold writes at fpar w xor the bit's half, and the    *)
(* three parity sweeps say those are the same number on both sides -- which   *)
(* is what lets one pty serve where two would not have matched.               *)
Lemma fold_conj_pt pg gr bt : inrange pg gr bt ->
  pt 47 (membinv (unplace e8invi e4ofi par8i par4i
                   (Kof pg) (Gof pg gr bt) (Bof pg bt)))
  = ((pt 47 (membinv (unplace e8invi e4ofi par8i par4i pg gr bt)))
      ^ pt 47 (sy (Sof pg)))%g.
Proof.
move=> hr.
have hr' := fold_inrange hr.
have /and3P[hpg hgr hbt] := hr.
have /and3P[hK hG hB] := hr'.
have b0 : (to_nat pg < npagen)%N by apply/nltbP.
have hb : (to_nat bt < nbitn)%N by apply/nltbP.
have hg : (to_nat gr < ngroupn)%N by apply/nltbP.
have hu : (to_nat (fren (PArray.get fpgi pg)) < nsymn)%N.
  by apply/nltbP; apply: (Row.iter_at frnRCP b0).
have hp : (to_nat (Ptyof pg bt) < nptyn)%N.
  by apply/nltbP; apply: (Row.iter_at (Row.iter_at ptyRCP b0) hb).
have hKn : (to_nat (Kof pg) < npagen)%N by apply/nltbP.
have hGn : (to_nat (Gof pg gr bt) < ngroupn)%N by apply/nltbP.
have hBn : (to_nat (Bof pg bt) < nbitn)%N by apply/nltbP.
have hs : (Sof pg < 16)%N by apply: (aiota_lt f2sCP hu).
have epty : Ptyof pg bt
          = Uint63.lxor (PArray.get par8i pg)
                        (PArray.get par4i (PArray.get e4ofi bt)).
  by rewrite (eqP (Row.iter_at parbtCP hb));
     have /andP[_ /eqP ->] := Row.iter_at fpgCP b0.
have epK : PArray.get par8i (Kof pg) = PArray.get par8i pg.
  by apply/eqP; apply: (Row.iter_at parKCP b0).
have epB : PArray.get par4i (PArray.get e4ofi (Bof pg bt))
         = PArray.get par4i (PArray.get e4ofi bt).
  by apply/eqP; apply: (Row.iter_at (Row.iter_at parBCP hu) hb).
have o1 : up8ok1 pg by apply: (Row.iter_at up8okC b0).
have o2 : up8ok1 (Kof pg) by apply: (Row.iter_at up8okC hKn).
have o3 : up8ok1 (PArray.get e8invi
            (Uint63.add (Uint63.mul gr 2) (Ptyof pg bt))).
  apply: (Row.iter_at up8okC); apply/nltbP.
  exact: (Row.iter_at (Row.iter_at ugrpRCP hg) hp).
have o4 : up8ok1 (PArray.get e8invi
            (Uint63.add (Uint63.mul (Gof pg gr bt) 2) (Ptyof pg bt))).
  apply: (Row.iter_at up8okC); apply/nltbP.
  exact: (Row.iter_at (Row.iter_at ugrpRCP hGn) hp).
have o5 : up4ok1 (PArray.get e4ofi bt).
  by apply: (Row.iter_at up4okC); apply/nltbP; exact: (Row.iter_at e4ofRCP hb).
have o6 : up4ok1 (PArray.get e4ofi (Bof pg bt)).
  by apply: (Row.iter_at up4okC); apply/nltbP; exact: (Row.iter_at e4ofRCP hBn).
rewrite (pt_membinv e8okC e4okC cpartokC upartokC mpartokC hmvokC hr').
rewrite (pt_membinv e8okC e4okC cpartokC upartokC mpartokC hmvokC hr).
rewrite /mcp /mud /mmp /unplace epK epB -epty.
apply: (memb_conj_pt hs o1 o2 o3 o4 o5 o6).
- exact: (cpart_conj b0 o1).
- exact: (upart_conj hu hp hg o3).
exact: (mpart_conj hu hb o5).
Qed.

(* ---- and in the shape RowFoldMem asks for ------------------------------- *)

(* fold_conj_pt is about membinv, which is the member read as a permutation   *)
(* of the forty eight the wrong way round.  What the row carries is memb2tab, *)
(* which is that inverted -- and a conjugate inverted is the inverse          *)
(* conjugated, so the statement comes across unchanged.                       *)
(*                                                                            *)
(* THIS IS RowFoldMem.fold_conj, and with it RowFoldOk's Porb is discharged:  *)
(* members that fold together stand or fall together.                         *)
Lemma fold_conj_memb pg gr bt : inrange pg gr bt ->
  exists2 i, (i < 16)%N &
    pt 47 (memb2tab (unplace e8invi e4ofi par8i par4i
                      (Kof pg) (Gof pg gr bt) (Bof pg bt)))
    = ((pt 47 (memb2tab (unplace e8invi e4ofi par8i par4i pg gr bt)))
        ^ pt 47 (nth [::] sym16ts i))%g.
Proof.
move=> hr; have /and3P[hpg _ _] := hr.
have b0 : (to_nat pg < npagen)%N by apply/nltbP.
have hu : (to_nat (fren (PArray.get fpgi pg)) < nsymn)%N.
  by apply/nltbP; apply: (Row.iter_at frnRCP b0).
exists (Sof pg); first by apply: (aiota_lt f2sCP hu).
have E : forall x, pt 47 (memb2tab x) = ((pt 47 (membinv x))^-1)%g.
  by move=> x; rewrite /memb2tab (ptV (membinv_ok cpartokC upartokC mpartokC x)).
by rewrite !E (fold_conj_pt hr) conjVg.
Qed.
