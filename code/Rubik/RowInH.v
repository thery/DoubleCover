(* =========================================================================  *)
(*  InH.v -- the phase one coordinate solved says the position is in H.       *)
(* =========================================================================  *)

(* WHAT RowReal's r_p1H MEANS.  The pruning table reading nought is not a     *)
(* fact about the cube; what is meant is that the phase one coordinate is     *)
(* the solved one -- no corner twisted, no edge flipped, the four middle      *)
(* edges in the middle layer -- and that this puts the position in H.        *)
(*                                                                            *)
(* THE COORDINATE HALF IS PROVED HERE, in full: a solved coordinate gives     *)
(* the five conditions RowLeaf's hok asks of the table.  hok is read on the   *)
(* INVERSE table, which is where the coordinate already looks: coordfs and    *)
(* coordtw ask what sticker sits at a place, and that is g^-1 of the place.   *)
(*                                                                            *)
(* WHAT IS LEFT is the converse of RowLeaf's inH_hok -- a position of the     *)
(* group whose table keeps the five conditions is in H -- and that one lemma  *)
(* is admitted below, with what it needs written beside it.                   *)
(*                                                                            *)
(* BEING IN THE GROUP IS NOT OPTIONAL.  Two corners swapped and nothing else  *)
(* has a solved coordinate and keeps all five conditions, and it is not in H. *)
(* pstok does not carry it, so the two statements at the foot of the file ask *)
(* for it; in the search it is free, the state being the superflip times a    *)
(* word.                                                                      *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst RowMemb RowLeaf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- what every position of the group already satisfies ------------------ *)

(* Phase1 has the invariant at the identity and across a move, so it travels  *)
(* along the word: the cubies stay together, the corners turn rigidly, the    *)
(* eight twists sum to nought and the flips are even.                         *)
Lemma G_twcP g : g \in G -> twcP g.
Proof.
move=> /mem_gen_ball[n]; move: g.
elim: n => [|n ih] g; first by rewrite ball0 inE => /eqP->; exact: twcP1.
rewrite /= inE => /orP[/ih//|/mulsgP[b m bB mS ->]].
by apply: twcPM; [exact: ih | exact: mS].
Qed.

(* ---- no corner is twisted ------------------------------------------------ *)

(* every digit of the nought coordinate is nought, the eighth included        *)
Lemma dign0 q : dign 0%uint63 q = 0%N.
Proof.
have h0 r : dig3n (to_nat 0%uint63) r = 0%N.
  by rewrite /dig3n to_nat_0 div0n mod0n.
have hs : foldr (fun r a => a + dig3n (to_nat 0%uint63) r) 0%N (iota 0 7) = 0%N.
  by rewrite [iota 0 7]/= /= !h0.
by rewrite /dign; case: eqP => _; [rewrite /dig8 hs | apply: h0].
Qed.

(* the seven stored digits are seven of the orientations and the eighth is    *)
(* the one the sum forces, so a nought coordinate is eight nought             *)
(* orientations                                                              *)
Lemma corientg0 g p : cubcP g -> twsum g = 0%N -> coordtw g = 0%uint63 ->
  (p < 8)%N -> corientg g p = 0%N.
Proof. by move=> cg ts c0 pL; rewrite -(dignE cg ts pL) c0 dign0. Qed.

(* and a nought orientation says the U or D facelet of the place holds a U    *)
(* or D sticker                                                              *)
Lemma corientg0_prim g p : (p < 8)%N -> corientg g p = 0%N ->
  udcol (g^-1 (cprimf p)).
Proof.
move=> pL h.
have := Coordfs.all_iota_lt ctrip_facts pL.
move: h; rewrite /corientg /cprimf.
case E : (nth (0, 0, 0)%N ctrip p) => [[c0 c1] c2].
case: ifP => [hud _|_]; last by case: ifP.
by case/and5P => /eqP -> _ _ _ _.
Qed.

(* ---- no edge is flipped and the slice is solved -------------------------- *)

(* the two halves of the packed summary, read one bit at a time               *)
Lemma nbit_coordfs_flip g p : (p < nedge)%N -> nbit (coordfs g) p = flipb g p.
Proof.
move=> pL; rewrite /coordfs nbit_packn ?ncoord_dig ?pL //.
by rewrite (leq_trans pL) // leq_addr.
Qed.

Lemma nbit_coordfs_slice g p :
  (p < nedge)%N -> nbit (coordfs g) (nedge + p)%N = sliceb g p.
Proof.
move=> pL.
have hb : (nedge + p < ncoord)%N by rewrite /ncoord ltn_add2l.
rewrite /coordfs (@nbit_packn ncoord _ _ hb ncoord_dig).
by rewrite ltnNge leq_addr /= addKn.
Qed.

(* the solved value has every flip bit clear                                  *)
Lemma flipb_solved g p :
  (p < nedge)%N -> coordfs g = coordfs 1 -> flipb g p = false.
Proof.
move=> pL e; rewrite -nbit_coordfs_flip // e nbit_coordfs_flip //.
by rewrite /flipb invg1 perm1 pcol_eprimf.
Qed.

(* and its slice bits are the four places of the middle layer                 *)
Lemma sliceb_solved g p :
  (p < nedge)%N -> coordfs g = coordfs 1 -> sliceb g p = scol (eprimf p).
Proof.
move=> pL e; rewrite -nbit_coordfs_slice // e nbit_coordfs_slice //.
by rewrite /sliceb invg1 perm1.
Qed.

(* ---- reading the inverse table as the inverse permutation ---------------- *)

Lemma nth_inv_tabE t f : tab_ok flast t -> (f < 48)%N ->
  nth 0%N (inv_tab flast t) f = ((pt flast t)^-1 (inord f) : nat).
Proof.
move=> tok fL; have iok := tab_ok_inv tok.
have e1 : ((inord f : facelet) : nat) = f by rewrite inordK.
have e2 : (pt flast t)^-1 (inord f)
        = inord (nth 0%N (inv_tab flast t) (inord f : facelet)).
  by rewrite (ptV tok); exact: ptE _ _ _ iok.
by rewrite e2 e1 inordK // (tab_ltn iok fL).
Qed.

(* ---- three lookups on the edge and corner data --------------------------- *)

(* a primary edge facelet is in the middle layer exactly when its place is    *)
Lemma scol_eposnC :
  all (fun f => (f \in drop 8 eprim ++ drop 8 esec) == (8 <= eposn f)%N) eprim.
Proof. by vm_compute. Qed.

(* and the last four places are the middle ones                               *)
Lemma eprim_sliceC :
  all (fun p => (nth 0%N eprim p \in drop 8 eprim ++ drop 8 esec) == (8 <= p)%N)
      (iota 0 12).
Proof. by vm_compute. Qed.

Lemma cprim_mem f : f \in cprim -> exists2 q, (q < 8)%N & nth 0%N cprim q = f.
Proof.
move=> hf; have hsz : seq.size cprim = 8%N by [].
by exists (index f cprim); [rewrite -hsz index_mem | apply: nth_index].
Qed.

(* ---- the rotation of the corners commutes with the inverse table --------- *)

(* the first of the five, and the only one that is about tables rather than   *)
(* facelets: both sides are tables, so pt_inj turns the equation into one     *)
(* between permutations, and there it is cubcP carried to the inverse.        *)
Lemma comm_ccyct t : tab_ok flast t -> cubcP (pt flast t) ->
  comp_tab (inv_tab flast t) ccyct = comp_tab ccyct (inv_tab flast t).
Proof.
move=> tok cc.
have cok : tab_ok flast ccyct := ccyct_ok.
have vok : tab_ok flast (inv_tab flast t) := tab_ok_inv tok.
apply: (Tsearch.pt_inj (tab_ok_comp vok cok) (tab_ok_comp cok vok)).
rewrite -(ptM vok cok) -(ptM cok vok) -(ptV tok).
apply/permP => f; rewrite !permM.
by have /forallP hi := cubcPI cc; rewrite (eqP (hi f)).
Qed.

(* ---- THE COORDINATE HALF, and it is proved ------------------------------- *)

(* THE FIVE CONDITIONS FROM THE COORDINATE.  The rotation commuting is cubcP  *)
(* carried to the inverse; the pairing is cubP the same way; the U or D       *)
(* sticker of each corner is the twist being nought; the primary sticker of   *)
(* each edge is the flip being nought; and the half of the slice a place      *)
(* belongs to is the slice bits.                                              *)
(*                                                                            *)
(* THE THREE HYPOTHESES BELOW ARE WHAT pstok CARRIES: cubti gives the         *)
(* pairing, twPti the rotation and the sum of the twists.                     *)
Lemma coord_solved_hok t : tab_ok flast t ->
  cubP (pt flast t) -> cubcP (pt flast t) -> twsum (pt flast t) = 0%N ->
  coordtw (pt flast t) = 0%uint63 -> coordfs (pt flast t) = coordfs 1 ->
  hok (inv_tab flast t).
Proof.
move=> tok cg cc ts htw hfs.
have vok : tab_ok flast (inv_tab flast t) := tab_ok_inv tok.
have hv f : (f < 48)%N ->
    nth 0%N (inv_tab flast t) f = ((pt flast t)^-1 (inord f) : nat).
  by move=> fL; apply: nth_inv_tabE.
apply/and5P; split.
(* the rotation of the corners still commutes                                 *)
- by apply/eqP; exact: comm_ccyct tok cc.
(* no corner is twisted                                                       *)
- apply/allP => p; rewrite mem_iota add0n => /andP[_ pL].
  have hcp : nth 0%N cprimp p \in cprim by rewrite -(perm_mem cprimpP) mem_nth.
  have [q qL hq] := cprim_mem hcp.
  have /andP[_ q48] := Coordfs.all_iota_lt cprim_facts qL.
  rewrite -hq hv //.
  exact: (corientg0_prim qL (corientg0 cc ts htw qL)).
(* the two facelets of an edge stay together                                  *)
- have hcv : cubt (inv_tab flast t).
    by rewrite -(cubtE vok) -(ptV tok); exact: cubPV cg.
  apply/allP => f; rewrite mem_iota add0n => /andP[_ fL].
  by rewrite eq_sym; apply: (Coordfs.all_iota_lt hcv fL).
(* no edge is flipped                                                         *)
- apply/allP => p; rewrite mem_iota add0n => /andP[_ pL].
  rewrite hv ?(Coordfs.eprim_lt pL) //.
  by have := flipb_solved pL hfs; rewrite /flipb => /negbT/negbNE.
(* and a place stays in its own half of the slice                             *)
apply/allP => p; rewrite mem_iota add0n => /andP[_ pL].
have p48 := Coordfs.eprim_lt pL.
have hfe : nth 0%N (inv_tab flast t) (nth 0%N eprim p) \in eprim.
  by rewrite (hv _ p48); have := flipb_solved pL hfs;
     rewrite /flipb => /negbT/negbNE.
have := sliceb_solved pL hfs; rewrite /sliceb /scol (eprimfK pL) => hs.
have hsl : (nth 0%N (inv_tab flast t) (nth 0%N eprim p)
             \in drop 8 eprim ++ drop 8 esec)
         = (nth 0%N eprim p \in drop 8 eprim ++ drop 8 esec).
  by rewrite (hv _ p48) hs.
rewrite -(eqP (allP scol_eposnC _ hfe)) hsl.
exact: (Coordfs.all_iota_lt eprim_sliceC pL).
Qed.

(* the same from being in the group, which carries the three                  *)
Lemma G_coord_solved_hok t : tab_ok flast t -> pt flast t \in G ->
  coordtw (pt flast t) = 0%uint63 -> coordfs (pt flast t) = coordfs 1 ->
  hok (inv_tab flast t).
Proof.
move=> tok gG htw hfs.
have /and3P[cg tg _] := G_twcP gG.
have /andP[cc /eqP ts] := tg.
exact: coord_solved_hok tok cg cc ts htw hfs.
Qed.

(* ---- THE ONE STEP LEFT, and it is a fact about the group ----------------- *)

(* THE CONVERSE OF RowLeaf's inH_hok.  That one says a position of H has a    *)
(* table keeping the five conditions; this says a position of the GROUP whose *)
(* table keeps them is in H, so that the five conditions cut H out of G       *)
(* exactly.                                                                   *)
(*                                                                            *)
(* NOTHING IN THE TREE PROVES IT and nothing here does either.  Two ways are  *)
(* known.  One is to solve: turn such a position into a word over the ten     *)
(* generators of H, which is a phase two algorithm and its correctness.  The  *)
(* other is to count: H has 8! * 8! * 4! / 2 elements and so do the positions *)
(* of G keeping the five conditions, and inH_hok already gives one inclusion, *)
(* so the two would be equal -- but neither cardinal is in the tree.          *)
Lemma hok_inH v : tab_ok flast v -> pt flast v \in G -> hok v ->
  pt flast v \in H.
Proof. Admitted.

(* ---- and the statement the row wants ------------------------------------- *)

(* on a table: the coordinate is the solved one, so the position is in H      *)
Lemma inH_of_coord t : tab_ok flast t -> pt flast t \in G ->
  coordtw (pt flast t) = 0%uint63 -> coordfs (pt flast t) = coordfs 1 ->
  pt flast t \in H.
Proof.
move=> tok gG htw hfs.
have vok : tab_ok flast (inv_tab flast t) := tab_ok_inv tok.
have vG : pt flast (inv_tab flast t) \in G by rewrite -(ptV tok) groupV.
have := hok_inH vok vG (G_coord_solved_hok tok gG htw hfs).
by rewrite -(ptV tok) groupV.
Qed.

(* and on a state of the search, which is the shape r_p1H is stated in        *)
Lemma inH_of_coordi x : pstok x -> pt flast (ti2t flast x) \in G ->
  ctwisti x = 0%uint63 -> coordi x = coordfs 1 ->
  pt flast (ti2t flast x) \in H.
Proof.
move=> /and3P[xok _ _] xG htw hfs.
apply: (inH_of_coord (t := ti2t flast x) xok xG).
  by rewrite (ctwisttE xok) -(ctwistiE xok) htw.
by rewrite (coordtE xok) -(coordiE xok) hfs.
Qed.
