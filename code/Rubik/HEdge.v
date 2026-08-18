(* =========================================================================  *)
(*  HEdge.v -- obligation C for the edges: a turn acts on the datum.          *)
(* =========================================================================  *)

(* The e coordinate is a ranking of where the four slice cubies sit and how   *)
(* they lie.  What C needs is that a turn sends that datum to another datum   *)
(* by a rule that does not look at the position -- then the table is the      *)
(* ranking of the rule and is checked datum by datum, 190080 of them, with no *)
(* unranking anywhere.  See the header of HAgree.v.                           *)
(*                                                                            *)
(* THE TWO FACTS A TURN GIVES, both computed here over the twelve turns:      *)
(* it carries edge facelets to edge facelets, and it carries the two facelets *)
(* of a place to the two of one place, primary to primary or to secondary     *)
(* consistently.  So `which place a cubie came from' and `is it turned over'  *)
(* are read off the turn alone, which is eplc and eflp below.                 *)
(*                                                                            *)
(* pt_tab_inj is used from HSound.  It belongs in Table.v -- two tables that  *)
(* differ present different permutations is about tables and nothing else --  *)
(* and moving it there is a rebuild of the whole chain, so it waits.          *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon HSound.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- inverting a composition, on tables ---------------------------------- *)

(* Table.v has neither this nor pt_tab_inj; with the second the first is one  *)
(* step through the permutations.                                            *)
Lemma inv_tab_comp t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  inv_tab flast (comp_tab t1 t2)
    = comp_tab (inv_tab flast t2) (inv_tab flast t1).
Proof.
move=> ok1 ok2.
apply: pt_tab_inj; first by apply: tab_ok_inv; apply: tab_ok_comp.
  by apply: tab_ok_comp; apply: tab_ok_inv.
by rewrite -ptV ?tab_ok_comp // -ptM // -ptM ?tab_ok_inv // -!ptV // invMg.
Qed.

(* ---- what a turn does to a place ----------------------------------------- *)

(* the facelet the sticker at the primary facelet of place j comes from       *)
Definition eidx (m j : nat) : nat :=
  index (nth 0%N (inv_tab flast (mvt m)) (nth 0%N eprim j)) (eprim ++ esec).

(* the place it came from, and whether it is turned over on the way           *)
Definition eplc (m j : nat) : nat := (eidx m j %% nedge)%N.
Definition eflp (m j : nat) : nat := (eidx m j %/ nedge)%N.

(* A TURN KEEPS EDGES EDGES, both ways round.                                 *)
Lemma emv_edge :
  all (fun m => all (fun f =>
         (index (nth 0%N (mvt m) f) (eprim ++ esec) < 24)%N)
                    (eprim ++ esec)) (iota 0 nq)
  &&
  all (fun m => all (fun f =>
         (index (nth 0%N (inv_tab flast (mvt m)) f) (eprim ++ esec) < 24)%N)
                    (eprim ++ esec)) (iota 0 nq).
Proof. by vm_compute. Qed.

(* AND IT KEEPS THE TWO FACELETS OF A PLACE TOGETHER: they land on the two of *)
(* one place, one on the primary and one on the secondary.                    *)
Lemma emv_pair :
  all (fun m => all (fun j =>
    let ip := index (nth 0%N (mvt m) (nth 0%N eprim j)) (eprim ++ esec) in
    let is_ := index (nth 0%N (mvt m) (nth 0%N esec j)) (eprim ++ esec) in
    ((ip %% nedge == is_ %% nedge) && (ip %/ nedge + is_ %/ nedge == 1))%N)
    (iota 0 nedge)) (iota 0 nq).
Proof. by vm_compute. Qed.

(* eplc is a permutation of the twelve places, and eflp is a bit             *)
Lemma eplc_perm :
  all (fun m => (perm_eq [seq eplc m j | j <- iota 0 nedge] (iota 0 nedge)) &&
                all (fun j => (eflp m j < 2)%N) (iota 0 nedge)) (iota 0 nq).
Proof. by vm_compute. Qed.

(* ---- reading a sticker back through the turn ----------------------------- *)

(* The whole dependence on the position is here, and it is one step: after    *)
(* the turn, the sticker at a facelet is the one that was at the facelet the  *)
(* turn brings it from.  Which facelet that is depends on the turn alone.     *)
Lemma ti2t_mvq : all (fun m => ti2t flast (mvq m) == mvt m) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma tabi_ok_mvq m : (m < nq)%N -> tabi_ok flast (mvq m).
Proof.
move=> mL; rewrite /tabi_ok.
have /eqP -> := allP ti2t_mvq _ (mem_iota0 mL).
by apply: mvt_ok.
Qed.

Lemma getn_step (a : arr) (m f : nat) : tabi_ok flast a -> (m < nq)%N ->
  (f < 48)%N ->
  getn (inv_tabi flast (comp_tabi flast a (mvq m))) f
    = getn (inv_tabi flast a) (nth 0%N (inv_tab flast (mvt m)) f).
Proof.
move=> aok mL fL.
have mok := tabi_ok_mvq mL.
have /eqP mE := allP ti2t_mvq _ (mem_iota0 mL).
have cok := tabi_ok_comp n47_small n47_len aok mok.
rewrite /getn
  -[to_nat (get (inv_tabi flast _) (of_nat f))](nth_ti2t (n := flast)) //.
rewrite -[to_nat (get (inv_tabi flast a) _)](nth_ti2t (n := flast)) //;
    last first.
  by have := tab_lt (t := inv_tab flast (mvt m)) (inord f : facelet)
       (tab_ok_inv (mvt_ok mL)); rewrite inordK.
rewrite (ti2t_inv n47_small n47_len cok) (ti2t_inv n47_small n47_len aok).
rewrite (ti2t_comp n47_small n47_len aok mok) mE.
rewrite (inv_tab_comp aok (mvt_ok mL)).
by rewrite nth_comp_tab // size_inv_tab.
Qed.

(* ---- the two facelets of a place hold one cubie -------------------------- *)

(* This is where the guard is spent.  When the turn brings a sticker in on    *)
(* the secondary facelet of its place, the cubie is read from there, and it   *)
(* is the same cubie only because the position keeps the two facelets of an   *)
(* edge together.                                                             *)
Lemma esec_epairn : all (fun j => nth 0%N esec j == epairn (nth 0%N eprim j))
  (iota 0 nedge).
Proof. by vm_compute. Qed.

Lemma eposn_epairn : all (fun f => eposn (epairn f) == eposn f) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma eprim_lt48 :
  all (fun j => (nth 0%N eprim j < 48)%N && (nth 0%N esec j < 48)%N)
      (iota 0 nedge).
Proof. by vm_compute. Qed.

(* the coordinates read the inverse of the position, so the guard has to be   *)
(* carried there, and it is: the pairing commutes with a permutation exactly  *)
(* when it commutes with its inverse                                          *)
Lemma cubt_inv t : tab_ok flast t -> cubt t -> cubt (inv_tab flast t).
Proof.
move=> tok ct.
rewrite -(cubtE (tab_ok_inv tok)) -ptV //.
by apply: cubPV; rewrite cubtE.
Qed.

(* A REWRITE THAT DOES NOT COME BACK.  Pushing both getn through nth_ti2t in  *)
(* one rewrite hangs; naming each of the two equalities first is instant.     *)
Lemma getn_sec (u : arr) j : tabi_ok flast u -> cubt (ti2t flast u) ->
  (j < nedge)%N ->
  eposn (getn u (nth 0%N esec j)) = eposn (getn u (nth 0%N eprim j)).
Proof.
move=> uok cu jL.
have /andP[pL sL] := allP eprim_lt48 _ (mem_iota0 jL).
have /eqP pj := allP esec_epairn _ (mem_iota0 jL).
have h1 : getn u (nth 0%N esec j) = nth 0%N (ti2t flast u) (nth 0%N esec j).
  by rewrite /getn (nth_ti2t u sL).
have h2 : getn u (nth 0%N eprim j) = nth 0%N (ti2t flast u) (nth 0%N eprim j).
  by rewrite /getn (nth_ti2t u pL).
rewrite h1 h2 pj.
have /eqP <- := allP cu _ (mem_iota0 (n := nfacelet) pL).
apply/eqP; apply: (allP eposn_epairn); apply: mem_iota0.
by have := tab_lt (t := ti2t flast u) (inord (nth 0%N eprim j) : facelet) uok;
   rewrite inordK.
Qed.

(* ---- the place after a turn --------------------------------------------- *)

(* THE CORE OF C FOR THE EDGES: where a cubie is after a turn depends on      *)
(* where it was and on the turn, and on nothing else about the position.      *)
Lemma eidx_lt : all (fun m => all (fun j => (eidx m j < 24)%N) (iota 0 nedge))
  (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma size_ee : seq.size (eprim ++ esec) = 24%N.
Proof. by vm_compute. Qed.

Lemma size_eprim : seq.size eprim = nedge.
Proof. by vm_compute. Qed.

Lemma emv_in m j : (m < nq)%N -> (j < nedge)%N ->
  nth 0%N (inv_tab flast (mvt m)) (nth 0%N eprim j)
    = nth 0%N (eprim ++ esec) (eidx m j).
Proof.
move=> mL jL.
rewrite /eidx nth_index // -index_mem size_ee.
by have := allP (allP eidx_lt _ (mem_iota0 mL)) _ (mem_iota0 jL).
Qed.

Lemma eplace_step (a : arr) m j : tabi_ok flast a ->
  cubt (ti2t flast (inv_tabi flast a)) -> (m < nq)%N -> (j < nedge)%N ->
  eplace (inv_tabi flast (comp_tabi flast a (mvq m))) j
    = eplace (inv_tabi flast a) (eplc m j).
Proof.
move=> aok cu mL jL.
have /andP[pL _] := allP eprim_lt48 _ (mem_iota0 jL).
have iL := allP (allP eidx_lt _ (mem_iota0 mL)) _ (mem_iota0 jL).
have uok : tabi_ok flast (inv_tabi flast a).
  by rewrite /tabi_ok (ti2t_inv n47_small n47_len aok); apply: tab_ok_inv.
have cL : (eplc m j < nedge)%N by rewrite /eplc ltn_mod.
rewrite /eplace (getn_step aok mL pL) (emv_in mL jL).
case: (ltnP (eidx m j) nedge) => h.
  rewrite nth_cat size_eprim h.
  by rewrite /eplc modn_small.
rewrite nth_cat size_eprim ltnNge h /=.
have -> : (eidx m j - nedge = eplc m j)%N.
  by rewrite /eplc -{2}(subnK h) modnDr modn_small // ltn_subLR.
by apply: getn_sec.
Qed.

(* ---- the flip after a turn ---------------------------------------------- *)

(* The twin of eplace_step, and the one difference: reading the cubie off the *)
(* secondary facelet of its place is exactly what turns it over, so the flip  *)
(* picks up eflp m j where the place picks up nothing.                        *)
Lemma epairn_fixn :
  all (fun f => (epairn f == f) == (f \notin eprim ++ esec)) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma epairn_eprim :
  all (fun f => (f \in eprim ++ esec) ==>
        ((epairn f \in eprim) == (f \notin eprim))) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma epairn_lt : all (fun f => (epairn f < 48)%N) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma eprim_mem : all (fun j => (nth 0%N eprim j \in eprim ++ esec) &&
                                (nth 0%N esec j \in eprim ++ esec))
                      (iota 0 nedge).
Proof. by vm_compute. Qed.

Lemma ee_lt48 : all (fun f => (f < 48)%N) (eprim ++ esec).
Proof. by vm_compute. Qed.

(* An edge facelet holds an edge sticker, and that is not free either: it     *)
(* follows from the guard, since the pairing moves a facelet exactly when the *)
(* facelet is an edge one, and the position is injective.                     *)
Lemma getn_edge (u : arr) f : tabi_ok flast u -> cubt (ti2t flast u) ->
  (f < 48)%N -> (f \in eprim ++ esec) -> (getn u f \in eprim ++ esec).
Proof.
move=> uok cu fL fin.
have /and3P[/eqP usz _ uuniq] := uok.
have pfL := allP epairn_lt _ (mem_iota0 fL).
have hx : getn u f = nth 0%N (ti2t flast u) f by rewrite /getn (nth_ti2t u fL).
have xL : (getn u f < 48)%N.
  by rewrite hx; have := tab_lt (t := ti2t flast u) (inord f : facelet) uok;
     rewrite inordK.
have /eqP he := allP epairn_fixn _ (mem_iota0 xL).
have /eqP hc := allP cu _ (mem_iota0 (n := nfacelet) fL).
apply/negPn/negP => hnot.
have hfix : epairn (getn u f) = getn u f by apply/eqP; rewrite he.
move: hc; rewrite -hx hfix hx => hEq.
have : (epairn f == f).
  by rewrite -(nth_uniq 0%N _ _ uuniq) ?usz // -hEq.
have /eqP hf2 := allP epairn_fixn _ (mem_iota0 fL).
by rewrite hf2 fin.
Qed.

(* the sticker at the secondary facelet is the partner of the one at the      *)
(* primary -- the guard again, at the level of the sticker                    *)
Lemma getn_pair (u : arr) j : tabi_ok flast u -> cubt (ti2t flast u) ->
  (j < nedge)%N ->
  getn u (nth 0%N esec j) = epairn (getn u (nth 0%N eprim j)).
Proof.
move=> uok cu jL.
have /andP[pL sL] := allP eprim_lt48 _ (mem_iota0 jL).
have /eqP pj := allP esec_epairn _ (mem_iota0 jL).
have h1 : getn u (nth 0%N esec j) = nth 0%N (ti2t flast u) (nth 0%N esec j).
  by rewrite /getn (nth_ti2t u sL).
have h2 : getn u (nth 0%N eprim j) = nth 0%N (ti2t flast u) (nth 0%N eprim j).
  by rewrite /getn (nth_ti2t u pL).
rewrite h1 h2 pj.
by have /eqP <- := allP cu _ (mem_iota0 (n := nfacelet) pL).
Qed.

Lemma eflipn_step (a : arr) m j : tabi_ok flast a ->
  cubt (ti2t flast (inv_tabi flast a)) -> (m < nq)%N -> (j < nedge)%N ->
  eflipn (inv_tabi flast (comp_tabi flast a (mvq m))) j
    = ((eflipn (inv_tabi flast a) (eplc m j) + eflp m j) %% 2)%N.
Proof.
move=> aok cu mL jL.
have /andP[pL _] := allP eprim_lt48 _ (mem_iota0 jL).
have iL := allP (allP eidx_lt _ (mem_iota0 mL)) _ (mem_iota0 jL).
have uok : tabi_ok flast (inv_tabi flast a).
  by rewrite /tabi_ok (ti2t_inv n47_small n47_len aok); apply: tab_ok_inv.
have cL : (eplc m j < nedge)%N by rewrite /eplc ltn_mod.
rewrite /eflipn (getn_step aok mL pL) (emv_in mL jL).
case: (ltnP (eidx m j) nedge) => h.
  have e1 : eplc m j = eidx m j by rewrite /eplc modn_small.
  have e2 : eflp m j = 0%N by rewrite /eflp divn_small.
  rewrite nth_cat size_eprim h e1 e2 addn0.
  by case: (_ \in _).
have e1 : (eidx m j - nedge = eplc m j)%N.
  by rewrite /eplc -{2}(subnK h) modnDr modn_small // ltn_subLR.
have e2 : eflp m j = 1%N.
  rewrite /eflp; apply/eqP; rewrite eqn_leq -ltnS.
  by rewrite divn_gt0 // h andbT ltn_divLR.
have /andP[cpL _] := allP eprim_lt48 _ (mem_iota0 cL).
have /andP[cpM _] := allP eprim_mem _ (mem_iota0 cL).
rewrite nth_cat size_eprim ltnNge h /= e1 e2 (getn_pair uok cu cL).
set X := getn (inv_tabi flast a) (nth 0%N eprim (eplc m j)).
have XM : X \in eprim ++ esec by apply: getn_edge.
have /implyP/(_ XM)/eqP -> :=
  allP epairn_eprim _ (mem_iota0 (allP ee_lt48 _ XM)).
by case: (X \in eprim).
Qed.

(* ---- what is left -------------------------------------------------------- *)

(* The place and the flip are both done, so a turn moves the pair (place,     *)
(* flip) of every one of the twelve edge slots by a rule with no position in  *)
(* it.  What is left for the edges: eslot, which picks out of those twelve    *)
(* the four the coordinate reads; the datum, which is those four; and the     *)
(* sweep over the 190080 data, which ties the rule to the table.  Then the    *)
(* same twice more for the corners, where there are 70 and 2187 data and no   *)
(* pairing to keep.                                                           *)
