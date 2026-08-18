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

(* ---- a position permutes the places -------------------------------------- *)

(* eslot picks, out of the twelve places, the one holding a given cubie, so   *)
(* it is only well behaved because there is exactly one.  That is not free    *)
(* either: two places holding the same cubie would have to hold its two       *)
(* facelets, and then the guard and injectivity put a primary facelet on a    *)
(* secondary one.                                                             *)
Lemma eprim_esec_disj :
  all (fun j1 => all (fun j2 => nth 0%N esec j1 != nth 0%N eprim j2)
        (iota 0 nedge)) (iota 0 nedge).
Proof. by vm_compute. Qed.

Lemma eprim_inj :
  all (fun j1 => all (fun j2 => (nth 0%N eprim j1 == nth 0%N eprim j2) ==>
        (j1 == j2)) (iota 0 nedge)) (iota 0 nedge).
Proof. by vm_compute. Qed.

(* two edge facelets are on the same place exactly when they are the same     *)
(* facelet or the two of that place                                           *)
Lemma eposn_inj :
  all (fun f1 => all (fun f2 =>
        ((f1 \in eprim ++ esec) && (f2 \in eprim ++ esec)) ==>
        ((eposn f1 == eposn f2) == ((f1 == f2) || (f1 == epairn f2))))
        (iota 0 48)) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma eplace_inj (u : arr) j1 j2 : tabi_ok flast u -> cubt (ti2t flast u) ->
  (j1 < nedge)%N -> (j2 < nedge)%N -> eplace u j1 = eplace u j2 -> j1 = j2.
Proof.
move=> uok cu j1L j2L he.
have /and3P[/eqP usz _ uuniq] := uok.
have /andP[p1L s1L] := allP eprim_lt48 _ (mem_iota0 j1L).
have /andP[p2L s2L] := allP eprim_lt48 _ (mem_iota0 j2L).
have /andP[p1M _] := allP eprim_mem _ (mem_iota0 j1L).
have /andP[p2M s2M] := allP eprim_mem _ (mem_iota0 j2L).
have X1M := getn_edge uok cu p1L p1M.
have X2M := getn_edge uok cu p2L p2M.
have h1 : getn u (nth 0%N eprim j1) = nth 0%N (ti2t flast u) (nth 0%N eprim j1).
  by rewrite /getn (nth_ti2t u p1L).
have h2 : getn u (nth 0%N eprim j2) = nth 0%N (ti2t flast u) (nth 0%N eprim j2).
  by rewrite /getn (nth_ti2t u p2L).
have hs : getn u (nth 0%N esec j2) = nth 0%N (ti2t flast u) (nth 0%N esec j2).
  by rewrite /getn (nth_ti2t u s2L).
have /implyP/(_ (introT andP (conj X1M X2M)))/eqP hd :=
  allP (allP eposn_inj _ (mem_iota0 (allP ee_lt48 _ X1M))) _
       (mem_iota0 (allP ee_lt48 _ X2M)).
move: he; rewrite /eplace => /eqP; rewrite hd => /orP[/eqP hx|/eqP hx].
  apply/eqP; have /implyP := allP (allP eprim_inj _ (mem_iota0 j1L)) _
    (mem_iota0 j2L); apply.
  have i1 : (nth 0%N eprim j1 < seq.size (ti2t flast u))%N by rewrite usz.
  have i2 : (nth 0%N eprim j2 < seq.size (ti2t flast u))%N by rewrite usz.
  have hnu := nth_uniq 0%N i1 i2 uuniq.
  by rewrite -hnu -h1 -h2 hx.
have i1 : (nth 0%N eprim j1 < seq.size (ti2t flast u))%N by rewrite usz.
have i3 : (nth 0%N esec j2 < seq.size (ti2t flast u))%N by rewrite usz.
have hnu := nth_uniq 0%N i1 i3 uuniq.
have hcon : nth 0%N eprim j1 == nth 0%N esec j2.
  by rewrite -hnu -h1 -hs (getn_pair uok cu j2L) hx.
have /negP := allP (allP eprim_esec_disj _ (mem_iota0 j2L)) _ (mem_iota0 j1L).
by case; rewrite eq_sym.
Qed.

(* ---- every cubie is somewhere, and the fold finds it --------------------- *)

(* eslot runs over the twelve places and keeps the last that holds the cubie *)
(* it is after.  With eplace_inj there is at most one, and since the twelve  *)
(* places carry twelve distinct values below twelve there is exactly one.    *)
Lemma eplace_ltn (u : arr) j : (eplace u j < nedge)%N.
Proof. by rewrite /eplace /eposn ltn_mod. Qed.

Lemma eplace_onto (u : arr) v : tabi_ok flast u -> cubt (ti2t flast u) ->
  (v < nedge)%N -> exists2 j, (j < nedge)%N & eplace u j = v.
Proof.
move=> uok cu vL.
have huniq : uniq [seq eplace u j | j <- iota 0 nedge].
  have hinj : {in iota 0 nedge &, injective (eplace u)}.
    move=> x y; rewrite !mem_iota !add0n => /andP[_ xL] /andP[_ yL].
    by apply: eplace_inj.
  rewrite (map_inj_in_uniq hinj); exact: iota_uniq.
have hsub : {subset [seq eplace u j | j <- iota 0 nedge] <= iota 0 nedge}.
  by move=> x /mapP[j _ ->]; rewrite mem_iota add0n eplace_ltn.
have hsz : (seq.size (iota 0 nedge)
              <= seq.size [seq eplace u j | j <- iota 0 nedge])%N.
  by rewrite size_map.
have [_ hi] := uniq_min_size huniq hsub hsz.
have : v \in [seq eplace u j | j <- iota 0 nedge].
  by rewrite hi mem_iota add0n.
by case/mapP => j; rewrite mem_iota add0n => /andP[_ jL] ->; exists j.
Qed.

(* the fold keeps what the one match gives it                                 *)
Lemma foldl_uniq (T : Type) (g : nat -> T) (P : nat -> bool) n s0 j0 :
  (j0 < n)%N -> P j0 -> (forall j, (j < n)%N -> P j -> j = j0) ->
  foldl (fun s j => if P j then g j else s) s0 (iota 0 n) = g j0.
Proof.
elim: n j0 => [|n ih] j0 // j0L Pj0 hun.
rewrite -[n.+1]addn1 iotaD add0n foldl_cat /=.
case: ifP => [Pn|Pn].
  by rewrite (hun n _ Pn).
have j0n : (j0 < n)%N.
  rewrite ltn_neqAle -ltnS j0L andbT.
  by apply/eqP => e; move: Pn; rewrite -e Pj0.
by apply: ih => // j jL Pj; apply: hun => //; apply: ltnW.
Qed.

(* ---- the guard survives a turn ------------------------------------------- *)

(* Which is also what the search needs of the positions it meets.            *)
Lemma cubt_mvt : all (fun m => cubt (mvt m)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma cubt_comp t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  cubt t1 -> cubt t2 -> cubt (comp_tab t1 t2).
Proof.
move=> ok1 ok2 c1 c2.
rewrite -(cubtE (tab_ok_comp ok1 ok2)) -ptM //.
by apply: cubPM; rewrite cubtE.
Qed.

Lemma cubt_step (a : arr) m : tabi_ok flast a -> (m < nq)%N ->
  cubt (ti2t flast a) -> cubt (ti2t flast (comp_tabi flast a (mvq m))).
Proof.
move=> aok mL ca.
have /eqP mE := allP ti2t_mvq _ (mem_iota0 mL).
rewrite (ti2t_comp n47_small n47_len aok (tabi_ok_mvq mL)) mE.
by apply: cubt_comp => //; [apply: mvt_ok | apply: (allP cubt_mvt);
   apply: mem_iota0].
Qed.

Lemma tabi_ok_invi a : tabi_ok flast a -> tabi_ok flast (inv_tabi flast a).
Proof.
by move=> aok; rewrite /tabi_ok (ti2t_inv n47_small n47_len aok);
   apply: tab_ok_inv.
Qed.

Lemma cubt_invi a : tabi_ok flast a -> cubt (ti2t flast a) ->
  cubt (ti2t flast (inv_tabi flast a)).
Proof.
by move=> aok ca; rewrite (ti2t_inv n47_small n47_len aok); apply: cubt_inv.
Qed.

(* ---- THE DATUM STEPS ----------------------------------------------------- *)

(* Where a place goes, read backwards: the turn takes einv m j to j.         *)
Definition einv (m j : nat) : nat := index j [seq eplc m k | k <- iota 0 nedge].

Lemma einv_tab :
  all (fun m => all (fun j =>
        [&& einv m j < nedge, eplc m (einv m j) == j & einv m (eplc m j) == j])
      (iota 0 nedge)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma einv_lt m j : (m < nq)%N -> (j < nedge)%N -> (einv m j < nedge)%N.
Proof.
by move=> mL jL; have /and3P[h _ _] := allP (allP einv_tab _ (mem_iota0 mL)) _
  (mem_iota0 jL).
Qed.

Lemma eplc_einv m j : (m < nq)%N -> (j < nedge)%N -> eplc m (einv m j) = j.
Proof.
move=> mL jL.
by have /and3P[_ /eqP h _] := allP (allP einv_tab _ (mem_iota0 mL)) _
  (mem_iota0 jL).
Qed.

Lemma einv_eplc m j : (m < nq)%N -> (j < nedge)%N -> einv m (eplc m j) = j.
Proof.
move=> mL jL.
by have /and3P[_ _ /eqP h] := allP (allP einv_tab _ (mem_iota0 mL)) _
  (mem_iota0 jL).
Qed.

Lemma eflipn_lt (u : arr) j : (eflipn u j < 2)%N.
Proof. by rewrite /eflipn; case: ifP. Qed.

(* eslot is the place of a cubie and its flip, and it is the fold that says   *)
(* so -- there is exactly one place holding the cubie                         *)
Lemma eslotE (u : arr) i j0 : tabi_ok flast u -> cubt (ti2t flast u) ->
  (j0 < nedge)%N -> eplace u j0 = (nedge - nslicec + i)%N ->
  eslot u i = (2 * j0 + eflipn u j0)%N.
Proof.
move=> uok cu j0L hj0.
rewrite /eslot.
apply: (@foldl_uniq _ (fun j => (2 * j + eflipn u j)%N)
          (fun j => eplace u j == (nedge - nslicec + i)%N) nedge 0%N j0) => //.
  by rewrite hj0.
move=> j jL /eqP hj; apply: eplace_inj uok cu jL j0L _.
by rewrite hj hj0.
Qed.

(* THE MATHEMATICS OF C, FOR ONE SLICE CUBIE.  Where it sits and how it lies  *)
(* after a turn is a rule in the turn and in where it sat and how it lay, and *)
(* there is no position left in it.                                           *)
Lemma eslot_step (a : arr) m i : tabi_ok flast a -> cubt (ti2t flast a) ->
  (m < nq)%N -> (i < nslicec)%N ->
  eslot (inv_tabi flast (comp_tabi flast a (mvq m))) i =
    (let x := eslot (inv_tabi flast a) i in
     let j' := einv m (x %/ 2)%N in
     2 * j' + (x %% 2 + eflp m j') %% 2)%N.
Proof.
move=> aok ca mL iL.
have uok := tabi_ok_invi aok.
have cu := cubt_invi aok ca.
have vL : (nedge - nslicec + i < nedge)%N by [].
have [j0 j0L hj0] := eplace_onto uok cu vL.
have hx := eslotE uok cu j0L hj0.
have j'L : (einv m j0 < nedge)%N by apply: einv_lt.
have a'ok := tabi_ok_comp n47_small n47_len aok (tabi_ok_mvq mL).
have ca' := cubt_step aok mL ca.
have u'ok := tabi_ok_invi a'ok.
have cu' := cubt_invi a'ok ca'.
have hpl := eplace_step aok cu mL j'L.
rewrite (eplc_einv mL j0L) in hpl.
have hj' : eplace (inv_tabi flast (comp_tabi flast a (mvq m))) (einv m j0)
             = (nedge - nslicec + i)%N by rewrite hpl.
rewrite (eslotE u'ok cu' j'L hj') (eflipn_step aok cu mL j'L).
rewrite (eplc_einv mL j0L) hx.
have f2 : (eflipn (inv_tabi flast a) j0 < 2)%N := eflipn_lt _ _.
cbv zeta.
set k := (2 * j0 + eflipn (inv_tabi flast a) j0)%N.
have hk1 : (k %/ 2)%N = j0.
  rewrite /k [(2 * j0)%N]mulnC divnMDl.
    by rewrite (divn_small f2) addn0.
  by [].
have hk2 : (k %% 2)%N = eflipn (inv_tabi flast a) j0.
  rewrite /k [(2 * j0)%N]mulnC modnMDl.
  by rewrite (modn_small f2).
by rewrite hk1 hk2.
Qed.

(* ---- what is left -------------------------------------------------------- *)

(* The place and the flip are both done, so a turn moves the pair (place,     *)
(* flip) of every one of the twelve edge slots by a rule with no position in  *)
(* it.  What is left for the edges: eslot, which picks out of those twelve    *)
(* the four the coordinate reads; the datum, which is those four; and the     *)
(* sweep over the 190080 data, which ties the rule to the table.  Then the    *)
(* same twice more for the corners, where there are 70 and 2187 data and no   *)
(* pairing to keep.                                                           *)
