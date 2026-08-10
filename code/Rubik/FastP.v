(* =========================================================================  *)
(*  FastP.v -- The proofs about Fast.v: searchz3n equals searchz3.          *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Coordfsi Moves Redun Searchir Phase1 Far Farp1 Fast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(*  Towards searchz3nE: the pieces, all proved                                *)
(* =========================================================================  *)

(* the early exit changes nothing *)
Lemma eq_tabifE a b : eq_tabif a b = eq_tabi 47 a b.
Proof.
rewrite /eq_tabif /eq_tabi.
have gen : forall k i, eqif k i a b = eqi k i a b.
  by elim=> [|k IH] i //=; case: (_ =? _)%uint63; rewrite ?IH.
by apply: gen.
Qed.

(* max <= c iff both are: what lets the nine lookups short circuit *)
Lemma maxi_leb a b c :
  (maxi a b <=? c)%uint63 = ((a <=? c)%uint63 && (b <=? c)%uint63).
Proof.
apply/idP/idP; rewrite /maxi.
  case: ifP => hab h; apply/andP; split.
  - by move/nlebP: hab => hab; move/nlebP: h => h;
       apply/nlebP; apply: leq_trans hab h.
  - exact: h.
  - exact: h.
  move/nlebP: h => h; apply/nlebP.
  have hba : to_nat b <= to_nat a.
    apply: ltnW; rewrite ltnNge; apply/negP => hc.
    by move: hab; have := introT (nlebP a b) hc => ->.
  by apply: leq_trans hba h.
by case/andP => ha hb; case: ifP.
Qed.

Lemma hv1leE T tf di : hv1le T tf di = (hv1 T tf <=? di)%uint63.
Proof.
rewrite /hv1le /hv1 !maxi_leb.
by case: (_ <=? _)%uint63; case: (_ <=? _)%uint63; case: (_ <=? _)%uint63.
Qed.

(* maxi_leb is restricted to the two OUTER maxi, or it fires inside hv1 too
   and the two sides stop matching *)
Lemma h3leE T x di : h3le T x di = (h3i T x <=? di)%uint63.
Proof.
case: x => [[x0 x1] x2]; rewrite /h3le /h3i.
rewrite (maxi_leb (hv1 T x0)) (maxi_leb (hv1 T x1)) !hv1leE.
by case: (hv1 T x0 <=? di)%uint63; case: (hv1 T x1 <=? di)%uint63;
   case: (hv1 T x2 <=? di)%uint63.
Qed.

(* the whole list at once: eighteen separate vm_computes did not return *)
Lemma mtisaE_all : [seq PArray.get mtisa (of_nat k) | k <- iota 0 18] = mtis.
Proof. by vm_compute. Qed.

Lemma mtisaE k : (k < 18)%N ->
  PArray.get mtisa (of_nat k) = nth (id_tabi 47) mtis k.
Proof.
move=> kL; rewrite -mtisaE_all (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

Lemma step3iE x k :
  step3i x ((of_nat k, of_nat (nth 0%N mv3a k)), of_nat (nth 0%N mv3b k))
  = step3 x k.
Proof.
by case: x => [[x0 x1] x2]; rewrite /step3i /step3 !acttwiiE !actfsriE.
Qed.

(* allowed3 is its own definition, so this is conversion; it is stated
   because the induction needs to rewrite with it. *)
Lemma allowed3E_all :
  allowed3 =
  [seq [seq (((of_nat k, of_nat (nth 0%N mv3a k)), of_nat (nth 0%N mv3b k)),
             fcpos k)
       | k <- allowedr mtis nfcube oppf fcpos p]
  | p <- iota 0 7].
Proof. by vm_compute. Qed.

Lemma allowed3E p : (p < 7)%N ->
  nth [::] allowed3 p =
  [seq (((of_nat k, of_nat (nth 0%N mv3a k)), of_nat (nth 0%N mv3b k)),
        fcpos k)
  | k <- allowedr mtis nfcube oppf fcpos p].
Proof.
move=> pL; rewrite allowed3E_all (nth_map 0%N); last by rewrite size_iota.
by rewrite nth_iota.
Qed.

(* ---- the solved test, which is the one step that is not a reordering ----- *)

Lemma tabi_ok_idi : tabi_ok 47 (id_tabi 47).
Proof. by rewrite /tabi_ok (ti2t_id n47_small n47_len); exact: tab_ok_id. Qed.

(* init3 factors through ti2t, so tables with the same ti2t have the same
   three views *)
Lemma init3_ti2t a b : tabi_ok 47 a -> tabi_ok 47 b ->
  ti2t 47 a = ti2t 47 b -> init3 a = init3 b.
Proof.
move=> aok bok hab.
have step : forall u v, tabi_ok 47 u -> tabi_ok 47 v ->
    ti2t 47 u = ti2t 47 v -> ti2t 47 (conj3 u) = ti2t 47 (conj3 v).
  by move=> u v uok vok huv; rewrite !conj3E !(ti2t_conji rot3t_ok) // huv.
have ok3a := tabi_ok_conj3 aok; have ok3b := tabi_ok_conj3 bok.
have ok33a := tabi_ok_conj3 ok3a; have ok33b := tabi_ok_conj3 ok3b.
have h3 := step _ _ aok bok hab.
have h33 := step _ _ ok3a ok3b h3.
rewrite /init3 (ctwisti_ti2t aok bok hab) (coordi_ti2t aok bok hab).
rewrite (ctwisti_ti2t ok3a ok3b h3) (coordi_ti2t ok3a ok3b h3).
by rewrite (ctwisti_ti2t ok33a ok33b h33) (coordi_ti2t ok33a ok33b h33).
Qed.

(* SOLVED IMPLIES COORDINATES SOLVED -- what makes the cheap test sound *)
Lemma issolved_eq a : tabi_ok 47 a ->
  eq_tabi 47 a (id_tabi 47) -> issolved (init3 a).
Proof.
move=> aok; rewrite (eq_tabiE n47_small aok tabi_ok_idi) => /eqP hti.
by rewrite (init3_ti2t aok tabi_ok_idi hti); vm_compute.
Qed.

(* and so the cheap test in front changes nothing *)
Lemma solved_stepE a : tabi_ok 47 a ->
  (if issolved (init3 a) then eq_tabif a (id_tabi 47) else false)
  = eq_tabi 47 a (id_tabi 47).
Proof.
move=> aok; rewrite eq_tabifE.
(* boolP SUBSTITUTES, so the false branch has no eq_tabi left to rewrite *)
case: (boolP (eq_tabi 47 a (id_tabi 47))) => h.
  by rewrite (issolved_eq aok h).
by case: (issolved _).
Qed.

(* one move of the path, by foldr's own equation -- this is what the `rev'
   was breaking *)
Lemma rebuild_cons a0 k path :
  rebuild a0 (k :: path) = comp_tabi 47 (rebuild a0 path) (PArray.get mtisa k).
Proof. by []. Qed.

(* =========================================================================  *)
(*  searchz3m = searchz3.  A PURE REORDERING, so no invariant is needed:      *)
(*  searchz3m carries the table and tests eq_tabi against it directly.        *)
(*  (searchz3n, which carries the path instead, additionally needs x aligned  *)
(*  with the table -- step3_init -- and so drags in fsmoveC, cubti and twP3.) *)
(* =========================================================================  *)

(* the depth, one step down, on the int side *)
Lemma of_natS_sub d : (d.+1 <= 63)%N ->
  Uint63.sub (of_nat d.+1) 1%uint63 = of_nat d.
Proof.
move=> dL.
have hs : (d.+1 < nwB)%N by apply: small_nwB.
have hd : (d < nwB)%N by apply: small_nwB; apply: ltnW.
apply/to_nat_inj; rewrite to_nat_sub ?to_nat_1 ?of_natK ?subn1 //.
Qed.

(* one unfolding, in the shape searchz3S has for searchz3.  The && here is in
   the SPECIFICATION, where only the value matters; the code keeps its nested
   ifs, because andb is strict and would run the recursive call even when the
   guard fails.

   x is destructured and stepv is used rather than step3i, so that both sides
   are the SAME TERMS and not merely convertible -- otherwise `/=' unfolds
   step3i on one side only and nothing matches. *)
Lemma searchz3mS T d di a x0 x1 x2 p : (d.+1 <= 63)%N -> di = of_nat d.+1 ->
  searchz3m T d.+1 di a (x0, x1, x2) p =
  (h3 T (x0, x1, x2) <= d.+1)%N &&
  (eq_tabi 47 a (id_tabi 47) ||
   has (fun m =>
          let: (mm, pk) := m in
          let: ((k, ka), kb) := mm in
          (if hv1le T (stepv x0 k) (Uint63.sub di 1%uint63)
           then if hv1le T (stepv x1 ka) (Uint63.sub di 1%uint63)
                then hv1le T (stepv x2 kb) (Uint63.sub di 1%uint63)
                else false
           else false) &&
          searchz3m T d (Uint63.sub di 1%uint63)
                    (comp_tabi 47 a (PArray.get mtisa k))
                    (stepv x0 k, stepv x1 ka, stepv x2 kb) pk)
       (nth [::] allowed3 p)).
Proof.
move=> dL ->; rewrite {1}/searchz3m -/searchz3m.
rewrite h3leE (h3iE T (x0, x1, x2) dL) eq_tabifE.
case: (h3 T (x0, x1, x2) <= d.+1)%N => //=.
case: (eq_tabi 47 a (id_tabi 47)) => //=.
elim: (nth [::] allowed3 p) => [|[[[k ka] kb] pk] l IH] //=.
(* no `//=' on these: it partially reduces one side and the two stop
   matching syntactically *)
case: (hv1le _ _ _); last by rewrite IH.
case: (hv1le _ _ _); last by rewrite IH.
case: (hv1le _ _ _); last by rewrite IH.
by case: (searchz3m _ _ _ _ _ _); rewrite ?IH.
Qed.

(* searchz3 tests the heuristic first thing, so conjoining that test in front
   of it changes nothing *)
(* stated with the NAT test: `rewrite /searchz3' cannot unfold a fixpoint
   whose decreasing argument is a variable, so d is cased and the successor
   case goes through searchz3S. *)
Lemma test_and_searchz3 T d A X P : (d <= 63)%N ->
  (((h3 T X) <= d)%N && searchz3 T d A X P) = searchz3 T d A X P.
Proof.
move=> dL; apply: andb_idl.
case: d dL => [|d'] dL.
  rewrite /searchz3 (h3iE T X dL) => hs.
  by move: hs; case: (h3 T X <= 0)%N.
by rewrite (searchz3S T A X P dL) => /andP[hh _].
Qed.

(* h3le on a literal triple, folded back *)
Lemma h3le_split T y0 y1 y2 dj :
  (if hv1le T y0 dj then if hv1le T y1 dj then hv1le T y2 dj else false
   else false) = (h3i T (y0, y1, y2) <=? dj)%uint63.
Proof. by rewrite -h3leE. Qed.

Lemma searchz3mE T d : (d <= 63)%N -> forall di a x p, (p < 7)%N ->
  di = of_nat d -> searchz3m T d di a x p = searchz3 T d a x p.
Proof.
elim: d => [|d IH] dL di a [[x0 x1] x2] p pL ->.
  rewrite /searchz3m /searchz3 h3leE eq_tabifE.
  by case: (h3i T _ <=? _)%uint63.
rewrite (searchz3mS T a x0 x1 x2 p dL erefl) (searchz3S T a (x0, x1, x2) p dL).
congr (_ && _); congr (_ || _).
rewrite (allowed3E pL) has_map.
apply: eq_in_has => k hk.
have kL : (k < 18)%N.
  by move: hk; rewrite mem_filter mem_iota size_mtis => /andP[_ /andP[_ ]].
have pkL : (fcpos k < 7)%N by rewrite /fcpos ltn_divLR // (leq_trans kL).
have sv : forall v j, stepv v (of_nat j) = (acttwi v.1 j, actfsr v.2 j).
  by move=> v j; rewrite /stepv acttwiiE actfsriE.
rewrite /preim /= (of_natS_sub dL) (mtisaE kL) !sv.
rewrite (IH (ltnW dL) _ _ _ _ pkL erefl).
(* [X in X && _] IS NOT TIDINESS.  Left to search the whole goal, rewrite
   walks into the two searchz3 terms and does not return -- MEASURED, it ran
   past 240 s where the restricted form takes 1.7 s. *)
rewrite [X in X && _]h3le_split [X in X && _](h3iE T _ (ltnW dL)).
exact: test_and_searchz3 (ltnW dL).
Qed.

(* =========================================================================  *)
(*  searchz3n = searchz3m: THE ONE STEP THAT IS NOT A REORDERING              *)
(*                                                                            *)
(*  searchz3n drops the maintained table, keeps the move path, and tests the  *)
(*  COORDINATES for solvedness, rebuilding the table only when they say it    *)
(*  might be.  Sound because solved implies coordinates solved (issolved_eq), *)
(*  and that needs the coordinates carried to be the table's own --           *)
(*  x = init3 a, kept along the descent by step3_init.  Which is why fsmoveC  *)
(*  appears here and nowhere above.                                          *)
(* =========================================================================  *)

(* one unfolding, searchz3mS's shape with the path in place of the table *)
Lemma searchz3nS T d di a0 path x0 x1 x2 p :
  (d.+1 <= 63)%N -> di = of_nat d.+1 ->
  searchz3n T d.+1 di a0 path (x0, x1, x2) p =
  (h3 T (x0, x1, x2) <= d.+1)%N &&
  ((if issolved (x0, x1, x2)
    then eq_tabi 47 (rebuild a0 path) (id_tabi 47) else false) ||
   has (fun m =>
          let: (mm, pk) := m in
          let: ((k, ka), kb) := mm in
          (if hv1le T (stepv x0 k) (Uint63.sub di 1%uint63)
           then if hv1le T (stepv x1 ka) (Uint63.sub di 1%uint63)
                then hv1le T (stepv x2 kb) (Uint63.sub di 1%uint63)
                else false
           else false) &&
          searchz3n T d (Uint63.sub di 1%uint63) a0 (k :: path)
                    (stepv x0 k, stepv x1 ka, stepv x2 kb) pk)
       (nth [::] allowed3 p)).
Proof.
move=> dL ->; rewrite {1}/searchz3n -/searchz3n.
rewrite h3leE (h3iE T (x0, x1, x2) dL) eq_tabifE.
case: (h3 T (x0, x1, x2) <= d.+1)%N => //=.
case: (if issolved (x0, x1, x2)
       then eq_tabi 47 (rebuild a0 path) (id_tabi 47) else false) => //=.
elim: (nth [::] allowed3 p) => [|[[[k ka] kb] pk] l IH] //=.
case: (hv1le _ _ _); last by rewrite IH.
case: (hv1le _ _ _); last by rewrite IH.
case: (hv1le _ _ _); last by rewrite IH.
by case: (searchz3n _ _ _ _ _ _ _); rewrite ?IH.
Qed.

(* the invariant is x = init3 (rebuild a0 path): the coordinates carried are
   the ones of the table the path rebuilds.  step3_init is what keeps it, and
   solved_stepE is what turns the cheap test back into eq_tabi. *)
Lemma searchz3nmE T d : (d <= 63)%N -> fsmoveC ->
  forall di a0 path x0 x1 x2 p, di = of_nat d -> (p < 7)%N ->
  tabi_ok 47 (rebuild a0 path) -> cubti (rebuild a0 path) ->
  twP3 (rebuild a0 path) -> (x0, x1, x2) = init3 (rebuild a0 path) ->
  searchz3n T d di a0 path (x0, x1, x2) p
  = searchz3m T d di (rebuild a0 path) (x0, x1, x2) p.
Proof.
move=> dL hc.
(* fsmoveC INSTANTIATED ONCE AND THEN CLEARED.  With it in the context every
   trailing `done' unifies its goal against it and unfolds an all_pow at
   ncoord = 24; Farp1's step3_init clears it for exactly this reason. *)
have si := fun a k => @step3_init a k hc.
clear hc; move: dL.
elim: d => [|d IH] dL di a0 path x0 x1 x2 p -> pL aok ca tw hx.
  rewrite /searchz3n /searchz3m hx (solved_stepE aok) eq_tabifE.
  exact: refl_equal.
have dL' : (d <= 63)%N := ltnW dL.
rewrite (searchz3nS T a0 path x0 x1 x2 p dL erefl).
rewrite (searchz3mS T (rebuild a0 path) x0 x1 x2 p dL erefl).
(* the cheap test in front, removed once and for all -- as a `have', because
   (x0, x1, x2) occurs in h3 as well and a bare rewrite hits that one first *)
have hs : (if issolved (x0, x1, x2)
           then eq_tabi 47 (rebuild a0 path) (id_tabi 47) else false)
        = eq_tabi 47 (rebuild a0 path) (id_tabi 47).
  rewrite hx -eq_tabifE (solved_stepE aok) eq_tabifE; exact: refl_equal.
rewrite hs.
congr (_ && _); congr (_ || _).
rewrite (allowed3E pL) !has_map.
apply: eq_in_has => k hk.
have kL : (k < 18)%N.
  by move: hk; rewrite mem_filter mem_iota size_mtis => /andP[_ /andP[_ ]].
have pkL : (fcpos k < 7)%N by rewrite /fcpos ltn_divLR // (leq_trans kL).
have mtok : tabi_ok 47 (nth (id_tabi 47) mtis k).
  apply: (all_nthP (id_tabi 47) mtis_ok); rewrite size_mtis; exact: kL.
(* the path one move longer IS the table one move on, mtisaE apart *)
have hr : rebuild a0 (of_nat k :: path)
        = comp_tabi 47 (rebuild a0 path) (nth (id_tabi 47) mtis k).
  by rewrite rebuild_cons (mtisaE kL).
have Aok : tabi_ok 47 (rebuild a0 (of_nat k :: path)).
  by rewrite hr; apply: (tabi_ok_comp n47_small n47_len).
have cA : cubti (rebuild a0 (of_nat k :: path)).
  rewrite hr; apply: cubti_comp;
    [rewrite size_mtis; exact: kL | exact: aok | exact: ca].
have twA : twP3 (rebuild a0 (of_nat k :: path)).
  by rewrite hr; exact: twP3_step aok ca tw kL.
have sv : forall v j, stepv v (of_nat j) = (acttwi v.1 j, actfsr v.2 j).
  by move=> v j; rewrite /stepv acttwiiE actfsriE.
(* THE INVARIANT, one move on: step3_init read right to left *)
have hy : (stepv x0 (of_nat k), stepv x1 (of_nat (nth 0%N mv3a k)),
           stepv x2 (of_nat (nth 0%N mv3b k)))
        = init3 (rebuild a0 (of_nat k :: path)).
  rewrite hr -(si _ _ aok ca tw kL) -hx !sv; exact: refl_equal.
rewrite /preim /= (of_natS_sub dL).
congr (_ && _).
rewrite (IH dL' (of_nat d) a0 (of_nat k :: path) _ _ _ (fcpos k)
            erefl pkL Aok cA twA hy) hr (mtisaE kL).
exact: refl_equal.
Qed.

(* THE BRIDGE, no longer admitted *)
Lemma searchz3nE T d a p : (d <= 63)%N -> fsmoveC -> (p < 7)%N ->
  tabi_ok 47 a -> cubti a -> twP3 a ->
  searchz3n T d (of_nat d) a [::] (init3 a) p = searchz3 T d a (init3 a) p.
Proof.
move=> dL hc pL aok ca tw.
(* the triple has to be a LITERAL pair for searchz3nmE, whose statement
   destructures it *)
case E : (init3 a) => [[y0 y1] y2].
(* EVERY ARGUMENT GIVEN.  Left implicit, a0 and path come from unifying
   `rebuild ?a0 ?path' with `a' -- higher order, and it does not return:
   MEASURED, over 120 s against 9 ms. *)
rewrite (@searchz3nmE T d dL hc (of_nat d) a [::] y0 y1 y2 p erefl
                      pL aok ca tw (esym E)).
exact: (@searchz3mE T d dL (of_nat d) (rebuild a [::]) (y0, y1, y2) p pL erefl).
Qed.

(* the shape the generated Runp1_NN.v files need: apply this and cast the
   searchz3n statement.  Stated as an implication rather than an equation so
   the generated proof is one `apply' and no rewriting under a binder. *)
Lemma p1searchd_bridge T d j : (d <= 63)%N -> (j < nmoves)%N -> fsmoveC ->
  all (fun i => ~~ searchz3n T d (of_nat d) (prefixi i j) [::]
                             (init3 (prefixi i j)) nfcube) (iota 0 nroot) ->
  all (fun i => ~~ searchz3 T d (prefixi i j)
                            (init3 (prefixi i j)) nfcube) (iota 0 nroot).
Proof.
move=> dL jL hc.
(* same reason as above: fsmoveC used once, then out of the context *)
have sn : forall a, tabi_ok 47 a -> cubti a -> twP3 a ->
    searchz3n T d (of_nat d) a [::] (init3 a) nfcube
    = searchz3 T d a (init3 a) nfcube
  := fun a aok ca tw => @searchz3nE T d a nfcube dL hc isT aok ca tw.
clear hc => h; apply/allP => i hi.
have iL : (i < nroot)%N.
  by move: hi; rewrite mem_iota add0n => /andP[_].
have iL' : (i < nmoves)%N := leq_trans iL (isT : (nroot <= nmoves)%N).
have hn := allP h i hi.
rewrite -(sn _ (prefixi_ok iL' jL) (prefixi_cub iL' jL)
               (prefixi_twP3 iL' jL)).
exact: hn.
Qed.
