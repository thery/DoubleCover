(* =========================================================================  *)
(*  FastP.v                                                                   *)
(*                                                                            *)
(*  The proofs about Fast.v.  SEPARATE FILE ON PURPOSE: rocq-mcp cannot       *)
(*  elaborate Fast.v past `allowed3' -- a Definition whose body is an         *)
(*  `Eval vm_compute in' over allowedr -- and everything after it is then     *)
(*  invisible to the session.  Loading Fast.vo works, so putting the proofs   *)
(*  here makes them developable interactively.                                *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Cyc Ball Table Search Tsearch Tabi Rubik333 Sym Root Coord
        Coordfs Coordfsi Fstab FsTable Diameter Moves
        Searchr Redun Searchir P1Small P1Ts P1Fs P1Fsm Phase1 Far Fsparity
        Farp1 Fast.

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

Lemma searchz3mE T d : (d <= 63)%N -> forall di a x p, (p < 7)%N ->
  di = of_nat d -> searchz3m T d di a x p = searchz3 T d a x p.
Proof.
Admitted.

(* =========================================================================  *)
(*  THE BRIDGE, ADMITTED                                                      *)
(*                                                                            *)
(*  Everything above is a reordering of searchz3 except the last step, which  *)
(*  trades the maintained table for the move path.  None of it changes the    *)
(*  tree or the answer, and FastBench checks that on a real piece -- but that *)
(*  is a check, not a proof.                                                  *)
(*                                                                            *)
(*  ADMITTED DELIBERATELY so the chain can be RUN and timed.  Anything built  *)
(*  on it inherits the admit; `Print Assumptions' will say so.                *)
(*                                                                            *)
(*  To discharge it: mtisaE, allowed3E, step3iE, h3leE, eq_tabifE, then an    *)
(*  induction on d.  The first five are reorderings; the path step needs      *)
(*  `solved -> coordinates solved', which is what issolved filters on.        *)
(* =========================================================================  *)
Lemma searchz3nE T d a p :
  searchz3n T d (of_nat d) a [::] (init3 a) p = searchz3 T d a (init3 a) p.
Admitted.

(* the shape the generated Runp1_NN.v files need: apply this, discharge the
   `di = of_nat d' side condition by vm_compute, and cast the searchz3n
   statement.  Stated as an implication rather than an equation so the
   generated proof is one `apply' and no rewriting under a binder. *)
Lemma p1searchd_bridge T d di j :
  di = of_nat d ->
  all (fun i => ~~ searchz3n T d di (prefixi i j) [::]
                             (init3 (prefixi i j)) nfcube) (iota 0 nroot) ->
  all (fun i => ~~ searchz3 T d (prefixi i j)
                            (init3 (prefixi i j)) nfcube) (iota 0 nroot).
Proof.
move=> -> h; apply/allP => i hi.
have /allP/(_ i hi) := h.
by rewrite searchz3nE.
Qed.
