(* =========================================================================  *)
(*  HSound.v -- obligation E: what the run computed, as a statement about     *)
(*     maneuvers.                                                             *)
(* =========================================================================  *)

(* The seventy two HRun files say the same thing seventy two times: for one of*)
(* Reid's six positions and one of the 120 pairs of turns the search may play *)
(* first, hsearch came back false.  HBound.targ_far asks for something else,  *)
(*                                                                            *)
(*   forall k v, k < size rpfx -> qw v -> okw 0 v ->                          *)
(*     size (nth [::] rpfx k) + size v <= 24 ->                               *)
(*       wp (nth [::] rpfx k ++ v) != targ                                    *)
(*                                                                            *)
(* -- no word the rule accepts finishes the prefix.  Between the two there are*)
(* four steps, and this file holds the first of them, the one that needs no   *)
(* table at all: a word the rule accepts starts with one of the 120 pairs, so *)
(* the 120 jobs between them cover every word.  The other three are           *)
(*                                                                            *)
(*   the state the search carries IS the triple of the position it stands at  *)
(*     -- obligation C, HAgree;                                               *)
(*   the score it cuts on never exceeds the distance -- obligation D, HAdmis, *)
(*     whose h_cut is exactly what a cut needs;                               *)
(*   the fold reads back what the flat table holds.                           *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Ball Moves Coordfs Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the rule along a word ----------------------------------------------  *)

(* the class a word leaves the rule in                                        *)
Definition hclassw (p : nat) (w : seq nat) : nat := foldl hclass p w.

Lemma hclassw_cat p u v : hclassw p (u ++ v) = hclassw (hclassw p u) v.
Proof. by rewrite /hclassw foldl_cat. Qed.

Lemma okw_cat p u v : okw p (u ++ v) = okw p u && okw (hclassw p u) v.
Proof. by elim: u p => [|m u ih] p //=; rewrite -andbA ih. Qed.

(* ---- every accepted word starts with one of the 120 pairs ---------------  *)

(* The first turn is free and the second is whatever the rule allows after it,*)
(* which is how hpres was built, so this is a check over the 144 pairs.       *)
Lemma okw2_hpres :
  all (fun m1 => all (fun m2 => okw 0 [:: m1; m2] ==> ([:: m1; m2] \in hpres))
                     (iota 0 nq))
      (iota 0 nq).
Proof. by vm_compute. Qed.

(* so a word of at least two turns is one of the 120 jobs and a tail the rule *)
(* accepts from where the pair leaves it                                      *)
Lemma okw_hpres (m1 m2 : nat) (v : seq nat) :
  qw [:: m1, m2 & v] -> okw 0 [:: m1, m2 & v] ->
  ([:: m1; m2] \in hpres) /\ okw (hclassw 0 [:: m1; m2]) v.
Proof.
move=> /and3P[m1L m2L _] ow.
have /andP[ot ov] : okw 0 [:: m1; m2] && okw (hclassw 0 [:: m1; m2]) v.
  by rewrite -okw_cat; exact: ow.
split=> //.
have /implyP := allP (allP okw2_hpres _ (mem_iota0 m1L)) _ (mem_iota0 m2L).
by apply.
Qed.

(* ---- and the twelve jobs cover the 120 prefixes -------------------------- *)

(* The run deals the prefixes round robin over twelve jobs, so what has to be *)
(* true is that every one of them is dealt to somebody.                       *)
Lemma hslice_tab : all (fun w => has (fun j => w \in hslice j 12) (iota 0 12))
                       hpres.
Proof. by vm_compute. Qed.

Lemma hslice_mem (w : seq nat) : w \in hpres ->
  exists2 j, (j < 12)%N & w \in hslice j 12.
Proof.
move=> wp.
have /hasP[j jI wj] := allP hslice_tab _ wp.
by exists j => //; move: jI; rewrite mem_iota.
Qed.

(* ---- where the rule first refuses ---------------------------------------- *)

(* The rewriting needs a place to work at: the first letter the rule turns    *)
(* down, with everything before it accepted.  Then HCanon.bad_case says which *)
(* of the three rewrites applies there.                                       *)
Lemma okw_bad (w : seq nat) p : ~~ okw p w ->
  exists u m v, [/\ w = u ++ m :: v, okw p u & ~~ allowedq (hclassw p u) m].
Proof.
elim: w p => [|a w ih] p //=.
rewrite negb_and => /orP[ap|ow].
  by exists [::], a, w.
have [u [m [v [wE ou am]]]] := ih _ ow.
have [ap|ap] := boolP (allowedq p a); last by exists [::], a, w.
exists (a :: u), m, v; split => //=; first by rewrite wE.
by rewrite ap.
Qed.

(* ---- the class along a word ---------------------------------------------- *)

(* Three things bad_case wants of the class at that place: that it is not the *)
(* starting class, that it is a class at all, and that the turn it names is   *)
(* the letter just before.                                                    *)
Lemma hclass_gt0 p m : (0 < hclass p m)%N.
Proof. by rewrite /hclass; do ! case: ifP => _. Qed.

Lemma hclassw_gt0 p u : u != [::] -> (0 < hclassw p u)%N.
Proof.
case/lastP: u => // u a _.
by rewrite -cats1 /hclassw foldl_cat /= hclass_gt0.
Qed.

Lemma hclassw_lt p u : qw u -> okw p u -> (p < nclass)%N ->
  (hclassw p u < nclass)%N.
Proof.
elim: u p => [|a u ih] p //=; rewrite /qw /= => /andP[aL uq] /andP[ap ou] pL.
by apply: ih => //; have [h _ _ _] := hclass_ok pL aL ap.
Qed.

Lemma hclassw_last p u : u != [::] -> qw u -> okw p u -> (p < nclass)%N ->
  plast (hclassw p u) = last 0%N u.
Proof.
case/lastP: u => // u a _.
rewrite -cats1 /qw all_cat => /andP[uq]; rewrite /= andbT => aL.
rewrite okw_cat => /andP[ou]; rewrite /= andbT => aa pL.
rewrite /hclassw foldl_cat last_cat /=.
by have [_ -> _ _] := hclass_ok (hclassw_lt uq ou pL) aL aa.
Qed.

(* ---- run two ------------------------------------------------------------- *)

(* A run of two is two of the SAME turn, and that is what says the letter     *)
(* before the pair is the same again -- which is what the collapse needs.     *)
Lemma prun2_tab :
  all (fun p => all (fun m => allowedq p m ==> (prun (hclass p m) == 2)%N ==>
        ((0 < p)%N && (m == plast p))) (iota 0 nq)) (iota 0 nclass).
Proof. by vm_compute. Qed.

Lemma prun2_last p u a : qw u -> okw p u -> (p < nclass)%N -> (a < nq)%N ->
  allowedq (hclassw p u) a -> prun (hclass (hclassw p u) a) = 2%N ->
  (0 < hclassw p u)%N /\ a = plast (hclassw p u).
Proof.
move=> uq ou pL aL aa h2.
have cL := hclassw_lt uq ou pL.
have /implyP/(_ aa)/implyP/(_ (introT eqP h2))/andP[h1 /eqP h3] :=
  allP (allP prun2_tab _ (mem_iota0 cL)) _ (mem_iota0 aL).
by split.
Qed.

(* ---- the three rewrites, each on the word it works at -------------------- *)

Lemma qw_cat u v : qw (u ++ v) = qw u && qw v.
Proof. by rewrite /qw all_cat. Qed.

Lemma qw_cons m u : qw (m :: u) = ((m < nq)%N && qw u).
Proof. by []. Qed.

Lemma step_swap (u v : seq nat) a m : (a < nq)%N -> (m < nq)%N -> ohi a m ->
  [/\ wp (u ++ m :: a :: v) = wp (u ++ a :: m :: v),
      seq.size (u ++ m :: a :: v) = seq.size (u ++ a :: m :: v) &
      (phi (u ++ m :: a :: v) < phi (u ++ a :: m :: v))%N].
Proof.
move=> aL mL am; split.
- by apply: man_swap => //; move: am; rewrite /ohi => /andP[].
- by rewrite !size_cat.
by rewrite (phi_swap u v am).
Qed.

Lemma step_cancel (u v : seq nat) a m : (a < nq)%N -> (m < nq)%N ->
  fce m = fce a -> m != a ->
  [/\ wp (u ++ v) = wp (u ++ a :: m :: v),
      (seq.size (u ++ v)).+2 = seq.size (u ++ a :: m :: v) &
      (phi (u ++ v) <= phi (u ++ a :: m :: v))%N].
Proof.
move=> aL mL fam ma; split.
- rewrite wp_pair (qinv_same aL mL fam ma) qmv_cancel // mulg1.
  by rewrite wp_cat.
- by rewrite !size_cat /= addnS addnS.
apply: leq_trans (phi_del u v m) _.
by apply: (phi_del u (m :: v) a).
Qed.

Lemma step_run3 (u v : seq nat) a : (a < nq)%N ->
  [/\ wp (u ++ qinv a :: v) = wp (u ++ a :: a :: a :: v),
      (seq.size (u ++ qinv a :: v)).+2 = seq.size (u ++ a :: a :: a :: v) &
      (phi (u ++ qinv a :: v) <= phi (u ++ a :: a :: a :: v))%N].
Proof.
move=> aL; split.
- by rewrite wp_triple qmv_cube // wp_cat wp_cons mulgA.
- by rewrite !size_cat /= !addnS.
rewrite (phi_fce u v (fce_qinv aL)).
apply: leq_trans (phi_del u (a :: v) a) _.
by apply: (phi_del u (a :: a :: v) a).
Qed.

(* The collapse asks for the letter before the pair, so it is stated on the   *)
(* word rather than on a place in it: three of a face, and out comes one.     *)
Lemma step_run3_word (u v : seq nat) a : qw u -> qw v -> u != [::] ->
  a = last 0%N u -> (a < nq)%N ->
  exists w2, [/\ qw w2, wp w2 = wp (u ++ a :: a :: v),
      (seq.size w2).+2 = seq.size (u ++ a :: a :: v) &
      (phi w2 <= phi (u ++ a :: a :: v))%N].
Proof.
case/lastP: u => [_|u2 b] //; rewrite last_rcons -cats1 => uq vq _ ba aL.
rewrite -ba -catA /=.
have [h1 h2 h3] := step_run3 u2 v aL.
exists (u2 ++ qinv a :: v); split => //.
rewrite qw_cat qw_cons qinv_lt //= vq andbT.
by move: uq; rewrite qw_cat => /andP[].
Qed.

(* ---- OBLIGATION B -------------------------------------------------------- *)

(* Every word is matched by one the rule accepts, no longer.  While the rule  *)
(* refuses somewhere, rewrite at the first place it does: okw_bad says where, *)
(* bad_case says which of the three, and each of them drops size + phi -- a   *)
(* cancel and a collapse by two in the size, a swap by one in phi.            *)
Lemma canon_le n w : (seq.size w + phi w <= n)%N -> qw w ->
  exists w', [/\ qw w', wp w' = wp w, (seq.size w' <= seq.size w)%N & okw 0 w'].
Proof.
elim: n w => [|n ih] w wn wq.
  have /size0nil wE : seq.size w = 0%N.
    by move: wn; rewrite leqn0 addn_eq0 => /andP[/eqP].
  by exists [::]; rewrite wE.
have [ow|now] := boolP (okw 0 w); first by exists w.
have [u [m [v [wE ou am]]]] := okw_bad now.
have mL : (m < nq)%N by move: wq; rewrite wE qw_cat qw_cons => /andP[_ /andP[]].
have vq : qw v by move: wq; rewrite wE qw_cat qw_cons => /andP[_ /andP[_]].
case/lastP: u wE ou am => [|u1 a] wE ou am.
  by move: am; rewrite /allowedq /hclassw.
have uq : qw (rcons u1 a) by move: wq; rewrite wE qw_cat => /andP[].
have u1q : qw u1 by move: uq; rewrite -cats1 qw_cat => /andP[].
have aL : (a < nq)%N.
  by move: uq; rewrite -cats1 qw_cat qw_cons andbT => /andP[_].
have ou1 : okw 0 u1 by move: ou; rewrite -cats1 okw_cat => /andP[].
have p1L : (hclassw 0 u1 < nclass)%N by apply: hclassw_lt.
have aa : allowedq (hclassw 0 u1) a.
  by move: ou; rewrite -cats1 okw_cat /= andbT => /andP[_].
have hcE : hclassw 0 (rcons u1 a) = hclass (hclassw 0 u1) a.
  by rewrite -cats1 hclassw_cat.
have [pL aE _ _] := hclass_ok p1L aL aa.
have wE2 : w = u1 ++ a :: m :: v by rewrite wE -cats1 -catA.
move: am; rewrite hcE => am.
have [] := bad_case (hclass_gt0 (hclassw 0 u1) a) pL mL am; rewrite aE.
- (* the two cancel                                                           *)
  move=> [fam ma].
  have [hwp hsz hph] := step_cancel u1 v aL mL fam ma.
  have w2q : qw (u1 ++ v) by rewrite qw_cat u1q vq.
  have hn : (seq.size (u1 ++ v) + phi (u1 ++ v) <= n)%N.
    have h2 : ((seq.size (u1 ++ v) + phi (u1 ++ v)).+2 <= n.+1)%N.
      apply: leq_trans _ wn; rewrite wE2 -addSn -addSn hsz.
      by rewrite leq_add2l.
    by rewrite !ltnS in h2; apply: ltnW.
  have [w' [q' p' s' o']] := ih _ hn w2q.
  exists w'; split => //; first by rewrite p' hwp -wE2.
  apply: leq_trans s' _.
  by rewrite wE2 -hsz; apply: ltnW; apply: ltnW.
- (* three of a face collapse into one                                        *)
  move=> [maE prE].
  have [p10 aE1] := prun2_last u1q ou1 isT aL aa prE.
  have u10 : u1 != [::] by apply/eqP => uE; move: p10; rewrite uE /hclassw.
  have alast : a = last 0%N u1.
    by rewrite aE1 (hclassw_last u10 u1q ou1 isT).
  move: wE2; rewrite maE => wE2.
  have [w2 [q2 p2 s2 f2]] := step_run3_word u1q vq u10 alast aL.
  have hn : (seq.size w2 + phi w2 <= n)%N.
    have h2 : ((seq.size w2 + phi w2).+2 <= n.+1)%N.
      apply: leq_trans _ wn; rewrite wE2 -addSn -addSn s2.
      by rewrite leq_add2l.
    by rewrite !ltnS in h2; apply: ltnW.
  have [w' [q' p' s' o']] := ih _ hn q2.
  exists w'; split => //; first by rewrite p' p2 -wE2.
  apply: leq_trans s' _.
  by rewrite wE2 -s2; apply: ltnW; apply: ltnW.
(* the two opposite faces swap                                                *)
move=> hoi.
have [hwp hsz hph] := step_swap u1 v aL mL hoi.
have w2q : qw (u1 ++ m :: a :: v).
  by rewrite qw_cat !qw_cons mL aL vq !andbT.
have hn : (seq.size (u1 ++ m :: a :: v) + phi (u1 ++ m :: a :: v) <= n)%N.
  rewrite -ltnS; apply: leq_trans wn.
  by rewrite wE2 hsz ltn_add2l.
have [w' [q' p' s' o']] := ih _ hn w2q.
exists w'; split => //; first by rewrite p' hwp -wE2.
by apply: leq_trans s' _; rewrite wE2 hsz.
Qed.

(* and the hypothesis HBound.targ_far asks for                                *)
Theorem canon v : qw v ->
  exists v', [/\ qw v', wp v' = wp v, (seq.size v' <= seq.size v)%N & okw 0 v'].
Proof. by apply: (canon_le (leqnn _)). Qed.

(* ---- WHAT IS LEFT OF THE BOUND ------------------------------------------- *)

(* With B discharged, `no maneuver of 25 quarter turns' rests on Hrun alone.  *)
(* Print Assumptions targ_far_run names nothing but the int63 and PArray      *)
(* primitives.                                                                *)
Theorem targ_far_run
  (Hrun : forall k v, (k < seq.size rpfx)%N -> qw v -> okw 0 v ->
     (seq.size (nth [::] rpfx k) + seq.size v <= 24)%N ->
     wp (nth [::] rpfx k ++ v) != targ) :
  targ \notin ball Sq 25.
Proof. by apply: targ_far Hrun canon. Qed.

(* And Hrun is where the run has to be read as a statement about maneuvers.   *)
(* okw_hpres and hslice_tab do the cutting up; what is left is the search     *)
(* itself -- that a false means no accepted word of that length solves --     *)
(* which needs obligation C (HAgree), obligation D (HAdmis, whose h_cut is    *)
(* the form a cut needs, and HSweep for the sweep under it) and the fold read *)
(* back as the flat table.                                                    *)

(* ---- the words the run never searches ------------------------------------ *)

(* Different tables, different permutations.  Table.v does not say it, and    *)
(* the short words below are settled by a table, so it is needed here.        *)
Lemma pt_tab_inj t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  pt flast t1 = pt flast t2 -> t1 = t2.
Proof.
move=> ok1 ok2 hp.
have /and3P[/eqP s1 _ _] := ok1.
have /and3P[/eqP s2 _ _] := ok2.
apply: (@eq_from_nth _ 0%N); first by rewrite s1 s2.
move=> i iL; rewrite s1 in iL.
have := f_equal (fun s : {perm facelet} => s (inord i)) hp.
rewrite !ptE // => h.
have h2 : nth 0 t1 (inord i : facelet) = nth 0 t2 (inord i : facelet).
  rewrite -(inordK (tab_lt (inord i) ok1)) -(inordK (tab_lt (inord i) ok2)).
  by rewrite h.
by move: h2; rewrite inordK.
Qed.

Lemma targ_tab_ok : tab_ok flast (ti2t flast targeti).
Proof. by vm_compute. Qed.

Lemma wp_neq_targ w : qw w -> wtr w != ti2t flast targeti -> wp w != targ.
Proof.
move=> wq hne; apply/eqP => hw.
case/eqP: hne; apply: pt_tab_inj (targ_tab_ok) _; first by apply: wtr_ok.
by rewrite -wp_wtr.
Qed.

Lemma rpfx_qw : all qw rpfx.
Proof. by vm_compute. Qed.

(* THE RUN SEARCHES NOTHING SHORTER THAN TWO TURNS past a prefix, because the *)
(* jobs are cut on pairs.  So a word of one turn or none needs its own        *)
(* argument, and there are only seventy eight of them.                        *)
Lemma short_tab :
  all (fun k => all (fun v => wtr (nth [::] rpfx k ++ v) != ti2t flast targeti)
        ([::] :: [seq [:: m] | m <- iota 0 nq])) (iota 0 (seq.size rpfx)).
Proof. by vm_compute. Qed.

Lemma short_no_targ k v : (k < seq.size rpfx)%N -> qw v ->
  (seq.size v <= 1)%N -> wp (nth [::] rpfx k ++ v) != targ.
Proof.
move=> kL vq vs.
have kq : qw (nth [::] rpfx k) by apply: (allP rpfx_qw); apply: mem_nth.
have ht : wtr (nth [::] rpfx k ++ v) != ti2t flast targeti.
  have h := allP short_tab _ (mem_iota0 kL).
  apply: (allP h); rewrite inE.
  case: v vq vs => [_ _|m v0]; first by rewrite eqxx.
  case: v0 => [|x l]; last by [].
  move=> /andP[mL _] _; apply/orP; right.
  by apply: map_f; apply: mem_iota0.
by apply: wp_neq_targ => //; rewrite qw_cat kq vq.
Qed.

(* ---- the statement the run files have to be read through ----------------- *)

Section RunSound.

Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

(* THE SEARCH IS SOUND WHEN IT FAILS.  hrun coming back false has to mean     *)
(* that no word the rule accepts, of the depth it was given, finishes the     *)
(* prefix.  That is what the seventy two run files are worth, and it is what  *)
(* obligations C and D are for: C says the triple the search carries is the   *)
(* triple of the position it stands at, D says the score it cuts on never     *)
(* exceeds the distance, so a cut throws no maneuver away.                    *)
Definition run_sound : Prop :=
  forall (k d : nat) (w v : seq nat),
    (k < seq.size rpfx)%N -> w \in hpres -> qw v ->
    okw (hclassw 0 w) v -> (seq.size v <= d)%N ->
    hrun mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold k w d = false ->
    wp (nth [::] rpfx k ++ w ++ v) != targ.

(* the depth each job was given: 24 less the prefix and the pair of turns the *)
(* job starts with, which is Reid's 22 and 21 counted from the position       *)
Definition hdepth (k : nat) : nat := (24 - (seq.size (nth [::] rpfx k) + 2))%N.

Lemma hdepth_val : [seq hdepth k | k <- iota 0 (seq.size rpfx)]
  = [:: 20; 19; 19; 19; 19; 19]%N.
Proof. by vm_compute. Qed.

(* THE ASSEMBLY.  Given the search sound and the run files, no word the rule  *)
(* accepts finishes a prefix -- which is targ_far's Hrun.  A word of two      *)
(* turns or more is one of the 120 prefixes and a tail, and a shorter one is  *)
(* short_no_targ.                                                             *)
Lemma Hrun_of :
  run_sound ->
  (forall k w, (k < seq.size rpfx)%N -> w \in hpres ->
     hrun mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold k w (hdepth k)
       = false) ->
  forall k v, (k < seq.size rpfx)%N -> qw v -> okw 0 v ->
    (seq.size (nth [::] rpfx k) + seq.size v <= 24)%N ->
    wp (nth [::] rpfx k ++ v) != targ.
Proof.
move=> Hs Hj k v kL vq ov hsz.
case: (leqP (seq.size v) 1) => [vs|v1]; first by apply: short_no_targ.
case: v vq ov hsz v1 => [|m1 [|m2 v']] // vq ov hsz _.
have [wp2 ov'] := okw_hpres vq ov.
apply: (Hs k (hdepth k) [:: m1; m2] v') => //.
- by move: vq; rewrite !qw_cons => /andP[_ /andP[]].
- rewrite /hdepth leq_subRL.
    rewrite -addnA [(2 + _)%N]addnC; first by move: hsz => /=; rewrite addn2.
  by apply: leq_trans hsz; rewrite leq_add2l.
by apply: Hj.
Qed.

(* and so the bound, off the search being sound and the run files alone       *)
Theorem targ_far_of :
  run_sound ->
  (forall k w, (k < seq.size rpfx)%N -> w \in hpres ->
     hrun mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold k w (hdepth k)
       = false) ->
  targ \notin ball Sq 25.
Proof. by move=> Hs Hj; apply: targ_far_run; apply: Hrun_of. Qed.

End RunSound.

(* SO ONE THING IS LEFT: run_sound, the search itself.  Everything around it  *)
(* is proved -- targ_far_of takes run_sound and the seventy two run files and *)
(* gives the bound.  run_sound is where obligations C and D are spent: C says *)
(* the triple the search carries is the triple of the position it stands at,  *)
(* D says a cut throws no maneuver away.                                      *)
