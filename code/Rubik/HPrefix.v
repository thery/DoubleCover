(* =========================================================================  *)
(*  HPrefix.v -- the prefix: playing a word is stepping the state.            *)
(* =========================================================================  *)

(* HSearch.hprefix folds hplay over the word a job starts with, carrying a    *)
(* maneuver, a state and a class.  HRunS.hsearch_sound wants the state to be  *)
(* the state of the position the maneuver rebuilds.  That is what this file   *)
(* proves, by induction on the word, off HPok's stt_step and pok_step; and    *)
(* then the run itself is read as a statement about maneuvers.                *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Sym Ball Moves Coordfs Coordfsi Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge HBound HCanon
        HSound HEdge HRunS HCorner HSweepC HGlue HPok.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- the maneuver a word leaves behind ----------------------------------- *)

(* hplay remembers a turn by pushing its index among the eighteen on the      *)
(* front of the maneuver, so this is the maneuver a whole word leaves.        *)
Definition apath (path : seq int) (w : seq nat) : seq int :=
  foldl (fun pa m => of_nat (qt18 m) :: pa) path w.

Lemma foldl_cons (T R : Type) (f : R -> T -> R) (x : R) (m : T) (w : seq T) :
  foldl f x (m :: w) = foldl f (f x m) w.
Proof. by []. Qed.

Lemma apath_cons path m w :
  apath path (m :: w) = apath (of_nat (qt18 m) :: path) w.
Proof. by []. Qed.

Lemma hclassw_cons p m w : hclassw p (m :: w) = hclassw (hclass p m) w.
Proof. by []. Qed.

Lemma aw_cat a u v : aw a (u ++ v) = aw (aw a u) v.
Proof. by rewrite /aw foldl_cat. Qed.

Lemma rebuild_nil (a0 : arr) : rebuild a0 [::] = a0.
Proof. by []. Qed.

(* the maneuver is the position: rebuilding what a word left behind is        *)
(* playing that word                                                          *)
Lemma rebuild_apath (a0 : arr) w : forall path, qw w ->
  rebuild a0 (apath path w) = aw (rebuild a0 path) w.
Proof.
elim: w => [|m w ih] path wq; first by [].
move: wq; rewrite HSound.qw_cons => /andP[mL wq].
rewrite apath_cons (@ih _ wq) aw_cons.
by rewrite (rebuild_cons a0 path mL).
Qed.

(* and the guards survive a whole word                                        *)
Lemma pok_apath (a0 : arr) w : forall path, qw w -> pok (rebuild a0 path) ->
  pok (rebuild a0 (apath path w)).
Proof.
elim: w => [|m w ih] path wq pk; first by [].
move: wq; rewrite HSound.qw_cons => /andP[mL wq].
have pk' : pok (rebuild a0 (of_nat (qt18 m) :: path)).
  by rewrite (rebuild_cons a0 path mL); apply: (pok_step pk mL).
by rewrite apath_cons; apply: (@ih _ wq pk').
Qed.

Section Root.

Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

Local Notation stp := (stepa mt_e mt_cl mt_ct).
Local Notation hply := (hplay mt_e mt_cl mt_ct).
Local Notation hpfx := (hprefix mt_e mt_cl mt_ct).
Local Notation hsrch :=
  (hsearch mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold).
Local Notation hrn := (hrun mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold).

(* the three sweeps, which is what makes the tables the tables                *)
Hypothesis Hse : sweep_e mt_e.
Hypothesis Hscl : sweep_cl mt_cl.
Hypothesis Hsct : sweep_ct mt_ct.

(* ---- one turn played ----------------------------------------------------- *)

(* hplay on a state written out: the turn it reads out of amoves is the turn  *)
(* seen from the three axes.                                                  *)
Lemma hplayE path x0 x1 x2 p m : (m < nq)%N ->
  hply (path, (x0, x1, x2), p) m =
  (of_nat (qt18 m) :: path,
   (stp x0 (of_nat (cmv 0 m)), stp x1 (of_nat (cmv 1 m)),
    stp x2 (of_nat (cmv 2 m))), hclass p m).
Proof. by move=> mL; rewrite /hplay (amoves_nth mL). Qed.

(* playing a turn on the state of a position is the state of the position     *)
(* with that turn played on it                                                *)
Lemma hplay_stt (a0 : arr) path p m : (m < nq)%N -> pok (rebuild a0 path) ->
  hply (path, stt (rebuild a0 path), p) m =
  (of_nat (qt18 m) :: path, stt (rebuild a0 (of_nat (qt18 m) :: path)),
   hclass p m).
Proof.
move=> mL pk.
have hst := stt_step Hse Hscl Hsct pk mL.
have hr := rebuild_cons a0 path mL.
rewrite hr hst.
by case: (stt (rebuild a0 path)) => [[y0 y1] y2]; rewrite (hplayE _ _ _ _ _ mL).
Qed.

(* ---- a whole word played ------------------------------------------------- *)

(* THE PREFIX.  Folding hplay over a word leaves the maneuver the word wrote, *)
(* the state of the position that maneuver rebuilds, and the class the rule   *)
(* is left in.                                                                *)
Lemma hplay_fold (a0 : arr) w : forall path p, qw w -> pok (rebuild a0 path) ->
  foldl hply (path, stt (rebuild a0 path), p) w =
  (apath path w, stt (rebuild a0 (apath path w)), hclassw p w).
Proof.
elim: w => [|m w ih] path p wq pk; first by [].
move: wq; rewrite HSound.qw_cons => /andP[mL wq].
have pk' : pok (rebuild a0 (of_nat (qt18 m) :: path)).
  by rewrite (rebuild_cons a0 path mL); apply: (pok_step pk mL).
rewrite foldl_cons (hplay_stt p mL pk) apath_cons hclassw_cons.
by apply: (@ih _ _ wq pk').
Qed.

(* the same at the root, where the run starts                                 *)
Lemma hprefix_stt k w : (k < npfx)%N -> qw w ->
  hpfx k w =
  (apath [::] w, stt (rebuild (rooti k) (apath [::] w)), hclassw 0 w).
Proof.
move=> kL wq.
have pk : pok (rooti k) by apply: (allP pok_rooti); apply: mem_iota0.
have pk0 : pok (rebuild (rooti k) [::]) by rewrite rebuild_nil.
have hf := @hplay_fold (rooti k) w [::] 0%N wq pk0.
rewrite rebuild_nil in hf.
rewrite /hprefix -(stt_rooti kL).
exact hf.
Qed.

(* ---- the run, read as a statement about maneuvers ------------------------ *)

(* everything the search needs of a cut, which is obligation D                *)
Hypothesis Hcut : forall (a : arr) (v : seq nat) (n : nat),
  pok a -> qw v -> (seq.size v <= n)%N -> (n <= 24)%N ->
  eq_tabi flast (aw a v) idi ->
  hle which fam sym_cl sym_ct hfold (stt a) (of_nat n).

(* A run coming back false says no word the rule accepts, of the depth the    *)
(* job was given, finishes the prefix at that position.                       *)
Lemma hrun_sound k w v d : (k < npfx)%N -> qw w -> qw v ->
  okw (hclassw 0 w) v -> okw 0 w -> (seq.size v <= d)%N -> (d <= 24)%N ->
  hrn k w d = false -> ~~ eq_tabi flast (aw (rooti k) (w ++ v)) idi.
Proof.
move=> kL wq vq ov ow vs dL hf.
have pk : pok (rooti k) by apply: (allP pok_rooti); apply: mem_iota0.
have pk0 : pok (rebuild (rooti k) [::]) by rewrite rebuild_nil.
have pkp : pok (rebuild (rooti k) (apath [::] w))
  by apply: (@pok_apath (rooti k) w [::] wq pk0).
have hr : rebuild (rooti k) (apath [::] w) = aw (rooti k) w.
  by rewrite (@rebuild_apath (rooti k) w [::] wq) rebuild_nil.
have pL : (hclassw 0 w < nclass)%N by apply: (hclassw_lt wq ow isT).
move: hf; rewrite /hrun (hprefix_stt kL wq) => hf.
have hcc := @hsearch_sound mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold
  pok stt (@pok_step) (@stt_step mt_e mt_cl mt_ct Hse Hscl Hsct) (@stt_sol)
  Hcut d (rooti k) (apath [::] w) v (hclassw 0 w) dL pkp vq ov pL vs hf.
rewrite hr in hcc.
by rewrite aw_cat.
Qed.

End Root.

(* ---- the maneuver the run is about --------------------------------------- *)

(* The search asks whether the rebuilt table is the identity; Reid's question *)
(* is whether the word is his position.  These are the same question, and     *)
(* what makes them the same is that HIS POSITION IS AN INVOLUTION: playing a  *)
(* word that gives the position ON the position gives the solved cube.        *)
Lemma hpres_qw : all (fun w => qw w && okw 0 w) hpres.
Proof. by vm_compute. Qed.

Lemma rpfx_pfxs : rpfx = pfxs.
Proof. by []. Qed.

Lemma targeti_ok : tabi_ok flast targeti.
Proof. by vm_compute. Qed.

Lemma targ_targ :
  comp_tab (ti2t flast targeti) (ti2t flast targeti) = id_tab flast.
Proof. by vm_compute. Qed.

(* a word of quarter turns played on a position, the two ways it is written  *)
Lemma appw_qtw (a : arr) w : appw a (qtw w) = aw a w.
Proof. by elim: w a => [//|m w ih] a /=; rewrite ih. Qed.

Lemma rooti_aw k : rooti k = aw targeti (nth [::] pfxs k).
Proof. by rewrite /rooti appw_qtw. Qed.

Lemma comp_tabA t1 t2 t3 : tab_ok flast t1 -> tab_ok flast t2 ->
  tab_ok flast t3 ->
  comp_tab (comp_tab t1 t2) t3 = comp_tab t1 (comp_tab t2 t3).
Proof.
move=> o1 o2 o3.
apply: pt_tab_inj.
- by apply: tab_ok_comp => //; apply: tab_ok_comp.
- by apply: tab_ok_comp => //; apply: tab_ok_comp.
by rewrite -!ptM ?tab_ok_comp // mulgA.
Qed.

Lemma comp_tab_idr t : tab_ok flast t -> comp_tab t (id_tab flast) = t.
Proof.
move=> tok; apply: pt_tab_inj => //; first by apply: tab_ok_comp => //;
  apply: tab_ok_id.
by rewrite -ptM ?tab_ok_id // pt1 mulg1.
Qed.

(* playing a word on a position is composing with the word's table           *)
Lemma ti2t_aw (a : arr) u : tabi_ok flast a -> qw u ->
  ti2t flast (aw a u) = comp_tab (ti2t flast a) (wtr u).
Proof.
elim: u a => [|m u ih] a aok uq.
  by symmetry; apply: (comp_tab_idr aok).
move: uq; rewrite qw_cons => /andP[mL uq].
have qok := tabi_ok_mvq mL.
rewrite aw_cons (ih _ (tabi_ok_comp n47_small n47_len aok qok) uq).
rewrite (ti2t_comp n47_small n47_len aok qok).
rewrite (eqP (allP ti2t_mvq _ (mem_iota0 mL))).
by rewrite comp_tabA //; [apply: mvt_ok | apply: wtr_ok].
Qed.

Lemma tabi_ok_aw (a : arr) u : tabi_ok flast a -> qw u ->
  tabi_ok flast (aw a u).
Proof.
elim: u a => [//|m u ih] a aok; rewrite qw_cons => /andP[mL uq].
by rewrite aw_cons; apply: ih => //;
   apply: (tabi_ok_comp n47_small n47_len aok (tabi_ok_mvq mL)).
Qed.

Section Bridge.

Variable mt_e mt_cl mt_ct : arr.
Variable which fam sym_cl sym_ct : arr.
Variable hfold : PArray.array arr.

Local Notation hrn := (hrun mt_e mt_cl mt_ct which fam sym_cl sym_ct hfold).

Hypothesis Hse : sweep_e mt_e.
Hypothesis Hscl : sweep_cl mt_cl.
Hypothesis Hsct : sweep_ct mt_ct.

Hypothesis Hcut : forall (a : arr) (v : seq nat) (n : nat),
  pok a -> qw v -> (seq.size v <= n)%N -> (n <= 24)%N ->
  eq_tabi flast (aw a v) idi ->
  hle which fam sym_cl sym_ct hfold (stt a) (of_nat n).

(* HSound.run_sound, but for a depth of at most twenty four -- which is what  *)
(* a table capped at twenty four can answer for, and what every job is given. *)
Lemma run_soundP k d w v : (k < seq.size rpfx)%N -> w \in hpres -> qw v ->
  okw (hclassw 0 w) v -> (seq.size v <= d)%N -> (d <= 24)%N ->
  hrn k w d = false -> wp (nth [::] rpfx k ++ w ++ v) != targ.
Proof.
move=> kL wh vq ov vs dL hf.
have /andP[wq ow] := allP hpres_qw _ wh.
have kL' : (k < npfx)%N by move: kL; rewrite rpfx_pfxs.
have hns := hrun_sound Hse Hscl Hsct Hcut kL' wq vq ov ow vs dL hf.
apply/negP => /eqP hwp; case/negP: hns.
have hpq : qw (nth [::] rpfx k) by apply: (allP rpfx_qw); apply: mem_nth.
have hu : qw (nth [::] rpfx k ++ w ++ v) by rewrite !qw_cat hpq wq vq.
have hwt : wtr (nth [::] rpfx k ++ w ++ v) = ti2t flast targeti.
  apply: pt_tab_inj (wtr_ok hu) targ_tab_ok _.
  by rewrite -wp_wtr // hwp.
have haw : aw (rooti k) (w ++ v) = aw targeti (nth [::] rpfx k ++ (w ++ v)).
  by rewrite rooti_aw rpfx_pfxs aw_cat.
have aok := tabi_ok_aw targeti_ok hu.
rewrite haw (eq_tabi_id n47_small n47_len aok).
by apply/eqP; rewrite (ti2t_aw targeti_ok hu) hwt; exact: targ_targ.
Qed.

(* THE HYPOTHESIS THE BOUND TAKES.  Given the seventy two run files, no word  *)
(* the rule accepts is Reid's position.  A word of one turn or none is never  *)
(* searched and is settled by HSound.short_no_targ.                           *)
Lemma HrunP (Hj : forall k w, (k < seq.size rpfx)%N -> w \in hpres ->
    hrn k w (hdepth k) = false) :
  forall k v, (k < seq.size rpfx)%N -> qw v -> okw 0 v ->
    (seq.size (nth [::] rpfx k) + seq.size v <= 24)%N ->
    wp (nth [::] rpfx k ++ v) != targ.
Proof.
move=> k v kL vq ov hsz.
case: (leqP (seq.size v) 1) => [vs|v1]; first by apply: short_no_targ.
case: v vq ov hsz v1 => [|m1 [|m2 v']] // vq ov hsz _.
have [wp2 ov'] := okw_hpres vq ov.
apply: (run_soundP (k := k) (d := hdepth k) (w := [:: m1; m2])) => //.
- by move: vq; rewrite !qw_cons => /andP[_ /andP[]].
- rewrite /hdepth leq_subRL.
    rewrite -addnA [(2 + _)%N]addnC; first by move: hsz => /=; rewrite addn2.
  by apply: leq_trans hsz; rewrite leq_add2l.
- by rewrite /hdepth leq_subr.
by apply: Hj.
Qed.

(* and with it the bound itself, on the run files and Hcut alone             *)
Lemma targ_far_runP (Hj : forall k w, (k < seq.size rpfx)%N -> w \in hpres ->
    hrn k w (hdepth k) = false) : targ \notin ball Sq 25.
Proof. by apply: targ_far_run (HrunP Hj). Qed.

End Bridge.
