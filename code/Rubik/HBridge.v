(* =========================================================================  *)
(*  HBridge.v -- from Proposition 2 to the position the run searches.         *)
(* =========================================================================  *)

(* HProp2 proves Proposition 2 for pfb, the position with fourspot turned onto*)
(* the front-back axis, and states it with the prefixes R F and R' F.  The run*)
(* searches targeti, Reid's own orientation, with Reid's own prefixes.  Two   *)
(* steps join them, and both are relabellings:                                *)
(*                                                                            *)
(*   1. the rotation Sx carries targeti to pfb, so it carries a maneuver for  *)
(*      one to a maneuver for the other, letter by letter and length for      *)
(*      length;                                                               *)
(*   2. the symmetry 6, which fixes pfb, carries R F to R B and the five kept *)
(*      turns to the five Reid keeps -- so the six sequences of prop2 and the *)
(*      six the run searches are the same six seen twice.                     *)
(*                                                                            *)
(* prop2_search below is Proposition 2 for the searched position, in Reid's   *)
(* numbering.  What is still missing for the bound is at the end of the file. *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Moves Coordfs Phase1
        HRoot HCoord HReid HProp2.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- 1. the rotation that joins the two orientations --------------------  *)

(* Sx turns the cube about the right-left axis; conjugating by it relabels the*)
(* twelve turns, and xrel is that relabelling, yrel the one going back.       *)
Definition xrelt : seq nat := Eval vm_compute in
  [seq index (conjt Sxtab (mvt m)) qtabs | m <- iota 0 nq].

Definition xrel (m : nat) : nat := nth 0%N xrelt m.

Definition yrelt : seq nat := Eval vm_compute in
  [seq index m xrelt | m <- iota 0 nq].

Definition yrel (m : nat) : nat := nth 0%N yrelt m.

Lemma Sxtab_ok : tab_ok flast Sxtab.
Proof. by vm_compute. Qed.

Lemma xrel_conj :
  all (fun m => conjt Sxtab (mvt m) == mvt (xrel m)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma xrel_lt : all (fun m => (xrel m < nq)%N) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma yrel_lt : all (fun m => (yrel m < nq)%N) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma xrelK : all (fun m => xrel (yrel m) == m) (iota 0 nq).
Proof. by vm_compute. Qed.

(* the searched position, as a permutation                                    *)
Definition targ : {perm facelet} := pt flast (ti2t flast targeti).

Lemma ttab_ok : tab_ok flast (ti2t flast targeti).
Proof. by vm_compute. Qed.

(* THE ONE CONJUGATION: turning the searched position by Sx gives the one     *)
(* Proposition 2 is proved for.                                               *)
Lemma targ_Sx : conjt Sxtab (ti2t flast targeti) = ti2t flast pfb.
Proof. by apply/eqP; vm_compute. Qed.

Definition sxp : {perm facelet} := pt flast Sxtab.

Lemma targ_J : targ ^ sxp = P.
Proof.
rewrite /targ /sxp /P (@ptJ flast _ _ ttab_ok Sxtab_ok).
by congr pt; exact: targ_Sx.
Qed.

Lemma qmv_Jx m : (m < nq)%N -> (qmv m) ^ sxp = qmv (xrel m).
Proof.
move=> mL.
have /eqP hs := allP xrel_conj _ (mem_iota0 mL).
have mrL : (xrel m < nq)%N by apply: (allP xrel_lt); exact: mem_iota0.
rewrite /sxp !qmvE // (@ptJ flast _ _ (mvt_ok mL) Sxtab_ok).
by congr pt; exact: hs.
Qed.

Lemma xrel_qw (w : seq nat) : qw w -> qw [seq xrel m | m <- w].
Proof.
move=> wq; apply/allP => k /mapP[m mw ->].
by apply: (allP xrel_lt); apply: mem_iota0; apply: (allP wq).
Qed.

Lemma yrel_qw (w : seq nat) : qw w -> qw [seq yrel m | m <- w].
Proof.
move=> wq; apply/allP => k /mapP[m mw ->].
by apply: (allP yrel_lt); apply: mem_iota0; apply: (allP wq).
Qed.

(* A REWRITE THAT DOES NOT TERMINATE, and why it is an exact instead.  The two*)
(* sides of targ_J are pt of a forty eight entry table; rewriting with it asks*)
(* for a match up to conversion on those, and it never came back.  exact takes*)
(* the same step by conversion in no time.                                    *)
Lemma man_x (w : seq nat) : qw w -> wp w = targ -> wp [seq xrel m | m <- w] = P.
Proof.
move=> wq hw.
have h : (wp w) ^ sxp = wp [seq xrel m | m <- w].
  by apply: wp_map => k kw; apply: qmv_Jx; apply: (allP wq).
rewrite -h hw; exact: targ_J.
Qed.

(* and back again, so the maneuvers of the two positions are in bijection     *)
Definition syp : {perm facelet} := pt flast (inv_tab flast Sxtab).

Lemma Sxtabi_ok : tab_ok flast (inv_tab flast Sxtab).
Proof. by vm_compute. Qed.

Lemma yrel_conj :
  all (fun m => conjt (inv_tab flast Sxtab) (mvt m) == mvt (yrel m))
      (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma qmv_Jy m : (m < nq)%N -> (qmv m) ^ syp = qmv (yrel m).
Proof.
move=> mL.
have /eqP hs := allP yrel_conj _ (mem_iota0 mL).
have mrL : (yrel m < nq)%N by apply: (allP yrel_lt); exact: mem_iota0.
rewrite /syp !qmvE // (@ptJ flast _ _ (mvt_ok mL) Sxtabi_ok).
by congr pt; exact: hs.
Qed.

Lemma P_Jy : P ^ syp = targ.
Proof.
have hs : syp = sxp^-1 by rewrite /syp /sxp ptV ?Sxtab_ok.
by rewrite hs -targ_J conjgK.
Qed.

Lemma man_y (w : seq nat) : qw w -> wp w = P -> wp [seq yrel m | m <- w] = targ.
Proof.
move=> wq hw.
have h : (wp w) ^ syp = wp [seq yrel m | m <- w].
  by apply: wp_map => k kw; apply: qmv_Jy; apply: (allP wq).
rewrite -h hw; exact: P_Jy.
Qed.

(* ---- 2. the six sequences of prop2 are the six the run searches ---------  *)

(* Reid's prefixes as words of quarter turns: R U, R' U D, R' U F', R' U R',  *)
(* R' U B', R' U L'.                                                          *)
Definition rpfx : seq (seq nat) :=
  [:: [:: 2; 0]; [:: 3; 0; 6]; [:: 3; 0; 5];
      [:: 3; 0; 3]; [:: 3; 0; 11]; [:: 3; 0; 9] ]%N.

(* the same, turned by Sx: what they look like where prop2 lives              *)
Lemma xpfxE : [seq [seq xrel m | m <- pw] | pw <- rpfx] =
  [:: [:: 2; 10]; [:: 3; 10; 4]; [:: 3; 10; 1];
      [:: 3; 10; 3]; [:: 3; 10; 7]; [:: 3; 10; 9] ]%N.
Proof. by vm_compute. Qed.

(* so the heads to look for, on that side, are R B and R' B with one of five  *)
Definition ksearch : seq nat := [:: 4; 1; 3; 7; 9]%N.

Definition sheads (w : seq nat) : bool :=
  ((nth 0%N w 0 == 2) && (nth 0%N w 1 == 10)) ||
  [&& nth 0%N w 0 == 3, nth 0%N w 1 == 10 & nth 0%N w 2 \in ksearch].

(* THE MATCH.  The symmetry 6 fixes the position, sends R to R and R' to R',  *)
(* takes F to B, and carries the five turns prop2 keeps onto the five Reid    *)
(* keeps.  So the two sets of six sequences are the same six seen twice.      *)
Lemma srel6_2 : srel 6 2 = 2. Proof. by vm_compute. Qed.
Lemma srel6_3 : srel 6 3 = 3. Proof. by vm_compute. Qed.
Lemma srel6_4 : srel 6 4 = 10. Proof. by vm_compute. Qed.

Lemma kept_search : all (fun t => srel 6 t \in ksearch) kept.
Proof. by vm_compute. Qed.

Lemma heads_sheads (w : seq nat) : (2 < seq.size w)%N -> heads w ->
  sheads [seq srel 6 m | m <- w].
Proof.
move=> s3 hh.
have n0 : nth 0%N [seq srel 6 m | m <- w] 0 = srel 6 (nth 0%N w 0).
  by rewrite (nth_map 0%N) //; apply: leq_trans s3.
have n1 : nth 0%N [seq srel 6 m | m <- w] 1 = srel 6 (nth 0%N w 1).
  by rewrite (nth_map 0%N) //; apply: leq_trans s3.
have n2 : nth 0%N [seq srel 6 m | m <- w] 2 = srel 6 (nth 0%N w 2).
  by rewrite (nth_map 0%N).
rewrite /sheads n0 n1 n2.
case/orP: hh => [/andP[/eqP e0 /eqP e1]|/and3P[/eqP e0 /eqP e1 e2]].
  by rewrite e0 e1 srel6_2 srel6_4 !eqxx.
apply/orP; right; apply/and3P; split.
- by rewrite e0 srel6_3.
- by rewrite e1 srel6_4.
by apply: (allP kept_search).
Qed.

(* ---- Proposition 2 for the position the run searches --------------------  *)

(* A shortest maneuver for the searched position becomes one of the same      *)
(* length whose Sx image begins with one of Reid's six sequences.             *)
Theorem prop2_search (w : seq nat) : qw w -> wp w = targ ->
  (forall u, qw u -> wp u = targ -> (seq.size w <= seq.size u)%N) ->
  exists w', [/\ qw w', seq.size w' = seq.size w, wp w' = targ
              & sheads [seq xrel m | m <- w'] ].
Proof.
move=> wq hw hmin.
have hx := man_x wq hw.
have hxq := xrel_qw wq.
have hxmin : forall u, qw u -> wp u = P ->
             (seq.size [seq xrel m | m <- w] <= seq.size u)%N.
  move=> u uq hu; rewrite size_map.
  by have := hmin _ (yrel_qw uq) (man_y uq hu); rewrite size_map.
have [w2 [q2 s2 p2 h2]] := prop2 hxq hx hxmin.
have s3 : (2 < seq.size w2)%N by apply: man_size3.
have q3 := srel_qw (i := 6) isT q2.
have p3 := man_sym (i := 6) isT q2 p2.
have h3 := heads_sheads s3 h2.
exists [seq yrel m | m <- [seq srel 6 m | m <- w2]]; split.
- by apply: yrel_qw.
- by rewrite !size_map s2 size_map.
- by apply: man_y.
have hb : [seq xrel m | m <- [seq yrel m | m <- [seq srel 6 m | m <- w2]]]
        = [seq srel 6 m | m <- w2].
  rewrite -map_comp -[RHS]map_id; apply/eq_in_map => m mw /=.
  by apply/eqP; apply: (allP xrelK); apply: mem_iota0; apply: (allP q3).
by rewrite hb.
Qed.

(* ---- 3, in part: what a shortest maneuver cannot contain ----------------  *)

(* The search keeps only words its rule allows: no turn cancelling the one    *)
(* before it, no run of three, and one order of two opposite faces.  The first*)
(* two are properties of a SHORTEST maneuver and are proved here.  What is not*)
(* proved is that the whole rule loses nothing -- see the end of the file.    *)

Lemma qmv_cancel m : (m < nq)%N -> qmv m * qmv (qinv m) = 1.
Proof. by move=> mL; rewrite -qmvV // mulgV. Qed.

(* a quarter turn has order four                                              *)
Lemma qmv4 : all (fun m => comp_tab (comp_tab (mvt m) (mvt m))
                                    (comp_tab (mvt m) (mvt m)) == id_tab flast)
                 (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma qmv_cube m : (m < nq)%N -> qmv m * qmv m * qmv m = qmv (qinv m).
Proof.
move=> mL; have /eqP h4 := allP qmv4 _ (mem_iota0 mL).
have hq : qmv m * qmv m * (qmv m * qmv m) = 1.
  rewrite !qmvE // !ptM ?mvt_ok ?tab_ok_comp ?mvt_ok //.
  by rewrite h4 pt1.
rewrite -qmvV //; apply: (mulIg (qmv m)).
by rewrite mulVg -mulgA hq.
Qed.

Lemma wp_triple (a b c : nat) (u v : seq nat) :
  wp (u ++ a :: b :: c :: v) = wp u * (qmv a * qmv b * qmv c) * wp v.
Proof. by rewrite wp_cat !wp_cons !mulgA. Qed.

Lemma cancel_short (u v : seq nat) m : (m < nq)%N ->
  wp (u ++ m :: qinv m :: v) = targ -> wp (u ++ v) = targ.
Proof. by move=> mL h; rewrite wp_cat -h wp_pair qmv_cancel // mulg1. Qed.

Lemma run3_short (u v : seq nat) m : (m < nq)%N ->
  wp (u ++ m :: m :: m :: v) = targ -> wp (u ++ qinv m :: v) = targ.
Proof.
by move=> mL h; rewrite -h wp_triple qmv_cube // wp_cat wp_cons mulgA.
Qed.

Lemma min_no_cancel (w u v : seq nat) m : (m < nq)%N -> qw w ->
  (forall t, qw t -> wp t = targ -> (seq.size w <= seq.size t)%N) ->
  wp w = targ -> w = u ++ m :: qinv m :: v -> False.
Proof.
move=> mL wq hmin hw wE.
have uq : qw u by move: wq; rewrite wE /qw all_cat => /andP[].
have vq : qw v.
  by move: wq; rewrite wE /qw all_cat /= => /andP[_ /and3P[_ _]].
have quv : qw (u ++ v) by rewrite /qw all_cat; apply/andP; split.
have hc : wp (u ++ v) = targ by apply: (cancel_short mL); rewrite -wE.
have := hmin _ quv hc; rewrite wE !size_cat /= leq_add2l => hle.
have h2 := leq_trans (leqnSn (seq.size v).+1) hle.
by rewrite ltnn in h2.
Qed.

Lemma min_no_run3 (w u v : seq nat) m : (m < nq)%N -> qw w ->
  (forall t, qw t -> wp t = targ -> (seq.size w <= seq.size t)%N) ->
  wp w = targ -> w = u ++ m :: m :: m :: v -> False.
Proof.
move=> mL wq hmin hw wE.
have uq : qw u by move: wq; rewrite wE /qw all_cat => /andP[].
have vq : qw v.
  by move: wq; rewrite wE /qw all_cat /= => /andP[_ /and4P[_ _ _]].
have quv : qw (u ++ qinv m :: v).
  rewrite /qw all_cat; apply/andP; split => //=; apply/andP; split => //.
  by apply: qinv_lt.
have hc : wp (u ++ qinv m :: v) = targ by apply: (run3_short mL); rewrite -wE.
have := hmin _ quv hc; rewrite wE !size_cat /= leq_add2l => hle.
have h2 := leq_trans (leqnSn (seq.size v).+1) hle.
by rewrite ltnn in h2.
Qed.

(* ---- what is left -------------------------------------------------------  *)

(* 1 and 2 are done: the run searches the position prop2_search speaks about, *)
(* and its six prefixes are the six of prop2.                                 *)
(*                                                                            *)
(* 3 is half done.  A shortest maneuver has no cancelling pair and no run of  *)
(* three, which is min_no_cancel and min_no_run3.  What is left of it is that *)
(* the search's rule as a whole loses nothing: it also keeps only one of the  *)
(* two orders of two opposite faces, and turning a maneuver into one the rule *)
(* accepts everywhere at once needs an argument that terminates, which is not *)
(* here.                                                                      *)
(*                                                                            *)
(* 4 is untouched, and is the biggest piece: the table has to BE a lower      *)
(* bound.  What that means is that h of a coset never exceeds the distance of *)
(* any position in it, and the sweep that would prove it is Dstep over        *)
(* 2.9e10 cosets and twelve moves -- about twelve CPU-hours by the phase 1    *)
(* scaling, and a proof rather than a run.  Until it is done the search is a  *)
(* computation whose answer is not yet a theorem about distance.              *)
