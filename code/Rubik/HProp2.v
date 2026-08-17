(* =========================================================================  *)
(*  HProp2.v -- maneuvers as words, and the three transformations of them.    *)
(* =========================================================================  *)

(* Reid's Proposition 2 says that every maneuver for the position can be      *)
(* turned into one beginning with one of six sequences.  His proof moves a    *)
(* maneuver about with three transformations and uses one fact about the      *)
(* twelve turns; HReid.v proved the arithmetic of that fact, and this file    *)
(* turns all of it into statements about WORDS.                               *)
(*                                                                            *)
(* A word is a list of numbers below twelve, and wp is what it multiplies out *)
(* to.  A maneuver for the position is a word w with wp w = P.  The three     *)
(* transformations, each of them keeping both the product and the length:     *)
(*                                                                            *)
(*   man_sym   conjugate by one of the sixteen symmetries that fix P;         *)
(*   man_inv   invert, which reverses the word and inverts each turn;         *)
(*   man_rot   shift cyclically, the moved part conjugated by P itself.       *)
(*                                                                            *)
(* and the fact that both kinds of turn must occur:                           *)
(*                                                                            *)
(*   eight_not_P  no word of the eight is P, because each of them keeps the   *)
(*                primary edge stickers primary and P keeps none;             *)
(*   four_not_P   no word of the four is P, because they reach only sixteen   *)
(*                positions.                                                  *)
(*                                                                            *)
(* THE SIXTEEN ARE FOUND, NOT CONSTRUCTED.  Closing the three generators of   *)
(* Sym.v gives all 48 symmetries as tables; the ones that matter are those    *)
(* that fix P, and there are exactly sixteen of them.  Nothing here has to    *)
(* say which axis they keep.                                                  *)
(*                                                                            *)
(* What is still missing is the case analysis on the first three turns.  See  *)
(* the end of the file.                                                       *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Moves Coordfs Phase1
        HRoot HCoord HReid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Notation arr := (PArray.array int).

(* ---- words and what they multiply out to --------------------------------  *)

(* the twelve quarter turns                                                   *)
Definition nq := 12.

Definition qmv (m : nat) : {perm facelet} := nth 1 moves (qt18 m).

(* a word: every letter is a quarter turn                                     *)
Definition qw (w : seq nat) : bool := all (fun m => (m < nq)%N) w.

Definition wp (w : seq nat) : {perm facelet} := \prod_(m <- w) qmv m.

(* the same product on tables, where everything computes                      *)
Definition wtr (w : seq nat) : seq nat :=
  foldr (fun m t => comp_tab (mvt m) t) (id_tab flast) w.

Definition conjt (s t : seq nat) : seq nat :=
  comp_tab (inv_tab flast s) (comp_tab t s).

Lemma mem_iota0 n k : (k < n)%N -> k \in iota 0 n.
Proof. by move=> kL; rewrite mem_iota add0n leq0n kL. Qed.

Lemma qt18_lt m : (m < nq)%N -> (qt18 m < 18)%N.
Proof. by case: m => // [] [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]. Qed.

Lemma size_mtabs : seq.size mtabs = 18%N.
Proof. by vm_compute. Qed.

Lemma mvt_ok m : (m < nq)%N -> tab_ok flast (mvt m).
Proof.
move=> mL; rewrite /mvt; apply: (allP mtabs_ok); apply: mem_nth.
by rewrite size_mtabs qt18_lt.
Qed.

Lemma qmvE m : (m < nq)%N -> qmv m = pt flast (mvt m).
Proof.
by move=> mL; rewrite /qmv /mvt mtabsE (nth_map (id_tab flast))
     ?size_mtabs ?qt18_lt.
Qed.

Lemma wp_nil : wp [::] = 1.
Proof. by rewrite /wp big_nil. Qed.

Lemma wp_cons m w : wp (m :: w) = qmv m * wp w.
Proof. by rewrite /wp big_cons. Qed.

Lemma wp_cat u v : wp (u ++ v) = wp u * wp v.
Proof. by rewrite /wp big_cat. Qed.

Lemma wp_one m : wp [:: m] = qmv m.
Proof. by rewrite wp_cons wp_nil mulg1. Qed.

Lemma wtr_ok w : qw w -> tab_ok flast (wtr w).
Proof.
elim: w => [_|m w ih /andP[mL wL]] /=; first by apply: tab_ok_id.
by apply: tab_ok_comp; [apply: mvt_ok | apply: ih].
Qed.

Lemma wp_wtr w : qw w -> wp w = pt flast (wtr w).
Proof.
elim: w => [_ | m w ih]; first by rewrite wp_nil pt1.
rewrite /qw /= => /andP[mL wL].
by rewrite wp_cons ih // qmvE // ptM ?mvt_ok ?wtr_ok.
Qed.

(* ---- the position, as a permutation -------------------------------------  *)

Definition P : {perm facelet} := pt flast (ti2t flast pfb).

Lemma ptab_ok : tab_ok flast (ti2t flast pfb).
Proof. by vm_compute. Qed.

(* ---- no word of the eight is the position -------------------------------  *)

(* THE INVARIANT IS A SET, not an orientation: each of the eight sends the    *)
(* primary sticker of every edge to a primary sticker, so a product of them   *)
(* does too, while the position sends none of them there -- every edge of it  *)
(* is flipped.  Composition preserving a set needs no arithmetic at all.      *)
Definition keepst (t : seq nat) : bool :=
  all (fun f => nth 0%N t f \in eprim) eprim.

Definition eightw (w : seq nat) : bool := all (fun m => m \in eightm) w.
Definition fourw  (w : seq nat) : bool := all (fun m => m \in fourm) w.

Lemma nth_comp_tab t1 t2 i : (i < seq.size t1)%N ->
  nth 0%N (comp_tab t1 t2) i = nth 0%N t2 (nth 0%N t1 i).
Proof. by move=> iL; rewrite /comp_tab (nth_map 0%N). Qed.

Lemma eprim_lt f : f \in eprim -> (f < 48)%N.
Proof. by move: f; apply/allP; vm_compute. Qed.

Lemma tab_ok_size t : tab_ok flast t -> seq.size t = 48%N.
Proof. by rewrite /tab_ok => /andP[/eqP-> _]. Qed.

Lemma keepst_comp t1 t2 : tab_ok flast t1 ->
  keepst t1 -> keepst t2 -> keepst (comp_tab t1 t2).
Proof.
move=> t1ok k1 k2; apply/allP => f fE.
rewrite nth_comp_tab ?tab_ok_size ?eprim_lt //.
by apply: (allP k2); apply: (allP k1).
Qed.

Lemma keepst_id : keepst (id_tab flast).
Proof. by vm_compute. Qed.

Lemma eight_keeps : all (fun m => keepst (mvt m)) eightm.
Proof. by vm_compute. Qed.

Lemma eightm_lt m : m \in eightm -> (m < nq)%N.
Proof. by move: m; apply/allP; vm_compute. Qed.

Lemma fourm_lt m : m \in fourm -> (m < nq)%N.
Proof. by move: m; apply/allP; vm_compute. Qed.

Lemma eightw_qw w : eightw w -> qw w.
Proof. by move/allP=> h; apply/allP => m /h /eightm_lt. Qed.

Lemma fourw_qw w : fourw w -> qw w.
Proof. by move/allP=> h; apply/allP => m /h /fourm_lt. Qed.

Lemma keepst_wtr w : eightw w -> keepst (wtr w).
Proof.
elim: w => [_|m w ih] /=; first exact: keepst_id.
move=> /andP[mE wE]; apply: keepst_comp; last exact: ih.
- by apply: mvt_ok; apply: eightm_lt.
by apply: (allP eight_keeps).
Qed.

Lemma pfb_not_keepst : keepst (ti2t flast pfb) = false.
Proof. by vm_compute. Qed.

Lemma eight_not_P w : eightw w -> wp w != P.
Proof.
move=> wE; apply/eqP => wPE.
have := pfb_not_keepst; rewrite -(_ : wtr w = ti2t flast pfb) ?keepst_wtr //.
apply: (@pt_inj flast);
  [by apply: wtr_ok; apply: eightw_qw | exact: ptab_ok |].
by rewrite -wp_wtr ?wPE //; apply: eightw_qw.
Qed.

(* ---- nor of the four, which reach only sixteen positions ----------------  *)

Lemma gen4_prod : all (fun t => all (fun s => comp_tab t s \in gen4) gen4) gen4.
Proof. by vm_compute. Qed.

Lemma four_in_gen4 : all (fun m => mvt m \in gen4) fourm.
Proof. by vm_compute. Qed.

Lemma id_in_gen4 : id_tab flast \in gen4.
Proof. by vm_compute. Qed.

Lemma wtr_gen4 w : fourw w -> wtr w \in gen4.
Proof.
elim: w => [_|m w ih] /=; first exact: id_in_gen4.
move=> /andP[mE wE].
by apply: (allP (allP gen4_prod _ (allP four_in_gen4 _ mE))); exact: ih.
Qed.

Lemma four_not_P w : fourw w -> wp w != P.
Proof.
move=> wE; apply/eqP => wPE.
have := pfb_not_gen4; rewrite -(_ : wtr w = ti2t flast pfb) ?wtr_gen4 //.
apply: (@pt_inj flast);
  [by apply: wtr_ok; apply: fourw_qw | exact: ptab_ok |].
by rewrite -wp_wtr ?wPE //; apply: fourw_qw.
Qed.

(* ---- a relabelling of the letters, applied to a word --------------------  *)

Lemma wp_map (f : nat -> nat) (g : {perm facelet}) (w : seq nat) :
  (forall m, m \in w -> (qmv m) ^ g = qmv (f m)) ->
  (wp w) ^ g = wp [seq f m | m <- w].
Proof.
elim: w => [_|m w ih]; first by rewrite /wp !big_nil conj1g.
move=> h; rewrite map_cons !wp_cons conjMg h ?mem_head //.
by rewrite ih // => k kw; apply: h; rewrite inE kw orbT.
Qed.

(* ---- the cyclic shift --------------------------------------------------   *)

(* Shifting the head of a maneuver to its end is a maneuver again because the *)
(* head comes back conjugated by the position: with a the head's product and b*)
(* the tail's, b * a ^ (a * b) = a * b.                                       *)
Lemma sigma_tab :
  all (fun m => conjt (ti2t flast pfb) (mvt m) == mvt (sigq m)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma sigq_lt m : (m < nq)%N -> (sigq m < nq)%N.
Proof. by case: m => // [] [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]. Qed.

Lemma qmv_JP m : (m < nq)%N -> (qmv m) ^ P = qmv (sigq m).
Proof.
move=> mL.
have /eqP hs := allP sigma_tab _ (mem_iota0 mL).
rewrite /P !qmvE ?sigq_lt // ptJ ?mvt_ok ?ptab_ok //.
by congr pt; exact: hs.
Qed.

Lemma sigq_qw (w : seq nat) : qw w -> qw [seq sigq m | m <- w].
Proof.
move=> wq; apply/allP => k /mapP[m mw ->].
by apply: sigq_lt; apply: (allP wq).
Qed.

Theorem man_rot (u v : seq nat) : qw u -> wp (u ++ v) = P ->
  wp (v ++ [seq sigq m | m <- u]) = P.
Proof.
move=> uq hP.
have hu : (wp u) ^ P = wp [seq sigq m | m <- u].
  by apply: wp_map => k ku; apply: qmv_JP; apply: (allP uq).
rewrite wp_cat -hu conjgE -hP wp_cat.
by rewrite invMg -!mulgA mulKVg mulKg.
Qed.

(* ---- inversion ---------------------------------------------------------   *)

(* The turns pair up: an even letter and the odd one after it are inverse.    *)
Definition qinv (m : nat) : nat := if odd m then (m - 1)%N else (m + 1)%N.

Lemma qinv_lt m : (m < nq)%N -> (qinv m < nq)%N.
Proof. by case: m => // [] [|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]. Qed.

Lemma inv_tab_mvt :
  all (fun m => inv_tab flast (mvt m) == mvt (qinv m)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma qmvV m : (m < nq)%N -> (qmv m)^-1 = qmv (qinv m).
Proof.
move=> mL; have /eqP hs := allP inv_tab_mvt _ (mem_iota0 mL).
by rewrite !qmvE ?qinv_lt // ptV ?mvt_ok //; congr pt.
Qed.

Lemma P_invE : P^-1 = P.
Proof. by rewrite /P ptV ?ptab_ok //; congr pt. Qed.

Lemma qinv_qw (w : seq nat) : qw w -> qw [seq qinv m | m <- rev w].
Proof.
move=> wq; apply/allP => k /mapP[m mw ->]; apply: qinv_lt.
by apply: (allP wq); rewrite -mem_rev.
Qed.

Lemma wp_rev (w : seq nat) : qw w -> wp [seq qinv m | m <- rev w] = (wp w)^-1.
Proof.
elim: w => [_|m w ih]; first by rewrite /rev /= wp_nil invg1.
rewrite /qw /= => /andP[mL wL].
rewrite rev_cons -cats1 map_cat wp_cat wp_one ih // -(qmvV mL).
by rewrite wp_cons invMg.
Qed.

Theorem man_inv (w : seq nat) : qw w -> wp w = P ->
  wp [seq qinv m | m <- rev w] = P.
Proof. by move=> wq hP; rewrite wp_rev // hP P_invE. Qed.

(* ---- the sixteen symmetries that fix the position ----------------------   *)

Definition symgen : seq (seq nat) := [:: Sytab; Sxtab; cycs_tab flast Smncyc].

Definition grows (l : seq (seq nat)) : seq (seq nat) :=
  undup (l ++ flatten [seq [seq comp_tab t s | s <- symgen] | t <- l]).

Definition sym48 : seq (seq nat) := Eval vm_compute in
  iter 7 grows [:: id_tab flast].

Definition sym16 : seq (seq nat) := Eval vm_compute in
  [seq s <- sym48 | conjt s (ti2t flast pfb) == ti2t flast pfb].

Definition qtabs : seq (seq nat) := Eval vm_compute in
  [seq mvt m | m <- iota 0 nq].

Definition srelt : seq (seq nat) := Eval vm_compute in
  [seq [seq index (conjt s (mvt m)) qtabs | m <- iota 0 nq] | s <- sym16].

Definition srel (i m : nat) : nat := nth 0%N (nth [::] srelt i) m.

Definition symp (i : nat) : {perm facelet} := pt flast (nth [::] sym16 i).

Lemma size_sym48 : seq.size sym48 = 48%N.
Proof. by vm_compute. Qed.

Lemma size_sym16 : seq.size sym16 = 16%N.
Proof. by vm_compute. Qed.

Lemma sym16_ok : all (tab_ok flast) sym16.
Proof. by vm_compute. Qed.

Lemma sym16_fix :
  all (fun s => conjt s (ti2t flast pfb) == ti2t flast pfb) sym16.
Proof. by vm_compute. Qed.

Lemma srel_conj :
  all (fun i => all (fun m => conjt (nth [::] sym16 i) (mvt m)
                                == mvt (srel i m))
                    (iota 0 nq))
      (iota 0 16).
Proof. by vm_compute. Qed.

Lemma srel_lt :
  all (fun i => all (fun m => (srel i m < nq)%N) (iota 0 nq)) (iota 0 16).
Proof. by vm_compute. Qed.

Lemma sym16_mem i : (i < 16)%N -> nth [::] sym16 i \in sym16.
Proof. by move=> iL; apply: mem_nth; rewrite size_sym16. Qed.

Lemma sym16_nth_ok i : (i < 16)%N -> tab_ok flast (nth [::] sym16 i).
Proof. by move=> iL; apply: (allP sym16_ok); exact: sym16_mem. Qed.

Lemma qmv_Jsym i m : (i < 16)%N -> (m < nq)%N ->
  (qmv m) ^ (symp i) = qmv (srel i m).
Proof.
move=> iL mL.
have /eqP hs := allP (allP srel_conj _ (mem_iota0 iL)) _ (mem_iota0 mL).
have mrL : (srel i m < nq)%N.
  by apply: (allP (allP srel_lt _ (mem_iota0 iL)) _ (mem_iota0 mL)).
rewrite /symp !qmvE // ptJ ?mvt_ok ?sym16_nth_ok //.
by congr pt; exact: hs.
Qed.

Lemma P_Jsym i : (i < 16)%N -> P ^ (symp i) = P.
Proof.
move=> iL; have /eqP hs := allP sym16_fix _ (sym16_mem iL).
rewrite /P /symp (@ptJ flast _ _ ptab_ok (sym16_nth_ok iL)).
by congr pt; exact: hs.
Qed.

Lemma srel_qw i (w : seq nat) : (i < 16)%N -> qw w ->
  qw [seq srel i m | m <- w].
Proof.
move=> iL wq; apply/allP => k /mapP[m mw ->].
apply: (allP (allP srel_lt _ (mem_iota0 iL))); apply: mem_iota0.
by apply: (allP wq).
Qed.

Theorem man_sym i (w : seq nat) : (i < 16)%N -> qw w -> wp w = P ->
  wp [seq srel i m | m <- w] = P.
Proof.
move=> iL wq hP.
have h : (wp w) ^ (symp i) = wp [seq srel i m | m <- w].
  by apply: wp_map => k kw; apply: qmv_Jsym => //; apply: (allP wq).
by rewrite -h hP P_Jsym.
Qed.

(* ---- what is left ------------------------------------------------------   *)

(* Everything above keeps a maneuver a maneuver and keeps its length, and no  *)
(* maneuver is all of one kind.  The case analysis on top of that is still to *)
(* be written:                                                                *)
(*                                                                            *)
(*   1. going round a cyclic word in which both kinds occur, some place has a *)
(*      turn of the eight followed by one of the four; man_rot brings it to   *)
(*      the front;                                                            *)
(*   2. for each of the 8 * 4 such pairs there is a symmetry among the sixteen*)
(*      carrying it to one of two pairs -- a finite check on srel, which is   *)
(*      not yet stated;                                                       *)
(*   3. after the second of those two, the eleven possible third turns reduce *)
(*      to five, the other six going to the first case by a symmetry or by    *)
(*      man_inv followed by man_rot.                                          *)
(*                                                                            *)
(* Until 1 to 3 are done, Proposition 2 is not proved, and the six positions  *)
(* the run searches are not yet known to be the right six.                    *)
