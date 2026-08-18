(* =========================================================================  *)
(*  HCanon.v -- obligation B: the search's rule loses no maneuver.            *)
(* =========================================================================  *)

(* WHAT IS OWED.  HBound.targ_far takes this as a hypothesis:                 *)
(*                                                                            *)
(*   forall v, qw v -> exists v', [/\ qw v', wp v' = wp v,                    *)
(*                                  size v' <= size v & okw 0 v']             *)
(*                                                                            *)
(* -- every element a word reaches is reached by a word the rule accepts, no  *)
(* longer.  Searchr.v IS this theorem, abstractly, for a group with a face    *)
(* structure, and it is proved there: reduce_word, ball_reduced, ball_searchr.*)
(* It does not instantiate here because of one hypothesis:                    *)
(*                                                                            *)
(*   fc_close : m1 * m2 = 1 \/ exists m3 in S, fc m3 = fc m1 /\ m1 * m2 = m3  *)
(*                                                                            *)
(* which says two turns of a face collapse into one turn OF THE SET.  For the *)
(* eighteen moves U * U = U2 is in the set; for the twelve quarter turns it is*)
(* not, which is exactly why the quarter-turn rule allows U U and forbids only*)
(* the third.  So B is Searchr.v generalised: two may stand, three collapse.  *)
(*                                                                            *)
(* This file has the parts of that which are specific to the quarter turns and*)
(* cheap: the three rewrites and the measure that makes them terminate.  The  *)
(* generalisation of Searchr.v itself is not here.                            *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Tsearch Rubik333 Sym Moves Coordfs Phase1
        HRoot HCoord HReid HProp2 HSearch HBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the three rewrites -------------------------------------------------  *)

(* Two of them are already proved, for any target, in HProp2: man_cancel takes*)
(* out a turn and its inverse, and qmv_cube turns three of a face into one.   *)
(* The third is the swap of two opposite faces, and that is here.             *)

Definition fce (m : nat) : nat := (m %/ 2)%N.

Definition oppq (a b : nat) : bool := (fce b == (fce a + 3) %% 6)%N.

Lemma comm_opp_tab :
  all (fun a => all (fun b => oppq a b ==>
         (comp_tab (mvt a) (mvt b) == comp_tab (mvt b) (mvt a))) (iota 0 nq))
      (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma qmv_comm_opp a b : (a < nq)%N -> (b < nq)%N -> oppq a b ->
  qmv a * qmv b = qmv b * qmv a.
Proof.
move=> aL bL ab.
have /implyP/(_ ab)/eqP h :=
  allP (allP comm_opp_tab _ (mem_iota0 aL)) _ (mem_iota0 bL).
by rewrite !qmvE // !ptM ?mvt_ok //; congr pt.
Qed.

Lemma man_swap (a b : nat) (u v : seq nat) (g : {perm facelet}) :
  (a < nq)%N -> (b < nq)%N -> oppq a b ->
  wp (u ++ a :: b :: v) = g -> wp (u ++ b :: a :: v) = g.
Proof. by move=> aL bL ab; rewrite !wp_pair qmv_comm_opp. Qed.

(* ---- the measure --------------------------------------------------------  *)

(* A cancel and a collapse make the word shorter; a swap does not, so on its  *)
(* own it could go round for ever.  What stops it: of two opposite faces the  *)
(* rule keeps the larger index first, and every swap moves one such pair the  *)
(* right way round.  phi counts the pairs still the wrong way round, and      *)
(* size + phi falls at every rewrite -- the shortenings cannot raise phi,     *)
(* since taking letters out only takes pairs out.                             *)

Definition ohi (a b : nat) : bool := oppq a b && (fce a < fce b)%N.

Fixpoint phi (w : seq nat) : nat :=
  if w is m :: w' then (count (ohi m) w' + phi w')%N else 0%N.

Lemma phi_cat (u s : seq nat) :
  phi (u ++ s) = (phi u + sumn [seq count (ohi m) s | m <- u] + phi s)%N.
Proof.
elim: u => [|m u ih] /=; first by rewrite add0n.
rewrite count_cat ih !addnA.
by rewrite [(count (ohi m) u + count (ohi m) s + phi u)%N]addnAC.
Qed.

(* Of two opposite faces only one order counts, so a swap cannot go both ways.*)
Lemma ohiN (a b : nat) : ohi a b -> ~~ ohi b a.
Proof. by rewrite /ohi => /andP[_ ab]; rewrite andbC leqNgt ltnW. Qed.

(* A SWAP DROPS phi BY EXACTLY ONE.  The pairs other than the swapped one are *)
(* untouched: the two letters only trade places between the same neighbours,  *)
(* so every count over the part before them is the same sum in another order. *)
Lemma phi_swap (a b : nat) (u v : seq nat) : ohi a b ->
  phi (u ++ a :: b :: v) = (phi (u ++ b :: a :: v)).+1.
Proof.
move=> ab; rewrite !phi_cat /=.
have hu : sumn [seq ohi m a + (ohi m b + count (ohi m) v) | m <- u]
        = sumn [seq ohi m b + (ohi m a + count (ohi m) v) | m <- u].
  by congr sumn; apply: eq_map => m; rewrite addnCA.
rewrite hu ab (negbTE (ohiN ab)) /= add0n add1n addSn addnS.
by congr (_ + _).+1; rewrite addnCA.
Qed.

(* THE TWO SHORTENINGS CANNOT RAISE phi.  Taking a letter out only takes pairs*)
(* out, and the collapse of three turns of a face into one leaves the face    *)
(* alone, which is all phi reads.                                             *)
Lemma phi_fce (u v : seq nat) (a m : nat) : fce a = fce m ->
  phi (u ++ a :: v) = phi (u ++ m :: v).
Proof.
move=> fam; rewrite !phi_cat /=.
have ho x : ohi x a = ohi x m by rewrite /ohi /oppq fam.
have hoa x : ohi a x = ohi m x by rewrite /ohi /oppq fam.
have hc : count (ohi a) v = count (ohi m) v.
  by apply: eq_count => x; rewrite hoa.
congr (_ + _ + _); last by rewrite hc.
by congr sumn; apply: eq_map => x; rewrite ho.
Qed.

Lemma phi_del (u v : seq nat) (m : nat) : (phi (u ++ v) <= phi (u ++ m :: v))%N.
Proof.
elim: u => [|x u ih] /=; first by rewrite leq_addl.
by rewrite leq_add // !count_cat /= addnCA leq_addl.
Qed.

(* ---- reading a class back ------------------------------------------------ *)

(* The class is `the last turn and how long its run is', and that is the form *)
(* the rewriting needs.  THE GUARD IS NOT DECORATION: a third turn of the same*)
(* face would take the class out of its own coding, and it is allowedq alone  *)
(* that keeps it in.                                                          *)
Lemma hclass_tab :
  all (fun p => all (fun m => allowedq p m ==>
        [&& hclass p m < nclass, plast (hclass p m) == m,
            0 < prun (hclass p m) & prun (hclass p m) <= 2]%N)
      (iota 0 nq)) (iota 0 nclass).
Proof. by vm_compute. Qed.

Lemma hclass_ok p m : (p < nclass)%N -> (m < nq)%N -> allowedq p m ->
  [/\ (hclass p m < nclass)%N, plast (hclass p m) = m,
      (0 < prun (hclass p m))%N & (prun (hclass p m) <= 2)%N].
Proof.
move=> pL mL ap.
have /implyP/(_ ap)/and4P[h1 /eqP h2 h3 h4] :=
  allP (allP hclass_tab _ (mem_iota0 pL)) _ (mem_iota0 mL).
by split.
Qed.

(* ---- what a violation calls for ------------------------------------------ *)

(* THE THREE REWRITES ARE EXHAUSTIVE, and this is where that is settled: a    *)
(* turn the rule refuses is either the other turn of the face just played --  *)
(* the two cancel -- or a third turn of it, which collapses into one, or the  *)
(* smaller of two opposite faces coming second, which swaps.  Twenty five     *)
(* classes by twelve turns, so it is a computation.                           *)
Lemma bad_tab :
  all (fun p => all (fun m => (0 < p)%N ==> ~~ allowedq p m ==>
     [|| (fce m == fce (plast p)) && (m != plast p),
         (m == plast p) && (prun p == 2)%N
       | ohi (plast p) m ])
      (iota 0 nq)) (iota 0 nclass).
Proof. by vm_compute. Qed.

Lemma bad_case p m :
  (0 < p)%N -> (p < nclass)%N -> (m < nq)%N -> ~~ allowedq p m ->
  [\/ fce m = fce (plast p) /\ m != plast p,
      m = plast p /\ prun p = 2%N | ohi (plast p) m].
Proof.
move=> p0 pL mL ap.
have /implyP/(_ p0)/implyP/(_ ap)/or3P[] :=
  allP (allP bad_tab _ (mem_iota0 pL)) _ (mem_iota0 mL).
- by move=> /andP[/eqP h1 h2]; apply: Or31.
- by move=> /andP[/eqP h1 /eqP h2]; apply: Or32.
by move=> h; apply: Or33.
Qed.

(* ---- the two turns of a face --------------------------------------------- *)

(* A face has two quarter turns and they are inverse, so of two turns of one  *)
(* face that are not the same one, the second undoes the first -- that is the *)
(* cancel.  And the turn three of a face collapse into is a turn of that same *)
(* face, which is all phi reads of it.                                        *)
Lemma qinv_tab :
  all (fun a => all (fun m => ((fce m == fce a) && (m != a)) ==> (m == qinv a))
       (iota 0 nq)) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma qinv_same a m : (a < nq)%N -> (m < nq)%N -> fce m = fce a -> m != a ->
  m = qinv a.
Proof.
move=> aL mL fam ma.
have /implyP/(_ (introT andP (conj (introT eqP fam) ma)))/eqP h :=
  allP (allP qinv_tab _ (mem_iota0 aL)) _ (mem_iota0 mL).
by [].
Qed.

Lemma fce_qinv_tab : all (fun a => fce (qinv a) == fce a) (iota 0 nq).
Proof. by vm_compute. Qed.

Lemma fce_qinv a : (a < nq)%N -> fce (qinv a) = fce a.
Proof.
by move=> aL; apply/eqP; apply: (allP fce_qinv_tab); apply: mem_iota0.
Qed.

(* ---- what is left -------------------------------------------------------  *)

(* With the three rewrites and this measure, the shape of the argument is     *)
(* Searchr.v's: while the word breaks the rule somewhere, rewrite there; the  *)
(* measure falls, so it stops; and it stops at a word the rule accepts.  Two  *)
(* pieces are missing:                                                        *)
(*                                                                            *)
(*   the analysis of a violation -- from ~~ okw 0 w, produce the place and    *)
(*     which of the three rewrites applies, which needs the class to be read  *)
(*     back as `the last turn and how long its run is';                       *)
(*   the induction on size + phi.                                             *)
(*                                                                            *)
(* Doing it by generalising Searchr.v rather than here is the better route:   *)
(* its inv/nosame/reduce machinery is this argument already, and only the     *)
(* merge case changes.                                                        *)
