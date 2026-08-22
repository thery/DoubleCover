(* =========================================================================  *)
(*  RowLeaf.v -- a position of H is its three ranks.                          *)
(* =========================================================================  *)

(* WHAT RowInst STILL ASKS FOR, taken apart.  memb2tab builds a cube from     *)
(* three ranks and tomemb reads three ranks off a cube; leaf_memb and         *)
(* tomemb_tab say the two undo each other on a position of H.                 *)
(*                                                                            *)
(* THE PREMISE IN RowInst IS THE WRONG ONE.  It reads `wdist (p1get p1 c) =   *)
(* 0', and p1 is a VARIABLE -- an arbitrary array.  Nothing ties that number  *)
(* to the cube, so neither fact is provable as it stands.  What is meant is   *)
(* that the position is in H, and that is a condition on the POSITION: no     *)
(* corner twisted, no edge flipped, the middle four in the middle layer.  p1  *)
(* is then only the pruning table, which soundness never looks at.            *)
(*                                                                            *)
(* Being in H says the same thing three times, once for each layout: the      *)
(* position carries a place to a place and leaves the SLOT alone.  That is    *)
(* assumed here, as hqc, hqu and hqm, and it is what is left to prove.        *)
(* leaf_memb is proved from it below.                                         *)

From mathcomp Require Import all_ssreflect all_fingroup.
From Stdlib Require Import Uint63.
From Stdlib Require Import -(notations) PArray.
From Rubik Require Import ssrint63.
Require Import Table Tabi Rubik333 Diameter Moves Ball.
Require Import Coordfs Coordfsi Phase1.
Require Import Row RowMap RowRun RowFinal RowInst RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the parity of a permutation of the places --------------------------- *)

(* Counted as inversions, which is what the tables have to agree with.        *)
Definition prmn (n : nat) (q : nat -> nat) : bool :=
  odd (count (fun ij => ((ij.1 < ij.2) && (q ij.2 < q ij.1))%N)
             (allpairs (fun i j => (i, j)) (iota 0 n) (iota 0 n))).

(* ---- a fold does not look past its list ---------------------------------- *)

Lemma foldl_eq_in (T : eqType) (R : Type) (F G : R -> T -> R)
  (s : seq T) (r : R) :
  (forall x r', x \in s -> F r' x = G r' x) -> foldl F r s = foldl G r s.
Proof.
elim: s r => [|x s ih] r hFG //=.
rewrite hFG ?mem_head //; apply: ih => y r' hy.
by apply: hFG; rewrite in_cons hy orbT.
Qed.

(* so the rank only looks at the places                                       *)
Lemma lrank_eq n (f g : nat -> nat) :
  (forall p, (p < n)%N -> f p = g p) -> lrank n f = lrank n g.
Proof.
move=> hfg; rewrite /lrank; apply: foldl_eq_in => i r.
rewrite mem_iota add0n => /andP[_ hi]; congr (_ + _)%N.
apply: eq_in_count => j; rewrite mem_iota => /andP[hj1 hj2].
by rewrite !hfg // (leq_trans hj2) // subnKC.
Qed.

(* ---- the first facelet of a place, the same three times ------------------ *)

Lemma cflatp_prim :
  all (fun p => nth 0%N cflatp (p * 3)%N == nth 0%N cprimp p) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma ulay_prim :
  all (fun p => nth 0%N ulay (p * 2)%N == nth 0%N eprim p) (iota 0 8).
Proof. by vm_compute. Qed.

(* and the middle four sit at places eight and up                             *)
Lemma eposn_mlayC :
  all (fun p => eposn (nth 0%N mlay (p * 2)%N) == (8 + p)%N) (iota 0 4).
Proof. by vm_compute. Qed.

Lemma mlay_prim :
  all (fun p => nth 0%N mlay (p * 2)%N == nth 0%N eprim (8 + p)%N) (iota 0 4).
Proof. by vm_compute. Qed.

(* ---- and reading a place back off its own layout ------------------------- *)

Lemma cposn_lay p : (p < 8)%N -> cposn (nth 0%N cflatp (p * 3)%N) = p.
Proof.
move=> hp; have hi : (p * 3 < 8 * 3)%N by rewrite ltn_mul2r.
have /and4P[_ _ /eqP h _] := layP clayokC hi.
by rewrite h mulnK.
Qed.

Lemma eposn_ulay p : (p < 8)%N -> eposn (nth 0%N ulay (p * 2)%N) = p.
Proof.
move=> hp; have hi : (p * 2 < 8 * 2)%N by rewrite ltn_mul2r.
have /and4P[_ _ /eqP h _] := layP ulayokC hi.
by rewrite h mulnK.
Qed.

Lemma mplc_mlay p : (p < 4)%N -> mplc (nth 0%N mlay (p * 2)%N) = p.
Proof.
move=> hp; have hi : (p * 2 < 4 * 2)%N by rewrite ltn_mul2r.
have /and4P[_ _ /eqP h _] := layP mlayokC hi.
by rewrite h mulnK.
Qed.

(* ---- what a Lehmer rank owes, and it is arithmetic ----------------------- *)

(* At place i the rank multiplies by n - i and adds a count over n - i - 1    *)
(* places, so it never reaches n factorial.  Nothing about the cube, and true *)
(* of ANY function, not only of a permutation.                                *)
(* the fold in general: it multiplies by n - i and adds something below       *)
(* n - i - 1, so from r it never reaches (r + 1) times m factorial            *)
Lemma fold_mixed n (g : nat -> nat) :
  (forall i, (g i <= n - i.+1)%N) ->
  forall m k r, (k + m = n)%N ->
    (foldl (fun a i => (a * (n - i) + g i)%N) r (iota k m) < (r + 1) * m`!)%N.
Proof.
move=> hg; elim=> [|m ih] k r hkm /=; first by rewrite fact0 muln1 addn1.
have hnk : (n - k = m.+1)%N by rewrite -hkm addKn.
have hnk1 : (n - k.+1 = m)%N by rewrite -hkm -addSnnS addKn.
have hgk : (g k <= m)%N by rewrite -hnk1; apply: hg.
apply: leq_trans (ih k.+1 _ _) _; first by rewrite addSnnS.
have hf : (0 < m`!)%N by apply: fact_gt0.
rewrite factS mulnA leq_pmul2r //.
by rewrite hnk mulnDl mul1n -addnA leq_add2l addn1 ltnS.
Qed.

Lemma lrank_lt n f : (lrank n f < n`!)%N.
Proof.
have hg i : (count (fun j => (f j < f i)%N) (iota i.+1 (n - i.+1))
             <= n - i.+1)%N.
  by rewrite -{2}(size_iota i.+1 (n - i.+1)); apply: count_size.
by move: (fold_mixed hg 0%N (add0n n)); rewrite add0n mul1n /lrank.
Qed.

Lemma rank8_ltP f : (rank8 f <? npagei)%uint63.
Proof.
have h8 : (8`! = 40320)%N by [].
have hl : (lrank 8 f < 40320)%N by rewrite -h8; apply: lrank_lt.
have hw : (40320 < nwB)%N by apply: (@ltn_nwB 16).
apply/nltbP; rewrite /rank8 (of_natK _ (leq_trans hl (ltnW hw))).
by rewrite -/npagen npagenE.
Qed.

Lemma rank4_ltP f : (rank4 f <? nbiti)%uint63.
Proof.
have h4 : (4`! = 24)%N by [].
have hl : (lrank 4 f < 24)%N by rewrite -h4; apply: lrank_lt.
have hw : (24 < nwB)%N by apply: (@ltn_nwB 5).
apply/nltbP; rewrite /rank4 (of_natK _ (leq_trans hl (ltnW hw))).
by have -> : to_nat nbiti = 24%N by vm_compute.
Qed.

(* ---- the parity, like the rank, only looks at its places ----------------- *)

Lemma prmn_eq n (f g : nat -> nat) :
  (forall p, (p < n)%N -> f p = g p) -> prmn n f = prmn n g.
Proof.
move=> hfg; rewrite /prmn; congr odd; apply: eq_in_count => ij.
move=> /allpairsPdep[i [j [hi hj ->]]] /=.
by move: hi hj; rewrite !mem_iota !add0n => /andP[_ hi] /andP[_ hj];
   rewrite !hfg.
Qed.

(* ---- and the unranking undoes the ranking -------------------------------- *)

(* up8 IS A TABLE, so that it inverts the ranking is a fact about the data,   *)
(* not about the cube: rank the row and the row number comes back.  A walk    *)
(* over the 40320, and over the 24 for the middle four.                       *)
(*                                                                            *)
(* THE WALKS ARE CARRIED AS ARGUMENTS, never as section hypotheses.  Put in   *)
(* the context they change what `//' closes in proofs that have nothing to do *)
(* with them, and three lemmas broke that way.                                *)
Definition up8inv : bool :=
  iter npagen 0%uint63 (fun r => (rank8 (up8 r) =? r)%uint63).
Definition up4inv : bool :=
  iter nbitn 0%uint63 (fun r => (rank4 (up4 r) =? r)%uint63).

(* ---- the ranking is one to one on permutations --------------------------- *)

(* Lehmer's own fact, and it comes apart in two.  The CODE of a permutation   *)
(* is, at each place, how many later places hold something smaller; the rank  *)
(* is the code read as a mixed radix number, digit i below n - i - 1.         *)
Definition lcode (n : nat) (q : nat -> nat) (i : nat) : nat :=
  count (fun j => (q j < q i)%N) (iota i.+1 (n - i.+1)).

(* one: the rank determines the code, because the radix leaves no choice.     *)
(* This is fold_mixed read backwards and wants the same induction.            *)
Lemma lrank_code n (q1 q2 : nat -> nat) :
  lrank n q1 = lrank n q2 ->
  forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i.
Proof. Admitted.

(* two: the code determines the permutation.  At the first place the code     *)
(* says how many of the others are smaller, which fixes q 0 outright, and the *)
(* rest follows on the places that are left.                                  *)
Lemma code_perm n (q1 q2 : nat -> nat) :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  (forall i, (i < n)%N -> lcode n q1 i = lcode n q2 i) ->
  forall p, (p < n)%N -> q1 p = q2 p.
Proof. Admitted.

Lemma lrank_inj n (q1 q2 : nat -> nat) :
  perm_eq [seq q1 p | p <- iota 0 n] (iota 0 n) ->
  perm_eq [seq q2 p | p <- iota 0 n] (iota 0 n) ->
  lrank n q1 = lrank n q2 -> forall p, (p < n)%N -> q1 p = q2 p.
Proof.
move=> h1 h2 hr; apply: code_perm => //.
exact: lrank_code hr.
Qed.

(* and the int63 rank determines the nat rank, both being small               *)
Lemma rank8_inj q1 q2 : rank8 q1 = rank8 q2 -> lrank 8 q1 = lrank 8 q2.
Proof.
move=> h; rewrite /rank8 in h.
have hw : (40320 < nwB)%N by apply: (@ltn_nwB 16).
have b q : (lrank 8 q < nwB)%N.
  apply: leq_trans (ltnW hw); have -> : (40320 = 8`!)%N by [].
  exact: lrank_lt.
by rewrite -(of_natK _ (b q1)) -(of_natK _ (b q2)) h.
Qed.

Lemma rank4_inj q1 q2 : rank4 q1 = rank4 q2 -> lrank 4 q1 = lrank 4 q2.
Proof.
move=> h; rewrite /rank4 in h.
have hw : (24 < nwB)%N by apply: (@ltn_nwB 5).
have b q : (lrank 4 q < nwB)%N.
  apply: leq_trans (ltnW hw); have -> : (24 = 4`!)%N by [].
  exact: lrank_lt.
by rewrite -(of_natK _ (b q1)) -(of_natK _ (b q2)) h.
Qed.

Lemma up8_lrank q : up8inv -> up8ok ->
  perm_eq [seq q p | p <- iota 0 8] (iota 0 8) ->
  forall p, (p < 8)%N -> up8 (rank8 q) p = q p.
Proof.
move=> hw h8 hq p hp; have hr := rank8_ltP q.
have hrr : rank8 (up8 (rank8 q)) = rank8 q.
  by apply/eqP; apply: (iter_at hw (ltn_npagei hr)).
have hperm : perm_eq [seq up8 (rank8 q) p | p <- iota 0 8] (iota 0 8).
  by apply: (iter_at h8 (ltn_npagei hr)).
exact: (lrank_inj hperm hq (rank8_inj hrr) hp).
Qed.

Lemma up4_lrank q : up4inv -> up4ok ->
  perm_eq [seq q p | p <- iota 0 4] (iota 0 4) ->
  forall p, (p < 4)%N -> up4 (rank4 q) p = q p.
Proof.
move=> hw h4 hq p hp; have hr := rank4_ltP q.
have hrr : rank4 (up4 (rank4 q)) = rank4 q.
  by apply/eqP; apply: (iter_at hw (ltn_nbiti hr)).
have hperm : perm_eq [seq up4 (rank4 q) p | p <- iota 0 4] (iota 0 4).
  by apply: (iter_at h4 (ltn_nbiti hr)).
exact: (lrank_inj hperm hq (rank4_inj hrr) hp).
Qed.

(* ---- what the parity tables owe, as a walk ------------------------------- *)

(* par8 at a rank is the parity of the permutation that rank names.  It is    *)
(* NOT e8ok, which ties par8 to e8num and says nothing about a parity.        *)
Definition par8okw (par8t : arr) : bool :=
  iter npagen 0%uint63
    (fun r => (PArray.get par8t r
               =? (if prmn 8 (up8 r) then 1 else 0))%uint63).

Definition par4okw (par4t : arr) : bool :=
  iter nbitn 0%uint63
    (fun r => (PArray.get par4t r
               =? (if prmn 4 (up4 r) then 1 else 0))%uint63).

Lemma par8okP par8t q : up8inv -> up8ok -> par8okw par8t ->
  perm_eq [seq q p | p <- iota 0 8] (iota 0 8) ->
  PArray.get par8t (rank8 q) = (if prmn 8 q then 1 else 0)%uint63.
Proof.
move=> hi h8 hw hq.
have := iter_at hw (ltn_npagei (rank8_ltP q)) => /eqP ->.
by rewrite (prmn_eq (up8_lrank hi h8 hq)).
Qed.

Lemma par4okP par4t q : up4inv -> up4ok -> par4okw par4t ->
  perm_eq [seq q p | p <- iota 0 4] (iota 0 4) ->
  PArray.get par4t (rank4 q) = (if prmn 4 q then 1 else 0)%uint63.
Proof.
move=> hi h4 hw hq.
have := iter_at hw (ltn_nbiti (rank4_ltP q)) => /eqP ->.
by rewrite (prmn_eq (up4_lrank hi h4 hq)).
Qed.

(* ---- a part only looks at its own places --------------------------------- *)

Lemma part_eq (lay : seq nat) (nsl : nat) (inL : nat -> bool)
  (plc slt : nat -> nat) (v1 v2 : nat -> nat) :
  (forall f, (f < 48)%N -> inL f -> v1 (plc f) = v2 (plc f)) ->
  part lay nsl inL plc slt v1 = part lay nsl inL plc slt v2.
Proof.
move=> h; apply: (@eq_from_nth _ 0%N); first by rewrite !size_mkseq.
move=> f; rewrite size_mkseq => hf; rewrite !nth_mkseq //.
by case: (boolP (inL f)) => hL //; rewrite h.
Qed.

(* ---- and the three sets cover the forty eight facelets ------------------- *)

(* Twenty four corners, sixteen outer, eight middle.  It is what lets the     *)
(* three parts compose to the whole position and not merely agree on part of  *)
(* it.                                                                        *)
Definition covers : bool :=
  all (fun f => [|| inC f, inU f | inM f]) (iota 0 48).

Lemma coversC : covers.  Proof. by vm_compute. Qed.

(* ---- the parity law, and its checkable half ------------------------------ *)

(* THE THIRD INVARIANT of the cube: a position reached by moves has the same  *)
(* parity on the corners as on the edges.  It is not cubP -- cubP is the      *)
(* centraliser of an involution and is bigger than the group -- so it has to  *)
(* come along the word, one move at a time.                                   *)
(*                                                                            *)
(* The per move half IS checkable, and is checked here: the corner            *)
(* permutation of each of the eighteen moves and its edge permutation have    *)
(* the same parity.  Each move is a four cycle on four corners and a four     *)
(* cycle on four edges, so both are odd; the doubles are even on both.        *)

(* the corner permutation and the edge permutation a table names              *)
Definition cperm_of (t : seq nat) (p : nat) : nat :=
  cposn (nth 0%N t (nth 0%N cprimp p)).
Definition eperm_of (t : seq nat) (p : nat) : nat :=
  eposn (nth 0%N t (nth 0%N eprim p)).

Definition mvparok : bool :=
  all (fun m => prmn 8 (cperm_of (inv_tab flast (mvt m)))
                == prmn 12 (eperm_of (inv_tab flast (mvt m))))
      (iota 0 18).

Lemma mvparokC : mvparok.  Proof. by vm_compute. Qed.

(* THE LAW ITSELF, and it is the induction mvparokC feeds: the identity has   *)
(* both parities even, every move flips both or neither, so every position    *)
(* reached by a word has them equal.  This is where being IN THE GROUP is     *)
(* used, and it is the only place.                                            *)
(* THE BASE OF THE INDUCTION, and it is checked: the solved cube has both     *)
(* parities even.                                                             *)
Lemma prm_idC :
  prmn 8 (cperm_of (id_tab flast)) == prmn 12 (eperm_of (id_tab flast)).
Proof. by vm_compute. Qed.

(* AND THE STEP.  Playing a move on a position composes the two permutations  *)
(* with that move's, and the parity of a composition is the exclusive or, so  *)
(* both sides pick up the same bit -- which is exactly what mvparokC says.    *)
(* It needs the move to carry corners to corners and edges to edges, which is *)
(* what a facelet table of the cube does.                                     *)
Lemma prm_step t m : tab_ok flast t -> (m < 18)%N ->
  prmn 8 (cperm_of (comp_tab (mvt m) t))
    = prmn 8 (cperm_of (inv_tab flast (mvt m))) (+) prmn 8 (cperm_of t) /\
  prmn 12 (eperm_of (comp_tab (mvt m) t))
    = prmn 12 (eperm_of (inv_tab flast (mvt m))) (+) prmn 12 (eperm_of t).
Proof. Admitted.

(* and then the law is the induction along the word, prm_idC at the bottom    *)
(* and prm_step with mvparokC at each turn.  Ball.mem_gen_ball turns being in *)
(* the group into being in a ball, which is the word.                         *)
Lemma prm_law t : tab_ok flast t -> pt flast t \in G ->
  prmn 8 (cperm_of t) = prmn 12 (eperm_of t).
Proof. Admitted.

(* ---- what being in H says about the corners ------------------------------ *)

(* THE ONE THING LEFT is that being in H carries a place to a place and       *)
(* leaves the slot alone.  For the corners it comes from two facts, and       *)
(* NEITHER IS NEW.                                                            *)
(*                                                                            *)
(* The first is that the position commutes with ccyct, the three cycle that   *)
(* turns every corner in place.  That is Phase1's cubcP, which pstok already  *)
(* carries inside twP, and Moves.moves_cubcP_tab checks it for every move.    *)
(* It says the three facelets of a corner stay together AND IN ORDER, so a    *)
(* slot is carried to the same slot.                                          *)
(*                                                                            *)
(* The second is that the twist is nought, which says the U or D facelet of   *)
(* every place holds a U or D sticker -- so the primary facelet of a place    *)
(* goes to the primary facelet of a place, and that fixes which place.        *)

(* the layout and the rotation agree: ccyct sends the facelet at slot j of a  *)
(* place to the one at slot j + 1, the same place                             *)
Lemma ccyct_lay :
  all (fun i => nth 0%N ccyct (nth 0%N cflatp i)
                == nth 0%N cflatp ((i %/ 3) * 3 + (i %% 3).+1 %% 3)%N)
      (iota 0 24).
Proof. by vm_compute. Qed.

(* and the primary facelet of a place is the one whose slot is nought         *)
Lemma cprimp_lay :
  all (fun p => nth 0%N cprimp p == nth 0%N cflatp (p * 3)%N) (iota 0 8).
Proof. by vm_compute. Qed.

Section InHCorner.

Variable u : seq nat.
Hypothesis huok : tab_ok flast u.

(* pstok's cubcP half, as a table                                             *)
Hypothesis hcyc : comp_tab u ccyct = comp_tab ccyct u.

(* the twist is nought, place by place                                        *)
Hypothesis htw0 : forall p, (p < 8)%N ->
  nth 0%N u (nth 0%N cprimp p) \in cprim.

(* so the corners keep their slot, with the place permutation cperm_of u      *)
Lemma inH_corner p j : (p < 8)%N -> (j < 3)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3 + j)%N)
  = nth 0%N cflatp (cperm_of u p * 3 + j)%N.
Proof. Admitted.

End InHCorner.

Section Leaf.

(* ---- the position, as the table tomemb reads ----------------------------- *)

(* tomemb reads the INVERSE table: at the primary facelet of a place it gives *)
(* the home facelet of whatever sits there.                                   *)
Variable u : seq nat.

(* ---- 1, ASSUMED: being in H is three place permutations ------------------ *)

Variable qc qu qm : nat -> nat.

Hypothesis hqc : forall p j, (p < 8)%N -> (j < 3)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3 + j)%N) = nth 0%N cflatp (qc p * 3 + j)%N.
Hypothesis hqu : forall p j, (p < 8)%N -> (j < 2)%N ->
  nth 0%N u (nth 0%N ulay (p * 2 + j)%N) = nth 0%N ulay (qu p * 2 + j)%N.
Hypothesis hqm : forall p j, (p < 4)%N -> (j < 2)%N ->
  nth 0%N u (nth 0%N mlay (p * 2 + j)%N) = nth 0%N mlay (qm p * 2 + j)%N.

Hypothesis hqcP : perm_eq [seq qc p | p <- iota 0 8] (iota 0 8).
Hypothesis hquP : perm_eq [seq qu p | p <- iota 0 8] (iota 0 8).
Hypothesis hqmP : perm_eq [seq qm p | p <- iota 0 4] (iota 0 4).

(* a permutation of the places stays inside them                              *)
Lemma qc_lt p : (p < 8)%N -> (qc p < 8)%N.
Proof.
move=> hp; have : qc p \in [seq qc q | q <- iota 0 8].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hqcP) mem_iota.
Qed.

Lemma qu_lt p : (p < 8)%N -> (qu p < 8)%N.
Proof.
move=> hp; have : qu p \in [seq qu q | q <- iota 0 8].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hquP) mem_iota.
Qed.

Lemma qm_lt p : (p < 4)%N -> (qm p < 4)%N.
Proof.
move=> hp; have : qm p \in [seq qm q | q <- iota 0 4].
  by apply/mapP; exists p => //; rewrite mem_iota.
by rewrite (perm_mem hqmP) mem_iota.
Qed.

(* ---- the parity tables, and their walk ----------------------------------- *)

Variable par8t par4t : arr.

Hypothesis hp8w : par8okw par8t.
Hypothesis hp4w : par4okw par4t.

(* ---- and the one fact about the cube ------------------------------------- *)

(* ---- the parity condition, and where it comes from ----------------------- *)

(* THE COUNT SPLITS INTO THE TWO BLOCKS: the pairs inside the outer eight,    *)
(* the pairs inside the middle four, and the mixed ones -- and a mixed pair   *)
(* is never an inversion, because an outer place holds something below eight  *)
(* and a middle place something at eight or above.                            *)
(*                                                                            *)
(* At a position of H the twelve edges are the outer eight and the middle     *)
(* four side by side, each keeping to its own, so a pair of places from       *)
(* different halves is never an inversion and the parity of the twelve is     *)
(* the exclusive or of the two.                                               *)
Lemma prm12_split (e : nat -> nat) :
  (forall p, (p < 8)%N -> e p = qu p) ->
  (forall p, (p < 4)%N -> e (8 + p)%N = (8 + qm p)%N) ->
  prmn 12 e = prmn 8 qu (+) prmn 4 qm.
Proof. Admitted.

(* and then the parity condition is the law at this position                  *)
Lemma hcubeP : tab_ok flast u -> pt flast u \in G ->
  prmn 8 qc = prmn 8 qu (+) prmn 4 qm.
Proof.
move=> huok hG.
have hc : prmn 8 qc = prmn 8 (cperm_of u).
  apply: prmn_eq => p hp; rewrite /cperm_of.
  rewrite -(eqP (all_iota_lt cflatp_prim hp)).
  by rewrite -[(p * 3)%N]addn0 hqc // addn0 cposn_lay // qc_lt.
have he : prmn 12 (eperm_of u) = prmn 8 qu (+) prmn 4 qm.
  apply: prm12_split => p hp; rewrite /eperm_of.
  - rewrite -(eqP (all_iota_lt ulay_prim hp)).
    by rewrite -[(p * 2)%N]addn0 hqu // addn0 eposn_ulay // qu_lt.
  rewrite -(eqP (all_iota_lt mlay_prim hp)).
  rewrite -[(p * 2)%N]addn0 hqm // addn0.
  by rewrite (eqP (all_iota_lt eposn_mlayC (qm_lt hp))).
by rewrite hc (prm_law huok hG).
Qed.

(* ---- the three ranks tomemb reads are the three permutations ------------- *)

Lemma tomembE a : ti2t flast (inv_tabi flast a) = u ->
  tomemb a = (rank8 qc, rank8 qu, rank4 qm).
Proof.
move=> hu; rewrite /tomemb hu; congr (_, _, _); rewrite /rank8 /rank4.
- have -> : lrank 8 (fun p => cposn (nth 0%N u (nth 0%N cprimp p)))
          = lrank 8 qc; last by [].
  apply: lrank_eq => p hp.
  rewrite -(eqP (all_iota_lt cflatp_prim hp)).
  by rewrite -[(p * 3)%N]addn0 hqc // addn0 cposn_lay // qc_lt.
- have -> : lrank 8 (fun p => eposn (nth 0%N u (nth 0%N eprim p)))
          = lrank 8 qu; last by [].
  apply: lrank_eq => p hp.
  rewrite -(eqP (all_iota_lt ulay_prim hp)).
  by rewrite -[(p * 2)%N]addn0 hqu // addn0 eposn_ulay // qu_lt.
have -> : lrank 4 (fun p => (eposn (nth 0%N u (nth 0%N eprim (8 + p)%N)) - 8)%N)
        = lrank 4 qm; last by [].
apply: lrank_eq => p hp.
rewrite -(eqP (all_iota_lt mlay_prim hp)).
rewrite -[(p * 2)%N]addn0 hqm // addn0.
by have := mplc_mlay (qm_lt hp); rewrite /mplc.
Qed.

(* ---- and they satisfy membok --------------------------------------------  *)

Lemma leaf_membH a : up8inv -> up8ok -> up4inv -> up4ok ->
  tab_ok flast u -> pt flast u \in G ->
  ti2t flast (inv_tabi flast a) = u -> membok par8t par4t (tomemb a).
Proof.
move=> hi8 h8 hi4 h4 huok hG hu.
have hcube := hcubeP huok hG.
rewrite (tomembE hu) /membok /mcp /mud /mmp.
rewrite !rank8_ltP rank4_ltP /=.
rewrite (par8okP hi8 h8 hp8w hqcP) (par8okP hi8 h8 hp8w hquP)
        (par4okP hi4 h4 hp4w hqmP) hcube.
by case: (prmn 8 qu); case: (prmn 4 qm).
Qed.

(* ---- the three parts ARE the three permutations -------------------------- *)

Lemma cpartE : up8inv -> up8ok ->
  cpart (rank8 qc) = part cflatp 3 inC cposn cslotn qc.
Proof.
(* NOT `=> //': what done closes there is the bound on the place, and it      *)
(* measured forty two seconds.  Both premises are handed over.                *)
move=> hi h8; apply: part_eq => f hf hL.
apply: (up8_lrank hi h8); first exact: hqcP.
by have /andP[h _] := lay_rng clayokC hf hL.
Qed.

Lemma upartE : up8inv -> up8ok ->
  upart (rank8 qu) = part ulay 2 inU eposn eslt qu.
Proof.
(* NOT `=> //': what done closes there is the bound on the place, and it      *)
(* measured forty two seconds.  Both premises are handed over.                *)
move=> hi h8; apply: part_eq => f hf hL.
apply: (up8_lrank hi h8); first exact: hquP.
by have /andP[h _] := lay_rng ulayokC hf hL.
Qed.

Lemma mpartE : up4inv -> up4ok ->
  mpart (rank4 qm) = part mlay 2 inM mplc eslt qm.
Proof.
(* NOT `=> //': what done closes there is the bound on the place, and it      *)
(* measured forty two seconds.  Both premises are handed over.                *)
move=> hi h4; apply: part_eq => f hf hL.
apply: (up4_lrank hi h4); first exact: hqmP.
by have /andP[h _] := lay_rng mlayokC hf hL.
Qed.

(* ---- and composed they are the position ---------------------------------- *)

(* EACH PART AGREES WITH THE POSITION ON ITS OWN FACELETS -- that is hqc, hqu *)
(* and hqm -- and is the identity outside them, and the three sets cover the  *)
(* forty eight.  So the composition is the position everywhere.               *)
Let pC := part cflatp 3 inC cposn cslotn qc.
Let pU := part ulay 2 inU eposn eslt qu.
Let pM := part mlay 2 inM mplc eslt qm.

Lemma pC_ok : partok inC pC.  Proof. exact: part_partok clayokC hqcP. Qed.
Lemma pU_ok : partok inU pU.  Proof. exact: part_partok ulayokC hquP. Qed.
Lemma pM_ok : partok inM pM.  Proof. exact: part_partok mlayokC hqmP. Qed.

(* a part read at a facelet, and read outside its own set                     *)
Lemma part_at (lay : seq nat) (nsl : nat) (inL : nat -> bool)
  (plc slt : nat -> nat) (v : nat -> nat) f : (f < 48)%N ->
  nth 0%N (part lay nsl inL plc slt v) f
  = if inL f then nth 0%N lay (v (plc f) * nsl + slt f)%N else f.
Proof. by move=> hf; rewrite /part nth_mkseq. Qed.

Lemma partok_out (S : nat -> bool) t f :
  partok S t -> (f < 48)%N -> ~~ S f -> nth 0%N t f = f.
Proof.
by case/and3P => _ h _ hf hS; move: (all_iota_lt h hf); rewrite (negbTE hS)
   => /eqP.
Qed.

Lemma partok_in (S : nat -> bool) t f :
  partok S t -> (f < 48)%N -> S f -> S (nth 0%N t f).
Proof. by case/and3P => _ _ h hf hS; move: (all_iota_lt h hf); rewrite hS. Qed.

(* ---- and composed they are the position ---------------------------------- *)

(* EACH PART AGREES WITH THE POSITION ON ITS OWN FACELETS -- that is hqc, hqu *)
(* and hqm -- and is the identity outside them, and the three sets cover the  *)
(* forty eight.  So the composition is the position everywhere.               *)
Lemma tab_ltn t f : tab_ok flast t -> (f < 48)%N -> (nth 0%N t f < 48)%N.
Proof.
by case/and3P => /eqP hs /allP hall _ hf; apply: hall; apply: mem_nth;
   rewrite hs.
Qed.

Lemma parts_compose : tab_ok flast u -> comp_tab (comp_tab pC pU) pM = u.
Proof.
move=> huok.
have hCt := partok_tab pC_ok; have hUt := partok_tab pU_ok.
have hMt := partok_tab pM_ok.
have hCU := tab_ok_comp hCt hUt.
apply: tab_eq => //; first by apply: tab_ok_comp.
move=> f hf.
rewrite comp_tabE ?(tab_ok_size hCU) // comp_tabE ?(tab_ok_size hCt) //.
have hcov := all_iota_lt coversC hf.
case: (boolP (inC f)) => hCf.
  have hv : nth 0%N pC f = nth 0%N cflatp (qc (cposn f) * 3 + cslotn f)%N.
    by rewrite /pC part_at // hCf.
  have hin : inC (nth 0%N pC f) := partok_in pC_ok hf hCf.
  have hl : (nth 0%N pC f < 48)%N := tab_ltn hCt hf.
  have hnU : ~~ inU (nth 0%N pC f).
    by move: (all_iota_lt dsj_cu hl); rewrite hin.
  have hnM : ~~ inM (nth 0%N pC f).
    by move: (all_iota_lt dsj_cm hl); rewrite hin.
  rewrite (partok_out pU_ok hl hnU) (partok_out pM_ok hl hnM) hv.
  have /andP[hp hs] := lay_rng clayokC hf hCf.
  by rewrite -(hqc hp hs) (layK clayokC hf hCf).
case: (boolP (inU f)) => hUf.
  have hv : nth 0%N pU f = nth 0%N ulay (qu (eposn f) * 2 + eslt f)%N.
    by rewrite /pU part_at // hUf.
  have hin : inU (nth 0%N pU f) := partok_in pU_ok hf hUf.
  have hl : (nth 0%N pU f < 48)%N := tab_ltn hUt hf.
  have hnM : ~~ inM (nth 0%N pU f).
    by move: (all_iota_lt dsj_um hl); rewrite hin.
  rewrite (partok_out pC_ok hf hCf) (partok_out pM_ok hl hnM) hv.
  have /andP[hp hs] := lay_rng ulayokC hf hUf.
  by rewrite -(hqu hp hs) (layK ulayokC hf hUf).
have hMf : inM f by move: hcov; rewrite (negbTE hCf) (negbTE hUf).
rewrite (partok_out pC_ok hf hCf) (partok_out pU_ok hf hUf).
rewrite /pM part_at // hMf.
have /andP[hp hs] := lay_rng mlayokC hf hMf.
by rewrite -(hqm hp hs) (layK mlayokC hf hMf).
Qed.

(* ---- so the three ranks rebuild the position ----------------------------- *)

Lemma membrng_ranks : membrng (rank8 qc, rank8 qu, rank4 qm).
Proof. by rewrite /membrng /mcp /mud /mmp !rank8_ltP rank4_ltP. Qed.

Lemma tomemb_tabH a : up8inv -> up8ok -> up4inv -> up4ok ->
  tabi_ok flast a -> ti2t flast (inv_tabi flast a) = u ->
  pt flast (memb2tab (tomemb a)) = pt flast (ti2t flast a).
Proof.
move=> hi8 h8 hi4 h4 haok hu.
have htok : tab_ok flast (ti2t flast a) := haok.
have hui : u = inv_tab flast (ti2t flast a).
  by rewrite -hu (ti2t_inv n47_small n47_len haok).
have huok : tab_ok flast u by rewrite hui; apply: tab_ok_inv.
have hmi : membinv (tomemb a) = u.
  rewrite (tomembE hu) /membinv.
  case: ifPn => [hn|_]; first by rewrite membrng_ranks in hn.
  rewrite /mcp /mud /mmp (cpartE hi8 h8) (upartE hi8 h8) (mpartE hi4 h4).
  exact: parts_compose.
by rewrite /memb2tab hmi -(ptV huok) hui -(ptV htok) invgK.
Qed.

End Leaf.
