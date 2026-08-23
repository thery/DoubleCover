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
Require Import Lehmer.
Require Import Row RowMap RowRun RowFinal RowInst RowMemb.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* ---- the parity of a permutation of the places --------------------------- *)

(* THE NUMBER OF INVERSIONS, COUNTED PLACE BY PLACE.  At each place, how many *)
(* later places hold something smaller -- which is the Lehmer digit lcode     *)
(* below, so the parity and the rank count the same thing and differ only in  *)
(* how they add it up.                                                        *)
(*                                                                            *)
(* Counting it this way rather than over all pairs at once is what makes the  *)
(* exchange of two neighbouring places a LOCAL fact: every digit but two is   *)
(* untouched, because exchanging two of the later places does not change how  *)
(* many of them are smaller.                                                  *)

(* ---- inversions are the sign, and that has to be proved once ------------- *)

(* THE ONE LEMMA THE PARITY LAW WANTS.  mathcomp has odd_permM, so the sign   *)
(* multiplies -- but its odd_perm counts ORBITS, `odd #|T| (+) odd            *)
(* #|porbits s|', and prmn counts INVERSIONS.  The two agree and the library  *)
(* does not say so, so the bridge is ours.  It cannot be avoided by using     *)
(* odd_perm instead: prmn has to COMPUTE, for the parity table walk, and a    *)
(* permutation of ordinals does not.                                          *)

(* the identity inverts nothing                                               *)

(* THE CRUX, and it is the classical one: exchanging two neighbouring places  *)
(* changes the number of inversions by exactly one.  The pairs fall into four *)
(* kinds and only one of them moves:                                          *)
(*                                                                            *)
(*   neither place is i or i + 1        the pair is untouched                 *)
(*   the pair IS (i, i + 1)             its inversion is turned over          *)
(*   one place is i, the other beyond   this pair and the one at i + 1 trade  *)
(*   one place is i + 1, other before   statuses, so the two together do not  *)
(*                                      change the count                      *)
(*                                                                            *)
(* so the count moves by exactly one and the parity turns over.  Written out  *)
(* it is a reindexing of the count over the pairs by the exchange, which is   *)
(* an involution on them -- bigop's reindex, once the count is a double sum.  *)
(*                                                                            *)
(* Every permutation is reached from the identity by such exchanges, which is *)
(* bubble sort, so prmn_mul follows from this by induction on the inversions. *)
(* NB THE PREMISE.  Without q i <> q i + 1 the statement is FALSE: a constant *)
(* q inverts nothing either way.  It is there because a permutation is        *)
(* injective, and it is where injectivity is the whole of what is used.       *)
(* exchanging the places i and i + 1                                          *)


(* AWAY FROM THE TWO PLACES NOTHING MOVES.  At a place before i the later     *)
(* places are exchanged among themselves, and how many of them are smaller    *)
(* does not depend on their order; at a place after i + 1 neither is in       *)
(* range.                                                                     *)

(* AND AT THE TWO PLACES THE COUNT MOVES BY ONE.  The digit at i becomes the  *)
(* digit that was at i + 1 plus whether q i is below q (i + 1); the digit at  *)
(* i + 1 becomes the digit that was at i less whether q (i + 1) is below q i. *)
(* A permutation makes exactly one of those two hold, so the two digits       *)
(* together move by exactly one.                                              *)


(* and then the sign multiplies, which is all prm_step needs                  *)

(* ---- a fold does not look past its list ---------------------------------- *)


(* so the rank only looks at the places                                       *)

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

(* the other side of fold_mixed: the fold never falls below r times m         *)
(* factorial.  With the two together the fold lands in one radix window and   *)
(* the digits come back out by a division, which is what lrank_code needs.    *)

(* so the fold sits in one radix window and a division reads its start back   *)

(* ---- the ranking is one to one on permutations --------------------------- *)

(* Lehmer's own fact, and it comes apart in two.  The CODE of a permutation   *)
(* is, at each place, how many later places hold something smaller; the rank  *)
(* is the code read as a mixed radix number, digit i below n - i - 1.         *)

(* one: the rank determines the code, because the radix leaves no choice.     *)
(* This is fold_mixed read backwards and wants the same induction.            *)

(* two: the code determines the permutation.  At the first place the code     *)
(* says how many of the others are smaller, which fixes q 0 outright, and the *)
(* rest follows on the places that are left.                                  *)


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

(* ---- how far a table can send a facelet ---------------------------------  *)

Lemma tab_ltn t f : tab_ok flast t -> (f < 48)%N -> (nth 0%N t f < 48)%N.
Proof.
by case/and3P => /eqP hs /allP hall _ hf; apply: hall; apply: mem_nth;
   rewrite hs.
Qed.

Lemma cflatp_lt i : (i < 24)%N -> (nth 0%N cflatp i < 48)%N.
Proof. by move=> hi; have /and4P[h _ _ _] := layP clayokC hi. Qed.

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
  all (fun m => prmn 8 (cperm_of (mvt m)) == prmn 12 (eperm_of (mvt m)))
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
(*                                                                            *)
(* IT REDUCES TO TWO THINGS AND NOTHING ELSE.  One is prmn_mul above, the     *)
(* sign multiplying.  The other is that the place permutation of a            *)
(* composition is the composition of the place permutations -- which needs    *)
(* the position to carry the facelets of one cubie to the facelets of one     *)
(* cubie, and that is cubcP for the corners and cubP for the edges, both of   *)
(* which pstok already carries.  A move may TWIST a corner, so it is only at  *)
(* the level of places that this holds, which is why cperm_of reads cposn and *)
(* throws the slot away.                                                      *)
(* ---- what a table must do to the cubies for the parity to compose -------- *)

(* THE PLACE PERMUTATION OF A COMPOSITION IS THE COMPOSITION OF THE PLACE     *)
(* PERMUTATIONS, and that is the only thing the step needs.  cperm_of reads   *)
(* the place a corner goes to and throws the SLOT away, so it composes as     *)
(* soon as the second table sends the three facelets of one corner to the     *)
(* three facelets of one corner -- it may twist them, and every move does.    *)
(* That is a fact about the eighteen moves and it is checked below, at every  *)
(* facelet, not assumed.                                                      *)
(*                                                                            *)
(* What is asked of the FIRST table is only that it sends a corner facelet    *)
(* to a corner facelet and an edge facelet to an edge facelet, which is tcub. *)

(* a facelet of an edge, either of the two                                    *)
Definition inPS (f : nat) : bool := inP f || inS f.

(* corners go to corners and edges to edges                                   *)
Definition tcub (t : seq nat) : bool :=
  all (fun f => (inC f ==> inC (nth 0%N t f))
             && (inPS f ==> inPS (nth 0%N t f))) (iota 0 48).

(* and a move reads on the places alone, however it twists and flips          *)
Definition mvcubc : bool :=
  all (fun m => all (fun f => inC f ==>
        (cposn (nth 0%N (mvt m) f) == cperm_of (mvt m) (cposn f)))
      (iota 0 48)) (iota 0 18).

Definition mvcube : bool :=
  all (fun m => all (fun f => inPS f ==>
        (eposn (nth 0%N (mvt m) f) == eperm_of (mvt m) (eposn f)))
      (iota 0 48)) (iota 0 18).

Lemma mvcubcC : mvcubc.  Proof. by vm_compute. Qed.
Lemma mvcubeC : mvcube.  Proof. by vm_compute. Qed.

(* ---- and that the two place permutations are permutations ---------------- *)

(* prmn_mul asks it of both sides, so it travels along the word with the      *)
(* parity: it holds of the solved cube, it holds of every move, and a         *)
(* composition of two permutations is one.                                    *)
Definition cpermok (t : seq nat) : bool :=
  perm_eq [seq cperm_of t p | p <- iota 0 8] (iota 0 8).
Definition epermok (t : seq nat) : bool :=
  perm_eq [seq eperm_of t p | p <- iota 0 12] (iota 0 12).

Definition pok (t : seq nat) : bool := [&& tcub t, cpermok t & epermok t].

Lemma pok_mvC : all (fun m => pok (mvt m)) (iota 0 18).
Proof. by vm_compute. Qed.

Lemma pok_idC : pok (id_tab flast).  Proof. by vm_compute. Qed.

Lemma pok_mv m : (m < 18)%N -> pok (mvt m).
Proof. by move=> hm; apply: all_iota_lt pok_mvC hm. Qed.

(* the primary facelet of a place is a facelet of the right kind              *)
Lemma cprimp_inC : all (fun p => inC (nth 0%N cprimp p)) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma eprim_inPS : all (fun p => inPS (nth 0%N eprim p)) (iota 0 12).
Proof. by vm_compute. Qed.

Lemma cprimp_lt : all (fun p => nth 0%N cprimp p < 48) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma eprim_lt : all (fun p => nth 0%N eprim p < 48) (iota 0 12).
Proof. by vm_compute. Qed.

(* ---- so the place permutation composes ----------------------------------- *)

Lemma cperm_ofM t m : tab_ok flast t -> tcub t -> (m < 18)%N ->
  forall p, (p < 8)%N ->
  cperm_of (comp_tab t (mvt m)) p = cperm_of (mvt m) (cperm_of t p).
Proof.
move=> htok htc hm p hp.
have hcp48 : (nth 0%N cprimp p < 48)%N := all_iota_lt cprimp_lt hp.
have hcpC : inC (nth 0%N cprimp p) := all_iota_lt cprimp_inC hp.
have /andP[hC _] := all_iota_lt htc hcp48.
have hfC : inC (nth 0%N t (nth 0%N cprimp p)) by apply: (implyP hC).
have hf48 := tab_ltn htok hcp48.
rewrite /cperm_of comp_tabE ?(tab_ok_size htok) //.
by apply/eqP; apply: (implyP (all_iota_lt (all_iota_lt mvcubcC hm) hf48)).
Qed.

Lemma eperm_ofM t m : tab_ok flast t -> tcub t -> (m < 18)%N ->
  forall p, (p < 12)%N ->
  eperm_of (comp_tab t (mvt m)) p = eperm_of (mvt m) (eperm_of t p).
Proof.
move=> htok htc hm p hp.
have hep48 : (nth 0%N eprim p < 48)%N := all_iota_lt eprim_lt hp.
have hepE : inPS (nth 0%N eprim p) := all_iota_lt eprim_inPS hp.
have /andP[_ hE] := all_iota_lt htc hep48.
have hfE : inPS (nth 0%N t (nth 0%N eprim p)) by apply: (implyP hE).
have hf48 := tab_ltn htok hep48.
rewrite /eperm_of comp_tabE ?(tab_ok_size htok) //.
by apply/eqP; apply: (implyP (all_iota_lt (all_iota_lt mvcubeC hm) hf48)).
Qed.

(* and playing a move keeps all three                                         *)
Lemma pok_comp t m : tab_ok flast t -> pok t -> (m < 18)%N ->
  pok (comp_tab t (mvt m)).
Proof.
move=> htok /and3P[htc hcp hep] hm.
have /and3P[hmc hmcp hmep] := pok_mv hm.
have htcc : tcub (comp_tab t (mvt m)).
  apply/allP => f; rewrite mem_iota add0n => /andP[_ hf].
  have hf48 := tab_ltn htok hf.
  have /andP[h1 h2] := all_iota_lt htc hf.
  have /andP[h3 h4] := all_iota_lt hmc hf48.
  rewrite comp_tabE ?(tab_ok_size htok) //; apply/andP; split; apply/implyP.
    by move=> hin; apply: (implyP h3); apply: (implyP h1).
  by move=> hin; apply: (implyP h4); apply: (implyP h2).
rewrite /pok htcc /=; apply/andP; split.
  rewrite /cpermok.
  have -> : [seq cperm_of (comp_tab t (mvt m)) p | p <- iota 0 8]
          = [seq cperm_of (mvt m) (cperm_of t p) | p <- iota 0 8].
    by apply/eq_in_map => p; rewrite mem_iota add0n => /andP[_ hp];
       apply: cperm_ofM.
  exact: perm_comp hmcp hcp.
rewrite /epermok.
have -> : [seq eperm_of (comp_tab t (mvt m)) p | p <- iota 0 12]
        = [seq eperm_of (mvt m) (eperm_of t p) | p <- iota 0 12].
  by apply/eq_in_map => p; rewrite mem_iota add0n => /andP[_ hp];
     apply: eperm_ofM.
exact: perm_comp hmep hep.
Qed.

(* AND THE STEP.  Playing a move on a position composes the two place         *)
(* permutations, and prmn_mul says the parity of a composition is the         *)
(* exclusive or -- so both sides pick up the same bit, which is what          *)
(* mvparokC says.                                                             *)
(*                                                                            *)
(* THE MOVE GOES ON THE RIGHT.  A word is read left to right, so a ball of    *)
(* length n + 1 is a ball of length n times a move, and the table that names  *)
(* it is the position's table composed with the move's -- comp_tab t (mvt m), *)
(* not the other way about.  It matters: the twisting table has to be the     *)
(* SECOND one.                                                                *)
Lemma prm_step t m : tab_ok flast t -> pok t -> (m < 18)%N ->
  prmn 8 (cperm_of (comp_tab t (mvt m)))
    = prmn 8 (cperm_of t) (+) prmn 8 (cperm_of (mvt m)) /\
  prmn 12 (eperm_of (comp_tab t (mvt m)))
    = prmn 12 (eperm_of t) (+) prmn 12 (eperm_of (mvt m)).
Proof.
move=> htok hpok hm; have /and3P[htc hcp hep] := hpok.
have /and3P[hmc hmcp hmep] := pok_mv hm.
split.
  have h : forall p, (p < 8)%N ->
    cperm_of (comp_tab t (mvt m)) p = cperm_of (mvt m) (cperm_of t p).
    by apply: cperm_ofM.
  by rewrite (prmn_eq h) (prmn_mul hmcp hcp) addbC.
have h : forall p, (p < 12)%N ->
  eperm_of (comp_tab t (mvt m)) p = eperm_of (mvt m) (eperm_of t p).
  by apply: eperm_ofM.
by rewrite (prmn_eq h) (prmn_mul hmep hep) addbC.
Qed.

(* AND THE LAW, as the induction along the word: prm_idC at the bottom and    *)
(* prm_step with mvparokC at each turn.  Ball.mem_gen_ball turns being in the *)
(* group into being in a ball, which is the word.                             *)
(*                                                                            *)
(* IT BUILDS THE TABLE rather than taking the given one apart, because pok    *)
(* travels forward with the parity and not backward; pt_inj then says the     *)
(* table it built is the one it was handed.  Stated that way it says more     *)
(* than the law -- every position of the group HAS a table and that table is  *)
(* pok -- and the covering at the foot of the file wants exactly that.        *)
Lemma G_pok g : g \in G -> exists v,
  [/\ tab_ok flast v, pok v, pt flast v = g &
      prmn 8 (cperm_of v) = prmn 12 (eperm_of v)].
Proof.
move=> /mem_gen_ball[n]; move: g.
elim: n => [|n ih] g.
  rewrite ball0 inE => /eqP->.
  exists (id_tab flast); split; [exact: tab_ok_id | exact: pok_idC
                                | exact: pt1 | by apply/eqP; exact: prm_idC].
rewrite /= inE => /orP[/ih//|/mulsgP[b m bB mS ->]].
have [v [vok vpok vpt vpar]] := ih b bB.
have mI : m \in moves by move: mS; rewrite inE.
have kL : (index m moves < seq.size moves)%N by rewrite index_mem.
rewrite size_moves in kL.
set k := index m moves.
have hm : m = pt flast (mvt k) by rewrite -(nth_index 1 mI) (mvtE kL).
have hok := mvt_ok kL.
exists (comp_tab v (mvt k)); split.
- exact: tab_ok_comp.
- exact: pok_comp.
- by rewrite -(ptM vok hok) vpt -hm.
have [hc he] := prm_step vok vpok kL.
rewrite hc he vpar.
have : prmn 8 (cperm_of (mvt k)) == prmn 12 (eperm_of (mvt k)).
  by move: (all_nthP 0%N mvparokC k); rewrite size_iota nth_iota // => /(_ kL).
by move=> /eqP->.
Qed.

Lemma prm_law t : tab_ok flast t -> pt flast t \in G ->
  prmn 8 (cperm_of t) = prmn 12 (eperm_of t).
Proof.
move=> tok /G_pok[v [vok vpok vpt vpar]].
by rewrite (Tsearch.pt_inj tok vok (esym vpt)).
Qed.

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

(* a U or D sticker is a corner facelet at slot nought, and that is what the  *)
(* twist being nought hands over                                              *)
Lemma cprim_lay :
  all (fun f => (f \in cprim) ==> (inC f && (cslotn f == 0%N))) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma size_ccyct : seq.size ccyct = 48%N.
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
(* the position commutes with the rotation, read at one facelet               *)
Lemma hcom f : (f < 48)%N ->
  nth 0%N u (nth 0%N ccyct f) = nth 0%N ccyct (nth 0%N u f).
Proof.
move=> hf; have := congr1 (fun t => nth 0%N t f) hcyc.
by rewrite !comp_tabE ?(tab_ok_size huok) ?size_ccyct.
Qed.

(* THE BASE: the twist being nought puts the primary facelet of a place at    *)
(* the primary facelet of a place, and that says which place.                 *)
Lemma inH_corner0 p : (p < 8)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3)%N)
  = nth 0%N cflatp (cperm_of u p * 3)%N.
Proof.
move=> hp.
have hi0 : (p * 3 < 24)%N by rewrite -[24%N]/(8 * 3)%N ltn_mul2r.
have hcp : nth 0%N cprimp p = nth 0%N cflatp (p * 3)%N.
  exact: (eqP (all_iota_lt cprimp_lay hp)).
have hf48 : (nth 0%N u (nth 0%N cflatp (p * 3)%N) < 48)%N.
  exact: tab_ltn huok (cflatp_lt hi0).
have hpr : nth 0%N u (nth 0%N cflatp (p * 3)%N) \in cprim.
  by rewrite -hcp; apply: htw0.
have /andP[hin hs0] : inC (nth 0%N u (nth 0%N cflatp (p * 3)%N))
                      && (cslotn (nth 0%N u (nth 0%N cflatp (p * 3)%N)) == 0%N).
  by move: (all_iota_lt cprim_lay hf48); rewrite hpr.
rewrite /cperm_of hcp.
by rewrite -{1}(layK clayokC hf48 hin) (eqP hs0) addn0.
Qed.

(* AND ONE SLOT AT A TIME: the rotation takes slot k to slot k + 1 and the    *)
(* position goes through it, which is hcom.                                   *)
(* the place a corner goes to is a place                                      *)
Lemma cperm_of_lt p : (p < 8)%N -> (cperm_of u p < 8)%N.
Proof.
move=> hp.
have hi0 : (p * 3 < 24)%N by rewrite -[24%N]/(8 * 3)%N ltn_mul2r.
have hcp : nth 0%N cprimp p = nth 0%N cflatp (p * 3)%N.
  exact: (eqP (all_iota_lt cprimp_lay hp)).
have hf48 : (nth 0%N u (nth 0%N cflatp (p * 3)%N) < 48)%N.
  exact: tab_ltn huok (cflatp_lt hi0).
have hpr : nth 0%N u (nth 0%N cflatp (p * 3)%N) \in cprim.
  by rewrite -hcp; apply: htw0.
have /andP[hin _] : inC (nth 0%N u (nth 0%N cflatp (p * 3)%N))
                    && (cslotn (nth 0%N u (nth 0%N cflatp (p * 3)%N)) == 0%N).
  by move: (all_iota_lt cprim_lay hf48); rewrite hpr.
by rewrite /cperm_of hcp; have /andP[h _] := lay_rng clayokC hf48 hin.
Qed.

(* the rotation reads on the layout as one step of the slot                   *)
Lemma ccyct_step r k : (r < 8)%N -> (k < 2)%N ->
  nth 0%N ccyct (nth 0%N cflatp (r * 3 + k)%N)
  = nth 0%N cflatp (r * 3 + k.+1)%N.
Proof.
move=> hr hk.
have hk3 : (k < 3)%N by apply: leq_trans hk _.
have hi : (r * 3 + k < 24)%N.
  by rewrite -[24%N]/(8 * 3)%N; apply: lidx.
have := eqP (all_iota_lt ccyct_lay hi).
by rewrite divnMDl // modnMDl !modn_small // divn_small // addn0.
Qed.

Lemma inH_cornerS p k : (p < 8)%N -> (k < 2)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3 + k)%N)
    = nth 0%N cflatp (cperm_of u p * 3 + k)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3 + k.+1)%N)
    = nth 0%N cflatp (cperm_of u p * 3 + k.+1)%N.
Proof.
move=> hp hk ih.
have hk3 : (k < 3)%N by apply: leq_trans hk _.
have hi : (p * 3 + k < 24)%N.
  by rewrite -[24%N]/(8 * 3)%N; apply: lidx.
rewrite -(ccyct_step hp hk) (hcom (cflatp_lt hi)) ih.
by rewrite (ccyct_step (cperm_of_lt hp) hk).
Qed.

Lemma inH_corner p j : (p < 8)%N -> (j < 3)%N ->
  nth 0%N u (nth 0%N cflatp (p * 3 + j)%N)
  = nth 0%N cflatp (cperm_of u p * 3 + j)%N.
Proof.
move=> hp; case: j => [_|[_|[_|]]] //.
- by rewrite !addn0; apply: inH_corner0.
- by apply: inH_cornerS => //; rewrite !addn0; apply: inH_corner0.
apply: inH_cornerS => //; apply: inH_cornerS => //.
by rewrite !addn0; apply: inH_corner0.
Qed.

End InHCorner.

(* ---- and what it says about the edges ------------------------------------ *)

(* THE SAME SHAPE, and again neither fact is new.                             *)
(*                                                                            *)
(* The position commutes with epair, which swaps the two facelets of an edge. *)
(* That is Coordfs's cubP, and pstok already carries it as cubti.  It says    *)
(* the two facelets of an edge stay together, so a slot goes to a slot.       *)
(*                                                                            *)
(* The flip is nought, so a primary facelet goes to a primary facelet, which  *)
(* is slot nought to slot nought rather than the two exchanged.               *)
(*                                                                            *)
(* And the slice is solved, so a middle place holds a middle edge and an      *)
(* outer place an outer one: the two layouts do not mix, which is what lets   *)
(* the eight and the four be separate permutations at all.                    *)

(* the layouts and the pairing agree: epair swaps the two slots of a place    *)
Lemma epairn_ulay :
  all (fun i => epairn (nth 0%N ulay i)
                == nth 0%N ulay ((i %/ 2) * 2 + (i %% 2).+1 %% 2)%N)
      (iota 0 16).
Proof. by vm_compute. Qed.

Lemma epairn_mlay :
  all (fun i => epairn (nth 0%N mlay i)
                == nth 0%N mlay ((i %/ 2) * 2 + (i %% 2).+1 %% 2)%N)
      (iota 0 8).
Proof. by vm_compute. Qed.

(* and the primary facelet of an edge place is the one whose slot is nought   *)
Lemma eprim_ulay :
  all (fun p => nth 0%N eprim p == nth 0%N ulay (p * 2)%N) (iota 0 8).
Proof. by vm_compute. Qed.

Lemma eprim_mlay :
  all (fun p => nth 0%N eprim (8 + p)%N == nth 0%N mlay (p * 2)%N) (iota 0 4).
Proof. by vm_compute. Qed.

(* a primary sticker at an outer place is an outer facelet at slot nought,    *)
(* and at a middle place a middle one -- which is what the flip being nought  *)
(* and the slice being solved hand over                                       *)
Lemma eprim_layu :
  all (fun f => ((f \in eprim) && (eposn f < 8)%N)
                ==> (inU f && (eslt f == 0%N))) (iota 0 48).
Proof. by vm_compute. Qed.

Lemma eprim_laym :
  all (fun f => ((f \in eprim) && (8 <= eposn f)%N)
                ==> (inM f && (eslt f == 0%N))) (iota 0 48).
Proof. by vm_compute. Qed.

(* the pairing reads on the layouts as one step of the slot                   *)
Lemma epairn_ustep r : (r < 8)%N ->
  epairn (nth 0%N ulay (r * 2)%N) = nth 0%N ulay (r * 2 + 1)%N.
Proof.
move=> hr; have hi : (r * 2 < 16)%N by rewrite -[16%N]/(8 * 2)%N ltn_mul2r.
have := eqP (all_iota_lt epairn_ulay hi).
by rewrite mulnK // modnMl.
Qed.

Lemma epairn_mstep r : (r < 4)%N ->
  epairn (nth 0%N mlay (r * 2)%N) = nth 0%N mlay (r * 2 + 1)%N.
Proof.
move=> hr; have hi : (r * 2 < 8)%N by rewrite -[8%N]/(4 * 2)%N ltn_mul2r.
have := eqP (all_iota_lt epairn_mlay hi).
by rewrite mulnK // modnMl.
Qed.

Section InHEdge.

Variable u : seq nat.
Hypothesis huok : tab_ok flast u.

(* pstok's cubti, as a table: the two facelets of an edge stay together       *)
Hypothesis hpair : forall f, (f < 48)%N ->
  nth 0%N u (epairn f) = epairn (nth 0%N u f).

(* the flip is nought, place by place                                         *)
Hypothesis hfl0 : forall p, (p < 12)%N ->
  nth 0%N u (nth 0%N eprim p) \in eprim.

(* and the slice is solved: a middle place holds a middle edge and an outer   *)
(* place an outer one                                                         *)
Hypothesis hsl : forall p, (p < 12)%N ->
  (8 <= eposn (nth 0%N u (nth 0%N eprim p)))%N = (8 <= p)%N.

(* THE BASE, outer: the flip being nought puts a primary sticker at a primary *)
(* sticker, and the slice being solved keeps it outer.                        *)
Lemma inH_outer0 p : (p < 8)%N ->
  nth 0%N u (nth 0%N ulay (p * 2)%N) = nth 0%N ulay (eperm_of u p * 2)%N.
Proof.
move=> hp.
have hp12 : (p < 12)%N by apply: leq_trans hp _.
have hep : nth 0%N eprim p = nth 0%N ulay (p * 2)%N.
  exact: (eqP (all_iota_lt eprim_ulay hp)).
have hi : (p * 2 < 16)%N by rewrite -[16%N]/(8 * 2)%N ltn_mul2r.
have hu48 : (nth 0%N ulay (p * 2)%N < 48)%N.
  by have /and4P[h _ _ _] := layP ulayokC hi.
have hf48 := tab_ltn huok hu48.
have hpr : nth 0%N u (nth 0%N ulay (p * 2)%N) \in eprim.
  by rewrite -hep; apply: hfl0.
have hlt : (eposn (nth 0%N u (nth 0%N ulay (p * 2)%N)) < 8)%N.
  by rewrite -hep ltnNge (hsl hp12) leqNgt hp.
have /andP[hin hs0] : inU (nth 0%N u (nth 0%N ulay (p * 2)%N))
                      && (eslt (nth 0%N u (nth 0%N ulay (p * 2)%N)) == 0%N).
  by move: (all_iota_lt eprim_layu hf48); rewrite hpr hlt.
rewrite /eperm_of hep.
by rewrite -{1}(layK ulayokC hf48 hin) (eqP hs0) addn0.
Qed.

Lemma eperm_of_ltu p : (p < 8)%N -> (eperm_of u p < 8)%N.
Proof.
move=> hp; have hp12 : (p < 12)%N by apply: leq_trans hp _.
have hep : nth 0%N eprim p = nth 0%N ulay (p * 2)%N.
  exact: (eqP (all_iota_lt eprim_ulay hp)).
by rewrite /eperm_of ltnNge (hsl hp12) leqNgt hp.
Qed.

Lemma inH_outer p j : (p < 8)%N -> (j < 2)%N ->
  nth 0%N u (nth 0%N ulay (p * 2 + j)%N)
  = nth 0%N ulay (eperm_of u p * 2 + j)%N.
Proof.
move=> hp; case: j => [_|[_|]] //; first by rewrite !addn0; apply: inH_outer0.
have hi : (p * 2 < 16)%N by rewrite -[16%N]/(8 * 2)%N ltn_mul2r.
have hu48 : (nth 0%N ulay (p * 2)%N < 48)%N.
  by have /and4P[h _ _ _] := layP ulayokC hi.
rewrite -(epairn_ustep hp) (hpair hu48) inH_outer0 //.
by rewrite (epairn_ustep (eperm_of_ltu hp)).
Qed.

(* THE BASE, middle: the same, and the slice keeps it middle                  *)
Lemma inH_middle0 p : (p < 4)%N ->
  nth 0%N u (nth 0%N mlay (p * 2)%N)
  = nth 0%N mlay ((eperm_of u (8 + p)%N - 8) * 2)%N.
Proof.
move=> hp.
have hp12 : (8 + p < 12)%N by rewrite ltn_add2l.
have hep : nth 0%N eprim (8 + p)%N = nth 0%N mlay (p * 2)%N.
  exact: (eqP (all_iota_lt eprim_mlay hp)).
have hi : (p * 2 < 8)%N by rewrite -[8%N]/(4 * 2)%N ltn_mul2r.
have hu48 : (nth 0%N mlay (p * 2)%N < 48)%N.
  by have /and4P[h _ _ _] := layP mlayokC hi.
have hf48 := tab_ltn huok hu48.
have hpr : nth 0%N u (nth 0%N mlay (p * 2)%N) \in eprim.
  by rewrite -hep; apply: hfl0.
have hge : (8 <= eposn (nth 0%N u (nth 0%N mlay (p * 2)%N)))%N.
  by rewrite -hep (hsl hp12) leq_addr.
have /andP[hin hs0] : inM (nth 0%N u (nth 0%N mlay (p * 2)%N))
                      && (eslt (nth 0%N u (nth 0%N mlay (p * 2)%N)) == 0%N).
  by move: (all_iota_lt eprim_laym hf48); rewrite hpr hge.
rewrite /eperm_of hep -/(mplc _).
by rewrite -{1}(layK mlayokC hf48 hin) (eqP hs0) addn0.
Qed.

Lemma eperm_of_ltm p : (p < 4)%N -> (eperm_of u (8 + p)%N - 8 < 4)%N.
Proof.
move=> hp.
have hp12 : (8 + p < 12)%N by rewrite ltn_add2l.
have hep : nth 0%N eprim (8 + p)%N = nth 0%N mlay (p * 2)%N.
  exact: (eqP (all_iota_lt eprim_mlay hp)).
have hi : (p * 2 < 8)%N by rewrite -[8%N]/(4 * 2)%N ltn_mul2r.
have hu48 : (nth 0%N mlay (p * 2)%N < 48)%N.
  by have /and4P[h _ _ _] := layP mlayokC hi.
have hf48 := tab_ltn huok hu48.
have hpr : nth 0%N u (nth 0%N mlay (p * 2)%N) \in eprim.
  by rewrite -hep; apply: hfl0.
have hge : (8 <= eposn (nth 0%N u (nth 0%N mlay (p * 2)%N)))%N.
  by rewrite -hep (hsl hp12) leq_addr.
have /andP[hin _] : inM (nth 0%N u (nth 0%N mlay (p * 2)%N))
                    && (eslt (nth 0%N u (nth 0%N mlay (p * 2)%N)) == 0%N).
  by move: (all_iota_lt eprim_laym hf48); rewrite hpr hge.
rewrite /eperm_of hep -/(mplc _).
by have /andP[h _] := lay_rng mlayokC hf48 hin.
Qed.

Lemma inH_middle p j : (p < 4)%N -> (j < 2)%N ->
  nth 0%N u (nth 0%N mlay (p * 2 + j)%N)
  = nth 0%N mlay ((eperm_of u (8 + p)%N - 8) * 2 + j)%N.
Proof.
move=> hp; case: j => [_|[_|]] //; first by rewrite !addn0; apply: inH_middle0.
have hi : (p * 2 < 8)%N by rewrite -[8%N]/(4 * 2)%N ltn_mul2r.
have hu48 : (nth 0%N mlay (p * 2)%N < 48)%N.
  by have /and4P[h _ _ _] := layP mlayokC hi.
rewrite -(epairn_mstep hp) (hpair hu48) inH_middle0 //.
by rewrite (epairn_mstep (eperm_of_ltm hp)).
Qed.

End InHEdge.

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
Proof.
by move=> he1 he2; apply: (prmn_cat he1 he2) => p hp; exact: qu_lt.
Qed.

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

(* ---- the covering: every position of H is a member ----------------------- *)

(* WHAT THE ROW THEOREM WANTS.  RowInst's superflip_row_within_20 says every  *)
(* member is within twenty, and asks in exchange that every position of H IS  *)
(* a member.  That is this, and its two halves are leaf_membH and             *)
(* tomemb_tabH above.                                                         *)

(* being in H, read on the table: the position carries a place to a place and *)
(* leaves the slot alone, once for each of the three layouts                  *)
Definition placeP (u : seq nat) (qc qu qm : nat -> nat) : Prop :=
  [/\ forall p j, (p < 8)%N -> (j < 3)%N ->
        nth 0%N u (nth 0%N cflatp (p * 3 + j)%N)
        = nth 0%N cflatp (qc p * 3 + j)%N,
      forall p j, (p < 8)%N -> (j < 2)%N ->
        nth 0%N u (nth 0%N ulay (p * 2 + j)%N)
        = nth 0%N ulay (qu p * 2 + j)%N,
      forall p j, (p < 4)%N -> (j < 2)%N ->
        nth 0%N u (nth 0%N mlay (p * 2 + j)%N)
        = nth 0%N mlay (qm p * 2 + j)%N,
      perm_eq [seq qc p | p <- iota 0 8] (iota 0 8)
    & perm_eq [seq qu p | p <- iota 0 8] (iota 0 8)
      /\ perm_eq [seq qm p | p <- iota 0 4] (iota 0 4)].

(* ---- being in H, as a walk over the ten generators ----------------------- *)

(* THE FIVE CONDITIONS, as one boolean on a table.  Each is decidable -- a    *)
(* table is forty eight numbers -- so the identity and the ten generators of  *)
(* H can simply be checked, and what is left to prove is that a composition   *)
(* keeps them.                                                               *)
Definition hok (t : seq nat) : bool :=
  [&& comp_tab t ccyct == comp_tab ccyct t,
      all (fun p => nth 0%N t (nth 0%N cprimp p) \in cprim) (iota 0 8),
      all (fun f => nth 0%N t (epairn f) == epairn (nth 0%N t f)) (iota 0 48),
      all (fun p => nth 0%N t (nth 0%N eprim p) \in eprim) (iota 0 12) &
      all (fun p => (8 <= eposn (nth 0%N t (nth 0%N eprim p)))%N == (8 <= p)%N)
          (iota 0 12)].

(* the ten generators of H among the eighteen moves.  faces is U R F D L B    *)
(* and each contributes its quarter turn, its half turn and its inverse, so   *)
(* U U2 U' are 0 1 2, D D2 D' are 9 10 11, and F2 B2 L2 R2 are 7 16 13 4.     *)
Definition aidx : seq nat := [:: 0; 1; 2; 9; 10; 11; 7; 16; 13; 4]%N.

Lemma aidxE j : (j < 10)%N -> nth 1 Amoves j = nth 1 moves (nth 0%N aidx j).
Proof. by case: j => [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]. Qed.

Lemma aidx_lt j : (j < 10)%N -> (nth 0%N aidx j < 18)%N.
Proof. by case: j => [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]. Qed.

Lemma hok_idC : hok (id_tab flast).  Proof. by vm_compute. Qed.

Lemma hok_aC : all (fun k => hok (mvt k)) aidx.  Proof. by vm_compute. Qed.

(* ---- and a composition keeps them --------------------------------------- *)

(* the tables compose associatively, once the first two are tables            *)
Lemma comp_tabA t1 t2 t3 : tab_ok flast t1 -> tab_ok flast t2 ->
  comp_tab (comp_tab t1 t2) t3 = comp_tab t1 (comp_tab t2 t3).
Proof.
move=> h1 h2; rewrite {1 3}/comp_tab -map_comp.
apply/eq_in_map => i hi /=.
have /and3P[_ /allP hall _] := h1.
by rewrite comp_tabE ?(tab_ok_size h2) //; apply: hall.
Qed.

(* THE THREE FACTS THE COMPOSITION NEEDS, and all three are lookups.  The     *)
(* primary facelets of the corners are cprim, listed in the prototype's own   *)
(* order; a primary facelet of an edge names its own place; and the pairing   *)
(* of a facelet is a facelet.                                                 *)
Lemma cprimpP : perm_eq cprimp cprim.  Proof. by vm_compute. Qed.

Lemma eposn_eprimC : all (fun j => eposn (nth 0%N eprim j) == j) (iota 0 12).
Proof. by vm_compute. Qed.

Lemma epairn_ltC : all (fun f => epairn f < 48) (iota 0 48).
Proof. by vm_compute. Qed.

(* TWO TABLES THAT KEEP THE FIVE COMPOSE TO ONE THAT DOES.  The commuting is  *)
(* associativity and nothing else.  The other four all read the same way: the *)
(* first table carries the facelet somewhere the second still knows about --  *)
(* a primary facelet of a corner, a primary facelet of an edge, the other     *)
(* facelet of the pair, a place in the same half of the slice -- so the       *)
(* second table's own condition applies there.                                *)
Lemma hok_comp t1 t2 : tab_ok flast t1 -> tab_ok flast t2 ->
  hok t1 -> hok t2 -> hok (comp_tab t1 t2).
Proof.
move=> h1 h2 /and5P[a1 a2 a3 a4 a5] /and5P[b1 b2 b3 b4 b5].
have hcE f : (f < 48)%N ->
    nth 0%N (comp_tab t1 t2) f = nth 0%N t2 (nth 0%N t1 f).
  by move=> hf; rewrite comp_tabE ?(tab_ok_size h1).
have hcp f : f \in cprim -> exists2 p, (p < 8)%N & nth 0%N cprimp p = f.
  move=> hf; have hf2 : f \in cprimp by rewrite (perm_mem cprimpP).
  have hsz : seq.size cprimp = 8%N by [].
  by exists (index f cprimp); [rewrite -hsz index_mem | apply: nth_index].
have hep f : f \in eprim -> exists2 p, (p < 12)%N & nth 0%N eprim p = f.
  move=> hf; have hsz : seq.size eprim = 12%N by [].
  by exists (index f eprim); [rewrite -hsz index_mem | apply: nth_index].
apply/and5P; split.
(* the rotation of the corners still commutes                                *)
- apply/eqP; rewrite (@comp_tabA t1 t2 ccyct h1 h2) (eqP b1).
  rewrite -(@comp_tabA t1 ccyct t2 h1 ccyct_ok) (eqP a1).
  by rewrite (@comp_tabA ccyct t1 t2 ccyct_ok h1).
(* a primary facelet of a corner still goes to one                           *)
- apply/allP => p; rewrite mem_iota add0n => /andP[_ hp].
  rewrite hcE ?(all_iota_lt cprimp_lt hp) //.
  have [q hq hqe] := hcp _ (all_iota_lt a2 hp).
  by rewrite -hqe; apply: (all_iota_lt b2 hq).
(* the two facelets of an edge still stay together                           *)
- apply/allP => f; rewrite mem_iota add0n => /andP[_ hf].
  rewrite !hcE ?(all_iota_lt epairn_ltC hf) // (eqP (all_iota_lt a3 hf)).
  exact: (all_iota_lt b3 (tab_ltn h1 hf)).
(* a primary facelet of an edge still goes to one                            *)
- apply/allP => p; rewrite mem_iota add0n => /andP[_ hp].
  rewrite hcE ?(all_iota_lt eprim_lt hp) //.
  have [q hq hqe] := hep _ (all_iota_lt a4 hp).
  by rewrite -hqe; apply: (all_iota_lt b4 hq).
(* and a place stays in its own half of the slice                            *)
apply/allP => p; rewrite mem_iota add0n => /andP[_ hp].
rewrite hcE ?(all_iota_lt eprim_lt hp) //.
have [q hq hqe] := hep _ (all_iota_lt a4 hp).
have heq : eposn (nth 0%N t1 (nth 0%N eprim p)) = q.
  by rewrite -hqe; apply/eqP; apply: (all_iota_lt eposn_eprimC hq).
rewrite -hqe (eqP (all_iota_lt b5 hq)).
by rewrite -(eqP (all_iota_lt a5 hp)) heq.
Qed.

(* and then being in H gives a table that keeps them, by the same induction   *)
(* as G_pok: the identity at the bottom, one generator at each step           *)
Lemma inH_hok h : h \in H ->
  exists v, [/\ tab_ok flast v, hok v & pt flast v = h].
Proof.
move=> /mem_gen_ball[n]; move: h.
elim: n => [|n ih] h.
  rewrite ball0 inE => /eqP->; exists (id_tab flast).
  by split; [exact: tab_ok_id | exact: hok_idC | exact: pt1].
rewrite /= inE => /orP[/ih//|/mulsgP[b m bB mS ->]].
have [v [vok vhok vpt]] := ih b bB.
have mI : m \in Amoves by move: mS; rewrite inE.
have j10 : (index m Amoves < 10)%N by rewrite index_mem.
set k := nth 0%N aidx (index m Amoves).
have kL : (k < 18)%N by apply: aidx_lt.
have hm : m = pt flast (mvt k).
  by rewrite -(nth_index 1 mI) (aidxE j10) (mvtE kL).
have hkok : tab_ok flast (mvt k) := mvt_ok kL.
have hhk : hok (mvt k) by apply: (all_nthP 0%N hok_aC).
exists (comp_tab v (mvt k)); split.
- exact: tab_ok_comp.
- exact: (hok_comp vok hkok vhok hhk).
by rewrite -(ptM vok hkok) vpt -hm.
Qed.

(* the five conditions InHCorner and InHEdge ask for, read off hok            *)
Lemma inH_tabconds u : tab_ok flast u -> pt flast u \in H ->
  [/\ comp_tab u ccyct = comp_tab ccyct u,
      forall p, (p < 8)%N -> nth 0%N u (nth 0%N cprimp p) \in cprim,
      forall f, (f < 48)%N -> nth 0%N u (epairn f) = epairn (nth 0%N u f),
      forall p, (p < 12)%N -> nth 0%N u (nth 0%N eprim p) \in eprim &
      forall p, (p < 12)%N ->
        (8 <= eposn (nth 0%N u (nth 0%N eprim p)))%N = (8 <= p)%N].
Proof.
move=> uok uH.
have [v [vok vhok vpt]] := inH_hok uH.
have hv : v = u by apply: (Tsearch.pt_inj vok uok); rewrite vpt.
rewrite hv in vhok.
have /and5P[k1 k2 k3 k4 k5] := vhok; split.
- exact/eqP.
- by move=> p hp; apply: (all_iota_lt k2 hp).
- by move=> f hf; move: (all_iota_lt k3 hf) => /eqP ->.
- by move=> p hp; apply: (all_iota_lt k4 hp).
by move=> p hp; move: (all_iota_lt k5 hp) => /eqP ->.
Qed.

(* AND FROM THE FIVE, placeP, with nothing new.  The three place             *)
(* permutations are inH_corner, inH_outer and inH_middle; that each is a      *)
(* permutation is pok, which G_pok carries -- for the twelve edges at once,   *)
(* and the slice being solved splits it into the outer eight and the middle   *)
(* four.                                                                      *)
Lemma inH_conds u : tab_ok flast u -> pt flast u \in H ->
  exists qc qu qm, placeP u qc qu qm.
Proof.
move=> uok uH.
have [c1 c2 c3 c4 c5] := inH_tabconds uok uH.
have uG : pt flast u \in G by apply: (subsetP HsubG).
have [v [vok vpok vpt _]] := G_pok uG.
have hv : v = u by apply: (Tsearch.pt_inj vok uok); rewrite vpt.
have /and3P[_ hcp hep] : pok u by rewrite -hv.
(* the twelve are all different, so the eight and the four are               *)
have h12u : uniq [seq eperm_of u p | p <- iota 0 12].
  by rewrite (perm_uniq hep) iota_uniq.
have h8u : uniq [seq eperm_of u p | p <- iota 0 8].
  by move: h12u; rewrite -[12%N]/(8 + 4)%N iotaD add0n map_cat cat_uniq
     => /and3P[].
have h4u : uniq [seq (eperm_of u (8 + p)%N - 8)%N | p <- iota 0 4].
  rewrite map_inj_in_uniq; first by move: h12u;
    rewrite -[12%N]/(8 + 4)%N iotaD add0n map_cat cat_uniq
      => /and3P[_ _]; rewrite -[in iota 8 4](addn0 8) iotaDl -map_comp.
  move=> p q; rewrite !mem_iota !add0n => /andP[_ hp] /andP[_ hq] he.
  have hp8 := eperm_of_ltm uok c4 c5 hp.
  have hq8 := eperm_of_ltm uok c4 c5 hq.
  have h8p : (8 <= eperm_of u (8 + p)%N)%N.
    rewrite /eperm_of (c5 (8 + p)%N); first exact: leq_addr.
    by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
  have h8q : (8 <= eperm_of u (8 + q)%N)%N.
    rewrite /eperm_of (c5 (8 + q)%N); first exact: leq_addr.
    by rewrite -[12%N]/(8 + 4)%N ltn_add2l.
  have hE : eperm_of u (8 + p)%N = eperm_of u (8 + q)%N.
    by rewrite -(subnK h8p) -(subnK h8q) he.
  have hlt r : (r < 4)%N -> (8 + r < 12)%N.
    by move=> hr; rewrite -[12%N]/(8 + 4)%N ltn_add2l.
  have := perm_inj hep (hlt _ hp) (hlt _ hq) hE.
  by move/eqP; rewrite eqn_add2l => /eqP.
exists (cperm_of u), (eperm_of u), (fun p => (eperm_of u (8 + p)%N - 8)%N).
split.
- by move=> p j hp hj; apply: (inH_corner uok c1 c2).
- by move=> p j hp hj; apply: (inH_outer uok c3 c4 c5).
- by move=> p j hp hj; apply: (inH_middle uok c3 c4 c5).
- exact: hcp.
split.
  apply: perm_of_rng => [|p hp]; first exact: h8u.
  exact: (eperm_of_ltu c5 hp).
apply: perm_of_rng => [|p hp]; first exact: h4u.
exact: (eperm_of_ltm uok c4 c5 hp).
Qed.

(* AND THE TABLE ITSELF IS FREE.  G_pok says every position of the group has  *)
(* a table, so h needs none of its own: take the one for h^-1, since tomemb   *)
(* reads the inverse table anyway, and t2ti carries it to an array.           *)
Lemma inH_places h : h \in H -> exists a qc qu qm,
  [/\ tabi_ok flast a, pt flast (ti2t flast a) = h
    & placeP (ti2t flast (inv_tabi flast a)) qc qu qm].
Proof.
move=> hh.
have hVH : h^-1 \in H by rewrite groupV.
have hVG : h^-1 \in G by apply: (subsetP HsubG).
have [u [uok upok upt _]] := G_pok hVG.
have huH : pt flast u \in H by rewrite upt.
have [qc [qu [qm hpl]]] := inH_conds uok huH.
have hiu : tab_ok flast (inv_tab flast u) := tab_ok_inv uok.
have ha : tabi_ok flast (t2ti flast (inv_tab flast u))
  := tabi_ok_t2ti n47_small n47_len hiu.
have hti : ti2t flast (t2ti flast (inv_tab flast u)) = inv_tab flast u
  := ti2t_t2ti n47_small n47_len hiu.
have hpa : pt flast (ti2t flast (t2ti flast (inv_tab flast u))) = h.
  by rewrite hti -(ptV uok) upt invgK.
have hu : ti2t flast (inv_tabi flast (t2ti flast (inv_tab flast u))) = u.
  rewrite (ti2t_inv n47_small n47_len ha) hti.
  apply: (Tsearch.pt_inj (tab_ok_inv hiu) uok).
  by rewrite -(ptV hiu) -(ptV uok) invgK.
by exists (t2ti flast (inv_tab flast u)), qc, qu, qm; rewrite hu.
Qed.

(* and then the covering is the two lemmas above, with nothing new            *)
Lemma row_cover par8t par4t : up8inv -> up8ok -> up4inv -> up4ok ->
  par8okw par8t -> par4okw par4t ->
  forall h, h \in H ->
  exists x, membok par8t par4t x /\ pt flast (memb2tab x) = h.
Proof.
move=> hi8 h8 hi4 h4 hp8 hp4 h hh.
have [a [qc [qu [qm [haok hpt [c1 c2 c3 c4 [c5 c6]]]]]]] := inH_places hh.
set u := ti2t flast (inv_tabi flast a).
have htok : tab_ok flast (ti2t flast a) := haok.
have hui : u = inv_tab flast (ti2t flast a).
  by rewrite /u (ti2t_inv n47_small n47_len haok).
have huok : tab_ok flast u by rewrite hui; apply: tab_ok_inv.
have huG : pt flast u \in G.
  rewrite hui -(ptV htok) hpt groupV.
  by apply: (subsetP HsubG).
exists (tomemb a); split.
  exact: (leaf_membH c1 c2 c3 c4 c5 c6 hp8 hp4 hi8 h8 hi4 h4 huok huG
                     (erefl u)).
by rewrite (tomemb_tabH c1 c2 c3 c4 c5 c6 hi8 h8 hi4 h4 haok (erefl u)).
Qed.
