(* =========================================================================  *)
(*  Searchr.v -- The search with the move redundancy rules.                   *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Ball Search.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Searchr.

Variable gT : finGroupType.
Variable Sseq : seq gT.
Local Notation S := [set x in Sseq].
Hypothesis Ssym : S^-1 = S.

Variable h : gT -> nat.
Hypothesis h1 : h 1 = 0.
Hypothesis hstep : forall g m, m \in S -> h g <= (h (g * m)).+1.

(* ---- 1. The face structure ------------------------------------------------*)

(* nfc faces, numbered 0 .. nfc-1, and opp pairs them up.  For the cube nfc   *)
(* is 6 and opp is U<->D, R<->L, F<->B.                                       *)
Variable nfc : nat.
Variable fc : gT -> nat.
Variable opp : nat -> nat.

Hypothesis fc_lt : forall m, m \in S -> fc m < nfc.
Hypothesis oppK : forall f, f < nfc -> opp (opp f) = f.
(* opp_lt and opp_neq were assumed here too and are NOT needed: nothing in    *)
(* the file uses them, and searchrN does not depend on them.  Removed so      *)
(* Rubik333.v is not asked for facts no proof consumes.                       *)

(* THE FIRST FACT.  The moves of one face together with 1 are closed under    *)
(* product: U * U = U2, U * U2 = U', U * U' = 1.  So two consecutive moves    *)
(* of the same face are never needed -- the word gets shorter.                *)
Hypothesis fc_close : forall m1 m2, m1 \in S -> m2 \in S -> fc m1 = fc m2 ->
  (m1 * m2 = 1) \/ (exists2 m3, m3 \in S & fc m3 = fc m1 /\ m1 * m2 = m3).

(* THE SECOND FACT.  Opposite faces commute, so of the two orders one may be  *)
(* fixed arbitrarily -- here the one with the smaller face index first.       *)
Hypothesis fc_comm : forall m1 m2, m1 \in S -> m2 \in S ->
  fc m2 = opp (fc m1) -> m1 * m2 = m2 * m1.

(* Only these two facts.  An earlier draft also assumed fc m^-1 = fc m, for a *)
(* reduced_revV that turned out to be FALSE and unnecessary -- see (c).       *)

(* ---- 2. Reduced words ---------------------------------------------------- *)

(* may a move of face f follow one of face p?  Not if same face, and of an    *)
(* opposite pair only the smaller index first.                                *)
Definition okfc (p f : nat) : bool := (f != p) && ~~ ((f == opp p) && (p < f)).

(* nfc is not the index of any face, so it means "no previous move"           *)
Definition okfc0 (p f : nat) : bool := if p < nfc then okfc p f else true.

Fixpoint reduced (p : nat) (l : seq gT) : bool :=
  if l is m :: l' then [&& m \in Sseq, okfc0 p (fc m) & reduced (fc m) l']
  else true.

(* the two defects a word can have, split out because the induction treats    *)
(* them differently: a merge shortens the word, a swap only reorders it.      *)
Definition badp (p f : nat) : bool := (f == opp p) && (p < f).

(* the guard has to mirror okfc0: at p = nfc there is no previous move, so    *)
(* the first move is unconstrained. Without the guard reducedE is simply      *)
(* false.                                                                     *)
Fixpoint nosame (p : nat) (l : seq gT) : bool :=
  if l is m :: l'
  then (if p < nfc then fc m != p else true) && nosame (fc m) l'
  else true.

(* how many adjacent opposite pairs are the wrong way round                   *)
Fixpoint inv (p : nat) (l : seq gT) : nat :=
  if l is m :: l'
  then (if p < nfc then badp p (fc m) else false) + inv (fc m) l'
  else 0.

(* reduced = in the move set, no same face twice, no inversion                *)
Lemma reducedE p l :
  reduced p l = [&& all (mem Sseq) l, nosame p l & inv p l == 0].
Proof.
elim: l p => [//|m l IH] p /=.
rewrite IH /okfc0 /okfc /badp addn_eq0.
by case: (p < nfc) => /=; case: (m \in Sseq) => //=;
   case: (fc m == p) => /=; case: (fc m == opp p) => /=;
   case: (p < fc m) => /=; case: (all (mem Sseq) l) => /=;
   case: (nosame (fc m) l) => //=.
Qed.

(* ---- 3. The search, with the rules --------------------------------------- *)

Fixpoint searchr (d : nat) (g : gT) (p : nat) : bool :=
  (h g <= d) &&
  ((g == 1) ||
   (if d is d'.+1
    then has (fun m => okfc0 p (fc m) && searchr d' (g * m) (fc m)) Sseq
    else false)).

(* ---- 4. What has to be proved -------------------------------------------- *)

(* (a) NORMALISATION, the whole content of the file.                          *)
(*                                                                            *)
(*  Two rewrites.  fc_close MERGES a same-face pair and strictly shortens the *)
(*  word; fc_comm SWAPS an out-of-order opposite pair and leaves the length   *)
(*  alone.  So the measure is (size, inv) lexicographic, with merges taking   *)
(*  priority -- and the priority is not cosmetic.  Swapping can CREATE a      *)
(*  same-face pair: D U D has none, and swapping its bad (U,D) gives D D U.   *)
(*  What is true, and what makes inv decrease, is that when the word has NO   *)
(*  same-face pair anywhere, a swap removes one inversion and creates none:   *)
(*  a new bad pair on the left would need face opp b = a, which was same-face *)
(*  with l_i before the swap, and on the right it would need face b, which was*)
(*  same-face with l_i+1.  Both excluded.                                     *)

(* the face the word leaves behind, so cat lemmas can be stated               *)
Fixpoint lastfc (p : nat) (l : seq gT) : nat :=
  if l is m :: l' then lastfc (fc m) l' else p.

Lemma inv_cat p a b : inv p (a ++ b) = inv p a + inv (lastfc p a) b.
Proof. by elim: a p => [|x a IH] p /=; rewrite ?add0n // IH addnA. Qed.

Lemma nosame_cat p a b : nosame p (a ++ b) = nosame p a && nosame (lastfc p a) b.
Proof. by elim: a p => [|x a IH] p /=; rewrite ?andTb // IH andbA. Qed.

(* THE DELICATE STEP of swap_step: after the swap the face entering l2        *)
(* changes from fc m2 to fc m1, and inv over l2 is unchanged all the same.    *)
(* Both head contributions are false, but for DIFFERENT reasons, and getting  *)
(* them the wrong way round is the trap: badp (fc m1) (fc m3) dies on its     *)
(* EQUALITY (nosame forbids fc m3 = fc m2), while badp (fc m2) (fc m3) dies   *)
(* on its ORDERING -- fc m3 = fc m1 is perfectly legal (U D U), and what      *)
(* kills it is fc m1 < fc m2.                                                 *)
Lemma inv_swap_tail m1 m2 l2 :
  fc m1 < nfc -> fc m2 < nfc -> badp (fc m1) (fc m2) ->
  nosame (fc m2) l2 ->
  inv (fc m1) l2 = inv (fc m2) l2.
Proof.
move=> h1n h2n; rewrite /badp => /andP[/eqP f2E hlt].
(* rewrite the two guards BEFORE destructuring, or h3 is an if-expression     *)
(* rather than a negation and negbTE will not apply                           *)
case: l2 => [//|m3 l2] /=; rewrite h1n h2n => /andP[h3 _].
have e1 : badp (fc m1) (fc m3) = false.
  by rewrite /badp -f2E (negbTE h3).
have e2 : badp (fc m2) (fc m3) = false.
  rewrite /badp f2E (oppK h1n).
  case: (boolP (fc m3 == fc m1)) => [/eqP->|_]; last by rewrite andFb.
  by rewrite andTb -f2E ltnNge (ltnW hlt).
by rewrite e1 e2.
Qed.

(* the two surgeries.  Stated as "there is a split", which is what the        *)
(* induction consumes; no indices anywhere.                                   *)
(* Phrased over a previous MOVE, not a previous face. With a face, `~~ nosame *)
(* p l` can be violated at the boundary with p and there is then no same-face *)
(* pair inside l at all; with a move the boundary case is just l1 = [::]. At  *)
(* the top level p is nfc, the guard is vacuous, and nosame nfc (m :: l) is   *)
(* nosame (fc m) l -- so this is the form the induction wants.                *)
Lemma find_same m0 l :
  ~~ nosame (fc m0) l ->
  exists l1 m1 m2 l2, [/\ m0 :: l = l1 ++ m1 :: m2 :: l2, fc m1 = fc m2
                       & size l1 + 2 + size l2 = (size l).+1].
Proof.
elim: l m0 => [//|m l IH] m0 /=.
case: (boolP (fc m0 < nfc)) => h0; last first.
  rewrite andTb => /(IH m)[l1 [m1 [m2 [l2 [lE fE sE]]]]].
  by exists (m0 :: l1), m1, m2, l2; split; rewrite ?lE //= !addSn sE.
rewrite negb_and negbK.
case/orP => [/eqP fE|/(IH m)[l1 [m1 [m2 [l2 [lE fE sE]]]]]].
  by exists [::], m0, m, l; split; rewrite //= fE.
by exists (m0 :: l1), m1, m2, l2; split; rewrite ?lE //= !addSn sE.
Qed.

Lemma find_bad m0 l :
  inv (fc m0) l != 0 ->
  exists l1 m1 m2 l2, [/\ m0 :: l = l1 ++ m1 :: m2 :: l2, badp (fc m1) (fc m2)
                       & size l1 + 2 + size l2 = (size l).+1].
Proof.
elim: l m0 => [//|m l IH] m0 /=.
case: (boolP (fc m0 < nfc)) => h0; last first.
  rewrite add0n => /(IH m)[l1 [m1 [m2 [l2 [lE fE sE]]]]].
  by exists (m0 :: l1), m1, m2, l2; split; rewrite ?lE //= !addSn sE.
case: (boolP (badp (fc m0) (fc m))) => bE.
  by exists [::], m0, m, l; split.
rewrite add0n => /(IH m)[l1 [m1 [m2 [l2 [lE fE sE]]]]].
by exists (m0 :: l1), m1, m2, l2; split; rewrite ?lE //= !addSn sE.
Qed.

(* big_cat wants a commutative law, so the product over a cat is proved here  *)
Lemma prodcat (a b : seq gT) :
  \prod_(m <- a ++ b) m = (\prod_(m <- a) m) * (\prod_(m <- b) m).
Proof. by elim: a => [|x a IH]; rewrite ?big_nil ?mul1g //= !big_cons IH mulgA. Qed.

(* merging a same-face pair: shorter, same product.  Note the mulgA has to be *)
(* aimed -- a bare rewrite re-associates the wrong occurrence.                *)
Lemma merge_step l1 m1 m2 l2 :
  all (mem Sseq) (l1 ++ m1 :: m2 :: l2) -> fc m1 = fc m2 ->
  exists2 l', all (mem Sseq) l' &
    size l' < size (l1 ++ m1 :: m2 :: l2) /\
    \prod_(m <- l') m = \prod_(m <- l1 ++ m1 :: m2 :: l2) m.
Proof.
move=> allS fE.
move: allS; rewrite all_cat /= => /andP[a1 /andP[s1 /andP[s2 a2]]].
have m1S : m1 \in S by rewrite inE.
have m2S : m2 \in S by rewrite inE.
case: (fc_close m1S m2S fE) => [mE|[m3 m3S [f3E mE]]].
  exists (l1 ++ l2); first by rewrite all_cat a1 a2.
  split; first by rewrite !size_cat /= ltn_add2l ltnS leqnSn.
  by rewrite !prodcat !big_cons [m1 * (m2 * _)]mulgA mE mul1g.
exists (l1 ++ m3 :: l2).
  have s3 : m3 \in Sseq by move: m3S; rewrite inE.
  by rewrite all_cat a1 /= s3 a2.
split; first by rewrite !size_cat /= ltn_add2l ltnS leqnn.
by rewrite !prodcat !big_cons [m1 * (m2 * _)]mulgA mE.
Qed.

(* swapping an out-of-order opposite pair: same length, same product, and one *)
(* inversion fewer -- the last part is the delicate one, see above.           *)
(* Swapping an out-of-order opposite pair.  The delicate conjunct is inv,     *)
(* by induction on l1: at the head, badp a b = true becomes badp b a =        *)
(* false since b > a, so the count drops by one; the tail is unchanged        *)
(* because the face entering l2 is the same set either way.  That last        *)
(* step is what nosame is for -- a new bad pair could only appear against a   *)
(* same-face neighbour, and there are none.                                   *)
Lemma swap_step p l1 m1 m2 l2 :
  all (mem Sseq) (l1 ++ m1 :: m2 :: l2) -> nosame p (l1 ++ m1 :: m2 :: l2) ->
  badp (fc m1) (fc m2) ->
  [/\ all (mem Sseq) (l1 ++ m2 :: m1 :: l2),
      size (l1 ++ m2 :: m1 :: l2) = size (l1 ++ m1 :: m2 :: l2),
      \prod_(m <- l1 ++ m2 :: m1 :: l2) m = \prod_(m <- l1 ++ m1 :: m2 :: l2) m
    & inv p (l1 ++ m2 :: m1 :: l2) < inv p (l1 ++ m1 :: m2 :: l2)].
Proof.
move=> allS nsS bE.
have bE' := bE; move: bE'; rewrite /badp => /andP[/eqP f2E hlt].
move: allS; rewrite all_cat /= => /andP[a1 /andP[s1 /andP[s2 a2]]].
have m1S : m1 \in S by rewrite inE.
have m2S : m2 \in S by rewrite inE.
have h1n : fc m1 < nfc by apply: fc_lt.
have h2n : fc m2 < nfc by apply: fc_lt.
move: nsS; rewrite nosame_cat => /andP[ns1].
set q := lastfc p l1; rewrite /= => /andP[hq /andP[h12 ns2]].
split.
- by rewrite all_cat a1 /= s1 s2 a2.
- by rewrite !size_cat.
- rewrite !prodcat !big_cons [m1 * (m2 * _)]mulgA [m2 * (m1 * _)]mulgA.
  by rewrite (fc_comm m1S m2S f2E).
rewrite !inv_cat /= h1n h2n bE.
have -> : badp (fc m2) (fc m1) = false.
  by rewrite /badp f2E (oppK h1n) eqxx andTb -f2E ltnNge (ltnW hlt).
have -> : inv (fc m1) l2 = inv (fc m2) l2 by apply: inv_swap_tail.
case: (boolP (q < nfc)) => hqn; last by rewrite !add0n ltn_add2l.
have -> : badp q (fc m2) = false.
  rewrite /badp f2E; case: (boolP (opp (fc m1) == opp q)) => [|_]; last first.
    by rewrite andFb.
  move=> /eqP oE.
  have qE : fc m1 = q by rewrite -(oppK h1n) oE (oppK hqn).
  (* hq may still carry its `if q < nfc` guard; hqn reduces it                *)
  by move: hq; rewrite ?hqn qE eqxx.
by rewrite !add0n add1n ltn_add2l leq_addl.
Qed.

(* The nested induction: outer on the length bound, inner on inv.             *)
(*                                                                            *)
(* THE MERGE BRANCH IS SEPARATE because reduce_inv needs it too.  A swap can  *)
(* BREAK nosame -- D U D has none, and swapping its bad pair gives D D U --   *)
(* so the inner induction cannot carry nosame and must fall back here.        *)
(* the nested induction: outer on the length bound, inner on inv              *)
(* THE MERGE BRANCH, on its own because reduce_inv needs it too: a swap can   *)
(* BREAK nosame (D U D has none, swapping its bad pair gives D D U), so the   *)
(* inner induction cannot carry nosame and must be able to fall back here.    *)
Lemma reduce_merge n
  (IHn : forall l, size l <= n -> all (mem Sseq) l ->
     exists2 l', reduced nfc l' & size l' <= size l /\
                 \prod_(m <- l') m = \prod_(m <- l) m)
  l :
  ~~ nosame nfc l -> size l <= n.+1 -> all (mem Sseq) l ->
  exists2 l', reduced nfc l' & size l' <= size l /\
              \prod_(m <- l') m = \prod_(m <- l) m.
Proof.
case: l => [|m l0] // nsl sl lS.
(* nfc < nfc is not reduced by /=; ltnn does it                               *)
move: nsl; rewrite /= ltnn andTb => nsl.
case: (find_same nsl) => l1 [m1 [m2 [l2 [lE fE sE]]]].
have lS' : all (mem Sseq) (l1 ++ m1 :: m2 :: l2) by rewrite -lE.
case: (merge_step lS' fE) => l3 l3S [s3 p3].
have sEq : size (l1 ++ m1 :: m2 :: l2) = (size l0).+1 by rewrite -lE.
have s3n : size l3 <= n.
  by rewrite -ltnS; apply: leq_trans s3 _; rewrite sEq; exact: sl.
case: (IHn _ s3n l3S) => l4 r4 [s4 p4].
exists l4 => //; split.
  by apply: leq_trans s4 _; rewrite -sEq; apply: ltnW.
by rewrite p4 p3 -lE.
Qed.

(* the INNER induction on inv.  NOTE: no nosame hypothesis -- see reduce_merge. *)
Lemma reduce_inv n
  (IHn : forall l, size l <= n -> all (mem Sseq) l ->
     exists2 l', reduced nfc l' & size l' <= size l /\
                 \prod_(m <- l') m = \prod_(m <- l) m)
  k l :
  inv nfc l <= k -> size l <= n.+1 -> all (mem Sseq) l ->
  exists2 l', reduced nfc l' & size l' <= size l /\
              \prod_(m <- l') m = \prod_(m <- l) m.
Proof.
elim: k l => [|k IHk] l ik sl lS.
  case: (boolP (nosame nfc l)) => nsl; last exact: (reduce_merge IHn nsl sl lS).
  exists l; first by rewrite reducedE lS nsl /= -leqn0 ik.
  by split.
case: (boolP (nosame nfc l)) => nsl; last exact: (reduce_merge IHn nsl sl lS).
case: (boolP (inv nfc l == 0)) => i0.
  exists l; first by rewrite reducedE lS nsl i0.
  by split.
case: l ik sl lS nsl i0 => [|m l1] // ik sl lS nsl.
move: ik nsl; rewrite /= ltnn add0n => ik nsl i0.
case: (find_bad i0) => l1' [m1 [m2 [l2 [lE bE sE]]]].
have lS' : all (mem Sseq) (l1' ++ m1 :: m2 :: l2) by rewrite -lE.
have nsl' : nosame nfc (l1' ++ m1 :: m2 :: l2).
  by rewrite -lE /= ltnn andTb; move: nsl; rewrite andTb.
case: (swap_step lS' nsl' bE) => aS sQ pQ iQ.
have ikk : inv nfc (l1' ++ m2 :: m1 :: l2) <= k.
  rewrite -ltnS; apply: leq_trans iQ _; rewrite -lE /= ltnn add0n; exact: ik.
have slQ : size (l1' ++ m2 :: m1 :: l2) <= n.+1 by rewrite sQ -lE.
case: (IHk _ ikk slQ aS) => l4 r4 [s4 p4].
exists l4 => //; split; first by apply: leq_trans s4 _; rewrite sQ -lE.
by rewrite p4 pQ -lE.
Qed.

Lemma reduce_bound n l :
  size l <= n -> all (mem Sseq) l ->
  exists2 l', reduced nfc l' & size l' <= size l /\
              \prod_(m <- l') m = \prod_(m <- l) m.
Proof.
elim: n l => [|n IHn] l.
  by rewrite leqn0 size_eq0 => /eqP-> _; exists [::]; rewrite ?big_nil.
by move=> sl lS; apply: (reduce_inv IHn (k := inv nfc l)).
Qed.

Lemma reduce_word (l : seq gT) :
  all (mem Sseq) l ->
  exists2 l', reduced nfc l' & size l' <= size l /\ \prod_(m <- l') m = \prod_(m <- l) m.
Proof. exact: (reduce_bound (leqnn (size l))). Qed.

(* (b) the ball is exactly the reduced words, which is (a) plus the standard  *)
(* "ball d = products of lists of length at most d".                          *)
(* [HARD] not reached. SKELETON: induction on d. ball S 0 = [set 1] gives l = *)
(* [::]. For d.+1, ball S d.+1 = ball S d :|: (ball S d * S), so either the   *)
(* IH applies directly (size <= d <= d.+1), or g = a * s with a in ball S d   *)
(* and s in S: take l = (word for a) ++ [:: s], and prodcat/big_cons finish   *)
(* it. Ball.v may already have something close -- check before proving.       *)
Lemma ball_prod d g :
  g \in ball S d -> exists2 l, all (mem Sseq) l & size l <= d /\ \prod_(m <- l) m = g.
Proof.
elim: d g => [g|d IH g].
  by rewrite /= set1gE inE => /eqP->; exists [::]; rewrite ?big_nil.
rewrite {1}/ball -/ball inE => /orP[gb|].
  by case: (IH _ gb) => l lS [sl pl]; exists l => //; split=> //; apply: leqW.
case/mulsgP => a s aB sS ->.
case: (IH _ aB) => l lS [sl pl].
have sQ : s \in Sseq by move: sS; rewrite inE.
exists (l ++ [:: s]); first by rewrite all_cat lS /= sQ.
split; first by rewrite size_cat /= addn1 ltnS.
by rewrite prodcat big_cons big_nil mulg1 pl.
Qed.

(* [EASY once ball_prod and reduce_word are in] SKELETON: ball_prod gives a   *)
(* word, reduce_word reduces it, and size l' <= size l <= d chains.           *)
Lemma ball_reduced d g :
  g \in ball S d ->
  exists2 l, reduced nfc l & size l <= d /\ \prod_(m <- l) m = g.
Proof.
case/ball_prod => l lS [sl pl].
case: (reduce_word lS) => l' rl' [sl' pl'].
by exists l' => //; split; [apply: leq_trans sl' sl | rewrite pl' pl].
Qed.

(* (c) completeness, the analogue of Search.ball_search.  Note the word is    *)
(* read the other way round in search (g * m1 * m2 ... = 1), so this needs    *)
(* reduced to be stable under inverse-and-reverse -- Ssym and oppK give it,   *)
(* but it is a step in its own right.                                         *)
(* (c) completeness.  searchr wants m1 * ... * mk = g^-1, so the reduced word *)
(* is taken for g^-1 rather than for g, and NOTHING IS REVERSED.              *)
(*                                                                            *)
(*  An earlier draft tried to reverse the word for g, via                     *)
(*    reduced_revV : reduced nfc l -> reduced nfc (rev [seq m^-1 | m <- l])   *)
(*  which is FALSE: l = [D; U] has faces (3,0) and is reduced, since okfc     *)
(*  wants the larger face first; its reverse has faces (0,3) and is not.      *)
(*  The convention simply is not symmetric under reversal.  Ball.mem_ballV    *)
(*  moves to g^-1 instead and the whole problem disappears.                   *)

(* converse of ball_prod: a word of length k lands in ball S k                *)
Lemma prod_in_ball l :
  all (mem Sseq) l -> \prod_(m <- l) m \in ball S (size l).
Proof.
elim/last_ind: l => [|l m IH].
  by move=> _; rewrite big_nil; exact: mem1_ball.
rewrite -cats1 all_cat /= andbT => /andP[lS mS].
rewrite prodcat big_cons big_nil mulg1 size_cat /= addn1.
rewrite {1}/ball -/ball inE; apply/orP; right.
by apply/mulsgP; exists (\prod_(m0 <- l) m0) m => //; [apply: IH | rewrite inE].
Qed.

Lemma ballW a b (x : gT) : a <= b -> x \in ball S a -> x \in ball S b.
Proof.
elim: b => [|b IHb]; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|ab xa].
by apply: (subsetP (ball_mono _ _)); apply: IHb; rewrite ?xa // -ltnS.
Qed.

(* a reduced word for g^-1 IS a successful search from g                      *)
Lemma searchr_word d g p l :
  size l <= d -> reduced p l -> \prod_(m <- l) m = g^-1 -> searchr d g p.
Proof.
elim: l d g p => [|m l IH] d g p sl rl pl.
  move: pl; rewrite big_nil => gE.
  have -> : g = 1 by rewrite -(invgK g) -gE invg1.
  by case: d sl => [|d] sl; rewrite /= h1 eqxx.
have lS : all (mem Sseq) (m :: l) by move: rl; rewrite reducedE => /and3P[].
have gB : g \in ball S d.
  rewrite -mem_ballV // -pl; apply: ballW (prod_in_ball lS); exact: sl.
case: d sl gB => [//|d] sl gB.
rewrite /= (h_ball Ssym h1 hstep gB) /=; apply/orP; right.
move: rl; rewrite /= => /and3P[mQ okm rl].
apply/hasP; exists m => //; rewrite okm /=.
apply: (IH _ _ _ _ rl); first by move: sl; rewrite /= ltnS.
by rewrite invMg; move: pl; rewrite big_cons => <-; rewrite mulKg.
Qed.

Lemma ball_searchr d g : g \in ball S d -> searchr d g nfc.
Proof.
rewrite -mem_ballV // => gB.
case: (ball_reduced gB) => l rl [sl pl].
exact: (searchr_word sl rl pl).
Qed.

Corollary searchrN d g : searchr d g nfc = false -> g \notin ball S d.
Proof. by move=> sF; apply/negP => /ball_searchr; rewrite sF. Qed.

(* ---- 5. Splitting the root, WITH the guard ---------------------------------*)

(* Option A of the ball_split2 question, and it turns out Search.ball_split2  *)
(* does not have to change at all: the split belongs at the searchr level,    *)
(* where the guard already exists, and it is then two unfoldings of searchr   *)
(* and no ball reasoning whatsoever.                                          *)
(* Only guard respecting pairs (m1, m2) need checking, which is where the     *)
(* redundancy factor at the TOP of the search comes from -- after a U face    *)
(* root the guard kills faces U and D, so twelve second moves instead of      *)
(* eighteen.  Measured cost of NOT doing this: 1.348^2 = 1.82x.               *)
Lemma searchr_split2 d g p :
  g != 1 ->
  (forall m1, m1 \in Sseq -> okfc0 p (fc m1) -> g * m1 != 1) ->
  (forall m1 m2, m1 \in Sseq -> m2 \in Sseq ->
     okfc0 p (fc m1) -> okfc0 (fc m1) (fc m2) ->
     searchr d (g * m1 * m2) (fc m2) = false) ->
  searchr d.+2 g p = false.
Proof.
move=> g1 gm1 gmm.
apply/negP => /andP[_]; rewrite (negbTE g1) orFb.
case/hasP => m1 m1S /andP[ok1] /andP[_].
rewrite (negbTE (gm1 _ m1S ok1)) orFb.
case/hasP => m2 m2S /andP[ok2].
(* the goal here shows searchr unfolded to its fix, so rewrite cannot match   *)
(* it; exact does, up to conversion                                           *)
move=> sm; case/negP: (negbT (gmm _ _ m1S m2S ok1 ok2)); exact: sm.
Qed.

(* ---- 6. Deeper is not worse ---------------------------------------------- *)

(* Search.v has search_mono for the unguarded search; the guarded one never   *)
(* needed it, since everything reaches balls through ball_searchr and ballW.  *)
(* It is what lets a piece proved at one depth be used at a smaller one.      *)
Lemma searchr_mono d g p : searchr d g p -> searchr d.+1 g p.
Proof.
elim: d g p => [|d IH] g p /andP[hg]; rewrite /= (leqW hg) /=.
  by case/orP => [->//|].
case/orP => [->//|/hasP[m mS /andP[okm sm]]]; apply/orP; right.
by apply/hasP; exists m => //; rewrite okm /=; exact: IH.
Qed.

Lemma searchrW d d' g p : d <= d' -> searchr d g p -> searchr d' g p.
Proof.
elim: d' => [|d' IH]; first by rewrite leqn0 => /eqP->.
rewrite leq_eqVlt => /orP[/eqP->//|dd' sd].
by apply: searchr_mono; apply: IH; rewrite // -ltnS.
Qed.

(* ---- 7. The root split, KEEPING the guard on the move after the root ------*)

(* The first move comes from Sr and is chosen by symmetry, not by the guard,  *)
(* so nothing constrains the second one -- see Root.v.  But the word AFTER    *)
(* that second move is reduced like any other, so its own first move is       *)
(* guarded against fc m2, and that is one whole level of branching.  The      *)
(* search files threw it away by starting each piece at nfc.                  *)
(*                                                                            *)
(* hroot is Root.ball_root at d.+1, and the rest is one unfolding of searchr, *)
(* exactly as in searchr_split2.                                              *)
Lemma searchr_root2 (Sr : seq gT) d g :
  (g \in ball S d.+2 -> exists2 m1, m1 \in Sr & g * m1 \in ball S d.+1) ->
  (forall m1, m1 \in Sr -> g * m1 != 1) ->
  (forall m1 m2, m1 \in Sr -> m2 \in Sseq ->
     searchr d (g * m1 * m2) (fc m2) = false) ->
  g \notin ball S d.+2.
Proof.
move=> hroot hn1 hmm; apply/negP => gB.
have [m1 m1R gm1B] := hroot gB.
move: (ball_searchr gm1B) => /andP[_].
rewrite (negbTE (hn1 _ m1R)) orFb.
(* the goal shows searchr unfolded to its fix, so rewrite cannot match it;    *)
(* exact does, up to conversion -- as in searchr_split2                       *)
case/hasP => m2 m2S /andP[_ sm2].
by case/negP: (negbT (hmm _ _ m1R m2S)); exact: sm2.
Qed.

(* (d) and the sanity check that this is worth it: the rules only ever remove *)
(* candidates, so a reduced search that fails is a search that fails.         *)
Lemma searchr_search d g p : searchr d g p -> search Sseq h d g.
Proof.
elim: d g p => [g p|d IH g p] //=.
case/andP => hg /orP[/eqP gE|]; first by rewrite hg gE eqxx.
case/hasP => m mS /andP[_ sm]; rewrite hg /=; apply/orP; right.
by apply/hasP; exists m => //; apply: IH sm.
Qed.

(* (e) soundness, the pair of ball_searchr.  Note p is arbitrary here, where  *)
(* ball_searchr needs nfc: the guard only ever REMOVES candidates, so a       *)
(* guarded search that succeeds is still telling the truth.                   *)
Lemma searchr_ball d g p : searchr d g p -> g \in ball S d.
Proof. by move/searchr_search; exact: search_ball. Qed.

(* the form everything else uses -- searchrN is this one at p = nfc, in the   *)
(* other direction                                                            *)
Corollary searchr_far d g p : g \notin ball S d -> searchr d g p = false.
Proof. by move=> gB; apply/negP => /searchr_ball; apply/negP. Qed.

(* ---- 8. The same root split, and the second move guarded as well ----------*)

(* searchr_root2 asks for every second move; this asks only for those on a    *)
(* DIFFERENT FACE from the first.  A second move on the same face merges with *)
(* the first (fc_close), which shortens the word -- so the case is not        *)
(* removed, it is moved to a smaller depth, and that is what the induction on *)
(* k is for.  Two ingredients beyond searchr_root2: searchrW, since the       *)
(* surviving pieces sit at depth d and the induction meets them lower, and    *)
(* searchr_ball, to come back from a search that succeeded to the ball the    *)
(* induction hypothesis speaks about.                                         *)
Lemma searchr_root2m (Sr : seq gT) d g :
  {subset Sr <= Sseq} ->
  g != 1 ->
  (forall k, g \in ball S k.+1 -> exists2 m1, m1 \in Sr & g * m1 \in ball S k) ->
  (forall m1, m1 \in Sr -> g * m1 != 1) ->
  (forall m1 m2, m1 \in Sr -> m2 \in Sseq -> fc m2 != fc m1 ->
     searchr d (g * m1 * m2) (fc m2) = false) ->
  g \notin ball S d.+2.
Proof.
move=> SrS g1 hroot hn1 hmm.
suff H : forall k, k <= d.+2 -> g \notin ball S k by apply: H.
elim => [_|k IH kL]; first by rewrite /= set1gE inE.
apply/negP => gB.
have [m1 m1R gm1B] := hroot k gB.
case: k IH kL gB gm1B => [|k] IH kL gB gm1B.
  by move: gm1B; rewrite /= set1gE inE => /eqP gE; case/eqP: (hn1 _ m1R).
move: (ball_searchr gm1B) => /andP[_].
rewrite (negbTE (hn1 _ m1R)) orFb.
case/hasP => m2 m2S /andP[_ sm2].
(* the goal shows searchr unfolded to its fix; exact matches up to conversion *)
have sm : searchr k (g * m1 * m2) (fc m2) by exact: sm2.
have kd : (k <= d)%N by move: kL; rewrite !ltnS.
have gnB : g \notin ball S k.+1 by apply: IH; apply: ltnW.
case: (eqVneq (fc m2) (fc m1)) => [fe|fne]; last first.
  by move: (hmm _ _ m1R m2S fne); rewrite (searchrW kd sm).
have m1S : m1 \in S by rewrite memS; apply: SrS.
have m2SS : m2 \in S by rewrite memS.
case: (fc_close m1S m2SS (esym fe)) => [me|[m3 m3S [fm3 me]]].
  rewrite -mulgA me mulg1 in sm.
  by case/negP: gnB; apply: ballW (searchr_ball sm).
rewrite -mulgA me in sm.
case/negP: gnB; rewrite {1}/ball -/ball inE; apply/orP; right.
apply/mulsgP; exists (g * m3) m3^-1; last by rewrite -mulgA mulgV mulg1.
  exact: searchr_ball sm.
by apply: memSV.
Qed.

End Searchr.
