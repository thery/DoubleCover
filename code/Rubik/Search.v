(* =========================================================================  *)
(*  Search.v -- The lower bound search: iterative deepening with an           *)
(*     admissible heuristic.                                                  *)
(* =========================================================================  *)

From mathcomp Require Import all_ssreflect all_fingroup.
Require Import Ball.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Search.

Variable gT : finGroupType.

(* The move set, given as the list the search actually walks over.            *)
Variable Sseq : seq gT.
Local Notation S := [set g in Sseq].

(* The move set is symmetric: this is what lets a word be undone one move at  *)
(* a time, i.e. what makes "search from g towards 1" the same problem as      *)
(* "reach g from 1".                                                          *)
Hypothesis Ssym : S^-1 = S.

(* The pruning heuristic, and the two local conditions it must satisfy.       *)
Variable h : gT -> nat.
Hypothesis h1 : h 1 = 0.
Hypothesis hstep : forall g m, m \in S -> h g <= (h (g * m)).+1.

Lemma memS m : (m \in S) = (m \in Sseq). Proof. by rewrite inE. Qed.

Lemma memSV m : m \in S -> m^-1 \in S.
Proof. by move=> mS; rewrite -Ssym mem_invg invgK. Qed.

(* ---- 1. The heuristic is a lower bound on the distance --------------------*)

Lemma h_ball g d : g \in ball S d -> h g <= d.
Proof.
elim: d g => [g|d IH g]; first by rewrite /= set1gE inE => /eqP->; rewrite h1.
rewrite /= inE => /orP[/IH hg|]; first by apply: leq_trans hg _.
case/mulsgP => a s aB sS ->.
have sV : s^-1 \in S := memSV sS.
have H := hstep (a * s) sV.
by rewrite -mulgA mulgV mulg1 in H; apply: leq_trans H _; rewrite ltnS IH.
Qed.

(* ---- 2. The search ------------------------------------------------------- *)

(* [search d g] is "g might be solvable in at most d moves".  It answers      *)
(* honestly on the "no" side, which is the side a lower bound needs.          *)
Fixpoint search (d : nat) (g : gT) : bool :=
  (h g <= d) &&
  ((g == 1) || (if d is d'.+1 then has (fun m => search d' (g * m)) Sseq
                else false)).

Lemma search_mono d g : search d g -> search d.+1 g.
Proof.
elim: d g => [|d IH] g /andP[hg gE]; apply/andP; split;
    try by apply: leq_trans hg _.
  by move: gE; rewrite orbF => ->.
move: gE => /orP[->//|/hasP[m mS sm]].
by apply/orP; right; apply/hasP; exists m => //; apply: IH.
Qed.

(* The whole point: everything in the d-ball is found.                        *)
Lemma ball_search d g : g \in ball S d -> search d g.
Proof.
elim: d g => [g|d IH g].
  by rewrite /= set1gE inE => /eqP->; rewrite /search h1 eqxx.
move=> gB; rewrite /= (h_ball gB) /=.
move: gB; rewrite {1}/ball -/ball inE => /orP[gb|].
  by have := search_mono (IH _ gb); rewrite /= => /andP[_].
case/mulsgP => a s aB sS ->.
apply/orP; right; apply/hasP; exists s^-1; first by rewrite -memS; apply: memSV.
by rewrite -mulgA mulgV mulg1; apply: IH.
Qed.

(* And the other side: what the search finds is really there.  Only the "no"
   side is needed for a lower bound, which is why this was never stated; it
   is what lets a search that succeeded put its argument back in a ball.      *)
Lemma search_ball d g : search d g -> g \in ball S d.
Proof.
elim: d g => [g|d IH g] /andP[hg].
  by rewrite orbF => /eqP->; rewrite /= set1gE inE.
case/orP => [/eqP->|/hasP[m mS sm]].
  exact: mem1_ball.
rewrite {1}/ball -/ball inE; apply/orP; right.
apply/mulsgP; exists (g * m) m^-1; last by rewrite -mulgA mulgV mulg1.
  exact: IH.
by apply: memSV; rewrite memS.
Qed.

(* ... which is to say, a negative answer is a proof.                         *)
Corollary searchN d g : search d g = false -> g \notin ball S d.
Proof. by move=> sF; apply/negP => /ball_search; rewrite sF. Qed.

(* ---- 3. Splitting the root, for checking in parallel ----------------------*)

Lemma ball_cons d g :
  g \in ball S d.+1 -> g = 1 \/ exists2 m, m \in Sseq & g * m \in ball S d.
Proof.
(* in both steps the witness is s^-1, which is in S by symmetry, and the      *)
(* shortened word g * s^-1 is the prefix a.                                   *)
elim: d g => [|d IH] g.
  rewrite /= inE => /orP[|].
    by rewrite set1gE inE => /eqP->; left.
  case/mulsgP => a s; rewrite set1gE inE => /eqP-> sS ->.
  right; exists s^-1; first by rewrite -memS; apply: memSV.
  by rewrite -mulgA mulgV mulg1 inE.
rewrite {1}/ball -/ball inE => /orP[gb|].
  case: (IH _ gb) => [->|[m mS gm]]; first by left.
  by right; exists m => //; apply: (subsetP (ball_mono _ _)).
case/mulsgP => a s aB sS ->; right; exists s^-1.
  by rewrite -memS; apply: memSV.
by rewrite -mulgA mulgV mulg1.
Qed.

(* One search of depth d.+2 becomes the independent searches of depth d under *)
(* each pair of first moves -- one lemma per pair, no shared state.           *)
Lemma ball_split2 d g :
  g != 1 ->
  (forall m, m \in Sseq -> g * m != 1) ->
  (forall m1 m2, m1 \in Sseq -> m2 \in Sseq -> g * m1 * m2 \notin ball S d) ->
  g \notin ball S d.+2.
Proof.
move=> g1 gm1 gmm; apply/negP => /ball_cons[g1E|[m1 m1S]].
  by case/eqP: g1.
case/ball_cons => [gm1E|[m2 m2S gmmB]].
  by case/eqP: (gm1 _ m1S).
by case/negP: (gmm _ _ m1S m2S).
Qed.

End Search.
